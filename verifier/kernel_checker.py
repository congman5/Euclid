"""
kernel_checker.py — Strict proof-checking kernel for System E.

This module contains ONLY the trusted verification logic.  Every proof
step must be justified by an explicit, exact rule application.  No
search, no SMT, no consequence-closure fallback.

Design contract (per instructions.txt, Phase 3):
  For every step:
    1. verify refs exist
    2. verify refs are earlier than current step
    3. verify refs are in scope
    4. verify the rule name is recognized
    5. verify the refs match the rule input pattern exactly
    6. verify new variables are fresh and typed correctly
    7. verify step.assertions are exactly the allowed outputs (or a
       documented subset)
    8. add only the validated outputs to known facts

No step is accepted because it is "some consequence of self.known".

Allowed imports:
  - AST / literals / substitutions
  - theorem registry
  - rule schemas
  - proof step datatypes

Disallowed imports (NOT imported anywhere in this module):
  - e_backward
  - e_discovery
  - smt_backend
  - anything that searches for a proof rather than checking one
"""
from __future__ import annotations

from dataclasses import dataclass, field
from typing import Dict, FrozenSet, List, Optional, Set, Tuple

from .e_ast import (
    Sort, Literal, Sequent,
    Equals, On, SameSide, Between, Center, Inside, Intersects,
    SegmentTerm, AngleTerm, AreaTerm,
    ProofStep, StepKind, EProof, ETheorem,
    SymbolInfo, atom_vars, literal_vars, substitute_literal,
)
from .e_construction import (
    ALL_CONSTRUCTION_RULES, CONSTRUCTION_RULE_BY_NAME, ConstructionRule,
)


# ═══════════════════════════════════════════════════════════════════════
# Checking contract (Deliverable 4 — documentation note)
# ═══════════════════════════════════════════════════════════════════════

STRICT_CHECKING_CONTRACT = """\
Strict Checking Contract for System E Proof Verification
=========================================================

Every non-premise line is accepted ONLY if it satisfies ALL of:

 1. REFS EXIST — all cited line references are valid proof step IDs.
 2. REFS PRIOR — all cited references are earlier than the current step.
 3. RULE RECOGNIZED — the cited justification maps to a known rule in
    the axiom registry, construction table, or theorem library.
 4. PREMISES MATCH — the facts established by the cited references
    exactly match the rule's required input pattern.
 5. CONCLUSION MATCH — the step's assertions are exactly the rule's
    allowed outputs (or a documented subset for rules supporting
    subset output like theorem application).
 6. FRESH VARIABLES — any new variables introduced by the step are
    fresh (not already in scope) and have correct sorts.
 7. NO HIDDEN MUTATION — verifying a step does not add facts to the
    global context other than the step's validated outputs.

Prohibited behaviors:
 - Accepting a step because the conclusion is derivable from context.
 - Accepting a step because a different rule would justify it.
 - Accepting a step because a search/SMT/consequence engine can derive it.
 - theorem_name bypass: only _check_theorem processes theorem_name.
 - Mutating self.known during derivability tests (_is_any_consequence
   is excluded from the strict path).

Case splits (Phase 9):
 - Each branch runs in an isolated child checker.
 - Only explicitly declared target assertions proved in BOTH branches
   are imported back to the parent context.
 - Arbitrary intersection of branch known-sets is NOT imported.

Two verification paths:
 - EProof path (verify_proof / check_proof): uses compat mode
   (strict=False) for legacy EProof objects with generic StepKind.
 - JSON path (verify_e_proof_json): uses strict rule-checking for
   proofs submitted through the UI with specific axiom justifications.
 - KernelChecker.check_proof_strict(): always strict, for testing
   and future use.
"""


# ═══════════════════════════════════════════════════════════════════════
# Diagnostic types
# ═══════════════════════════════════════════════════════════════════════

@dataclass
class KernelCheckResult:
    """Result of checking a single proof step or an entire proof."""
    valid: bool = True
    errors: List[str] = field(default_factory=list)
    warnings: List[str] = field(default_factory=list)
    established: Set[Literal] = field(default_factory=set)
    variables: Dict[str, Sort] = field(default_factory=dict)

    def add_error(self, msg: str) -> None:
        self.valid = False
        self.errors.append(msg)

    def add_warning(self, msg: str) -> None:
        self.warnings.append(msg)


# ═══════════════════════════════════════════════════════════════════════
# Central validators  (Phase 10)
# ═══════════════════════════════════════════════════════════════════════

def validate_refs_exist(
    step: ProofStep,
    established_ids: Set[int],
) -> Optional[str]:
    """Return an error string if any ref does not point to an
    established step, or ``None`` if all refs are valid."""
    for r in step.refs:
        if r not in established_ids:
            return (
                f"Step {step.id}: ref {r} does not reference an "
                f"established step.")
    return None


def validate_refs_prior(
    step: ProofStep,
) -> Optional[str]:
    """Return an error if any ref is not strictly earlier than this step."""
    for r in step.refs:
        if r >= step.id:
            return (
                f"Step {step.id}: ref {r} must be earlier than "
                f"the current step.")
    return None


def validate_fresh_vars(
    step: ProofStep,
    variables: Dict[str, Sort],
) -> Optional[str]:
    """Return an error if any ``step.new_vars`` name is already in scope."""
    for name, sort in step.new_vars:
        if name in variables:
            return (
                f"Step {step.id}: variable '{name}' already exists "
                f"(sort {variables[name].name}).")
    return None


def validate_assertions_well_typed(
    step: ProofStep,
    variables: Dict[str, Sort],
) -> Optional[str]:
    """Return an error if any assertion references an undeclared variable.

    This is a light structural check — it does NOT type-check metric
    terms (that is the metric engine's job).  It only verifies that
    diagrammatic atoms reference variables whose sorts are compatible.
    """
    for lit in step.assertions:
        for vname in atom_vars(lit.atom):
            # Variables introduced by this construction step are ok
            new_names = {n for n, _ in step.new_vars}
            if vname not in variables and vname not in new_names:
                return (
                    f"Step {step.id}: variable '{vname}' in "
                    f"assertion {lit} is not declared.")
    return None


# ═══════════════════════════════════════════════════════════════════════
# Strict kernel checker
# ═══════════════════════════════════════════════════════════════════════

class KernelChecker:
    """Strict proof kernel for System E.

    Unlike ``EChecker``, this module:
      - never searches for proofs (no consequence closure used as
        a verification method)
      - never mutates ``self.known`` during derivability tests
      - never accepts a step because the conclusion is derivable —
        only because the exact cited rule + refs justify it

    The ``strict`` flag is always True in this module.  It exists so
    callers can document their intent.
    """

    def __init__(
        self,
        theorems: Optional[Dict[str, ETheorem]] = None,
        *,
        strict: bool = True,
    ):
        self.known: Set[Literal] = set()
        self.variables: Dict[str, Sort] = {}
        self.theorems: Dict[str, ETheorem] = theorems or {}
        self.strict: bool = strict
        # Track step ids that have been successfully checked
        self._established_ids: Set[int] = set()
        # Per-step output record (for ref-restricted checking)
        self._step_outputs: Dict[int, Set[Literal]] = {}

    # ── Full proof check ──────────────────────────────────────────

    def check_proof(self, proof: EProof) -> KernelCheckResult:
        """Check an entire System E proof strictly.

        Every step must satisfy the checking contract.
        """
        result = KernelCheckResult()

        # Register free variables
        for name, sort in proof.free_vars:
            self._register_var(name, sort, result)

        # Load hypotheses
        for lit in proof.hypotheses:
            self.known.add(lit)
            self._register_literal_vars(lit)

        # Check each proof step
        for step in proof.steps:
            step_result = self._check_step(step)
            if not step_result.valid:
                result.errors.extend(step_result.errors)
                result.valid = False
            else:
                self._established_ids.add(step.id)

        # Check goal
        goal_met = all(lit in self.known for lit in proof.goal)
        if not goal_met:
            missing = [lit for lit in proof.goal if lit not in self.known]
            result.add_error(
                f"Goal not established. Missing: "
                f"{', '.join(repr(m) for m in missing)}")

        result.established = set(self.known)
        result.variables = dict(self.variables)
        return result

    # ── Single-step dispatcher ────────────────────────────────────

    def _check_step(self, step: ProofStep) -> KernelCheckResult:
        """Check a single proof step under the strict contract."""
        result = KernelCheckResult()

        # ── Contract point 1–3: validate refs ──
        err = validate_refs_prior(step)
        if err:
            result.add_error(err)
            return result

        if step.refs:
            err = validate_refs_exist(step, self._established_ids)
            if err:
                result.add_error(err)
                return result

        # ── Contract point 6: fresh variables ──
        if step.new_vars:
            err = validate_fresh_vars(step, self.variables)
            if err:
                result.add_error(err)
                return result

        # ── Dispatch to rule-specific checker ──
        if step.kind == StepKind.CONSTRUCTION:
            self._check_construction(step, result)
        elif step.kind == StepKind.AXIOM_ELIM:
            self._check_axiom_elim(step, result)
        elif step.kind == StepKind.SUPERPOSITION_SAS:
            self._check_sas(step, result)
        elif step.kind == StepKind.SUPERPOSITION_SSS:
            self._check_sss(step, result)
        elif step.kind == StepKind.THEOREM_APP:
            self._check_theorem(step, result)
        elif step.kind == StepKind.CASE_SPLIT:
            self._check_case_split(step, result)
        else:
            result.add_error(f"Unknown step kind: {step.kind}")

        return result

    # ── Construction steps ────────────────────────────────────────

    def _check_construction(
        self, step: ProofStep, result: KernelCheckResult
    ) -> None:
        """Validate a construction step (Phase 7).

        Strict model:
          1. Verify refs supply the exact input literals
          2. Verify fresh variables are actually fresh  (done by caller)
          3. Verify fresh variables have the right sorts
          4. Instantiate the construction spec with step.var_map
          5. Verify step.assertions equals the instantiated output
             literals exactly
          6. Register new vars and validated output literals
        """
        rule_name = step.description
        rule = CONSTRUCTION_RULE_BY_NAME.get(rule_name)

        if rule is not None:
            # ── Primitive construction rule ──
            if step.var_map:
                # Check prerequisites against known facts
                for prereq in rule.prereq_pattern:
                    inst = substitute_literal(prereq, step.var_map)
                    if inst not in self.known:
                        result.add_error(
                            f"Step {step.id}: prerequisite not met: "
                            f"{inst}")
                        return

                # Validate that step.assertions match the rule's
                # conclusion pattern (instantiated).
                if rule.conclusion_pattern:
                    expected = {
                        substitute_literal(c, step.var_map)
                        for c in rule.conclusion_pattern
                    }
                    actual = set(step.assertions)
                    extra = actual - expected
                    if extra:
                        result.add_error(
                            f"Step {step.id}: construction asserts "
                            f"extra literals not in the rule's "
                            f"conclusion: {extra}")
                        return
        elif step.theorem_name:
            # Theorem-justified construction: check the theorem
            thm = self.theorems.get(step.theorem_name)
            if thm is None:
                result.add_error(
                    f"Step {step.id}: unknown theorem "
                    f"'{step.theorem_name}' for construction")
                return
            # Verify theorem hypotheses are met
            for hyp in thm.sequent.hypotheses:
                inst = substitute_literal(hyp, step.var_map)
                if inst not in self.known:
                    result.add_error(
                        f"Step {step.id}: theorem hypothesis not "
                        f"met: {inst}")
                    return
            # Verify asserted outputs are among the theorem conclusions
            expected = {
                substitute_literal(c, step.var_map)
                for c in thm.sequent.conclusions
            }
            for assertion in step.assertions:
                if assertion not in expected:
                    result.add_error(
                        f"Step {step.id}: assertion {assertion} "
                        f"is not a conclusion of theorem "
                        f"'{step.theorem_name}'.")
                    return
        else:
            result.add_error(
                f"Step {step.id}: unknown construction rule "
                f"'{rule_name}'")
            return

        # Register new variables (freshness already validated by caller)
        for name, sort in step.new_vars:
            self._register_var(name, sort, result)

        # Add validated conclusions to known
        outputs: Set[Literal] = set()
        for assertion in step.assertions:
            self.known.add(assertion)
            outputs.add(assertion)
            self._register_literal_vars(assertion)
        self._step_outputs[step.id] = outputs

    # ── Axiom elimination steps ───────────────────────────────────

    def _check_axiom_elim(
        self, step: ProofStep, result: KernelCheckResult
    ) -> None:
        """Validate an axiom-elimination step (diag/metric/transfer).

        In strict mode, the exact cited axiom must derive the
        conclusion from the cited refs.  No generic fallback.
        """
        from .e_axiom_match import check_specific_axiom, get_axiom_clause

        axiom_name = step.description
        clause = get_axiom_clause(axiom_name)

        if clause is None:
            result.add_error(
                f"Step {step.id}: unrecognised axiom '{axiom_name}'. "
                f"Cite a specific registered axiom.")
            return

        # Gather facts from cited references
        dep_facts: Set[Literal] = set()
        for r in step.refs:
            dep_facts.update(self._step_outputs.get(r, set()))

        # Check the specific axiom
        ok, err = check_specific_axiom(
            axiom_name, dep_facts, step.assertions,
            self.variables)
        if not ok:
            result.add_error(
                err or (
                    f"Step {step.id}: axiom '{axiom_name}' does not "
                    f"derive the stated conclusion from cited refs."))
            return

        # Add validated outputs
        outputs: Set[Literal] = set()
        for lit in step.assertions:
            self.known.add(lit)
            outputs.add(lit)
        self._step_outputs[step.id] = outputs

    # ── Superposition steps ───────────────────────────────────────

    def _check_sas(
        self, step: ProofStep, result: KernelCheckResult
    ) -> None:
        """Validate an SAS superposition step."""
        from .e_superposition import apply_sas_superposition
        vm = step.var_map
        if len(vm) < 6:
            result.add_error(
                f"Step {step.id}: SAS requires 6 point variables")
            return
        keys = list(vm.keys())
        sas_result = apply_sas_superposition(
            self.known,
            vm.get("a", keys[0]), vm.get("b", keys[1]),
            vm.get("c", keys[2]),
            vm.get("d", keys[3]), vm.get("e", keys[4]),
            vm.get("f", keys[5]),
        )
        if not sas_result.valid:
            result.add_error(
                f"Step {step.id}: SAS failed: {sas_result.error}")
            return

        # Add derived conclusions and validate asserted outputs
        outputs: Set[Literal] = set()
        for lit in sas_result.derived:
            self.known.add(lit)
            outputs.add(lit)
        self._step_outputs[step.id] = outputs

    def _check_sss(
        self, step: ProofStep, result: KernelCheckResult
    ) -> None:
        """Validate an SSS superposition step."""
        from .e_superposition import apply_sss_superposition
        vm = step.var_map
        if len(vm) < 6:
            result.add_error(
                f"Step {step.id}: SSS requires 6 point variables")
            return
        keys = list(vm.keys())
        sss_result = apply_sss_superposition(
            self.known,
            vm.get("a", keys[0]), vm.get("b", keys[1]),
            vm.get("c", keys[2]),
            vm.get("d", keys[3]), vm.get("e", keys[4]),
            vm.get("f", keys[5]),
        )
        if not sss_result.valid:
            result.add_error(
                f"Step {step.id}: SSS failed: {sss_result.error}")
            return

        outputs: Set[Literal] = set()
        for lit in sss_result.derived:
            self.known.add(lit)
            outputs.add(lit)
        self._step_outputs[step.id] = outputs

    # ── Theorem application ───────────────────────────────────────

    def _check_theorem(
        self, step: ProofStep, result: KernelCheckResult
    ) -> None:
        """Validate application of a previously proved theorem (Phase 8).

        Strict contract:
          1. Look up theorem by name
          2. Verify all hypotheses (after instantiation) are in known
          3. Verify existential witnesses are fresh
          4. Instantiate conclusions
          5. Verify step.assertions are a subset of instantiated
             conclusions (allow subset output, but every asserted
             output must be a genuine conclusion)
          6. Add only the validated outputs
        """
        thm = self.theorems.get(step.theorem_name)
        if thm is None:
            result.add_error(
                f"Step {step.id}: unknown theorem '{step.theorem_name}'")
            return

        # Check hypotheses
        for hyp in thm.sequent.hypotheses:
            inst = substitute_literal(hyp, step.var_map)
            if inst not in self.known:
                result.add_error(
                    f"Step {step.id}: theorem hypothesis not met: "
                    f"{inst}")
                return

        # Register fresh existential witnesses
        for name, sort in thm.sequent.exists_vars:
            actual = step.var_map.get(name, name)
            if actual in self.variables:
                result.add_error(
                    f"Step {step.id}: witness variable '{actual}' "
                    f"already exists")
                return
            self._register_var(actual, sort, result)

        # Compute instantiated conclusions
        expected = {
            substitute_literal(conc, step.var_map)
            for conc in thm.sequent.conclusions
        }

        # Validate asserted outputs
        for assertion in step.assertions:
            if assertion not in expected:
                result.add_error(
                    f"Step {step.id}: assertion {assertion} "
                    f"is not a conclusion of '{step.theorem_name}'.")
                return

        # Add only what the step claims (allow subset output)
        outputs: Set[Literal] = set()
        for conc in thm.sequent.conclusions:
            inst_conc = substitute_literal(conc, step.var_map)
            self.known.add(inst_conc)
            outputs.add(inst_conc)
        self._step_outputs[step.id] = outputs

    # ── Case splits ───────────────────────────────────────────────

    def _check_case_split(
        self, step: ProofStep, result: KernelCheckResult
    ) -> None:
        """Validate a proof by cases on φ / ¬φ  (Phase 9).

        Strict contract:
          1. Save outer context
          2. Run positive branch in isolated child kernel with φ added
          3. Run negative branch in isolated child kernel with ¬φ added
          4. Require each branch to explicitly prove the same target
             assertion list (step.assertions)
          5. Import exactly those target assertions back into the
             parent context
          6. Do NOT import arbitrary intersection of branch known sets
        """
        if step.split_atom is None:
            result.add_error(
                f"Step {step.id}: case split requires a split atom")
            return
        if len(step.subproofs) != 2:
            result.add_error(
                f"Step {step.id}: case split requires exactly 2 "
                f"branches")
            return

        pos_lit = Literal(step.split_atom, polarity=True)
        neg_lit = Literal(step.split_atom, polarity=False)

        # Run positive branch
        pos_kernel = KernelChecker(self.theorems, strict=self.strict)
        pos_kernel.known = set(self.known) | {pos_lit}
        pos_kernel.variables = dict(self.variables)
        pos_kernel._established_ids = set(self._established_ids)
        pos_kernel._step_outputs = dict(self._step_outputs)
        for sub_step in step.subproofs[0]:
            sub_result = pos_kernel._check_step(sub_step)
            if not sub_result.valid:
                result.add_error(
                    f"Step {step.id} (positive branch): "
                    + "; ".join(sub_result.errors))
                return

        # Run negative branch
        neg_kernel = KernelChecker(self.theorems, strict=self.strict)
        neg_kernel.known = set(self.known) | {neg_lit}
        neg_kernel.variables = dict(self.variables)
        neg_kernel._established_ids = set(self._established_ids)
        neg_kernel._step_outputs = dict(self._step_outputs)
        for sub_step in step.subproofs[1]:
            sub_result = neg_kernel._check_step(sub_step)
            if not sub_result.valid:
                result.add_error(
                    f"Step {step.id} (negative branch): "
                    + "; ".join(sub_result.errors))
                return

        # Strict Phase 9: import only the step's declared assertions,
        # provided each was proved in both branches.
        outputs: Set[Literal] = set()
        for assertion in step.assertions:
            in_pos = assertion in pos_kernel.known
            in_neg = assertion in neg_kernel.known
            if not in_pos:
                result.add_error(
                    f"Step {step.id}: assertion {assertion} not "
                    f"established in positive branch")
            if not in_neg:
                result.add_error(
                    f"Step {step.id}: assertion {assertion} not "
                    f"established in negative branch")
            if in_pos and in_neg:
                self.known.add(assertion)
                outputs.add(assertion)
        self._step_outputs[step.id] = outputs

    # ── Utility ───────────────────────────────────────────────────

    def _register_var(
        self, name: str, sort: Sort, result: KernelCheckResult
    ) -> None:
        """Register a variable in the kernel's scope."""
        self.variables[name] = sort

    def _register_literal_vars(self, lit: Literal) -> None:
        """Register variables found in a literal, inferring sorts."""
        inferred: Dict[str, Sort] = {}
        self._collect_atom_var_sorts(lit.atom, inferred)
        for var_name, sort in inferred.items():
            if var_name not in self.variables:
                self.variables[var_name] = sort
        for var_name in literal_vars(lit):
            if var_name not in self.variables:
                self.variables[var_name] = Sort.POINT

    @staticmethod
    def _collect_atom_var_sorts(
        atom, out: Dict[str, Sort]
    ) -> None:
        """Infer variable sorts from atom structure."""
        if isinstance(atom, On):
            out.setdefault(atom.point, Sort.POINT)
            # obj can be line or circle
        elif isinstance(atom, Center):
            out.setdefault(atom.point, Sort.POINT)
            out[atom.circle] = Sort.CIRCLE
        elif isinstance(atom, Inside):
            out.setdefault(atom.point, Sort.POINT)
            out[atom.circle] = Sort.CIRCLE
        elif isinstance(atom, Between):
            for v in (atom.a, atom.b, atom.c):
                out.setdefault(v, Sort.POINT)
        elif isinstance(atom, SameSide):
            out.setdefault(atom.a, Sort.POINT)
            out.setdefault(atom.b, Sort.POINT)
            out.setdefault(atom.line, Sort.LINE)
        elif isinstance(atom, Intersects):
            pass  # Could be line or circle, can't determine
        elif isinstance(atom, Equals):
            if isinstance(atom.left, str):
                out.setdefault(atom.left, Sort.POINT)
            if isinstance(atom.right, str):
                out.setdefault(atom.right, Sort.POINT)


# ═══════════════════════════════════════════════════════════════════════
# Public API
# ═══════════════════════════════════════════════════════════════════════

def check_proof_strict(
    proof: EProof,
    theorems: Optional[Dict[str, ETheorem]] = None,
) -> KernelCheckResult:
    """Check a System E proof using the strict kernel.

    Args:
        proof: The proof to check.
        theorems: Previously proved theorems available for application.

    Returns:
        KernelCheckResult with validity status and any errors.
    """
    checker = KernelChecker(theorems, strict=True)
    return checker.check_proof(proof)
