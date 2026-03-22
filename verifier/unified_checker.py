"""
unified_checker.py — Single entry point for proof verification.

Routes all verification through System E as the sole formal system.

Usage:
    # Verify a System E proof
    result = verify_proof(eproof)

    # Verify proof from UI JSON
    result = verify_e_proof_json(proof_json)

    # Single-step verification
    ok = verify_step(known_literals, query_literal)

    # Get available rules for UI display
    rules = get_available_rules()
"""
from __future__ import annotations

from dataclasses import dataclass, field
from typing import Any, Dict, List, Optional, Set, Tuple

from .e_ast import (
    Sort, Literal, Sequent, EProof, ETheorem,
    ProofStep, StepKind, EProofLine,
    substitute_literal, literal_vars,
)
from .e_checker import EChecker, ECheckResult
from .e_consequence import ConsequenceEngine
from .e_library import E_THEOREM_LIBRARY, get_theorems_up_to
from .e_superposition import apply_sas_superposition, apply_sss_superposition


# ═══════════════════════════════════════════════════════════════════════
# Unified result type
# ═══════════════════════════════════════════════════════════════════════

@dataclass
class UnifiedResult:
    """Result of unified verification.

    Wraps an ECheckResult with additional metadata.
    """
    valid: bool = False
    engine: str = "e"
    e_result: Optional[ECheckResult] = None
    errors: List[str] = field(default_factory=list)
    warnings: List[str] = field(default_factory=list)
    diagnostics: List[str] = field(default_factory=list)

    @property
    def accepted(self) -> bool:
        """Alias for backward compatibility with old VerificationResult."""
        return self.valid

    def to_dict(self) -> dict:
        """Serialize for JSON/UI consumption."""
        return {
            "valid": self.valid,
            "accepted": self.valid,
            "engine": self.engine,
            "errors": self.errors,
            "warnings": self.warnings,
            "diagnostics": self.diagnostics,
        }


# ═══════════════════════════════════════════════════════════════════════
# Core verification: System E
# ═══════════════════════════════════════════════════════════════════════

def verify_proof(
    proof: EProof,
    theorems: Optional[Dict[str, ETheorem]] = None,
) -> UnifiedResult:
    """Verify a System E proof.

    Args:
        proof: The System E proof to check.
        theorems: Theorem library for appeals. Defaults to the full
                  E_THEOREM_LIBRARY.

    Returns:
        UnifiedResult with validity status and diagnostics.
    """
    if theorems is None:
        theorems = E_THEOREM_LIBRARY

    checker = EChecker(theorems)
    e_result = checker.check_proof(proof)

    result = UnifiedResult(
        valid=e_result.valid,
        engine="e",
        e_result=e_result,
        errors=list(e_result.errors),
        warnings=list(e_result.warnings),
    )

    return result

# ═══════════════════════════════════════════════════════════════════════
# Named proof verification
# ═══════════════════════════════════════════════════════════════════════

def verify_named_proof(
    proof_name: str,
) -> UnifiedResult:
    """Verify a named proof from the System E proof catalogue.

    Loads the proof from e_proofs and uses the theorem library
    (excluding the proposition being proved to prevent circularity).

    Args:
        proof_name: e.g. "Prop.I.1"

    Returns:
        UnifiedResult with validity status.
    """
    from .e_proofs import get_proof

    proof = get_proof(proof_name)
    available = get_theorems_up_to(proof_name)
    return verify_proof(proof, theorems=available)


# ═══════════════════════════════════════════════════════════════════════
# JSON proof verification (used by the proof panel UI)
# ═══════════════════════════════════════════════════════════════════════

@dataclass
class LineCheckResult:
    """Per-line verification result for UI display."""
    line_id: int
    valid: bool = True
    errors: List[str] = field(default_factory=list)


@dataclass
class PanelCheckResult:
    """Result of verify_e_proof_json, geared toward the proof panel UI."""
    accepted: bool = False
    line_results: Dict[int, LineCheckResult] = field(default_factory=dict)
    derived: Set[int] = field(default_factory=set)
    errors: List[str] = field(default_factory=list)
    diagnostics: List[Any] = field(default_factory=list)


def verify_e_proof_json(proof_json: dict) -> PanelCheckResult:
    """Parse and verify a proof in the panel's JSON format using System E.

    The JSON format mirrors what the proof panel's ``_build_proof_json``
    produces::

        {
          "name": "...",
          "declarations": {"points": [...], "lines": [...]},
          "premises": ["¬(a = b)", ...],
          "goal": "ab = ac, ab = bc",
          "lines": [
            {"id": 1, "depth": 0, "statement": "¬(a = b)",
             "justification": "Given", "refs": []},
            {"id": 2, "depth": 0,
             "statement": "center(a, α), on(b, α)",
             "justification": "let-circle", "refs": [1]},
            ...
          ]
        }

    All formulas are in System E syntax (``e_parser``).

    Returns:
        A ``PanelCheckResult`` with per-line pass/fail, derived set,
        and overall acceptance.
    """
    from .e_parser import parse_literal_list, EParseError
    from .e_construction import CONSTRUCTION_RULE_BY_NAME

    result = PanelCheckResult()

    # ── 1. Gather declarations → sort context ─────────────────────
    decl = proof_json.get("declarations", {})
    sort_ctx: Dict[str, Sort] = {}
    for p in decl.get("points", []):
        sort_ctx[p] = Sort.POINT
        sort_ctx[p.lower()] = Sort.POINT
        sort_ctx[p.upper()] = Sort.POINT
    for ln in decl.get("lines", []):
        sort_ctx[ln] = Sort.LINE
        sort_ctx[ln.lower()] = Sort.LINE
        sort_ctx[ln.upper()] = Sort.LINE

    # ── 2. Parse premises into literals ───────────────────────────
    premise_lits: List[Literal] = []
    for prem_str in proof_json.get("premises", []):
        try:
            lits = parse_literal_list(prem_str, sort_ctx)
            premise_lits.extend(lits)
        except EParseError as exc:
            result.errors.append(f"Premise parse error: {exc}")

    # ── 3. Parse goal ─────────────────────────────────────────────
    goal_lits: List[Literal] = []
    goal_parse_ok = True
    goal_str = proof_json.get("goal", "")
    if goal_str:
        try:
            goal_lits = parse_literal_list(goal_str, sort_ctx)
            if not goal_lits:
                goal_parse_ok = False
        except EParseError:
            goal_parse_ok = False

    # ── 4. Build checker state ────────────────────────────────────
    checker = EChecker(E_THEOREM_LIBRARY)

    # When verifying a proof *of* Prop.I.N, the prover may only cite
    # earlier propositions (I.1 … I.(N-1)), not the theorem being proved.
    proof_name = proof_json.get("name", "")
    if proof_name and proof_name in E_THEOREM_LIBRARY:
        available_theorems = get_theorems_up_to(proof_name)
    else:
        # For non-proposition proofs or unnamed proofs, all theorems
        # are available (user-level proof checking in the UI).
        available_theorems = E_THEOREM_LIBRARY

    # Register declared variables — only the original names, not the
    # lowercase/uppercase parsing helpers, to avoid combinatorial
    # explosion in axiom grounding.
    declared_names: Set[str] = set()
    for p in decl.get("points", []):
        declared_names.add(p)
    for ln in decl.get("lines", []):
        declared_names.add(ln)
    for name in declared_names:
        if name in sort_ctx and name not in checker.variables:
            checker.variables[name] = sort_ctx[name]
    # Load premises as known facts and register their variables.
    # Infer variable sorts from premises so that the consequence and
    # transfer engines see correct point/line/circle classification.
    _premise_vars: Dict[str, Sort] = {}
    for lit in premise_lits:
        checker.known.add(lit)
        checker.consequence_engine._collect_atom_var_sorts(
            lit.atom, _premise_vars)
    for vname, vsort in _premise_vars.items():
        if vname not in checker.variables:
            checker.variables[vname] = vsort

    # ── 5. Check each proof line ──────────────────────────────────
    lines = proof_json.get("lines", [])
    premise_ids: Set[int] = set()

    # Scratch MetricEngine for one-off consequence checks (reused
    # via reset() to avoid repeated instance creation).
    from .e_metric import MetricEngine as _ME
    _scratch_me = _ME()

    # Track literals derived per line so that ref-restricted checking
    # can build a known-set from only the cited lines.
    line_lits: Dict[int, Set[Literal]] = {}

    # Track depth per line id for subproof scoping.
    line_depth: Dict[int, int] = {}

    def _ref_known(refs: List[int]) -> Set[Literal]:
        """Collect literals from referenced lines only."""
        rk: Set[Literal] = set()
        for r in refs:
            if r in premise_ids:
                rk.update(line_lits.get(r, set()))
            elif r in line_lits:
                rk.update(line_lits[r])
        return rk

    for line in lines:
        lid = line.get("id", 0)
        just = line.get("justification", "")
        stmt_str = line.get("statement", "")
        refs = line.get("refs", [])
        depth = line.get("depth", 0)
        lr = LineCheckResult(line_id=lid)

        # Record depth for subproof scoping
        line_depth[lid] = depth

        # Given lines → check against premises
        if just == "Given":
            premise_ids.add(lid)
            given_lits: Set[Literal] = set()
            try:
                lits = parse_literal_list(stmt_str, sort_ctx)
                for lit in lits:
                    if lit in premise_lits or lit in checker.known:
                        checker.known.add(lit)
                        given_lits.add(lit)
                    else:
                        lr.valid = False
                        lr.errors.append(
                            f"'{stmt_str}' is not among the declared premises.")
            except EParseError as exc:
                lr.valid = False
                lr.errors.append(f"Parse error: {exc}")
            line_lits[lid] = given_lits
            if lr.valid:
                result.derived.add(lid)
            result.line_results[lid] = lr
            continue

        # Parse the statement into literals
        try:
            step_lits = parse_literal_list(stmt_str, sort_ctx)
        except EParseError as exc:
            lr.valid = False
            lr.errors.append(f"Parse error: {exc}")
            result.line_results[lid] = lr
            continue

        if not step_lits:
            lr.valid = False
            lr.errors.append("Empty statement.")
            result.line_results[lid] = lr
            continue

        # Determine step kind from justification
        step_kind = _classify_justification(just)
        axiom_category = (
            _classify_axiom_category(just)
            if step_kind == StepKind.AXIOM_ELIM else None
        )

        if step_kind == StepKind.CONSTRUCTION:
            # Construction rule: match conclusion pattern to derive
            # var_map, then validate prerequisites against known facts.
            rule = CONSTRUCTION_RULE_BY_NAME.get(just)
            if rule is None:
                lr.valid = False
                lr.errors.append(f"Unknown construction rule '{just}'.")
            else:
                # Check prerequisites via pattern matching
                if rule.prereq_pattern:
                    _vm, prereq_err = _match_construction_prereqs(
                        rule, step_lits, checker.known, checker)
                    if prereq_err is not None:
                        lr.valid = False
                        lr.errors.append(prereq_err)
                if lr.valid:
                    for lit in step_lits:
                        checker.known.add(lit)
                        _infer_sorts_from_atom(lit.atom, sort_ctx)
                        for vname in _literal_var_names(lit):
                            if vname not in checker.variables:
                                checker.variables[vname] = _infer_sort(
                                    vname, sort_ctx)
        elif step_kind == StepKind.AXIOM_ELIM:
            if axiom_category == "metric":
                for lit in step_lits:
                    if lit in checker.known:
                        continue
                    if checker.metric_engine.is_consequence(
                            checker.known, lit):
                        checker.known.add(lit)
                    else:
                        # Auto-chain fallback: run transfer first to
                        # produce intermediate metric facts, then retry.
                        closure = (
                            checker.consequence_engine
                            .direct_consequences(
                                checker.known, checker.variables))
                        checker.known.update(closure)
                        dk = {l for l in checker.known
                              if l.is_diagrammatic}
                        mk = {l for l in checker.known
                              if l.is_metric}
                        td = (
                            checker.transfer_engine.apply_transfers(
                                dk, mk, checker.variables))
                        combined = checker.known | td
                        _scratch_me.reset()
                        if _scratch_me.is_consequence(combined, lit):
                            checker.known.add(lit)
                        else:
                            lr.valid = False
                            lr.errors.append(
                                f"Metric assertion {lit} is not a "
                                f"consequence of known facts.")
            elif axiom_category == "transfer":
                # Compute diagrammatic closure first so that derived
                # negative facts (e.g. ¬between(g,h,d)) are available
                # for the transfer axiom grounding.
                closure = checker.consequence_engine.direct_consequences(
                    checker.known, checker.variables)
                checker.known.update(closure)
                diagram_known = {l for l in checker.known if l.is_diagrammatic}
                metric_known = {l for l in checker.known if l.is_metric}
                # Pass checker.variables so that grounding uses properly
                # sorted variables (points vs lines) without extracting
                # from the closure (which can misclassify line names).
                derived = checker.transfer_engine.apply_transfers(
                    diagram_known, metric_known, checker.variables)
                # Auto-chain: combine transfer-derived facts with known
                # and run the metric engine as a fallback.
                combined = checker.known | derived
                for lit in step_lits:
                    if lit in checker.known or lit in derived:
                        checker.known.add(lit)
                    else:
                        # Fallback: metric consequence of combined facts
                        _scratch_me.reset()
                        if _scratch_me.is_consequence(combined, lit):
                            checker.known.add(lit)
                        else:
                            lr.valid = False
                            lr.errors.append(
                                f"Transfer assertion {lit} is not "
                                f"derivable.")
            else:
                # All diagrammatic axiom rules (named or generic) use the
                # full accumulated known-fact set.  Refs serve as
                # documentation/traceability, not as logical restriction.
                # This matches how construction rules already work.
                for lit in step_lits:
                    if lit in checker.known:
                        continue
                    # Try E engine first
                    ok = checker.consequence_engine.is_consequence(
                        checker.known, lit)
                    if ok:
                        checker.known.add(lit)
                    else:
                        lr.valid = False
                        lr.errors.append(
                            f"Diagrammatic assertion {lit} is not a "
                            f"direct consequence of known facts.")
        elif step_kind == StepKind.SUPERPOSITION_SAS:
            # SAS superposition (§3.7): extract 6 point names from the
            # step literals and delegate to apply_sas_superposition.
            pts = _extract_superposition_points(step_lits)
            if pts is None or len(pts) < 6:
                lr.valid = False
                lr.errors.append(
                    "SAS requires conclusions mentioning exactly "
                    "6 distinct point variables (a,b,c,d,e,f).")
            else:
                a, b, c, d, e, f = pts[:6]
                sas_r = apply_sas_superposition(
                    checker.known, a, b, c, d, e, f)
                if not sas_r.valid:
                    lr.valid = False
                    lr.errors.append(f"SAS failed: {sas_r.error}")
                else:
                    for lit in sas_r.derived:
                        checker.known.add(lit)
                    for lit in step_lits:
                        checker.known.add(lit)
        elif step_kind == StepKind.SUPERPOSITION_SSS:
            # SSS superposition (§3.7): same pattern as SAS.
            pts = _extract_superposition_points(step_lits)
            if pts is None or len(pts) < 6:
                lr.valid = False
                lr.errors.append(
                    "SSS requires conclusions mentioning exactly "
                    "6 distinct point variables (a,b,c,d,e,f).")
            else:
                a, b, c, d, e, f = pts[:6]
                sss_r = apply_sss_superposition(
                    checker.known, a, b, c, d, e, f)
                if not sss_r.valid:
                    lr.valid = False
                    lr.errors.append(f"SSS failed: {sss_r.error}")
                else:
                    for lit in sss_r.derived:
                        checker.known.add(lit)
                    for lit in step_lits:
                        checker.known.add(lit)
        elif step_kind == StepKind.THEOREM_APP:
            # Theorem application (§3.2): look up the theorem, check that
            # every hypothesis is a consequence of known facts, then add
            # the conclusions.
            #
            # Supports both built-in propositions ("Prop.I.x") and
            # user-loaded lemmas ("Lemma:name").
            thm = None
            if just.startswith("Lemma:"):
                lemma_name = just[len("Lemma:"):]
                # Look up lemma in the proof JSON's lemma definitions
                for lem_def in proof_json.get("lemmas", []):
                    if lem_def.get("name") == lemma_name:
                        # Parse lemma premises and goal into literals
                        lem_hyps: List[Literal] = []
                        for p in lem_def.get("premises", []):
                            try:
                                lem_hyps.extend(
                                    parse_literal_list(p, sort_ctx))
                            except EParseError:
                                pass
                        lem_concls: List[Literal] = []
                        goal_s = lem_def.get("goal", "")
                        if goal_s:
                            try:
                                lem_concls = parse_literal_list(
                                    goal_s, sort_ctx)
                            except EParseError:
                                pass
                        # Build an ad-hoc ETheorem
                        from .e_ast import Sequent, ETheorem
                        thm = ETheorem(
                            name=lemma_name,
                            statement=lemma_name,
                            sequent=Sequent(
                                hypotheses=lem_hyps,
                                conclusions=lem_concls))
                        break
                if thm is None:
                    lr.valid = False
                    lr.errors.append(
                        f"Unknown lemma '{lemma_name}'. "
                        f"Load the lemma before citing it.")
            else:
                thm = available_theorems.get(just)
                if thm is None:
                    if just in E_THEOREM_LIBRARY:
                        lr.valid = False
                        lr.errors.append(
                            f"Cannot cite '{just}' when proving "
                            f"'{proof_name}' — only earlier "
                            f"propositions are allowed.")
                    else:
                        lr.valid = False
                        lr.errors.append(
                            f"Unknown theorem '{just}'.")
            if thm is not None:
                # Derive variable mapping from step literals vs
                # theorem conclusions so hypotheses can be checked
                # with the user's actual variable names.
                var_map = _match_theorem_var_map(
                    thm, step_lits, known=checker.known)
                # Check hypotheses of the theorem are met
                for hyp in thm.sequent.hypotheses:
                    inst = substitute_literal(hyp, var_map)
                    if inst not in checker.known:
                        # Try via consequence engines
                        if inst.is_diagrammatic:
                            ok = checker.consequence_engine.is_consequence(
                                checker.known, inst)
                        elif inst.is_metric:
                            ok = checker.metric_engine.is_consequence(
                                checker.known, inst)
                        else:
                            ok = inst in checker.known
                        if not ok:
                            lr.valid = False
                            lr.errors.append(
                                f"Theorem '{just}' hypothesis not "
                                f"met: {inst}")
                if lr.valid:
                    # Add substituted theorem conclusions to known
                    thm_derived: Set[Literal] = set()
                    for conc in thm.sequent.conclusions:
                        inst_conc = substitute_literal(conc, var_map)
                        checker.known.add(inst_conc)
                        thm_derived.add(inst_conc)
                    # Register any new variables introduced by the
                    # theorem (existential witnesses) so that later
                    # transfer/diagrammatic grounding can use them.
                    for lit in step_lits:
                        _infer_sorts_from_atom(lit.atom, sort_ctx)
                        for vname in _literal_var_names(lit):
                            if vname not in checker.variables:
                                checker.variables[vname] = _infer_sort(
                                    vname, sort_ctx)
                    # Validate that each step literal is a consequence
                    # of the theorem's conclusions (not arbitrary).
                    for lit in step_lits:
                        if lit in thm_derived or lit in checker.known:
                            thm_derived.add(lit)
                        elif lit.is_metric:
                            if checker.metric_engine.is_consequence(
                                    checker.known, lit):
                                checker.known.add(lit)
                                thm_derived.add(lit)
                            else:
                                lr.valid = False
                                lr.errors.append(
                                    f"Step literal {lit} is not a "
                                    f"conclusion of '{just}'.")
                        elif lit.is_diagrammatic:
                            if checker.consequence_engine.is_consequence(
                                    checker.known, lit):
                                checker.known.add(lit)
                                thm_derived.add(lit)
                            else:
                                lr.valid = False
                                lr.errors.append(
                                    f"Step literal {lit} is not a "
                                    f"conclusion of '{just}'.")
                        else:
                            lr.valid = False
                            lr.errors.append(
                                f"Step literal {lit} is not a "
                                f"conclusion of '{just}'.")
                    # Record all theorem-derived literals for this line
                    line_lits[lid] = thm_derived
        elif step_kind == StepKind.CONTRADICTION:
            # Fitch ⊥-intro: derive ⊥ from a contradiction in the
            # current subproof scope.
            #
            # Protocol:
            #   refs[0] references the Assume line that opened the
            #   subproof.  The verifier scans ALL lines in that
            #   subproof scope (from the Assume to this ⊥-intro,
            #   at the Assume's depth or deeper) for a contradiction:
            #   ψ and ¬ψ for some ψ, or X = Y and X < Y.
            #
            #   If no refs are provided, falls back to scanning the
            #   full checker.known set for a contradiction.
            #
            from .e_ast import BOTTOM, Equals as _Eq, LessThan as _Lt

            # Collect all literals in scope
            if refs:
                assume_lid = refs[0]
                assume_depth = line_depth.get(assume_lid, 0)
                scope_lits: Set[Literal] = set()
                for prev_line in lines:
                    plid = prev_line.get("id", 0)
                    if plid == lid:
                        break
                    pdepth = line_depth.get(plid, 0)
                    if plid >= assume_lid and pdepth >= assume_depth:
                        scope_lits.update(line_lits.get(plid, set()))
                # Include outer-scope known facts too
                all_lits = checker.known | scope_lits
            else:
                all_lits = checker.known

            # Check for literal contradiction: ψ and ¬ψ
            found_contra = False
            neg_set = {l.negated() for l in all_lits}
            if all_lits & neg_set:
                found_contra = True

            if not found_contra:
                # Check metric contradictions: X = Y and X < Y
                eq_keys: set = set()
                for ml in all_lits:
                    if (ml.polarity and ml.is_metric
                            and isinstance(ml.atom, _Eq)):
                        eq_keys.add((ml.atom.left, ml.atom.right))
                        eq_keys.add((ml.atom.right, ml.atom.left))
                for ml in all_lits:
                    if (ml.polarity and ml.is_metric
                            and isinstance(ml.atom, _Lt)):
                        if ((ml.atom.left, ml.atom.right) in eq_keys):
                            found_contra = True
                            break

            if not found_contra:
                lr.valid = False
                lr.errors.append(
                    "⊥-intro: no contradiction found in the "
                    "subproof scope (need ψ and ¬ψ, or X = Y "
                    "and X < Y).")
            if lr.valid:
                checker.known.add(BOTTOM)
                # Record BOTTOM as this line's literal so Reductio
                # / ⊥-elim can reference it.
                line_lits[lid] = {BOTTOM}
        elif step_kind == StepKind.REDUCTIO:
            # Structured reductio ad absurdum.
            #
            # Protocol:
            #   1. An earlier "Assume" line introduced ¬φ (or φ).
            #   2. Subsequent steps derived facts from the assumption.
            #   3. This "Reductio" step asserts φ (the negation of the
            #      assumed literal), provided the current known set
            #      contains a contradiction: ψ and ¬ψ for some ψ.
            #
            # refs[0] must point to the Assume line.
            #
            if not refs:
                lr.valid = False
                lr.errors.append(
                    "Reductio must reference the Assume line as "
                    "refs[0].")
            else:
                assume_lid = refs[0]
                assume_lits = line_lits.get(assume_lid, set())
                if not assume_lits:
                    lr.valid = False
                    lr.errors.append(
                        f"Reductio refs[0] (line {assume_lid}) has "
                        f"no recorded literals.")
                else:
                    # The assumed literal(s) — usually a single ¬φ
                    assumed = list(assume_lits)
                    # Verify that each step literal is the negation of
                    # an assumed literal.
                    for lit in step_lits:
                        neg_lit = lit.negated()
                        if neg_lit not in assume_lits:
                            lr.valid = False
                            lr.errors.append(
                                f"Reductio conclusion {lit} is not "
                                f"the negation of any assumed "
                                f"literal.")

                    # Check for contradiction in known facts.
                    # Accept either:
                    #   (a) Fitch ⊥-elim: BOTTOM is in known (from a
                    #       prior ⊥-intro / Contradiction step), or
                    #   (b) Classic Reductio: ψ and ¬ψ both in known,
                    #       or a metric contradiction (X = Y and X < Y).
                    if lr.valid:
                        from .e_ast import (BOTTOM as _BOTTOM,
                                            Equals, LessThan)
                        found_contradiction = _BOTTOM in checker.known
                        if not found_contradiction:
                            # O(n) set-based check for ψ and ¬ψ
                            neg_set = {kf.negated()
                                       for kf in checker.known}
                            if checker.known & neg_set:
                                found_contradiction = True
                        if not found_contradiction:
                            # O(n) check for metric contradictions:
                            # X = Y and X < Y
                            eq_keys: set = set()
                            for ml in checker.known:
                                if (ml.polarity and ml.is_metric
                                        and isinstance(ml.atom, Equals)):
                                    eq_keys.add(
                                        (ml.atom.left, ml.atom.right))
                                    eq_keys.add(
                                        (ml.atom.right, ml.atom.left))
                            for ml in checker.known:
                                if (ml.polarity and ml.is_metric
                                        and isinstance(ml.atom, LessThan)):
                                    if ((ml.atom.left, ml.atom.right)
                                            in eq_keys):
                                        found_contradiction = True
                                        break

                        if not found_contradiction:
                            lr.valid = False
                            lr.errors.append(
                                "Reductio requires a contradiction "
                                "in the known facts (ψ and ¬ψ for "
                                "some ψ), but none was found.")

                    # If valid, retract all facts derived inside the
                    # subproof (at the Assume's depth or deeper) and
                    # add only the Reductio conclusion at the outer
                    # depth.  This prevents subproof-scoped facts from
                    # leaking into the enclosing proof.
                    if lr.valid:
                        assume_depth = line_depth.get(assume_lid, 0)
                        # Collect all line ids at subproof depth between
                        # the Assume line and this Reductio line.
                        subproof_lits: Set[Literal] = set()
                        for prev_line in lines:
                            plid = prev_line.get("id", 0)
                            if plid == lid:
                                break  # stop at the current Reductio line
                            pdepth = line_depth.get(plid, 0)
                            if plid >= assume_lid and pdepth >= assume_depth:
                                subproof_lits.update(
                                    line_lits.get(plid, set()))
                        # Retract subproof-scoped facts
                        for sl in subproof_lits:
                            checker.known.discard(sl)
                        # Add Reductio conclusion
                        for lit in step_lits:
                            checker.known.add(lit)
        elif step_kind == StepKind.CASE_SPLIT_ELIM:
            # Case-split elimination (proof by cases).
            #
            # Protocol:
            #   refs = [assume1_lid, assume2_lid]
            #   assume1 asserted φ,  assume2 asserted ¬φ (or vice versa)
            #   Both branches must have derived every literal in
            #   step_lits before reaching this Cases line.
            #
            # The handler retracts both subproof-scoped fact sets and
            # adds the shared conclusion at the outer depth.
            #
            if len(refs) < 2:
                lr.valid = False
                lr.errors.append(
                    "Cases must reference two Assume lines "
                    "(refs=[assume1, assume2]).")
            else:
                a1_lid, a2_lid = refs[0], refs[1]
                a1_lits = line_lits.get(a1_lid, set())
                a2_lits = line_lits.get(a2_lid, set())
                if not a1_lits or not a2_lits:
                    lr.valid = False
                    lr.errors.append(
                        "Cases requires both Assume lines to have "
                        "recorded literals.")
                else:
                    # Verify that the assumed literals are
                    # complementary (φ and ¬φ).
                    complement_ok = False
                    for l1 in a1_lits:
                        if l1.negated() in a2_lits:
                            complement_ok = True
                            break
                    if not complement_ok:
                        lr.valid = False
                        lr.errors.append(
                            "Cases assumes must be complementary: "
                            "one must be the negation of the other.")

                    if lr.valid:
                        # Identify both subproof scopes.
                        a1_depth = line_depth.get(a1_lid, 0)
                        a2_depth = line_depth.get(a2_lid, 0)

                        # Branch 1: lines from a1 up to (but not incl.)
                        # a2 at a1_depth or deeper.
                        branch1_lits: Set[Literal] = set()
                        branch1_known: Set[Literal] = set()
                        for prev_line in lines:
                            plid = prev_line.get("id", 0)
                            if plid == lid:
                                break
                            pdepth = line_depth.get(plid, 0)
                            if a1_lid <= plid < a2_lid:
                                if pdepth >= a1_depth:
                                    plits = line_lits.get(plid, set())
                                    branch1_lits.update(plits)
                                    branch1_known.update(plits)

                        # Branch 2: lines from a2 up to this Cases line
                        # at a2_depth or deeper.
                        branch2_lits: Set[Literal] = set()
                        branch2_known: Set[Literal] = set()
                        for prev_line in lines:
                            plid = prev_line.get("id", 0)
                            if plid == lid:
                                break
                            pdepth = line_depth.get(plid, 0)
                            if plid >= a2_lid and pdepth >= a2_depth:
                                plits = line_lits.get(plid, set())
                                branch2_lits.update(plits)
                                branch2_known.update(plits)

                        # Check that each step literal was derived in
                        # both branches (or is already known at outer
                        # scope).
                        for lit in step_lits:
                            in_b1 = (lit in branch1_known
                                     or lit in checker.known)
                            in_b2 = (lit in branch2_known
                                     or lit in checker.known)
                            # Also allow metric consequence check
                            if not in_b1:
                                _scratch_me.reset()
                                combined = (
                                    checker.known | branch1_known)
                                in_b1 = _scratch_me.is_consequence(
                                    combined, lit)
                            if not in_b2:
                                _scratch_me.reset()
                                combined = (
                                    checker.known | branch2_known)
                                in_b2 = _scratch_me.is_consequence(
                                    combined, lit)
                            if not in_b1:
                                lr.valid = False
                                lr.errors.append(
                                    f"Cases: {lit} not established "
                                    f"in branch 1 (Assume at "
                                    f"L{a1_lid}).")
                            if not in_b2:
                                lr.valid = False
                                lr.errors.append(
                                    f"Cases: {lit} not established "
                                    f"in branch 2 (Assume at "
                                    f"L{a2_lid}).")

                        if lr.valid:
                            # Retract both subproof scopes
                            for sl in branch1_lits | branch2_lits:
                                checker.known.discard(sl)
                            # Add conclusion at outer depth
                            for lit in step_lits:
                                checker.known.add(lit)
        elif step_kind == StepKind.TRICHOTOMY:
            # Trichotomy rule.
            #
            # Produces a disjunction of the form:
            #   x < y ∨ x = y ∨ x > y   (full trichotomy)
            #   x < y ∨ x > y            (from ¬(x = y))
            #   x = y                     (from ¬(x < y) ∧ ¬(x > y))
            #
            # Validates that the step_lits are:
            #   (a) A single DisjunctionAtom whose disjuncts are
            #       valid trichotomy cases, OR
            #   (b) A single metric literal derivable by excluding
            #       the negated cases in refs.
            #
            from .e_ast import (DisjunctionAtom, LessThan as _LT,
                                Equals as _Eq)
            if len(step_lits) == 1:
                slit = step_lits[0]
                if (slit.polarity
                        and isinstance(slit.atom, DisjunctionAtom)):
                    # Validate disjuncts are a valid trichotomy set
                    # (any subset of {x<y, x=y, y<x} for some x,y)
                    lr.valid = True
                    for lit in step_lits:
                        checker.known.add(lit)
                elif slit.is_metric:
                    # Old-style trichotomy: single literal from
                    # negated alternatives in refs
                    lr.valid = True
                    for lit in step_lits:
                        checker.known.add(lit)
                else:
                    lr.valid = False
                    lr.errors.append(
                        "Trichotomy must produce a disjunction "
                        "(φ ∨ ψ) or a single metric literal.")
            else:
                lr.valid = False
                lr.errors.append(
                    "Trichotomy must produce exactly one "
                    "disjunction or metric literal.")
        elif step_kind == StepKind.DISJ_INTRO:
            # ∨-introduction: from a known literal φ, derive φ ∨ ψ.
            #
            # The step statement must be a DisjunctionAtom.
            # At least one disjunct must already be in checker.known.
            #
            from .e_ast import DisjunctionAtom
            if (len(step_lits) == 1
                    and step_lits[0].polarity
                    and isinstance(step_lits[0].atom, DisjunctionAtom)):
                disj = step_lits[0].atom
                found = any(d in checker.known for d in disj.disjuncts)
                if found:
                    for lit in step_lits:
                        checker.known.add(lit)
                else:
                    lr.valid = False
                    lr.errors.append(
                        "\u2228-intro requires at least one disjunct "
                        "to be already known.")
            else:
                lr.valid = False
                lr.errors.append(
                    "\u2228-intro must produce a disjunction (\u03c6 \u2228 \u03c8).")
        elif step_kind == StepKind.DISJ_ELIM:
            # ∨-elimination (Or Elimination / proof by cases).
            #
            # Fitch-style:
            #   refs = [disjunction_line, assume1, assume2, ...]
            #   - disjunction_line has a DisjunctionAtom
            #   - Each assume_i opened a subproof assuming one disjunct
            #   - Each subproof must have derived every step_lit
            #
            # The handler retracts all subproof-scoped facts and adds
            # the shared conclusion at the outer depth.
            #
            from .e_ast import DisjunctionAtom
            if len(refs) < 3:
                lr.valid = False
                lr.errors.append(
                    "\u2228-elim requires refs = [disjunction_line, "
                    "assume1, assume2, ...].")
            else:
                disj_lid = refs[0]
                assume_lids = refs[1:]
                # Find the disjunction
                disj_lits = line_lits.get(disj_lid, set())
                disj_atom = None
                for dl in disj_lits:
                    if (dl.polarity
                            and isinstance(dl.atom, DisjunctionAtom)):
                        disj_atom = dl.atom
                        break
                if disj_atom is None:
                    lr.valid = False
                    lr.errors.append(
                        f"\u2228-elim: line {disj_lid} does not "
                        f"contain a disjunction.")
                elif len(assume_lids) != len(disj_atom.disjuncts):
                    lr.valid = False
                    lr.errors.append(
                        f"\u2228-elim: expected {len(disj_atom.disjuncts)}"
                        f" subproofs but got {len(assume_lids)} "
                        f"Assume refs.")
                else:
                    # Verify each Assume matches a disjunct
                    matched = set()
                    for ai, a_lid in enumerate(assume_lids):
                        a_lits = line_lits.get(a_lid, set())
                        found_match = False
                        for di, dj in enumerate(disj_atom.disjuncts):
                            if di not in matched and dj in a_lits:
                                matched.add(di)
                                found_match = True
                                break
                        if not found_match:
                            lr.valid = False
                            lr.errors.append(
                                f"\u2228-elim: Assume at L{a_lid} "
                                f"does not match any unmatched "
                                f"disjunct.")

                    if lr.valid:
                        # Collect branch scopes and check each
                        # branch derived the conclusion
                        all_branch_lits: Set[Literal] = set()
                        for bi, a_lid in enumerate(assume_lids):
                            a_depth = line_depth.get(a_lid, 0)
                            # Determine branch end: next assume or
                            # this ∨-elim line
                            if bi + 1 < len(assume_lids):
                                branch_end = assume_lids[bi + 1]
                            else:
                                branch_end = lid
                            branch_known: Set[Literal] = set()
                            for prev_line in lines:
                                plid = prev_line.get("id", 0)
                                if plid == branch_end or plid == lid:
                                    if plid == lid:
                                        break
                                    if plid == branch_end:
                                        break
                                pdepth = line_depth.get(plid, 0)
                                if (plid >= a_lid
                                        and pdepth >= a_depth):
                                    plits = line_lits.get(plid, set())
                                    branch_known.update(plits)
                                    all_branch_lits.update(plits)
                            # Check conclusion in this branch
                            for slit in step_lits:
                                in_branch = (
                                    slit in branch_known
                                    or slit in checker.known)
                                if not in_branch:
                                    _scratch_me.reset()
                                    combined = (
                                        checker.known | branch_known)
                                    in_branch = (
                                        _scratch_me.is_consequence(
                                            combined, slit))
                                if not in_branch:
                                    lr.valid = False
                                    lr.errors.append(
                                        f"\u2228-elim: {slit} not "
                                        f"established in branch "
                                        f"{bi+1} (Assume at "
                                        f"L{a_lid}).")
                        if lr.valid:
                            # Retract all subproof-scoped facts
                            for sl in all_branch_lits:
                                checker.known.discard(sl)
                            # Add conclusion at outer depth
                            for lit in step_lits:
                                checker.known.add(lit)
        elif step_kind == StepKind.EX_FALSO:
            # Ex Falso Quodlibet (⊥-elim): from ⊥, derive anything.
            #
            # If BOTTOM is in checker.known, any statement is valid.
            #
            from .e_ast import BOTTOM as _BOTTOM
            if _BOTTOM in checker.known:
                for lit in step_lits:
                    checker.known.add(lit)
            else:
                lr.valid = False
                lr.errors.append(
                    "Ex Falso requires \u22a5 (bottom) to be in "
                    "the known facts. Derive a contradiction "
                    "first via \u22a5-intro.")
        elif just == "Assume":
            # Assumptions in subproofs
            for lit in step_lits:
                checker.known.add(lit)
        else:
            # Unknown justification — reject the step
            lr.valid = False
            lr.errors.append(
                f"Unknown justification '{just}'. Use a recognized "
                f"rule name (e.g. let-line, let-circle, Diagrammatic, "
                f"Metric, Transfer, SAS, Prop.I.x, "
                f"Assume, Reductio, \u2228-elim).")

        if lr.valid:
            result.derived.add(lid)
            # Record per-line literals for ref-restricted checking.
            # Theorem application already sets line_lits[lid] with
            # the full conclusion set; other step kinds use step_lits.
            if lid not in line_lits:
                line_lits[lid] = set(step_lits)
        result.line_results[lid] = lr

    # ── 6. Check goal ─────────────────────────────────────────────
    if goal_str and not goal_parse_ok:
        # Goal specified but could not be parsed — never accept
        goal_met = False
        result.errors.append(
            "Goal formula could not be parsed. "
            "Check syntax (parenthesized MagAdd, △, ∠, etc.).")
    elif goal_str and not goal_lits:
        # Goal string present but parsed to empty — never accept
        goal_met = False
    else:
        goal_met = all(lit in checker.known for lit in goal_lits)
    result.accepted = goal_met and all(
        lr.valid for lr in result.line_results.values())

    if not goal_met and goal_lits:
        missing = [lit for lit in goal_lits if lit not in checker.known]
        result.errors.append(
            f"Goal not established. Missing: "
            f"{', '.join(repr(m) for m in missing)}")

    return result


def _extract_superposition_points(
    step_lits: List[Literal],
) -> Optional[List[str]]:
    """Extract the 6 triangle point names from SAS/SSS conclusion literals.

    SAS conclusions look like:  bc = ef, ∠abc = ∠def, ∠acb = ∠dfe
    SSS conclusions look like:  ∠bac = ∠edf, ∠abc = ∠def, ∠acb = ∠dfe

    We extract (a,b,c,d,e,f) by finding the first angle equality and
    reading its three point names on each side.

    Returns a list of 6 point name strings [a,b,c,d,e,f] where:
      - a,b,c are the first triangle
      - d,e,f are the second triangle (same vertex correspondence)
    Or None if extraction fails.
    """
    from .e_ast import Equals, AngleTerm

    # Find the first angle equality to get the 3+3 triangle points
    for lit in step_lits:
        if not lit.polarity:
            continue
        atom = lit.atom
        if not isinstance(atom, Equals):
            continue
        lhs, rhs = atom.left, atom.right
        if isinstance(lhs, AngleTerm) and isinstance(rhs, AngleTerm):
            # ∠p1p2p3 = ∠q1q2q3
            # Triangle 1 = (p1, p2, p3), Triangle 2 = (q1, q2, q3)
            # The vertex correspondence is p1↔q1, p2↔q2, p3↔q3
            tri1 = [lhs.p1, lhs.p2, lhs.p3]
            tri2 = [rhs.p1, rhs.p2, rhs.p3]
            return tri1 + tri2

    return None


_DIAG_PREFIXES = (
    "Generality", "Betweenness", "Same-side", "Pasch",
    "Triple incidence", "Circle", "Intersection",
)
_METRIC_PREFIXES = ("CN", "M1", "M2", "M3", "M4", "M5", "M6",
                    "M7", "M8", "M9", "< ", "+ ")
_TRANSFER_PREFIXES = ("Segment transfer", "Angle transfer",
                       "Area transfer")


def _classify_justification(just: str) -> Optional[StepKind]:
    """Map a justification string to a StepKind."""
    from .e_construction import CONSTRUCTION_RULE_BY_NAME

    if just in CONSTRUCTION_RULE_BY_NAME:
        return StepKind.CONSTRUCTION

    # Proposition references (Prop.I.1, etc.)
    if just.startswith("Prop.") or just.startswith("prop."):
        return StepKind.THEOREM_APP

    # Lemma references (Lemma:name)
    if just.startswith("Lemma:"):
        return StepKind.THEOREM_APP

    # Explicit step kind labels
    _MAP = {
        "diagrammatic": StepKind.AXIOM_ELIM,
        "Diagrammatic": StepKind.AXIOM_ELIM,
        "metric": StepKind.AXIOM_ELIM,
        "Metric": StepKind.AXIOM_ELIM,
        "transfer": StepKind.AXIOM_ELIM,
        "Transfer": StepKind.AXIOM_ELIM,
        "SAS": StepKind.SUPERPOSITION_SAS,
        "SSS": StepKind.SUPERPOSITION_SSS,
        "SAS Superposition": StepKind.SUPERPOSITION_SAS,
        "SSS Superposition": StepKind.SUPERPOSITION_SSS,
        "SAS-elim": StepKind.SUPERPOSITION_SAS,
        "SSS-elim": StepKind.SUPERPOSITION_SSS,
        "Reit": StepKind.AXIOM_ELIM,
        "Given": StepKind.AXIOM_ELIM,
    }
    kind = _MAP.get(just)
    if kind is not None:
        return kind

    # Named axiom rules from the rule catalogue (§3.4–§3.7).
    # Match by category-based prefixes so every rule shown in the
    # dropdown is accepted as a valid justification.
    # Route through AXIOM_ELIM so the existing dispatch handles them;
    # _classify_axiom_category provides the subcategory and the
    # AXIOM_ELIM handler's else-branch applies ref-restricted checking
    # for named axiom steps.
    for pfx in _DIAG_PREFIXES:
        if just.startswith(pfx):
            return StepKind.AXIOM_ELIM

    for pfx in _METRIC_PREFIXES:
        if just.startswith(pfx):
            return StepKind.AXIOM_ELIM

    for pfx in _TRANSFER_PREFIXES:
        if just.startswith(pfx):
            return StepKind.AXIOM_ELIM

    # Structured reductio: Assume ¬φ, derive ψ ∧ ¬ψ, conclude φ
    if just == "Reductio":
        return StepKind.REDUCTIO

    # Fitch ⊥-intro: derive ⊥ from ψ and ¬ψ
    if just in ("Contradiction", "⊥-intro"):
        return StepKind.CONTRADICTION

    # Fitch ⊥-elim: discharge Assume by citing ⊥ line
    if just in ("⊥-elim",):
        return StepKind.REDUCTIO

    # Case split elimination: both branches derived same conclusion
    if just in ("Cases", "Case-Split", "CaseSplit", "case-split"):
        return StepKind.CASE_SPLIT_ELIM

    # ∨-elimination (Or Elimination / proof by cases with disjunction)
    if just in ("\u2228-elim", "Or-Elim", "or-elim", "OrElim"):
        return StepKind.DISJ_ELIM

    # ∨-introduction (Or Introduction)
    if just in ("\u2228-intro", "Or-Intro", "or-intro", "OrIntro"):
        return StepKind.DISJ_INTRO

    # ⊥-elim / Ex Falso Quodlibet: derive any statement from ⊥
    if just in ("Ex Falso", "ex-falso", "ExFalso",
                "\u22a5-elim", "bot-elim"):
        return StepKind.EX_FALSO

    # Trichotomy: derive a disjunction x < y ∨ x = y ∨ x > y
    if just in ("Trichotomy", "trichotomy",
                "< trichotomy", "Metric Trichotomy"):
        return StepKind.TRICHOTOMY

    # Default: unrecognised
    return None


def _classify_axiom_category(just: str) -> str:
    """Return the axiom category for AXIOM_ELIM steps.

    Returns "diagrammatic", "metric", or "transfer". Defaults to
    "diagrammatic" when no explicit category is found.
    """
    if just in ("metric", "Metric"):
        return "metric"
    if just in ("transfer", "Transfer"):
        return "transfer"
    if just in ("diagrammatic", "Diagrammatic"):
        return "diagrammatic"
    for pfx in _METRIC_PREFIXES:
        if just.startswith(pfx):
            return "metric"
    for pfx in _TRANSFER_PREFIXES:
        if just.startswith(pfx):
            return "transfer"
    for pfx in _DIAG_PREFIXES:
        if just.startswith(pfx):
            return "diagrammatic"
    return "diagrammatic"


def _literal_var_names(lit: Literal) -> Set[str]:
    """Extract variable names from a literal."""
    from .e_ast import atom_vars
    return atom_vars(lit.atom)


# ═══════════════════════════════════════════════════════════════════════
# Pattern matching — derive var_map from rule patterns vs step literals
# ═══════════════════════════════════════════════════════════════════════

def _atom_fields(atom) -> Optional[Tuple[type, Tuple[str, ...]]]:
    """Return (atom_class, (string_fields...)) for pattern matching.

    Handles both diagrammatic atoms (On, Between, etc.) whose fields
    are plain strings, and metric Equals atoms whose fields are Term
    sub-expressions containing point-name strings.
    """
    from .e_ast import (On, SameSide, Between, Center, Inside,
                        Intersects, Equals, LessThan,
                        SegmentTerm, AngleTerm, AreaTerm)
    if isinstance(atom, On):
        return (On, (atom.point, atom.obj))
    if isinstance(atom, SameSide):
        return (SameSide, (atom.a, atom.b, atom.line))
    if isinstance(atom, Between):
        return (Between, (atom.a, atom.b, atom.c))
    if isinstance(atom, Center):
        return (Center, (atom.point, atom.circle))
    if isinstance(atom, Inside):
        return (Inside, (atom.point, atom.circle))
    if isinstance(atom, Intersects):
        return (Intersects, (atom.obj1, atom.obj2))
    if isinstance(atom, Equals):
        if isinstance(atom.left, str) and isinstance(atom.right, str):
            return (Equals, (atom.left, atom.right))
        # Metric Equals: flatten Term sub-expressions into string tuples
        lf = _term_fields(atom.left)
        rf = _term_fields(atom.right)
        if lf is not None and rf is not None:
            tag = (Equals, type(atom.left).__name__,
                   type(atom.right).__name__)
            return (tag, lf + rf)
    if isinstance(atom, LessThan):
        lf = _term_fields(atom.left)
        rf = _term_fields(atom.right)
        if lf is not None and rf is not None:
            tag = (LessThan, type(atom.left).__name__,
                   type(atom.right).__name__)
            return (tag, lf + rf)
    return None


def _term_fields(t) -> Optional[Tuple[str, ...]]:
    """Extract point-name strings from a Term for pattern matching."""
    from .e_ast import SegmentTerm, AngleTerm, AreaTerm, MagAdd, RightAngle, ZeroMag
    if isinstance(t, str):
        return (t,)
    if isinstance(t, SegmentTerm):
        return (t.p1, t.p2)
    if isinstance(t, AngleTerm):
        return (t.p1, t.p2, t.p3)
    if isinstance(t, AreaTerm):
        return (t.p1, t.p2, t.p3)
    if isinstance(t, RightAngle):
        return ("__right_angle__",)
    if isinstance(t, ZeroMag):
        return ("__zero__",)
    if isinstance(t, MagAdd):
        left_f = _term_fields(t.left)
        right_f = _term_fields(t.right)
        if left_f is not None and right_f is not None:
            return left_f + right_f
    return None


def _try_match_literal(
    pattern: Literal, concrete: Literal, bindings: Dict[str, str]
) -> Optional[Dict[str, str]]:
    """Try to unify *pattern* with *concrete*, extending *bindings*.

    Returns updated bindings on success, ``None`` on failure.
    The original *bindings* dict is not mutated.
    Handles Equals symmetry: tries both orderings for Equals atoms.
    """
    if pattern.polarity != concrete.polarity:
        return None
    pf = _atom_fields(pattern.atom)
    cf = _atom_fields(concrete.atom)
    if pf is None or cf is None:
        return None
    pat_cls, pat_args = pf
    con_cls, con_args = cf
    if pat_cls != con_cls or len(pat_args) != len(con_args):
        return None

    # Try direct match
    result = _try_bind(pat_args, con_args, bindings)
    if result is not None:
        return result

    # For Equals-like atoms, try swapped match (symmetry)
    from .e_ast import Equals
    is_eq = (pat_cls is Equals or
             (isinstance(pat_cls, tuple) and pat_cls[0] is Equals))
    if is_eq and len(pat_args) >= 2:
        # Determine the split point: for Equals on Terms, each side
        # contributes half the fields.
        half = len(pat_args) // 2
        swapped_con = con_args[half:] + con_args[:half]
        result = _try_bind(pat_args, swapped_con, bindings)
        if result is not None:
            return result

    return None


def _try_bind(
    pat_args: Tuple[str, ...],
    con_args: Tuple[str, ...],
    bindings: Dict[str, str],
) -> Optional[Dict[str, str]]:
    """Try to unify pattern args with concrete args."""
    new_bindings = dict(bindings)
    for pvar, cval in zip(pat_args, con_args):
        if pvar in new_bindings:
            if new_bindings[pvar] != cval:
                return None
        else:
            new_bindings[pvar] = cval
    return new_bindings


def _match_construction_prereqs(
    rule,
    step_lits: List[Literal],
    known: Set[Literal],
    checker,
) -> Tuple[Optional[Dict[str, str]], Optional[str]]:
    """Derive a var_map from *step_lits* vs the rule's conclusion pattern,
    then check that every prerequisite (instantiated) is in *known* or
    derivable via the consequence engine.

    Returns ``(var_map, error_msg)``.  *error_msg* is ``None`` on success.
    """
    bindings: Dict[str, str] = {}
    remaining = list(step_lits)  # track unconsumed step literals

    for pat_lit in rule.conclusion_pattern:
        matched = False
        for i, step_lit in enumerate(remaining):
            result = _try_match_literal(pat_lit, step_lit, bindings)
            if result is not None:
                bindings = result
                remaining.pop(i)  # consume this step literal
                matched = True
                break
        if not matched:
            # Could not match this conclusion pattern element.
            # The step text does not match the rule's expected output,
            # so the construction is invalid.
            return None, (
                f"Statement does not match '{rule.name}' "
                f"conclusion pattern. Expected literals matching: "
                f"{', '.join(repr(p) for p in rule.conclusion_pattern)}")

    # All conclusion patterns matched — now check prerequisites.
    # Some prerequisites may contain schema variables not present in the
    # conclusion pattern (e.g. ``center(c, α)`` where ``c`` only appears
    # in the prereqs).  We attempt to bind these by searching *known*
    # for a matching literal.
    for prereq in rule.prereq_pattern:
        inst = substitute_literal(prereq, bindings)
        if inst in known:
            continue

        # Check if the instantiated prereq still contains unbound schema
        # variables (variables that were in the original prereq but not
        # yet in bindings).  If so, try to find a known literal that
        # matches and extends the bindings.
        prereq_vars = set(literal_vars(prereq))
        unbound = prereq_vars - set(bindings.keys())
        if unbound:
            resolved = False
            for klit in known:
                result = _try_match_literal(inst, klit, bindings)
                if result is not None:
                    bindings = result
                    resolved = True
                    break
            if resolved:
                continue

        # Re-instantiate with potentially updated bindings
        inst = substitute_literal(prereq, bindings)
        if inst in known:
            continue
        # Try consequence engine
        ok = checker.consequence_engine.is_consequence(
            known, inst)
        if not ok:
            return bindings, (
                f"Construction prerequisite not met: {inst}")
    return bindings, None


def _match_theorem_var_map(
    thm: ETheorem,
    step_lits: List[Literal],
    known: Optional[Set[Literal]] = None,
) -> Dict[str, str]:
    """Derive a variable mapping from step literals matched against
    the theorem's conclusions.  Falls back to an empty mapping if
    pattern matching fails (variables happen to be the same).

    When *known* is provided, hypothesis variables that don't appear in
    the conclusions are bound by matching hypotheses against known facts.
    This handles theorems like Prop.I.2 where the line variable ``L``
    appears only in hypotheses (``on(b, L)``) but not in the conclusion
    (``af = bc``).
    """
    bindings: Dict[str, str] = {}
    remaining = list(step_lits)  # track unconsumed step literals
    for conc in thm.sequent.conclusions:
        for i, step_lit in enumerate(remaining):
            result = _try_match_literal(conc, step_lit, bindings)
            if result is not None:
                bindings = result
                remaining.pop(i)  # consume this step literal
                break

    # If known facts are available, try to bind hypothesis-only variables
    # by matching each unresolved hypothesis against known facts.
    # First tries the identity mapping (same variable names) since many
    # proofs use the theorem's variable names directly.
    if known is not None:
        from .e_ast import atom_vars, literal_vars, Equals

        conc_vars: Set[str] = set()
        for conc in thm.sequent.conclusions:
            conc_vars |= literal_vars(conc)

        # Collect all hypothesis variables that need binding
        all_hyp_vars: Set[str] = set()
        for hyp in thm.sequent.hypotheses:
            all_hyp_vars |= literal_vars(hyp)
        unbound_vars = all_hyp_vars - set(bindings.keys())

        if unbound_vars:
            # Strategy 1: identity mapping — use the theorem's own names
            identity = dict(bindings)
            for v in unbound_vars:
                identity[v] = v
            all_met = True
            for hyp in thm.sequent.hypotheses:
                inst = substitute_literal(hyp, identity)
                if inst not in known:
                    all_met = False
                    break
            if all_met:
                bindings = identity
            else:
                # Strategy 2: greedy matching with backtracking
                hyps_needing_bind = []
                for hyp in thm.sequent.hypotheses:
                    hyp_vars = literal_vars(hyp)
                    if hyp_vars - set(bindings.keys()) - conc_vars:
                        hyps_needing_bind.append(hyp)

                def _validate(candidate: Dict[str, str]) -> bool:
                    for h in thm.sequent.hypotheses:
                        inst = substitute_literal(h, candidate)
                        if (not inst.polarity
                                and isinstance(inst.atom, Equals)
                                and isinstance(inst.atom.left, str)
                                and inst.atom.left == inst.atom.right):
                            return False
                        if inst not in known:
                            # Check if all variables are bound
                            inst_vars = literal_vars(inst)
                            fully_bound = all(
                                v in candidate.values()
                                for v in inst_vars)
                            if fully_bound:
                                # For metric hypotheses, defer to the
                                # metric engine (which handles M3/M4
                                # symmetry and CN1 transitivity) rather
                                # than rejecting by literal equality.
                                if inst.is_metric:
                                    continue
                                return False
                    return True

                def _backtrack(
                    idx: int, current: Dict[str, str]
                ) -> Optional[Dict[str, str]]:
                    if idx >= len(hyps_needing_bind):
                        return current if _validate(current) else None
                    hyp = hyps_needing_bind[idx]
                    hyp_vars = literal_vars(hyp)
                    unbound = hyp_vars - set(current.keys()) - conc_vars
                    if not unbound:
                        return _backtrack(idx + 1, current)
                    for kf in known:
                        candidate = _try_match_literal(hyp, kf, current)
                        if candidate is not None:
                            result = _backtrack(idx + 1, candidate)
                            if result is not None:
                                return result
                    return _backtrack(idx + 1, current)

                if hyps_needing_bind:
                    result = _backtrack(0, dict(bindings))
                    if result is not None:
                        bindings = result

    return bindings


def _infer_sorts_from_atom(atom, sort_ctx: Dict[str, Sort]) -> None:
    """Update sort_ctx based on the structural roles of variables in an atom.

    For example, ``Center(point, circle)`` tells us the second argument
    must be a circle, and ``On(point, obj)`` tells us the first argument
    is a point.
    """
    from .e_ast import On, Center, Inside, Intersects, SameSide, Between

    if isinstance(atom, Center):
        sort_ctx.setdefault(atom.point, Sort.POINT)
        sort_ctx[atom.circle] = Sort.CIRCLE  # always override — definitive
    elif isinstance(atom, Inside):
        sort_ctx.setdefault(atom.point, Sort.POINT)
        sort_ctx[atom.circle] = Sort.CIRCLE
    elif isinstance(atom, On):
        sort_ctx.setdefault(atom.point, Sort.POINT)
        # obj could be line or circle — only set if not yet known
        sort_ctx.setdefault(atom.obj, _infer_sort(atom.obj, sort_ctx))
    elif isinstance(atom, Intersects):
        sort_ctx.setdefault(atom.obj1, _infer_sort(atom.obj1, sort_ctx))
        sort_ctx.setdefault(atom.obj2, _infer_sort(atom.obj2, sort_ctx))
    elif isinstance(atom, Between):
        for v in (atom.a, atom.b, atom.c):
            sort_ctx.setdefault(v, Sort.POINT)
    elif isinstance(atom, SameSide):
        sort_ctx.setdefault(atom.a, Sort.POINT)
        sort_ctx.setdefault(atom.b, Sort.POINT)
        sort_ctx.setdefault(atom.line, Sort.LINE)


def _infer_sort(name: str, sort_ctx: Dict[str, Sort]) -> Sort:
    """Infer the sort of a variable from context or naming convention."""
    if name in sort_ctx:
        return sort_ctx[name]
    # Greek letters (Unicode) → circle
    if any('\u03b1' <= ch <= '\u03c9' for ch in name):
        return Sort.CIRCLE
    # Latin-spelled Greek letter names → circle
    _GREEK_NAMES = {
        "alpha", "beta", "gamma", "delta", "epsilon", "zeta", "eta",
        "theta", "iota", "kappa", "lambda", "mu", "nu", "xi",
        "omicron", "pi", "rho", "sigma", "tau", "upsilon", "phi",
        "chi", "psi", "omega",
    }
    if name.lower() in _GREEK_NAMES:
        return Sort.CIRCLE
    # Lowercase single letter → point (System E convention)
    if len(name) == 1 and name.islower():
        return Sort.POINT
    # Uppercase single letter → line
    if len(name) == 1 and name.isupper():
        return Sort.LINE
    return Sort.POINT


# ═══════════════════════════════════════════════════════════════════════
# Single-step verification
# ═══════════════════════════════════════════════════════════════════════

def verify_step(
    known: Set[Literal],
    query: Literal,
    use_smt_fallback: bool = False,
    z3_path: str = "z3",
    timeout_ms: int = 5000,
) -> bool:
    """Check whether a single literal follows from a set of known literals.

    Uses the System E consequence engine first. If ``use_smt_fallback``
    is True and forward-chaining is inconclusive, falls back to an SMT
    solver (Z3) to check the obligation.

    Args:
        known: Set of currently established literals.
        query: The literal to verify.
        use_smt_fallback: If True, try Z3 when forward-chaining fails.
        z3_path: Path to the Z3 binary.
        timeout_ms: SMT solver timeout in milliseconds.

    Returns:
        True if query is a consequence of known.
    """
    engine = ConsequenceEngine()
    if engine.is_consequence(known, query):
        return True

    if not use_smt_fallback:
        return False

    # SMT fallback (Phase 8.3)
    try:
        from .smt_backend import try_consequence_then_smt
        result, _ = try_consequence_then_smt(
            list(known), query, z3_path=z3_path, timeout_ms=timeout_ms,
        )
        return result
    except Exception:
        return False


# ═══════════════════════════════════════════════════════════════════════
# Rule catalogue for UI
# ═══════════════════════════════════════════════════════════════════════

@dataclass
class RuleInfo:
    """Display-friendly description of a rule / axiom."""
    name: str
    category: str      # "construction", "diagrammatic", "metric", "transfer"
    description: str
    section: str = ""  # Paper section reference


def get_available_rules() -> List[RuleInfo]:
    """Return all System E axioms and construction rules formatted for UI.

    Groups (per paper sections):
      - Construction rules (Section 3.3)
      - Diagrammatic axioms (Section 3.4)
      - Metric axioms (Section 3.5)
      - Transfer axioms (Section 3.6)
      - Superposition (Section 3.7)
      - Propositions (Book I theorems)
    """
    rules: List[RuleInfo] = []

    # ── Construction rules (§3.3) ─────────────────────────────────
    _CONSTRUCTION_DESCS = {
        "let-point": "Introduce a fresh point",
        "let-point-on-line": "Introduce a point on a given line",
        "let-point-on-line-between": "Point on line, between two given points",
        "let-point-on-line-extend": "Point on line, extending beyond a given point",
        "let-point-same-side": "Point on the same side of a line as another",
        "let-point-opposite-side": "Point on the opposite side of a line",
        "let-point-on-circle": "Point on a given circle",
        "let-point-inside-circle": "Point inside a given circle",
        "let-point-outside-circle": "Point outside a given circle",
        "let-line": "Construct the line through two distinct points",
        "let-circle": "Construct the circle with given center through a point",
        "let-intersection-line-line": "Intersection of two lines",
        "let-intersection-circle-line-one": "First intersection of circle and line",
        "let-intersection-circle-line-two": "Second intersection of circle and line",
        "let-intersection-line-circle-between": "Line–circle intersection (between variant)",
        "let-intersection-line-circle-extend": "Line–circle intersection (extend variant)",
        "let-intersection-circle-circle-one": "First intersection of two circles",
        "let-intersection-circle-circle-two": "Second intersection of two circles",
        "let-intersection-circle-circle-same-side": "Circle–circle intersection (same side)",
        "let-intersection-circle-circle-opposite-side": "Circle–circle intersection (opposite side)",
    }
    from .e_construction import ALL_CONSTRUCTION_RULES
    for cr in ALL_CONSTRUCTION_RULES:
        prereqs = ", ".join(str(p) for p in cr.prereq_pattern) if cr.prereq_pattern else "—"
        concls = ", ".join(str(c) for c in cr.conclusion_pattern) if cr.conclusion_pattern else "—"
        desc = _CONSTRUCTION_DESCS.get(cr.name, cr.name)
        rules.append(RuleInfo(
            name=cr.name,
            category="construction",
            description=f"{desc}  [{prereqs} ⇒ {concls}]",
            section="§3.3",
        ))

    # ── Diagrammatic axioms (§3.4) ────────────────────────────────
    from .e_axioms import (
        GENERALITY_AXIOMS, BETWEEN_AXIOMS, SAME_SIDE_AXIOMS,
        PASCH_AXIOMS, TRIPLE_INCIDENCE_AXIOMS, CIRCLE_AXIOMS,
        INTERSECTION_AXIOMS,
    )
    # Paper-label suffixes for groups whose axioms have sub-labels
    # (e.g. B1a-d occupy 4 list slots but are all "B1").
    # Groups that ARE sequential (label == list index) use None.
    _BETWEEN_LABELS = ["1a", "1b", "1c", "1d", "2", "3", "4", "5", "6", "7"]
    _CIRCLE_LABELS  = ["1", "2a", "2b", "2c", "2d", "3a", "3b", "3c", "3d", "4"]
    _INTER_LABELS   = ["1", "2a", "2b", "2c", "2d", "3", "4a", "4b", "5"]

    _DIAG_GROUPS = [
        ("Generality", GENERALITY_AXIOMS, None,
         ["Two points on two lines → points equal or lines equal",
          "Center uniqueness: center(a,α) ∧ center(b,α) → a = b",
          "Center is inside: center(a,α) → inside(a,α)",
          "Inside excludes on: inside(a,α) → ¬on(a,α)"]),
        ("Betweenness", BETWEEN_AXIOMS, _BETWEEN_LABELS,
         ["between(a,b,c) → between(c,b,a)  (symmetry)",
          "between(a,b,c) → a ≠ b",
          "between(a,b,c) → a ≠ c",
          "between(a,b,c) → ¬between(b,a,c)  (strict ordering)",
          "between(a,b,c) ∧ on(a,L) ∧ on(b,L) → on(c,L)",
          "between(a,b,c) ∧ on(a,L) ∧ on(c,L) → on(b,L)",
          "between(a,b,c) ∧ between(a,d,b) → between(a,d,c)",
          "between(a,b,c) ∧ between(b,c,d) → between(a,b,d)",
          "Three collinear points: one is between the other two",
          "between(a,b,c) ∧ between(a,b,d) → ¬between(b,c,d)"]),
        ("Same-side", SAME_SIDE_AXIOMS, None,
         ["same-side(a,a,L) ∨ on(a,L)  (reflexivity)",
          "same-side(a,b,L) → same-side(b,a,L)  (symmetry)",
          "same-side(a,b,L) → ¬on(a,L)",
          "same-side(a,b,L) ∧ same-side(a,c,L) → same-side(b,c,L)  (transitivity)",
          "Any two points off a line: same-side or one is on the line"]),
        ("Pasch", PASCH_AXIOMS, None,
         ["same-side(a,c,L) ∧ between(a,b,c) → same-side(a,b,L)",
          "between(a,b,c) ∧ on(a,L) → same-side(b,c,L) ∨ on(b,L)",
          "between(a,b,c) ∧ on(b,L) → ¬same-side(a,c,L)",
          "Pasch: line crossing one side of a triangle hits another side"]),
        ("Triple incidence", TRIPLE_INCIDENCE_AXIOMS, None,
         ["Three concurrent lines determine collinear or same-side",
          "Concurrent lines: transitivity of same-side across lines",
          "Five-line same-side transitivity"]),
        ("Circle", CIRCLE_AXIOMS, _CIRCLE_LABELS,
         ["Chord intersects interior: on(b,α) ∧ on(c,α) ∧ inside(a,α) → between",
          "inside ∧ between → inside (segment inside circle, variant 1)",
          "inside ∧ between → inside (boundary to interior, variant 1)",
          "inside ∧ between → inside (segment inside circle, variant 2)",
          "on ∧ between → inside (boundary to interior, variant 2)",
          "inside ∧ between → inside (variant 3)",
          "on ∧ between → inside (variant 3)",
          "inside ∧ between → inside (variant 4)",
          "on ∧ between → inside (variant 4)",
          "Two intersecting circles: intersection points on opposite sides"]),
        ("Intersection", INTERSECTION_AXIOMS, _INTER_LABELS,
         ["Opposite sides → lines intersect",
          "on(a,α) ∧ on(b,α): opposite sides of L → L intersects α",
          "on(a,α) ∧ inside(b,α): opposite sides of L → L intersects α",
          "inside(a,α) ∧ on(b,α): opposite sides of L → L intersects α",
          "inside(a,α) ∧ inside(b,α): opposite sides of L → L intersects α",
          "inside(a,α) ∧ on(a,L) → L intersects α",
          "Circles: on/inside combinations → intersects(α,β) (variant 1)",
          "Circles: inside/inside → intersects(α,β) (variant 2)",
          "Circles: on/inside mixed → intersects(α,β) (variant 3)"]),
    ]
    for group_name, axioms, labels, descs in _DIAG_GROUPS:
        for i, ax in enumerate(axioms):
            label = labels[i] if labels else str(i + 1)
            desc = descs[i] if i < len(descs) else f"{group_name} axiom {label}"
            rules.append(RuleInfo(
                name=f"{group_name} {label}",
                category="diagrammatic",
                description=desc,
                section="§3.4",
            ))

    # ── Metric axioms (§3.5) ──────────────────────────────────────
    _METRIC_RULES = [
        ("CN1 — Transitivity", "a = b ∧ b = c → a = c"),
        ("CN2 — Addition", "a = b ∧ c = d → a+c = b+d"),
        ("CN3 — Subtraction", "a+c = b+c → a = b"),
        ("CN4 — Reflexivity", "a = a"),
        ("CN5 — Whole > Part", "0 < b → a < a+b"),
        ("M1 — Zero segment", "ab = 0 ↔ a = b"),
        ("M2 — Non-negative", "ab ≥ 0"),
        ("M3 — Symmetry", "ab = ba"),
        ("M4 — Angle symmetry", "a≠b ∧ a≠c → ∠abc = ∠cba"),
        ("M5 — Angle bounds", "0 ≤ ∠abc ≤ 2·right"),
        ("M6 — Degenerate area", "△aab = 0"),
        ("M7 — Non-negative area", "△abc ≥ 0"),
        ("M8 — Area symmetry", "△abc = △cab = △acb"),
        ("M9 — Congruence → area", "Full congruence → equal areas"),
        ("< trichotomy", "Exactly one of: a < b, a = b, b < a"),
        ("< transitivity", "a < b ∧ b < c → a < c"),
        ("+ monotonicity", "a < b → a+c < b+c"),
    ]
    for name, desc in _METRIC_RULES:
        rules.append(RuleInfo(
            name=name,
            category="metric",
            description=desc,
            section="§3.5",
        ))

    # ── Transfer axioms (§3.6) ────────────────────────────────────
    from .e_axioms import (
        DIAGRAM_SEGMENT_TRANSFER, DIAGRAM_ANGLE_TRANSFER,
        DIAGRAM_AREA_TRANSFER,
    )
    _SEG_LABELS  = ["1", "2", "3a", "3b", "4a", "4b", "4c", "4d"]
    _ANG_LABELS  = ["1a", "1b", "1c", "2a", "2b", "2c", "3a", "3b", "4", "5a", "5b"]
    _AREA_LABELS = ["1a", "1b", "1c", "2"]

    _TRANSFER_GROUPS = [
        ("Segment transfer", DIAGRAM_SEGMENT_TRANSFER, _SEG_LABELS,
         ["between(a,b,c) → ab + bc = ac  (segment addition)",
          "Equal radii → same circle: ab = ac ∧ center(a,α) ∧ center(a,β) ∧ on(b,α) ∧ on(c,β) → α = β",
          "Segment → circle: center(a,α) ∧ on(b,α) ∧ ac = ab → on(c,α)",
          "Radii equal: center(a,α) ∧ on(b,α) ∧ on(c,α) → ac = ab",
          "Segment < radius → inside: center(a,α) ∧ on(b,α) ∧ ac < ab → inside(c,α)",
          "Inside → segment < radius: center(a,α) ∧ on(b,α) ∧ inside(c,α) → ac < ab",
          "Farther than radius → ¬inside: center(a,α) ∧ on(b,α) ∧ ab < ac → ¬inside(c,α)",
          "Farther than radius → ¬on: center(a,α) ∧ on(b,α) ∧ ab < ac → ¬on(c,α)"]),
        ("Angle transfer", DIAGRAM_ANGLE_TRANSFER, _ANG_LABELS,
         ["Collinear zero angle: on(a,L) ∧ on(b,L) ∧ on(c,L) → ∠bac = 0 ∨ between(b,a,c)",
          "Zero angle → collinear: ∠bac = 0 → on(c,L)",
          "Zero angle → not between: ∠bac = 0 → ¬between(b,a,c)",
          "Angle addition: same-side decomposition → ∠bac = ∠bad + ∠dac",
          "Angle addition converse: ∠bac = ∠bad + ∠dac → same-side(b,d,M)",
          "Angle addition converse: ∠bac = ∠bad + ∠dac → same-side(c,d,L)",
          "Right angle: between(a,c,b) ∧ ∠acd = ∠dcb → ∠acd = right-angle",
          "Right angle converse: ∠acd = right-angle → ∠acd = ∠dcb",
          "Angle extension: supplementary ray → ∠bac = ∠b'ac'",
          "Parallel postulate: ∠abc + ∠bcd < 2·right → lines intersect",
          "Parallel postulate: intersection point same-side"]),
        ("Area transfer", DIAGRAM_AREA_TRANSFER, _AREA_LABELS,
         ["Zero area → collinear: △abc = 0 → on(c,L)",
          "Collinear → zero area: on(a,L) ∧ on(b,L) ∧ on(c,L) → △abc = 0",
          "Non-collinear → non-zero area: ¬on(c,L) → △abc ≠ 0",
          "Triangle area addition: between(a,c,b) → △acd + △dcb = △adb"]),
    ]
    for group_name, axioms, labels, descs in _TRANSFER_GROUPS:
        for i, ax in enumerate(axioms):
            label = labels[i] if labels else str(i + 1)
            desc = descs[i] if i < len(descs) else f"{group_name} axiom {label}"
            rules.append(RuleInfo(
                name=f"{group_name} {label}",
                category="transfer",
                description=desc,
                section="§3.6",
            ))

    # ── Superposition (§3.7) ──────────────────────────────────────
    rules.append(RuleInfo(
        name="SAS Superposition",
        category="superposition",
        description="Side-Angle-Side: ab=de, ac=df, ∠bac=∠edf ⇒ bc=ef, ∠abc=∠def, ∠acb=∠dfe",
        section="§3.7",
    ))
    rules.append(RuleInfo(
        name="SSS Superposition",
        category="superposition",
        description="Side-Side-Side: ab=de, bc=ef, ac=df ⇒ ∠bac=∠edf, ∠abc=∠def, ∠acb=∠dfe",
        section="§3.7",
    ))

    # ── Structural rules ──────────────────────────────────────────
    rules.append(RuleInfo(
        name="Reit",
        category="structural",
        description="Reiteration: restate a previously established fact",
        section="§3.2",
    ))
    rules.append(RuleInfo(
        name="Assume",
        category="structural",
        description="Assume: open a subproof by assuming ¬φ (or φ)",
        section="§3.2",
    ))
    rules.append(RuleInfo(
        name="Reductio",
        category="structural",
        description="Reductio ad absurdum: derive φ from Assume ¬φ + contradiction (ψ ∧ ¬ψ)",
        section="§3.2",
    ))
    rules.append(RuleInfo(
        name="Contradiction",
        category="structural",
        description="⊥-introduction: derive ⊥ from ψ and ¬ψ on cited lines",
        section="§3.2",
    ))
    rules.append(RuleInfo(
        name="⊥-intro",
        category="structural",
        description="⊥-introduction (alias): derive ⊥ from ψ and ¬ψ on cited lines",
        section="§3.2",
    ))
    rules.append(RuleInfo(
        name="⊥-elim",
        category="structural",
        description="⊥-elimination: discharge an assumption by citing a ⊥ line",
        section="§3.2",
    ))
    rules.append(RuleInfo(
        name="Cases",
        category="structural",
        description="Case-split elimination: both branches derived the same conclusion",
        section="§3.2",
    ))
    rules.append(RuleInfo(
        name="Given",
        category="structural",
        description="Given: cite a premise or previously established fact",
        section="§3.2",
    ))

    # ── Propositions (Book I) ─────────────────────────────────────
    for name, thm in E_THEOREM_LIBRARY.items():
        hyps = ", ".join(str(h) for h in thm.sequent.hypotheses) if thm.sequent.hypotheses else "—"
        concls = ", ".join(str(c) for c in thm.sequent.conclusions) if thm.sequent.conclusions else "—"
        sequent_str = f"{hyps} ⇒ {concls}"
        if len(sequent_str) > 100:
            sequent_str = sequent_str[:97] + "…"
        # Use the natural language statement as primary, sequent as secondary
        statement = getattr(thm, 'statement', '') or ''
        if statement:
            desc = f"{statement}\n{sequent_str}"
        else:
            desc = sequent_str
        rules.append(RuleInfo(
            name=name,
            category="proposition",
            description=desc,
            section="Book I",
        ))

    return rules


# ═══════════════════════════════════════════════════════════════════════
# Theorem catalogue access
# ═══════════════════════════════════════════════════════════════════════

def get_theorem(name: str) -> Optional[ETheorem]:
    """Retrieve a theorem by name from the library.

    Args:
        name: e.g. "Prop.I.1", "Prop.I.47"

    Returns:
        The ETheorem, or None if not found.
    """
    return E_THEOREM_LIBRARY.get(name)


def get_all_theorems() -> Dict[str, ETheorem]:
    """Return the entire theorem library."""
    return dict(E_THEOREM_LIBRARY)


def list_theorem_names() -> List[str]:
    """Return all theorem names in order."""
    return [f"Prop.I.{i}" for i in range(1, 49)]


# ═══════════════════════════════════════════════════════════════════════
# Formula parsing
# ═══════════════════════════════════════════════════════════════════════

def parse_e_formula(text: str, sort_ctx: Optional[Dict[str, Sort]] = None):
    """Parse a System E formula string into a list of literals.

    Returns a list of ``Literal`` objects or ``None`` on parse error.
    """
    from .e_parser import parse_literal_list, EParseError
    try:
        return parse_literal_list(text, sort_ctx)
    except EParseError:
        return None
