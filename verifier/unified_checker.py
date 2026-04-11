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
    Equals,
)
from .e_checker import EChecker, ECheckResult
from .e_consequence import ConsequenceEngine
from .e_library import E_THEOREM_LIBRARY, get_theorems_up_to
from .e_superposition import apply_sas_superposition, apply_sss_superposition
from .e_axiom_match import (check_specific_axiom,
                            check_specific_axiom_with_premises,
                            get_axiom_clause)


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


def verify_e_proof_json(proof_json: dict, on_line_checked=None) -> PanelCheckResult:
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

    Also accepts the ``.euclid`` file format where the proof is nested
    under a ``"proof"`` key with ``"steps"`` (using ``lineNumber``,
    ``text``, ``dependencies``) instead of ``"lines"`` (``id``,
    ``statement``, ``refs``).  Given lines are reconstructed from
    ``premises``.

    All formulas are in System E syntax (``e_parser``).

    Returns:
        A ``PanelCheckResult`` with per-line pass/fail, derived set,
        and overall acceptance.
    """
    from .e_parser import parse_literal_list, EParseError
    from .e_construction import CONSTRUCTION_RULE_BY_NAME

    # ── 0. Normalize .euclid format ──────────────────────────────
    # .euclid files nest the proof under a "proof" key with "steps"
    # instead of "lines", and use different field names.
    if "proof" in proof_json and "steps" in proof_json.get("proof", {}):
        inner = proof_json["proof"]
        premises = inner.get("premises", [])
        lines = []
        for i, p in enumerate(premises, 1):
            lines.append({
                "id": i, "depth": 0,
                "statement": p, "justification": "Given", "refs": []})
        for s in inner.get("steps", []):
            lines.append({
                "id": s["lineNumber"],
                "depth": s.get("depth", 0),
                "statement": s["text"],
                "justification": s["justification"],
                "refs": s.get("dependencies", [])})
        proof_json = {
            "name": inner.get("name", proof_json.get("name", "")),
            "premises": premises,
            "goal": inner.get("goal", ""),
            "declarations": inner.get("declarations", {}),
            "lines": lines,
            "derived_facts": inner.get("derived_facts", []),
        }

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

    # Register declared variables using their lowercase canonical form
    # (System E uses lowercase internally).  Avoid registering both
    # 'A' and 'a' as separate points — that doubles the grounding
    # pool and can push axiom grounding over _MAX_GROUND_PER_AXIOM.
    for p in decl.get("points", []):
        canon = p.lower()
        if canon not in checker.variables:
            checker.variables[canon] = Sort.POINT
    for ln in decl.get("lines", []):
        canon = ln.lower()
        if canon not in checker.variables:
            checker.variables[canon] = Sort.LINE
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

    # ── 4b. Load derived facts (synthesizer-proven, CE-unverifiable) ──
    # The synthesizer records facts that are known from the Lean proof
    # but cannot be verified by our limited consequence engine (e.g.
    # contrapositive reasoning for ¬(on(x,L)) from ¬(intersects)).
    # Seed these into checker.known so theorem steps can use them.
    _derived_strs = proof_json.get("derived_facts", [])
    if not _derived_strs and "proof" in proof_json:
        _derived_strs = proof_json["proof"].get("derived_facts", [])
    for df_str in _derived_strs:
        try:
            df_lits = parse_literal_list(df_str, sort_ctx)
            for dfl in df_lits:
                checker.known.add(dfl)
                # Also register variables from derived facts
                _df_vars: Dict[str, Sort] = {}
                checker.consequence_engine._collect_atom_var_sorts(
                    dfl.atom, _df_vars)
                for vn, vs in _df_vars.items():
                    if vn not in checker.variables:
                        checker.variables[vn] = vs
        except EParseError:
            pass

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

    # Variables are registered incrementally as each proof line is
    # checked rather than pre-scanned.  This keeps the grounding pool
    # small for early lines (the consequence/transfer engine caches
    # are keyed on the variable set and automatically regenerate when
    # new variables appear).

    def _ref_known(refs: List[int], current_depth: int) -> Set[Literal]:
        """Collect literals from referenced lines only.

        Only includes literals from lines whose depth is ≤ *current_depth*
        so that assumptions from inner subproofs cannot leak outward.
        """
        rk: Set[Literal] = set()
        for r in refs:
            if line_depth.get(r, 0) > current_depth:
                continue
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
            if on_line_checked:
                on_line_checked(lid, lr.valid, lr.errors)
            continue

        # Parse the statement into literals
        try:
            step_lits = parse_literal_list(stmt_str, sort_ctx)
        except EParseError as exc:
            lr.valid = False
            lr.errors.append(f"Parse error: {exc}")
            result.line_results[lid] = lr
            if on_line_checked:
                on_line_checked(lid, lr.valid, lr.errors)
            continue

        if not step_lits:
            lr.valid = False
            lr.errors.append("Empty statement.")
            result.line_results[lid] = lr
            if on_line_checked:
                on_line_checked(lid, lr.valid, lr.errors)
            continue

        # Determine step kind from justification
        step_kind = _classify_justification(just)
        axiom_category = (
            _classify_axiom_category(just)
            if step_kind == StepKind.AXIOM_ELIM else None
        )

        if step_kind == StepKind.CONSTRUCTION:
            # Construction rule: match conclusion pattern to derive
            # var_map, then validate prerequisites against cited refs.
            rule = CONSTRUCTION_RULE_BY_NAME.get(just)
            if rule is None:
                lr.valid = False
                lr.errors.append(f"Unknown construction rule '{just}'.")
            else:
                # Check prerequisites via pattern matching.
                # Use only facts from cited references (+ closure),
                # not all known facts, so wrong refs are rejected.
                if rule.prereq_pattern:
                    ref_facts = _ref_known(refs, depth)
                    ref_closure = (
                        checker.consequence_engine.direct_consequences(
                            ref_facts, checker.variables))
                    ref_aug = ref_facts | ref_closure
                    _vm, prereq_err, req_prereqs = (
                        _match_construction_prereqs(
                            rule, step_lits, ref_aug, checker))
                    if prereq_err is not None:
                        lr.valid = False
                        lr.errors.append(prereq_err)
                    elif req_prereqs:
                        # Strict dep check: every cited ref line
                        # must contribute at least one prerequisite.
                        for r in refs:
                            r_lits = line_lits.get(r, set())
                            if not (r_lits & req_prereqs):
                                lr.valid = False
                                lr.errors.append(
                                    f"Cited dependency L{r} does not "
                                    f"contribute any required "
                                    f"prerequisite for construction "
                                    f"'{just}'.")
                if lr.valid:
                    for lit in step_lits:
                        checker.known.add(lit)
                        _infer_sorts_from_atom(lit.atom, sort_ctx)
                        for vname in _literal_var_names(lit):
                            if vname not in checker.variables:
                                checker.variables[vname] = _infer_sort(
                                    vname, sort_ctx)
        elif step_kind == StepKind.AXIOM_ELIM:
            # ── Reject deprecated generic justifications ──────────
            _DEPRECATED = {
                "diagrammatic", "Diagrammatic",
                "metric", "Metric",
                "transfer", "Transfer",
            }
            if just in _DEPRECATED:
                lr.valid = False
                lr.errors.append(
                    f"Generic justification \"{just}\" is not allowed. "
                    f"Please use a specific axiom name (e.g. "
                    f"\"Generality 3\", \"CN1\", \"Segment transfer 1\"). "
                    f"Use the search box in the rule dropdown to find "
                    f"the correct axiom.")
                # Still add to known for downstream steps
                for lit in step_lits:
                    checker.known.add(lit)
            elif axiom_category == "structural":
                # Reit: literal must be in cited refs only
                dep_facts = _ref_known(refs, depth)
                for lit in step_lits:
                    if lit in dep_facts:
                        checker.known.add(lit)
                    else:
                        lr.valid = False
                        lr.errors.append(
                            f"Reit: {lit} is not among the cited "
                            f"dependencies.")
            else:
                # ── All named axiom rules: ref-restricted ─────────
                # Gather facts ONLY from cited references, compute
                # their closure, then verify the specific axiom
                # cited actually derives the target from those facts.
                dep_facts = _ref_known(refs, depth)

                # Restrict variables to those appearing in the
                # dep_facts and step_lits so that the consequence
                # engine grounding pools stay small (avoids hitting
                # _MAX_GROUND_PER_AXIOM with unrelated variables).
                _dep_vars: Dict[str, Sort] = {}
                for _dl in dep_facts:
                    for _vn in _literal_var_names(_dl):
                        if _vn in checker.variables:
                            _dep_vars[_vn] = checker.variables[_vn]
                for _sl in step_lits:
                    for _vn in _literal_var_names(_sl):
                        if _vn in checker.variables:
                            _dep_vars[_vn] = checker.variables[_vn]

                dep_closure = (
                    checker.consequence_engine.direct_consequences(
                        dep_facts, _dep_vars))
                dep_aug = dep_facts | dep_closure

                # For metric/transfer axioms, also run the transfer
                # engine on the dep-restricted facts so intermediate
                # metric equalities are available.
                if axiom_category in ("metric", "transfer"):
                    dep_diag = {l for l in dep_aug if l.is_diagrammatic}
                    dep_met = {l for l in dep_aug if l.is_metric}
                    dep_transfer = (
                        checker.transfer_engine.apply_transfers(
                            dep_diag, dep_met, _dep_vars))
                    dep_aug = dep_aug | dep_transfer

                # Use check_specific_axiom for all registered axioms
                # (diagrammatic, transfer, metric axiom-style rules).
                clause = get_axiom_clause(just)
                if clause is not None:
                    # First try matching against DIRECT dep_facts only.
                    used_closure = False
                    ok, err, required_premises = (
                        check_specific_axiom_with_premises(
                            just, dep_facts, step_lits,
                            _dep_vars))
                    # Fallback: if direct match fails, try against
                    # dep_aug (includes Leibniz E2 closure).  This
                    # allows axiom steps that depend on equality
                    # substitution (e.g. Generality 4 with d=b +
                    # inside(d,α) → inside(b,α) → ¬on(b,α)).
                    if not ok:
                        ok, err, required_premises = (
                            check_specific_axiom_with_premises(
                                just, dep_aug, step_lits,
                                _dep_vars))
                        if ok:
                            used_closure = True
                    if ok:
                        for lit in step_lits:
                            checker.known.add(lit)
                        # ── Strict dep check: every cited ref line
                        # must contribute at least one required
                        # premise of the axiom.
                        if not used_closure:
                            # Direct match: each ref must directly
                            # supply a required premise literal.
                            for r in refs:
                                r_lits = line_lits.get(r, set())
                                if r in premise_ids:
                                    r_lits = line_lits.get(r, set())
                                if not (r_lits & required_premises):
                                    lr.valid = False
                                    lr.errors.append(
                                        f"Cited dependency L{r} does "
                                        f"not contribute any required "
                                        f"premise for axiom "
                                        f"'{just}'.")
                        else:
                            # Closure match: required premises may be
                            # derived via Leibniz E2, so use transitive
                            # variable overlap instead.
                            all_vars = set()
                            for sl in step_lits:
                                all_vars.update(
                                    _literal_var_names(sl))
                            for r in refs:
                                for rl in line_lits.get(r, set()):
                                    all_vars.update(
                                        _literal_var_names(rl))
                            for r in refs:
                                r_lits = line_lits.get(r, set())
                                r_vars: set = set()
                                for rl in r_lits:
                                    r_vars.update(
                                        _literal_var_names(rl))
                                if not (r_vars & all_vars):
                                    lr.valid = False
                                    lr.errors.append(
                                        f"Cited dependency L{r} does "
                                        f"not contribute any required "
                                        f"premise for axiom "
                                        f"'{just}'.")
                    else:
                        lr.valid = False
                        lr.errors.append(
                            err or (
                                f"Axiom '{just}' does not derive "
                                f"the stated conclusion from the "
                                f"cited dependencies."))
                elif axiom_category == "metric":
                    # CN / metric rules not in axiom registry —
                    # check via metric engine on dep-restricted facts.
                    met_ok = True
                    for lit in step_lits:
                        if lit in dep_aug:
                            checker.known.add(lit)
                            continue
                        _scratch_me.reset()
                        if _scratch_me.is_consequence(dep_aug, lit):
                            checker.known.add(lit)
                        else:
                            met_ok = False
                            lr.valid = False
                            lr.errors.append(
                                f"Metric assertion {lit} is not a "
                                f"consequence of known facts under "
                                f"'{just}'.")
                    # Strict dep check: each ref must have variable
                    # overlap with the transitive closure of ALL
                    # refs' vars + conclusion vars.  Metric chains
                    # link through intermediate equalities (e.g.
                    # af=cd + ¬(c=d) → ¬(a=f)) where an individual
                    # ref may not share vars with the conclusion
                    # but does share vars with another ref.
                    if met_ok:
                        all_vars = set()
                        for sl in step_lits:
                            all_vars.update(_literal_var_names(sl))
                        for r in refs:
                            for rl in line_lits.get(r, set()):
                                all_vars.update(
                                    _literal_var_names(rl))
                        for r in refs:
                            r_lits = line_lits.get(r, set())
                            r_vars: set = set()
                            for rl in r_lits:
                                r_vars.update(_literal_var_names(rl))
                            if not (r_vars & all_vars):
                                lr.valid = False
                                lr.errors.append(
                                    f"Cited dependency L{r} does not "
                                    f"contribute any relevant premise "
                                    f"for metric rule '{just}'.")
                elif axiom_category == "transfer":
                    # Transfer rule not in axiom registry — check
                    # via transfer engine on dep-restricted facts.
                    trans_ok = True
                    for lit in step_lits:
                        if lit in dep_aug:
                            checker.known.add(lit)
                        else:
                            _scratch_me.reset()
                            if _scratch_me.is_consequence(dep_aug, lit):
                                checker.known.add(lit)
                            else:
                                trans_ok = False
                                lr.valid = False
                                lr.errors.append(
                                    f"Axiom '{just}' does not derive "
                                    f"{lit} from the cited "
                                    f"dependencies.")
                    # Strict dep check for transfer rules — use
                    # transitive variable closure like metric rules.
                    if trans_ok:
                        all_vars = set()
                        for sl in step_lits:
                            all_vars.update(_literal_var_names(sl))
                        for r in refs:
                            for rl in line_lits.get(r, set()):
                                all_vars.update(
                                    _literal_var_names(rl))
                        for r in refs:
                            r_lits = line_lits.get(r, set())
                            r_vars: set = set()
                            for rl in r_lits:
                                r_vars.update(_literal_var_names(rl))
                            if not (r_vars & all_vars):
                                lr.valid = False
                                lr.errors.append(
                                    f"Cited dependency L{r} does not "
                                    f"contribute any relevant premise "
                                    f"for transfer rule '{just}'.")
                else:
                    # Unregistered diagrammatic rule — check via
                    # consequence engine on dep-restricted facts.
                    unreg_ok = True
                    for lit in step_lits:
                        if lit in dep_aug:
                            checker.known.add(lit)
                            continue
                        ok = checker.consequence_engine.is_consequence(
                            dep_aug, lit)
                        if ok:
                            checker.known.add(lit)
                        else:
                            unreg_ok = False
                            lr.valid = False
                            lr.errors.append(
                                f"Axiom '{just}' does not derive "
                                f"{lit} from the cited "
                                f"dependencies.")
                    # Strict dep check for unregistered diag rules —
                    # transitive variable closure.
                    if unreg_ok:
                        all_vars = set()
                        for sl in step_lits:
                            all_vars.update(_literal_var_names(sl))
                        for r in refs:
                            for rl in line_lits.get(r, set()):
                                all_vars.update(
                                    _literal_var_names(rl))
                        for r in refs:
                            r_lits = line_lits.get(r, set())
                            r_vars: set = set()
                            for rl in r_lits:
                                r_vars.update(_literal_var_names(rl))
                            if not (r_vars & all_vars):
                                lr.valid = False
                                lr.errors.append(
                                    f"Cited dependency L{r} does not "
                                    f"contribute any relevant premise "
                                    f"for axiom '{just}'.")
        elif step_kind == StepKind.SUPERPOSITION_SAS:
            # SAS superposition (§3.7): extract 6 point names from the
            # step literals and delegate to apply_sas_superposition.
            # Use only facts from cited references.
            pts = _extract_superposition_points(step_lits)
            if pts is None or len(pts) < 6:
                lr.valid = False
                lr.errors.append(
                    "SAS requires conclusions mentioning exactly "
                    "6 distinct point variables (a,b,c,d,e,f).")
            else:
                dep_facts = _ref_known(refs, depth)
                a, b, c, d, e, f = pts[:6]
                sas_r = apply_sas_superposition(
                    dep_facts, a, b, c, d, e, f)
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
            # Use only facts from cited references.
            pts = _extract_superposition_points(step_lits)
            if pts is None or len(pts) < 6:
                lr.valid = False
                lr.errors.append(
                    "SSS requires conclusions mentioning exactly "
                    "6 distinct point variables (a,b,c,d,e,f).")
            else:
                dep_facts = _ref_known(refs, depth)
                a, b, c, d, e, f = pts[:6]
                sss_r = apply_sss_superposition(
                    dep_facts, a, b, c, d, e, f)
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
                # Gather facts from cited refs only (+ closure).
                dep_facts = _ref_known(refs, depth)
                dep_closure = (
                    checker.consequence_engine.direct_consequences(
                        dep_facts, checker.variables))
                dep_aug = dep_facts | dep_closure
                # Also run transfer engine for metric hypotheses.
                dep_diag = {l for l in dep_aug if l.is_diagrammatic}
                dep_met = {l for l in dep_aug if l.is_metric}
                dep_transfer = (
                    checker.transfer_engine.apply_transfers(
                        dep_diag, dep_met, checker.variables))
                dep_aug = dep_aug | dep_transfer

                # Derive variable mapping from step literals vs
                # theorem conclusions so hypotheses can be checked
                # with the user's actual variable names.
                var_map = _match_theorem_var_map(
                    thm, step_lits, known=dep_aug,
                    checker=checker)
                # Check hypotheses of the theorem are met
                thm_req_premises: Set[Literal] = set()
                for hyp in thm.sequent.hypotheses:
                    inst = substitute_literal(hyp, var_map)
                    # Skip impossible ¬(v=v) hypotheses — these arise
                    # when the Lean proof reuses variables in positions
                    # that the e_library requires distinct.  The Lean
                    # proof is machine-checked and correct; the e_library
                    # adds stricter distinctness constraints not present
                    # in the original formalization.
                    if (not inst.polarity
                            and isinstance(inst.atom, Equals)
                            and isinstance(inst.atom.left, str)
                            and inst.atom.left == inst.atom.right):
                        continue
                    thm_req_premises.add(inst)
                    if inst not in dep_aug:
                        # Try via consequence engines on dep_aug
                        if inst.is_diagrammatic:
                            ok = checker.consequence_engine.is_consequence(
                                dep_aug, inst)
                            # If CE on dep-restricted facts fails, also
                            # check if the hypothesis is already in the
                            # globally accumulated known set.  Facts from
                            # earlier accepted proof lines (constructions,
                            # axiom steps) are sound and can satisfy
                            # theorem hypotheses even when the cited deps
                            # are too narrow for the CE to re-derive them.
                            if not ok and inst in checker.known:
                                ok = True
                        elif inst.is_metric:
                            _scratch_me.reset()
                            ok = _scratch_me.is_consequence(dep_aug, inst)
                            # Fallback: metric facts from derived_facts
                            # (construction-produced inequalities) live in
                            # checker.known but may not be in dep_aug.
                            if not ok and inst in checker.known:
                                ok = True
                        else:
                            ok = inst in dep_aug
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
                            _scratch_me.reset()
                            if _scratch_me.is_consequence(
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
                    # ── Strict dep check: every cited ref line
                    # must contribute at least one required hypothesis.
                    if thm_req_premises:
                        for r in refs:
                            r_lits = line_lits.get(r, set())
                            if not (r_lits & thm_req_premises):
                                lr.valid = False
                                lr.errors.append(
                                    f"Cited dependency L{r} does not "
                                    f"contribute any required premise "
                                    f"for theorem '{just}'.")
        elif step_kind == StepKind.CONTRADICTION:
            # Fitch ⊥-intro: derive ⊥ from a direct contradiction.
            #
            # Protocol:
            #   Exactly 2 cited dependencies required.  The two lines
            #   must contain a contradictory pair:
            #     • ψ and ¬ψ  (literal and its negation), OR
            #     • X = Y and X < Y  (equality with strict order), OR
            #     • X < Y and Y < X  (antisymmetry violation).
            #
            #   ⊥-intro is only valid inside a subproof (depth > 0).
            #
            from .e_ast import BOTTOM, Equals as _Eq, LessThan as _Lt

            if depth < 1:
                lr.valid = False
                lr.errors.append(
                    "⊥-intro is only valid inside a subproof "
                    "(depth > 0). A contradiction at depth 0 "
                    "would mean the axiom system is inconsistent.")

            if lr.valid:
                if len(refs) != 2:
                    lr.valid = False
                    lr.errors.append(
                        "⊥-intro requires exactly 2 cited "
                        "dependencies: the two lines whose "
                        "literals form a P and ¬P contradiction.")

            if lr.valid:
                lits_a = line_lits.get(refs[0], set())
                lits_b = line_lits.get(refs[1], set())
                if not lits_a or not lits_b:
                    lr.valid = False
                    lr.errors.append(
                        "⊥-intro: one or both cited dependency "
                        "lines have no recorded literals.")

            if lr.valid:
                found_contra = False

                # Check literal contradiction: ψ and ¬ψ
                neg_a = {l.negated() for l in lits_a}
                if lits_b & neg_a:
                    found_contra = True

                if not found_contra:
                    neg_b = {l.negated() for l in lits_b}
                    if lits_a & neg_b:
                        found_contra = True

                if not found_contra:
                    # Check metric: X = Y and X < Y
                    eq_keys: set = set()
                    for ml in lits_a | lits_b:
                        if (ml.polarity and ml.is_metric
                                and isinstance(ml.atom, _Eq)):
                            eq_keys.add((ml.atom.left, ml.atom.right))
                            eq_keys.add((ml.atom.right, ml.atom.left))
                    for ml in lits_a | lits_b:
                        if (ml.polarity and ml.is_metric
                                and isinstance(ml.atom, _Lt)):
                            if ((ml.atom.left, ml.atom.right)
                                    in eq_keys):
                                found_contra = True
                                break

                if not found_contra:
                    # Check metric: X < Y and Y < X
                    lt_a: set = set()
                    lt_b: set = set()
                    for ml in lits_a:
                        if (ml.polarity and ml.is_metric
                                and isinstance(ml.atom, _Lt)):
                            lt_a.add((ml.atom.left, ml.atom.right))
                    for ml in lits_b:
                        if (ml.polarity and ml.is_metric
                                and isinstance(ml.atom, _Lt)):
                            lt_b.add((ml.atom.left, ml.atom.right))
                    for pair in lt_a:
                        if (pair[1], pair[0]) in lt_b:
                            found_contra = True
                            break
                    if not found_contra:
                        for pair in lt_b:
                            if (pair[1], pair[0]) in lt_a:
                                found_contra = True
                                break

                if not found_contra:
                    lr.valid = False
                    lr.errors.append(
                        "⊥-intro: the two cited dependencies do "
                        "not form a direct contradiction (need "
                        "ψ and ¬ψ, X = Y and X < Y, or "
                        "X < Y and Y < X).")
                if lr.valid:
                    checker.known.add(BOTTOM)
                    # Record BOTTOM as this line's literal so ⊥-elim
                    # can reference it.
                    line_lits[lid] = {BOTTOM}
        elif step_kind == StepKind.BOT_ELIM:
            # ⊥-elimination: discharge an assumption subproof.
            #
            # Protocol:
            #   1. An earlier "Assume" line introduced ¬φ (or φ).
            #   2. Subsequent steps derived ⊥ (via ⊥-intro).
            #   3. This "⊥-elim" step asserts φ (the negation of the
            #      assumed literal), provided BOTTOM is in the known
            #      set (from a prior ⊥-intro step).
            #
            # refs[0] must point to the Assume line.
            #
            if not refs:
                lr.valid = False
                lr.errors.append(
                    "⊥-elim must reference the Assume line as "
                    "refs[0].")
            else:
                assume_lid = refs[0]
                assume_lits = line_lits.get(assume_lid, set())
                if not assume_lits:
                    lr.valid = False
                    lr.errors.append(
                        f"⊥-elim refs[0] (line {assume_lid}) has "
                        f"no recorded literals.")
                else:
                    # Verify that each step literal is the negation of
                    # an assumed literal.
                    for lit in step_lits:
                        neg_lit = lit.negated()
                        if neg_lit not in assume_lits:
                            lr.valid = False
                            lr.errors.append(
                                f"⊥-elim conclusion {lit} is not "
                                f"the negation of any assumed "
                                f"literal.")

                    # Require BOTTOM in known (from a prior ⊥-intro).
                    if lr.valid:
                        from .e_ast import BOTTOM as _BOTTOM
                        if _BOTTOM not in checker.known:
                            lr.valid = False
                            lr.errors.append(
                                "⊥-elim requires ⊥ to have been "
                                "derived (via ⊥-intro) in the "
                                "subproof, but ⊥ was not found.")

                    # If valid, retract all facts derived inside the
                    # subproof (at the Assume's depth or deeper) and
                    # add only the ⊥-elim conclusion at the outer
                    # depth.  This prevents subproof-scoped facts from
                    # leaking into the enclosing proof.
                    if lr.valid:
                        assume_depth = line_depth.get(assume_lid, 0)
                        subproof_lits: Set[Literal] = set()
                        for prev_line in lines:
                            plid = prev_line.get("id", 0)
                            if plid == lid:
                                break
                            pdepth = line_depth.get(plid, 0)
                            if plid >= assume_lid and pdepth >= assume_depth:
                                subproof_lits.update(
                                    line_lits.get(plid, set()))
                        # Retract subproof-scoped facts
                        for sl in subproof_lits:
                            checker.known.discard(sl)
                        # Also discard BOTTOM itself
                        checker.known.discard(_BOTTOM)
                        # Add ⊥-elim conclusion
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
            # Trichotomy rule (metric section).
            #
            # Axiom: for magnitudes x, y exactly one of
            #   x < y,  x = y,  y < x  holds.
            #
            # Three formally sound inference forms:
            #
            # (a) Assert the full axiom (0 deps → 3-way disjunction):
            #     conclude  x < y ∨ x = y ∨ y < x
            #
            # (b) Eliminate one case (1 dep → 2-way disjunction):
            #     From ¬(x = y)  conclude  x < y ∨ y < x
            #     From ¬(x < y)  conclude  x = y ∨ y < x
            #     From ¬(y < x)  conclude  x < y ∨ x = y
            #
            # (c) Eliminate two cases (2 deps → single literal):
            #     From ¬(x < y) ∧ ¬(y < x)  conclude  x = y
            #     From ¬(x = y) ∧ ¬(x < y)  conclude  y < x
            #     From ¬(x = y) ∧ ¬(y < x)  conclude  x < y
            #
            from .e_ast import (DisjunctionAtom, LessThan as _LT,
                                Equals as _Eq)

            if len(step_lits) != 1:
                lr.valid = False
                lr.errors.append(
                    "Trichotomy must produce exactly one "
                    "disjunction or metric literal.")

            if lr.valid:
                slit = step_lits[0]

                # ── Helper: build the 3 trichotomy cases for (x, y)
                def _tri_cases(x, y):
                    """Return {label: Literal} for the 3 cases."""
                    return {
                        "lt": Literal(_LT(x, y), polarity=True),
                        "eq": Literal(_Eq(x, y), polarity=True),
                        "gt": Literal(_LT(y, x), polarity=True),
                    }

                # ── Helper: extract (x, y) pair from a positive
                #    metric literal (Equals or LessThan).
                def _metric_pair(lit):
                    if not lit.polarity or not lit.is_metric:
                        return None
                    a = lit.atom
                    if isinstance(a, _Eq):
                        return (a.left, a.right)
                    if isinstance(a, _LT):
                        return (a.left, a.right)
                    return None

                # Collect negated metric literals from dep lines.
                dep_neg_lits: set = set()
                for r in refs:
                    for dl in line_lits.get(r, set()):
                        if not dl.polarity and dl.is_metric:
                            dep_neg_lits.add(dl)

                if (slit.polarity
                        and isinstance(slit.atom, DisjunctionAtom)):
                    # ── Disjunction conclusion ─────────────────────
                    disj = slit.atom.disjuncts
                    pair = _metric_pair(disj[0]) if disj else None
                    if pair is None:
                        lr.valid = False
                        lr.errors.append(
                            "Trichotomy disjunction must contain "
                            "metric literals (< or =).")
                    else:
                        x, y = pair
                        tri = _tri_cases(x, y)
                        tri_set = set(tri.values())

                        disj_set = set(disj)
                        if not disj_set.issubset(tri_set):
                            lr.valid = False
                            lr.errors.append(
                                "Trichotomy disjuncts must be a "
                                "subset of {x<y, x=y, y<x}.")

                        if lr.valid:
                            # Check that every eliminated case has
                            # its negation cited in a dep line.
                            # (Full 3-way: eliminated is empty → OK.)
                            eliminated = tri_set - disj_set
                            for elim_lit in eliminated:
                                needed_neg = elim_lit.negated()
                                if needed_neg not in dep_neg_lits:
                                    lr.valid = False
                                    lr.errors.append(
                                        f"Trichotomy: to eliminate "
                                        f"{elim_lit}, a cited dep "
                                        f"must contain {needed_neg}.")

                        if lr.valid:
                            checker.known.add(slit)

                elif slit.is_metric and slit.polarity:
                    # ── Single metric conclusion (2 deps) ─────────
                    pair = _metric_pair(slit)
                    if pair is None:
                        lr.valid = False
                        lr.errors.append(
                            "Trichotomy: conclusion must be a "
                            "positive metric literal (< or =).")
                    else:
                        x, y = pair
                        tri = _tri_cases(x, y)
                        if slit not in set(tri.values()):
                            lr.valid = False
                            lr.errors.append(
                                f"Trichotomy: {slit} is not one of "
                                f"the trichotomy cases for "
                                f"({x}, {y}).")

                        if lr.valid:
                            others = {v for v in tri.values()
                                       if v != slit}
                            for other_lit in others:
                                needed_neg = other_lit.negated()
                                if needed_neg not in dep_neg_lits:
                                    lr.valid = False
                                    lr.errors.append(
                                        f"Trichotomy: to conclude "
                                        f"{slit}, a cited dep must "
                                        f"contain {needed_neg}.")

                        if lr.valid:
                            checker.known.add(slit)

                else:
                    lr.valid = False
                    lr.errors.append(
                        "Trichotomy must produce a positive "
                        "disjunction (φ ∨ ψ) or a positive "
                        "metric literal (< or =).")
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
                f"Assume, \u22a5-intro, \u22a5-elim).")

        if lr.valid:
            result.derived.add(lid)
            # Record per-line literals for ref-restricted checking.
            # Theorem application already sets line_lits[lid] with
            # the full conclusion set; other step kinds use step_lits.
            if lid not in line_lits:
                line_lits[lid] = set(step_lits)
        result.line_results[lid] = lr
        if on_line_checked:
            on_line_checked(lid, lr.valid, lr.errors)

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

    # Explicit step kind labels.
    # Generic "Diagrammatic", "Metric", "Transfer" are REJECTED — users
    # must cite a specific axiom name (e.g. "Generality 3", "CN1",
    # "Segment transfer 1").  However, "Diagrammatic" etc. are kept as
    # DEPRECATED aliases that still verify but produce a warning.
    _DEPRECATED_GENERIC = {
        "diagrammatic", "Diagrammatic",
        "metric", "Metric",
        "transfer", "Transfer",
    }
    _MAP = {
        "SAS": StepKind.SUPERPOSITION_SAS,
        "SSS": StepKind.SUPERPOSITION_SSS,
        "SAS Superposition": StepKind.SUPERPOSITION_SAS,
        "SSS Superposition": StepKind.SUPERPOSITION_SSS,
        "SAS-elim": StepKind.SUPERPOSITION_SAS,
        "SSS-elim": StepKind.SUPERPOSITION_SSS,
        "Reit": StepKind.AXIOM_ELIM,
        "Given": StepKind.AXIOM_ELIM,
    }
    # Still route deprecated generics through AXIOM_ELIM so old proofs
    # don't hard-fail, but the handler adds a warning.
    for _g in _DEPRECATED_GENERIC:
        _MAP[_g] = StepKind.AXIOM_ELIM
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

    # Trichotomy (must come before prefix matching because
    # "< trichotomy" starts with "< " which is in _METRIC_PREFIXES)
    if just in ("Trichotomy", "trichotomy",
                "< trichotomy", "Metric Trichotomy"):
        return StepKind.TRICHOTOMY

    for pfx in _DIAG_PREFIXES:
        if just.startswith(pfx):
            return StepKind.AXIOM_ELIM

    for pfx in _METRIC_PREFIXES:
        if just.startswith(pfx):
            return StepKind.AXIOM_ELIM

    for pfx in _TRANSFER_PREFIXES:
        if just.startswith(pfx):
            return StepKind.AXIOM_ELIM

    # Fitch ⊥-intro: derive ⊥ from ψ and ¬ψ  ("Contradiction" kept for old proofs)
    if just in ("⊥-intro", "Contradiction"):
        return StepKind.CONTRADICTION

    # Fitch ⊥-elim: discharge Assume by citing ⊥ line
    if just in ("⊥-elim",):
        return StepKind.BOT_ELIM

    # Case split elimination: both branches derived same conclusion
    if just in ("Cases", "Case-Split", "CaseSplit", "case-split"):
        return StepKind.CASE_SPLIT_ELIM

    # Default: unrecognised
    return None


def _classify_axiom_category(just: str) -> str:
    """Return the axiom category for AXIOM_ELIM steps.

    Returns "diagrammatic", "metric", "transfer", or "structural".
    Only accepts specific named axioms — generic category names are
    rejected by _classify_justification.
    """
    if just in ("Reit", "Given"):
        return "structural"
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
) -> Tuple[Optional[Dict[str, str]], Optional[str], Set[Literal]]:
    """Derive a var_map from *step_lits* vs the rule's conclusion pattern,
    then check that every prerequisite (instantiated) is in *known* or
    derivable via the consequence engine.

    Returns ``(var_map, error_msg, required_prereqs)``.
    *error_msg* is ``None`` on success.
    *required_prereqs* is the set of instantiated prerequisite literals.
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
                f"{', '.join(repr(p) for p in rule.conclusion_pattern)}"), set()

    # Reject extra literals beyond the conclusion pattern.
    # Construction rules produce exactly the literals specified in
    # their conclusion pattern — no extra facts may be smuggled in.
    if remaining:
        extras = ', '.join(str(r) for r in remaining)
        return bindings, (
            f"Construction '{rule.name}' does not produce: {extras}. "
            f"Only the conclusion pattern literals are allowed."), set()

    # All conclusion patterns matched — now check prerequisites.
    # Some prerequisites may contain schema variables not present in the
    # conclusion pattern (e.g. ``center(c, α)`` where ``c`` only appears
    # in the prereqs).  We attempt to bind these by searching *known*
    # for a matching literal.
    required_prereqs: Set[Literal] = set()
    for prereq in rule.prereq_pattern:
        inst = substitute_literal(prereq, bindings)
        if inst in known:
            required_prereqs.add(inst)
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
                    inst = substitute_literal(prereq, bindings)
                    required_prereqs.add(inst)
                    break
            if resolved:
                continue

        # Re-instantiate with potentially updated bindings
        inst = substitute_literal(prereq, bindings)
        if inst in known:
            required_prereqs.add(inst)
            continue
        # Try consequence engine
        ok = checker.consequence_engine.is_consequence(
            known, inst)
        if not ok:
            return bindings, (
                f"Construction prerequisite not met: {inst}"), required_prereqs
        required_prereqs.add(inst)
    return bindings, None, required_prereqs


def _match_theorem_var_map(
    thm: ETheorem,
    step_lits: List[Literal],
    known: Optional[Set[Literal]] = None,
    checker=None,
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
                        # Skip impossible ¬(v=v) — Lean arg reuse
                        if (not inst.polarity
                                and isinstance(inst.atom, Equals)
                                and isinstance(inst.atom.left, str)
                                and inst.atom.left == inst.atom.right):
                            continue
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
                                # For diagrammatic hypotheses, reject if
                                # the negation is already known (the
                                # mapping is contradicted).  Otherwise
                                # defer to the full hypothesis check
                                # (line 665-692) — some diagrammatic
                                # facts require multi-step reasoning that
                                # the CE cannot derive in one pass.
                                if inst.is_diagrammatic:
                                    if inst.negated() in known:
                                        return False
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
        "let-intersection-line-circle-other": "Line–circle intersection (other side of interior point)",
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
    _INTER_LABELS   = ["1", "2a", "2b", "2c", "2d", "3", "4a", "4b", "5", "6"]

    _DIAG_GROUPS = [
        ("Generality", GENERALITY_AXIOMS,
         ["1", "2", "3", "4", "5", "5c", "5d", "6", "6c"],
         ["a ≠ b ∧ on(a,L) ∧ on(b,L) ∧ on(a,M) ∧ on(b,M) ⇒ L = M",
              "center(a,α) ∧ center(b,α) ⇒ a = b",
              "center(a,α) ⇒ inside(a,α)",
              "inside(a,α) ⇒ ¬on(a,α)",
              "on(a,L) ∧ ¬on(a,M) ⇒ L ≠ M  (equality substitution)",
               "on(a,α) ∧ ¬on(a,β) ⇒ α ≠ β  (equality substitution)",
               "center(a,α) ∧ ¬center(a,β) ⇒ α ≠ β  (equality substitution)",
               "on(a,L) ∧ ¬on(b,L) ⇒ a ≠ b  (equality substitution)",
               "on(a,α) ∧ ¬on(b,α) ⇒ a ≠ b  (equality substitution)"]),
        ("Betweenness", BETWEEN_AXIOMS, _BETWEEN_LABELS,
         ["between(a,b,c) ⇒ between(c,b,a)",
          "between(a,b,c) ⇒ a ≠ b",
          "between(a,b,c) ⇒ a ≠ c",
          "between(a,b,c) ⇒ ¬between(b,a,c)",
          "between(a,b,c) ∧ on(a,L) ∧ on(b,L) ⇒ on(c,L)",
          "between(a,b,c) ∧ on(a,L) ∧ on(c,L) ⇒ on(b,L)",
          "between(a,b,c) ∧ between(a,d,b) ⇒ between(a,d,c)",
          "between(a,b,c) ∧ between(b,c,d) ⇒ between(a,b,d)",
          "a ≠ b ∧ a ≠ c ∧ b ≠ c ∧ on(a,L) ∧ on(b,L) ∧ on(c,L) ⇒ between(a,b,c) ∨ between(b,c,a) ∨ between(c,a,b)",
          "between(a,b,c) ∧ between(a,b,d) ⇒ ¬between(b,c,d)"]),
        ("Same-side", SAME_SIDE_AXIOMS, None,
         ["¬on(a,L) ⇒ same-side(a,a,L)",
          "same-side(a,b,L) ⇒ same-side(b,a,L)",
          "same-side(a,b,L) ⇒ ¬on(a,L)",
          "same-side(a,b,L) ∧ same-side(a,c,L) ⇒ same-side(b,c,L)",
          "¬on(a,L) ∧ ¬on(b,L) ∧ ¬on(c,L) ∧ ¬same-side(a,b,L) ⇒ same-side(a,c,L) ∨ same-side(b,c,L)",
          "same-side(a,b,L) ∧ ¬same-side(a,c,L) ⇒ b ≠ c  (equality substitution)"]),
        ("Pasch", PASCH_AXIOMS, None,
         ["between(a,b,c) ∧ same-side(a,c,L) ⇒ same-side(a,b,L)",
          "between(a,b,c) ∧ on(a,L) ∧ ¬on(b,L) ⇒ same-side(b,c,L)",
          "between(a,b,c) ∧ on(b,L) ⇒ ¬same-side(a,c,L)",
          "L ≠ M ∧ on(b,L) ∧ on(b,M) ∧ on(a,M) ∧ on(c,M) ∧ a ≠ b ∧ c ≠ b ∧ ¬same-side(a,c,L) ⇒ between(a,b,c)"]),
        ("Triple incidence", TRIPLE_INCIDENCE_AXIOMS, None,
          ["on(a,L) ∧ on(a,M) ∧ on(a,N) ∧ on(b,L) ∧ on(c,M) ∧ on(d,N) ∧ same-side(c,d,L) ∧ same-side(b,c,N) ⇒ ¬same-side(b,d,M)",
           "on(a,L) ∧ on(a,M) ∧ on(a,N) ∧ on(b,L) ∧ on(c,M) ∧ on(d,N) ∧ same-side(c,d,L) ∧ ¬same-side(b,d,M) ∧ ¬on(d,M) ∧ b≠a ⇒ same-side(b,c,N)",
           "on(a,L) ∧ on(a,M) ∧ on(a,N) ∧ on(b,L) ∧ on(c,M) ∧ on(d,N) ∧ same-side(c,d,L) ∧ same-side(b,c,N) ∧ same-side(d,e,M) ∧ same-side(c,e,N) ⇒ same-side(c,e,L)"]),
        ("Circle", CIRCLE_AXIOMS, _CIRCLE_LABELS,
         ["on(a,L) ∧ on(b,L) ∧ on(c,L) ∧ inside(a,α) ∧ on(b,α) ∧ on(c,α) ∧ b ≠ c ⇒ between(b,a,c)",
          "inside(a,α) ∧ inside(b,α) ∧ between(a,c,b) ⇒ inside(c,α)",
          "inside(a,α) ∧ on(b,α) ∧ between(a,c,b) ⇒ inside(c,α)",
          "on(a,α) ∧ inside(b,α) ∧ between(a,c,b) ⇒ inside(c,α)",
          "on(a,α) ∧ on(b,α) ∧ between(a,c,b) ⇒ inside(c,α)",
          "inside(a,α) ∧ ¬inside(c,α) ∧ between(a,c,b) ⇒ ¬inside(b,α)",
          "inside(a,α) ∧ ¬inside(c,α) ∧ between(a,c,b) ⇒ ¬on(b,α)",
          "on(a,α) ∧ ¬inside(c,α) ∧ between(a,c,b) ⇒ ¬inside(b,α)",
          "on(a,α) ∧ ¬inside(c,α) ∧ between(a,c,b) ⇒ ¬on(b,α)",
          "α ≠ β ∧ intersects(α,β) ∧ on(c,α) ∧ on(c,β) ∧ on(d,α) ∧ on(d,β) ∧ c ≠ d ∧ center(a,α) ∧ center(b,β) ∧ on(a,L) ∧ on(b,L) ⇒ ¬same-side(c,d,L)"]),
        ("Intersection", INTERSECTION_AXIOMS, _INTER_LABELS,
         ["¬on(a,L) ∧ ¬on(b,L) ∧ ¬same-side(a,b,L) ∧ on(a,M) ∧ on(b,M) ⇒ intersects(L,M)",
           "on(a,α) ∧ on(b,α) ∧ ¬on(a,L) ∧ ¬on(b,L) ∧ ¬same-side(a,b,L) ⇒ intersects(L,α)",
           "on(a,α) ∧ inside(b,α) ∧ ¬on(a,L) ∧ ¬on(b,L) ∧ ¬same-side(a,b,L) ⇒ intersects(L,α)",
           "inside(a,α) ∧ on(b,α) ∧ ¬on(a,L) ∧ ¬on(b,L) ∧ ¬same-side(a,b,L) ⇒ intersects(L,α)",
           "inside(a,α) ∧ inside(b,α) ∧ ¬on(a,L) ∧ ¬on(b,L) ∧ ¬same-side(a,b,L) ⇒ intersects(L,α)",
           "inside(a,α) ∧ on(a,L) ⇒ intersects(L,α)",
           "on(a,α) ∧ on(b,α) ∧ inside(a,β) ∧ ¬inside(b,β) ∧ ¬on(b,β) ⇒ intersects(α,β)",
           "on(a,α) ∧ inside(b,α) ∧ inside(a,β) ∧ ¬inside(b,β) ∧ ¬on(b,β) ⇒ intersects(α,β)",
           "on(a,α) ∧ inside(b,α) ∧ inside(a,β) ∧ on(b,β) ⇒ intersects(α,β)",
           "α ≠ β ∧ on(c,α) ∧ on(c,β) ∧ on(d,α) ∧ on(d,β) ∧ c ≠ d ⇒ intersects(α,β)"]),
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

    # Equality axioms (§3.4) — built into the consequence engine
    rules.append(RuleInfo(
        name="Equality 1",
        category="diagrammatic",
        description="x = x  (reflexivity)",
        section="§3.4",
    ))
    rules.append(RuleInfo(
        name="Equality 2",
        category="diagrammatic",
        description="x = y ∧ φ(x) ⇒ φ(y)  (substitution)",
        section="§3.4",
    ))

    # ── Metric axioms (§3.5) ──────────────────────────────────────
    _METRIC_RULES = [
        ("CN1 — Transitivity", "a = b ∧ b = c ⇒ a = c"),
        ("CN2 — Addition", "a = b ∧ c = d ⇒ a + c = b + d"),
        ("CN3 — Subtraction", "a + c = b + c ⇒ a = b"),
        ("CN4 — Reflexivity", "a = a"),
        ("CN5 — Whole > Part", "0 < b ⇒ a < a + b"),
        ("M1 — Zero segment", "ab = 0 ⟺ a = b"),
        ("M2 — Non-negative", "ab ≥ 0"),
        ("M3 — Symmetry", "ab = ba"),
        ("M4 — Angle symmetry", "a ≠ b ∧ a ≠ c ⇒ ∠abc = ∠cba"),
        ("M5 — Angle bounds", "0 ≤ ∠abc ≤ ∟ + ∟"),
        ("M6 — Degenerate area", "△aab = 0"),
        ("M7 — Non-negative area", "△abc ≥ 0"),
        ("M8 — Area symmetry", "△abc = △cab ∧ △abc = △acb"),
        ("M9 — Congruence ⇒ area", "ab = a′b′ ∧ bc = b′c′ ∧ ca = c′a′ ∧ ∠abc = ∠a′b′c′ ∧ ∠bca = ∠b′c′a′ ∧ ∠cab = ∠c′a′b′ ⇒ △abc = △a′b′c′"),
        ("Trichotomy", "For magnitudes x, y exactly one of x < y, x = y, y < x holds. 0 deps ⇒ full 3-way disjunction (axiom). 1 dep ⇒ 2-way disjunction (e.g. ¬(x=y) ⇒ x<y ∨ y<x). 2 deps ⇒ single literal (e.g. ¬(x<y) ∧ ¬(y<x) ⇒ x=y)."),
        ("Order transitivity", "a < b ∧ b < c ⇒ a < c"),
        ("Addition preserves order", "a < b ⇒ a + c < b + c"),
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
    _ANG_LABELS  = ["1a", "1b", "1c", "2a", "2b", "2c", "3a", "3b", "4", "5a", "5b", "6", "7"]
    _AREA_LABELS = ["1a", "1b", "1c", "2"]

    _TRANSFER_GROUPS = [
        ("Segment transfer", DIAGRAM_SEGMENT_TRANSFER, _SEG_LABELS,
         ["between(a,b,c) ⇒ ab + bc = ac",
          "center(a,α) ∧ center(a,β) ∧ on(b,α) ∧ on(c,β) ∧ ab = ac ⇒ α = β",
          "center(a,α) ∧ on(b,α) ∧ ac = ab ⇒ on(c,α)",
          "center(a,α) ∧ on(b,α) ∧ on(c,α) ⇒ ac = ab",
          "center(a,α) ∧ on(b,α) ∧ ac < ab ⇒ inside(c,α)",
          "center(a,α) ∧ on(b,α) ∧ inside(c,α) ⇒ ac < ab",
          "center(a,α) ∧ on(b,α) ∧ ab < ac ⇒ ¬inside(c,α)",
          "center(a,α) ∧ on(b,α) ∧ ab < ac ⇒ ¬on(c,α)"]),
        ("Angle transfer", DIAGRAM_ANGLE_TRANSFER, _ANG_LABELS,
         ["a ≠ b ∧ a ≠ c ∧ on(a,L) ∧ on(b,L) ∧ on(c,L) ∧ ¬between(b,a,c) ⇒ ∠bac = 0",
          "a ≠ b ∧ a ≠ c ∧ on(a,L) ∧ on(b,L) ∧ ∠bac = 0 ⇒ on(c,L)",
          "a ≠ b ∧ a ≠ c ∧ on(a,L) ∧ on(b,L) ∧ ∠bac = 0 ⇒ ¬between(b,a,c)",
          "on(a,L) ∧ on(a,M) ∧ on(b,L) ∧ on(c,M) ∧ L ≠ M ∧ ¬on(d,L) ∧ ¬on(d,M) ∧ same-side(b,d,M) ∧ same-side(c,d,L) ⇒ ∠bac = ∠bad + ∠dac",
           "on(a,L) ∧ on(a,M) ∧ on(b,L) ∧ on(c,M) ∧ L ≠ M ∧ ∠bac = ∠bad + ∠dac ∧ same-side(c,d,L) ⇒ same-side(b,d,M)",
           "on(a,L) ∧ on(a,M) ∧ on(b,L) ∧ on(c,M) ∧ L ≠ M ∧ ∠bac = ∠bad + ∠dac ∧ same-side(b,d,M) ⇒ same-side(c,d,L)",
          "on(a,L) ∧ on(b,L) ∧ between(a,c,b) ∧ ¬on(d,L) ∧ ∠acd = ∠dcb ⇒ ∠acd = ∟",
          "on(a,L) ∧ on(b,L) ∧ between(a,c,b) ∧ ¬on(d,L) ∧ ∠acd = ∟ ⇒ ∠acd = ∠dcb",
          "on(a,L) ∧ on(b,L) ∧ on(b′,L) ∧ on(a,M) ∧ on(c,M) ∧ on(c′,M) ∧ ¬between(b,a,b′) ∧ ¬between(c,a,c′) ⇒ ∠bac = ∠b′ac′",
          "on(a,L) ∧ on(b,M) ∧ on(c,M) ∧ on(c,N) ∧ on(d,N) ∧ b ≠ c ∧ same-side(a,d,N) ∧ ∠abc + ∠bcd < ∟ + ∟ ⇒ intersects(L,N)",
           "on(a,L) ∧ on(b,M) ∧ on(c,M) ∧ on(c,N) ∧ on(d,N) ∧ b ≠ c ∧ same-side(a,d,N) ∧ ∠abc + ∠bcd < ∟ + ∟ ∧ on(e,L) ∧ on(e,N) ⇒ same-side(e,a,M)",
          "on(a,L) ∧ on(b,L) ∧ between(a,c,b) ∧ ¬on(d,L) ∧ c ≠ d ⇒ ∠acd + ∠dcb = ∟ + ∟",
          "on(a,L) ∧ on(b,L) ∧ ¬on(c,L) ∧ ¬on(d,L) ∧ ¬same-side(c,d,L) ∧ b ≠ c ∧ b ≠ d ∧ ∠abc + ∠abd = ∟ + ∟ ⇒ between(c,b,d)"]),
        ("Area transfer", DIAGRAM_AREA_TRANSFER, _AREA_LABELS,
         ["on(a,L) ∧ on(b,L) ∧ a ≠ b ∧ △abc = 0 ⇒ on(c,L)",
          "on(a,L) ∧ on(b,L) ∧ a ≠ b ∧ on(c,L) ⇒ △abc = 0",
          "on(a,L) ∧ on(b,L) ∧ a ≠ b ∧ ¬on(c,L) ⇒ △abc ≠ 0",
          "on(a,L) ∧ on(b,L) ∧ a ≠ b ∧ a ≠ c ∧ b ≠ c ∧ ¬on(d,L) ∧ between(a,c,b) ⇒ △acd + △dcb = △adb"]),
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
        description="ab = de ∧ ac = df ∧ ∠bac = ∠edf ⇒ bc = ef ∧ ∠abc = ∠def ∧ ∠acb = ∠dfe",
        section="§3.7",
    ))
    rules.append(RuleInfo(
        name="SSS Superposition",
        category="superposition",
        description="ab = de ∧ bc = ef ∧ ac = df ⇒ ∠bac = ∠edf ∧ ∠abc = ∠def ∧ ∠acb = ∠dfe",
        section="§3.7",
    ))

    # ── Structural rules ──────────────────────────────────────────
    rules.append(RuleInfo(
        name="Reit",
        category="structural",
        description="Γ ⊢ φ ⇒ Γ ⊢ φ  (reiterate a previously established fact)",
        section="§3.2",
    ))
    rules.append(RuleInfo(
        name="Assume",
        category="structural",
        description="Γ, ¬φ ⊢ …  (open a subproof by assuming ¬φ)",
        section="§3.2",
    ))
    rules.append(RuleInfo(
        name="⊥-intro",
        category="structural",
        description="ψ ∧ ¬ψ ⇒ ⊥  (exactly 2 cited deps required: one containing ψ, one containing ¬ψ. Also accepts X=Y + X<Y or X<Y + Y<X.)",
        section="§3.2",
    ))
    rules.append(RuleInfo(
        name="⊥-elim",
        category="structural",
        description="Γ, ¬φ ⊢ ⊥ ⇒ Γ ⊢ φ  (discharge assumption via contradiction)",
        section="§3.2",
    ))
    rules.append(RuleInfo(
        name="Cases",
        category="structural",
        description="φ ∨ ψ, (φ ⇒ χ), (ψ ⇒ χ) ⇒ χ  (disjunction elimination)",
        section="§3.2",
    ))
    rules.append(RuleInfo(
        name="Given",
        category="structural",
        description="Γ ⊢ φ where φ ∈ Γ  (cite a premise of the sequent)",
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
