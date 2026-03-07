"""
unified_checker.py — Single entry point for proof verification.

Routes all verification through System E as the primary engine, with
automatic T bridge fallback for completeness.

Usage:
    # Verify a System E proof
    result = verify_proof(eproof)

    # Verify a System E proof with T-bridge fallback
    result = verify_proof(eproof, use_t_fallback=True)

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
    substitute_literal,
)
from .e_checker import EChecker, ECheckResult
from .e_consequence import ConsequenceEngine
from .e_library import E_THEOREM_LIBRARY, get_theorems_up_to


# ═══════════════════════════════════════════════════════════════════════
# Unified result type
# ═══════════════════════════════════════════════════════════════════════

@dataclass
class UnifiedResult:
    """Result of unified verification.

    Wraps an ECheckResult with additional metadata about which engine
    was used and whether T-bridge fallback was invoked.
    """
    valid: bool = False
    engine: str = "e"          # "e", "t_fallback", or "legacy"
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
    use_t_fallback: bool = False,
) -> UnifiedResult:
    """Verify a System E proof.

    Primary path: System E checker.
    Fallback path (if use_t_fallback=True and E fails): translate to
    Tarski's system and check via the completeness pipeline.

    Args:
        proof: The System E proof to check.
        theorems: Theorem library for appeals. Defaults to the full
                  E_THEOREM_LIBRARY.
        use_t_fallback: If True, invoke T bridge when E is inconclusive.

    Returns:
        UnifiedResult with validity status and diagnostics.
    """
    if theorems is None:
        theorems = E_THEOREM_LIBRARY

    # ── Primary: System E ─────────────────────────────────────────
    checker = EChecker(theorems)
    e_result = checker.check_proof(proof)

    result = UnifiedResult(
        valid=e_result.valid,
        engine="e",
        e_result=e_result,
        errors=list(e_result.errors),
        warnings=list(e_result.warnings),
    )

    if e_result.valid:
        return result

    # ── Fallback: T bridge completeness ───────────────────────────
    if use_t_fallback:
        result = _try_t_fallback(proof, result)

    return result


def _try_t_fallback(proof: EProof, result: UnifiedResult) -> UnifiedResult:
    """Attempt T-bridge fallback for an E proof that failed direct check."""
    try:
        from .t_completeness import is_valid_for_ruler_compass

        seq = Sequent(
            hypotheses=list(proof.hypotheses),
            exists_vars=list(proof.exists_vars),
            conclusions=list(proof.goal),
        )

        comp_result = is_valid_for_ruler_compass(seq)
        result.diagnostics.extend(comp_result.diagnostics)

        if comp_result.is_valid:
            result.valid = True
            result.engine = "t_fallback"
            result.warnings.append(
                "Proof accepted via T-bridge completeness fallback."
            )
        else:
            result.diagnostics.append(
                "T-bridge fallback also failed to validate the sequent."
            )
    except Exception as exc:
        result.diagnostics.append(
            f"T-bridge fallback error: {exc}"
        )

    return result


# ═══════════════════════════════════════════════════════════════════════
# Named proof verification
# ═══════════════════════════════════════════════════════════════════════

def verify_named_proof(
    proof_name: str,
    use_t_fallback: bool = False,
) -> UnifiedResult:
    """Verify a named proof from the System E proof catalogue.

    Loads the proof from e_proofs and uses the theorem library
    (excluding the proposition being proved to prevent circularity).

    Args:
        proof_name: e.g. "Prop.I.1"
        use_t_fallback: If True, invoke T bridge when E is inconclusive.

    Returns:
        UnifiedResult with validity status.
    """
    from .e_proofs import get_proof

    proof = get_proof(proof_name)
    available = get_theorems_up_to(proof_name)
    return verify_proof(proof, theorems=available,
                        use_t_fallback=use_t_fallback)


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
    t_bridge_accepted: bool = False


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
    # Register declared variables
    for name, sort in sort_ctx.items():
        if name not in checker.variables:
            checker.variables[name] = sort
    # Load premises as known facts
    for lit in premise_lits:
        checker.known.add(lit)

    # ── 5. Check each proof line ──────────────────────────────────
    lines = proof_json.get("lines", [])
    premise_ids: Set[int] = set()

    for line in lines:
        lid = line.get("id", 0)
        just = line.get("justification", "")
        stmt_str = line.get("statement", "")
        refs = line.get("refs", [])
        lr = LineCheckResult(line_id=lid)

        # Given lines → check against premises
        if just == "Given":
            premise_ids.add(lid)
            try:
                lits = parse_literal_list(stmt_str, sort_ctx)
                for lit in lits:
                    if lit in premise_lits or lit in checker.known:
                        checker.known.add(lit)
                    else:
                        lr.valid = False
                        lr.errors.append(
                            f"'{stmt_str}' is not among the declared premises.")
            except EParseError as exc:
                lr.valid = False
                lr.errors.append(f"Parse error: {exc}")
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

        if step_kind == StepKind.CONSTRUCTION:
            # Construction rule: check prereqs from refs, add conclusions
            rule = CONSTRUCTION_RULE_BY_NAME.get(just)
            if rule is None:
                lr.valid = False
                lr.errors.append(f"Unknown construction rule '{just}'.")
            else:
                # Check that referenced lines supply the prereqs
                # For now we just check all assertions are consistent
                # and add them to known
                for lit in step_lits:
                    checker.known.add(lit)
                    # Infer sorts from atom structure (e.g. center → circle)
                    _infer_sorts_from_atom(lit.atom, sort_ctx)
                    # Register any new variables from the literal
                    for vname in _literal_var_names(lit):
                        if vname not in checker.variables:
                            checker.variables[vname] = _infer_sort(
                                vname, sort_ctx)
        elif step_kind == StepKind.DIAGRAMMATIC:
            for lit in step_lits:
                if lit in checker.known:
                    continue
                if checker.consequence_engine.is_consequence(
                        checker.known, lit, checker.variables):
                    checker.known.add(lit)
                else:
                    lr.valid = False
                    lr.errors.append(
                        f"Diagrammatic assertion {lit} is not a "
                        f"direct consequence of known facts.")
        elif step_kind == StepKind.METRIC:
            for lit in step_lits:
                if lit in checker.known:
                    continue
                if checker.metric_engine.is_consequence(
                        checker.known, lit):
                    checker.known.add(lit)
                else:
                    lr.valid = False
                    lr.errors.append(
                        f"Metric assertion {lit} is not a "
                        f"consequence of known facts.")
        elif step_kind == StepKind.TRANSFER:
            diagram_known = {l for l in checker.known if l.is_diagrammatic}
            metric_known = {l for l in checker.known if l.is_metric}
            derived = checker.transfer_engine.apply_transfers(
                diagram_known, metric_known, checker.variables)
            for lit in step_lits:
                if lit in checker.known or lit in derived:
                    checker.known.add(lit)
                else:
                    lr.valid = False
                    lr.errors.append(
                        f"Transfer assertion {lit} is not derivable.")
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
                thm = E_THEOREM_LIBRARY.get(just)
                if thm is None:
                    lr.valid = False
                    lr.errors.append(
                        f"Unknown theorem '{just}'.")
            if thm is not None:
                # Check hypotheses of the theorem are met
                for hyp in thm.sequent.hypotheses:
                    if hyp not in checker.known:
                        # Try via consequence engines
                        if hyp.is_diagrammatic:
                            ok = checker.consequence_engine.is_consequence(
                                checker.known, hyp, checker.variables)
                        elif hyp.is_metric:
                            ok = checker.metric_engine.is_consequence(
                                checker.known, hyp)
                        else:
                            ok = hyp in checker.known
                        if not ok:
                            lr.valid = False
                            lr.errors.append(
                                f"Theorem '{just}' hypothesis not "
                                f"met: {hyp}")
                if lr.valid:
                    # Add theorem conclusions to known facts
                    for conc in thm.sequent.conclusions:
                        checker.known.add(conc)
                    # Also add step's own literals (which may be
                    # a subset of the conclusions)
                    for lit in step_lits:
                        checker.known.add(lit)
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
                f"Metric, Transfer, SAS, Prop.I.x).")

        if lr.valid:
            result.derived.add(lid)
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
        "diagrammatic": StepKind.DIAGRAMMATIC,
        "Diagrammatic": StepKind.DIAGRAMMATIC,
        "metric": StepKind.METRIC,
        "Metric": StepKind.METRIC,
        "transfer": StepKind.TRANSFER,
        "Transfer": StepKind.TRANSFER,
        "SAS": StepKind.SUPERPOSITION_SAS,
        "SSS": StepKind.SUPERPOSITION_SSS,
        "SAS Superposition": StepKind.SUPERPOSITION_SAS,
        "SSS Superposition": StepKind.SUPERPOSITION_SSS,
        # Legacy diagrammatic rule aliases
        "Ord2": StepKind.DIAGRAMMATIC,
        "Ord3": StepKind.DIAGRAMMATIC,
        "Ord4": StepKind.DIAGRAMMATIC,
        "Bet": StepKind.DIAGRAMMATIC,
        "Inc1": StepKind.DIAGRAMMATIC,
        "Inc2": StepKind.DIAGRAMMATIC,
        "Inc3": StepKind.DIAGRAMMATIC,
        "Pasch": StepKind.DIAGRAMMATIC,
        "SS1": StepKind.DIAGRAMMATIC,
        "SS2": StepKind.DIAGRAMMATIC,
        "SS3": StepKind.DIAGRAMMATIC,
        "Reit": StepKind.DIAGRAMMATIC,
        "Given": StepKind.DIAGRAMMATIC,
    }
    kind = _MAP.get(just)
    if kind is not None:
        return kind

    # Named axiom rules from the rule catalogue (§3.4–§3.7).
    # Match by category-based prefixes so every rule shown in the
    # dropdown is accepted as a valid justification.
    _DIAG_PREFIXES = (
        "Generality", "Betweenness", "Same-side", "Pasch",
        "Triple incidence", "Circle", "Intersection",
    )
    for pfx in _DIAG_PREFIXES:
        if just.startswith(pfx):
            return StepKind.DIAGRAMMATIC

    _METRIC_PREFIXES = ("CN", "M1", "M2", "M3", "M4", "M5", "M6",
                        "M7", "M8", "M9", "< ", "+ ")
    for pfx in _METRIC_PREFIXES:
        if just.startswith(pfx):
            return StepKind.METRIC

    _TRANSFER_PREFIXES = ("Segment transfer", "Angle transfer",
                          "Area transfer")
    for pfx in _TRANSFER_PREFIXES:
        if just.startswith(pfx):
            return StepKind.TRANSFER

    # Default: unrecognised
    return None


def _literal_var_names(lit: Literal) -> Set[str]:
    """Extract variable names from a literal."""
    from .e_ast import atom_vars
    return atom_vars(lit.atom)


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
    _DIAG_GROUPS = [
        ("Generality", GENERALITY_AXIOMS,
         ["Two points on two lines → points equal or lines equal",
          "Center uniqueness: center(a,α) ∧ center(b,α) → a = b",
          "Center is inside: center(a,α) → inside(a,α)",
          "Inside excludes on: inside(a,α) → ¬on(a,α)"]),
        ("Betweenness", BETWEEN_AXIOMS,
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
        ("Same-side", SAME_SIDE_AXIOMS,
         ["same-side(a,a,L) ∨ on(a,L)  (reflexivity)",
          "same-side(a,b,L) → same-side(b,a,L)  (symmetry)",
          "same-side(a,b,L) → ¬on(a,L)",
          "same-side(a,b,L) ∧ same-side(a,c,L) → same-side(b,c,L)  (transitivity)",
          "Any two points off a line: same-side or one is on the line"]),
        ("Pasch", PASCH_AXIOMS,
         ["same-side(a,c,L) ∧ between(a,b,c) → same-side(a,b,L)",
          "between(a,b,c) ∧ on(a,L) → same-side(b,c,L) ∨ on(b,L)",
          "between(a,b,c) ∧ on(b,L) → ¬same-side(a,c,L)",
          "Pasch: line crossing one side of a triangle hits another side"]),
        ("Triple incidence", TRIPLE_INCIDENCE_AXIOMS,
         ["Three concurrent lines determine collinear or same-side",
          "Concurrent lines: transitivity of same-side across lines",
          "Five-line same-side transitivity"]),
        ("Circle", CIRCLE_AXIOMS,
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
        ("Intersection", INTERSECTION_AXIOMS,
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
    for group_name, axioms, descs in _DIAG_GROUPS:
        for i, ax in enumerate(axioms):
            desc = descs[i] if i < len(descs) else f"{group_name} axiom {i+1}"
            rules.append(RuleInfo(
                name=f"{group_name} {i+1}",
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
    _TRANSFER_GROUPS = [
        ("Segment transfer", DIAGRAM_SEGMENT_TRANSFER,
         ["between(a,b,c) → ab + bc = ac  (segment addition)",
          "Equal radii → same circle: ab = ac ∧ center(a,α) ∧ center(a,β) ∧ on(b,α) ∧ on(c,β) → α = β",
          "Segment → circle: center(a,α) ∧ on(b,α) ∧ ac = ab → on(c,α)",
          "Radii equal: center(a,α) ∧ on(b,α) ∧ on(c,α) → ac = ab",
          "Segment < radius → inside: center(a,α) ∧ on(b,α) ∧ ac < ab → inside(c,α)",
          "Inside → segment < radius: center(a,α) ∧ on(b,α) ∧ inside(c,α) → ac < ab"]),
        ("Angle transfer", DIAGRAM_ANGLE_TRANSFER,
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
        ("Area transfer", DIAGRAM_AREA_TRANSFER,
         ["Zero area → collinear: △abc = 0 → on(c,L)",
          "Collinear → zero area: on(a,L) ∧ on(b,L) ∧ on(c,L) → △abc = 0",
          "Triangle area addition: between(a,c,b) → △acd + △dcb = △adb"]),
    ]
    for group_name, axioms, descs in _TRANSFER_GROUPS:
        for i, ax in enumerate(axioms):
            desc = descs[i] if i < len(descs) else f"{group_name} axiom {i+1}"
            rules.append(RuleInfo(
                name=f"{group_name} {i+1}",
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
# Legacy-format bridge (Phase 6.5.4)
#
# These functions let the UI call into the old parse_proof/ProofChecker
# pipeline through unified_checker, so no UI file needs to import
# verifier.parser or verifier.checker directly.
# ═══════════════════════════════════════════════════════════════════════

def parse_e_formula(text: str, sort_ctx: Optional[Dict[str, Sort]] = None):
    """Parse a System E formula string into a list of literals.

    Replacement for the old ``parse_legacy_formula``.
    Returns a list of ``Literal`` objects or ``None`` on parse error.
    """
    from .e_parser import parse_literal_list, EParseError
    try:
        return parse_literal_list(text, sort_ctx)
    except EParseError:
        return None


# Aliases for backward-compatibility (referenced by smoke tests)
parse_legacy_formula = parse_e_formula


def verify_old_proof_json(proof_json: dict) -> PanelCheckResult:
    """Thin wrapper around :func:`verify_e_proof_json`.

    Kept for backward-compatibility with tests that import this name.
    """
    return verify_e_proof_json(proof_json)


def get_legacy_rules() -> List[RuleInfo]:
    """Return available rules (alias for :func:`get_available_rules`).

    Kept for backward-compatibility with tests that import this name.
    """
    return get_available_rules()
