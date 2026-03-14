"""
e_backward.py — Backward-chaining proof search for System E.

Given a goal (set of literals) and a set of known facts (premises),
searches backward to find a sequence of proof steps that derives the
goal.  The search considers:

  - Diagrammatic closure (automatic)
  - Transfer axioms (segment/angle/area sums from betweenness/angles)
  - Metric rules (transitivity, cancellation, substitution)
  - Theorem application (I.1, I.2, ..., up to the current proposition)
  - SAS / SSS superposition

This is a depth-limited prototype — it does NOT handle constructions
(let-line, let-circle, let-intersection-*) which require existential
witnesses.  Construction steps must still be provided by the proof
writer.  The search fills in the logical derivation steps that follow
from known facts and explicit constructions.

Usage::

    from verifier.e_backward import backward_search
    steps = backward_search(premises, goals, variables,
                            available_theorems=["Prop.I.1", ...])
    for step in steps:
        print(step)
"""
from __future__ import annotations

from dataclasses import dataclass, field
from typing import Dict, FrozenSet, List, Optional, Set, Tuple

from .e_ast import (
    Sort, Literal, Sequent, ETheorem,
    Equals, LessThan,
    SegmentTerm, AngleTerm, AreaTerm, MagAdd, RightAngle, ZeroMag,
    On, SameSide, Between, Center, Inside, Intersects,
    substitute_literal, literal_vars,
)
from .e_axioms import ALL_DIAGRAMMATIC_AXIOMS, ALL_TRANSFER_AXIOMS
from .e_consequence import ConsequenceEngine
from .e_transfer import TransferEngine
from .e_metric import MetricEngine


@dataclass
class ProofHint:
    """A suggested proof step from backward search."""
    statement: str
    justification: str
    explanation: str = ""

    def __repr__(self) -> str:
        s = f"{self.statement}  [{self.justification}]"
        if self.explanation:
            s += f"  -- {self.explanation}"
        return s


@dataclass
class SearchResult:
    """Result of a backward-chaining proof search."""
    found: bool = False
    hints: List[ProofHint] = field(default_factory=list)
    unsatisfied: List[Literal] = field(default_factory=list)
    closure_facts: Set[Literal] = field(default_factory=set)
    transfer_facts: Set[Literal] = field(default_factory=set)
    metric_facts: Set[Literal] = field(default_factory=set)

    def print_report(self) -> None:
        """Pretty-print the search result."""
        import sys
        out = sys.stdout
        if self.found:
            out.write("✓ All goals derivable.\n")
        else:
            out.write("✗ Some goals NOT derivable.\n")
            out.write(f"  Unsatisfied: {self.unsatisfied}\n")
        if self.hints:
            out.write(f"\n  Suggested proof steps ({len(self.hints)}):\n")
            for i, hint in enumerate(self.hints, 1):
                out.write(f"    {i}. {hint}\n")


def backward_search(
    known: Set[Literal],
    goals: List[Literal],
    variables: Dict[str, Sort],
    *,
    available_theorems: Optional[Dict[str, ETheorem]] = None,
    max_depth: int = 3,
) -> SearchResult:
    """Search backward from goals to known facts.

    Args:
        known: Set of known literals (premises + derived so far).
        goals: Literals we want to derive.
        variables: Variable name → sort mapping.
        available_theorems: Theorems that may be applied.
        max_depth: Maximum search depth for recursive subgoals.

    Returns:
        SearchResult with hints for proof steps.
    """
    result = SearchResult()

    # Phase 1: Compute what's already derivable
    ce = ConsequenceEngine(ALL_DIAGRAMMATIC_AXIOMS)
    closure = ce.direct_consequences(known, variables)
    result.closure_facts = closure

    diagram_known = {lit for lit in closure if lit.is_diagrammatic}
    metric_known = {lit for lit in closure if lit.is_metric}

    te = TransferEngine(ALL_TRANSFER_AXIOMS)
    transfer_derived = te.apply_transfers(
        diagram_known, metric_known, variables)
    result.transfer_facts = transfer_derived

    me = MetricEngine()
    all_metric = metric_known | {lit for lit in transfer_derived
                                 if lit.is_metric}
    metric_derived = me.process_literals(all_metric)
    result.metric_facts = metric_derived

    all_derivable = closure | transfer_derived | metric_derived

    # Phase 2: Check each goal
    remaining_goals = []
    for goal in goals:
        if goal in known:
            result.hints.append(ProofHint(
                repr(goal), "Given/Known",
                "already in known set"))
        elif goal in closure:
            result.hints.append(ProofHint(
                repr(goal), "Diagrammatic",
                "derivable from diagrammatic closure"))
        elif goal in transfer_derived:
            # Determine transfer type
            _jtype = _classify_transfer(goal)
            result.hints.append(ProofHint(
                repr(goal), "Transfer",
                f"derivable via {_jtype}"))
        elif goal in metric_derived:
            result.hints.append(ProofHint(
                repr(goal), "Metric",
                "derivable from metric engine"))
        elif _check_metric_with_transfer(goal, all_metric, me):
            result.hints.append(ProofHint(
                repr(goal), "Metric",
                "derivable via transfer → metric chain"))
        else:
            remaining_goals.append(goal)

    # Phase 3: Try deeper search for remaining goals
    if remaining_goals and max_depth > 0:
        for goal in list(remaining_goals):
            found = _deep_search(
                goal, known, closure, transfer_derived, metric_derived,
                variables, available_theorems, max_depth - 1, result)
            if found:
                remaining_goals.remove(goal)

    result.unsatisfied = remaining_goals
    result.found = len(remaining_goals) == 0
    return result


def _classify_transfer(lit: Literal) -> str:
    """Classify what kind of transfer produced this literal."""
    atom = lit.atom
    if isinstance(atom, Equals):
        left, right = atom.left, atom.right
        if isinstance(left, MagAdd) or isinstance(right, MagAdd):
            if _any_term_is(left, SegmentTerm) or _any_term_is(
                    right, SegmentTerm):
                return "betweenness → segment sum"
            if _any_term_is(left, AngleTerm) or _any_term_is(
                    right, AngleTerm):
                return "angle sum (DA2)"
            if _any_term_is(left, AreaTerm) or _any_term_is(
                    right, AreaTerm):
                return "area decomposition (DAr2)"
        if _any_term_is(left, SegmentTerm) or _any_term_is(
                right, SegmentTerm):
            return "segment equality"
        if _any_term_is(left, AngleTerm) or _any_term_is(
                right, AngleTerm):
            return "angle equality"
    elif isinstance(atom, LessThan):
        return "inequality transfer"
    return "transfer"


def _any_term_is(term, cls) -> bool:
    """Check if a term or any sub-term is an instance of cls."""
    if isinstance(term, cls):
        return True
    if isinstance(term, MagAdd):
        return _any_term_is(term.left, cls) or _any_term_is(term.right, cls)
    return False


def _check_metric_with_transfer(
    goal: Literal,
    all_metric: Set[Literal],
    me: MetricEngine,
) -> bool:
    """Check if goal is derivable from metric engine on combined facts."""
    combined = all_metric | {goal}  # Check if adding goal is consistent
    return me.is_consequence(all_metric, goal)


def _deep_search(
    goal: Literal,
    known: Set[Literal],
    closure: Set[Literal],
    transfer_derived: Set[Literal],
    metric_derived: Set[Literal],
    variables: Dict[str, Sort],
    available_theorems: Optional[Dict[str, ETheorem]],
    depth: int,
    result: SearchResult,
) -> bool:
    """Try to find goal via theorem application or multi-step reasoning.

    Returns True if goal can be derived, adding hints to result.
    """
    all_derivable = closure | transfer_derived | metric_derived

    # Strategy 1: Check if SAS/SSS can produce this goal
    sas_hint = _check_sas_sss(goal, all_derivable)
    if sas_hint is not None:
        result.hints.append(sas_hint)
        return True

    # Strategy 2: Check if a theorem can produce this goal
    if available_theorems:
        for thm_name, thm in available_theorems.items():
            match = _theorem_produces(thm, goal, all_derivable, variables)
            if match is not None:
                unmet, matched_concls = match
                if not unmet:
                    # All hypotheses satisfied
                    concl_str = ", ".join(repr(c) for c in matched_concls)
                    result.hints.append(ProofHint(
                        concl_str, thm_name,
                        f"all hypotheses satisfied"))
                    return True
                elif depth > 0:
                    # Try to satisfy unmet hypotheses recursively
                    # (only if few remain)
                    if len(unmet) <= 2:
                        sub_result = backward_search(
                            known | all_derivable, unmet, variables,
                            available_theorems=available_theorems,
                            max_depth=depth)
                        if sub_result.found:
                            result.hints.extend(sub_result.hints)
                            concl_str = ", ".join(
                                repr(c) for c in matched_concls)
                            result.hints.append(ProofHint(
                                concl_str, thm_name,
                                "hypotheses satisfied via sub-search"))
                            return True

    # Strategy 3: For metric equalities, try substitution with known
    # equalities to transform the goal into a derivable form
    if isinstance(goal.atom, Equals) and goal.polarity:
        me = MetricEngine()
        processed = me.process_literals(
            {lit for lit in all_derivable if lit.is_metric})
        if goal in processed:
            result.hints.append(ProofHint(
                repr(goal), "Metric",
                "derivable via extended metric processing"))
            return True

    return False


def _check_sas_sss(
    goal: Literal,
    known: Set[Literal],
) -> Optional[ProofHint]:
    """Check if SAS or SSS can produce the goal literal.

    Looks for triangle congruence patterns in the known facts and
    checks if the goal is a conclusion of SAS or SSS.
    """
    from .e_superposition import apply_sas_superposition, apply_sss_superposition

    atom = goal.atom
    if not goal.polarity:
        return None

    # Strategy 1: Extract triangle pairs directly from the goal
    triangles = _extract_triangle_pair(atom)
    for (a, b, c, d, e, f) in triangles:
        # Try SAS
        sas_result = apply_sas_superposition(known, a, b, c, d, e, f)
        if sas_result.valid and goal in sas_result.derived:
            return ProofHint(
                ", ".join(repr(lit) for lit in sas_result.derived),
                "SAS",
                f"from {a}{b}={d}{e}, {a}{c}={d}{f}, "
                f"\u2220{b}{a}{c}=\u2220{e}{d}{f}")

        # Try SSS
        sss_result = apply_sss_superposition(known, a, b, c, d, e, f)
        if sss_result.valid and goal in sss_result.derived:
            return ProofHint(
                ", ".join(repr(lit) for lit in sss_result.derived),
                "SSS",
                f"from {a}{b}={d}{e}, {b}{c}={e}{f}, {c}{a}={f}{d}")

    # Strategy 2: For segment equalities, find SAS/SSS from known
    # segment/angle equalities by enumerating candidate triangles.
    if (isinstance(atom, Equals)
            and isinstance(atom.left, SegmentTerm)
            and isinstance(atom.right, SegmentTerm)):
        seg_goal = atom
        # Collect known segment equalities between different triangles
        seg_eqs = []
        angle_eqs = []
        for lit in known:
            if lit.polarity and isinstance(lit.atom, Equals):
                if isinstance(lit.atom.left, SegmentTerm):
                    seg_eqs.append(lit.atom)
                elif isinstance(lit.atom.left, AngleTerm):
                    angle_eqs.append(lit.atom)

        # For each angle equality ∠bac = ∠edf, try SAS with those
        # triangles
        for aeq in angle_eqs:
            al, ar = aeq.left, aeq.right
            if isinstance(al, AngleTerm) and isinstance(ar, AngleTerm):
                a, b, c = al.p1, al.p2, al.p3
                d, e, f = ar.p1, ar.p2, ar.p3
                sas_r = apply_sas_superposition(known, b, a, c, e, d, f)
                if sas_r.valid and goal in sas_r.derived:
                    return ProofHint(
                        ", ".join(repr(l) for l in sas_r.derived),
                        "SAS",
                        f"from angle \u2220{a}{b}{c}=\u2220{d}{e}{f}")
                sas_r = apply_sas_superposition(known, c, b, a, f, e, d)
                if sas_r.valid and goal in sas_r.derived:
                    return ProofHint(
                        ", ".join(repr(l) for l in sas_r.derived),
                        "SAS",
                        f"from angle \u2220{a}{b}{c}=\u2220{d}{e}{f}")

    return None


def _extract_triangle_pair(atom) -> List[Tuple[str, str, str, str, str, str]]:
    """Extract (a,b,c,d,e,f) triangle pairs from an equality atom.

    Works for segment, angle, and area equalities between two
    triangles' corresponding parts.
    """
    if not isinstance(atom, Equals):
        return []

    left, right = atom.left, atom.right
    pairs = []

    if isinstance(left, SegmentTerm) and isinstance(right, SegmentTerm):
        # bc = ef → triangles (?, b, c) and (?, e, f)
        # Try all possible vertex orderings
        pass  # Too ambiguous for segment alone

    elif isinstance(left, AngleTerm) and isinstance(right, AngleTerm):
        # ∠abc = ∠def → triangles (a, b, c) and (d, e, f)
        pairs.append((left.p1, left.p2, left.p3,
                       right.p1, right.p2, right.p3))
        # Also try reversed vertex ordering
        pairs.append((left.p3, left.p2, left.p1,
                       right.p3, right.p2, right.p1))

    elif isinstance(left, AreaTerm) and isinstance(right, AreaTerm):
        # △abc = △def → triangles (a, b, c) and (d, e, f)
        pairs.append((left.p1, left.p2, left.p3,
                       right.p1, right.p2, right.p3))

    return pairs


def _theorem_produces(
    thm: ETheorem,
    goal: Literal,
    known: Set[Literal],
    variables: Dict[str, Sort],
) -> Optional[Tuple[List[Literal], List[Literal]]]:
    """Check if theorem can produce a literal matching goal.

    Returns (unmet_hypotheses, matched_conclusions) or None if
    the theorem doesn't match.
    """
    seq = thm.sequent

    # Try to match goal against each conclusion
    for concl in seq.conclusions:
        # Try to find a substitution that maps concl to goal
        subst = _match_literal(concl, goal, seq.exists_vars)
        if subst is not None:
            # Apply substitution to hypotheses and check
            unmet = []
            for hyp in seq.hypotheses:
                sub_hyp = substitute_literal(hyp, subst)
                if sub_hyp not in known:
                    unmet.append(sub_hyp)
            # Apply substitution to all conclusions
            matched = [substitute_literal(c, subst)
                       for c in seq.conclusions]
            return (unmet, matched)

    return None


def _match_literal(
    pattern: Literal,
    target: Literal,
    exists_vars: List[Tuple[str, Sort]],
) -> Optional[Dict[str, str]]:
    """Try to match a pattern literal against a target literal.

    Returns a substitution dict {pattern_var -> target_var} or None.
    """
    if pattern.polarity != target.polarity:
        return None
    return _match_atom(pattern.atom, target.atom, exists_vars)


def _match_atom(pattern, target, exists_vars) -> Optional[Dict[str, str]]:
    """Try to match a pattern atom against a target atom."""
    if type(pattern) != type(target):
        return None

    subst: Dict[str, str] = {}
    exists_names = {v for v, _ in exists_vars}

    if isinstance(pattern, On):
        if not _unify(pattern.point, target.point, subst, exists_names):
            return None
        if not _unify(pattern.line, target.line, subst, exists_names):
            return None
        return subst

    elif isinstance(pattern, SameSide):
        if not _unify(pattern.p1, target.p1, subst, exists_names):
            return None
        if not _unify(pattern.p2, target.p2, subst, exists_names):
            return None
        if not _unify(pattern.line, target.line, subst, exists_names):
            return None
        return subst

    elif isinstance(pattern, Between):
        if not _unify(pattern.p1, target.p1, subst, exists_names):
            return None
        if not _unify(pattern.p2, target.p2, subst, exists_names):
            return None
        if not _unify(pattern.p3, target.p3, subst, exists_names):
            return None
        return subst

    elif isinstance(pattern, Equals):
        if isinstance(pattern.left, str) and isinstance(target.left, str):
            # Point equality
            if not _unify(pattern.left, target.left, subst, exists_names):
                return None
            if not _unify(pattern.right, target.right, subst, exists_names):
                return None
            return subst
        elif isinstance(pattern.left, SegmentTerm):
            return _match_term_eq(pattern, target, subst, exists_names)
        elif isinstance(pattern.left, AngleTerm):
            return _match_term_eq(pattern, target, subst, exists_names)
        elif isinstance(pattern.left, AreaTerm):
            return _match_term_eq(pattern, target, subst, exists_names)

    elif isinstance(pattern, LessThan):
        return _match_term_eq_as_ineq(pattern, target, subst, exists_names)

    return None


def _match_term_eq(pattern_eq, target_eq, subst, exists_names):
    """Match Equals(term1, term2) patterns."""
    if not _match_term(pattern_eq.left, target_eq.left, subst, exists_names):
        return None
    if not _match_term(pattern_eq.right, target_eq.right, subst, exists_names):
        return None
    return subst


def _match_term_eq_as_ineq(pattern_lt, target_lt, subst, exists_names):
    """Match LessThan(term1, term2) patterns."""
    if not _match_term(pattern_lt.left, target_lt.left, subst, exists_names):
        return None
    if not _match_term(pattern_lt.right, target_lt.right, subst, exists_names):
        return None
    return subst


def _match_term(pattern, target, subst, exists_names) -> bool:
    """Match a single term, updating subst in place."""
    if type(pattern) != type(target):
        return False

    if isinstance(pattern, SegmentTerm):
        return (_unify(pattern.p1, target.p1, subst, exists_names)
                and _unify(pattern.p2, target.p2, subst, exists_names))
    elif isinstance(pattern, AngleTerm):
        return (_unify(pattern.p1, target.p1, subst, exists_names)
                and _unify(pattern.p2, target.p2, subst, exists_names)
                and _unify(pattern.p3, target.p3, subst, exists_names))
    elif isinstance(pattern, AreaTerm):
        return (_unify(pattern.p1, target.p1, subst, exists_names)
                and _unify(pattern.p2, target.p2, subst, exists_names)
                and _unify(pattern.p3, target.p3, subst, exists_names))
    elif isinstance(pattern, MagAdd):
        return (_match_term(pattern.left, target.left, subst, exists_names)
                and _match_term(pattern.right, target.right, subst, exists_names))
    elif isinstance(pattern, RightAngle):
        return isinstance(target, RightAngle)
    elif isinstance(pattern, ZeroMag):
        return isinstance(target, ZeroMag) and pattern.sort == target.sort
    return False


def _unify(pvar: str, tvar: str, subst: Dict[str, str],
           exists_names: set) -> bool:
    """Unify a pattern variable with a target variable.

    Free variables in the pattern (including exists_vars) can bind to
    any target variable.  Already-bound variables must match consistently.
    """
    if pvar in subst:
        return subst[pvar] == tvar
    subst[pvar] = tvar
    return True
