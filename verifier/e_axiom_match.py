"""
e_axiom_match.py — Specific axiom matching for System E verification.

Given a named axiom (e.g. "Pasch 3"), the facts from cited dependency
lines, and the target conclusion, verifies that the specific axiom
derives the target from the cited facts.

This replaces the generic consequence-derivation approach where ANY
axiom from the category could satisfy the check.  Now the verifier
ensures the EXACT cited axiom applies.
"""
from __future__ import annotations

from itertools import product
from typing import Dict, FrozenSet, List, Optional, Set, Tuple

from .e_ast import (
    Atom, Literal, Clause, Sort,
    On, SameSide, Between, Center, Inside, Intersects,
    Equals, LessThan, DisjunctionAtom,
    SegmentTerm, AngleTerm, AreaTerm, MagAdd, RightAngle, ZeroMag,
    atom_vars, substitute_literal, literal_vars,
)
from .e_axioms import (
    GENERALITY_AXIOMS, BETWEEN_AXIOMS, SAME_SIDE_AXIOMS,
    PASCH_AXIOMS, TRIPLE_INCIDENCE_AXIOMS, CIRCLE_AXIOMS,
    INTERSECTION_AXIOMS,
    DIAGRAM_SEGMENT_TRANSFER, DIAGRAM_ANGLE_TRANSFER,
    DIAGRAM_AREA_TRANSFER,
)


# ═══════════════════════════════════════════════════════════════════════
# AXIOM NAME REGISTRY
# ═══════════════════════════════════════════════════════════════════════

_AXIOM_REGISTRY: Dict[str, Clause] = {}


def _register_group(
    prefix: str,
    axioms: List[Clause],
    labels: Optional[List[str]] = None,
) -> None:
    """Register axioms under '{prefix} {label}' keys.

    Also registers 1-based sequential numeric aliases when the labels
    use sub-labels (e.g. "2a", "2b") so that both ``Intersection 5``
    (formal label) and ``Intersection 9`` (sequential index) resolve to
    the same clause.  Numeric aliases are only added when they would NOT
    collide with an existing formal label for the same group.
    """
    for i, ax in enumerate(axioms):
        label = labels[i] if labels else str(i + 1)
        name = f"{prefix} {label}"
        _AXIOM_REGISTRY[name] = ax

    # Add sequential numeric aliases (1-based) for groups whose labels
    # are not already purely sequential integers.
    if labels is not None:
        for i, ax in enumerate(axioms):
            seq_label = str(i + 1)
            seq_name = f"{prefix} {seq_label}"
            # Only add if it does not collide with a formal label
            if seq_name not in _AXIOM_REGISTRY:
                _AXIOM_REGISTRY[seq_name] = ax


def _build_registry() -> None:
    """Build the mapping from axiom names to their clause objects."""
    if _AXIOM_REGISTRY:
        return  # Already built

    # Diagrammatic axiom groups
    _register_group("Generality", GENERALITY_AXIOMS,
                     ["1", "2", "3", "4", "5", "5c", "5d", "6", "6c"])
    _BETWEEN_LABELS = ["1a", "1b", "1c", "1d", "2", "3", "4", "5", "6", "7"]
    _register_group("Betweenness", BETWEEN_AXIOMS, _BETWEEN_LABELS)
    _register_group("Same-side", SAME_SIDE_AXIOMS)
    _register_group("Pasch", PASCH_AXIOMS)
    _register_group("Triple incidence", TRIPLE_INCIDENCE_AXIOMS)
    _CIRCLE_LABELS = ["1", "2a", "2b", "2c", "2d", "3a", "3b", "3c", "3d", "4"]
    _register_group("Circle", CIRCLE_AXIOMS, _CIRCLE_LABELS)
    _INTER_LABELS = ["1", "2a", "2b", "2c", "2d", "3", "4a", "4b", "5", "6"]
    _register_group("Intersection", INTERSECTION_AXIOMS, _INTER_LABELS)

    # Transfer axiom groups
    _SEG_LABELS = ["1", "2", "3a", "3b", "4a", "4b", "4c", "4d"]
    _register_group("Segment transfer", DIAGRAM_SEGMENT_TRANSFER, _SEG_LABELS)
    _ANG_LABELS = [
        "1a", "1b", "1c", "2a", "2b", "2c", "3a", "3b",
        "4", "5a", "5b", "6", "7",
    ]
    _register_group("Angle transfer", DIAGRAM_ANGLE_TRANSFER, _ANG_LABELS)
    _AREA_LABELS = ["1a", "1b", "1c", "2"]
    _register_group("Area transfer", DIAGRAM_AREA_TRANSFER, _AREA_LABELS)


def get_axiom_clause(name: str) -> Optional[Clause]:
    """Look up the clause for a named axiom.  Returns None if unknown."""
    _build_registry()
    return _AXIOM_REGISTRY.get(name)


def list_axiom_names() -> List[str]:
    """Return all registered axiom names."""
    _build_registry()
    return list(_AXIOM_REGISTRY.keys())


# ═══════════════════════════════════════════════════════════════════════
# VARIABLE SORT INFERENCE (from schema clauses)
# ═══════════════════════════════════════════════════════════════════════

def _infer_schema_sorts(clause: Clause) -> Dict[str, Sort]:
    """Infer sorts of schema variables from their positions in the clause."""
    sorts: Dict[str, Sort] = {}
    # Sort literals before iterating so that sort inference is deterministic
    # regardless of PYTHONHASHSEED (FrozenSet iteration order varies across
    # Python process restarts, which can misclassify ambiguous schema vars).
    for lit in sorted(clause.literals, key=lambda l: repr(l)):
        _collect_sorts(lit.atom, sorts)
    return sorts


def _collect_sorts(atom: Atom, out: Dict[str, Sort]) -> None:
    """Collect variable-sort mappings from an atom."""
    if isinstance(atom, On):
        out.setdefault(atom.point, Sort.POINT)
        if atom.obj not in out:
            out[atom.obj] = _sort_from_name(atom.obj)
    elif isinstance(atom, SameSide):
        out.setdefault(atom.a, Sort.POINT)
        out.setdefault(atom.b, Sort.POINT)
        out.setdefault(atom.line, Sort.LINE)
    elif isinstance(atom, Between):
        out.setdefault(atom.a, Sort.POINT)
        out.setdefault(atom.b, Sort.POINT)
        out.setdefault(atom.c, Sort.POINT)
    elif isinstance(atom, Center):
        out.setdefault(atom.point, Sort.POINT)
        out.setdefault(atom.circle, Sort.CIRCLE)
    elif isinstance(atom, Inside):
        out.setdefault(atom.point, Sort.POINT)
        out.setdefault(atom.circle, Sort.CIRCLE)
    elif isinstance(atom, Intersects):
        # Could be line-line, line-circle, or circle-circle
        if atom.obj1 not in out:
            out[atom.obj1] = _sort_from_name(atom.obj1)
        if atom.obj2 not in out:
            out[atom.obj2] = _sort_from_name(atom.obj2)
    elif isinstance(atom, Equals):
        _collect_term_sorts(atom.left, out)
        _collect_term_sorts(atom.right, out)
    elif isinstance(atom, LessThan):
        _collect_term_sorts(atom.left, out)
        _collect_term_sorts(atom.right, out)
    elif isinstance(atom, DisjunctionAtom):
        for d in atom.disjuncts:
            _collect_sorts(d.atom, out)


def _collect_term_sorts(t, out: Dict[str, Sort]) -> None:
    """Collect sorts from a term (magnitude expressions use POINT vars)."""
    if isinstance(t, str):
        # Bare string var in Equals — could be line or point
        if t not in out:
            out[t] = _sort_from_name(t)
    elif isinstance(t, SegmentTerm):
        out.setdefault(t.p1, Sort.POINT)
        out.setdefault(t.p2, Sort.POINT)
    elif isinstance(t, AngleTerm):
        out.setdefault(t.p1, Sort.POINT)
        out.setdefault(t.p2, Sort.POINT)
        out.setdefault(t.p3, Sort.POINT)
    elif isinstance(t, AreaTerm):
        out.setdefault(t.p1, Sort.POINT)
        out.setdefault(t.p2, Sort.POINT)
        out.setdefault(t.p3, Sort.POINT)
    elif isinstance(t, MagAdd):
        _collect_term_sorts(t.left, out)
        _collect_term_sorts(t.right, out)


def _sort_from_name(name: str) -> Sort:
    """Guess sort from naming convention (schema variable names)."""
    if name in ("\u03b1", "\u03b2", "\u03b3", "\u03b4"):
        return Sort.CIRCLE
    if len(name) == 1 and name.isupper():
        return Sort.LINE
    return Sort.POINT


# ═══════════════════════════════════════════════════════════════════════
# SPECIFIC AXIOM MATCHING
# ═══════════════════════════════════════════════════════════════════════

def check_specific_axiom(
    axiom_name: str,
    dep_facts: Set[Literal],
    target_literals: List[Literal],
    variables: Dict[str, Sort],
) -> Tuple[bool, Optional[str]]:
    """Check if the named axiom derives the target(s) from dep_facts.

    Parameters
    ----------
    axiom_name : str
        The specific axiom cited (e.g. "Pasch 3").
    dep_facts : Set[Literal]
        Literals from the cited dependency lines.
    target_literals : List[Literal]
        The literal(s) the step claims to derive.
    variables : Dict[str, Sort]
        All concrete variable names and their sorts from the proof.

    Returns
    -------
    (success, error_message)
        success=True if all targets are derivable; error_message explains
        any failure.
    """
    ok, err, _premises = check_specific_axiom_with_premises(
        axiom_name, dep_facts, target_literals, variables)
    return ok, err


def check_specific_axiom_with_premises(
    axiom_name: str,
    dep_facts: Set[Literal],
    target_literals: List[Literal],
    variables: Dict[str, Sort],
) -> Tuple[bool, Optional[str], Set[Literal]]:
    """Like check_specific_axiom but also returns the required premises.

    Returns
    -------
    (success, error_message, required_premises)
        required_premises is the set of instantiated premise literals
        that the axiom actually needed from dep_facts.  Empty on failure.
    """
    clause = get_axiom_clause(axiom_name)
    if clause is None:
        return False, f"Unknown axiom '{axiom_name}'.", set()

    known = set(dep_facts)
    all_premises: Set[Literal] = set()

    for target in target_literals:
        ok, premises = _match_single(clause, known, target, variables)
        if not ok:
            return False, (
                f"Axiom '{axiom_name}' does not derive {target} "
                f"from the cited dependencies."
            ), set()
        all_premises |= premises
        known.add(target)

    return True, None, all_premises


def _match_single(
    clause: Clause,
    known: Set[Literal],
    target: Literal,
    variables: Dict[str, Sort],
) -> Tuple[bool, Set[Literal]]:
    """Check if one specific clause derives `target` from `known`.

    Uses constraint-guided matching: unify the target with each
    candidate literal in the clause, then verify that ALL remaining
    literals are resolved (their negation is in `known`).

    Returns (success, required_premises) where required_premises is the
    set of instantiated premise literals needed from known.
    """
    schema_sorts = _infer_schema_sorts(clause)

    # Partition concrete variables by sort (sorted for determinism —
    # _dep_vars insertion order depends on set iteration which varies
    # with PYTHONHASHSEED).
    points = sorted(v for v, s in variables.items() if s == Sort.POINT)
    lines = sorted(v for v, s in variables.items() if s == Sort.LINE)
    circles = sorted(v for v, s in variables.items() if s == Sort.CIRCLE)

    # Also extract variables from the target and dep_facts that might
    # not be in the proof-level variables dict
    for lit in known | {target}:
        for vname in literal_vars(lit):
            if vname not in variables:
                s = _sort_from_name(vname)
                if s == Sort.POINT and vname not in points:
                    points.append(vname)
                elif s == Sort.LINE and vname not in lines:
                    lines.append(vname)
                elif s == Sort.CIRCLE and vname not in circles:
                    circles.append(vname)

    schema_vars = list(schema_sorts.items())

    return _match_constrained(clause, schema_vars, known,
                              target, points, lines, circles)


def _match_constrained(
    clause: Clause,
    schema_vars: List[Tuple[str, Sort]],
    known: Set[Literal],
    target: Literal,
    points: List[str],
    lines: List[str],
    circles: List[str],
) -> Tuple[bool, Set[Literal]]:
    """Constraint-guided axiom matching.

    For each literal in the clause, try to unify it with the target.
    If unification succeeds, extend the substitution for any remaining
    schema variables and verify that ALL other literals are resolved
    (their negation is in ``known``).

    Returns (success, required_premises).
    """
    clause_lits = list(clause.literals)

    for i, candidate in enumerate(clause_lits):
        # Try to unify this literal with the target (may yield
        # multiple substitutions for symmetric atoms like Equals)
        subs = _unify_literal_all(candidate, target)

        for sub in subs:
            # Extend the substitution to cover remaining schema vars
            remaining_vars = [
                (name, sort) for name, sort in schema_vars
                if name not in sub
            ]

            if not remaining_vars:
                # Fully bound — check if all other literals are resolved
                premises = _collect_premises(
                    clause_lits, i, sub, known)
                if premises is not None:
                    return True, premises
                continue

            # Build pools for remaining vars
            rem_pools = []
            for name, sort in remaining_vars:
                if sort == Sort.POINT:
                    rem_pools.append(points)
                elif sort == Sort.LINE:
                    rem_pools.append(lines)
                elif sort == Sort.CIRCLE:
                    rem_pools.append(circles)
                else:
                    rem_pools.append([])

            rem_names = [name for name, _ in remaining_vars]

            est = 1
            for p in rem_pools:
                est *= max(len(p), 1)
            if est > 500_000:
                continue  # Still too large, skip this candidate

            for combo in product(*rem_pools):
                full_sub = dict(sub)
                full_sub.update(zip(rem_names, combo))
                premises = _collect_premises(
                    clause_lits, i, full_sub, known)
                if premises is not None:
                    return True, premises

    return False, set()


def _check_remaining(
    clause_lits: list,
    conclusion_idx: int,
    sub: Dict[str, str],
    known: Set[Literal],
) -> bool:
    """Check that all other literals (except the conclusion) are resolved.

    For a clause A ∨ B ∨ ¬C ∨ ¬D, to conclude A we need ¬B ∧ C ∧ D.
    - Negative literal ¬C: its positive counterpart C must be in known.
    - Positive literal B: its negation ¬B must be in known.
    """
    return _collect_premises(clause_lits, conclusion_idx, sub, known) is not None


def _is_tautological(lit: Literal) -> bool:
    """Return True if *lit* is a logical tautology of System E.

    Recognised tautologies (no proof step required):
      • ¬between(x,y,z) when any two of x,y,z are the same concrete
        name — follows from Betweenness axioms B1b/B1c and symmetry
        (between with duplicate arguments implies a≠a).
      • x = x  (reflexivity of equality for any sort).
    """
    atom = lit.atom
    if isinstance(atom, Between) and not lit.polarity:
        a, b, c = atom.a, atom.b, atom.c
        if a == b or a == c or b == c:
            return True
    if isinstance(atom, Equals) and lit.polarity:
        if atom.left == atom.right:
            return True
    return False


def _collect_premises(
    clause_lits: list,
    conclusion_idx: int,
    sub: Dict[str, str],
    known: Set[Literal],
) -> Optional[Set[Literal]]:
    """Collect the required premises if all are satisfied.

    Returns the set of instantiated premise literals (the negations of
    the non-conclusion clause literals) that must be in known, or None
    if any premise is not satisfied.

    Premises that are logical tautologies of the formal system (e.g.
    ¬between(x,y,x) from Betweenness 1c) are automatically satisfied
    and excluded from the returned set — they do not need to appear in
    any dependency line.
    """
    premises: Set[Literal] = set()
    for j, lit in enumerate(clause_lits):
        if j == conclusion_idx:
            continue
        glit = substitute_literal(lit, sub)
        neg = glit.negated()
        if _is_tautological(neg):
            continue
        if neg not in known:
            return None
        premises.add(neg)
    return premises


def _unify_literal_all(
    schema_lit: Literal,
    concrete_lit: Literal,
) -> List[Dict[str, str]]:
    """Try to unify a schema literal with a concrete literal.

    Returns a list of substitution dicts (possibly empty) mapping schema
    var names to concrete names.  For symmetric atoms (Equals, SameSide,
    Intersects) both orderings are returned when valid.
    """
    if schema_lit.polarity != concrete_lit.polarity:
        return []

    return _unify_atom_all(schema_lit.atom, concrete_lit.atom)


def _unify_literal(
    schema_lit: Literal,
    concrete_lit: Literal,
) -> Optional[Dict[str, str]]:
    """Try to unify a schema literal with a concrete literal.

    Returns a substitution dict mapping schema var names to concrete
    names, or None if unification fails.
    """
    results = _unify_literal_all(schema_lit, concrete_lit)
    return results[0] if results else None


def _unify_atom_all(
    schema: Atom,
    concrete: Atom,
) -> List[Dict[str, str]]:
    """Unify a schema atom with a concrete atom, returning all valid subs.

    For symmetric atoms (Equals, SameSide, Intersects), both argument
    orderings are tried and all successful substitutions are returned.
    """
    if type(schema) != type(concrete):
        return []

    if isinstance(schema, On):
        sub: Dict[str, str] = {}
        if not _bind(schema.point, concrete.point, sub):
            return []
        if not _bind(schema.obj, concrete.obj, sub):
            return []
        return [sub]

    if isinstance(schema, SameSide):
        # SameSide is symmetric in its point arguments
        results = []
        for ca, cb in [(concrete.a, concrete.b), (concrete.b, concrete.a)]:
            sub = {}
            if (_bind(schema.line, concrete.line, sub) and
                    _bind(schema.a, ca, sub) and
                    _bind(schema.b, cb, sub)):
                results.append(sub)
        return results

    if isinstance(schema, Between):
        sub = {}
        if not _bind(schema.a, concrete.a, sub):
            return []
        if not _bind(schema.b, concrete.b, sub):
            return []
        if not _bind(schema.c, concrete.c, sub):
            return []
        return [sub]

    if isinstance(schema, Center):
        sub = {}
        if not _bind(schema.point, concrete.point, sub):
            return []
        if not _bind(schema.circle, concrete.circle, sub):
            return []
        return [sub]

    if isinstance(schema, Inside):
        sub = {}
        if not _bind(schema.point, concrete.point, sub):
            return []
        if not _bind(schema.circle, concrete.circle, sub):
            return []
        return [sub]

    if isinstance(schema, Intersects):
        # Intersects is symmetric
        results = []
        for co1, co2 in [(concrete.obj1, concrete.obj2),
                         (concrete.obj2, concrete.obj1)]:
            sub = {}
            if _bind(schema.obj1, co1, sub) and _bind(schema.obj2, co2, sub):
                results.append(sub)
        return results

    if isinstance(schema, Equals):
        # Equals is symmetric: try both orderings
        results = []
        for cl, cr in [(concrete.left, concrete.right),
                       (concrete.right, concrete.left)]:
            sub = {}
            if _bind_term(schema.left, cl, sub) and _bind_term(schema.right, cr, sub):
                results.append(sub)
        return results

    if isinstance(schema, LessThan):
        sub = {}
        if not _bind_term(schema.left, concrete.left, sub):
            return []
        if not _bind_term(schema.right, concrete.right, sub):
            return []
        return [sub]

    return []


def _bind(schema_var: str, concrete_val: str, sub: Dict[str, str]) -> bool:
    """Bind a schema variable to a concrete value, checking consistency."""
    if schema_var in sub:
        return sub[schema_var] == concrete_val
    sub[schema_var] = concrete_val
    return True


def _bind_term(schema_t, concrete_t, sub: Dict[str, str]) -> bool:
    """Bind terms, handling magnitude expressions."""
    if isinstance(schema_t, str) and isinstance(concrete_t, str):
        return _bind(schema_t, concrete_t, sub)

    if type(schema_t) != type(concrete_t):
        return False

    if isinstance(schema_t, SegmentTerm):
        # SegmentTerm is symmetric (ab = ba), try both orderings
        if (_bind(schema_t.p1, concrete_t.p1, dict(sub)) and
                _bind(schema_t.p2, concrete_t.p2, dict(sub))):
            _bind(schema_t.p1, concrete_t.p1, sub)
            _bind(schema_t.p2, concrete_t.p2, sub)
            return True
        if (_bind(schema_t.p1, concrete_t.p2, dict(sub)) and
                _bind(schema_t.p2, concrete_t.p1, dict(sub))):
            _bind(schema_t.p1, concrete_t.p2, sub)
            _bind(schema_t.p2, concrete_t.p1, sub)
            return True
        return False

    if isinstance(schema_t, AngleTerm):
        if not _bind(schema_t.p1, concrete_t.p1, sub):
            return False
        if not _bind(schema_t.p2, concrete_t.p2, sub):
            return False
        if not _bind(schema_t.p3, concrete_t.p3, sub):
            return False
        return True

    if isinstance(schema_t, AreaTerm):
        if not _bind(schema_t.p1, concrete_t.p1, sub):
            return False
        if not _bind(schema_t.p2, concrete_t.p2, sub):
            return False
        if not _bind(schema_t.p3, concrete_t.p3, sub):
            return False
        return True

    if isinstance(schema_t, MagAdd):
        if not _bind_term(schema_t.left, concrete_t.left, sub):
            return False
        if not _bind_term(schema_t.right, concrete_t.right, sub):
            return False
        return True

    if isinstance(schema_t, (RightAngle, ZeroMag)):
        return type(schema_t) == type(concrete_t)

    return False
