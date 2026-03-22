"""
e_consequence.py — Direct consequence engine for System E (Section 3.8).

Implements the polynomial-time forward-chaining algorithm from
Proposition 3.2 of Avigad, Dean, Mumma (2009).

Given a set Δ of known literals and a set S of clauses (axioms),
the *direct consequences* of Δ under S are computed by:

  1. Start with Δ' = Δ
  2. For each clause {φ₁, …, φₙ} in S (under all variable substitutions
     involving the known variables), if ¬φ₁, …, ¬φₙ₋₁ are all in Δ',
     add φₙ to Δ'
  3. Repeat until fixpoint (no new literals added) or contradiction

This uses ALL contrapositive variants of each clause: for a clause
{φ₁, …, φₙ}, if all but one literal have their negations in Δ',
the remaining literal is added to Δ'.

Theorem 3.6 guarantees this runs in polynomial time in the number
of points, lines, and circles.
"""
from __future__ import annotations

from itertools import product
from typing import Dict, FrozenSet, List, Optional, Set, Tuple

from .e_ast import (
    Sort, Literal, Clause,
    Atom, On, SameSide, Between, Center, Inside, Intersects, Equals,
    LessThan,
    atom_vars, literal_vars, substitute_literal,
)
from .e_axioms import ALL_DIAGRAMMATIC_AXIOMS


# ═══════════════════════════════════════════════════════════════════════
# Core consequence engine
# ═══════════════════════════════════════════════════════════════════════

class ConsequenceEngine:
    """Computes direct consequences of a set of diagrammatic literals.

    Implements the closure algorithm from Section 3.8 / Proposition 3.2.
    """

    def __init__(self, axioms: Optional[List[Clause]] = None):
        """Initialize with a set of axiom clauses.

        If not provided, uses all diagrammatic axioms from Section 3.4.
        """
        self.axioms = axioms if axioms is not None else ALL_DIAGRAMMATIC_AXIOMS
        # Cache ground clauses keyed on frozenset(variables.items()) to
        # avoid regenerating them when the variable set hasn't changed.
        self._ground_cache_key: Optional[FrozenSet] = None
        self._ground_cache: Optional[List[Clause]] = None
        self._compiled_cache_key: Optional[FrozenSet] = None
        self._compiled_cache: Optional[List[Tuple]] = None
        # sat_index[L] = clause indices containing literal L (for marking satisfied)
        self._sat_index: Optional[Dict] = None
        # res_index[f] = clause indices where f resolves a literal
        #   (i.e., clause contains literal L with L.negated() == f)
        self._res_index: Optional[Dict] = None

    def direct_consequences(
        self,
        known: Set[Literal],
        variables: Optional[Dict[str, Sort]] = None,
    ) -> Set[Literal]:
        """Compute the direct consequences of a set of known literals.

        Args:
            known: The initial set Δ of known literals
            variables: Mapping from variable names to sorts (for grounding)

        Returns:
            The closure Δ' — all direct consequences including the originals.
            If a contradiction is found (both φ and ¬φ), returns all possible
            literals as a sentinel.
        """
        if variables is None:
            variables = self._extract_variables(known)

        # Build ground instances — uses pre-compiled format with negated
        # literals pre-computed and separate indices for fast lookup.
        compiled = self._compiled_clauses(self.axioms, variables)
        sat_index = self._sat_index
        res_index = self._res_index

        closure = set(known)
        satisfied = bytearray(len(compiled))

        # Seed worklist and mark initially satisfied clauses
        worklist = list(known)
        for fact in known:
            for ci in sat_index.get(fact, ()):
                satisfied[ci] = 1

        while worklist:
            fact = worklist.pop()

            # Check for contradiction
            if fact.negated() in closure:
                from .e_ast import BOTTOM
                closure.add(BOTTOM)
                closure.add(BOTTOM.negated())
                return closure

            # Check clauses where knowing `fact` resolves a literal
            for ci in res_index.get(fact, ()):
                if satisfied[ci]:
                    continue
                result = self._apply_compiled(compiled[ci], closure)
                if result is self._CLAUSE_CONTRADICTION:
                    from .e_ast import BOTTOM
                    closure.add(BOTTOM)
                    closure.add(BOTTOM.negated())
                    return closure
                if result is not None and result not in closure:
                    closure.add(result)
                    worklist.append(result)
                    # Mark clauses satisfied by this new literal
                    for sci in sat_index.get(result, ()):
                        satisfied[sci] = 1

        return closure

    def is_consequence(
        self,
        known: Set[Literal],
        query: Literal,
        variables: Optional[Dict[str, Sort]] = None,
    ) -> bool:
        """Check if a literal is a direct consequence of the known literals.

        This is the key query: "can we read off `query` from the diagram?"
        If the known set is inconsistent (contains a contradiction),
        every literal follows — return True.
        """
        closure = self.direct_consequences(known, variables)
        if self._has_contradiction(closure):
            return True
        return query in closure

    # ── Internal methods ──────────────────────────────────────────────

    # Sentinel returned by _apply_clause when every disjunct in a
    # ground clause is negated by the known set — i.e. the clause is
    # violated, indicating the known set is inconsistent.
    _CLAUSE_CONTRADICTION = object()

    def _apply_clause(
        self, clause: Clause, known: Set[Literal]
    ) -> Optional[Literal]:
        """Try to derive a new literal from a clause and known literals.

        For clause {φ₁, …, φₙ}: if all but one literal have their
        negations in `known`, return the remaining literal.

        Returns ``_CLAUSE_CONTRADICTION`` if every disjunct is negated
        (the clause is violated — the known set is inconsistent).
        Returns None if no new literal can be derived.
        """
        literals = list(clause.literals)
        unknown_idx = None

        for i, lit in enumerate(literals):
            neg = lit.negated()
            if neg in known:
                # This literal's negation is known, so this disjunct fails
                continue
            elif lit in known:
                # This literal is already known — clause is already satisfied
                return None
            else:
                # This literal is neither known nor its negation is known
                if unknown_idx is not None:
                    # More than one unknown — can't derive anything
                    return None
                unknown_idx = i

        if unknown_idx is not None:
            return literals[unknown_idx]

        # All literals have their negations known — clause is violated!
        return self._CLAUSE_CONTRADICTION

    def _compiled_clauses(
        self,
        axioms: List[Clause],
        variables: Dict[str, Sort],
    ) -> List[Tuple]:
        """Return pre-compiled clause data with negated literals pre-computed.

        Each compiled clause is a tuple of (literal, negated_literal) pairs.
        Also builds a literal → clause indices index for fast lookup.
        Both are cached.
        """
        cache_key = frozenset(variables.items())
        if (cache_key == self._compiled_cache_key
                and self._compiled_cache is not None):
            return self._compiled_cache

        ground_clauses = self._ground_clauses(axioms, variables)
        compiled = []
        sat_index: Dict[Literal, List[int]] = {}
        res_index: Dict[Literal, List[int]] = {}
        for i, clause in enumerate(ground_clauses):
            pairs = tuple(
                (lit, lit.negated()) for lit in clause.literals
            )
            compiled.append(pairs)
            for lit, neg in pairs:
                # sat_index[lit] → clause is satisfied when lit is known
                if lit not in sat_index:
                    sat_index[lit] = []
                sat_index[lit].append(i)
                # res_index[neg] → when neg is known, lit is resolved
                # (because neg = lit.negated(), so knowing neg eliminates lit)
                if neg not in res_index:
                    res_index[neg] = []
                res_index[neg].append(i)
        self._compiled_cache_key = cache_key
        self._compiled_cache = compiled
        self._sat_index = sat_index
        self._res_index = res_index
        return compiled

    @staticmethod
    def _apply_compiled(clause_pairs: Tuple, known: Set[Literal]):
        """Unit propagation using pre-compiled (literal, negated) pairs.

        Returns the derivable literal, _CLAUSE_CONTRADICTION, or None.
        """
        unknown_lit = None
        for lit, neg in clause_pairs:
            if neg in known:
                continue
            elif lit in known:
                return None
            else:
                if unknown_lit is not None:
                    return None
                unknown_lit = lit
        if unknown_lit is not None:
            return unknown_lit
        return ConsequenceEngine._CLAUSE_CONTRADICTION

    # Maximum number of ground clauses produced per axiom before the
    # axiom is skipped.  Prevents combinatorial explosion when the
    # variable set is large (e.g. 9+ points with 5-point axioms).
    _MAX_GROUND_PER_AXIOM = 200_000

    def _ground_clauses(
        self,
        axioms: List[Clause],
        variables: Dict[str, Sort],
    ) -> List[Clause]:
        """Generate ground instances of axiom schemas.

        Each axiom clause contains schema variables (a, b, c, L, M, α, etc.)
        We instantiate them with all combinations of actual variable names
        of matching sorts.

        Axioms whose variable-sort combination would exceed
        ``_MAX_GROUND_PER_AXIOM`` ground instances are skipped to
        prevent combinatorial explosion.
        """
        # Check cache — keyed on the variable set (names + sorts)
        cache_key = frozenset(variables.items())
        if cache_key == self._ground_cache_key and self._ground_cache is not None:
            return self._ground_cache

        points = [v for v, s in variables.items() if s == Sort.POINT]
        lines = [v for v, s in variables.items() if s == Sort.LINE]
        circles = [v for v, s in variables.items() if s == Sort.CIRCLE]

        ground: List[Clause] = []
        for axiom in axioms:
            # Collect schema variables and their sorts
            schema_vars = self._clause_schema_vars(axiom)
            if not schema_vars:
                ground.append(axiom)
                continue

            # Estimate combination count and skip if too large
            est = 1
            for _, sort in schema_vars:
                if sort == Sort.POINT:
                    est *= len(points)
                elif sort == Sort.LINE:
                    est *= len(lines)
                elif sort == Sort.CIRCLE:
                    est *= len(circles)
            if est > self._MAX_GROUND_PER_AXIOM:
                continue

            # Extract equality constraints: pairs of schema variable names
            # that appear in _pos(Equals(x, y)) literals.  When both map
            # to the same concrete name, the clause is trivially satisfied
            # (x = x is always true), so we skip those substitutions.
            eq_pairs = set()
            for lit in axiom.literals:
                if (lit.polarity and isinstance(lit.atom, Equals)
                        and isinstance(lit.atom.left, str)
                        and isinstance(lit.atom.right, str)
                        and lit.atom.left != lit.atom.right):
                    eq_pairs.add((lit.atom.left, lit.atom.right))

            # Similarly for _neg(Between(a,b,c)): between(a,b,c) is
            # trivially false when any two of a,b,c are equal (B1b/c),
            # making ¬between(a,b,c) trivially true → clause satisfied.
            for lit in axiom.literals:
                if (not lit.polarity and isinstance(lit.atom, Between)):
                    a, b, c = lit.atom.a, lit.atom.b, lit.atom.c
                    # between(a,b,a) is always false, etc.
                    # But this is handled by degenerate between seeding;
                    # skip for now to avoid over-filtering.

            # Generate all substitutions, skipping trivially satisfied
            var_names = [name for name, _ in schema_vars]
            for sub in self._all_substitutions(schema_vars, points, lines,
                                                circles):
                # Skip if any equality pair maps to the same value
                skip = False
                for v1, v2 in eq_pairs:
                    if sub.get(v1) == sub.get(v2):
                        skip = True
                        break
                if skip:
                    continue
                new_lits = frozenset(
                    substitute_literal(lit, sub)
                    for lit in axiom.literals)
                ground.append(Clause(new_lits))

        self._ground_cache_key = cache_key
        self._ground_cache = ground
        return ground

    def _clause_schema_vars(self, clause: Clause) -> List[Tuple[str, Sort]]:
        """Extract schema variable names and their inferred sorts."""
        vars_seen: Dict[str, Sort] = {}
        for lit in clause.literals:
            self._collect_atom_var_sorts(lit.atom, vars_seen)
        return list(vars_seen.items())

    def _collect_atom_var_sorts(
        self, atom: Atom, out: Dict[str, Sort]
    ) -> None:
        """Infer the sort of each variable in an atom from its position."""
        if isinstance(atom, On):
            out.setdefault(atom.point, Sort.POINT)
            # obj could be line or circle — infer from naming convention
            # If a name is unrecognised, default to LINE (not POINT) since
            # On(p, obj) requires obj to be a line or circle.
            if atom.obj not in out:
                inferred = self._infer_sort_from_name(atom.obj)
                if inferred == Sort.POINT:
                    inferred = Sort.LINE
                out[atom.obj] = inferred
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
            # Center definitively identifies its second arg as a circle
            out[atom.circle] = Sort.CIRCLE
        elif isinstance(atom, Inside):
            out.setdefault(atom.point, Sort.POINT)
            # Inside definitively identifies its second arg as a circle
            out[atom.circle] = Sort.CIRCLE
        elif isinstance(atom, Intersects):
            if atom.obj1 not in out:
                out[atom.obj1] = self._infer_sort_from_name(atom.obj1)
            if atom.obj2 not in out:
                out[atom.obj2] = self._infer_sort_from_name(atom.obj2)
        elif isinstance(atom, Equals):
            # Both sides should be same sort
            if isinstance(atom.left, str) and isinstance(atom.right, str):
                if atom.left not in out and atom.right not in out:
                    # Default to point
                    out.setdefault(atom.left, Sort.POINT)
                    out.setdefault(atom.right, Sort.POINT)
                elif atom.left in out:
                    out.setdefault(atom.right, out[atom.left])
                elif atom.right in out:
                    out.setdefault(atom.left, out[atom.right])
            # Magnitude terms are handled by the metric engine, skip here

    def _infer_sort_from_name(self, name: str) -> Sort:
        """Infer sort from naming convention in axiom schemas."""
        if name in ("L", "M", "N"):
            return Sort.LINE
        # Greek lowercase letters are circles by convention
        if any('\u03b1' <= ch <= '\u03c9' for ch in name):
            return Sort.CIRCLE
        # Default heuristic: single uppercase → could be line
        if len(name) == 1 and name.isupper() and name >= "L":
            return Sort.LINE
        return Sort.POINT

    def _all_substitutions(
        self,
        schema_vars: List[Tuple[str, Sort]],
        points: List[str],
        lines: List[str],
        circles: List[str],
    ):
        """Generate all substitutions mapping schema vars to actual vars."""
        pools = []
        for name, sort in schema_vars:
            if sort == Sort.POINT:
                pools.append(points)
            elif sort == Sort.LINE:
                pools.append(lines)
            elif sort == Sort.CIRCLE:
                pools.append(circles)
            else:
                pools.append([])

        if any(len(p) == 0 for p in pools):
            return

        names = [name for name, _ in schema_vars]
        for combo in product(*pools):
            yield dict(zip(names, combo))

    def _extract_variables(self, known: Set[Literal]) -> Dict[str, Sort]:
        """Extract variable names and infer their sorts from known literals.

        Uses a two-pass approach: first processes atoms that
        definitively establish sorts (On, Center, Inside, etc.), then
        processes Equals atoms that may need to inherit sorts from
        other atoms.
        """
        vars_: Dict[str, Sort] = {}
        # Pass 1: non-Equals atoms establish definitive sorts
        for lit in known:
            if not (isinstance(lit.atom, Equals)
                    and isinstance(getattr(lit.atom, 'left', None), str)):
                self._collect_atom_var_sorts(lit.atom, vars_)
        # Pass 2: Equals atoms inherit sorts
        for lit in known:
            if (isinstance(lit.atom, Equals)
                    and isinstance(getattr(lit.atom, 'left', None), str)):
                self._collect_atom_var_sorts(lit.atom, vars_)
        return vars_

    def _has_contradiction(self, known: Set[Literal]) -> bool:
        """Check if the known set contains both φ and ¬φ."""
        for lit in known:
            if lit.negated() in known:
                return True
        return False


# ═══════════════════════════════════════════════════════════════════════
# Convenience singleton
# ═══════════════════════════════════════════════════════════════════════

_default_engine: Optional[ConsequenceEngine] = None


def get_consequence_engine() -> ConsequenceEngine:
    """Get the default consequence engine with all diagrammatic axioms."""
    global _default_engine
    if _default_engine is None:
        _default_engine = ConsequenceEngine()
    return _default_engine


def is_diagrammatic_consequence(
    known: Set[Literal], query: Literal
) -> bool:
    """Check if a literal is a direct diagrammatic consequence."""
    return get_consequence_engine().is_consequence(known, query)
