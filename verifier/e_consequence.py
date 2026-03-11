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

        # Build ground instances of all clauses
        ground_clauses = self._ground_clauses(self.axioms, variables)

        # Forward-chaining closure
        closure = set(known)
        changed = True

        while changed:
            changed = False

            # Check for contradiction
            if self._has_contradiction(closure):
                return closure  # Everything follows from contradiction

            for clause in ground_clauses:
                result = self._apply_clause(clause, closure)
                if result is not None and result not in closure:
                    closure.add(result)
                    changed = True

        return closure

    def is_consequence(
        self,
        known: Set[Literal],
        query: Literal,
        variables: Optional[Dict[str, Sort]] = None,
    ) -> bool:
        """Check if a literal is a direct consequence of the known literals.

        This is the key query: "can we read off `query` from the diagram?"
        """
        closure = self.direct_consequences(known, variables)
        return query in closure

    # ── Internal methods ──────────────────────────────────────────────

    def _apply_clause(
        self, clause: Clause, known: Set[Literal]
    ) -> Optional[Literal]:
        """Try to derive a new literal from a clause and known literals.

        For clause {φ₁, …, φₙ}: if all but one literal have their
        negations in `known`, return the remaining literal.

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

        # All literals have their negations known — contradiction!
        # This shouldn't happen in a consistent state
        return None

    # Maximum number of ground clauses produced per axiom before the
    # axiom is skipped.  Prevents combinatorial explosion when the
    # variable set is large (e.g. 9+ points with 5-point axioms).
    _MAX_GROUND_PER_AXIOM = 50_000

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

            # Generate all substitutions
            for sub in self._all_substitutions(schema_vars, points, lines,
                                                circles):
                new_lits = frozenset(
                    substitute_literal(lit, sub)
                    for lit in axiom.literals)
                ground.append(Clause(new_lits))

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
