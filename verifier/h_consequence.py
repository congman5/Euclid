"""
h_consequence.py — Direct consequence engine for System H.

Implements the same polynomial-time forward-chaining algorithm as
e_consequence.py (Avigad et al. 2009, Proposition 3.2), adapted
for Hilbert's axiom clauses.

Given a set Δ of known HLiterals and a set S of HClauses (axioms),
the *direct consequences* of Δ under S are computed by:
  1. Start with Δ' = Δ
  2. For each clause {φ₁, …, φₙ} in S (under all variable substitutions),
     if ¬φ₁, …, ¬φₙ₋₁ are all in Δ', add φₙ to Δ'
  3. Repeat until fixpoint or contradiction

GeoCoq reference: the axiom clauses come from h_axioms.py, which
encodes GeoCoq's Hilbert_neutral_dimensionless class.
"""
from __future__ import annotations

from itertools import product
from typing import Dict, FrozenSet, List, Optional, Set, Tuple

from .h_ast import (
    HSort, HLiteral, HClause, HAtom,
    IncidL, IncidP, BetH, CongH, CongaH, EqL, EqP, EqPt,
    ColH, Cut, OutH, Disjoint, SameSideH, SameSidePrime, Para, IncidLP,
    h_atom_vars, h_literal_vars, h_substitute_literal,
)
from .h_axioms import ALL_H_AXIOMS


class HConsequenceEngine:
    """Computes direct consequences of a set of System H literals.

    Uses the contrapositive forward-chaining closure from Section 3.8
    of Avigad et al. (2009), applied to Hilbert's axiom clauses.
    """

    def __init__(self, axioms: Optional[List[HClause]] = None):
        self.axioms = axioms if axioms is not None else ALL_H_AXIOMS

    def direct_consequences(
        self,
        known: Set[HLiteral],
        variables: Optional[Dict[str, HSort]] = None,
    ) -> Set[HLiteral]:
        """Compute the direct consequences of known literals.

        Returns the closure Δ' including originals.
        """
        if variables is None:
            variables = self._extract_variables(known)

        ground_clauses = self._ground_clauses(self.axioms, variables)

        closure = set(known)
        changed = True

        while changed:
            changed = False

            if self._has_contradiction(closure):
                return closure

            for clause in ground_clauses:
                result = self._apply_clause(clause, closure)
                if result is not None and result not in closure:
                    closure.add(result)
                    changed = True

        return closure

    def is_consequence(
        self,
        known: Set[HLiteral],
        query: HLiteral,
        variables: Optional[Dict[str, HSort]] = None,
    ) -> bool:
        """Check if a literal is a direct consequence of the known literals."""
        closure = self.direct_consequences(known, variables)
        return query in closure

    # ── Internal methods ──────────────────────────────────────────────

    def _apply_clause(
        self, clause: HClause, known: Set[HLiteral]
    ) -> Optional[HLiteral]:
        """Unit propagation: if all but one disjunct's negation is known,
        derive the remaining disjunct."""
        literals = list(clause.literals)
        unknown_idx = None

        for i, lit in enumerate(literals):
            neg = lit.negated()
            if neg in known:
                continue
            elif lit in known:
                return None
            else:
                if unknown_idx is not None:
                    return None
                unknown_idx = i

        if unknown_idx is not None:
            return literals[unknown_idx]
        return None

    def _ground_clauses(
        self,
        axioms: List[HClause],
        variables: Dict[str, HSort],
    ) -> List[HClause]:
        """Generate ground instances of axiom schemas."""
        points = [v for v, s in variables.items() if s == HSort.POINT]
        lines = [v for v, s in variables.items() if s == HSort.LINE]
        planes = [v for v, s in variables.items() if s == HSort.PLANE]

        ground: List[HClause] = []
        for axiom in axioms:
            schema_vars = self._clause_schema_vars(axiom)
            if not schema_vars:
                ground.append(axiom)
                continue

            for sub in self._all_substitutions(schema_vars, points, lines,
                                                planes):
                new_lits = frozenset(
                    h_substitute_literal(lit, sub)
                    for lit in axiom.literals)
                ground.append(HClause(new_lits))

        return ground

    def _clause_schema_vars(self, clause: HClause) -> List[Tuple[str, HSort]]:
        """Extract schema variable names and their inferred sorts."""
        vars_seen: Dict[str, HSort] = {}
        for lit in clause.literals:
            self._collect_atom_var_sorts(lit.atom, vars_seen)
        return list(vars_seen.items())

    def _collect_atom_var_sorts(
        self, atom: HAtom, out: Dict[str, HSort]
    ) -> None:
        """Infer the sort of each variable from its position in the atom."""
        if isinstance(atom, IncidL):
            out.setdefault(atom.point, HSort.POINT)
            out.setdefault(atom.line, HSort.LINE)
        elif isinstance(atom, IncidP):
            out.setdefault(atom.point, HSort.POINT)
            out.setdefault(atom.plane, HSort.PLANE)
        elif isinstance(atom, BetH):
            out.setdefault(atom.a, HSort.POINT)
            out.setdefault(atom.b, HSort.POINT)
            out.setdefault(atom.c, HSort.POINT)
        elif isinstance(atom, CongH):
            out.setdefault(atom.a, HSort.POINT)
            out.setdefault(atom.b, HSort.POINT)
            out.setdefault(atom.c, HSort.POINT)
            out.setdefault(atom.d, HSort.POINT)
        elif isinstance(atom, CongaH):
            out.setdefault(atom.a, HSort.POINT)
            out.setdefault(atom.b, HSort.POINT)
            out.setdefault(atom.c, HSort.POINT)
            out.setdefault(atom.d, HSort.POINT)
            out.setdefault(atom.e, HSort.POINT)
            out.setdefault(atom.f, HSort.POINT)
        elif isinstance(atom, EqL):
            out.setdefault(atom.left, HSort.LINE)
            out.setdefault(atom.right, HSort.LINE)
        elif isinstance(atom, EqP):
            out.setdefault(atom.left, HSort.PLANE)
            out.setdefault(atom.right, HSort.PLANE)
        elif isinstance(atom, EqPt):
            out.setdefault(atom.left, HSort.POINT)
            out.setdefault(atom.right, HSort.POINT)
        elif isinstance(atom, ColH):
            out.setdefault(atom.a, HSort.POINT)
            out.setdefault(atom.b, HSort.POINT)
            out.setdefault(atom.c, HSort.POINT)
        elif isinstance(atom, Cut):
            out.setdefault(atom.line, HSort.LINE)
            out.setdefault(atom.a, HSort.POINT)
            out.setdefault(atom.b, HSort.POINT)
        elif isinstance(atom, OutH):
            out.setdefault(atom.p, HSort.POINT)
            out.setdefault(atom.a, HSort.POINT)
            out.setdefault(atom.b, HSort.POINT)
        elif isinstance(atom, Disjoint):
            out.setdefault(atom.a, HSort.POINT)
            out.setdefault(atom.b, HSort.POINT)
            out.setdefault(atom.c, HSort.POINT)
            out.setdefault(atom.d, HSort.POINT)
        elif isinstance(atom, SameSideH):
            out.setdefault(atom.a, HSort.POINT)
            out.setdefault(atom.b, HSort.POINT)
            out.setdefault(atom.line, HSort.LINE)
        elif isinstance(atom, SameSidePrime):
            out.setdefault(atom.a, HSort.POINT)
            out.setdefault(atom.b, HSort.POINT)
            out.setdefault(atom.x, HSort.POINT)
            out.setdefault(atom.y, HSort.POINT)
        elif isinstance(atom, Para):
            out.setdefault(atom.line1, HSort.LINE)
            out.setdefault(atom.line2, HSort.LINE)
        elif isinstance(atom, IncidLP):
            out.setdefault(atom.line, HSort.LINE)
            out.setdefault(atom.plane, HSort.PLANE)

    def _all_substitutions(
        self,
        schema_vars: List[Tuple[str, HSort]],
        points: List[str],
        lines: List[str],
        planes: List[str],
    ):
        """Generate all substitutions mapping schema vars to actual vars."""
        pools = []
        for name, sort in schema_vars:
            if sort == HSort.POINT:
                pools.append(points)
            elif sort == HSort.LINE:
                pools.append(lines)
            elif sort == HSort.PLANE:
                pools.append(planes)
            else:
                pools.append([])

        if any(len(p) == 0 for p in pools):
            return

        names = [name for name, _ in schema_vars]
        for combo in product(*pools):
            yield dict(zip(names, combo))

    def _extract_variables(self, known: Set[HLiteral]) -> Dict[str, HSort]:
        """Extract variable names and infer sorts from known literals."""
        vars_: Dict[str, HSort] = {}
        for lit in known:
            self._collect_atom_var_sorts(lit.atom, vars_)
        return vars_

    def _has_contradiction(self, known: Set[HLiteral]) -> bool:
        """Check if known contains both φ and ¬φ."""
        for lit in known:
            if lit.negated() in known:
                return True
        return False


# ═══════════════════════════════════════════════════════════════════════
# Convenience
# ═══════════════════════════════════════════════════════════════════════

_default_engine: Optional[HConsequenceEngine] = None


def get_h_consequence_engine() -> HConsequenceEngine:
    """Get the default consequence engine with all Hilbert axioms."""
    global _default_engine
    if _default_engine is None:
        _default_engine = HConsequenceEngine()
    return _default_engine


def is_h_consequence(known: Set[HLiteral], query: HLiteral) -> bool:
    """Check if a literal is a direct consequence under Hilbert axioms."""
    return get_h_consequence_engine().is_consequence(known, query)
