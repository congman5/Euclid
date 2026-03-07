"""
t_consequence.py — Direct consequence engine for System T (Tarski).

Implements the polynomial-time forward-chaining algorithm from
Proposition 3.2 of Avigad et al. (2009), adapted for Tarski's
single-sorted axiom system.

Since Tarski's system uses only one sort (POINT), the grounding
step only needs a single pool of point names.

GeoCoq reference: theories/Axioms/tarski_axioms.v
"""
from __future__ import annotations

from itertools import product
from typing import Dict, List, Optional, Set, Tuple

from .t_ast import (
    TSort, TLiteral, TClause, TAtom,
    B, Cong, NotB, NotCong, Eq, Neq,
    t_atom_vars, t_literal_vars, t_substitute_literal,
)
from .t_axioms import DEDUCTION_AXIOMS


class TConsequenceEngine:
    """Computes direct consequences of a set of System T literals.

    Uses the contrapositive forward-chaining closure from Section 3.8
    of Avigad et al. (2009), applied to Tarski's axiom clauses.
    """

    def __init__(self, axioms: Optional[List[TClause]] = None):
        self.axioms = axioms if axioms is not None else DEDUCTION_AXIOMS

    def direct_consequences(
        self,
        known: Set[TLiteral],
        variables: Optional[Dict[str, TSort]] = None,
    ) -> Set[TLiteral]:
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
        known: Set[TLiteral],
        query: TLiteral,
        variables: Optional[Dict[str, TSort]] = None,
    ) -> bool:
        """Check if a literal is a direct consequence of the known literals."""
        closure = self.direct_consequences(known, variables)
        return query in closure

    # ── Internal methods ──────────────────────────────────────────────

    def _apply_clause(
        self, clause: TClause, known: Set[TLiteral]
    ) -> Optional[TLiteral]:
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
        axioms: List[TClause],
        variables: Dict[str, TSort],
    ) -> List[TClause]:
        """Generate ground instances of axiom schemas.

        Since Tarski's system is single-sorted (POINT only), all schema
        variables are grounded from the single POINT pool.
        """
        points = [v for v, s in variables.items() if s == TSort.POINT]

        ground: List[TClause] = []
        for axiom in axioms:
            schema_vars = self._clause_schema_vars(axiom)
            if not schema_vars:
                ground.append(axiom)
                continue

            names = [name for name, _ in schema_vars]
            for combo in product(points, repeat=len(names)):
                sub = dict(zip(names, combo))
                new_lits = frozenset(
                    t_substitute_literal(lit, sub)
                    for lit in axiom.literals)
                ground.append(TClause(new_lits))

        return ground

    def _clause_schema_vars(self, clause: TClause) -> List[Tuple[str, TSort]]:
        """Extract schema variable names and their sorts (all POINT)."""
        seen: Dict[str, TSort] = {}
        for lit in clause.literals:
            for v in t_atom_vars(lit.atom):
                seen.setdefault(v, TSort.POINT)
        return list(seen.items())

    def _extract_variables(self, known: Set[TLiteral]) -> Dict[str, TSort]:
        """Extract variable names from known literals (all POINT)."""
        vars_: Dict[str, TSort] = {}
        for lit in known:
            for v in t_atom_vars(lit.atom):
                vars_.setdefault(v, TSort.POINT)
        return vars_

    def _has_contradiction(self, known: Set[TLiteral]) -> bool:
        """Check if known contains both φ and ¬φ."""
        for lit in known:
            if lit.negated() in known:
                return True
        return False


# ═══════════════════════════════════════════════════════════════════════
# Convenience
# ═══════════════════════════════════════════════════════════════════════

_default_engine: Optional[TConsequenceEngine] = None


def get_t_consequence_engine() -> TConsequenceEngine:
    """Get the default consequence engine with all Tarski deduction axioms."""
    global _default_engine
    if _default_engine is None:
        _default_engine = TConsequenceEngine()
    return _default_engine


def is_t_consequence(known: Set[TLiteral], query: TLiteral) -> bool:
    """Check if a literal is a direct consequence under Tarski's axioms."""
    return get_t_consequence_engine().is_consequence(known, query)
