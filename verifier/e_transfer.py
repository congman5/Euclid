"""
e_transfer.py — Transfer inference engine for System E (Section 3.6).

Transfer inferences connect diagrammatic and metric assertions:
  - Diagram → Metric:  e.g. between(a,b,c) → ab + bc = ac
  - Metric → Diagram:  e.g. center(a,α) ∧ on(b,α) ∧ ac=ab → on(c,α)

Transfer axioms are stored as clauses in e_axioms.py.
This engine applies them by combining the diagrammatic consequence
engine and the metric engine.
"""
from __future__ import annotations

from typing import Dict, Optional, Set

from .e_ast import (
    Sort, Literal, Clause,
    On, SameSide, Between, Center, Inside, Intersects, Equals, LessThan,
    SegmentTerm, AngleTerm, AreaTerm, MagAdd,
    atom_vars, substitute_literal,
)
from .e_axioms import ALL_TRANSFER_AXIOMS
from .e_consequence import ConsequenceEngine
from .e_metric import MetricEngine


class TransferEngine:
    """Applies transfer axioms between diagrammatic and metric domains.

    A transfer inference uses known diagrammatic facts to derive metric
    conclusions, or known metric facts to derive diagrammatic conclusions,
    or a combination of both.
    """

    def __init__(self, transfer_axioms: Optional[list] = None):
        self.axioms = (transfer_axioms if transfer_axioms is not None
                       else ALL_TRANSFER_AXIOMS)

    def apply_transfers(
        self,
        diagram_known: Set[Literal],
        metric_known: Set[Literal],
        variables: Optional[Dict[str, Sort]] = None,
    ) -> Set[Literal]:
        """Apply transfer axioms to derive new facts.

        Takes known diagrammatic and metric literals, returns newly derived
        literals from both domains.
        """
        if variables is None:
            variables = self._extract_variables(diagram_known | metric_known)

        all_known = diagram_known | metric_known
        derived: Set[Literal] = set()

        # Ground the transfer axiom clauses
        ground_clauses = self._ground_clauses(self.axioms, variables)

        changed = True
        while changed:
            changed = False
            for clause in ground_clauses:
                result = self._apply_clause(clause, all_known)
                if result is not None and result not in all_known:
                    all_known.add(result)
                    derived.add(result)
                    changed = True

        return derived

    def _apply_clause(
        self, clause: Clause, known: Set[Literal]
    ) -> Optional[Literal]:
        """Same unit-propagation logic as ConsequenceEngine."""
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

    def _ground_clauses(self, axioms, variables):
        """Delegate to ConsequenceEngine's grounding logic."""
        engine = ConsequenceEngine(axioms=[])
        return engine._ground_clauses(axioms, variables)

    def _extract_variables(self, known: Set[Literal]) -> Dict[str, Sort]:
        engine = ConsequenceEngine(axioms=[])
        return engine._extract_variables(known)
