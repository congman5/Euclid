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
        self._ground_cache_key = None
        self._ground_cache = None
        self._compiled_cache_key = None
        self._compiled_cache = None
        self._sat_index = None
        self._res_index = None

    def apply_transfers(
        self,
        diagram_known: Set[Literal],
        metric_known: Set[Literal],
        variables: Optional[Dict[str, Sort]] = None,
    ) -> Set[Literal]:
        """Apply transfer axioms to derive new facts.

        Uses indexed unit propagation for efficiency.
        """
        if variables is None:
            variables = self._extract_variables(diagram_known | metric_known)
        else:
            # Filter to variables actually appearing in the known facts.
            # This avoids grounding axioms over variables introduced by
            # later proof steps, which can explode combinatorially.
            used_names: set = set()
            for lit in diagram_known:
                used_names.update(atom_vars(lit.atom))
            for lit in metric_known:
                used_names.update(atom_vars(lit.atom))
            if len(used_names) < len(variables):
                variables = {k: v for k, v in variables.items()
                             if k in used_names}

        all_known = diagram_known | metric_known
        derived: Set[Literal] = set()

        # Seed degenerate between negations: between(x,y,x) is always
        # false because betweenness requires 3 distinct points (B1b/c
        # give between(a,b,c) → a≠b, a≠c).  When x=z, between(x,y,x)
        # would require x≠x — contradiction.  Explicitly adding these
        # lets transfer axioms like DA4 fire when template variables
        # map to the same concrete point.
        points = [v for v, s in variables.items() if s == Sort.POINT]
        for p in points:
            for q in points:
                neg_bet = Literal(Between(p, q, p), False)
                if neg_bet not in all_known:
                    all_known.add(neg_bet)
                neg_bet2 = Literal(Between(q, p, p), False)
                if neg_bet2 not in all_known:
                    all_known.add(neg_bet2)
                neg_bet3 = Literal(Between(p, p, q), False)
                if neg_bet3 not in all_known:
                    all_known.add(neg_bet3)

        # Ground the transfer axiom clauses — use pre-compiled format
        # with cached separate indices for fast lookup.
        compiled = self._compiled_clauses(self.axioms, variables)
        sat_index = self._sat_index
        res_index = self._res_index

        satisfied = bytearray(len(compiled))

        # Seed worklist and mark initially satisfied clauses
        worklist = list(all_known)
        for fact in all_known:
            for ci in sat_index.get(fact, ()):
                satisfied[ci] = 1

        while worklist:
            fact = worklist.pop()

            for ci in res_index.get(fact, ()):
                if satisfied[ci]:
                    continue
                result = ConsequenceEngine._apply_compiled(
                    compiled[ci], all_known)
                if (result is not None
                        and result is not ConsequenceEngine._CLAUSE_CONTRADICTION
                        and result not in all_known):
                    all_known.add(result)
                    derived.add(result)
                    worklist.append(result)
                    for sci in sat_index.get(result, ()):
                        satisfied[sci] = 1

        return derived

    def _compiled_clauses(self, axioms, variables):
        """Return pre-compiled clause data with negated literals and index."""
        from typing import FrozenSet
        cache_key: FrozenSet = frozenset(variables.items())
        if (cache_key == self._compiled_cache_key
                and self._compiled_cache is not None):
            return self._compiled_cache
        ground = self._ground_clauses(axioms, variables)
        compiled = []
        sat_index = {}
        res_index = {}
        for i, clause_lits in enumerate(ground):
            pairs = tuple(
                (lit, lit.negated()) for lit in clause_lits
            )
            compiled.append(pairs)
            for lit, neg in pairs:
                sat_index.setdefault(lit, []).append(i)
                res_index.setdefault(neg, []).append(i)
        self._compiled_cache_key = cache_key
        self._compiled_cache = compiled
        self._sat_index = sat_index
        self._res_index = res_index
        return compiled

    def _ground_clauses(self, axioms, variables):
        """Delegate to ConsequenceEngine's grounding logic, with caching."""
        from typing import FrozenSet
        cache_key: FrozenSet = frozenset(variables.items())
        if cache_key == self._ground_cache_key and self._ground_cache is not None:
            return self._ground_cache
        engine = ConsequenceEngine(axioms=[])
        result = engine._ground_clauses(axioms, variables)
        self._ground_cache_key = cache_key
        self._ground_cache = result
        return result

    def _extract_variables(self, known: Set[Literal]) -> Dict[str, Sort]:
        engine = ConsequenceEngine(axioms=[])
        return engine._extract_variables(known)
