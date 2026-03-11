"""
t_consequence.py — Direct consequence engine for System T (Tarski).

Implements the polynomial-time forward-chaining algorithm from
Proposition 3.2 of Avigad et al. (2009), adapted for Tarski's
single-sorted axiom system.

Since Tarski's system uses only one sort (POINT), the grounding
step only needs a single pool of point names.

Uses matched unit-propagation: instead of enumerating all point^k
substitutions upfront (infeasible for axioms with 6–8 variables),
for each axiom clause we try every literal as the "free" one to
derive, matching the remaining literals' negations against known
facts.  Only substitutions that satisfy *all* prerequisites are
used, keeping the grounding proportional to the number of known
facts rather than point^k.

GeoCoq reference: theories/Axioms/tarski_axioms.v
"""
from __future__ import annotations

from itertools import product as iprod
from typing import Dict, List, Optional, Set, Tuple

from .t_ast import (
    TSort, TLiteral, TClause, TAtom,
    B, Cong, NotB, NotCong, Eq, Neq,
    t_atom_vars, t_literal_vars, t_substitute_literal,
)
from .t_axioms import DEDUCTION_AXIOMS


def _atom_args(atom: TAtom) -> Tuple[str, ...]:
    """Extract argument names from a T atom in order."""
    if isinstance(atom, (B, NotB)):
        return (atom.a, atom.b, atom.c)
    if isinstance(atom, (Cong, NotCong)):
        return (atom.a, atom.b, atom.c, atom.d)
    if isinstance(atom, (Eq, Neq)):
        return (atom.left, atom.right)
    return ()


def _lit_key(lit: TLiteral) -> Tuple[str, bool]:
    """Index key: (atom type name, polarity)."""
    return (type(lit.atom).__name__, lit.polarity)


class TConsequenceEngine:
    """Computes direct consequences of a set of System T literals.

    Uses the contrapositive forward-chaining closure from Section 3.8
    of Avigad et al. (2009), applied to Tarski's axiom clauses.

    Optimisation: matched unit-propagation.  For each clause
    {L₁, …, Lₙ} and each index i, we attempt to derive Lᵢ by
    checking that ¬Lⱼ ∈ known for all j≠i.  Substitutions are
    obtained by matching the ¬Lⱼ patterns against known facts,
    avoiding the combinatorial blowup of full Cartesian-product
    grounding.
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

        points = sorted(v for v, s in variables.items()
                        if s == TSort.POINT)

        # Pre-split each axiom into a list of literals + schema vars
        axiom_info: List[Tuple[List[TLiteral], List[str]]] = []
        for clause in self.axioms:
            lits = list(clause.literals)
            svars = sorted(self._clause_schema_vars_set(clause))
            axiom_info.append((lits, svars))

        closure = set(known)
        changed = True

        while changed:
            changed = False

            if self._has_contradiction(closure):
                return closure

            # Build an index of known facts by (type, polarity)
            idx = self._build_index(closure)

            for lits, svars in axiom_info:
                n = len(lits)
                if not svars:
                    # Ground clause — direct unit propagation
                    result = self._unit_propagate(lits, closure)
                    if result is not None and result not in closure:
                        closure.add(result)
                        changed = True
                    continue

                # For each literal i as the "free" one to derive,
                # match all other literals' negations against known.
                for free_idx in range(n):
                    prereqs = [lits[j] for j in range(n) if j != free_idx]
                    for sub in self._match_prereqs(
                            prereqs, svars, idx, points):
                        # Check the clause isn't already satisfied
                        # (some other literal already in closure)
                        ground_free = t_substitute_literal(
                            lits[free_idx], sub)
                        if ground_free in closure:
                            continue
                        already_sat = False
                        for j in range(n):
                            if j == free_idx:
                                continue
                            gl = t_substitute_literal(lits[j], sub)
                            if gl in closure:
                                already_sat = True
                                break
                        if already_sat:
                            continue
                        closure.add(ground_free)
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

    # ── Unit propagation ──────────────────────────────────────────────

    @staticmethod
    def _unit_propagate(
        lits: List[TLiteral], closure: Set[TLiteral]
    ) -> Optional[TLiteral]:
        """Classic unit propagation on a ground clause.

        Returns the single derivable literal if all-but-one disjunct's
        negation is in closure, or None.
        """
        unknown_lit = None
        for lit in lits:
            if lit in closure:
                return None          # clause already satisfied
            neg = lit.negated()
            if neg in closure:
                continue             # this disjunct is eliminated
            if unknown_lit is not None:
                return None          # >1 unknown → can't derive
            unknown_lit = lit
        return unknown_lit

    # ── Matched grounding ─────────────────────────────────────────────

    def _build_index(
        self, known: Set[TLiteral]
    ) -> Dict[Tuple[str, bool], List[TLiteral]]:
        """Index known literals by (atom_type, polarity)."""
        idx: Dict[Tuple[str, bool], List[TLiteral]] = {}
        for lit in known:
            key = _lit_key(lit)
            idx.setdefault(key, []).append(lit)
        return idx

    def _match_prereqs(
        self,
        prereqs: List[TLiteral],
        schema_vars: List[str],
        idx: Dict[Tuple[str, bool], List[TLiteral]],
        points: List[str],
    ) -> List[Dict[str, str]]:
        """Find substitutions making all prereq negations appear in known.

        For each prereq Lⱼ, we need ¬Lⱼ ∈ known.
        ¬Lⱼ has the same atom but opposite polarity.
        """
        if not prereqs:
            # Unconditional — enumerate from points (rare, low arity)
            return self._enumerate_subs(schema_vars, points)

        # Sort prereqs so the most constraining (fewest candidates) comes first
        ordered = sorted(
            prereqs,
            key=lambda l: len(idx.get(
                (type(l.atom).__name__, not l.polarity), [])))

        # Seed from first prereq
        subs = self._seed_from_prereq(ordered[0], idx)
        for pq in ordered[1:]:
            if not subs:
                break
            subs = self._refine_with_prereq(subs, pq, idx)
            if not subs:
                break

        if not subs:
            return []

        # Fill any schema variables that appear only in the free literal
        return self._fill_unbound(subs, schema_vars, points)

    def _seed_from_prereq(
        self, prereq: TLiteral,
        idx: Dict[Tuple[str, bool], List[TLiteral]],
    ) -> List[Dict[str, str]]:
        """Match ¬prereq against known to get initial substitutions.

        prereq is Lⱼ; we need ¬Lⱼ = (atom, !polarity) in known.
        """
        neg_key = (type(prereq.atom).__name__, not prereq.polarity)
        candidates = idx.get(neg_key, [])
        schema_args = _atom_args(prereq.atom)

        subs: List[Dict[str, str]] = []
        for fact in candidates:
            fact_args = _atom_args(fact.atom)
            if len(fact_args) != len(schema_args):
                continue
            sub = self._unify_args(schema_args, fact_args)
            if sub is not None:
                subs.append(sub)
        return subs

    def _refine_with_prereq(
        self,
        subs: List[Dict[str, str]],
        prereq: TLiteral,
        idx: Dict[Tuple[str, bool], List[TLiteral]],
    ) -> List[Dict[str, str]]:
        """Keep only substitutions that also satisfy prereq's negation."""
        neg_key = (type(prereq.atom).__name__, not prereq.polarity)
        candidates = idx.get(neg_key, [])
        schema_args = _atom_args(prereq.atom)

        refined: List[Dict[str, str]] = []
        for sub in subs:
            # Check which schema args are already bound
            all_bound = all(a in sub for a in schema_args)

            if all_bound:
                # Fully ground — check if ¬prereq is in known
                grounded = tuple(sub[a] for a in schema_args)
                ground_atom = self._make_atom(neg_key[0], grounded)
                if ground_atom is not None:
                    target = TLiteral(ground_atom, neg_key[1])
                    if target in candidates or target in (
                            idx.get(neg_key, [])):
                        refined.append(sub)
            else:
                # Partially bound — match against candidates
                for fact in candidates:
                    fact_args = _atom_args(fact.atom)
                    if len(fact_args) != len(schema_args):
                        continue
                    new_sub = dict(sub)
                    ok = True
                    for svar, fval in zip(schema_args, fact_args):
                        if svar in new_sub:
                            if new_sub[svar] != fval:
                                ok = False
                                break
                        else:
                            new_sub[svar] = fval
                    if ok:
                        refined.append(new_sub)

        return refined

    def _fill_unbound(
        self,
        subs: List[Dict[str, str]],
        schema_vars: List[str],
        points: List[str],
    ) -> List[Dict[str, str]]:
        """Fill any remaining unbound schema variables with point pool.

        Skips expansion when the estimated number of combinations
        exceeds ``_MAX_FILL`` to prevent combinatorial blowup.
        """
        if not subs:
            return []
        # Quick check — any sub missing a variable?
        needs_fill = any(
            any(v not in sub for v in schema_vars) for sub in subs)
        if not needs_fill:
            return subs

        _MAX_FILL = 50_000
        filled: List[Dict[str, str]] = []
        for sub in subs:
            missing = [v for v in schema_vars if v not in sub]
            if not missing:
                filled.append(sub)
                continue
            if len(points) ** len(missing) > _MAX_FILL:
                continue
            for combo in iprod(points, repeat=len(missing)):
                new_sub = dict(sub)
                for var, val in zip(missing, combo):
                    new_sub[var] = val
                filled.append(new_sub)
        return filled

    def _enumerate_subs(
        self, schema_vars: List[str], points: List[str]
    ) -> List[Dict[str, str]]:
        """Enumerate all substitutions for schema variables from points.

        Returns an empty list when the combination count would exceed
        the safety limit.
        """
        if not schema_vars:
            return [{}]
        if len(points) ** len(schema_vars) > 50_000:
            return []
        result: List[Dict[str, str]] = []
        for combo in iprod(points, repeat=len(schema_vars)):
            result.append(dict(zip(schema_vars, combo)))
        return result

    @staticmethod
    def _unify_args(
        schema: Tuple[str, ...], concrete: Tuple[str, ...]
    ) -> Optional[Dict[str, str]]:
        """Try to unify schema args with concrete args.

        Returns a substitution dict if consistent, None if conflict.
        """
        sub: Dict[str, str] = {}
        for svar, cval in zip(schema, concrete):
            if svar in sub:
                if sub[svar] != cval:
                    return None
            else:
                sub[svar] = cval
        return sub

    @staticmethod
    def _make_atom(
        type_key: str, args: Tuple[str, ...]
    ) -> Optional[TAtom]:
        """Construct an atom from type key and argument tuple."""
        if type_key == "B" and len(args) == 3:
            return B(*args)
        if type_key == "Cong" and len(args) == 4:
            return Cong(*args)
        if type_key == "NotB" and len(args) == 3:
            return NotB(*args)
        if type_key == "NotCong" and len(args) == 4:
            return NotCong(*args)
        if type_key == "Eq" and len(args) == 2:
            return Eq(*args)
        if type_key == "Neq" and len(args) == 2:
            return Neq(*args)
        return None

    def _clause_schema_vars_set(self, clause: TClause) -> Set[str]:
        """Extract schema variable names from a clause."""
        seen: Set[str] = set()
        for lit in clause.literals:
            for v in t_atom_vars(lit.atom):
                seen.add(v)
        return seen

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
