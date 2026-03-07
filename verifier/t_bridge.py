"""
t_bridge.py — Bridge between System E and System T (Tarski's axioms).

Provides translation functions between the two formal systems,
implementing the maps π (E→T) and ρ (T→E) from Paper Section 5.3–5.4.

The full equivalence chain is:
  System E ↔ Tarski (T) ↔ Hilbert (H)
established by GeoCoq's:
  - tarski_to_euclid.v / euclid_to_tarski.v → T ↔ E
  - tarski_to_hilbert.v / hilbert_to_tarski.v → T ↔ H

Key translations:
  E                                T
  ──────────────────────────────  ──────────────────────────────
  between(a, b, c) (strict)       B(a,b,c) ∧ Neq(a,b) ∧ Neq(b,c) ∧ Neq(a,c)
  ¬between(a, b, c)               NotB(a,b,c) ∨ Eq(a,b) ∨ Eq(b,c) ∨ Eq(a,c)
  a = b  (point equality)         Eq(a, b)
  a ≠ b  (point disequality)      Neq(a, b)
  segment ab = cd                 Cong(a, b, c, d)
  segment ab ≠ cd                 NotCong(a, b, c, d)
  on(a, L)                        [complex: collinearity with line witnesses]
  same-side(a, b, L)              [complex: requires auxiliary points]
  center(a, α), inside(a, α)     [circle predicates: no direct T analog]

Note: Full translations of on(), same-side(), and circle predicates
require auxiliary existential variables and are part of Phase 5
(completeness infrastructure).  This module provides the direct
literal-level translations that are possible without existentials.

Reference:
  Avigad, Dean, Mumma (2009), Sections 5.3–5.4
  GeoCoq tarski_to_euclid.v / euclid_to_tarski.v
"""
from __future__ import annotations

from typing import Dict, List, Optional, Set

from .e_ast import (
    Sort as ESort,
    Literal as ELiteral,
    On, SameSide, Between, Center, Inside, Intersects,
    Equals as EEquals, LessThan,
    SegmentTerm, AngleTerm,
    Sequent as ESequent, ETheorem,
)
from .t_ast import (
    TSort, TLiteral, TSequent, TTheorem,
    B, Cong, NotB, NotCong, Eq, Neq,
)


# ═══════════════════════════════════════════════════════════════════════
# E → T Translation (partial π)
# ═══════════════════════════════════════════════════════════════════════

def e_literal_to_t(lit: ELiteral) -> Optional[List[TLiteral]]:
    """Translate a System E literal to System T literal(s).

    Returns a list of T literals (conjunction) that express the E
    literal in Tarski's language.  Returns None for literals that
    have no direct T counterpart (on, same-side, circle predicates).

    For strict between(a,b,c) in E, we need:
      B(a,b,c) ∧ Neq(a,b) ∧ Neq(b,c) ∧ Neq(a,c)
    """
    atom = lit.atom
    pol = lit.polarity

    # between(a, b, c) — strict betweenness
    if isinstance(atom, Between):
        if pol:
            # between(a,b,c) → B(a,b,c) ∧ a≠b ∧ b≠c ∧ a≠c
            return [
                TLiteral(B(atom.a, atom.b, atom.c), True),
                TLiteral(Neq(atom.a, atom.b), True),
                TLiteral(Neq(atom.b, atom.c), True),
                TLiteral(Neq(atom.a, atom.c), True),
            ]
        else:
            # ¬between(a,b,c) cannot be directly expressed as a
            # single conjunction; return None for now (Phase 5 handles
            # full disjunctive translations)
            return None

    # Point equality: a = b → Eq(a, b)
    if isinstance(atom, EEquals):
        left, right = atom.left, atom.right
        if isinstance(left, str) and isinstance(right, str):
            if pol:
                return [TLiteral(Eq(left, right), True)]
            else:
                return [TLiteral(Neq(left, right), True)]

        # Segment equality: ab = cd → Cong(a, b, c, d)
        if isinstance(left, SegmentTerm) and isinstance(right, SegmentTerm):
            if pol:
                return [TLiteral(
                    Cong(left.p1, left.p2, right.p1, right.p2), True
                )]
            else:
                return [TLiteral(
                    NotCong(left.p1, left.p2, right.p1, right.p2), True
                )]

        # Angle equality: complex translation (Phase 5)
        return None

    # on(), same-side(), center(), inside(), intersects() —
    # require existential auxiliary variables (Phase 5)
    return None


def e_literal_to_t_single(lit: ELiteral) -> Optional[TLiteral]:
    """Translate E literal to a single T literal (when possible).

    Returns None if the translation requires multiple literals or
    is not directly expressible.
    """
    result = e_literal_to_t(lit)
    if result is not None and len(result) == 1:
        return result[0]
    return None


# ═══════════════════════════════════════════════════════════════════════
# T → E Translation (partial ρ)
# ═══════════════════════════════════════════════════════════════════════

def t_literal_to_e(lit: TLiteral) -> Optional[ELiteral]:
    """Translate a System T literal to a System E literal.

    Returns None for literals that have no direct E counterpart.
    """
    atom = lit.atom
    pol = lit.polarity

    # B(a, b, c) → between(a, b, c) (but E's between is strict)
    # Note: B is nonstrict in T, strict in E.  A positive B translates
    # to between only when combined with distinctness info.  We provide
    # a best-effort translation here; full ρ is in Phase 5.
    if isinstance(atom, B):
        if pol:
            return ELiteral(Between(atom.a, atom.b, atom.c), True)
        else:
            return ELiteral(Between(atom.a, atom.b, atom.c), False)

    # NotB(a, b, c) → ¬between(a, b, c)
    if isinstance(atom, NotB):
        if pol:
            return ELiteral(Between(atom.a, atom.b, atom.c), False)
        else:
            return ELiteral(Between(atom.a, atom.b, atom.c), True)

    # Cong(a, b, c, d) → segment ab = cd
    if isinstance(atom, Cong):
        seg_left = SegmentTerm(atom.a, atom.b)
        seg_right = SegmentTerm(atom.c, atom.d)
        return ELiteral(EEquals(seg_left, seg_right), pol)

    # NotCong(a, b, c, d) → segment ab ≠ cd
    if isinstance(atom, NotCong):
        seg_left = SegmentTerm(atom.a, atom.b)
        seg_right = SegmentTerm(atom.c, atom.d)
        if pol:
            return ELiteral(EEquals(seg_left, seg_right), False)
        else:
            return ELiteral(EEquals(seg_left, seg_right), True)

    # Eq(a, b) → a = b
    if isinstance(atom, Eq):
        return ELiteral(EEquals(atom.left, atom.right), pol)

    # Neq(a, b) → a ≠ b
    if isinstance(atom, Neq):
        if pol:
            return ELiteral(EEquals(atom.left, atom.right), False)
        else:
            return ELiteral(EEquals(atom.left, atom.right), True)

    return None


# ═══════════════════════════════════════════════════════════════════════
# Sequent-level translations
# ═══════════════════════════════════════════════════════════════════════

def e_sequent_to_t(seq: ESequent) -> TSequent:
    """Translate a System E sequent to a System T sequent.

    Drops hypotheses/conclusions that cannot be directly translated
    (on, same-side, circle predicates).  Point-sorted existential
    variables are preserved; line/circle variables are dropped.
    """
    hyps: List[TLiteral] = []
    for h in seq.hypotheses:
        result = e_literal_to_t(h)
        if result:
            hyps.extend(result)

    concs: List[TLiteral] = []
    for c in seq.conclusions:
        result = e_literal_to_t(c)
        if result:
            concs.extend(result)

    evars = [
        (name, TSort.POINT)
        for name, sort in seq.exists_vars
        if sort == ESort.POINT
    ]

    return TSequent(
        hypotheses=hyps,
        exists_vars=evars,
        conclusions=concs,
    )


def t_sequent_to_e(seq: TSequent) -> ESequent:
    """Translate a System T sequent to a System E sequent.

    Drops literals that cannot be directly translated.
    """
    from .e_ast import Sequent as ESequent, Sort as ESort

    hyps: List[ELiteral] = []
    for h in seq.hypotheses:
        result = t_literal_to_e(h)
        if result:
            hyps.append(result)

    concs: List[ELiteral] = []
    for c in seq.conclusions:
        result = t_literal_to_e(c)
        if result:
            concs.append(result)

    evars = [
        (name, ESort.POINT)
        for name, sort in seq.exists_vars
        if sort == TSort.POINT
    ]

    return ESequent(
        hypotheses=hyps,
        exists_vars=evars,
        conclusions=concs,
    )


# ═══════════════════════════════════════════════════════════════════════
# Convenience API
# ═══════════════════════════════════════════════════════════════════════

def check_with_system_t(e_sequent: ESequent) -> Optional[bool]:
    """Translate an E sequent to T and check via consequence engine.

    Returns True if the T translation's conclusions follow from its
    hypotheses, False if not, None if translation is incomplete.
    """
    t_seq = e_sequent_to_t(e_sequent)
    if not t_seq.conclusions:
        return None

    from .t_consequence import TConsequenceEngine
    engine = TConsequenceEngine()
    known = set(t_seq.hypotheses)
    variables = {
        name: TSort.POINT
        for name, _ in t_seq.exists_vars
    }
    for lit in t_seq.hypotheses:
        from .t_ast import t_literal_vars
        for v in t_literal_vars(lit):
            variables[v] = TSort.POINT

    closure = engine.direct_consequences(known, variables)
    return all(c in closure for c in t_seq.conclusions)
