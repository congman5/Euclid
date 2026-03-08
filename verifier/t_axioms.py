"""
t_axioms.py — Axioms for Tarski's geometry (System T).

All axioms from Tarski's axiomatization of ruler-and-compass Euclidean
geometry (Paper Section 5.2), expressed as geometric rule schemes (GRS)
suitable for the contrapositive forward-chaining consequence engine.

Tarski's system uses one sort (points) and two primitives:
  B(a, b, c)      — nonstrict betweenness
  Cong(a, b, c, d) — equidistance (ab ≡ cd)

To make the axioms geometric (Negri 2003), explicit negation predicates
are added (Paper Section 5.2):
  Neq(a, b)          — a ≠ b
  NotB(a, b, c)      — ¬B(a, b, c)  (written B̄ in the paper)
  NotCong(a, b, c, d) — ¬Cong(a, b, c, d) (written ≢ in the paper)

Axiom List (from Paper Section 5.2, Tarski & Givant 1999):
  E1  — Equidistance symmetry:  ab ≡ ba
  E2  — Equidistance transitivity: ab≡pq ∧ ab≡rs → pq≡rs
  E3  — Identity of equidistance: ab≡cc → a=b
  A6  — Betweenness identity: B(aba) → a=b
  B   — Inner transitivity of betweenness: B(abd) ∧ B(bcd) → B(abc)
  SC  — Segment construction: ∃x. B(qax) ∧ ax≡bc
  5S  — Five-segment
  P   — Pasch: B(apc) ∧ B(qcb) → ∃x. B(axq) ∧ B(bpx)
  2L  — Lower 2D: ∃a,b,c. NotB(abc) ∧ NotB(bca) ∧ NotB(cab)
  2U  — Upper 2D: a≠b ∧ x₁a≡x₁b ∧ x₂a≡x₂b ∧ x₃a≡x₃b →
         B(x₁x₂x₃) ∨ B(x₂x₃x₁) ∨ B(x₃x₁x₂)
  PP  — Parallel postulate: B(adt) ∧ B(bdc) ∧ a≠d →
         ∃x,y. B(abx) ∧ B(acy) ∧ B(ytx)
  Int — Intersection: ax≡ax' ∧ az≡az' ∧ B(axz) ∧ B(xyz) →
         ∃y'. ay≡ay' ∧ B(x'y'z')

Negativity axioms (6 clauses):
  For each pair (P, P̄) ∈ {(Eq,Neq), (B,NotB), (Cong,NotCong)}:
    ∀x̄. P(x̄) ∨ P̄(x̄)           — decidability
    ∀x̄. P(x̄) ∧ P̄(x̄) → ⊥      — consistency

GeoCoq reference: theories/Axioms/tarski_axioms.v
"""
from __future__ import annotations

from typing import List

from .t_ast import (
    TLiteral, TClause,
    B, Cong, NotB, NotCong, Eq, Neq,
)


def _pos(atom) -> TLiteral:
    return TLiteral(atom, polarity=True)


def _neg(atom) -> TLiteral:
    return TLiteral(atom, polarity=False)


def _clause(*lits: TLiteral) -> TClause:
    return TClause(frozenset(lits))


# ═══════════════════════════════════════════════════════════════════════
# Equidistance axioms (E1, E2, E3)
# ═══════════════════════════════════════════════════════════════════════

EQUIDISTANCE_AXIOMS: List[TClause] = [
    # E1. Equidistance symmetry: ab ≡ ba  (always true)
    # GRS form: Cong(a,b,b,a), Γ ⇒ Δ  /  Γ ⇒ Δ
    # As a clause: Cong(a, b, b, a)
    _clause(_pos(Cong("a", "b", "b", "a"))),

    # E2. Equidistance transitivity:
    #   ab ≡ pq ∧ ab ≡ rs → pq ≡ rs
    # Clause: ¬Cong(a,b,p,q) ∨ ¬Cong(a,b,r,s) ∨ Cong(p,q,r,s)
    _clause(_neg(Cong("a", "b", "p", "q")),
            _neg(Cong("a", "b", "r", "s")),
            _pos(Cong("p", "q", "r", "s"))),

    # E3. Identity of equidistance: ab ≡ cc → a = b
    # Clause: ¬Cong(a,b,c,c) ∨ Eq(a,b)
    _clause(_neg(Cong("a", "b", "c", "c")),
            _pos(Eq("a", "b"))),
]


# ═══════════════════════════════════════════════════════════════════════
# Betweenness axioms (A6, B)
# ═══════════════════════════════════════════════════════════════════════

BETWEENNESS_AXIOMS: List[TClause] = [
    # A6. Betweenness identity: B(a,b,a) → a = b
    # Paper §5.2: "B(aba) → a = b"
    # Boutry et al. Table 1 (A6): "A B A ⇒ A = B"
    # Coghetto/Grabowski: "betweenness identity"
    # Clause: ¬B(a,b,a) ∨ Eq(a,b)
    _clause(_neg(B("a", "b", "a")),
            _pos(Eq("a", "b"))),

    # B (A15). Inner transitivity: B(abd) ∧ B(bcd) → B(abc)
    # Clause: ¬B(a,b,d) ∨ ¬B(b,c,d) ∨ B(a,b,c)
    _clause(_neg(B("a", "b", "d")),
            _neg(B("b", "c", "d")),
            _pos(B("a", "b", "c"))),
]


# ═══════════════════════════════════════════════════════════════════════
# Five-segment axiom (5S)
# ═══════════════════════════════════════════════════════════════════════

FIVE_SEGMENT_AXIOMS: List[TClause] = [
    # 5S. a≠b ∧ B(abc) ∧ B(pqr) ∧ ab≡pq ∧ bc≡qr ∧ ad≡ps ∧ bd≡qs
    #     → cd ≡ rs
    # Clause: Eq(a,b) ∨ ¬B(a,b,c) ∨ ¬B(p,q,r) ∨ ¬Cong(a,b,p,q)
    #         ∨ ¬Cong(b,c,q,r) ∨ ¬Cong(a,d,p,s) ∨ ¬Cong(b,d,q,s)
    #         ∨ Cong(c,d,r,s)
    # Note: a≠b in the hypothesis becomes Eq(a,b) (positive) in the clause
    # because the hypothesis Neq(a,b) negates to Eq(a,b) in contrapositive.
    _clause(_pos(Eq("a", "b")),
            _neg(B("a", "b", "c")),
            _neg(B("p", "q", "r")),
            _neg(Cong("a", "b", "p", "q")),
            _neg(Cong("b", "c", "q", "r")),
            _neg(Cong("a", "d", "p", "s")),
            _neg(Cong("b", "d", "q", "s")),
            _pos(Cong("c", "d", "r", "s"))),
]


# ═══════════════════════════════════════════════════════════════════════
# Upper 2D axiom (2U)
# ═══════════════════════════════════════════════════════════════════════
#
# a≠b ∧ x₁a≡x₁b ∧ x₂a≡x₂b ∧ x₃a≡x₃b
#   → B(x₁,x₂,x₃) ∨ B(x₂,x₃,x₁) ∨ B(x₃,x₁,x₂)
#
# This is a 3-way case split.  In GRS form, it becomes three premises:
#   B(x₁,x₂,x₃), Γ ⇒ Δ
#   B(x₂,x₃,x₁), Γ ⇒ Δ
#   B(x₃,x₁,x₂), Γ ⇒ Δ
#   ────────────────────────────
#   Neq(a,b), Cong(x₁,a,x₁,b), Cong(x₂,a,x₂,b), Cong(x₃,a,x₃,b), Γ ⇒ Δ
#
# As clauses (one per disjunct, all sharing the same hypotheses):

UPPER_2D_AXIOMS: List[TClause] = [
    # 2U, disjunct 1: → B(x₁,x₂,x₃)
    _clause(_pos(Eq("a", "b")),
            _neg(Cong("x1", "a", "x1", "b")),
            _neg(Cong("x2", "a", "x2", "b")),
            _neg(Cong("x3", "a", "x3", "b")),
            _pos(B("x1", "x2", "x3"))),

    # 2U, disjunct 2: → B(x₂,x₃,x₁)
    _clause(_pos(Eq("a", "b")),
            _neg(Cong("x1", "a", "x1", "b")),
            _neg(Cong("x2", "a", "x2", "b")),
            _neg(Cong("x3", "a", "x3", "b")),
            _pos(B("x2", "x3", "x1"))),

    # 2U, disjunct 3: → B(x₃,x₁,x₂)
    _clause(_pos(Eq("a", "b")),
            _neg(Cong("x1", "a", "x1", "b")),
            _neg(Cong("x2", "a", "x2", "b")),
            _neg(Cong("x3", "a", "x3", "b")),
            _pos(B("x3", "x1", "x2"))),
]


# ═══════════════════════════════════════════════════════════════════════
# Construction axioms (SC, P, PP, Int, 2L)
#
# These axioms have existential conclusions: ∃x. ...
# They are used in construction steps, not deduction steps.
# We encode them as clauses where the existential variable appears
# as a schema variable (the checker must ensure freshness).
# ═══════════════════════════════════════════════════════════════════════

CONSTRUCTION_AXIOMS: List[TClause] = [
    # SC (Segment Construction): ∃x. B(q,a,x) ∧ Cong(a,x,b,c)
    # Split into two clauses (conjunction):
    # SC.1: B(q, a, x)
    _clause(_pos(B("q", "a", "x"))),
    # SC.2: Cong(a, x, b, c)
    _clause(_pos(Cong("a", "x", "b", "c"))),
    # Note: x must be fresh.  The checker validates freshness.

    # P (Pasch): B(a,p,c) ∧ B(q,c,b) → ∃x. B(a,x,q) ∧ B(b,p,x)
    # P.1: ¬B(a,p,c) ∨ ¬B(q,c,b) ∨ B(a,x,q)
    _clause(_neg(B("a", "p", "c")),
            _neg(B("q", "c", "b")),
            _pos(B("a", "x", "q"))),
    # P.2: ¬B(a,p,c) ∨ ¬B(q,c,b) ∨ B(b,p,x)
    _clause(_neg(B("a", "p", "c")),
            _neg(B("q", "c", "b")),
            _pos(B("b", "p", "x"))),

    # PP (Parallel Postulate):
    #   B(a,d,t) ∧ B(b,d,c) ∧ a≠d → ∃x,y. B(a,b,x) ∧ B(a,c,y) ∧ B(y,t,x)
    # PP.1: ¬B(a,d,t) ∨ ¬B(b,d,c) ∨ Eq(a,d) ∨ B(a,b,x)
    _clause(_neg(B("a", "d", "t")),
            _neg(B("b", "d", "c")),
            _pos(Eq("a", "d")),
            _pos(B("a", "b", "x"))),
    # PP.2: ¬B(a,d,t) ∨ ¬B(b,d,c) ∨ Eq(a,d) ∨ B(a,c,y)
    _clause(_neg(B("a", "d", "t")),
            _neg(B("b", "d", "c")),
            _pos(Eq("a", "d")),
            _pos(B("a", "c", "y"))),
    # PP.3: ¬B(a,d,t) ∨ ¬B(b,d,c) ∨ Eq(a,d) ∨ B(y,t,x)
    _clause(_neg(B("a", "d", "t")),
            _neg(B("b", "d", "c")),
            _pos(Eq("a", "d")),
            _pos(B("y", "t", "x"))),

    # Int (Intersection):
    #   Cong(a,x,a,x') ∧ Cong(a,z,a,z') ∧ B(a,x,z) ∧ B(x,y,z)
    #     → ∃y'. Cong(a,y,a,y') ∧ B(x',y',z')
    # Int.1: ¬Cong(a,x,a,xp) ∨ ¬Cong(a,z,a,zp) ∨ ¬B(a,x,z)
    #        ∨ ¬B(x,y,z) ∨ Cong(a,y,a,yp)
    _clause(_neg(Cong("a", "x", "a", "xp")),
            _neg(Cong("a", "z", "a", "zp")),
            _neg(B("a", "x", "z")),
            _neg(B("x", "y", "z")),
            _pos(Cong("a", "y", "a", "yp"))),
    # Int.2: ¬Cong(a,x,a,xp) ∨ ¬Cong(a,z,a,zp) ∨ ¬B(a,x,z)
    #        ∨ ¬B(x,y,z) ∨ B(xp,yp,zp)
    _clause(_neg(Cong("a", "x", "a", "xp")),
            _neg(Cong("a", "z", "a", "zp")),
            _neg(B("a", "x", "z")),
            _neg(B("x", "y", "z")),
            _pos(B("xp", "yp", "zp"))),
]

# 2L (Lower 2D): ∃a,b,c. NotB(a,b,c) ∧ NotB(b,c,a) ∧ NotB(c,a,b)
# This is an existence axiom about *axiom constants*, similar to
# Hilbert's lower_dim_2.  Constants are named T_P1, T_P2, T_P3.
# These must NOT be grounded by the consequence engine.

LOWER_DIM_AXIOMS: List[TClause] = [
    # 2L.1: NotB(T_P1, T_P2, T_P3)
    _clause(_pos(NotB("T_P1", "T_P2", "T_P3"))),
    # 2L.2: NotB(T_P2, T_P3, T_P1)
    _clause(_pos(NotB("T_P2", "T_P3", "T_P1"))),
    # 2L.3: NotB(T_P3, T_P1, T_P2)
    _clause(_pos(NotB("T_P3", "T_P1", "T_P2"))),
]


# ═══════════════════════════════════════════════════════════════════════
# Negativity axioms (Paper Section 5.2)
#
# For each pair (P, P̄) ∈ {(Eq,Neq), (B,NotB), (Cong,NotCong)}:
#   Decidability:  P(x̄) ∨ P̄(x̄)
#   Consistency:   P(x̄) ∧ P̄(x̄) → ⊥  (encoded as: ¬P ∨ ¬P̄)
# ═══════════════════════════════════════════════════════════════════════

NEGATIVITY_AXIOMS: List[TClause] = [
    # Eq/Neq decidability: Eq(a,b) ∨ Neq(a,b)
    _clause(_pos(Eq("a", "b")), _pos(Neq("a", "b"))),

    # Eq/Neq consistency: ¬Eq(a,b) ∨ ¬Neq(a,b)
    _clause(_neg(Eq("a", "b")), _neg(Neq("a", "b"))),

    # B/NotB decidability: B(a,b,c) ∨ NotB(a,b,c)
    _clause(_pos(B("a", "b", "c")), _pos(NotB("a", "b", "c"))),

    # B/NotB consistency: ¬B(a,b,c) ∨ ¬NotB(a,b,c)
    _clause(_neg(B("a", "b", "c")), _neg(NotB("a", "b", "c"))),

    # Cong/NotCong decidability: Cong(a,b,c,d) ∨ NotCong(a,b,c,d)
    _clause(_pos(Cong("a", "b", "c", "d")),
            _pos(NotCong("a", "b", "c", "d"))),

    # Cong/NotCong consistency: ¬Cong(a,b,c,d) ∨ ¬NotCong(a,b,c,d)
    _clause(_neg(Cong("a", "b", "c", "d")),
            _neg(NotCong("a", "b", "c", "d"))),
]


# ═══════════════════════════════════════════════════════════════════════
# Equality axioms
#
# Standard first-order equality properties, needed since Tarski's
# system relies on equality for point identity.
# ═══════════════════════════════════════════════════════════════════════

EQUALITY_AXIOMS: List[TClause] = [
    # Reflexivity: Eq(a, a)
    _clause(_pos(Eq("a", "a"))),

    # Symmetry: Eq(a,b) → Eq(b,a)
    _clause(_neg(Eq("a", "b")), _pos(Eq("b", "a"))),

    # Transitivity: Eq(a,b) ∧ Eq(b,c) → Eq(a,c)
    _clause(_neg(Eq("a", "b")), _neg(Eq("b", "c")),
            _pos(Eq("a", "c"))),
]


# ═══════════════════════════════════════════════════════════════════════
# Aggregate collections
# ═══════════════════════════════════════════════════════════════════════

# Deduction axioms: used for deriving new facts from known ones.
# Excludes construction axioms (SC, P, PP, Int) and lower-dim (2L),
# which introduce existentially quantified variables.
DEDUCTION_AXIOMS: List[TClause] = (
    EQUIDISTANCE_AXIOMS
    + BETWEENNESS_AXIOMS
    + FIVE_SEGMENT_AXIOMS
    + UPPER_2D_AXIOMS
    + EQUALITY_AXIOMS
    + NEGATIVITY_AXIOMS
)

# All axioms including construction rules and lower-dim.
ALL_T_AXIOMS: List[TClause] = (
    DEDUCTION_AXIOMS
    + CONSTRUCTION_AXIOMS
    + LOWER_DIM_AXIOMS
)
