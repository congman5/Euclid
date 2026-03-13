"""
e_axioms.py — Diagrammatic, metric, and transfer axioms for System E.

All axioms from Sections 3.4–3.6 of Avigad, Dean, Mumma (2009),
"A Formal System for Euclid's Elements."

Each axiom is represented as one or more *clauses* — finite sets of
literals read disjunctively.  An axiom "if φ₁, …, φₙ then ψ" becomes
the clause {¬φ₁, …, ¬φₙ, ψ}.

Multi-conclusion axioms are split into multiple clauses.  Disjunctive
hypotheses are also split (see Section 3.8 of the paper).

The direct consequence engine (e_consequence.py) uses these clauses
with contrapositive forward-chaining.

GeoCoq connection (https://geocoq.github.io/GeoCoq/):
  GeoCoq formalizes foundations of geometry in Coq using Tarski's axioms
  and provides a bridge to Euclidean axioms.  Avigad et al. (2009,
  Section 5) prove that System E is sound and complete for ruler-and-
  compass constructions by translating to/from Tarski's axiomatization.
  GeoCoq's euclidean_axioms.v and tarski_to_euclid.v/euclid_to_tarski.v
  provide machine-checked proofs of this equivalence.  Our axiom clauses
  correspond directly to the GeoCoq Euclidean axiom formalization.
"""
from __future__ import annotations

from typing import List

from .e_ast import (
    Sort,
    SegmentTerm, AngleTerm, AreaTerm, MagAdd, RightAngle, ZeroMag,
    On, SameSide, Between, Center, Inside, Intersects,
    Equals, LessThan,
    Literal, Clause,
)


def _pos(atom) -> Literal:
    return Literal(atom, polarity=True)


def _neg(atom) -> Literal:
    return Literal(atom, polarity=False)


def _clause(*lits: Literal) -> Clause:
    return Clause(frozenset(lits))


# Variable naming convention for axiom schemas:
#   Points: a, b, c, d, e   Lines: L, M, N   Circles: α (alpha), β (beta)
# These are *schema variables* — they get instantiated with actual names.

# ═══════════════════════════════════════════════════════════════════════
# Section 3.4: Diagrammatic axioms
# ═══════════════════════════════════════════════════════════════════════

# ── Generalities ──────────────────────────────────────────────────────

GENERALITY_AXIOMS: List[Clause] = [
    # G1. If a ≠ b, on(a,L), on(b,L), on(a,M), on(b,M) → L = M
    #     Clause: a=b ∨ ¬on(a,L) ∨ ¬on(b,L) ∨ ¬on(a,M) ∨ ¬on(b,M) ∨ L=M
    _clause(_pos(Equals("a", "b")),
            _neg(On("a", "L")), _neg(On("b", "L")),
            _neg(On("a", "M")), _neg(On("b", "M")),
            _pos(Equals("L", "M"))),

    # G2. center(a,α) ∧ center(b,α) → a = b
    _clause(_neg(Center("a", "\u03b1")), _neg(Center("b", "\u03b1")),
            _pos(Equals("a", "b"))),

    # G3. center(a,α) → inside(a,α)
    _clause(_neg(Center("a", "\u03b1")), _pos(Inside("a", "\u03b1"))),

    # G4. inside(a,α) → ¬on(a,α)
    _clause(_neg(Inside("a", "\u03b1")), _neg(On("a", "\u03b1"))),

    # G5. on(a,L) ∧ ¬on(a,M) → L≠M
    # (If L=M then on(a,L)→on(a,M), contradicting ¬on(a,M).)
    _clause(_neg(On("a", "L")), _pos(On("a", "M")),
            _neg(Equals("L", "M"))),

    # G6. on(a,L) ∧ ¬on(b,L) → a≠b
    # (If a=b then on(a,L)→on(b,L), contradicting ¬on(b,L).)
    _clause(_neg(On("a", "L")), _pos(On("b", "L")),
            _neg(Equals("a", "b"))),
]

# ── Between axioms ────────────────────────────────────────────────────

BETWEEN_AXIOMS: List[Clause] = [
    # B1a. between(a,b,c) → between(c,b,a)
    _clause(_neg(Between("a", "b", "c")), _pos(Between("c", "b", "a"))),
    # B1b. between(a,b,c) → a ≠ b
    _clause(_neg(Between("a", "b", "c")), _neg(Equals("a", "b"))),
    # B1c. between(a,b,c) → a ≠ c
    _clause(_neg(Between("a", "b", "c")), _neg(Equals("a", "c"))),
    # B1d. between(a,b,c) → ¬between(b,a,c)
    _clause(_neg(Between("a", "b", "c")), _neg(Between("b", "a", "c"))),

    # B2. between(a,b,c) ∧ on(a,L) ∧ on(b,L) → on(c,L)
    _clause(_neg(Between("a", "b", "c")), _neg(On("a", "L")),
            _neg(On("b", "L")), _pos(On("c", "L"))),

    # B3. between(a,b,c) ∧ on(a,L) ∧ on(c,L) → on(b,L)
    _clause(_neg(Between("a", "b", "c")), _neg(On("a", "L")),
            _neg(On("c", "L")), _pos(On("b", "L"))),

    # B4. between(a,b,c) ∧ between(a,d,b) → between(a,d,c)
    _clause(_neg(Between("a", "b", "c")), _neg(Between("a", "d", "b")),
            _pos(Between("a", "d", "c"))),

    # B5. between(a,b,c) ∧ between(b,c,d) → between(a,b,d)
    _clause(_neg(Between("a", "b", "c")), _neg(Between("b", "c", "d")),
            _pos(Between("a", "b", "d"))),

    # B6. a,b,c distinct on L → between(a,b,c) ∨ between(b,c,a) ∨ between(c,a,b)
    # This has a disjunctive conclusion.  As a clause:
    # a=b ∨ a=c ∨ b=c ∨ ¬on(a,L) ∨ ¬on(b,L) ∨ ¬on(c,L) ∨
    # between(a,b,c) ∨ between(b,c,a) ∨ between(c,a,b)
    _clause(_pos(Equals("a", "b")), _pos(Equals("a", "c")),
            _pos(Equals("b", "c")),
            _neg(On("a", "L")), _neg(On("b", "L")), _neg(On("c", "L")),
            _pos(Between("a", "b", "c")),
            _pos(Between("b", "c", "a")),
            _pos(Between("c", "a", "b"))),

    # B7. between(a,b,c) ∧ between(a,b,d) → ¬between(b,c,d)
    #     (b,c,d on same side of b means b not between c,d)
    _clause(_neg(Between("a", "b", "c")), _neg(Between("a", "b", "d")),
            _neg(Between("b", "c", "d"))),
]

# ── Same-side axioms ──────────────────────────────────────────────────

SAME_SIDE_AXIOMS: List[Clause] = [
    # SS1. ¬on(a,L) → same-side(a,a,L)
    _clause(_pos(On("a", "L")), _pos(SameSide("a", "a", "L"))),

    # SS2. same-side(a,b,L) → same-side(b,a,L)
    _clause(_neg(SameSide("a", "b", "L")), _pos(SameSide("b", "a", "L"))),

    # SS3. same-side(a,b,L) → ¬on(a,L)
    _clause(_neg(SameSide("a", "b", "L")), _neg(On("a", "L"))),

    # SS4. same-side(a,b,L) ∧ same-side(a,c,L) → same-side(b,c,L)
    _clause(_neg(SameSide("a", "b", "L")), _neg(SameSide("a", "c", "L")),
            _pos(SameSide("b", "c", "L"))),

    # SS5. ¬on(a,L) ∧ ¬on(b,L) ∧ ¬on(c,L) ∧ ¬same-side(a,b,L) →
    #      same-side(a,c,L) ∨ same-side(b,c,L)
    _clause(_pos(On("a", "L")), _pos(On("b", "L")), _pos(On("c", "L")),
            _pos(SameSide("a", "b", "L")),
            _pos(SameSide("a", "c", "L")),
            _pos(SameSide("b", "c", "L"))),
]

# ── Pasch axioms ──────────────────────────────────────────────────────

PASCH_AXIOMS: List[Clause] = [
    # P1. between(a,b,c) ∧ same-side(a,c,L) → same-side(a,b,L)
    _clause(_neg(Between("a", "b", "c")), _neg(SameSide("a", "c", "L")),
            _pos(SameSide("a", "b", "L"))),

    # P2. between(a,b,c) ∧ on(a,L) ∧ ¬on(b,L) → same-side(b,c,L)
    _clause(_neg(Between("a", "b", "c")), _neg(On("a", "L")),
            _pos(On("b", "L")), _pos(SameSide("b", "c", "L"))),

    # P3. between(a,b,c) ∧ on(b,L) → ¬same-side(a,c,L)
    _clause(_neg(Between("a", "b", "c")), _neg(On("b", "L")),
            _neg(SameSide("a", "c", "L"))),

    # P4. L≠M ∧ on(b,L) ∧ on(b,M) ∧ on(a,M) ∧ on(c,M) ∧ a≠b ∧ c≠b
    #     ∧ ¬same-side(a,c,L) → between(a,b,c)
    _clause(_pos(Equals("L", "M")),
            _neg(On("b", "L")), _neg(On("b", "M")),
            _neg(On("a", "M")), _neg(On("c", "M")),
            _pos(Equals("a", "b")), _pos(Equals("c", "b")),
            _pos(SameSide("a", "c", "L")),
            _pos(Between("a", "b", "c"))),
]

# ── Triple-incidence axioms ───────────────────────────────────────────

TRIPLE_INCIDENCE_AXIOMS: List[Clause] = [
    # TI1. "L,M,N meet at a; b on L, c on M, d on N;
    #        same-side(c,d,L), same-side(b,c,N) → ¬same-side(b,d,M)"
    _clause(_neg(On("a", "L")), _neg(On("a", "M")), _neg(On("a", "N")),
            _neg(On("b", "L")), _neg(On("c", "M")), _neg(On("d", "N")),
            _neg(SameSide("c", "d", "L")), _neg(SameSide("b", "c", "N")),
            _neg(SameSide("b", "d", "M"))),

    # TI2. same hypotheses as TI1 but:
    #      same-side(c,d,L) ∧ ¬same-side(b,d,M) ∧ ¬on(d,M) ∧ b≠a
    #      → same-side(b,c,N)
    _clause(_neg(On("a", "L")), _neg(On("a", "M")), _neg(On("a", "N")),
            _neg(On("b", "L")), _neg(On("c", "M")), _neg(On("d", "N")),
            _neg(SameSide("c", "d", "L")),
            _pos(SameSide("b", "d", "M")),
            _pos(On("d", "M")), _pos(Equals("b", "a")),
            _pos(SameSide("b", "c", "N"))),

    # TI3. same hypotheses; same-side(c,d,L) ∧ same-side(b,c,N) ∧
    #      same-side(d,e,M) ∧ same-side(c,e,N) → same-side(c,e,L)
    _clause(_neg(On("a", "L")), _neg(On("a", "M")), _neg(On("a", "N")),
            _neg(On("b", "L")), _neg(On("c", "M")), _neg(On("d", "N")),
            _neg(SameSide("c", "d", "L")), _neg(SameSide("b", "c", "N")),
            _neg(SameSide("d", "e", "M")), _neg(SameSide("c", "e", "N")),
            _pos(SameSide("c", "e", "L"))),
]

# ── Circle axioms ─────────────────────────────────────────────────────

CIRCLE_AXIOMS: List[Clause] = [
    # C1. on(a,L) ∧ on(b,L) ∧ on(c,L) ∧ inside(a,α) ∧ on(b,α) ∧ on(c,α)
    #     ∧ b≠c → between(b,a,c)
    _clause(_neg(On("a", "L")), _neg(On("b", "L")), _neg(On("c", "L")),
            _neg(Inside("a", "\u03b1")),
            _neg(On("b", "\u03b1")), _neg(On("c", "\u03b1")),
            _pos(Equals("b", "c")),
            _pos(Between("b", "a", "c"))),

    # C2. (inside(a,α) ∨ on(a,α)) ∧ (inside(b,α) ∨ on(b,α))
    #     ∧ between(a,c,b) → inside(c,α)
    # Split into 4 clauses for each combination:
    # C2a: inside(a,α) ∧ inside(b,α) ∧ between(a,c,b) → inside(c,α)
    _clause(_neg(Inside("a", "\u03b1")), _neg(Inside("b", "\u03b1")),
            _neg(Between("a", "c", "b")), _pos(Inside("c", "\u03b1"))),
    # C2b: inside(a,α) ∧ on(b,α) ∧ between(a,c,b) → inside(c,α)
    _clause(_neg(Inside("a", "\u03b1")), _neg(On("b", "\u03b1")),
            _neg(Between("a", "c", "b")), _pos(Inside("c", "\u03b1"))),
    # C2c: on(a,α) ∧ inside(b,α) ∧ between(a,c,b) → inside(c,α)
    _clause(_neg(On("a", "\u03b1")), _neg(Inside("b", "\u03b1")),
            _neg(Between("a", "c", "b")), _pos(Inside("c", "\u03b1"))),
    # C2d: on(a,α) ∧ on(b,α) ∧ between(a,c,b) → inside(c,α)
    _clause(_neg(On("a", "\u03b1")), _neg(On("b", "\u03b1")),
            _neg(Between("a", "c", "b")), _pos(Inside("c", "\u03b1"))),

    # C3. (inside(a,α) ∨ on(a,α)) ∧ ¬inside(c,α) ∧ between(a,c,b)
    #     → ¬inside(b,α) ∧ ¬on(b,α)
    # Split for disjunctive hyp and conjunctive conclusion:
    # C3a: inside(a,α) ∧ ¬inside(c,α) ∧ between(a,c,b) → ¬inside(b,α)
    _clause(_neg(Inside("a", "\u03b1")), _pos(Inside("c", "\u03b1")),
            _neg(Between("a", "c", "b")), _neg(Inside("b", "\u03b1"))),
    # C3b: inside(a,α) ∧ ¬inside(c,α) ∧ between(a,c,b) → ¬on(b,α)
    _clause(_neg(Inside("a", "\u03b1")), _pos(Inside("c", "\u03b1")),
            _neg(Between("a", "c", "b")), _neg(On("b", "\u03b1"))),
    # C3c: on(a,α) ∧ ¬inside(c,α) ∧ between(a,c,b) → ¬inside(b,α)
    _clause(_neg(On("a", "\u03b1")), _pos(Inside("c", "\u03b1")),
            _neg(Between("a", "c", "b")), _neg(Inside("b", "\u03b1"))),
    # C3d: on(a,α) ∧ ¬inside(c,α) ∧ between(a,c,b) → ¬on(b,α)
    _clause(_neg(On("a", "\u03b1")), _pos(Inside("c", "\u03b1")),
            _neg(Between("a", "c", "b")), _neg(On("b", "\u03b1"))),

    # C4. α≠β ∧ intersects(α,β) ∧ on(c,α) ∧ on(c,β) ∧ on(d,α) ∧ on(d,β)
    #     ∧ c≠d ∧ center(a,α) ∧ center(b,β) ∧ on(a,L) ∧ on(b,L)
    #     → ¬same-side(c,d,L)
    _clause(_pos(Equals("\u03b1", "\u03b2")),
            _neg(Intersects("\u03b1", "\u03b2")),
            _neg(On("c", "\u03b1")), _neg(On("c", "\u03b2")),
            _neg(On("d", "\u03b1")), _neg(On("d", "\u03b2")),
            _pos(Equals("c", "d")),
            _neg(Center("a", "\u03b1")), _neg(Center("b", "\u03b2")),
            _neg(On("a", "L")), _neg(On("b", "L")),
            _neg(SameSide("c", "d", "L"))),
]

# ── Intersection axioms ───────────────────────────────────────────────

INTERSECTION_AXIOMS: List[Clause] = [
    # I1. ¬on(a,L) ∧ ¬on(b,L) ∧ ¬same-side(a,b,L) ∧ on(a,M) ∧ on(b,M)
    #     → intersects(L,M)
    # diff-side(a,b,L) means ¬on(a,L), ¬on(b,L), ¬same-side(a,b,L)
    _clause(_pos(On("a", "L")), _pos(On("b", "L")),
            _pos(SameSide("a", "b", "L")),
            _neg(On("a", "M")), _neg(On("b", "M")),
            _pos(Intersects("L", "M"))),

    # I2. (on(a,α)∨inside(a,α)) ∧ (on(b,α)∨inside(b,α))
    #     ∧ diff-side(a,b,L) → intersects(L,α)
    # Split for the disjunctive hypotheses (4 variants):
    _clause(_neg(On("a", "\u03b1")), _neg(On("b", "\u03b1")),
            _pos(On("a", "L")), _pos(On("b", "L")),
            _pos(SameSide("a", "b", "L")),
            _pos(Intersects("L", "\u03b1"))),
    _clause(_neg(On("a", "\u03b1")), _neg(Inside("b", "\u03b1")),
            _pos(On("a", "L")), _pos(On("b", "L")),
            _pos(SameSide("a", "b", "L")),
            _pos(Intersects("L", "\u03b1"))),
    _clause(_neg(Inside("a", "\u03b1")), _neg(On("b", "\u03b1")),
            _pos(On("a", "L")), _pos(On("b", "L")),
            _pos(SameSide("a", "b", "L")),
            _pos(Intersects("L", "\u03b1"))),
    _clause(_neg(Inside("a", "\u03b1")), _neg(Inside("b", "\u03b1")),
            _pos(On("a", "L")), _pos(On("b", "L")),
            _pos(SameSide("a", "b", "L")),
            _pos(Intersects("L", "\u03b1"))),

    # I3. inside(a,α) ∧ on(a,L) → intersects(L,α)
    _clause(_neg(Inside("a", "\u03b1")), _neg(On("a", "L")),
            _pos(Intersects("L", "\u03b1"))),

    # I4. on(a,α) ∧ (on(b,α)∨inside(b,α)) ∧ inside(a,β)
    #     ∧ ¬inside(b,β) ∧ ¬on(b,β) → intersects(α,β)
    _clause(_neg(On("a", "\u03b1")), _neg(On("b", "\u03b1")),
            _neg(Inside("a", "\u03b2")),
            _pos(Inside("b", "\u03b2")), _pos(On("b", "\u03b2")),
            _pos(Intersects("\u03b1", "\u03b2"))),
    _clause(_neg(On("a", "\u03b1")), _neg(Inside("b", "\u03b1")),
            _neg(Inside("a", "\u03b2")),
            _pos(Inside("b", "\u03b2")), _pos(On("b", "\u03b2")),
            _pos(Intersects("\u03b1", "\u03b2"))),

    # I5. on(a,α) ∧ inside(b,α) ∧ inside(a,β) ∧ on(b,β) → intersects(α,β)
    _clause(_neg(On("a", "\u03b1")), _neg(Inside("b", "\u03b1")),
            _neg(Inside("a", "\u03b2")), _neg(On("b", "\u03b2")),
            _pos(Intersects("\u03b1", "\u03b2"))),
]

# ── Equality axioms (handled specially, but included for completeness) ─

# E1. x = x  (reflexivity — built into the consequence engine)
# E2. x = y ∧ φ(x) → φ(y)  (substitution — built into the engine)
# These are not stored as clauses but handled by the engine directly.


# ═══════════════════════════════════════════════════════════════════════
# Section 3.5: Metric axioms
# ═══════════════════════════════════════════════════════════════════════

# The metric axioms describe ordered abelian group properties for each
# magnitude sort (segment, angle, area).  They are handled by a
# dedicated metric inference engine, not by clause-based reasoning.
# See e_metric.py for the implementation.
#
# However, we record the additional axioms from Section 3.5 here:
#
# M1. ab = 0 ↔ a = b
# M2. ab ≥ 0
# M3. ab = ba
# M4. a ≠ b ∧ a ≠ c → ∠abc = ∠cba
# M5. 0 ≰ ∠abc  ∧  ∠abc ≤ right-angle + right-angle
# M6. △aab = 0
# M7. △abc ≥ 0
# M8. △abc = △cab  ∧  △abc = △acb
# M9. (full congruence → equal areas)


# ═══════════════════════════════════════════════════════════════════════
# Section 3.6: Transfer axioms
# ═══════════════════════════════════════════════════════════════════════

# These connect diagrammatic and metric assertions.  They're stored as
# clauses for the transfer inference engine.

DIAGRAM_SEGMENT_TRANSFER: List[Clause] = [
    # DS1. between(a,b,c) → ab + bc = ac
    # This is a transfer axiom, not a pure diagram axiom.
    # Stored separately for the transfer engine.
    _clause(_neg(Between("a", "b", "c")),
            _pos(Equals(MagAdd(SegmentTerm("a", "b"),
                               SegmentTerm("b", "c")),
                        SegmentTerm("a", "c")))),

    # DS2. center(a,α) ∧ center(a,β) ∧ on(b,α) ∧ on(c,β) ∧ ab=ac → α=β
    _clause(_neg(Center("a", "\u03b1")), _neg(Center("a", "\u03b2")),
            _neg(On("b", "\u03b1")), _neg(On("c", "\u03b2")),
            _neg(Equals(SegmentTerm("a", "b"), SegmentTerm("a", "c"))),
            _pos(Equals("\u03b1", "\u03b2"))),

    # DS3. center(a,α) ∧ on(b,α) → (ac = ab ↔ on(c,α))
    # As two clauses:
    # DS3a: center(a,α) ∧ on(b,α) ∧ ac=ab → on(c,α)
    _clause(_neg(Center("a", "\u03b1")), _neg(On("b", "\u03b1")),
            _neg(Equals(SegmentTerm("a", "c"), SegmentTerm("a", "b"))),
            _pos(On("c", "\u03b1"))),
    # DS3b: center(a,α) ∧ on(b,α) ∧ on(c,α) → ac=ab
    _clause(_neg(Center("a", "\u03b1")), _neg(On("b", "\u03b1")),
            _neg(On("c", "\u03b1")),
            _pos(Equals(SegmentTerm("a", "c"), SegmentTerm("a", "b")))),

    # DS4. center(a,α) ∧ on(b,α) → (ac < ab ↔ inside(c,α))
    # As two clauses:
    # DS4a: center(a,α) ∧ on(b,α) ∧ ac < ab → inside(c,α)
    _clause(_neg(Center("a", "\u03b1")), _neg(On("b", "\u03b1")),
            _neg(LessThan(SegmentTerm("a", "c"), SegmentTerm("a", "b"))),
            _pos(Inside("c", "\u03b1"))),
    # DS4b: center(a,α) ∧ on(b,α) ∧ inside(c,α) → ac < ab
    _clause(_neg(Center("a", "\u03b1")), _neg(On("b", "\u03b1")),
            _neg(Inside("c", "\u03b1")),
            _pos(LessThan(SegmentTerm("a", "c"), SegmentTerm("a", "b")))),

    # DS3/DS4 negative directions (contrapositives of biconditionals):
    # When a point is strictly farther from the center than the radius,
    # it is neither inside nor on the circle.
    # DS4c: center(a,α) ∧ on(b,α) ∧ ab < ac → ¬inside(c,α)
    _clause(_neg(Center("a", "\u03b1")), _neg(On("b", "\u03b1")),
            _neg(LessThan(SegmentTerm("a", "b"), SegmentTerm("a", "c"))),
            _neg(Inside("c", "\u03b1"))),
    # DS4d: center(a,α) ∧ on(b,α) ∧ ab < ac → ¬on(c,α)
    _clause(_neg(Center("a", "\u03b1")), _neg(On("b", "\u03b1")),
            _neg(LessThan(SegmentTerm("a", "b"), SegmentTerm("a", "c"))),
            _neg(On("c", "\u03b1"))),
]

DIAGRAM_ANGLE_TRANSFER: List[Clause] = [
    # DA1. a≠b ∧ a≠c ∧ on(a,L) ∧ on(b,L) →
    #      (on(c,L) ∧ ¬between(b,a,c) ↔ ∠bac = 0)
    # DA1a (forward): a≠b, a≠c, on(a,L), on(b,L), on(c,L),
    #       ¬between(b,a,c) → ∠bac = 0
    _clause(_pos(Equals("a", "b")), _pos(Equals("a", "c")),
            _neg(On("a", "L")), _neg(On("b", "L")),
            _neg(On("c", "L")),
            _pos(Between("b", "a", "c")),
            _pos(Equals(AngleTerm("b", "a", "c"),
                        ZeroMag(Sort.ANGLE)))),
    # DA1b (backward, on(c,L)): a≠b, a≠c, on(a,L), on(b,L),
    #       ∠bac = 0 → on(c,L)
    _clause(_pos(Equals("a", "b")), _pos(Equals("a", "c")),
            _neg(On("a", "L")), _neg(On("b", "L")),
            _neg(Equals(AngleTerm("b", "a", "c"),
                        ZeroMag(Sort.ANGLE))),
            _pos(On("c", "L"))),
    # DA1c (backward, ¬between): a≠b, a≠c, on(a,L), on(b,L),
    #       ∠bac = 0 → ¬between(b,a,c)
    _clause(_pos(Equals("a", "b")), _pos(Equals("a", "c")),
            _neg(On("a", "L")), _neg(On("b", "L")),
            _neg(Equals(AngleTerm("b", "a", "c"),
                        ZeroMag(Sort.ANGLE))),
            _neg(Between("b", "a", "c"))),

    # DA2. a on L∧M, b on L, c on M, a≠b, a≠c, d not on L or M, L≠M →
    #      (∠bac = ∠bad + ∠dac ↔ same-side(b,d,M) ∧ same-side(c,d,L))
    # DA2a (forward): ..., same-side(b,d,M), same-side(c,d,L) →
    #       ∠bac = ∠bad + ∠dac
    _clause(_neg(On("a", "L")), _neg(On("a", "M")),
            _neg(On("b", "L")), _neg(On("c", "M")),
            _pos(Equals("a", "b")), _pos(Equals("a", "c")),
            _pos(On("d", "L")), _pos(On("d", "M")),
            _pos(Equals("L", "M")),
            _neg(SameSide("b", "d", "M")), _neg(SameSide("c", "d", "L")),
            _pos(Equals(AngleTerm("b", "a", "c"),
                        MagAdd(AngleTerm("b", "a", "d"),
                               AngleTerm("d", "a", "c"))))),
    # DA2b (backward, same-side(b,d,M)): ..., ∠bac = ∠bad + ∠dac,
    #       same-side(c,d,L) → same-side(b,d,M)
    _clause(_neg(On("a", "L")), _neg(On("a", "M")),
            _neg(On("b", "L")), _neg(On("c", "M")),
            _pos(Equals("a", "b")), _pos(Equals("a", "c")),
            _pos(On("d", "L")), _pos(On("d", "M")),
            _pos(Equals("L", "M")),
            _neg(Equals(AngleTerm("b", "a", "c"),
                        MagAdd(AngleTerm("b", "a", "d"),
                               AngleTerm("d", "a", "c")))),
            _neg(SameSide("c", "d", "L")),
            _pos(SameSide("b", "d", "M"))),
    # DA2c (backward, same-side(c,d,L)): ..., ∠bac = ∠bad + ∠dac,
    #       same-side(b,d,M) → same-side(c,d,L)
    _clause(_neg(On("a", "L")), _neg(On("a", "M")),
            _neg(On("b", "L")), _neg(On("c", "M")),
            _pos(Equals("a", "b")), _pos(Equals("a", "c")),
            _pos(On("d", "L")), _pos(On("d", "M")),
            _pos(Equals("L", "M")),
            _neg(Equals(AngleTerm("b", "a", "c"),
                        MagAdd(AngleTerm("b", "a", "d"),
                               AngleTerm("d", "a", "c")))),
            _neg(SameSide("b", "d", "M")),
            _pos(SameSide("c", "d", "L"))),

    # DA3. on(a,L) ∧ on(b,L) ∧ between(a,c,b) ∧ ¬on(d,L)
    #      → (∠acd = ∠dcb ↔ ∠acd = right-angle)
    # DA3a: ... ∧ ∠acd = ∠dcb → ∠acd = right-angle
    _clause(_neg(On("a", "L")), _neg(On("b", "L")),
            _neg(Between("a", "c", "b")), _pos(On("d", "L")),
            _neg(Equals(AngleTerm("a", "c", "d"),
                        AngleTerm("d", "c", "b"))),
            _pos(Equals(AngleTerm("a", "c", "d"), RightAngle()))),
    # DA3b: ... ∧ ∠acd = right-angle → ∠acd = ∠dcb
    _clause(_neg(On("a", "L")), _neg(On("b", "L")),
            _neg(Between("a", "c", "b")), _pos(On("d", "L")),
            _neg(Equals(AngleTerm("a", "c", "d"), RightAngle())),
            _pos(Equals(AngleTerm("a", "c", "d"),
                        AngleTerm("d", "c", "b")))),

    # DA4. on(a,L), on(b,L), on(b',L), on(a,M), on(c,M), on(c',M),
    #      b≠a, b'≠a, c≠a, c'≠a, ¬between(b,a,b'), ¬between(c,a,c')
    #      → ∠bac = ∠b'ac'
    _clause(_neg(On("a", "L")), _neg(On("b", "L")),
            _neg(On("bp", "L")),
            _neg(On("a", "M")), _neg(On("c", "M")),
            _neg(On("cp", "M")),
            _pos(Equals("b", "a")), _pos(Equals("bp", "a")),
            _pos(Equals("c", "a")), _pos(Equals("cp", "a")),
            _pos(Between("b", "a", "bp")),
            _pos(Between("c", "a", "cp")),
            _pos(Equals(AngleTerm("b", "a", "c"),
                        AngleTerm("bp", "a", "cp")))),

    # DA5. Parallel Postulate (Euclid's Postulate 5 / Axiom 5 of Section 3.6)
    #      on(a,L) ∧ on(b,L) ∧ on(b,M) ∧ on(c,M) ∧ on(c,N) ∧ on(d,N) ∧
    #      b≠c ∧ same-side(a,d,N) ∧
    #      ∠abc + ∠bcd < right-angle + right-angle →
    #      intersects(L,N)
    # DA5a: the lines intersect
    _clause(_neg(On("a", "L")), _neg(On("b", "L")),
            _neg(On("b", "M")), _neg(On("c", "M")),
            _neg(On("c", "N")), _neg(On("d", "N")),
            _pos(Equals("b", "c")),
            _neg(SameSide("a", "d", "N")),
            _neg(LessThan(
                MagAdd(AngleTerm("a", "b", "c"),
                       AngleTerm("b", "c", "d")),
                MagAdd(RightAngle(), RightAngle()))),
            _pos(Intersects("L", "N"))),
    # DA5b: the intersection point e is on the same side of M as a
    #       (this is applied when e is known to be on L and N)
    #       on(e,L) ∧ on(e,N) ∧ ... → same-side(e,a,M)
    _clause(_neg(On("a", "L")), _neg(On("b", "L")),
            _neg(On("b", "M")), _neg(On("c", "M")),
            _neg(On("c", "N")), _neg(On("d", "N")),
            _pos(Equals("b", "c")),
            _neg(SameSide("a", "d", "N")),
            _neg(LessThan(
                MagAdd(AngleTerm("a", "b", "c"),
                       AngleTerm("b", "c", "d")),
                MagAdd(RightAngle(), RightAngle()))),
            _neg(On("e", "L")), _neg(On("e", "N")),
            _pos(SameSide("e", "a", "M"))),
]

DIAGRAM_AREA_TRANSFER: List[Clause] = [
    # DAr1. on(a,L) ∧ on(b,L) ∧ a≠b → (△abc = 0 ↔ on(c,L))
    # DAr1a: ... ∧ △abc = 0 → on(c,L)
    _clause(_neg(On("a", "L")), _neg(On("b", "L")),
            _pos(Equals("a", "b")),
            _neg(Equals(AreaTerm("a", "b", "c"), ZeroMag(Sort.AREA))),
            _pos(On("c", "L"))),
    # DAr1b: ... ∧ on(c,L) → △abc = 0
    _clause(_neg(On("a", "L")), _neg(On("b", "L")),
            _pos(Equals("a", "b")),
            _neg(On("c", "L")),
            _pos(Equals(AreaTerm("a", "b", "c"), ZeroMag(Sort.AREA)))),
    # DAr1c (contrapositive of DAr1b): ... ∧ ¬on(c,L) → ¬(△abc = 0)
    _clause(_neg(On("a", "L")), _neg(On("b", "L")),
            _pos(Equals("a", "b")),
            _pos(On("c", "L")),
            _neg(Equals(AreaTerm("a", "b", "c"), ZeroMag(Sort.AREA)))),

    # DAr2. on(a,L) ∧ on(b,L) ∧ on(c,L) ∧ distinct(a,b,c) ∧ ¬on(d,L)
    #       → (between(a,c,b) ↔ △acd + △dcb = △adb)
    # DAr2a: ... ∧ between(a,c,b) → △acd + △dcb = △adb
    _clause(_neg(On("a", "L")), _neg(On("b", "L")), _neg(On("c", "L")),
            _pos(Equals("a", "b")), _pos(Equals("a", "c")),
            _pos(Equals("b", "c")),
            _pos(On("d", "L")),
            _neg(Between("a", "c", "b")),
            _pos(Equals(MagAdd(AreaTerm("a", "c", "d"),
                               AreaTerm("d", "c", "b")),
                        AreaTerm("a", "d", "b")))),
]


# ═══════════════════════════════════════════════════════════════════════
# Collected axiom sets
# ═══════════════════════════════════════════════════════════════════════

ALL_DIAGRAMMATIC_AXIOMS: List[Clause] = (
    GENERALITY_AXIOMS
    + BETWEEN_AXIOMS
    + SAME_SIDE_AXIOMS
    + PASCH_AXIOMS
    + TRIPLE_INCIDENCE_AXIOMS
    + CIRCLE_AXIOMS
    + INTERSECTION_AXIOMS
)

ALL_TRANSFER_AXIOMS: List[Clause] = (
    DIAGRAM_SEGMENT_TRANSFER
    + DIAGRAM_ANGLE_TRANSFER
    + DIAGRAM_AREA_TRANSFER
)

ALL_AXIOMS: List[Clause] = ALL_DIAGRAMMATIC_AXIOMS + ALL_TRANSFER_AXIOMS
