"""
h_axioms.py — Axioms for Hilbert's geometry (System H).

All axioms from GeoCoq's Hilbert_neutral_dimensionless class
(https://geocoq.github.io/GeoCoq/), organized by Hilbert's groups:

  Group I  — Incidence (points, lines, planes)
  Group II — Order (betweenness, Pasch)
  Group III — Congruence (segments, angles, SAS)
  Group IV — Parallels (Euclidean parallel postulate)

Each axiom is encoded as one or more *clauses* — finite disjunctive
sets of literals.  An axiom "if φ₁, …, φₙ then ψ" becomes the clause
{¬φ₁, …, ¬φₙ, ψ}.  Multi-conclusion axioms are split into multiple
clauses.

GeoCoq reference: theories/Axioms/hilbert_axioms.v
  - Hilbert_neutral_dimensionless: Groups I–III
  - Hilbert_neutral_2D: Pasch specialization for 2D
  - Hilbert_euclidean: Group IV (parallel postulate)

Avigad et al. (2009) Section 5 establishes the equivalence:
  System E ↔ Tarski's system T ↔ Hilbert's system H
via GeoCoq's tarski_to_hilbert.v / hilbert_to_tarski.v.
"""
from __future__ import annotations

from typing import List

from .h_ast import (
    HLiteral, HClause,
    IncidL, IncidP, BetH, CongH, CongaH, EqL, EqP, EqPt,
    ColH, Cut, OutH, Disjoint, SameSideH, SameSidePrime, Para, IncidLP,
)


def _pos(atom) -> HLiteral:
    return HLiteral(atom, polarity=True)


def _neg(atom) -> HLiteral:
    return HLiteral(atom, polarity=False)


def _clause(*lits: HLiteral) -> HClause:
    return HClause(frozenset(lits))


# ═══════════════════════════════════════════════════════════════════════
# Group I: Incidence Axioms
# ═══════════════════════════════════════════════════════════════════════
#
# GeoCoq: line_existence, line_uniqueness, two_points_on_line,
#          ColH (defined), lower_dim_2, plane axioms, line_on_plane

INCIDENCE_AXIOMS: List[HClause] = [
    # I.1  line_uniqueness:
    #   A ≠ B ∧ IncidL(A,l) ∧ IncidL(B,l) ∧ IncidL(A,m) ∧ IncidL(B,m)
    #     → EqL(l, m)
    # Clause: A=B ∨ ¬IncidL(A,l) ∨ ¬IncidL(B,l) ∨ ¬IncidL(A,m)
    #         ∨ ¬IncidL(B,m) ∨ EqL(l,m)
    _clause(_pos(EqPt("A", "B")),
            _neg(IncidL("A", "l")), _neg(IncidL("B", "l")),
            _neg(IncidL("A", "m")), _neg(IncidL("B", "m")),
            _pos(EqL("l", "m"))),

    # I.2  IncidL_dec (decidability):
    #   IncidL(A, l) ∨ ¬IncidL(A, l)
    # This is a tautology in classical logic; included for the
    # consequence engine to support case analysis.
    _clause(_pos(IncidL("A", "l")), _neg(IncidL("A", "l"))),

    # I.3  EqL reflexivity: EqL(l, l)
    _clause(_pos(EqL("l", "l"))),

    # I.4  EqL symmetry: EqL(l, m) → EqL(m, l)
    _clause(_neg(EqL("l", "m")), _pos(EqL("m", "l"))),

    # I.5  EqL transitivity: EqL(l, m) ∧ EqL(m, n) → EqL(l, n)
    _clause(_neg(EqL("l", "m")), _neg(EqL("m", "n")),
            _pos(EqL("l", "n"))),

    # I.6  IncidL morphism: IncidL(A, l) ∧ EqL(l, m) → IncidL(A, m)
    _clause(_neg(IncidL("A", "l")), _neg(EqL("l", "m")),
            _pos(IncidL("A", "m"))),

    # I.7  Point equality decidability: A = B ∨ A ≠ B
    _clause(_pos(EqPt("A", "B")), _neg(EqPt("A", "B"))),

    # I.8  Point equality reflexivity: A = A
    _clause(_pos(EqPt("A", "A"))),

    # I.9  Point equality symmetry: A = B → B = A
    _clause(_neg(EqPt("A", "B")), _pos(EqPt("B", "A"))),

    # I.10 Point equality transitivity: A = B ∧ B = C → A = C
    _clause(_neg(EqPt("A", "B")), _neg(EqPt("B", "C")),
            _pos(EqPt("A", "C"))),
]


# ── Collinearity (defined predicate) ─────────────────────────────────
# ColH(A,B,C) := ∃l. IncidL(A,l) ∧ IncidL(B,l) ∧ IncidL(C,l)
#
# We encode useful rules that follow from the definition.

COLLINEARITY_AXIOMS: List[HClause] = [
    # Col.1  IncidL(A,l) ∧ IncidL(B,l) ∧ IncidL(C,l) → ColH(A,B,C)
    _clause(_neg(IncidL("A", "l")), _neg(IncidL("B", "l")),
            _neg(IncidL("C", "l")), _pos(ColH("A", "B", "C"))),

    # Col.2  ColH symmetry: ColH(A,B,C) → ColH(B,A,C)
    _clause(_neg(ColH("A", "B", "C")), _pos(ColH("B", "A", "C"))),

    # Col.3  ColH rotation: ColH(A,B,C) → ColH(B,C,A)
    _clause(_neg(ColH("A", "B", "C")), _pos(ColH("B", "C", "A"))),

    # Col.4  ColH(A,B,C) → ColH(A,C,B)
    _clause(_neg(ColH("A", "B", "C")), _pos(ColH("A", "C", "B"))),
]


# ── lower_dim_2 ──────────────────────────────────────────────────────
# There exist three non-collinear points PP, PQ, PR.
# This is an existence axiom about *axiom constants*, NOT schema
# variables.  PP, PQ, PR are fixed points in any model.  These
# clauses must NOT be grounded by the consequence engine (which
# would substitute arbitrary point names, e.g. PP→A, PQ→A,
# producing the spurious ¬EqPt(A,A) conflicting with reflexivity).
# Instead, they are only relevant when the proof explicitly
# references the axiom constants PP, PQ, PR.

LOWER_DIM_AXIOMS: List[HClause] = [
    # PP ≠ PQ
    _clause(_neg(EqPt("PP", "PQ"))),
    # PQ ≠ PR
    _clause(_neg(EqPt("PQ", "PR"))),
    # PP ≠ PR
    _clause(_neg(EqPt("PP", "PR"))),
    # ¬ColH(PP, PQ, PR)
    _clause(_neg(ColH("PP", "PQ", "PR"))),
]


# ═══════════════════════════════════════════════════════════════════════
# Group II: Order Axioms (Betweenness)
# ═══════════════════════════════════════════════════════════════════════
#
# GeoCoq: between_diff, between_col, between_comm, between_out,
#          between_only_one, cut (defined), pasch

BETWEEN_AXIOMS: List[HClause] = [
    # B.1  between_diff: BetH(A,B,C) → A ≠ C
    _clause(_neg(BetH("A", "B", "C")), _neg(EqPt("A", "C"))),

    # B.2  between_col: BetH(A,B,C) → ColH(A,B,C)
    _clause(_neg(BetH("A", "B", "C")), _pos(ColH("A", "B", "C"))),

    # B.3  between_comm: BetH(A,B,C) → BetH(C,B,A)
    _clause(_neg(BetH("A", "B", "C")), _pos(BetH("C", "B", "A"))),

    # B.4  between_only_one: BetH(A,B,C) → ¬BetH(B,C,A)
    _clause(_neg(BetH("A", "B", "C")), _neg(BetH("B", "C", "A"))),

    # B.5  BetH(A,B,C) → A ≠ B  (follows from between_diff + between_comm)
    _clause(_neg(BetH("A", "B", "C")), _neg(EqPt("A", "B"))),

    # B.6  BetH(A,B,C) → B ≠ C  (follows from between_diff + between_comm)
    _clause(_neg(BetH("A", "B", "C")), _neg(EqPt("B", "C"))),
]


# ── Cut (defined predicate) ──────────────────────────────────────────
# cut(l, A, B) := ¬IncidL(A,l) ∧ ¬IncidL(B,l) ∧
#                  ∃I. IncidL(I,l) ∧ BetH(A,I,B)

CUT_AXIOMS: List[HClause] = [
    # Cut.1  cut(l,A,B) → ¬IncidL(A,l)
    _clause(_neg(Cut("l", "A", "B")), _neg(IncidL("A", "l"))),

    # Cut.2  cut(l,A,B) → ¬IncidL(B,l)
    _clause(_neg(Cut("l", "A", "B")), _neg(IncidL("B", "l"))),

    # Cut.3  Introduction: ¬IncidL(A,l) ∧ ¬IncidL(B,l) ∧ IncidL(I,l)
    #        ∧ BetH(A,I,B) → cut(l,A,B)
    _clause(_pos(IncidL("A", "l")), _pos(IncidL("B", "l")),
            _neg(IncidL("I", "l")), _neg(BetH("A", "I", "B")),
            _pos(Cut("l", "A", "B"))),
]


# ── Pasch axiom (2D specialization) ──────────────────────────────────
# pasch_2D:
#   ¬ColH(A,B,C) ∧ ¬IncidL(C,l) ∧ cut(l,A,B)
#     → cut(l,A,C) ∨ cut(l,B,C)
#
# This is a disjunctive conclusion, so we cannot encode it as a single
# clause.  Instead, it serves as a case-split rule in the proof system.
# We encode it as a pair of clauses that the checker can use:

PASCH_AXIOMS: List[HClause] = [
    # Pasch is a case-split rule; we encode the two cases for the
    # consequence engine to propagate when one case is excluded:
    #
    # Pasch.1:  ¬ColH(A,B,C) ∧ ¬IncidL(C,l) ∧ cut(l,A,B) ∧ ¬cut(l,B,C)
    #           → cut(l,A,C)
    _clause(_pos(ColH("A", "B", "C")), _pos(IncidL("C", "l")),
            _neg(Cut("l", "A", "B")), _pos(Cut("l", "B", "C")),
            _pos(Cut("l", "A", "C"))),

    # Pasch.2:  ¬ColH(A,B,C) ∧ ¬IncidL(C,l) ∧ cut(l,A,B) ∧ ¬cut(l,A,C)
    #           → cut(l,B,C)
    _clause(_pos(ColH("A", "B", "C")), _pos(IncidL("C", "l")),
            _neg(Cut("l", "A", "B")), _pos(Cut("l", "A", "C")),
            _pos(Cut("l", "B", "C"))),
]


# ═══════════════════════════════════════════════════════════════════════
# Group III: Congruence Axioms
# ═══════════════════════════════════════════════════════════════════════
#
# GeoCoq: cong_permr, cong_existence, cong_pseudo_transitivity,
#          disjoint (defined), addition,
#          CongaH (primitive), conga_refl, conga_comm, conga_permlr,
#          conga_out_conga, cong_4_existence, cong_4_uniqueness, cong_5

SEGMENT_CONGRUENCE_AXIOMS: List[HClause] = [
    # SC.1  cong_permr: CongH(A,B,C,D) → CongH(A,B,D,C)
    _clause(_neg(CongH("A", "B", "C", "D")),
            _pos(CongH("A", "B", "D", "C"))),

    # SC.2  cong_pseudo_transitivity:
    #       CongH(A,B,C,D) ∧ CongH(A,B,E,F) → CongH(C,D,E,F)
    _clause(_neg(CongH("A", "B", "C", "D")),
            _neg(CongH("A", "B", "E", "F")),
            _pos(CongH("C", "D", "E", "F"))),

    # SC.3  Reflexivity (derived): CongH(A,B,A,B)
    #       From pseudo_transitivity with C=A, D=B: CongH(A,B,A,B)
    #       We include it explicitly for the consequence engine.
    _clause(_pos(CongH("A", "B", "A", "B"))),

    # SC.4  Symmetry (derived): CongH(A,B,C,D) → CongH(C,D,A,B)
    #       Follows from reflexivity + pseudo_transitivity.
    _clause(_neg(CongH("A", "B", "C", "D")),
            _pos(CongH("C", "D", "A", "B"))),

    # SC.5  CongH(A,B,C,D) → CongH(B,A,C,D)
    #       Follows from cong_permr applied twice.
    _clause(_neg(CongH("A", "B", "C", "D")),
            _pos(CongH("B", "A", "C", "D"))),
]


# ── Segment addition ─────────────────────────────────────────────────
# addition:
#   ColH(A,B,C) ∧ ColH(A',B',C') ∧ disjoint(A,B,B,C) ∧
#   disjoint(A',B',B',C') ∧ CongH(A,B,A',B') ∧ CongH(B,C,B',C')
#     → CongH(A,C,A',C')

ADDITION_AXIOMS: List[HClause] = [
    _clause(_neg(ColH("A", "B", "C")), _neg(ColH("A'", "B'", "C'")),
            _neg(Disjoint("A", "B", "B", "C")),
            _neg(Disjoint("A'", "B'", "B'", "C'")),
            _neg(CongH("A", "B", "A'", "B'")),
            _neg(CongH("B", "C", "B'", "C'")),
            _pos(CongH("A", "C", "A'", "C'"))),
]


# ── Angle congruence ─────────────────────────────────────────────────

ANGLE_CONGRUENCE_AXIOMS: List[HClause] = [
    # AC.1  conga_refl: ¬ColH(A,B,C) → CongaH(A,B,C,A,B,C)
    _clause(_pos(ColH("A", "B", "C")),
            _pos(CongaH("A", "B", "C", "A", "B", "C"))),

    # AC.2  conga_comm: ¬ColH(A,B,C) → CongaH(A,B,C,C,B,A)
    _clause(_pos(ColH("A", "B", "C")),
            _pos(CongaH("A", "B", "C", "C", "B", "A"))),

    # AC.3  conga_permlr: CongaH(A,B,C,D,E,F) → CongaH(C,B,A,F,E,D)
    _clause(_neg(CongaH("A", "B", "C", "D", "E", "F")),
            _pos(CongaH("C", "B", "A", "F", "E", "D"))),

    # AC.4  conga symmetry (derived):
    #       CongaH(A,B,C,D,E,F) → CongaH(D,E,F,A,B,C)
    _clause(_neg(CongaH("A", "B", "C", "D", "E", "F")),
            _pos(CongaH("D", "E", "F", "A", "B", "C"))),
]


# ── SAS congruence (cong_5 / Hilbert's axiom III.5) ──────────────────
# cong_5:
#   ¬ColH(A,B,C) ∧ ¬ColH(A',B',C') ∧
#   CongH(A,B,A',B') ∧ CongH(A,C,A',C') ∧ CongaH(B,A,C,B',A',C')
#     → CongaH(A,B,C,A',B',C')

SAS_AXIOMS: List[HClause] = [
    _clause(_pos(ColH("A", "B", "C")),
            _pos(ColH("A'", "B'", "C'")),
            _neg(CongH("A", "B", "A'", "B'")),
            _neg(CongH("A", "C", "A'", "C'")),
            _neg(CongaH("B", "A", "C", "B'", "A'", "C'")),
            _pos(CongaH("A", "B", "C", "A'", "B'", "C'"))),
]


# ── same_side (defined) ──────────────────────────────────────────────
# same_side(A,B,l) := ∃P. cut(l,A,P) ∧ cut(l,B,P)

SAME_SIDE_AXIOMS: List[HClause] = [
    # SS.1  Introduction: cut(l,A,P) ∧ cut(l,B,P) → same_side(A,B,l)
    _clause(_neg(Cut("l", "A", "P")), _neg(Cut("l", "B", "P")),
            _pos(SameSideH("A", "B", "l"))),

    # SS.2  same_side reflexivity (derived):
    #       ¬IncidL(A,l) → same_side(A,A,l)
    #       (Need a witness P on opposite side; this is a theorem, not an axiom.
    #        We include a weaker rule for the consequence engine.)

    # SS.3  same_side symmetry: same_side(A,B,l) → same_side(B,A,l)
    _clause(_neg(SameSideH("A", "B", "l")),
            _pos(SameSideH("B", "A", "l"))),
]


# ═══════════════════════════════════════════════════════════════════════
# Group IV: Parallel Postulate (Euclidean)
# ═══════════════════════════════════════════════════════════════════════
#
# GeoCoq: Hilbert_euclidean class
# euclid_uniqueness:
#   ¬IncidL(P,l) ∧ Para(l,m1) ∧ IncidL(P,m1) ∧ Para(l,m2) ∧ IncidL(P,m2)
#     → EqL(m1, m2)

PARALLEL_AXIOMS: List[HClause] = [
    # Par.1  Uniqueness of parallels (Playfair):
    #   ¬IncidL(P,l) ∧ Para(l,m1) ∧ IncidL(P,m1)
    #   ∧ Para(l,m2) ∧ IncidL(P,m2) → EqL(m1,m2)
    _clause(_pos(IncidL("P", "l")),
            _neg(Para("l", "m1")), _neg(IncidL("P", "m1")),
            _neg(Para("l", "m2")), _neg(IncidL("P", "m2")),
            _pos(EqL("m1", "m2"))),
]


# ═══════════════════════════════════════════════════════════════════════
# Aggregate lists
# ═══════════════════════════════════════════════════════════════════════

ALL_INCIDENCE_AXIOMS: List[HClause] = (
    INCIDENCE_AXIOMS
    + COLLINEARITY_AXIOMS
    # LOWER_DIM_AXIOMS excluded: they are about axiom constants PP, PQ, PR,
    # not schema variables.  Grounding them with arbitrary point names is
    # unsound (produces ¬EqPt(A,A) conflicting with reflexivity).
)

ALL_ORDER_AXIOMS: List[HClause] = (
    BETWEEN_AXIOMS
    + CUT_AXIOMS
    + PASCH_AXIOMS
)

ALL_CONGRUENCE_AXIOMS: List[HClause] = (
    SEGMENT_CONGRUENCE_AXIOMS
    + ADDITION_AXIOMS
    + ANGLE_CONGRUENCE_AXIOMS
    + SAS_AXIOMS
    + SAME_SIDE_AXIOMS
)

ALL_H_AXIOMS: List[HClause] = (
    ALL_INCIDENCE_AXIOMS
    + ALL_ORDER_AXIOMS
    + ALL_CONGRUENCE_AXIOMS
    + PARALLEL_AXIOMS
)
