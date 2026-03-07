"""
e_library.py — Theorem library for System E.

Provides pre-proved theorems (ETheorem objects) that can be applied in
later proofs via theorem-application steps.

Each theorem is a sequent:  Γ ⇒ ∃x̄. Δ

Reference: Avigad, Dean, Mumma (2009), Section 4.2 (proofs) and
           Section 3.3 (construction rules used in proofs).

GeoCoq connection (https://geocoq.github.io/GeoCoq/):
  The propositions here correspond to those formalized in GeoCoq's
  Elements/OriginalProofs directory, which provides Coq proofs of
  Euclid's Book 1 propositions using an axiom system equivalent to
  System E (via Tarski-to-Euclid bridge).
"""
from __future__ import annotations

from typing import Dict, List

from .e_ast import (
    Sort, Literal, Sequent, ETheorem,
    On, SameSide, Between, Center, Inside, Intersects,
    Equals, LessThan,
    SegmentTerm, AngleTerm, AreaTerm, MagAdd, RightAngle, ZeroMag,
)


def _pos(atom) -> Literal:
    return Literal(atom, polarity=True)


def _neg(atom) -> Literal:
    return Literal(atom, polarity=False)


# ═══════════════════════════════════════════════════════════════════════
# Proposition I.1 — Construct an equilateral triangle on a given segment
# ═══════════════════════════════════════════════════════════════════════

PROP_I_1 = ETheorem(
    name="Prop.I.1",
    statement="On a given finite straight line, construct an equilateral triangle.",
    sequent=Sequent(
        # Hypotheses: a ≠ b  (two distinct points)
        hypotheses=[
            _neg(Equals("a", "b")),
        ],
        # ∃c such that ab = ac, ab = bc, c ≠ a, c ≠ b
        exists_vars=[("c", Sort.POINT)],
        conclusions=[
            _pos(Equals(SegmentTerm("a", "b"), SegmentTerm("a", "c"))),
            _pos(Equals(SegmentTerm("a", "b"), SegmentTerm("b", "c"))),
            _neg(Equals("c", "a")),
            _neg(Equals("c", "b")),
        ],
    ),
)


# ═══════════════════════════════════════════════════════════════════════
# Proposition I.2 — Copy a segment to a given point
# ═══════════════════════════════════════════════════════════════════════

PROP_I_2 = ETheorem(
    name="Prop.I.2",
    statement=(
        "From a given point, place a straight line equal to a given "
        "straight line."
    ),
    sequent=Sequent(
        # Hypotheses: L is a line, b and c distinct on L, a distinct from b,c
        hypotheses=[
            _pos(On("b", "L")),
            _pos(On("c", "L")),
            _neg(Equals("b", "c")),
            _neg(Equals("a", "b")),
            _neg(Equals("a", "c")),
        ],
        # ∃f such that af = bc
        exists_vars=[("f", Sort.POINT)],
        conclusions=[
            _pos(Equals(SegmentTerm("a", "f"), SegmentTerm("b", "c"))),
        ],
    ),
)


# ═══════════════════════════════════════════════════════════════════════
# Proposition I.3 — Cut off a segment equal to the less
# ═══════════════════════════════════════════════════════════════════════

PROP_I_3 = ETheorem(
    name="Prop.I.3",
    statement=(
        "From the greater of two unequal straight lines, cut off a "
        "straight line equal to the less."
    ),
    sequent=Sequent(
        # Hypotheses: on(a,L), on(b,L), a≠b, cd < ab
        hypotheses=[
            _pos(On("a", "L")),
            _pos(On("b", "L")),
            _neg(Equals("a", "b")),
            _pos(LessThan(SegmentTerm("c", "d"), SegmentTerm("a", "b"))),
        ],
        # ∃e: between(a,e,b) ∧ ae = cd
        exists_vars=[("e", Sort.POINT)],
        conclusions=[
            _pos(Between("a", "e", "b")),
            _pos(Equals(SegmentTerm("a", "e"), SegmentTerm("c", "d"))),
        ],
    ),
)


# ═══════════════════════════════════════════════════════════════════════
# Proposition I.4 — SAS triangle congruence
# ═══════════════════════════════════════════════════════════════════════

PROP_I_4 = ETheorem(
    name="Prop.I.4",
    statement="SAS: side-angle-side triangle congruence.",
    sequent=Sequent(
        # Hypotheses: ab=de, ac=df, ∠bac = ∠edf
        hypotheses=[
            _pos(Equals(SegmentTerm("a", "b"), SegmentTerm("d", "e"))),
            _pos(Equals(SegmentTerm("a", "c"), SegmentTerm("d", "f"))),
            _pos(Equals(AngleTerm("b", "a", "c"),
                        AngleTerm("e", "d", "f"))),
        ],
        # Conclusions: bc=ef, ∠abc=∠def, ∠bca=∠efd, △abc=△def
        exists_vars=[],
        conclusions=[
            _pos(Equals(SegmentTerm("b", "c"), SegmentTerm("e", "f"))),
            _pos(Equals(AngleTerm("a", "b", "c"),
                        AngleTerm("d", "e", "f"))),
            _pos(Equals(AngleTerm("b", "c", "a"),
                        AngleTerm("e", "f", "d"))),
            _pos(Equals(AreaTerm("a", "b", "c"),
                        AreaTerm("d", "e", "f"))),
        ],
    ),
)


# ═══════════════════════════════════════════════════════════════════════
# Proposition I.5 — Isosceles triangle: base angles equal
# ═══════════════════════════════════════════════════════════════════════

PROP_I_5 = ETheorem(
    name="Prop.I.5",
    statement="In isosceles triangles the base angles are equal.",
    sequent=Sequent(
        hypotheses=[
            _pos(Equals(SegmentTerm("a", "b"), SegmentTerm("a", "c"))),
            _neg(Equals("a", "b")),
            _neg(Equals("a", "c")),
            _neg(Equals("b", "c")),
        ],
        exists_vars=[],
        conclusions=[
            _pos(Equals(AngleTerm("a", "b", "c"),
                        AngleTerm("a", "c", "b"))),
        ],
    ),
)


# ═══════════════════════════════════════════════════════════════════════
# Proposition I.8 — SSS triangle congruence
# ═══════════════════════════════════════════════════════════════════════

PROP_I_8 = ETheorem(
    name="Prop.I.8",
    statement="SSS: side-side-side triangle congruence.",
    sequent=Sequent(
        hypotheses=[
            _pos(Equals(SegmentTerm("a", "b"), SegmentTerm("d", "e"))),
            _pos(Equals(SegmentTerm("b", "c"), SegmentTerm("e", "f"))),
            _pos(Equals(SegmentTerm("c", "a"), SegmentTerm("f", "d"))),
        ],
        exists_vars=[],
        conclusions=[
            _pos(Equals(AngleTerm("b", "a", "c"),
                        AngleTerm("e", "d", "f"))),
            _pos(Equals(AngleTerm("a", "b", "c"),
                        AngleTerm("d", "e", "f"))),
            _pos(Equals(AngleTerm("b", "c", "a"),
                        AngleTerm("e", "f", "d"))),
            _pos(Equals(AreaTerm("a", "b", "c"),
                        AreaTerm("d", "e", "f"))),
        ],
    ),
)


# ═══════════════════════════════════════════════════════════════════════
# Proposition I.10 — Bisect a finite straight line
# ═══════════════════════════════════════════════════════════════════════

PROP_I_10 = ETheorem(
    name="Prop.I.10",
    statement="To bisect a given finite straight line.",
    sequent=Sequent(
        hypotheses=[
            _pos(On("a", "L")),
            _pos(On("b", "L")),
            _neg(Equals("a", "b")),
        ],
        exists_vars=[("d", Sort.POINT)],
        conclusions=[
            _pos(Between("a", "d", "b")),
            _pos(Equals(SegmentTerm("a", "d"), SegmentTerm("d", "b"))),
        ],
    ),
)


# ═══════════════════════════════════════════════════════════════════════
# Proposition I.6 — Converse of I.5: equal base angles → isosceles
#
# If two angles of a triangle are equal, the sides opposite them
# are also equal.  (Converse of the isosceles-triangle theorem.)
# ═══════════════════════════════════════════════════════════════════════

PROP_I_6 = ETheorem(
    name="Prop.I.6",
    statement=(
        "If in a triangle two angles are equal, then the sides "
        "opposite the equal angles are also equal."
    ),
    sequent=Sequent(
        hypotheses=[
            _pos(Equals(AngleTerm("a", "b", "c"),
                        AngleTerm("a", "c", "b"))),
            _neg(Equals("a", "b")),
            _neg(Equals("a", "c")),
            _neg(Equals("b", "c")),
        ],
        exists_vars=[],
        conclusions=[
            _pos(Equals(SegmentTerm("a", "b"), SegmentTerm("a", "c"))),
        ],
    ),
)


# ═══════════════════════════════════════════════════════════════════════
# Proposition I.7 — Uniqueness of triangle construction
#
# Given a triangle ABC and a point D on the same side of BC as A,
# if BD = BA and CD = CA, then D = A.
# (This is a lemma for I.8, SSS.)
# ═══════════════════════════════════════════════════════════════════════

PROP_I_7 = ETheorem(
    name="Prop.I.7",
    statement=(
        "Given segments BA, CA from endpoints of a segment BC, there "
        "cannot be constructed from the same endpoints and on the same "
        "side of it other segments BD, CD equal to them respectively."
    ),
    sequent=Sequent(
        hypotheses=[
            _pos(On("b", "L")),
            _pos(On("c", "L")),
            _neg(Equals("b", "c")),
            _pos(SameSide("a", "d", "L")),
            _pos(Equals(SegmentTerm("b", "d"), SegmentTerm("b", "a"))),
            _pos(Equals(SegmentTerm("c", "d"), SegmentTerm("c", "a"))),
        ],
        exists_vars=[],
        conclusions=[
            _pos(Equals("d", "a")),
        ],
    ),
)


# ═══════════════════════════════════════════════════════════════════════
# Proposition I.9 — Bisect a rectilineal angle
#
# Given an angle ∠bac, construct a ray that bisects it.
# The bisector point e satisfies ∠bae = ∠cae, with e on the
# correct side of each arm.
# ═══════════════════════════════════════════════════════════════════════

PROP_I_9 = ETheorem(
    name="Prop.I.9",
    statement="To bisect a given rectilineal angle.",
    sequent=Sequent(
        hypotheses=[
            _neg(Equals("a", "b")),
            _neg(Equals("a", "c")),
            _neg(Equals("b", "c")),
            _pos(On("a", "M")),
            _pos(On("b", "M")),
            _pos(On("a", "N")),
            _pos(On("c", "N")),
            _pos(SameSide("c", "b", "M")),
            _pos(SameSide("b", "c", "N")),
        ],
        exists_vars=[("e", Sort.POINT)],
        conclusions=[
            _pos(Equals(AngleTerm("b", "a", "e"),
                        AngleTerm("c", "a", "e"))),
            _pos(SameSide("e", "c", "M")),
            _pos(SameSide("e", "b", "N")),
        ],
    ),
)


# ═══════════════════════════════════════════════════════════════════════
# Proposition I.11 — Draw a perpendicular from a point on a line
#
# From a point on a line, draw a perpendicular to the line.
# Depends on: I.1, I.3.
# ═══════════════════════════════════════════════════════════════════════

PROP_I_11 = ETheorem(
    name="Prop.I.11",
    statement=(
        "To draw a straight line at right angles to a given straight "
        "line from a given point on it."
    ),
    sequent=Sequent(
        hypotheses=[
            _pos(On("a", "L")),
            _pos(On("b", "L")),
            _neg(Equals("a", "b")),
        ],
        exists_vars=[("f", Sort.POINT)],
        conclusions=[
            _pos(Equals(AngleTerm("b", "a", "f"),
                        RightAngle())),
            _neg(Equals("f", "a")),
            _neg(On("f", "L")),
        ],
    ),
)


# ═══════════════════════════════════════════════════════════════════════
# Proposition I.12 — Drop a perpendicular from a point off a line
#
# From a point not on a line, draw a perpendicular to the line.
# Depends on: I.8, I.10.
# ═══════════════════════════════════════════════════════════════════════

PROP_I_12 = ETheorem(
    name="Prop.I.12",
    statement=(
        "To draw a straight line perpendicular to a given infinite "
        "straight line from a given point not on it."
    ),
    sequent=Sequent(
        hypotheses=[
            _pos(On("a", "L")),
            _pos(On("b", "L")),
            _neg(Equals("a", "b")),
            _neg(On("p", "L")),
        ],
        exists_vars=[("h", Sort.POINT)],
        conclusions=[
            _pos(On("h", "L")),
            _pos(Equals(AngleTerm("a", "h", "p"),
                        RightAngle())),
            _neg(Equals("h", "p")),
        ],
    ),
)


# ═══════════════════════════════════════════════════════════════════════
# Proposition I.13 — Supplementary angles sum to two right angles
#
# If a straight line falls on another, the adjacent angles sum
# to two right angles.
# Depends on: I.11.
# ═══════════════════════════════════════════════════════════════════════

PROP_I_13 = ETheorem(
    name="Prop.I.13",
    statement=(
        "If a straight line set up on a straight line makes angles, "
        "it makes either two right angles or angles equal to two "
        "right angles."
    ),
    sequent=Sequent(
        hypotheses=[
            _pos(On("a", "L")),
            _pos(On("c", "L")),
            _pos(Between("a", "b", "c")),
            _neg(On("d", "L")),
            _neg(Equals("b", "d")),
        ],
        exists_vars=[],
        conclusions=[
            _pos(Equals(
                MagAdd(AngleTerm("a", "b", "d"),
                       AngleTerm("d", "b", "c")),
                MagAdd(RightAngle(), RightAngle()),
            )),
        ],
    ),
)


# ═══════════════════════════════════════════════════════════════════════
# Proposition I.14 — Converse of I.13
#
# If two adjacent angles at a point on a line sum to two right
# angles, then the two outer rays form a straight line.
# Depends on: I.13.
# ═══════════════════════════════════════════════════════════════════════

PROP_I_14 = ETheorem(
    name="Prop.I.14",
    statement=(
        "If with any straight line, and at a point on it, two "
        "straight lines not lying on the same side make the adjacent "
        "angles equal to two right angles, the two lines are in a "
        "straight line with one another."
    ),
    sequent=Sequent(
        hypotheses=[
            _pos(On("a", "L")),
            _pos(On("b", "L")),
            _neg(Equals("a", "b")),
            _neg(On("c", "L")),
            _neg(On("d", "L")),
            _neg(Equals("b", "c")),
            _neg(Equals("b", "d")),
            _neg(SameSide("c", "d", "L")),
            _pos(Equals(
                MagAdd(AngleTerm("a", "b", "c"),
                       AngleTerm("a", "b", "d")),
                MagAdd(RightAngle(), RightAngle()),
            )),
        ],
        exists_vars=[],
        conclusions=[
            _pos(Between("c", "b", "d")),
        ],
    ),
)


# ═══════════════════════════════════════════════════════════════════════
# Proposition I.15 — Vertical angles are equal
#
# If two straight lines cut one another, they make the vertical
# angles equal to one another.
# Depends on: I.13.
# ═══════════════════════════════════════════════════════════════════════

PROP_I_15 = ETheorem(
    name="Prop.I.15",
    statement=(
        "If two straight lines cut one another, they make the "
        "vertical angles equal to one another."
    ),
    sequent=Sequent(
        hypotheses=[
            _pos(On("a", "L")),
            _pos(On("b", "L")),
            _pos(On("c", "M")),
            _pos(On("d", "M")),
            _pos(On("e", "L")),
            _pos(On("e", "M")),
            _pos(Between("a", "e", "b")),
            _pos(Between("c", "e", "d")),
            _neg(Equals("L", "M")),
        ],
        exists_vars=[],
        conclusions=[
            _pos(Equals(AngleTerm("a", "e", "c"),
                        AngleTerm("b", "e", "d"))),
        ],
    ),
)


# ═══════════════════════════════════════════════════════════════════════
# Proposition I.16 — Exterior angle greater than remote interior
#
# In any triangle, if one of the sides is produced, the exterior
# angle is greater than either of the interior and opposite angles.
# Depends on: I.3, I.4, I.10, I.15.
# ═══════════════════════════════════════════════════════════════════════

PROP_I_16 = ETheorem(
    name="Prop.I.16",
    statement=(
        "In any triangle, if one of the sides is produced, the "
        "exterior angle is greater than either of the interior "
        "and opposite angles."
    ),
    sequent=Sequent(
        hypotheses=[
            _pos(On("a", "L")),
            _pos(On("b", "L")),
            _pos(Between("a", "b", "d")),
            _neg(On("c", "L")),
            _neg(Equals("a", "b")),
            _neg(Equals("a", "c")),
            _neg(Equals("b", "c")),
        ],
        exists_vars=[],
        conclusions=[
            _pos(LessThan(AngleTerm("b", "a", "c"),
                          AngleTerm("d", "b", "c"))),
            _pos(LessThan(AngleTerm("b", "c", "a"),
                          AngleTerm("d", "b", "c"))),
        ],
    ),
)


# ═══════════════════════════════════════════════════════════════════════
# Proposition I.17 — Two angles of a triangle < two right angles
#
# In any triangle, two angles taken together are less than two
# right angles.
# Depends on: I.13, I.16.
# ═══════════════════════════════════════════════════════════════════════

PROP_I_17 = ETheorem(
    name="Prop.I.17",
    statement=(
        "In any triangle two angles taken together in any manner "
        "are less than two right angles."
    ),
    sequent=Sequent(
        hypotheses=[
            _neg(Equals("a", "b")),
            _neg(Equals("a", "c")),
            _neg(Equals("b", "c")),
            _pos(On("a", "L")),
            _pos(On("b", "L")),
            _neg(On("c", "L")),
        ],
        exists_vars=[],
        conclusions=[
            _pos(LessThan(
                MagAdd(AngleTerm("a", "b", "c"),
                       AngleTerm("b", "c", "a")),
                MagAdd(RightAngle(), RightAngle()),
            )),
        ],
    ),
)


# ═══════════════════════════════════════════════════════════════════════
# Proposition I.18 — Greater side opposite greater angle
#
# In any triangle the greater side subtends the greater angle.
# Depends on: I.3, I.5, I.16.
# ═══════════════════════════════════════════════════════════════════════

PROP_I_18 = ETheorem(
    name="Prop.I.18",
    statement=(
        "In any triangle the greater side subtends the greater angle."
    ),
    sequent=Sequent(
        hypotheses=[
            _neg(Equals("a", "b")),
            _neg(Equals("a", "c")),
            _neg(Equals("b", "c")),
            _pos(LessThan(SegmentTerm("a", "b"), SegmentTerm("a", "c"))),
        ],
        exists_vars=[],
        conclusions=[
            # AB < AC, so AC (opposite ∠B) is greater → ∠B > ∠C
            _pos(LessThan(AngleTerm("a", "c", "b"),
                          AngleTerm("a", "b", "c"))),
        ],
    ),
)


# ═══════════════════════════════════════════════════════════════════════
# Proposition I.19 — Greater angle opposite greater side (converse I.18)
#
# In any triangle the greater angle is subtended by the greater side.
# Depends on: I.5, I.18.
# ═══════════════════════════════════════════════════════════════════════

PROP_I_19 = ETheorem(
    name="Prop.I.19",
    statement=(
        "In any triangle the greater angle is subtended by the "
        "greater side."
    ),
    sequent=Sequent(
        hypotheses=[
            _neg(Equals("a", "b")),
            _neg(Equals("a", "c")),
            _neg(Equals("b", "c")),
            # ∠B < ∠C (angle at B is smaller)
            _pos(LessThan(AngleTerm("a", "b", "c"),
                          AngleTerm("a", "c", "b"))),
        ],
        exists_vars=[],
        conclusions=[
            # Side opposite smaller angle (∠B) < side opposite larger angle (∠C)
            # Side opposite ∠B is AC, side opposite ∠C is AB → AC < AB
            _pos(LessThan(SegmentTerm("a", "c"), SegmentTerm("a", "b"))),
        ],
    ),
)


# ═══════════════════════════════════════════════════════════════════════
# Proposition I.20 — Triangle inequality
#
# In any triangle two sides taken together are greater than
# the remaining one.
# Depends on: I.3, I.5, I.19.
# ═══════════════════════════════════════════════════════════════════════

PROP_I_20 = ETheorem(
    name="Prop.I.20",
    statement=(
        "In any triangle two sides taken together in any manner "
        "are greater than the remaining one."
    ),
    sequent=Sequent(
        hypotheses=[
            _neg(Equals("a", "b")),
            _neg(Equals("a", "c")),
            _neg(Equals("b", "c")),
        ],
        exists_vars=[],
        conclusions=[
            _pos(LessThan(
                SegmentTerm("b", "c"),
                MagAdd(SegmentTerm("a", "b"), SegmentTerm("a", "c")),
            )),
        ],
    ),
)


# ═══════════════════════════════════════════════════════════════════════
# Proposition I.21 — Inner triangle has shorter sides, larger angles
#
# If from the endpoints of a side of a triangle two lines are
# drawn meeting within the triangle, the sum of those lines is
# less than the sum of the remaining two sides but they contain
# a greater angle.
# Depends on: I.16, I.20.
# ═══════════════════════════════════════════════════════════════════════

PROP_I_21 = ETheorem(
    name="Prop.I.21",
    statement=(
        "If on one of the sides of a triangle, from its extremities, "
        "there be constructed two straight lines meeting within the "
        "triangle, the straight lines so constructed will be less "
        "than the remaining two sides but will contain a greater angle."
    ),
    sequent=Sequent(
        hypotheses=[
            _neg(Equals("a", "b")),
            _neg(Equals("a", "c")),
            _neg(Equals("b", "c")),
            _neg(Equals("d", "b")),
            _neg(Equals("d", "c")),
            # d is inside triangle abc (between-conditions ensure this)
            _pos(On("b", "L")),
            _pos(On("c", "L")),
            _neg(On("a", "L")),
            _pos(SameSide("d", "a", "L")),
        ],
        exists_vars=[],
        conclusions=[
            _pos(LessThan(
                MagAdd(SegmentTerm("b", "d"), SegmentTerm("d", "c")),
                MagAdd(SegmentTerm("b", "a"), SegmentTerm("a", "c")),
            )),
            _pos(LessThan(
                AngleTerm("b", "a", "c"),
                AngleTerm("b", "d", "c"),
            )),
        ],
    ),
)


# ═══════════════════════════════════════════════════════════════════════
# Proposition I.22 — Construct a triangle from three segments
#
# Out of three straight lines, which are equal to three given
# straight lines, to construct a triangle: thus it is necessary
# that two of the straight lines taken together in any manner
# should be greater than the remaining one.
# Depends on: I.3, I.20.
# ═══════════════════════════════════════════════════════════════════════

PROP_I_22 = ETheorem(
    name="Prop.I.22",
    statement=(
        "Out of three straight lines, which are equal to three "
        "given straight lines, to construct a triangle."
    ),
    sequent=Sequent(
        hypotheses=[
            _neg(Equals("a", "b")),
            _neg(Equals("c", "d")),
            _neg(Equals("e", "f")),
            # Triangle inequality prerequisites
            _pos(LessThan(
                SegmentTerm("a", "b"),
                MagAdd(SegmentTerm("c", "d"), SegmentTerm("e", "f")),
            )),
            _pos(LessThan(
                SegmentTerm("c", "d"),
                MagAdd(SegmentTerm("a", "b"), SegmentTerm("e", "f")),
            )),
            _pos(LessThan(
                SegmentTerm("e", "f"),
                MagAdd(SegmentTerm("a", "b"), SegmentTerm("c", "d")),
            )),
        ],
        exists_vars=[
            ("p", Sort.POINT), ("q", Sort.POINT), ("r", Sort.POINT),
        ],
        conclusions=[
            _pos(Equals(SegmentTerm("p", "q"), SegmentTerm("a", "b"))),
            _pos(Equals(SegmentTerm("p", "r"), SegmentTerm("c", "d"))),
            _pos(Equals(SegmentTerm("q", "r"), SegmentTerm("e", "f"))),
        ],
    ),
)


# ═══════════════════════════════════════════════════════════════════════
# Proposition I.23 — Copy an angle
#
# On a given straight line and at a point on it, to construct a
# rectilineal angle equal to a given rectilineal angle.
# Depends on: I.8, I.22.
# ═══════════════════════════════════════════════════════════════════════

PROP_I_23 = ETheorem(
    name="Prop.I.23",
    statement=(
        "On a given straight line and at a point on it, to construct "
        "a rectilineal angle equal to a given rectilineal angle."
    ),
    sequent=Sequent(
        hypotheses=[
            _neg(Equals("d", "e")),
            _neg(Equals("d", "f")),
            _neg(Equals("e", "f")),
            _pos(On("a", "L")),
            _pos(On("b", "L")),
            _neg(Equals("a", "b")),
        ],
        exists_vars=[("g", Sort.POINT)],
        conclusions=[
            _pos(Equals(AngleTerm("b", "a", "g"),
                        AngleTerm("e", "d", "f"))),
            _neg(On("g", "L")),
        ],
    ),
)


# ═══════════════════════════════════════════════════════════════════════
# Proposition I.24 — SAS inequality (hinge theorem)
#
# If two triangles have two sides equal respectively but the
# included angle of one greater, then the base of that one is
# greater than the base of the other.
# Depends on: I.3, I.4, I.5, I.19, I.23.
# ═══════════════════════════════════════════════════════════════════════

PROP_I_24 = ETheorem(
    name="Prop.I.24",
    statement=(
        "If two triangles have two sides equal respectively but the "
        "included angle of the first greater than that of the second, "
        "the base of the first is also greater than the base of the "
        "second."
    ),
    sequent=Sequent(
        hypotheses=[
            _pos(Equals(SegmentTerm("a", "b"), SegmentTerm("d", "e"))),
            _pos(Equals(SegmentTerm("a", "c"), SegmentTerm("d", "f"))),
            _pos(LessThan(AngleTerm("e", "d", "f"),
                          AngleTerm("b", "a", "c"))),
            _neg(Equals("a", "b")),
            _neg(Equals("a", "c")),
            _neg(Equals("b", "c")),
            _neg(Equals("d", "e")),
            _neg(Equals("d", "f")),
            _neg(Equals("e", "f")),
        ],
        exists_vars=[],
        conclusions=[
            _pos(LessThan(SegmentTerm("e", "f"),
                          SegmentTerm("b", "c"))),
        ],
    ),
)


# ═══════════════════════════════════════════════════════════════════════
# Proposition I.25 — Converse hinge theorem
#
# If two triangles have two sides equal respectively but the
# base of one greater, then the included angle of that one is
# greater.
# Depends on: I.4, I.24.
# ═══════════════════════════════════════════════════════════════════════

PROP_I_25 = ETheorem(
    name="Prop.I.25",
    statement=(
        "If two triangles have two sides equal respectively but the "
        "base of the first greater, the angle contained by the equal "
        "sides of the first is also greater."
    ),
    sequent=Sequent(
        hypotheses=[
            _pos(Equals(SegmentTerm("a", "b"), SegmentTerm("d", "e"))),
            _pos(Equals(SegmentTerm("a", "c"), SegmentTerm("d", "f"))),
            _pos(LessThan(SegmentTerm("e", "f"),
                          SegmentTerm("b", "c"))),
            _neg(Equals("a", "b")),
            _neg(Equals("a", "c")),
            _neg(Equals("b", "c")),
            _neg(Equals("d", "e")),
            _neg(Equals("d", "f")),
            _neg(Equals("e", "f")),
        ],
        exists_vars=[],
        conclusions=[
            _pos(LessThan(AngleTerm("e", "d", "f"),
                          AngleTerm("b", "a", "c"))),
        ],
    ),
)


# ═══════════════════════════════════════════════════════════════════════
# Proposition I.26 — ASA and AAS triangle congruence
#
# If two triangles have two angles equal to two angles
# respectively and one side equal — either the side between
# the equal angles (ASA) or the side opposite one of them
# (AAS) — then the triangles are congruent.
# Depends on: I.3, I.4, I.16.
# ═══════════════════════════════════════════════════════════════════════

PROP_I_26 = ETheorem(
    name="Prop.I.26",
    statement=(
        "If two triangles have the two angles equal to two angles "
        "respectively, and one side equal to one side, namely either "
        "the side adjoining the equal angles, or that subtending one "
        "of the equal angles, they will also have the remaining sides "
        "equal and the remaining angle equal."
    ),
    sequent=Sequent(
        # ASA case: ∠abc = ∠def, ∠bca = ∠efd, bc = ef
        hypotheses=[
            _pos(Equals(AngleTerm("a", "b", "c"),
                        AngleTerm("d", "e", "f"))),
            _pos(Equals(AngleTerm("b", "c", "a"),
                        AngleTerm("e", "f", "d"))),
            _pos(Equals(SegmentTerm("b", "c"), SegmentTerm("e", "f"))),
            _neg(Equals("a", "b")),
            _neg(Equals("a", "c")),
            _neg(Equals("b", "c")),
            _neg(Equals("d", "e")),
            _neg(Equals("d", "f")),
            _neg(Equals("e", "f")),
        ],
        exists_vars=[],
        conclusions=[
            _pos(Equals(SegmentTerm("a", "b"), SegmentTerm("d", "e"))),
            _pos(Equals(SegmentTerm("a", "c"), SegmentTerm("d", "f"))),
            _pos(Equals(AngleTerm("b", "a", "c"),
                        AngleTerm("e", "d", "f"))),
            _pos(Equals(AreaTerm("a", "b", "c"),
                        AreaTerm("d", "e", "f"))),
        ],
    ),
)


# ═══════════════════════════════════════════════════════════════════════
# Proposition I.27 — Alternate interior angles imply parallel
#
# If a straight line falling on two straight lines makes the
# alternate angles equal to one another, the straight lines will
# be parallel to one another.
# Depends on: I.16.
#
# In System E, "parallel" = ¬intersects(L, N).  The transversal M
# meets L at b and N at c.  If ∠abc = ∠bcd (alternate interior
# angles on opposite sides of M), then L and N do not intersect.
# ═══════════════════════════════════════════════════════════════════════

PROP_I_27 = ETheorem(
    name="Prop.I.27",
    statement=(
        "If a straight line falling on two straight lines makes the "
        "alternate angles equal to one another, the straight lines "
        "will be parallel to one another."
    ),
    sequent=Sequent(
        hypotheses=[
            # Lines L and N, transversal M meeting L at b, N at c
            _pos(On("a", "L")),
            _pos(On("b", "L")),
            _pos(On("b", "M")),
            _pos(On("c", "M")),
            _pos(On("c", "N")),
            _pos(On("d", "N")),
            _neg(Equals("a", "b")),
            _neg(Equals("b", "c")),
            _neg(Equals("c", "d")),
            _neg(Equals("L", "N")),
            # a, d on opposite sides of M (alternate angles)
            _neg(SameSide("a", "d", "M")),
            # Alternate interior angles are equal
            _pos(Equals(AngleTerm("a", "b", "c"),
                        AngleTerm("b", "c", "d"))),
        ],
        exists_vars=[],
        conclusions=[
            _neg(Intersects("L", "N")),
        ],
    ),
)


# ═══════════════════════════════════════════════════════════════════════
# Proposition I.28 — Corresponding or co-interior angles imply parallel
#
# If a straight line falling on two straight lines makes the
# exterior angle equal to the interior and opposite angle on the
# same side, or the interior angles on the same side equal to two
# right angles, the straight lines will be parallel.
# Depends on: I.13, I.15, I.27.
# ═══════════════════════════════════════════════════════════════════════

PROP_I_28 = ETheorem(
    name="Prop.I.28",
    statement=(
        "If a straight line falling on two straight lines makes the "
        "exterior angle equal to the interior and opposite angle on "
        "the same side, or the interior angles on the same side equal "
        "to two right angles, the straight lines will be parallel."
    ),
    sequent=Sequent(
        # Co-interior angles on the same side sum to two right angles
        # ⇒ lines do not intersect
        hypotheses=[
            _pos(On("a", "L")),
            _pos(On("b", "L")),
            _pos(On("b", "M")),
            _pos(On("c", "M")),
            _pos(On("c", "N")),
            _pos(On("d", "N")),
            _neg(Equals("a", "b")),
            _neg(Equals("b", "c")),
            _neg(Equals("c", "d")),
            _neg(Equals("L", "N")),
            _pos(SameSide("a", "d", "M")),
            # Co-interior angles sum to two right angles
            _pos(Equals(
                MagAdd(AngleTerm("a", "b", "c"),
                       AngleTerm("b", "c", "d")),
                MagAdd(RightAngle(), RightAngle()),
            )),
        ],
        exists_vars=[],
        conclusions=[
            _neg(Intersects("L", "N")),
        ],
    ),
)


# ═══════════════════════════════════════════════════════════════════════
# Proposition I.29 — Parallel implies alternate interior angles equal
#
# A straight line falling on parallel straight lines makes the
# alternate angles equal to one another, the exterior angle equal
# to the interior and opposite angle, and the interior angles on
# the same side equal to two right angles.
# Depends on: I.13, Post.5 (parallel postulate).
#
# This is the FIRST use of the parallel postulate (Postulate 5 /
# DA5 in e_axioms.py).  Everything before I.29 is neutral geometry.
# ═══════════════════════════════════════════════════════════════════════

PROP_I_29 = ETheorem(
    name="Prop.I.29",
    statement=(
        "A straight line falling on parallel straight lines makes "
        "the alternate angles equal to one another, the exterior "
        "angle equal to the interior and opposite angle, and the "
        "interior angles on the same side equal to two right angles."
    ),
    sequent=Sequent(
        hypotheses=[
            _pos(On("a", "L")),
            _pos(On("b", "L")),
            _pos(On("b", "M")),
            _pos(On("c", "M")),
            _pos(On("c", "N")),
            _pos(On("d", "N")),
            _neg(Equals("a", "b")),
            _neg(Equals("b", "c")),
            _neg(Equals("c", "d")),
            _neg(Equals("L", "N")),
            # a, d on opposite sides of transversal (for alternate angles)
            _neg(SameSide("a", "d", "M")),
            # Lines are parallel (do not intersect)
            _neg(Intersects("L", "N")),
        ],
        exists_vars=[],
        conclusions=[
            # Alternate interior angles are equal
            _pos(Equals(AngleTerm("a", "b", "c"),
                        AngleTerm("b", "c", "d"))),
        ],
    ),
)


# ═══════════════════════════════════════════════════════════════════════
# Proposition I.30 — Transitivity of parallelism
#
# Straight lines parallel to the same straight line are also
# parallel to one another.
# Depends on: I.27, I.29, I.23.
# ═══════════════════════════════════════════════════════════════════════

PROP_I_30 = ETheorem(
    name="Prop.I.30",
    statement=(
        "Straight lines parallel to the same straight line are also "
        "parallel to one another."
    ),
    sequent=Sequent(
        hypotheses=[
            # L ∥ M and M ∥ N (both do not intersect)
            _neg(Intersects("L", "M")),
            _neg(Intersects("M", "N")),
            _neg(Equals("L", "M")),
            _neg(Equals("M", "N")),
            _neg(Equals("L", "N")),
        ],
        exists_vars=[],
        conclusions=[
            _neg(Intersects("L", "N")),
        ],
    ),
)


# ═══════════════════════════════════════════════════════════════════════
# Proposition I.31 — Construct a parallel through a given point
#
# Through a given point to draw a straight line parallel to a
# given straight line.
# Depends on: I.23, I.27.
# ═══════════════════════════════════════════════════════════════════════

PROP_I_31 = ETheorem(
    name="Prop.I.31",
    statement=(
        "Through a given point to draw a straight line parallel to "
        "a given straight line."
    ),
    sequent=Sequent(
        hypotheses=[
            # Given line L and point a not on L
            _pos(On("b", "L")),
            _pos(On("c", "L")),
            _neg(Equals("b", "c")),
            _neg(On("a", "L")),
        ],
        exists_vars=[
            ("M", Sort.LINE),
        ],
        conclusions=[
            _pos(On("a", "M")),
            _neg(Intersects("L", "M")),
        ],
    ),
)


# ═══════════════════════════════════════════════════════════════════════
# Proposition I.32 — Exterior angle and angle sum of a triangle
#
# In any triangle, if one of the sides is produced, the exterior
# angle is equal to the two interior and opposite angles, and the
# three interior angles of the triangle are equal to two right
# angles.
# Depends on: I.13, I.29, I.31.
# ═══════════════════════════════════════════════════════════════════════

PROP_I_32 = ETheorem(
    name="Prop.I.32",
    statement=(
        "In any triangle, if one of the sides is produced, the "
        "exterior angle is equal to the two interior and opposite "
        "angles, and the three interior angles of the triangle are "
        "equal to two right angles."
    ),
    sequent=Sequent(
        hypotheses=[
            # Triangle abc (non-collinear) with bc produced to d
            _pos(On("b", "L")),
            _pos(On("c", "L")),
            _neg(On("a", "L")),     # a not on line BC (non-degenerate triangle)
            _neg(Equals("a", "b")),
            _neg(Equals("a", "c")),
            _neg(Equals("b", "c")),
            _pos(Between("b", "c", "d")),
            _neg(Equals("c", "d")),
        ],
        exists_vars=[],
        conclusions=[
            # Exterior angle ∠acd = ∠abc + ∠bac
            _pos(Equals(AngleTerm("a", "c", "d"),
                        MagAdd(AngleTerm("c", "a", "b"),
                               AngleTerm("a", "b", "c")))),
            # Angle sum: ∠abc + ∠bca + ∠cab = 2 right angles
            _pos(Equals(
                MagAdd(AngleTerm("a", "b", "c"),
                       MagAdd(AngleTerm("b", "c", "a"),
                              AngleTerm("c", "a", "b"))),
                MagAdd(RightAngle(), RightAngle()),
            )),
        ],
    ),
)


# ═══════════════════════════════════════════════════════════════════════
# Proposition I.33 — Opposite sides of a parallelogram are equal
#
# The straight lines joining equal and parallel straight lines
# (at the extremities which are) in the same directions (respectively)
# are themselves also equal and parallel.
# Depends on: I.4, I.27, I.29.
# ═══════════════════════════════════════════════════════════════════════

PROP_I_33 = ETheorem(
    name="Prop.I.33",
    statement=(
        "The straight lines joining equal and parallel straight lines "
        "at the extremities which are in the same directions "
        "respectively are themselves also equal and parallel."
    ),
    sequent=Sequent(
        hypotheses=[
            # ab ∥ cd (parallel lines, so L and N don't intersect)
            _pos(On("a", "L")),
            _pos(On("b", "L")),
            _pos(On("c", "N")),
            _pos(On("d", "N")),
            _neg(Intersects("L", "N")),
            _neg(Equals("a", "b")),
            _neg(Equals("c", "d")),
            # ab = cd (equal)
            _pos(Equals(SegmentTerm("a", "b"), SegmentTerm("c", "d"))),
            # a, c on line M (joining line ac)
            _pos(On("a", "M")),
            _pos(On("c", "M")),
            # b, d on line P (joining line bd)
            _pos(On("b", "P")),
            _pos(On("d", "P")),
            _neg(Equals("L", "N")),
        ],
        exists_vars=[],
        conclusions=[
            _pos(Equals(SegmentTerm("a", "c"), SegmentTerm("b", "d"))),
            _neg(Intersects("M", "P")),  # ac ∥ bd (line through a,c ∥ line through b,d)
        ],
    ),
)


# ═══════════════════════════════════════════════════════════════════════
# Proposition I.34 — Properties of a parallelogram
#
# In a parallelogram the opposite sides and angles are equal to
# one another, and the diagonal bisects the area.
# Depends on: I.4, I.26, I.29.
# ═══════════════════════════════════════════════════════════════════════

PROP_I_34 = ETheorem(
    name="Prop.I.34",
    statement=(
        "In a parallelogram the opposite sides and angles are equal "
        "to one another, and the diagonal bisects the area."
    ),
    sequent=Sequent(
        hypotheses=[
            # Parallelogram abcd: ab ∥ cd and ad ∥ bc
            _pos(On("a", "L")),
            _pos(On("b", "L")),
            _pos(On("c", "N")),
            _pos(On("d", "N")),
            _neg(Intersects("L", "N")),
            _pos(On("a", "M")),
            _pos(On("d", "M")),
            _pos(On("b", "P")),
            _pos(On("c", "P")),
            _neg(Intersects("M", "P")),
            _neg(Equals("a", "b")),
            _neg(Equals("c", "d")),
            _neg(Equals("a", "d")),
            _neg(Equals("b", "c")),
        ],
        exists_vars=[],
        conclusions=[
            _pos(Equals(SegmentTerm("a", "b"), SegmentTerm("c", "d"))),
            _pos(Equals(SegmentTerm("a", "d"), SegmentTerm("b", "c"))),
            _pos(Equals(AngleTerm("d", "a", "b"),
                        AngleTerm("b", "c", "d"))),
            _pos(Equals(AngleTerm("a", "b", "c"),
                        AngleTerm("c", "d", "a"))),
            _pos(Equals(AreaTerm("a", "b", "c"),
                        AreaTerm("a", "c", "d"))),
        ],
    ),
)


# ═══════════════════════════════════════════════════════════════════════
# Proposition I.35 — Parallelograms on the same base and between
# the same parallels are equal in area.
# Depends on: I.4, I.29, I.34, C.N.
# ═══════════════════════════════════════════════════════════════════════

PROP_I_35 = ETheorem(
    name="Prop.I.35",
    statement=(
        "Parallelograms which are on the same base and in the same "
        "parallels are equal to one another."
    ),
    sequent=Sequent(
        hypotheses=[
            # Two parallelograms ABCD, EBCF on base BC between
            # parallels L (through A,D,E,F) and N (through B,C)
            _pos(On("b", "N")),
            _pos(On("c", "N")),
            _pos(On("a", "L")),
            _pos(On("d", "L")),
            _pos(On("e", "L")),
            _pos(On("f", "L")),
            _neg(Intersects("L", "N")),
            _neg(Equals("b", "c")),
            _neg(Equals("a", "d")),
            _neg(Equals("e", "f")),
        ],
        exists_vars=[],
        conclusions=[
            # Area(ABCD) = Area(EBCF), expressed as sum of triangles
            _pos(Equals(
                MagAdd(AreaTerm("a", "b", "c"), AreaTerm("a", "c", "d")),
                MagAdd(AreaTerm("e", "b", "c"), AreaTerm("e", "c", "f")),
            )),
        ],
    ),
)


# ═══════════════════════════════════════════════════════════════════════
# Proposition I.36 — Parallelograms on equal bases and between
# the same parallels are equal in area.
# Depends on: I.33, I.34, I.35.
# ═══════════════════════════════════════════════════════════════════════

PROP_I_36 = ETheorem(
    name="Prop.I.36",
    statement=(
        "Parallelograms which are on equal bases and in the same "
        "parallels are equal to one another."
    ),
    sequent=Sequent(
        hypotheses=[
            _pos(On("b", "N")),
            _pos(On("c", "N")),
            _pos(On("e", "N")),
            _pos(On("f", "N")),
            _pos(On("a", "L")),
            _pos(On("d", "L")),
            _neg(Intersects("L", "N")),
            _pos(Equals(SegmentTerm("b", "c"), SegmentTerm("e", "f"))),
            _neg(Equals("b", "c")),
            _neg(Equals("e", "f")),
        ],
        exists_vars=[],
        conclusions=[
            _pos(Equals(
                MagAdd(AreaTerm("a", "b", "c"), AreaTerm("a", "c", "d")),
                MagAdd(AreaTerm("d", "e", "f"), AreaTerm("d", "f", "a")),
            )),
        ],
    ),
)


# ═══════════════════════════════════════════════════════════════════════
# Proposition I.37 — Triangles on the same base and between the
# same parallels are equal in area.
# Depends on: I.31, I.34, I.35.
# ═══════════════════════════════════════════════════════════════════════

PROP_I_37 = ETheorem(
    name="Prop.I.37",
    statement=(
        "Triangles which are on the same base and in the same "
        "parallels are equal to one another."
    ),
    sequent=Sequent(
        hypotheses=[
            _pos(On("b", "N")),
            _pos(On("c", "N")),
            _pos(On("a", "L")),
            _pos(On("d", "L")),
            _neg(Intersects("L", "N")),
            _neg(Equals("b", "c")),
            _neg(Equals("a", "d")),
            _neg(On("a", "N")),
            _neg(On("d", "N")),
        ],
        exists_vars=[],
        conclusions=[
            _pos(Equals(AreaTerm("a", "b", "c"),
                        AreaTerm("d", "b", "c"))),
        ],
    ),
)


# ═══════════════════════════════════════════════════════════════════════
# Proposition I.38 — Triangles on equal bases and between the
# same parallels are equal in area.
# Depends on: I.31, I.34, I.36.
# ═══════════════════════════════════════════════════════════════════════

PROP_I_38 = ETheorem(
    name="Prop.I.38",
    statement=(
        "Triangles which are on equal bases and in the same "
        "parallels are equal to one another."
    ),
    sequent=Sequent(
        hypotheses=[
            _pos(On("b", "N")),
            _pos(On("c", "N")),
            _pos(On("e", "N")),
            _pos(On("f", "N")),
            _pos(On("a", "L")),
            _pos(On("d", "L")),
            _neg(Intersects("L", "N")),
            _pos(Equals(SegmentTerm("b", "c"), SegmentTerm("e", "f"))),
            _neg(Equals("b", "c")),
            _neg(Equals("e", "f")),
            _neg(On("a", "N")),
            _neg(On("d", "N")),
        ],
        exists_vars=[],
        conclusions=[
            _pos(Equals(AreaTerm("a", "b", "c"),
                        AreaTerm("d", "e", "f"))),
        ],
    ),
)


# ═══════════════════════════════════════════════════════════════════════
# Proposition I.39 — Equal triangles on the same base are between
# the same parallels.
# Depends on: I.31, I.37.
# ═══════════════════════════════════════════════════════════════════════

PROP_I_39 = ETheorem(
    name="Prop.I.39",
    statement=(
        "Equal triangles which are on the same base and on the same "
        "side are also in the same parallels."
    ),
    sequent=Sequent(
        hypotheses=[
            _pos(On("b", "N")),
            _pos(On("c", "N")),
            _neg(Equals("b", "c")),
            _neg(On("a", "N")),
            _neg(On("d", "N")),
            _pos(SameSide("a", "d", "N")),
            _pos(Equals(AreaTerm("a", "b", "c"),
                        AreaTerm("d", "b", "c"))),
            # L is the line through a and d
            _pos(On("a", "L")),
            _pos(On("d", "L")),
        ],
        exists_vars=[],
        conclusions=[
            # ad ∥ bc — the line through a,d doesn't intersect N
            _neg(Intersects("L", "N")),
        ],
    ),
)


# ═══════════════════════════════════════════════════════════════════════
# Proposition I.40 — Equal triangles on equal bases and on the
# same side are between the same parallels.
# Depends on: I.31, I.38.
# ═══════════════════════════════════════════════════════════════════════

PROP_I_40 = ETheorem(
    name="Prop.I.40",
    statement=(
        "Equal triangles which are on equal bases and on the same "
        "side are also in the same parallels."
    ),
    sequent=Sequent(
        hypotheses=[
            _pos(On("b", "N")),
            _pos(On("c", "N")),
            _pos(On("e", "N")),
            _pos(On("f", "N")),
            _neg(Equals("b", "c")),
            _neg(Equals("e", "f")),
            _neg(On("a", "N")),
            _neg(On("d", "N")),
            _pos(SameSide("a", "d", "N")),
            _pos(Equals(SegmentTerm("b", "c"), SegmentTerm("e", "f"))),
            _pos(Equals(AreaTerm("a", "b", "c"),
                        AreaTerm("d", "e", "f"))),
            # L is the line through a and d
            _pos(On("a", "L")),
            _pos(On("d", "L")),
        ],
        exists_vars=[],
        conclusions=[
            _neg(Intersects("L", "N")),
        ],
    ),
)


# ═══════════════════════════════════════════════════════════════════════
# Proposition I.41 — A parallelogram on the same base and between
# the same parallels is double the triangle.
# Depends on: I.34, I.37.
# ═══════════════════════════════════════════════════════════════════════

PROP_I_41 = ETheorem(
    name="Prop.I.41",
    statement=(
        "If a parallelogram have the same base with a triangle and "
        "be in the same parallels, the parallelogram is double of "
        "the triangle."
    ),
    sequent=Sequent(
        hypotheses=[
            # Parallelogram ABCD on base BC between parallels L, N
            _pos(On("b", "N")),
            _pos(On("c", "N")),
            _pos(On("a", "L")),
            _pos(On("d", "L")),
            _neg(Intersects("L", "N")),
            _neg(Equals("b", "c")),
            _neg(Equals("a", "d")),
            # Triangle EBC with E on L
            _pos(On("e", "L")),
            _neg(On("e", "N")),
        ],
        exists_vars=[],
        conclusions=[
            # Area(ABCD) = 2 × Area(EBC)
            _pos(Equals(
                MagAdd(AreaTerm("a", "b", "c"), AreaTerm("a", "c", "d")),
                MagAdd(AreaTerm("e", "b", "c"), AreaTerm("e", "b", "c")),
            )),
        ],
    ),
)


# ═══════════════════════════════════════════════════════════════════════
# Proposition I.42 — Construct a parallelogram equal to a given
# triangle in a given angle.
# Depends on: I.10, I.23, I.31, I.38, I.41.
# ═══════════════════════════════════════════════════════════════════════

PROP_I_42 = ETheorem(
    name="Prop.I.42",
    statement=(
        "To construct, in a given rectilineal angle, a parallelogram "
        "equal to a given triangle."
    ),
    sequent=Sequent(
        hypotheses=[
            # Given triangle abc and a given angle
            _neg(Equals("a", "b")),
            _neg(Equals("a", "c")),
            _neg(Equals("b", "c")),
            # The given angle magnitude
            _neg(Equals(AngleTerm("d", "e", "f"), ZeroMag(Sort.ANGLE))),
        ],
        exists_vars=[
            ("g", Sort.POINT),
            ("h", Sort.POINT),
        ],
        conclusions=[
            # Constructed parallelogram has equal area
            _pos(Equals(AreaTerm("a", "b", "c"),
                        MagAdd(AreaTerm("g", "h", "b"),
                               AreaTerm("g", "b", "c")))),
        ],
    ),
)


# ═══════════════════════════════════════════════════════════════════════
# Proposition I.43 — Complements of parallelograms about a diagonal
# are equal.
# Depends on: I.34, C.N.
# ═══════════════════════════════════════════════════════════════════════

PROP_I_43 = ETheorem(
    name="Prop.I.43",
    statement=(
        "In any parallelogram the complements of the parallelograms "
        "about the diagonal are equal to one another."
    ),
    sequent=Sequent(
        hypotheses=[
            # Parallelogram ABCD with diagonal AC, point K on AC
            _pos(On("a", "L")),
            _pos(On("b", "L")),
            _pos(On("c", "N")),
            _pos(On("d", "N")),
            _neg(Intersects("L", "N")),
            _pos(On("a", "M")),
            _pos(On("d", "M")),
            _pos(On("b", "P")),
            _pos(On("c", "P")),
            _neg(Intersects("M", "P")),
            _pos(Between("a", "k", "c")),
            _neg(Equals("a", "b")),
            _neg(Equals("c", "d")),
        ],
        exists_vars=[],
        conclusions=[
            # Complement area equality
            _pos(Equals(AreaTerm("a", "k", "b"),
                        AreaTerm("k", "c", "d"))),
        ],
    ),
)


# ═══════════════════════════════════════════════════════════════════════
# Proposition I.44 — Apply a parallelogram equal to a given triangle
# on a given line in a given angle.
# Depends on: I.29, I.31, I.42, I.43. Uses parallel postulate.
# ═══════════════════════════════════════════════════════════════════════

PROP_I_44 = ETheorem(
    name="Prop.I.44",
    statement=(
        "To a given straight line to apply, in a given rectilineal "
        "angle, a parallelogram equal to a given triangle."
    ),
    sequent=Sequent(
        hypotheses=[
            # Given segment ab, triangle c, and angle d
            _pos(On("a", "L")),
            _pos(On("b", "L")),
            _neg(Equals("a", "b")),
            _neg(Equals("c", "d")),
            _neg(Equals("c", "e")),
            _neg(Equals("d", "e")),
        ],
        exists_vars=[
            ("f", Sort.POINT),
            ("g", Sort.POINT),
        ],
        conclusions=[
            # Parallelogram on AB with equal area
            _pos(On("f", "L")),
        ],
    ),
)


# ═══════════════════════════════════════════════════════════════════════
# Proposition I.45 — Construct a parallelogram equal to a given
# rectilineal figure in a given angle.
# Depends on: I.42, I.44. Uses parallel postulate.
# ═══════════════════════════════════════════════════════════════════════

PROP_I_45 = ETheorem(
    name="Prop.I.45",
    statement=(
        "To construct, in a given rectilineal angle, a parallelogram "
        "equal to a given rectilineal figure."
    ),
    sequent=Sequent(
        hypotheses=[
            _neg(Equals("a", "b")),
            _neg(Equals("a", "c")),
            _neg(Equals("b", "c")),
            _neg(Equals("a", "d")),
            _neg(Equals(AngleTerm("e", "f", "g"), ZeroMag(Sort.ANGLE))),
        ],
        exists_vars=[
            ("h", Sort.POINT),
            ("k", Sort.POINT),
            ("m", Sort.POINT),
        ],
        conclusions=[
            # Constructed parallelogram has the desired area
            _pos(Equals(
                MagAdd(AreaTerm("a", "b", "c"), AreaTerm("a", "c", "d")),
                MagAdd(AreaTerm("h", "k", "m"), AreaTerm("h", "m", "b")),
            )),
        ],
    ),
)


# ═══════════════════════════════════════════════════════════════════════
# Proposition I.46 — Construct a square on a given straight line.
# Depends on: I.11, I.3, I.31, I.29, I.34.
# ═══════════════════════════════════════════════════════════════════════

PROP_I_46 = ETheorem(
    name="Prop.I.46",
    statement=(
        "On a given straight line to describe a square."
    ),
    sequent=Sequent(
        hypotheses=[
            _pos(On("a", "L")),
            _pos(On("b", "L")),
            _neg(Equals("a", "b")),
        ],
        exists_vars=[
            ("c", Sort.POINT),
            ("d", Sort.POINT),
        ],
        conclusions=[
            # All four sides equal
            _pos(Equals(SegmentTerm("a", "b"), SegmentTerm("b", "c"))),
            _pos(Equals(SegmentTerm("b", "c"), SegmentTerm("c", "d"))),
            _pos(Equals(SegmentTerm("c", "d"), SegmentTerm("d", "a"))),
            # All four angles are right angles
            _pos(Equals(AngleTerm("d", "a", "b"), RightAngle())),
            _pos(Equals(AngleTerm("a", "b", "c"), RightAngle())),
            _pos(Equals(AngleTerm("b", "c", "d"), RightAngle())),
            _pos(Equals(AngleTerm("c", "d", "a"), RightAngle())),
        ],
    ),
)


# ═══════════════════════════════════════════════════════════════════════
# Proposition I.47 — The Pythagorean Theorem
#
# In right-angled triangles the square on the side subtending the
# right angle is equal to the squares on the sides containing
# the right angle.
# Depends on: I.4, I.14, I.41, I.46, C.N.
# ═══════════════════════════════════════════════════════════════════════

PROP_I_47 = ETheorem(
    name="Prop.I.47",
    statement=(
        "In right-angled triangles the square on the side subtending "
        "the right angle is equal to the squares on the sides "
        "containing the right angle."
    ),
    sequent=Sequent(
        hypotheses=[
            # Right-angled triangle: ∠bac = right angle
            _neg(Equals("a", "b")),
            _neg(Equals("a", "c")),
            _neg(Equals("b", "c")),
            _pos(Equals(AngleTerm("b", "a", "c"), RightAngle())),
        ],
        exists_vars=[
            # Square BDEC on hypotenuse BC
            ("d", Sort.POINT), ("e", Sort.POINT),
            # Square ABFG on side AB
            ("f", Sort.POINT), ("g", Sort.POINT),
            # Square ACHK on side AC
            ("h", Sort.POINT), ("k", Sort.POINT),
        ],
        conclusions=[
            # Square BDEC on BC: 4 equal sides + right angle at corner
            _pos(Equals(SegmentTerm("b", "c"), SegmentTerm("c", "d"))),
            _pos(Equals(SegmentTerm("c", "d"), SegmentTerm("d", "e"))),
            _pos(Equals(SegmentTerm("d", "e"), SegmentTerm("e", "b"))),
            _pos(Equals(AngleTerm("c", "b", "e"), RightAngle())),
            # Square ABFG on AB: 4 equal sides + right angle at corner
            _pos(Equals(SegmentTerm("a", "b"), SegmentTerm("b", "f"))),
            _pos(Equals(SegmentTerm("b", "f"), SegmentTerm("f", "g"))),
            _pos(Equals(SegmentTerm("f", "g"), SegmentTerm("g", "a"))),
            _pos(Equals(AngleTerm("a", "b", "f"), RightAngle())),
            # Square ACHK on AC: 4 equal sides + right angle at corner
            _pos(Equals(SegmentTerm("a", "c"), SegmentTerm("c", "h"))),
            _pos(Equals(SegmentTerm("c", "h"), SegmentTerm("h", "k"))),
            _pos(Equals(SegmentTerm("h", "k"), SegmentTerm("k", "a"))),
            _pos(Equals(AngleTerm("c", "a", "k"), RightAngle())),
            # Area equality: square on BC = square on AB + square on AC
            # Each square area = sum of 2 triangles from diagonal
            # BDEC diagonal DC: △bdc + △dec
            # ABFG diagonal af: △abf + △afg
            # ACHK diagonal ah: △ach + △ahk
            _pos(Equals(
                MagAdd(AreaTerm("b", "d", "c"), AreaTerm("d", "e", "c")),
                MagAdd(
                    MagAdd(AreaTerm("a", "b", "f"), AreaTerm("a", "f", "g")),
                    MagAdd(AreaTerm("a", "c", "h"), AreaTerm("a", "h", "k")),
                ),
            )),
        ],
    ),
)


# ═══════════════════════════════════════════════════════════════════════
# Proposition I.48 — Converse of the Pythagorean Theorem
#
# If in a triangle the square on one of the sides is equal to
# the squares on the remaining two sides, the angle contained
# by the remaining two sides is a right angle.
# Depends on: I.3, I.8, I.11, I.46, I.47.
# ═══════════════════════════════════════════════════════════════════════

PROP_I_48 = ETheorem(
    name="Prop.I.48",
    statement=(
        "If in a triangle the square on one of the sides be equal to "
        "the squares on the remaining two sides of the triangle, the "
        "angle contained by the remaining two sides of the triangle "
        "is right."
    ),
    sequent=Sequent(
        hypotheses=[
            _neg(Equals("a", "b")),
            _neg(Equals("a", "c")),
            _neg(Equals("b", "c")),
            # Squares constructed on all three sides (via I.46)
            # Square BDEC on BC
            _pos(Equals(SegmentTerm("b", "c"), SegmentTerm("c", "d"))),
            _pos(Equals(SegmentTerm("c", "d"), SegmentTerm("d", "e"))),
            _pos(Equals(SegmentTerm("d", "e"), SegmentTerm("e", "b"))),
            _pos(Equals(AngleTerm("c", "b", "e"), RightAngle())),
            # Square ABFG on AB
            _pos(Equals(SegmentTerm("a", "b"), SegmentTerm("b", "f"))),
            _pos(Equals(SegmentTerm("b", "f"), SegmentTerm("f", "g"))),
            _pos(Equals(SegmentTerm("f", "g"), SegmentTerm("g", "a"))),
            # Square ACHK on AC
            _pos(Equals(SegmentTerm("a", "c"), SegmentTerm("c", "h"))),
            _pos(Equals(SegmentTerm("c", "h"), SegmentTerm("h", "k"))),
            _pos(Equals(SegmentTerm("h", "k"), SegmentTerm("k", "a"))),
            # Pythagorean condition: area of square on BC = sum of areas
            # of squares on AB and AC
            _pos(Equals(
                MagAdd(AreaTerm("b", "d", "c"), AreaTerm("d", "e", "c")),
                MagAdd(
                    MagAdd(AreaTerm("a", "b", "f"), AreaTerm("a", "f", "g")),
                    MagAdd(AreaTerm("a", "c", "h"), AreaTerm("a", "h", "k")),
                ),
            )),
        ],
        exists_vars=[],
        conclusions=[
            _pos(Equals(AngleTerm("b", "a", "c"), RightAngle())),
        ],
    ),
)


# ═══════════════════════════════════════════════════════════════════════
# Theorem catalogue
# ═══════════════════════════════════════════════════════════════════════

E_THEOREM_LIBRARY: Dict[str, ETheorem] = {
    "Prop.I.1": PROP_I_1,
    "Prop.I.2": PROP_I_2,
    "Prop.I.3": PROP_I_3,
    "Prop.I.4": PROP_I_4,
    "Prop.I.5": PROP_I_5,
    "Prop.I.6": PROP_I_6,
    "Prop.I.7": PROP_I_7,
    "Prop.I.8": PROP_I_8,
    "Prop.I.9": PROP_I_9,
    "Prop.I.10": PROP_I_10,
    "Prop.I.11": PROP_I_11,
    "Prop.I.12": PROP_I_12,
    "Prop.I.13": PROP_I_13,
    "Prop.I.14": PROP_I_14,
    "Prop.I.15": PROP_I_15,
    "Prop.I.16": PROP_I_16,
    "Prop.I.17": PROP_I_17,
    "Prop.I.18": PROP_I_18,
    "Prop.I.19": PROP_I_19,
    "Prop.I.20": PROP_I_20,
    "Prop.I.21": PROP_I_21,
    "Prop.I.22": PROP_I_22,
    "Prop.I.23": PROP_I_23,
    "Prop.I.24": PROP_I_24,
    "Prop.I.25": PROP_I_25,
    "Prop.I.26": PROP_I_26,
    "Prop.I.27": PROP_I_27,
    "Prop.I.28": PROP_I_28,
    "Prop.I.29": PROP_I_29,
    "Prop.I.30": PROP_I_30,
    "Prop.I.31": PROP_I_31,
    "Prop.I.32": PROP_I_32,
    "Prop.I.33": PROP_I_33,
    "Prop.I.34": PROP_I_34,
    "Prop.I.35": PROP_I_35,
    "Prop.I.36": PROP_I_36,
    "Prop.I.37": PROP_I_37,
    "Prop.I.38": PROP_I_38,
    "Prop.I.39": PROP_I_39,
    "Prop.I.40": PROP_I_40,
    "Prop.I.41": PROP_I_41,
    "Prop.I.42": PROP_I_42,
    "Prop.I.43": PROP_I_43,
    "Prop.I.44": PROP_I_44,
    "Prop.I.45": PROP_I_45,
    "Prop.I.46": PROP_I_46,
    "Prop.I.47": PROP_I_47,
    "Prop.I.48": PROP_I_48,
}


def get_theorems_up_to(prop_name: str) -> Dict[str, ETheorem]:
    """Return the theorem library containing all theorems up to but not
    including the given proposition.

    This is used when checking a proof of `prop_name` — the prover can
    appeal to any earlier proposition but not to the one being proved.
    """
    ordered_names = [
        "Prop.I.1", "Prop.I.2", "Prop.I.3", "Prop.I.4",
        "Prop.I.5", "Prop.I.6", "Prop.I.7", "Prop.I.8",
        "Prop.I.9", "Prop.I.10",
        "Prop.I.11", "Prop.I.12", "Prop.I.13", "Prop.I.14",
        "Prop.I.15", "Prop.I.16", "Prop.I.17", "Prop.I.18",
        "Prop.I.19", "Prop.I.20",
        "Prop.I.21", "Prop.I.22", "Prop.I.23", "Prop.I.24",
        "Prop.I.25", "Prop.I.26",
        "Prop.I.27", "Prop.I.28", "Prop.I.29", "Prop.I.30",
        "Prop.I.31", "Prop.I.32",
        "Prop.I.33", "Prop.I.34", "Prop.I.35", "Prop.I.36",
        "Prop.I.37", "Prop.I.38", "Prop.I.39", "Prop.I.40",
        "Prop.I.41", "Prop.I.42", "Prop.I.43", "Prop.I.44",
        "Prop.I.45", "Prop.I.46", "Prop.I.47", "Prop.I.48",
    ]
    result: Dict[str, ETheorem] = {}
    for name in ordered_names:
        if name == prop_name:
            break
        if name in E_THEOREM_LIBRARY:
            result[name] = E_THEOREM_LIBRARY[name]
    return result
