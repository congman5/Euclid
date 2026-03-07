"""
e_construction.py — Construction rules for System E (Section 3.3).

Each construction rule is a built-in sequent of the form:
    Γ_prerequisites ⇒ ∃x̄. Δ_conclusions

These rules introduce new geometric objects (points, lines, circles)
into the diagram.  They are the *only* way to introduce new objects;
demonstration steps can only derive new assertions about existing objects.

Reference: Avigad, Dean, Mumma (2009), Section 3.3.
"""
from __future__ import annotations

from dataclasses import dataclass, field
from typing import List, Tuple

from .e_ast import (
    Sort, Literal,
    On, SameSide, Between, Center, Inside, Intersects, Equals,
    ConstructionRule,
)


def _pos(atom):
    """Positive literal."""
    return Literal(atom, polarity=True)


def _neg(atom):
    """Negative literal."""
    return Literal(atom, polarity=False)


# ═══════════════════════════════════════════════════════════════════════
# Point construction rules  (Section 3.3, Points 1–9)
# ═══════════════════════════════════════════════════════════════════════

POINT_RULES: List[ConstructionRule] = [
    # 1. Let a be a point [distinct from ...].
    #    Prerequisites: none
    #    Conclusion: [a is distinct from ...]
    ConstructionRule(
        name="let-point",
        category="point",
        prereq_pattern=[],
        new_vars=[("a", Sort.POINT)],
        conclusion_pattern=[],
        # Distinctness is handled dynamically at application time
    ),

    # 2. Let a be a point on L [distinct from ...].
    #    Prerequisites: [L is distinct from lines ...]
    #    Conclusion: on(a, L), [a is distinct from ...]
    ConstructionRule(
        name="let-point-on-line",
        category="point",
        prereq_pattern=[],  # L distinct from lines handled dynamically
        new_vars=[("a", Sort.POINT)],
        conclusion_pattern=[_pos(On("a", "L"))],
    ),

    # 3. Let a be a point on L between b and c.
    #    Prerequisites: on(b, L), on(c, L), b ≠ c
    #    Conclusion: on(a, L), between(b, a, c)
    #    NOTE: the paper says "a is between b and c", meaning between(b,a,c)
    ConstructionRule(
        name="let-point-on-line-between",
        category="point",
        prereq_pattern=[
            _pos(On("b", "L")),
            _pos(On("c", "L")),
            _neg(Equals("b", "c")),
        ],
        new_vars=[("a", Sort.POINT)],
        conclusion_pattern=[
            _pos(On("a", "L")),
            _pos(Between("b", "a", "c")),
        ],
    ),

    # 4. Let a be a point on L extending the segment from b to c.
    #    Prerequisites: on(b, L), on(c, L), b ≠ c
    #    Conclusion: on(a, L), between(b, c, a)
    ConstructionRule(
        name="let-point-on-line-extend",
        category="point",
        prereq_pattern=[
            _pos(On("b", "L")),
            _pos(On("c", "L")),
            _neg(Equals("b", "c")),
        ],
        new_vars=[("a", Sort.POINT)],
        conclusion_pattern=[
            _pos(On("a", "L")),
            _pos(Between("b", "c", "a")),
        ],
    ),

    # 5. Let a be a point on the same side of L as b.
    #    Prerequisite: ¬on(b, L)
    #    Conclusion: same-side(a, b, L)
    ConstructionRule(
        name="let-point-same-side",
        category="point",
        prereq_pattern=[
            _neg(On("b", "L")),
        ],
        new_vars=[("a", Sort.POINT)],
        conclusion_pattern=[
            _pos(SameSide("a", "b", "L")),
        ],
    ),

    # 6. Let a be a point on the side of L opposite b.
    #    Prerequisite: ¬on(b, L)
    #    Conclusion: ¬on(a, L), ¬same-side(a, b, L)
    ConstructionRule(
        name="let-point-opposite-side",
        category="point",
        prereq_pattern=[
            _neg(On("b", "L")),
        ],
        new_vars=[("a", Sort.POINT)],
        conclusion_pattern=[
            _neg(On("a", "L")),
            _neg(SameSide("a", "b", "L")),
        ],
    ),

    # 7. Let a be a point on α.
    #    Prerequisite: [α distinct from other circles]
    #    Conclusion: on(a, α)
    ConstructionRule(
        name="let-point-on-circle",
        category="point",
        prereq_pattern=[],
        new_vars=[("a", Sort.POINT)],
        conclusion_pattern=[
            _pos(On("a", "\u03b1")),
        ],
    ),

    # 8. Let a be a point inside α.
    #    Prerequisites: none
    #    Conclusion: inside(a, α)
    ConstructionRule(
        name="let-point-inside-circle",
        category="point",
        prereq_pattern=[],
        new_vars=[("a", Sort.POINT)],
        conclusion_pattern=[
            _pos(Inside("a", "\u03b1")),
        ],
    ),

    # 9. Let a be a point outside α.
    #    Prerequisites: none
    #    Conclusion: ¬inside(a, α), ¬on(a, α)
    ConstructionRule(
        name="let-point-outside-circle",
        category="point",
        prereq_pattern=[],
        new_vars=[("a", Sort.POINT)],
        conclusion_pattern=[
            _neg(Inside("a", "\u03b1")),
            _neg(On("a", "\u03b1")),
        ],
    ),
]


# ═══════════════════════════════════════════════════════════════════════
# Line and circle construction rules  (Section 3.3, Lines/Circles 1–2)
# ═══════════════════════════════════════════════════════════════════════

LINE_CIRCLE_RULES: List[ConstructionRule] = [
    # 1. Let L be the line through a and b.
    #    Prerequisite: a ≠ b
    #    Conclusion: on(a, L), on(b, L)
    ConstructionRule(
        name="let-line",
        category="line_circle",
        prereq_pattern=[
            _neg(Equals("a", "b")),
        ],
        new_vars=[("L", Sort.LINE)],
        conclusion_pattern=[
            _pos(On("a", "L")),
            _pos(On("b", "L")),
        ],
    ),

    # 2. Let α be the circle with center a passing through b.
    #    Prerequisite: a ≠ b
    #    Conclusion: center(a, α), on(b, α)
    ConstructionRule(
        name="let-circle",
        category="line_circle",
        prereq_pattern=[
            _neg(Equals("a", "b")),
        ],
        new_vars=[("\u03b1", Sort.CIRCLE)],
        conclusion_pattern=[
            _pos(Center("a", "\u03b1")),
            _pos(On("b", "\u03b1")),
        ],
    ),
]


# ═══════════════════════════════════════════════════════════════════════
# Intersection construction rules  (Section 3.3, Intersections 1–9)
# ═══════════════════════════════════════════════════════════════════════

INTERSECTION_RULES: List[ConstructionRule] = [
    # 1. Let a be the intersection of L and M.
    #    Prerequisite: intersects(L, M)
    #    Conclusion: on(a, L), on(a, M)
    ConstructionRule(
        name="let-intersection-line-line",
        category="intersection",
        prereq_pattern=[
            _pos(Intersects("L", "M")),
        ],
        new_vars=[("a", Sort.POINT)],
        conclusion_pattern=[
            _pos(On("a", "L")),
            _pos(On("a", "M")),
        ],
    ),

    # 2. Let a be a point of intersection of α and L.
    #    Prerequisite: intersects(α, L)   [or intersects(L, α)]
    #    Conclusion: on(a, α), on(a, L)
    ConstructionRule(
        name="let-intersection-circle-line-one",
        category="intersection",
        prereq_pattern=[
            _pos(Intersects("\u03b1", "L")),
        ],
        new_vars=[("a", Sort.POINT)],
        conclusion_pattern=[
            _pos(On("a", "\u03b1")),
            _pos(On("a", "L")),
        ],
    ),

    # 3. Let a and b be the two points of intersection of α and L.
    #    Prerequisite: intersects(α, L)
    #    Conclusion: on(a, α), on(a, L), on(b, α), on(b, L), a ≠ b
    ConstructionRule(
        name="let-intersection-circle-line-two",
        category="intersection",
        prereq_pattern=[
            _pos(Intersects("\u03b1", "L")),
        ],
        new_vars=[("a", Sort.POINT), ("b", Sort.POINT)],
        conclusion_pattern=[
            _pos(On("a", "\u03b1")),
            _pos(On("a", "L")),
            _pos(On("b", "\u03b1")),
            _pos(On("b", "L")),
            _neg(Equals("a", "b")),
        ],
    ),

    # 4. Let a be the point of intersection of L and α between b and c.
    #    Prerequisites: inside(b, α), on(b, L), ¬inside(c, α),
    #                   ¬on(c, α), on(c, L)
    #    Conclusion: on(a, α), on(a, L), between(b, a, c)
    ConstructionRule(
        name="let-intersection-line-circle-between",
        category="intersection",
        prereq_pattern=[
            _pos(Inside("b", "\u03b1")),
            _pos(On("b", "L")),
            _neg(Inside("c", "\u03b1")),
            _neg(On("c", "\u03b1")),
            _pos(On("c", "L")),
        ],
        new_vars=[("a", Sort.POINT)],
        conclusion_pattern=[
            _pos(On("a", "\u03b1")),
            _pos(On("a", "L")),
            _pos(Between("b", "a", "c")),
        ],
    ),

    # 5. Let a be the point of intersection of L and α extending from c to b.
    #    Prerequisites: inside(b, α), on(b, L), c ≠ b, on(c, L)
    #    Conclusion: on(a, α), on(a, L), between(a, b, c)
    #    NOTE: paper says "b is between a and c"
    ConstructionRule(
        name="let-intersection-line-circle-extend",
        category="intersection",
        prereq_pattern=[
            _pos(Inside("b", "\u03b1")),
            _pos(On("b", "L")),
            _neg(Equals("c", "b")),
            _pos(On("c", "L")),
        ],
        new_vars=[("a", Sort.POINT)],
        conclusion_pattern=[
            _pos(On("a", "\u03b1")),
            _pos(On("a", "L")),
            _pos(Between("a", "b", "c")),
        ],
    ),

    # 6. Let a be a point on the intersection of α and β.
    #    Prerequisite: intersects(α, β)
    #    Conclusion: on(a, α), on(a, β)
    ConstructionRule(
        name="let-intersection-circle-circle-one",
        category="intersection",
        prereq_pattern=[
            _pos(Intersects("\u03b1", "\u03b2")),
        ],
        new_vars=[("a", Sort.POINT)],
        conclusion_pattern=[
            _pos(On("a", "\u03b1")),
            _pos(On("a", "\u03b2")),
        ],
    ),

    # 7. Let a and b be the two points of intersection of α and β.
    #    Prerequisite: intersects(α, β)
    #    Conclusion: on(a, α), on(a, β), on(b, α), on(b, β), a ≠ b
    ConstructionRule(
        name="let-intersection-circle-circle-two",
        category="intersection",
        prereq_pattern=[
            _pos(Intersects("\u03b1", "\u03b2")),
        ],
        new_vars=[("a", Sort.POINT), ("b", Sort.POINT)],
        conclusion_pattern=[
            _pos(On("a", "\u03b1")),
            _pos(On("a", "\u03b2")),
            _pos(On("b", "\u03b1")),
            _pos(On("b", "\u03b2")),
            _neg(Equals("a", "b")),
        ],
    ),

    # 8. Let a be the intersection of α and β on the same side of L as b.
    #    Prerequisites: intersects(α, β), center(c, α), center(d, β),
    #                   on(c, L), on(d, L), ¬on(b, L)
    #    Conclusion: on(a, α), on(a, β), same-side(a, b, L)
    ConstructionRule(
        name="let-intersection-circle-circle-same-side",
        category="intersection",
        prereq_pattern=[
            _pos(Intersects("\u03b1", "\u03b2")),
            _pos(Center("c", "\u03b1")),
            _pos(Center("d", "\u03b2")),
            _pos(On("c", "L")),
            _pos(On("d", "L")),
            _neg(On("b", "L")),
        ],
        new_vars=[("a", Sort.POINT)],
        conclusion_pattern=[
            _pos(On("a", "\u03b1")),
            _pos(On("a", "\u03b2")),
            _pos(SameSide("a", "b", "L")),
        ],
    ),

    # 9. Let a be the intersection of α and β on the side of L opposite b.
    #    Prerequisites: intersects(α, β), center(c, α), center(d, β),
    #                   on(c, L), on(d, L), ¬on(b, L)
    #    Conclusion: on(a, α), on(a, β), ¬same-side(a, b, L), ¬on(a, L)
    ConstructionRule(
        name="let-intersection-circle-circle-opposite-side",
        category="intersection",
        prereq_pattern=[
            _pos(Intersects("\u03b1", "\u03b2")),
            _pos(Center("c", "\u03b1")),
            _pos(Center("d", "\u03b2")),
            _pos(On("c", "L")),
            _pos(On("d", "L")),
            _neg(On("b", "L")),
        ],
        new_vars=[("a", Sort.POINT)],
        conclusion_pattern=[
            _pos(On("a", "\u03b1")),
            _pos(On("a", "\u03b2")),
            _neg(SameSide("a", "b", "L")),
            _neg(On("a", "L")),
        ],
    ),
]


# ═══════════════════════════════════════════════════════════════════════
# All construction rules
# ═══════════════════════════════════════════════════════════════════════

ALL_CONSTRUCTION_RULES: List[ConstructionRule] = (
    POINT_RULES + LINE_CIRCLE_RULES + INTERSECTION_RULES
)

# Index by name for fast lookup
CONSTRUCTION_RULE_BY_NAME = {r.name: r for r in ALL_CONSTRUCTION_RULES}
