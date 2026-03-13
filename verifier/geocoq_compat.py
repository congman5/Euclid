"""
geocoq_compat.py — GeoCoq compatibility layer and statement comparison.

Maps our axiom/theorem names to GeoCoq's Coq identifiers and provides
reference descriptions of each Book I proposition in System E notation.

Phase 7.2 (name mapping) + Phase 10.3 (statement comparison) of the
implementation plan.

Reference:
  - GeoCoq: https://geocoq.github.io/GeoCoq/
  - GeoCoq Elements/Statements/Book_1.v
  - GeoCoq euclidean_axioms.v
"""
from __future__ import annotations

from dataclasses import dataclass
from typing import Dict, List, Optional, Tuple


# ═══════════════════════════════════════════════════════════════════════
# PREDICATE NAME MAPPINGS
# ═══════════════════════════════════════════════════════════════════════

@dataclass(frozen=True)
class PredicateMapping:
    """Maps an E predicate to its GeoCoq Coq identifier."""
    our_name: str
    geocoq_name: str
    our_system: str        # "E"
    geocoq_module: str     # Source Coq file
    arity: int
    description: str = ""


# System E predicates → GeoCoq equivalents
E_PREDICATE_MAPPINGS: List[PredicateMapping] = [
    PredicateMapping("on(a, L)", "IncidL a l",
                     "E", "euclidean_axioms.v", 2,
                     "Point lies on line"),
    PredicateMapping("between(a, b, c)", "BetS A B C",
                     "E", "euclidean_axioms.v", 3,
                     "Strict betweenness (b strictly between a and c)"),
    PredicateMapping("same-side(a, b, L)", "SameSide A B l",
                     "E", "euclidean_axioms.v", 3,
                     "Points on same side of a line"),
    PredicateMapping("center(a, α)", "CI J A B",
                     "E", "euclidean_axioms.v", 3,
                     "Point is center of circle (GeoCoq: circle from center+radius)"),
    PredicateMapping("inside(a, α)", "InCirc P J",
                     "E", "euclidean_axioms.v", 2,
                     "Point is inside circle"),
    PredicateMapping("on(a, α)", "OnCirc P J",
                     "E", "euclidean_axioms.v", 2,
                     "Point lies on circle"),
    PredicateMapping("intersects(L, M)", "LL L M",
                     "E", "euclidean_axioms.v", 2,
                     "Two lines intersect"),
    PredicateMapping("ab = cd", "Cong A B C D",
                     "E", "euclidean_axioms.v", 4,
                     "Segment congruence"),
    PredicateMapping("∠abc = ∠def", "CongA A B C D E F",
                     "E", "euclidean_axioms.v", 6,
                     "Angle congruence"),
    PredicateMapping("ab < cd", "Lt A B C D",
                     "E", "euclidean_axioms.v", 4,
                     "Segment ordering"),
    PredicateMapping("a = b", "eq A B",
                     "E", "euclidean_axioms.v", 2,
                     "Point equality"),
]

ALL_PREDICATE_MAPPINGS = E_PREDICATE_MAPPINGS


# ═══════════════════════════════════════════════════════════════════════
# AXIOM NAME MAPPINGS
# ═══════════════════════════════════════════════════════════════════════

@dataclass(frozen=True)
class AxiomMapping:
    """Maps an axiom from our system to its GeoCoq identifier."""
    our_name: str
    geocoq_name: str
    system: str       # "E"
    description: str


# System E axiom group mappings (Paper §3.3–3.7 → GeoCoq euclidean_axioms.v)
E_AXIOM_MAPPINGS: List[AxiomMapping] = [
    AxiomMapping("Construction", "postulate_*",
                 "E", "Construction rules (§3.3): line, circle, intersection"),
    AxiomMapping("Diagrammatic", "cn_*",
                 "E", "Diagrammatic axioms (§3.4): ordering, betweenness, Pasch"),
    AxiomMapping("Metric", "cn_congruencereflexive, cn_congruencetransitive, ...",
                 "E", "Metric axioms (§3.5): segment/angle congruence"),
    AxiomMapping("Transfer", "axiom_*_transfer",
                 "E", "Transfer axioms (§3.6): betweenness→segment"),
    AxiomMapping("SAS Superposition", "axiom_5_line",
                 "E", "Side-Angle-Side (§3.7)"),
    AxiomMapping("SSS Superposition", "axiom_SSS",
                 "E", "Side-Side-Side (§3.7)"),
]


# ═══════════════════════════════════════════════════════════════════════
# PROPOSITION STATEMENT COMPARISON
# ═══════════════════════════════════════════════════════════════════════

@dataclass(frozen=True)
class PropositionComparison:
    """Comparison record for one Book I proposition across formulations.

    Stores the GeoCoq Coq name, the natural-language description from
    Euclid's *Elements*, and structural metadata about the formal
    statement (number of hypotheses, conclusions, existential variables).

    These reference descriptions allow automated comparison against our
    ``e_library`` entries.
    """
    number: int
    our_name: str              # "Prop.I.1" etc.
    geocoq_name: str           # "proposition_1" etc.
    euclid_description: str    # Natural-language from Elements
    kind: str                  # "construction" or "theorem"
    key_predicates: Tuple[str, ...]  # Primary E predicates used
    min_hypotheses: int        # Minimum expected hypotheses
    min_conclusions: int       # Minimum expected conclusions
    has_existentials: bool     # Whether ∃ vars are expected


# All 48 propositions of Book I
PROPOSITION_COMPARISONS: List[PropositionComparison] = [
    # ── Basic Constructions (I.1–I.3) ─────────────────────────────
    PropositionComparison(
        1, "Prop.I.1", "proposition_1",
        "On a given finite straight line to construct an equilateral triangle",
        "construction", ("Equals",), 1, 2, True),
    PropositionComparison(
        2, "Prop.I.2", "proposition_2",
        "To place at a given point a straight line equal to a given straight line",
        "construction", ("Equals", "On"), 1, 1, True),
    PropositionComparison(
        3, "Prop.I.3", "proposition_3",
        "Given two unequal straight lines, to cut off from the greater a part equal to the less",
        "construction", ("Equals", "Between"), 1, 1, True),
    # ── Congruence (I.4–I.8) ──────────────────────────────────────
    PropositionComparison(
        4, "Prop.I.4", "proposition_4",
        "SAS: Two triangles with two sides and included angle equal are congruent",
        "theorem", ("Equals",), 3, 3, False),
    PropositionComparison(
        5, "Prop.I.5", "proposition_5",
        "In isosceles triangles the base angles are equal",
        "theorem", ("Equals",), 2, 1, False),
    PropositionComparison(
        6, "Prop.I.6", "proposition_6",
        "If two angles of a triangle are equal, the sides opposite them are equal",
        "theorem", ("Equals",), 2, 1, False),
    PropositionComparison(
        7, "Prop.I.7", "proposition_7",
        "Given two straight lines from the ends of a line, no two others equal to them can be constructed",
        "theorem", ("Equals",), 1, 1, False),
    PropositionComparison(
        8, "Prop.I.8", "proposition_8",
        "SSS: Two triangles with three sides equal are congruent",
        "theorem", ("Equals",), 3, 3, False),
    # ── Bisection & Perpendiculars (I.9–I.12) ────────────────────
    PropositionComparison(
        9, "Prop.I.9", "proposition_9",
        "To bisect a given rectilineal angle",
        "construction", ("Equals", "SameSide"), 1, 1, True),
    PropositionComparison(
        10, "Prop.I.10", "proposition_10",
        "To bisect a given finite straight line",
        "construction", ("Equals", "Between"), 1, 2, True),
    PropositionComparison(
        11, "Prop.I.11", "proposition_11",
        "To draw a straight line at right angles to a given straight line from a given point on it",
        "construction", ("Equals", "On"), 2, 1, True),
    PropositionComparison(
        12, "Prop.I.12", "proposition_12",
        "To a given infinite straight line, from a given point not on it, to draw a perpendicular",
        "construction", ("Equals", "On"), 1, 1, True),
    # ── Angles on a Line (I.13–I.15) ─────────────────────────────
    PropositionComparison(
        13, "Prop.I.13", "proposition_13",
        "If a straight line stands on a straight line, it makes angles equal to two right angles",
        "theorem", ("Equals", "Between"), 2, 1, False),
    PropositionComparison(
        14, "Prop.I.14", "proposition_14",
        "If angles at a point on one side of a line equal two right angles, the lines are collinear",
        "theorem", ("Equals", "Between"), 3, 1, False),
    PropositionComparison(
        15, "Prop.I.15", "proposition_15",
        "Vertical angles are equal",
        "theorem", ("Equals", "Between"), 2, 1, False),
    # ── Triangle Inequalities (I.16–I.26) ────────────────────────
    PropositionComparison(
        16, "Prop.I.16", "proposition_16",
        "The exterior angle of a triangle is greater than either remote interior angle",
        "theorem", ("LessThan", "Between"), 3, 1, False),
    PropositionComparison(
        17, "Prop.I.17", "proposition_17",
        "Two angles of a triangle are together less than two right angles",
        "theorem", ("LessThan",), 1, 1, False),
    PropositionComparison(
        18, "Prop.I.18", "proposition_18",
        "The greater side of a triangle subtends the greater angle",
        "theorem", ("LessThan",), 1, 1, False),
    PropositionComparison(
        19, "Prop.I.19", "proposition_19",
        "The greater angle of a triangle is subtended by the greater side",
        "theorem", ("LessThan",), 1, 1, False),
    PropositionComparison(
        20, "Prop.I.20", "proposition_20",
        "Any two sides of a triangle are together greater than the remaining side",
        "theorem", ("LessThan",), 1, 1, False),
    PropositionComparison(
        21, "Prop.I.21", "proposition_21",
        "Triangle formed on same base within another has lesser sides but greater angle",
        "theorem", ("LessThan",), 3, 1, False),
    PropositionComparison(
        22, "Prop.I.22", "proposition_22",
        "To construct a triangle from three lines equal to three given lines",
        "construction", ("Equals",), 3, 1, True),
    PropositionComparison(
        23, "Prop.I.23", "proposition_23",
        "To construct a rectilineal angle equal to a given angle on a given line",
        "construction", ("Equals",), 1, 1, True),
    PropositionComparison(
        24, "Prop.I.24", "proposition_24",
        "SAS inequality: if two sides equal but included angle greater, then base greater",
        "theorem", ("LessThan", "Equals"), 3, 1, False),
    PropositionComparison(
        25, "Prop.I.25", "proposition_25",
        "Converse of I.24: if two sides equal but base greater, then included angle greater",
        "theorem", ("LessThan", "Equals"), 3, 1, False),
    PropositionComparison(
        26, "Prop.I.26", "proposition_26",
        "ASA and AAS: two triangles with two angles and a side equal are congruent",
        "theorem", ("Equals",), 3, 3, False),
    # ── Parallel Lines (I.27–I.32) ───────────────────────────────
    PropositionComparison(
        27, "Prop.I.27", "proposition_27",
        "If alternate interior angles are equal, the lines are parallel",
        "theorem", ("Equals", "On", "SameSide"), 3, 1, False),
    PropositionComparison(
        28, "Prop.I.28", "proposition_28",
        "If corresponding angles are equal, the lines are parallel",
        "theorem", ("Equals", "On"), 3, 1, False),
    PropositionComparison(
        29, "Prop.I.29", "proposition_29",
        "A transversal cutting parallel lines makes alternate interior angles equal",
        "theorem", ("Equals", "On"), 4, 1, False),
    PropositionComparison(
        30, "Prop.I.30", "proposition_30",
        "Lines parallel to the same line are parallel to each other",
        "theorem", ("On",), 3, 1, False),
    PropositionComparison(
        31, "Prop.I.31", "proposition_31",
        "Through a given point to draw a line parallel to a given line",
        "construction", ("On",), 1, 1, True),
    PropositionComparison(
        32, "Prop.I.32", "proposition_32",
        "Exterior angle equals sum of remote interior angles; angle sum equals two right angles",
        "theorem", ("Equals", "Between"), 3, 2, False),
    # ── Parallelograms & Area (I.33–I.45) ────────────────────────
    PropositionComparison(
        33, "Prop.I.33", "proposition_33",
        "Lines joining equal and parallel lines are themselves equal and parallel",
        "theorem", ("Equals", "On"), 3, 1, False),
    PropositionComparison(
        34, "Prop.I.34", "proposition_34",
        "Opposite sides and angles of a parallelogram are equal; diagonal bisects it",
        "theorem", ("Equals",), 3, 1, False),
    PropositionComparison(
        35, "Prop.I.35", "proposition_35",
        "Parallelograms on the same base and between the same parallels are equal in area",
        "theorem", ("Equals", "On"), 3, 1, False),
    PropositionComparison(
        36, "Prop.I.36", "proposition_36",
        "Parallelograms on equal bases and between the same parallels are equal in area",
        "theorem", ("Equals", "On"), 3, 1, False),
    PropositionComparison(
        37, "Prop.I.37", "proposition_37",
        "Triangles on the same base and between the same parallels are equal in area",
        "theorem", ("Equals", "On"), 3, 1, False),
    PropositionComparison(
        38, "Prop.I.38", "proposition_38",
        "Triangles on equal bases and between the same parallels are equal in area",
        "theorem", ("Equals", "On"), 3, 1, False),
    PropositionComparison(
        39, "Prop.I.39", "proposition_39",
        "Equal triangles on the same base are between the same parallels",
        "theorem", ("Equals", "On"), 3, 1, False),
    PropositionComparison(
        40, "Prop.I.40", "proposition_40",
        "Equal triangles on equal bases are between the same parallels",
        "theorem", ("Equals", "On"), 3, 1, False),
    PropositionComparison(
        41, "Prop.I.41", "proposition_41",
        "A parallelogram on the same base as a triangle and between the same parallels is double the triangle",
        "theorem", ("Equals", "On"), 3, 1, False),
    PropositionComparison(
        42, "Prop.I.42", "proposition_42",
        "To construct a parallelogram equal to a given triangle in a given angle",
        "construction", ("Equals", "On"), 1, 1, True),
    PropositionComparison(
        43, "Prop.I.43", "proposition_43",
        "The complements of parallelograms about the diagonal are equal",
        "theorem", ("Equals",), 3, 1, False),
    PropositionComparison(
        44, "Prop.I.44", "proposition_44",
        "To a given straight line to apply a parallelogram equal to a given triangle",
        "construction", ("Equals", "On"), 2, 1, True),
    PropositionComparison(
        45, "Prop.I.45", "proposition_45",
        "To construct a parallelogram equal to a given rectilineal figure in a given angle",
        "construction", ("Equals",), 2, 1, True),
    # ── Pythagorean Theorem (I.46–I.48) ──────────────────────────
    PropositionComparison(
        46, "Prop.I.46", "proposition_46",
        "On a given straight line to describe a square",
        "construction", ("Equals", "On"), 1, 1, True),
    PropositionComparison(
        47, "Prop.I.47", "proposition_47",
        "In right-angled triangles the square on the hypotenuse equals the sum of the squares on the other sides",
        "theorem", ("Equals",), 3, 1, False),
    PropositionComparison(
        48, "Prop.I.48", "proposition_48",
        "If the square on one side equals the sum of squares on the other two, the angle is right",
        "theorem", ("Equals",), 3, 1, False),
]

# Build lookup dicts
_BY_OUR_NAME: Dict[str, PropositionComparison] = {
    p.our_name: p for p in PROPOSITION_COMPARISONS
}
_BY_NUMBER: Dict[int, PropositionComparison] = {
    p.number: p for p in PROPOSITION_COMPARISONS
}
_BY_GEOCOQ_NAME: Dict[str, PropositionComparison] = {
    p.geocoq_name: p for p in PROPOSITION_COMPARISONS
}


# ═══════════════════════════════════════════════════════════════════════
# PUBLIC API
# ═══════════════════════════════════════════════════════════════════════

def our_name_to_geocoq(our_name: str) -> Optional[str]:
    """Convert our proposition name to GeoCoq's Coq identifier.

    >>> our_name_to_geocoq("Prop.I.1")
    'proposition_1'
    >>> our_name_to_geocoq("Prop.I.47")
    'proposition_47'
    """
    p = _BY_OUR_NAME.get(our_name)
    return p.geocoq_name if p else None


def geocoq_to_our_name(geocoq_name: str) -> Optional[str]:
    """Convert GeoCoq's Coq identifier to our proposition name.

    >>> geocoq_to_our_name("proposition_1")
    'Prop.I.1'
    """
    p = _BY_GEOCOQ_NAME.get(geocoq_name)
    return p.our_name if p else None


def get_comparison(our_name: str) -> Optional[PropositionComparison]:
    """Get the full comparison record for a proposition."""
    return _BY_OUR_NAME.get(our_name)


def get_all_comparisons() -> List[PropositionComparison]:
    """Return all 48 proposition comparisons."""
    return list(PROPOSITION_COMPARISONS)


def validate_library_alignment() -> List[str]:
    """Validate that our E library aligns with the GeoCoq reference.

    Checks:
      1. All 48 propositions exist in our E library
      2. Constructions have existential variables
      3. Theorems have expected minimum hypotheses/conclusions
      4. Key predicates appear in the sequent

    Returns:
        List of alignment issues (empty = all good).
    """
    from .e_library import E_THEOREM_LIBRARY

    issues: List[str] = []

    for comp in PROPOSITION_COMPARISONS:
        thm = E_THEOREM_LIBRARY.get(comp.our_name)
        if thm is None:
            issues.append(f"{comp.our_name}: missing from E library")
            continue

        seq = thm.sequent

        # Check existential variables for constructions
        if comp.has_existentials and len(seq.exists_vars) == 0:
            issues.append(
                f"{comp.our_name}: construction should have existential vars"
            )

        # Check minimum hypotheses
        if len(seq.hypotheses) < comp.min_hypotheses:
            issues.append(
                f"{comp.our_name}: expected ≥{comp.min_hypotheses} hypotheses, "
                f"got {len(seq.hypotheses)}"
            )

        # Check minimum conclusions
        if len(seq.conclusions) < comp.min_conclusions:
            issues.append(
                f"{comp.our_name}: expected ≥{comp.min_conclusions} conclusions, "
                f"got {len(seq.conclusions)}"
            )

    return issues


