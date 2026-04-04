"""
lean_mapping.py — Mapping tables from LeanEuclid constructs to System E.

Defines how LeanEuclid tactics, rules, and expressions correspond to
System E StepKind, AST atoms, and proof structures.

Reference: euclid-plan.md §LeanEuclid Translation Rules
"""
from __future__ import annotations

from dataclasses import dataclass, field
from enum import Enum, auto
from typing import Dict, FrozenSet, List, Optional, Set, Tuple


# ═══════════════════════════════════════════════════════════════════════
# Rule classification: what kind of System E step does a Lean rule map to?
# ═══════════════════════════════════════════════════════════════════════

class RuleCategory(Enum):
    """Category of a LeanEuclid rule for System E translation."""
    PROPOSITION = auto()        # proposition_N → THEOREM_APP
    CONSTRUCTION = auto()       # line_from_points, circle_from_points, etc. → CONSTRUCTION
    EXTENSION_AXIOM = auto()    # extend_point, extend_point_longer, etc. → CONSTRUCTION
    INTERSECTION = auto()       # intersection_lines, intersection_circles → CONSTRUCTION
    DIAGRAMMATIC = auto()       # point_on_circle_onlyif, etc. → DIAGRAMMATIC
    METRIC = auto()             # sum_angles_if, sum_angles_onlyif → METRIC
    TRANSFER = auto()           # segment/angle transfer rules → TRANSFER
    SUPERPOSITION = auto()      # SAS / SSS → SUPERPOSITION
    SPECIAL = auto()            # arbitrary_point, distinct_points → CONSTRUCTION


@dataclass
class RuleMapping:
    """How a single LeanEuclid rule maps to System E."""
    lean_name: str                   # e.g. "proposition_16", "line_from_points"
    category: RuleCategory
    system_e_name: str = ""          # e.g. "Prop.I.16", "let-line"
    creates_objects: bool = False     # whether it introduces new variables
    object_sorts: List[str] = field(default_factory=list)  # sorts of created objects
    description: str = ""
    is_avigad_standard: bool = True  # False for LeanEuclid extensions


# ═══════════════════════════════════════════════════════════════════════
# Proposition mappings (I.1–I.48)
# ═══════════════════════════════════════════════════════════════════════

PROPOSITION_RULES: Dict[str, RuleMapping] = {}
for i in range(1, 49):
    lean_name = f"proposition_{i}"
    se_name = f"Prop.I.{i}"
    PROPOSITION_RULES[lean_name] = RuleMapping(
        lean_name=lean_name,
        category=RuleCategory.PROPOSITION,
        system_e_name=se_name,
        description=f"Euclid Book I Proposition {i}",
    )

# Add variant mappings (proposition_N', proposition_N'', etc.)
_VARIANTS = {
    "proposition_5'":  ("Prop.I.5", "I.5 variant: isosceles base angles (alternate form)"),
    "proposition_22'": ("Prop.I.22", "I.22 variant: construct triangle on given line"),
    "proposition_23'": ("Prop.I.23", "I.23 variant: copy angle to specified side"),
    "proposition_29'": ("Prop.I.29", "I.29 variant: alternate form"),
    "proposition_29''": ("Prop.I.29", "I.29 variant: corresponding angles"),
    "proposition_29'''": ("Prop.I.29", "I.29 variant: alternate interior angles"),
    "proposition_29''''": ("Prop.I.29", "I.29 variant: rearranged hypotheses"),
    "proposition_29'''''": ("Prop.I.29", "I.29 variant: further rearrangement"),
    "proposition_34'": ("Prop.I.34", "I.34 variant: without explicit BC"),
    "proposition_35'": ("Prop.I.35", "I.35 variant: equal bases form"),
    "proposition_36'": ("Prop.I.36", "I.36 variant: equal bases on parallels"),
    "proposition_37'": ("Prop.I.37", "I.37 variant: area form"),
    "proposition_42'": ("Prop.I.42", "I.42 variant: alternate parallelogram form"),
    "proposition_42''": ("Prop.I.42", "I.42 variant: second alternate form"),
    "proposition_42'''": ("Prop.I.42", "I.42 variant: third alternate form"),
    "proposition_44'": ("Prop.I.44", "I.44 variant: alternate construction form"),
    "proposition_46'": ("Prop.I.46", "I.46 variant: alternate square construction"),
    "proposition_11''": ("Prop.I.11", "I.11 variant: perpendicular from point on line"),
    "proposition_11'''": ("Prop.I.11", "I.11 variant: third form"),
    "proposition_22''": ("Prop.I.22", "I.22 variant: second alternate form"),
}
for lean_name, (se_name, desc) in _VARIANTS.items():
    PROPOSITION_RULES[lean_name] = RuleMapping(
        lean_name=lean_name,
        category=RuleCategory.PROPOSITION,
        system_e_name=se_name,
        description=desc,
    )


# ═══════════════════════════════════════════════════════════════════════
# Construction rules
# ═══════════════════════════════════════════════════════════════════════

CONSTRUCTION_RULES: Dict[str, RuleMapping] = {
    "line_from_points": RuleMapping(
        lean_name="line_from_points",
        category=RuleCategory.CONSTRUCTION,
        system_e_name="let-line",
        creates_objects=True,
        object_sorts=["LINE"],
        description="Construct line through two points",
    ),
    "circle_from_points": RuleMapping(
        lean_name="circle_from_points",
        category=RuleCategory.CONSTRUCTION,
        system_e_name="let-circle",
        creates_objects=True,
        object_sorts=["CIRCLE"],
        description="Construct circle through center and point",
    ),
    "extend_point": RuleMapping(
        lean_name="extend_point",
        category=RuleCategory.EXTENSION_AXIOM,
        system_e_name="let-point-on-line-extend",
        creates_objects=True,
        object_sorts=["POINT"],
        description="Extend line segment beyond a point",
    ),
    "extend_point_not_on_line": RuleMapping(
        lean_name="extend_point_not_on_line",
        category=RuleCategory.EXTENSION_AXIOM,
        system_e_name="let-point-on-line-extend",
        creates_objects=True,
        object_sorts=["POINT"],
        description="Extend line segment, not on given line",
    ),
    "extend_point_longer": RuleMapping(
        lean_name="extend_point_longer",
        category=RuleCategory.EXTENSION_AXIOM,
        system_e_name="let-point-on-line-extend",
        creates_objects=True,
        object_sorts=["POINT"],
        description="Extend line segment longer than given segment",
        is_avigad_standard=False,
    ),
    "intersection_lines": RuleMapping(
        lean_name="intersection_lines",
        category=RuleCategory.INTERSECTION,
        system_e_name="let-intersection-line-line",
        creates_objects=True,
        object_sorts=["POINT"],
        description="Intersection of two lines",
    ),
    "intersection_circles": RuleMapping(
        lean_name="intersection_circles",
        category=RuleCategory.INTERSECTION,
        system_e_name="let-intersection-circle-circle-one",
        creates_objects=True,
        object_sorts=["POINT"],
        description="Intersection of two circles",
    ),
    "intersection_circle_line": RuleMapping(
        lean_name="intersection_circle_line",
        category=RuleCategory.INTERSECTION,
        system_e_name="let-intersection-line-circle",
        creates_objects=True,
        object_sorts=["POINT"],
        description="Intersection of line and circle",
    ),
    "intersection_circle_line_extending_points": RuleMapping(
        lean_name="intersection_circle_line_extending_points",
        category=RuleCategory.INTERSECTION,
        system_e_name="let-intersection-line-circle-extend",
        creates_objects=True,
        object_sorts=["POINT"],
        description="Intersection of line and circle, extending between points",
    ),
    "intersection_same_side": RuleMapping(
        lean_name="intersection_same_side",
        category=RuleCategory.INTERSECTION,
        system_e_name="let-intersection-circle-circle-same-side",
        creates_objects=True,
        object_sorts=["POINT"],
        description="Circle-circle intersection on same side of line",
    ),
    "intersection_opposite_side": RuleMapping(
        lean_name="intersection_opposite_side",
        category=RuleCategory.INTERSECTION,
        system_e_name="let-intersection-circle-circle-opposite-side",
        creates_objects=True,
        object_sorts=["POINT"],
        description="Circle-circle intersection on opposite side of line",
    ),
    "arbitrary_point": RuleMapping(
        lean_name="arbitrary_point",
        category=RuleCategory.SPECIAL,
        system_e_name="let-point",
        creates_objects=True,
        object_sorts=["POINT"],
        description="Arbitrary point",
    ),
    "let_point_between": RuleMapping(
        lean_name="let_point_between",
        category=RuleCategory.CONSTRUCTION,
        system_e_name="let-point-on-line-between",
        creates_objects=True,
        object_sorts=["POINT"],
        description="Arbitrary point between two points",
        is_avigad_standard=False,
    ),
    "distinct_points": RuleMapping(
        lean_name="distinct_points",
        category=RuleCategory.SPECIAL,
        system_e_name="let-point",
        creates_objects=True,
        object_sorts=["POINT"],
        description="Point distinct from given point",
    ),
    "exists_point_between_points_on_line": RuleMapping(
        lean_name="exists_point_between_points_on_line",
        category=RuleCategory.CONSTRUCTION,
        system_e_name="let-point-on-line-between",
        creates_objects=True,
        object_sorts=["POINT"],
        description="Point between two points on a line",
    ),
    "point_same_side": RuleMapping(
        lean_name="point_same_side",
        category=RuleCategory.SPECIAL,
        system_e_name="let-point-same-side",
        creates_objects=True,
        object_sorts=["POINT"],
        description="Point on same side of line",
    ),
    "point_between_points_shorter_than": RuleMapping(
        lean_name="point_between_points_shorter_than",
        category=RuleCategory.EXTENSION_AXIOM,
        system_e_name="let-point-between-short",
        creates_objects=True,
        object_sorts=["POINT"],
        description="Point between, shorter than given segment",
        is_avigad_standard=False,
    ),
    "distinct_point_same_side": RuleMapping(
        lean_name="distinct_point_same_side",
        category=RuleCategory.SPECIAL,
        system_e_name="let-point-same-side-distinct",
        creates_objects=True,
        object_sorts=["POINT"],
        description="Distinct point on same side of line",
    ),
    "line_nonempty": RuleMapping(
        lean_name="line_nonempty",
        category=RuleCategory.SPECIAL,
        system_e_name="let-point-on-line",
        creates_objects=True,
        object_sorts=["POINT"],
        description="Every line has at least one point",
    ),
    "exists_distincts_points_on_line": RuleMapping(
        lean_name="exists_distincts_points_on_line",
        category=RuleCategory.SPECIAL,
        system_e_name="let-point-on-line",
        creates_objects=True,
        object_sorts=["POINT"],
        description="For any point and line, there exists a distinct point on the line",
    ),
    "point_on_line_same_side": RuleMapping(
        lean_name="point_on_line_same_side",
        category=RuleCategory.SPECIAL,
        system_e_name="let-point-on-line-same-side",
        creates_objects=True,
        object_sorts=["POINT"],
        description="Point on line M on same side of L as b (needs ¬on(b,L) and intersects(L,M))",
    ),
    "exists_point_opposite": RuleMapping(
        lean_name="exists_point_opposite",
        category=RuleCategory.SPECIAL,
        system_e_name="let-point-opposite-side",
        creates_objects=True,
        object_sorts=["POINT"],
        description="Point on opposite side of line from given point",
    ),
    "exists_distinct_point_opposite_side": RuleMapping(
        lean_name="exists_distinct_point_opposite_side",
        category=RuleCategory.SPECIAL,
        system_e_name="let-point-opposite-side",
        creates_objects=True,
        object_sorts=["POINT"],
        description="Distinct point on opposite side of line",
    ),
    "exists_point_on_circle": RuleMapping(
        lean_name="exists_point_on_circle",
        category=RuleCategory.SPECIAL,
        system_e_name="let-point-on-circle",
        creates_objects=True,
        object_sorts=["POINT"],
        description="There exists a point on any circle",
    ),
    "exists_distinct_point_on_circle": RuleMapping(
        lean_name="exists_distinct_point_on_circle",
        category=RuleCategory.SPECIAL,
        system_e_name="let-point-on-circle",
        creates_objects=True,
        object_sorts=["POINT"],
        description="Distinct point on a circle",
    ),
    "exists_point_on_extension": RuleMapping(
        lean_name="exists_point_on_extension",
        category=RuleCategory.EXTENSION_AXIOM,
        system_e_name="let-point-on-line-extend",
        creates_objects=True,
        object_sorts=["POINT"],
        description="Extend line segment (exists form)",
    ),
    "exists_point_on_extension_longer": RuleMapping(
        lean_name="exists_point_on_extension_longer",
        category=RuleCategory.EXTENSION_AXIOM,
        system_e_name="let-point-on-line-extend",
        creates_objects=True,
        object_sorts=["POINT"],
        description="Extend line segment longer than given (exists form)",
    ),
}


# ═══════════════════════════════════════════════════════════════════════
# Diagrammatic/metric/transfer rules
# ═══════════════════════════════════════════════════════════════════════

INFERENCE_RULES: Dict[str, RuleMapping] = {
    "point_on_circle_onlyif": RuleMapping(
        lean_name="point_on_circle_onlyif",
        category=RuleCategory.TRANSFER,
        system_e_name="Segment transfer 3b",
        description="Point on circle → equal radii",
    ),
    "sum_angles_if": RuleMapping(
        lean_name="sum_angles_if",
        category=RuleCategory.METRIC,
        system_e_name="M2 — Angle addition (if)",
        description="Angle addition: if between then sum",
    ),
    "sum_angles_onlyif": RuleMapping(
        lean_name="sum_angles_onlyif",
        category=RuleCategory.METRIC,
        system_e_name="M2 — Angle addition (onlyif)",
        description="Angle addition: onlyif between then sum",
    ),
    "rectangle_area": RuleMapping(
        lean_name="rectangle_area",
        category=RuleCategory.METRIC,
        system_e_name="rectangle area extension",
        description="Rectangle area (non-standard extension)",
        is_avigad_standard=False,
    ),
    "parallelogram_area": RuleMapping(
        lean_name="parallelogram_area",
        category=RuleCategory.METRIC,
        system_e_name="parallelogram area extension",
        description="Parallelogram area (non-standard extension)",
        is_avigad_standard=False,
    ),
    "sum_parallelograms_area": RuleMapping(
        lean_name="sum_parallelograms_area",
        category=RuleCategory.METRIC,
        system_e_name="sum parallelograms area extension",
        description="Sum of parallelogram areas (non-standard extension)",
        is_avigad_standard=False,
    ),
}


# ═══════════════════════════════════════════════════════════════════════
# Combined lookup
# ═══════════════════════════════════════════════════════════════════════

ALL_RULES: Dict[str, RuleMapping] = {}
ALL_RULES.update(PROPOSITION_RULES)
ALL_RULES.update(CONSTRUCTION_RULES)
ALL_RULES.update(INFERENCE_RULES)


def lookup_rule(lean_name: str) -> Optional[RuleMapping]:
    """Look up the System E mapping for a LeanEuclid rule name."""
    # Direct lookup
    if lean_name in ALL_RULES:
        return ALL_RULES[lean_name]
    # Strip trailing primes for variant lookup
    base = lean_name.rstrip("'")
    if base in ALL_RULES:
        return ALL_RULES[base]
    return None


def classify_rule(lean_name: str) -> RuleCategory:
    """Classify a LeanEuclid rule by its System E category."""
    mapping = lookup_rule(lean_name)
    if mapping:
        return mapping.category
    # Heuristic: proposition_N → PROPOSITION
    if lean_name.startswith("proposition_"):
        return RuleCategory.PROPOSITION
    return RuleCategory.SPECIAL


# ═══════════════════════════════════════════════════════════════════════
# Sort mapping
# ═══════════════════════════════════════════════════════════════════════

LEAN_SORT_TO_SYSTEM_E = {
    "Point": "POINT",
    "Line": "LINE",
    "Circle": "CIRCLE",
    "Segment": "SEGMENT",
}


def map_sort(lean_sort: str) -> str:
    """Map a LeanEuclid sort name to System E Sort enum name."""
    return LEAN_SORT_TO_SYSTEM_E.get(lean_sort, "POINT")


# ═══════════════════════════════════════════════════════════════════════
# Proposition dependency map (same as e_proofs._DEPS)
# ═══════════════════════════════════════════════════════════════════════

PROP_DEPS = {
    1: [],
    2: [1],
    3: [2],
    4: [],
    5: [4, 3],
    6: [4, 3],
    7: [5],
    8: [7],
    9: [1, 8],
    10: [1, 4],
    11: [1, 8],
    12: [8, 10],
    13: [11],
    14: [13],
    15: [13],
    16: [4, 10, 15],
    17: [16],
    18: [5, 16],
    19: [5, 18],
    20: [5, 19],
    21: [16, 20],
    22: [1, 3, 20],
    23: [8, 22],
    24: [4, 5, 19],
    25: [4, 24],
    26: [4, 16],
    27: [16],
    28: [27],
    29: [27],
    30: [27, 29],
    31: [23, 27],
    32: [13, 29, 31],
    33: [4, 27, 29],
    34: [4, 26, 29],
    35: [29, 34],
    36: [34, 35],
    37: [31, 35],
    38: [31, 36],
    39: [31, 37],
    40: [38, 39],
    41: [34, 37],
    42: [23, 31, 41],
    43: [34],
    44: [42, 43],
    45: [42, 44],
    46: [11, 31, 34],
    47: [4, 14, 41, 46],
    48: [8, 47],
}


# ═══════════════════════════════════════════════════════════════════════
# StepKind mapping
# ═══════════════════════════════════════════════════════════════════════

def category_to_step_kind_name(cat: RuleCategory) -> str:
    """Map a RuleCategory to the System E StepKind enum member name."""
    return {
        RuleCategory.PROPOSITION: "THEOREM_APP",
        RuleCategory.CONSTRUCTION: "CONSTRUCTION",
        RuleCategory.EXTENSION_AXIOM: "CONSTRUCTION",
        RuleCategory.INTERSECTION: "CONSTRUCTION",
        RuleCategory.DIAGRAMMATIC: "DIAGRAMMATIC",
        RuleCategory.METRIC: "METRIC",
        RuleCategory.TRANSFER: "TRANSFER",
        RuleCategory.SUPERPOSITION: "SUPERPOSITION_SAS",
        RuleCategory.SPECIAL: "CONSTRUCTION",
    }.get(cat, "METRIC")
