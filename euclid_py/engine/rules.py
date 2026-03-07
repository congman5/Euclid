"""
Rule Catalogs — ported from FitchProofPanel.jsx and geometricRules.js

Defines rule sets for Euclid, Hilbert, and Fitch axiom systems,
plus derivability mapping and rule-sentence validation.
"""
from __future__ import annotations

import re
from dataclasses import dataclass, field
from enum import Enum
from typing import Any, Callable, Dict, List, Optional, Set, Tuple


# ═══════════════════════════════════════════════════════════════════════════
# RULE CATEGORIES
# ═══════════════════════════════════════════════════════════════════════════

class RuleCategory(str, Enum):
    POSTULATE = "Postulate"
    COMMON_NOTION = "Common Notion"
    DEFINITION = "Definition"
    LOGICAL = "Logical"
    PROPOSITION = "Proposition"
    CONSTRUCTION = "Construction"
    PREMISE = "Premise"


# ═══════════════════════════════════════════════════════════════════════════
# RULE DEFINITION
# ═══════════════════════════════════════════════════════════════════════════

@dataclass
class Rule:
    id: str
    desc: str
    grp: str
    valid_for: Optional[List[str]] = None  # None = anything
    no_just_needed: bool = False
    is_axiom: bool = False

    def matches_sentence(self, predicate_names: List[str]) -> bool:
        """Check whether this rule is allowed to justify a sentence with these predicates."""
        if self.no_just_needed:
            return True
        if self.valid_for is None:
            return True
        if not predicate_names:
            return True
        return all(
            any(n.startswith(v) for v in self.valid_for)
            for n in predicate_names
        )


# ═══════════════════════════════════════════════════════════════════════════
# EUCLID RULES
# ═══════════════════════════════════════════════════════════════════════════

EUCLID_RULES: List[Rule] = [
    # Postulates
    Rule("Post.1", "Straight line between two points", "Postulates", ["Segment"]),
    Rule("Post.2", "Extend a finite straight line", "Postulates", ["Segment", "Between"]),
    Rule("Post.3", "Draw circle with center & radius", "Postulates", ["Circle", "OnCircle"]),
    Rule("Post.4", "All right angles are equal", "Postulates", ["RightAngle", "EqualAngle"]),
    Rule("Post.5", "Parallel postulate", "Postulates", None),
    # Intersection Axioms
    Rule("Intersect.CC", "Circle-circle intersection point", "Intersection Axioms", ["OnCircle", "Point"]),
    Rule("Intersect.CL", "Circle-line intersection point", "Intersection Axioms", ["OnCircle", "Point", "Between"]),
    # Common Notions
    Rule("C.N.1", "Things equal to the same are equal", "Common Notions", ["Equal", "EqualAngle", "EqualCircle"]),
    Rule("C.N.2", "Add equals to equals", "Common Notions", ["Equal", "EqualAngle", "EqualCircle"]),
    Rule("C.N.3", "Subtract equals from equals", "Common Notions", ["Equal", "EqualAngle", "EqualCircle"]),
    Rule("C.N.4", "Things which coincide are equal", "Common Notions", ["Equal", "Congruent", "EqualAngle", "EqualCircle"]),
    Rule("C.N.5", "Whole is greater than the part", "Common Notions", ["Longer", "Shorter"]),
    # Segment Arithmetic
    Rule("SegAdd", "Segment addition (Between + Equal → Equal whole)", "Segment Arithmetic", ["Equal"]),
    Rule("SegSub", "Segment subtraction (Between + Equal whole → Equal part)", "Segment Arithmetic", ["Equal"]),
    # Angle Arithmetic
    Rule("AngleSub", "Angle subtraction (EqualAngle whole − part = remainder)", "Angle Arithmetic", ["EqualAngle"]),
    Rule("AngleAdd", "Angle addition (EqualAngle parts → whole)", "Angle Arithmetic", ["EqualAngle"]),
    # Congruence Rules
    Rule("Cong.Elim", "Derive Equal/EqualAngle from Congruent", "Congruence Rules", ["Equal", "EqualAngle"]),
    # Area Axioms
    Rule("EqualArea", "Two figures have equal area", "Area Axioms", ["EqualArea"]),
    Rule("AreaAdd", "Area additivity (sum of parts = whole)", "Area Axioms", ["EqualArea"]),
    Rule("AreaSub", "Area subtraction (whole − part = remainder)", "Area Axioms", ["EqualArea"]),
    Rule("CongArea", "Congruent triangles have equal area", "Area Axioms", ["EqualArea"]),
    Rule("ParArea", "Parallelogram = double triangle on same base/parallels", "Area Axioms", ["EqualArea"]),
    # Definitions
    Rule("Def.1", "A point has no part", "Definitions", ["Point"]),
    Rule("Def.2", "A line is breadthless length", "Definitions", ["Segment"]),
    Rule("Def.3", "The ends of a line are points", "Definitions", ["Point"]),
    Rule("Def.4", "A straight line lies evenly with points on itself", "Definitions", ["Segment", "Collinear"]),
    Rule("Def.8", "A plane angle is the inclination of two lines", "Definitions", ["EqualAngle", "RightAngle"]),
    Rule("Def.10", "Right angle — equal adjacent angles", "Definitions", ["RightAngle"]),
    Rule("Def.11", "Obtuse angle — greater than a right angle", "Definitions", ["EqualAngle"]),
    Rule("Def.12", "Acute angle — less than a right angle", "Definitions", ["EqualAngle"]),
    Rule("Def.15", "Circle — all radii equal", "Definitions", ["Equal", "OnCircle", "EqualCircle"]),
    Rule("Def.16", "Center of a circle", "Definitions", ["Point", "Circle"]),
    Rule("Def.17", "Diameter — line through center terminated by circle", "Definitions", ["Segment", "OnCircle"]),
    Rule("Def.20", "Equilateral triangle — three equal sides", "Definitions", ["Equilateral"]),
    Rule("Def.21", "Isosceles triangle — two equal sides", "Definitions", ["Isosceles"]),
    Rule("Def.22", "Scalene triangle — no equal sides", "Definitions", None),
    Rule("Def.23", "Right-angled triangle", "Definitions", ["RightAngle"]),
    Rule("Def.35", "Parallel lines — never meet when produced", "Definitions", ["Parallel"]),
    # Existence
    Rule("Existence", "Assert existence of an object", "Existence", None, no_just_needed=True),
    Rule("Given", "Given premise", "Existence", None, no_just_needed=True),
]

# ═══════════════════════════════════════════════════════════════════════════
# HILBERT RULES
# ═══════════════════════════════════════════════════════════════════════════

HILBERT_RULES: List[Rule] = [
    Rule("H.I.1", "Two points determine a line", "Hilbert — Incidence", None, is_axiom=True),
    Rule("H.I.2", "Two distinct points on every line", "Hilbert — Incidence", None, is_axiom=True),
    Rule("H.I.3", "Three non-collinear points exist", "Hilbert — Incidence", None, is_axiom=True),
    Rule("H.O.1", "Betweenness is symmetric", "Hilbert — Order", None, is_axiom=True),
    Rule("H.O.2", "For A,B ∃ C with A*B*C", "Hilbert — Order", None, is_axiom=True),
    Rule("H.O.3", "Exactly one of three points is between", "Hilbert — Order", None, is_axiom=True),
    Rule("H.O.4", "Pasch's axiom", "Hilbert — Order", None, is_axiom=True),
    Rule("H.C.1", "Segment transfer", "Hilbert — Congruence", None, is_axiom=True),
    Rule("H.C.2", "Segment addition", "Hilbert — Congruence", None, is_axiom=True),
    Rule("H.C.3", "Angle transfer", "Hilbert — Congruence", None, is_axiom=True),
    Rule("H.C.4", "SAS axiom", "Hilbert — Congruence", None, is_axiom=True),
    Rule("H.P.1", "Playfair parallel axiom", "Hilbert — Parallels", None, is_axiom=True),
    Rule("H.Cont.1", "Archimedes axiom", "Hilbert — Continuity", None, is_axiom=True),
    Rule("H.Cont.2", "Line completeness", "Hilbert — Continuity", None, is_axiom=True),
]

# ═══════════════════════════════════════════════════════════════════════════
# FITCH LOGIC RULES
# ═══════════════════════════════════════════════════════════════════════════

FITCH_LOGIC_RULES: List[Rule] = [
    Rule("RAA.Assume", "Open temporary assumption for indirect proof", "Fitch Logic", None),
    Rule("Contradiction", "Introduce contradiction from φ and ¬φ", "Fitch Logic", ["Contradiction"]),
    Rule("RAA", "Discharge assumption by contradiction", "Fitch Logic", None),
]

# ═══════════════════════════════════════════════════════════════════════════
# PROOF SYSTEMS
# ═══════════════════════════════════════════════════════════════════════════

PROOF_SYSTEMS = {
    "F": dict(id="F", label="F (Fitch Logic Core)"),
    "E": dict(id="E", label="E (Euclid Axiomatic)"),
    "H": dict(id="H", label="H (Hilbert Axiomatic)"),
}


# ═══════════════════════════════════════════════════════════════════════════
# PROPOSITION RULES (generated dynamically)
# ═══════════════════════════════════════════════════════════════════════════

PROPOSITION_DESCS: Dict[int, str] = {
    1: "Equilateral triangle on segment",
    2: "Transfer a length to a point",
    3: "Cut off equal length",
    4: "SAS congruence",
    5: "Isosceles base angles",
    6: "Converse of base angles",
    7: "Unique triangle from segments",
    8: "SSS congruence",
    9: "Bisect an angle",
    10: "Bisect a segment",
    11: "Perpendicular from point on line",
    12: "Perpendicular from point off line",
    13: "Supplementary angles",
    14: "Converse of supplementary",
    15: "Vertical angles",
    16: "Exterior angle > remote interior",
    22: "Triangle from three segments",
    23: "Construct equal angle",
    26: "ASA / AAS congruence",
    27: "Alternate interior angles → parallel",
    28: "Ext angle = opp int → parallel",
    29: "Parallel → alternate int angles equal",
    31: "Construct parallel through point",
    32: "Exterior angle = sum of remotes",
    34: "Parallelogram opposite sides equal",
    35: "Parallelograms same base equal area",
    41: "Triangle half of parallelogram",
    46: "Construct square on segment",
    47: "Pythagorean theorem (area of squares)",
    48: "Converse of Pythagorean theorem",
}


def make_proposition_rules(max_prop: int = 48) -> List[Rule]:
    rules = []
    for n in range(1, min(max_prop, 48) + 1):
        rules.append(Rule(
            id=f"Prop.I.{n}",
            desc=PROPOSITION_DESCS.get(n, f"Proposition I.{n}"),
            grp="Propositions",
            valid_for=None,
        ))
    return rules


# ═══════════════════════════════════════════════════════════════════════════
# SYSTEM-SPECIFIC RULE SETS
# ═══════════════════════════════════════════════════════════════════════════

def get_rules_for_system(system_id: str, max_prop: int = 48) -> List[Rule]:
    proposition_rules = make_proposition_rules(max_prop)
    existence_rules = [r for r in EUCLID_RULES if r.grp == "Existence"]

    if system_id == "F":
        return existence_rules + FITCH_LOGIC_RULES

    if system_id == "H":
        shared_groups = {
            "Common Notions", "Segment Arithmetic", "Angle Arithmetic",
            "Congruence Rules", "Area Axioms", "Definitions", "Existence",
        }
        derived_shared = [r for r in EUCLID_RULES if r.grp in shared_groups]
        return derived_shared + proposition_rules + HILBERT_RULES + FITCH_LOGIC_RULES

    # E (Euclid)
    return EUCLID_RULES + proposition_rules + FITCH_LOGIC_RULES


def map_axiom_system(system: Optional[str]) -> str:
    """Map an incoming axiom-system name to system id (E, F, H)."""
    if not system:
        return "E"
    s = str(system).lower()
    if s in ("hilbert", "h"):
        return "H"
    if s in ("f", "fitch"):
        return "F"
    return "E"


# ═══════════════════════════════════════════════════════════════════════════
# RULE DERIVABILITY MAPPING
# ═══════════════════════════════════════════════════════════════════════════

RULE_DERIVABILITY: Dict[str, Dict[str, dict]] = {
    "Given":         {"F": {"kind": "axiom"}, "E": {"kind": "axiom"}, "H": {"kind": "axiom"}},
    "Existence":     {"F": {"kind": "axiom"}, "E": {"kind": "axiom"}, "H": {"kind": "axiom"}},
    "RAA.Assume":    {"F": {"kind": "axiom"}, "E": {"kind": "derived", "from": ["F"]}, "H": {"kind": "derived", "from": ["F"]}},
    "Contradiction": {"F": {"kind": "axiom"}, "E": {"kind": "derived", "from": ["F"]}, "H": {"kind": "derived", "from": ["F"]}},
    "RAA":           {"F": {"kind": "axiom"}, "E": {"kind": "derived", "from": ["F"]}, "H": {"kind": "derived", "from": ["F"]}},

    "Post.1":       {"E": {"kind": "axiom", "from": ["Postulate 1"]}},
    "Post.2":       {"E": {"kind": "axiom", "from": ["Postulate 2"]}},
    "Post.3":       {"E": {"kind": "axiom", "from": ["Postulate 3"]}},
    "Post.4":       {"E": {"kind": "axiom", "from": ["Postulate 4"]}},
    "Post.5":       {"E": {"kind": "axiom", "from": ["Postulate 5"]}, "H": {"kind": "derived", "from": ["H.P.1"]}},
    "Intersect.CC": {"E": {"kind": "axiom", "from": ["E4_CircleCircleIntersect"]}, "H": {"kind": "derived", "from": ["H.O.4", "H.Cont.2"]}},
    "Intersect.CL": {"E": {"kind": "axiom", "from": ["E5_CircleLineIntersect"]}, "H": {"kind": "derived", "from": ["H.O.4", "H.Cont.2"]}},

    "C.N.1": {"E": {"kind": "axiom", "from": ["Common Notion 1"]}, "H": {"kind": "derived", "from": ["H.C.1", "H.C.2"]}},
    "C.N.2": {"E": {"kind": "axiom", "from": ["Common Notion 2"]}, "H": {"kind": "derived", "from": ["H.C.2"]}},
    "C.N.3": {"E": {"kind": "axiom", "from": ["Common Notion 3"]}, "H": {"kind": "derived", "from": ["H.C.2"]}},
    "C.N.4": {"E": {"kind": "axiom", "from": ["Common Notion 4"]}, "H": {"kind": "derived", "from": ["H.C.4"]}},
    "C.N.5": {"E": {"kind": "axiom", "from": ["Common Notion 5"]}, "H": {"kind": "derived", "from": ["H.O.1", "H.O.3"]}},

    "SegAdd":    {"E": {"kind": "derived", "from": ["C.N.2", "Post.2"]}, "H": {"kind": "derived", "from": ["H.C.2"]}},
    "SegSub":    {"E": {"kind": "derived", "from": ["C.N.3", "Post.2"]}, "H": {"kind": "derived", "from": ["H.C.2"]}},
    "AngleAdd":  {"E": {"kind": "derived", "from": ["C.N.2", "Def.8"]}, "H": {"kind": "derived", "from": ["H.C.3"]}},
    "AngleSub":  {"E": {"kind": "derived", "from": ["C.N.3", "Def.8"]}, "H": {"kind": "derived", "from": ["H.C.3"]}},
    "Cong.Elim": {"E": {"kind": "derived", "from": ["Def.20", "Prop.I.4"]}, "H": {"kind": "derived", "from": ["H.C.4"]}},

    "AreaAdd":  {"E": {"kind": "derived", "from": ["C.N.2"]}, "H": {"kind": "derived", "from": ["H.C.2"]}},
    "AreaSub":  {"E": {"kind": "derived", "from": ["C.N.3"]}, "H": {"kind": "derived", "from": ["H.C.2"]}},
    "CongArea": {"E": {"kind": "derived", "from": ["Prop.I.4", "Def.20"]}, "H": {"kind": "derived", "from": ["H.C.4"]}},
    "ParArea":  {"E": {"kind": "derived", "from": ["Prop.I.34", "Prop.I.41"]}, "H": {"kind": "derived", "from": ["H.P.1", "H.C.4"]}},

    "Def.10": {"E": {"kind": "axiom", "from": ["Definition 10"]}, "H": {"kind": "derived", "from": ["H.C.3"]}},
    "Def.15": {"E": {"kind": "axiom", "from": ["Definition 15"]}, "H": {"kind": "derived", "from": ["H.C.1"]}},
    "Def.20": {"E": {"kind": "axiom", "from": ["Definition 20"]}, "H": {"kind": "derived", "from": ["H.C.4"]}},
    "Def.22": {"E": {"kind": "axiom", "from": ["Definition 22"]}, "H": {"kind": "derived", "from": ["H.C.4"]}},
    "Def.23": {"E": {"kind": "axiom", "from": ["Definition 23"]}, "H": {"kind": "derived", "from": ["H.P.1"]}},
    "Def.35": {"E": {"kind": "axiom", "from": ["Definition 35"]}, "H": {"kind": "derived", "from": ["H.P.1"]}},

    "SAS": {"E": {"kind": "axiom", "from": ["E6_SAS"]}, "H": {"kind": "derived", "from": ["H.C.4"]}},
    "SSS": {"E": {"kind": "derived", "from": ["Prop.I.7", "SAS"]}, "H": {"kind": "derived", "from": ["H.C.4"]}},
}


def is_rule_derivable(rule_id: str, system_id: str,
                      proposition: Optional[dict] = None,
                      strict: bool = True) -> dict:
    """Check if a rule is admissible in a given axiom system.
    Returns { ok: bool, reason: str }.
    """
    if not strict:
        return dict(ok=True, reason="")

    if rule_id and rule_id.startswith("H."):
        ok = system_id == "H"
        return dict(ok=ok, reason="" if ok else f"{rule_id} is Hilbert-only")

    if rule_id and rule_id.startswith("Prop.I."):
        try:
            n = int(rule_id.replace("Prop.I.", ""))
        except ValueError:
            return dict(ok=True, reason="")
        current = None
        if proposition:
            current = proposition.get("propNumber") or proposition.get("number")
        if current is not None and n >= current:
            return dict(ok=False, reason=f"{rule_id} is not admissible before proving I.{n}")
        return dict(ok=True, reason="")

    policy = RULE_DERIVABILITY.get(rule_id)
    if not policy:
        return dict(ok=False, reason=f"{rule_id} has no explicit derivability mapping")
    if system_id not in policy:
        return dict(ok=False, reason=f"{rule_id} is not admissible in system {system_id}")
    return dict(ok=True, reason="")
