"""
Geometric Constraint Solver — ported from constraints.js

Verifies geometric constraints against actual canvas data.
Bridges the formal proof system with the visual canvas.
"""
from __future__ import annotations

import math
from dataclasses import dataclass, field
from enum import Enum
from typing import Dict, List, Optional, Tuple


# ═══════════════════════════════════════════════════════════════════════════
# TOLERANCE SETTINGS
# ═══════════════════════════════════════════════════════════════════════════

@dataclass
class Tolerance:
    distance: float = 2.0
    angle: float = 0.02
    collinear: float = 0.01
    on_circle: float = 2.0


DEFAULT_TOLERANCE = Tolerance()


# ═══════════════════════════════════════════════════════════════════════════
# GEOMETRIC COMPUTATIONS
# ═══════════════════════════════════════════════════════════════════════════

def distance(p1: Optional[dict], p2: Optional[dict]) -> Optional[float]:
    if p1 is None or p2 is None:
        return None
    dx = p2["x"] - p1["x"]
    dy = p2["y"] - p1["y"]
    return math.hypot(dx, dy)


def angle_at_vertex(a: Optional[dict], b: Optional[dict], c: Optional[dict]) -> Optional[float]:
    if a is None or b is None or c is None:
        return None
    ba = (a["x"] - b["x"], a["y"] - b["y"])
    bc = (c["x"] - b["x"], c["y"] - b["y"])
    dot = ba[0] * bc[0] + ba[1] * bc[1]
    mag_ba = math.hypot(*ba)
    mag_bc = math.hypot(*bc)
    if mag_ba == 0 or mag_bc == 0:
        return None
    cos_angle = max(-1.0, min(1.0, dot / (mag_ba * mag_bc)))
    return math.acos(cos_angle)


def signed_area(p1: Optional[dict], p2: Optional[dict], p3: Optional[dict]) -> Optional[float]:
    if p1 is None or p2 is None or p3 is None:
        return None
    return 0.5 * ((p2["x"] - p1["x"]) * (p3["y"] - p1["y"])
                 - (p3["x"] - p1["x"]) * (p2["y"] - p1["y"]))


def are_collinear(p1, p2, p3, tolerance: float = DEFAULT_TOLERANCE.collinear) -> Optional[bool]:
    area = signed_area(p1, p2, p3)
    if area is None:
        return None
    d12 = distance(p1, p2) or 0
    d23 = distance(p2, p3) or 0
    d13 = distance(p1, p3) or 0
    max_dist = max(d12, d23, d13)
    if max_dist == 0:
        return True
    return abs(area) / (max_dist * max_dist) < tolerance


def segment_intersection(p1, p2, p3, p4) -> Optional[dict]:
    d1 = (p2["x"] - p1["x"], p2["y"] - p1["y"])
    d2 = (p4["x"] - p3["x"], p4["y"] - p3["y"])
    cross = d1[0] * d2[1] - d1[1] * d2[0]
    if abs(cross) < 1e-10:
        return None
    d3 = (p3["x"] - p1["x"], p3["y"] - p1["y"])
    t = (d3[0] * d2[1] - d3[1] * d2[0]) / cross
    u = (d3[0] * d1[1] - d3[1] * d1[0]) / cross
    if t < 0 or t > 1 or u < 0 or u > 1:
        return None
    return {"x": p1["x"] + t * d1[0], "y": p1["y"] + t * d1[1]}


def circle_intersections(c1, r1: float, c2, r2: float) -> List[dict]:
    d = distance(c1, c2)
    if d is None or d > r1 + r2 or d < abs(r1 - r2) or (d == 0 and r1 == r2):
        return []
    a = (r1 * r1 - r2 * r2 + d * d) / (2 * d)
    h = math.sqrt(max(0, r1 * r1 - a * a))
    px = c1["x"] + a * (c2["x"] - c1["x"]) / d
    py = c1["y"] + a * (c2["y"] - c1["y"]) / d
    if h < 1e-10:
        return [{"x": px, "y": py}]
    return [
        {"x": px + h * (c2["y"] - c1["y"]) / d, "y": py - h * (c2["x"] - c1["x"]) / d},
        {"x": px - h * (c2["y"] - c1["y"]) / d, "y": py + h * (c2["x"] - c1["x"]) / d},
    ]


def line_circle_intersections(p1, p2, center, radius: float) -> List[dict]:
    d = (p2["x"] - p1["x"], p2["y"] - p1["y"])
    f = (p1["x"] - center["x"], p1["y"] - center["y"])
    a = d[0] ** 2 + d[1] ** 2
    b = 2 * (f[0] * d[0] + f[1] * d[1])
    c = f[0] ** 2 + f[1] ** 2 - radius ** 2
    disc = b * b - 4 * a * c
    if disc < 0:
        return []
    sqrt_disc = math.sqrt(disc)
    pts = []
    t1 = (-b - sqrt_disc) / (2 * a)
    t2 = (-b + sqrt_disc) / (2 * a)
    if 0 <= t1 <= 1:
        pts.append({"x": p1["x"] + t1 * d[0], "y": p1["y"] + t1 * d[1]})
    if 0 <= t2 <= 1 and abs(t2 - t1) > 1e-10:
        pts.append({"x": p1["x"] + t2 * d[0], "y": p1["y"] + t2 * d[1]})
    return pts


# ═══════════════════════════════════════════════════════════════════════════
# CONSTRAINT TYPES
# ═══════════════════════════════════════════════════════════════════════════

class ConstraintType(str, Enum):
    DISTANCE_EQUAL = "distance_equal"
    ANGLE_EQUAL = "angle_equal"
    POINT_ON_SEGMENT = "point_on_segment"
    POINT_ON_CIRCLE = "point_on_circle"
    COLLINEAR = "collinear"
    BETWEEN = "between"
    PERPENDICULAR = "perpendicular"
    PARALLEL = "parallel"
    RIGHT_ANGLE = "right_angle"
    DISTINCT = "distinct"


@dataclass
class VerifyResult:
    satisfied: bool
    error: Optional[str] = None
    details: dict = field(default_factory=dict)


# ═══════════════════════════════════════════════════════════════════════════
# CONSTRAINT VERIFIER
# ═══════════════════════════════════════════════════════════════════════════

class ConstraintVerifier:
    def __init__(self, canvas_data: Optional[dict] = None, tolerance: Tolerance = DEFAULT_TOLERANCE):
        self.points: Dict[str, dict] = {}
        self.segments: List[dict] = []
        self.circles: List[dict] = []
        self.angles: List[dict] = []
        self.tolerance = tolerance
        if canvas_data:
            self._index(canvas_data)

    def _index(self, data: dict):
        for p in data.get("points", []):
            self.points[p["label"]] = {"x": p["x"], "y": p["y"]}
        for s in data.get("segments", []):
            self.segments.append({
                "from": s["from"], "to": s["to"],
                "p1": self.points.get(s["from"]),
                "p2": self.points.get(s["to"]),
            })
        for c in data.get("circles", []):
            self.circles.append({
                "center": c["center"],
                "centerPt": self.points.get(c["center"]),
                "radius": c["radius"],
            })
        self.angles = data.get("angleMarks", [])

    def get_point(self, label: str) -> Optional[dict]:
        return self.points.get(label)

    def get_distance(self, a: str, b: str) -> Optional[float]:
        return distance(self.get_point(a), self.get_point(b))

    def get_angle(self, from_: str, vertex: str, to: str) -> Optional[float]:
        return angle_at_vertex(self.get_point(from_), self.get_point(vertex), self.get_point(to))

    def get_circle(self, center_label: str) -> Optional[dict]:
        return next((c for c in self.circles if c["center"] == center_label), None)

    def verify(self, constraint: dict) -> VerifyResult:
        ct = constraint.get("type")
        dispatch = {
            ConstraintType.DISTANCE_EQUAL: self._distance_equal,
            ConstraintType.ANGLE_EQUAL: self._angle_equal,
            ConstraintType.POINT_ON_SEGMENT: self._point_on_segment,
            ConstraintType.POINT_ON_CIRCLE: self._point_on_circle,
            ConstraintType.COLLINEAR: self._collinear,
            ConstraintType.BETWEEN: self._between,
            ConstraintType.PERPENDICULAR: self._perpendicular,
            ConstraintType.PARALLEL: self._parallel,
            ConstraintType.RIGHT_ANGLE: self._right_angle,
            ConstraintType.DISTINCT: self._distinct,
        }
        handler = dispatch.get(ct)
        if handler is None:
            return VerifyResult(False, f"Unknown constraint type: {ct}")
        return handler(constraint)

    def _distance_equal(self, c: dict) -> VerifyResult:
        s1, s2 = c["seg1"], c["seg2"]
        d1 = self.get_distance(s1["from"], s1["to"])
        d2 = self.get_distance(s2["from"], s2["to"])
        if d1 is None or d2 is None:
            return VerifyResult(False, "Could not compute distances", {"d1": d1, "d2": d2})
        diff = abs(d1 - d2)
        ok = diff <= self.tolerance.distance
        return VerifyResult(ok, None if ok else f"Distances differ by {diff:.2f}", {"d1": d1, "d2": d2, "diff": diff})

    def _angle_equal(self, c: dict) -> VerifyResult:
        a1i, a2i = c["angle1"], c["angle2"]
        a1 = self.get_angle(a1i["from"], a1i["vertex"], a1i["to"])
        a2 = self.get_angle(a2i["from"], a2i["vertex"], a2i["to"])
        if a1 is None or a2 is None:
            return VerifyResult(False, "Could not compute angles")
        diff = abs(a1 - a2)
        ok = diff <= self.tolerance.angle
        deg = math.degrees
        return VerifyResult(ok, None if ok else f"Angles differ by {deg(diff):.2f}°",
                            {"a1": deg(a1), "a2": deg(a2), "diff": deg(diff)})

    def _point_on_segment(self, c: dict) -> VerifyResult:
        p = self.get_point(c["point"])
        s1 = self.get_point(c["segFrom"])
        s2 = self.get_point(c["segTo"])
        if not all([p, s1, s2]):
            return VerifyResult(False, "Points not found")
        if not are_collinear(s1, p, s2, self.tolerance.collinear):
            return VerifyResult(False, "Point not collinear with segment")
        dt = distance(s1, s2) or 0
        d1 = distance(s1, p) or 0
        d2 = distance(s2, p) or 0
        if d1 > dt + self.tolerance.distance or d2 > dt + self.tolerance.distance:
            return VerifyResult(False, "Point outside segment")
        return VerifyResult(True)

    def _point_on_circle(self, c: dict) -> VerifyResult:
        p = self.get_point(c["point"])
        circ = self.get_circle(c["circleCenter"])
        if not p or not circ:
            return VerifyResult(False, "Point or circle not found")
        d = distance(circ["centerPt"], p)
        if d is None:
            return VerifyResult(False, "Cannot compute distance")
        diff = abs(d - circ["radius"])
        ok = diff <= self.tolerance.on_circle
        return VerifyResult(ok, None if ok else f"Point is {diff:.2f} units from circle")

    def _collinear(self, c: dict) -> VerifyResult:
        labels = c["points"]
        pts = [self.get_point(l) for l in labels]
        if any(p is None for p in pts):
            return VerifyResult(False, "Some points not found")
        for i in range(len(pts) - 2):
            if not are_collinear(pts[i], pts[i + 1], pts[i + 2], self.tolerance.collinear):
                return VerifyResult(False, f"Points {labels[i]}, {labels[i+1]}, {labels[i+2]} not collinear")
        return VerifyResult(True)

    def _between(self, c: dict) -> VerifyResult:
        a_l, b_l, c_l = c["points"]
        pa, pb, pc = self.get_point(a_l), self.get_point(b_l), self.get_point(c_l)
        if not all([pa, pb, pc]):
            return VerifyResult(False, "Points not found")
        if not are_collinear(pa, pb, pc, self.tolerance.collinear):
            return VerifyResult(False, "Points not collinear")
        d_ac = distance(pa, pc) or 0
        d_ab = distance(pa, pb) or 0
        d_bc = distance(pb, pc) or 0
        if abs((d_ab + d_bc) - d_ac) > self.tolerance.distance:
            return VerifyResult(False, f"{b_l} is not between {a_l} and {c_l}")
        return VerifyResult(True)

    def _perpendicular(self, c: dict) -> VerifyResult:
        s1, s2 = c["seg1"], c["seg2"]
        p1, p2 = self.get_point(s1["from"]), self.get_point(s1["to"])
        p3, p4 = self.get_point(s2["from"]), self.get_point(s2["to"])
        if not all([p1, p2, p3, p4]):
            return VerifyResult(False, "Points not found")
        d1 = (p2["x"] - p1["x"], p2["y"] - p1["y"])
        d2 = (p4["x"] - p3["x"], p4["y"] - p3["y"])
        m1, m2 = math.hypot(*d1), math.hypot(*d2)
        if m1 == 0 or m2 == 0:
            return VerifyResult(False, "Degenerate segment")
        cos_a = (d1[0] * d2[0] + d1[1] * d2[1]) / (m1 * m2)
        ok = abs(cos_a) < self.tolerance.angle
        return VerifyResult(ok, None if ok else f"Not perpendicular (cos={cos_a:.3f})")

    def _parallel(self, c: dict) -> VerifyResult:
        s1, s2 = c["seg1"], c["seg2"]
        p1, p2 = self.get_point(s1["from"]), self.get_point(s1["to"])
        p3, p4 = self.get_point(s2["from"]), self.get_point(s2["to"])
        if not all([p1, p2, p3, p4]):
            return VerifyResult(False, "Points not found")
        d1 = (p2["x"] - p1["x"], p2["y"] - p1["y"])
        d2 = (p4["x"] - p3["x"], p4["y"] - p3["y"])
        m1, m2 = math.hypot(*d1), math.hypot(*d2)
        if m1 == 0 or m2 == 0:
            return VerifyResult(False, "Degenerate segment")
        sin_a = (d1[0] * d2[1] - d1[1] * d2[0]) / (m1 * m2)
        ok = abs(sin_a) < self.tolerance.angle
        return VerifyResult(ok, None if ok else f"Not parallel (sin={sin_a:.3f})")

    def _right_angle(self, c: dict) -> VerifyResult:
        ai = c["angle"]
        a = self.get_angle(ai["from"], ai["vertex"], ai["to"])
        if a is None:
            return VerifyResult(False, "Could not compute angle")
        diff = abs(a - math.pi / 2)
        ok = diff <= self.tolerance.angle
        return VerifyResult(ok, None if ok else f"Angle is {math.degrees(a):.1f}°, not 90°")

    def _distinct(self, c: dict) -> VerifyResult:
        p1l, p2l = c["points"]
        p1, p2 = self.get_point(p1l), self.get_point(p2l)
        if not p1 or not p2:
            return VerifyResult(False, "Points not found")
        d = distance(p1, p2) or 0
        ok = d > self.tolerance.distance
        return VerifyResult(ok, None if ok else f"Points {p1l} and {p2l} coincide")
