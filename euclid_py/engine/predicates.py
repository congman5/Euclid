"""
Geometric Predicates — ported from geometricPredicates.js

Tarski's World–style predicate evaluation for geometric relations.
"""
from __future__ import annotations

import math
import re
from dataclasses import dataclass, field
from enum import Enum
from typing import Any, Dict, List, Optional, Tuple

from ..models.world import GeometricWorld, WorldAngle


# ═══════════════════════════════════════════════════════════════════════════
# PREDICATE RESULT
# ═══════════════════════════════════════════════════════════════════════════

@dataclass
class PredicateResult:
    value: Optional[bool]
    explanation: str = ""
    details: dict = field(default_factory=dict)

    @staticmethod
    def true_(explanation: str = "", details: Optional[dict] = None) -> PredicateResult:
        return PredicateResult(value=True, explanation=explanation, details=details or {})

    @staticmethod
    def false_(explanation: str = "", details: Optional[dict] = None) -> PredicateResult:
        return PredicateResult(value=False, explanation=explanation, details=details or {})

    @staticmethod
    def undefined(explanation: str = "", details: Optional[dict] = None) -> PredicateResult:
        return PredicateResult(value=None, explanation=explanation, details=details or {})

    @property
    def is_true(self) -> bool:
        return self.value is True

    @property
    def is_false(self) -> bool:
        return self.value is False

    @property
    def is_undefined(self) -> bool:
        return self.value is None


# ═══════════════════════════════════════════════════════════════════════════
# PREDICATE CATEGORIES
# ═══════════════════════════════════════════════════════════════════════════

class PredicateCategory(str, Enum):
    POINT = "Point"
    SEGMENT = "Segment"
    CIRCLE = "Circle"
    ANGLE = "Angle"
    RELATION = "Relation"
    LOGICAL = "Logical"


# ═══════════════════════════════════════════════════════════════════════════
# HELPERS
# ═══════════════════════════════════════════════════════════════════════════

def _resolve_segment_arg(args: List[str]) -> dict:
    if len(args) == 1:
        s = str(args[0])
        if len(s) >= 2 and re.match(r"^[A-Z]", s[0], re.I) and re.match(r"^[A-Z]", s[1], re.I):
            return dict(points=[s[0], s[1]], ok=True)
        return dict(error=f'"{s}" must be a segment (like AB) or two points', ok=False)
    if len(args) == 2:
        return dict(points=[str(args[0]), str(args[1])], ok=True)
    return dict(error=f"Expected 1 segment (AB) or 2 points, got {len(args)}", ok=False)


def _resolve_segment_pair_args(args: List[str]) -> dict:
    if len(args) == 2:
        s1, s2 = str(args[0]), str(args[1])
        if len(s1) >= 2 and len(s2) >= 2:
            return dict(points=[s1[0], s1[1], s2[0], s2[1]], ok=True)
        if len(s1) < 2:
            return dict(error=f'First argument "{s1}" must be a segment (like AB)', ok=False)
        return dict(error=f'Second argument "{s2}" must be a segment (like CD)', ok=False)
    if len(args) == 4:
        return dict(points=[str(a) for a in args], ok=True)
    return dict(error=f"Expected 2 segments (AB, CD) or 4 points, got {len(args)}", ok=False)


def _angle_at(world: GeometricWorld, pA: str, pB: str, pC: str) -> Optional[float]:
    """Compute angle in degrees at vertex B of triangle (A, B, C) using dot product."""
    ptA = world.get_point(pA)
    ptB = world.get_point(pB)
    ptC = world.get_point(pC)
    if not ptA or not ptB or not ptC:
        return None
    v1x, v1y = ptA.x - ptB.x, ptA.y - ptB.y
    v2x, v2y = ptC.x - ptB.x, ptC.y - ptB.y
    dot = v1x * v2x + v1y * v2y
    m1 = math.hypot(v1x, v1y)
    m2 = math.hypot(v2x, v2y)
    if m1 < 1e-9 or m2 < 1e-9:
        return None
    return math.degrees(math.acos(max(-1.0, min(1.0, dot / (m1 * m2)))))


# ═══════════════════════════════════════════════════════════════════════════
# PREDICATE DEFINITIONS
# ═══════════════════════════════════════════════════════════════════════════

@dataclass
class PredicateDef:
    name: str
    category: PredicateCategory
    arity: int
    signature: str
    description: str
    flexible_arity: Optional[List[int]] = None
    aliases: Optional[List[str]] = None


def _eval_point(world: GeometricWorld, args: List[str], options: dict) -> PredicateResult:
    p = args[0]
    pt = world.get_point(p)
    if pt:
        return PredicateResult.true_(f"Point {p} exists at ({pt.x:.1f}, {pt.y:.1f})")
    return PredicateResult.undefined(f"Point {p} does not exist — place it on the canvas")


def _eval_segment(world: GeometricWorld, args: List[str], options: dict) -> PredicateResult:
    res = _resolve_segment_arg(args)
    if not res["ok"]:
        return PredicateResult.undefined(res["error"])
    p, q = res["points"]
    if world.has_segment(p, q):
        length = world.segment_length(p, q)
        return PredicateResult.true_(f"Segment {p}{q} exists (length: {length:.1f})" if length else f"Segment {p}{q} exists",
                                     dict(length=length))
    return PredicateResult.undefined(f"Segment {p}{q} does not exist — draw it on the canvas")


def _eval_circle(world: GeometricWorld, args: List[str], options: dict) -> PredicateResult:
    if len(args) == 1 and len(str(args[0])) == 2 and re.match(r"^[A-Z]{2}$", str(args[0]), re.I):
        c, p = str(args[0])[0], str(args[0])[1]
    else:
        c = str(args[0])
        p = str(args[1]) if len(args) >= 2 else None

    circle = world.get_circle(c)
    if not circle:
        return PredicateResult.undefined(f"Circle with center {c} does not exist — draw it on the canvas")
    if not p:
        return PredicateResult.true_(f"Circle with center {c} exists (radius: {circle.radius:.1f})",
                                     dict(radius=circle.radius))
    center_pt = world.get_point(c)
    circum_pt = world.get_point(p)
    if not center_pt:
        return PredicateResult.undefined(f"Center point {c} does not exist")
    if not circum_pt:
        return PredicateResult.undefined(f"Point {p} does not exist")
    dist = center_pt.distance_to(circum_pt)
    tolerance = options.get("tolerance", 3)
    diff = abs(circle.radius - dist)
    if diff < tolerance:
        return PredicateResult.true_(
            f"Circle ⊙{c} through {p}: radius {circle.radius:.1f} ≈ dist({c},{p}) = {dist:.1f}",
            dict(radius=circle.radius, distance=dist))
    return PredicateResult.false_(
        f"Circle ⊙{c} radius {circle.radius:.1f} ≠ dist({c},{p}) = {dist:.1f} (off by {diff:.1f})",
        dict(radius=circle.radius, distance=dist, difference=diff))


def _eval_on_segment(world: GeometricWorld, args: List[str], options: dict) -> PredicateResult:
    if len(args) == 2:
        p = str(args[0])
        seg = str(args[1])
        if len(seg) >= 2:
            a, b = seg[0], seg[1]
        else:
            return PredicateResult.undefined(f'Second argument "{seg}" must be a segment (like AB)')
    elif len(args) == 3:
        p, a, b = str(args[0]), str(args[1]), str(args[2])
    else:
        return PredicateResult.undefined(f"OnSegment requires (p, AB) or (p, A, B), got {len(args)} args")
    tolerance = options.get("tolerance", 2)
    if not world.has_point(p) or not world.has_point(a) or not world.has_point(b):
        return PredicateResult.undefined("One or more points do not exist")
    is_on = world.is_on_segment(p, a, b, tolerance)
    if is_on:
        return PredicateResult.true_(f"Point {p} lies on segment {a}{b}")
    return PredicateResult.false_(f"Point {p} does not lie on segment {a}{b}")


def _eval_on_circle(world: GeometricWorld, args: List[str], options: dict) -> PredicateResult:
    if len(args) == 2:
        p = str(args[0])
        seg = str(args[1])
        if len(seg) == 2 and re.match(r"^[A-Z]{2}$", seg, re.I):
            c, r = seg[0], seg[1]
        else:
            return PredicateResult.undefined(f'Second argument "{seg}" must be like AB where A=center, B=radius point')
    elif len(args) == 3:
        p, c, r = str(args[0]), str(args[1]), str(args[2])
    else:
        return PredicateResult.undefined(f"OnCircle requires (p, AB) or (p, A, B), got {len(args)} args")
    if not world.has_point(p):
        return PredicateResult.undefined(f"Point {p} does not exist — place it on the canvas")
    if not world.has_point(c):
        return PredicateResult.undefined(f"Center point {c} does not exist")
    if not world.has_point(r):
        return PredicateResult.undefined(f"Radius point {r} does not exist")
    circle = world.get_circle(c)
    if not circle:
        return PredicateResult.undefined(f"Circle with center {c} not on canvas — draw it first")
    tolerance = options.get("tolerance", 2)
    center_pt = world.get_point(c)
    pt = world.get_point(p)
    dist_p = center_pt.distance_to(pt)
    diff = abs(dist_p - circle.radius)
    if diff < tolerance:
        return PredicateResult.true_(
            f"{p} on ⊙{c}: dist({c},{p}) = {dist_p:.1f}, radius = {circle.radius:.1f}",
            dict(distance=dist_p, radius=circle.radius))
    return PredicateResult.false_(
        f"{p} not on ⊙{c}: dist({c},{p}) = {dist_p:.1f} but radius = {circle.radius:.1f} (off by {diff:.1f})",
        dict(distance=dist_p, radius=circle.radius, difference=diff))


def _eval_inside_circle(world: GeometricWorld, args: List[str], options: dict) -> PredicateResult:
    p, c = str(args[0]), str(args[1])
    circle = world.get_circle(c)
    if not circle:
        return PredicateResult.undefined(f"Circle with center {c} does not exist")
    if circle.contains_point_inside(p, world):
        return PredicateResult.true_(f"Point {p} is inside circle ⊙{c}")
    return PredicateResult.false_(f"Point {p} is not inside circle ⊙{c}")


def _eval_between(world: GeometricWorld, args: List[str], options: dict) -> PredicateResult:
    b, a, c = str(args[0]), str(args[1]), str(args[2])
    tolerance = options.get("tolerance", 2)
    for pt in (a, b, c):
        if not world.has_point(pt):
            return PredicateResult.undefined(f"Point {pt} does not exist")
    if world.is_between(b, a, c, tolerance):
        return PredicateResult.true_(f"Point {b} is between {a} and {c}")
    return PredicateResult.false_(f"Point {b} is not between {a} and {c}")


def _eval_collinear(world: GeometricWorld, args: List[str], options: dict) -> PredicateResult:
    a, b, c = str(args[0]), str(args[1]), str(args[2])
    tolerance = options.get("tolerance", 2)
    for pt in (a, b, c):
        if not world.has_point(pt):
            return PredicateResult.undefined(f"Point {pt} does not exist")
    if world.are_collinear(a, b, c, tolerance):
        return PredicateResult.true_(f"Points {a}, {b}, {c} are collinear")
    return PredicateResult.false_(f"Points {a}, {b}, {c} are not collinear")


def _eval_equal(world: GeometricWorld, args: List[str], options: dict) -> PredicateResult:
    tolerance = options.get("tolerance", 2)
    res = _resolve_segment_pair_args(args)
    if not res["ok"]:
        return PredicateResult.undefined(res["error"])
    a, b, c, d = res["points"]
    len1 = world.segment_length(a, b)
    len2 = world.segment_length(c, d)
    if len1 is None:
        return PredicateResult.undefined(f"Cannot compute length of {a}{b}")
    if len2 is None:
        return PredicateResult.undefined(f"Cannot compute length of {c}{d}")
    diff = abs(len1 - len2)
    if diff < tolerance:
        return PredicateResult.true_(f"|{a}{b}| = {len1:.1f} ≈ |{c}{d}| = {len2:.1f}",
                                     dict(len1=len1, len2=len2, diff=diff))
    return PredicateResult.false_(f"|{a}{b}| = {len1:.1f} ≠ |{c}{d}| = {len2:.1f} (diff: {diff:.1f})",
                                  dict(len1=len1, len2=len2, diff=diff))


def _eval_equal_angle(world: GeometricWorld, args: List[str], options: dict) -> PredicateResult:
    p1, v1, q1, p2, v2, q2 = [str(a) for a in args]
    tolerance = options.get("tolerance", 2)
    for pt in (p1, v1, q1, p2, v2, q2):
        if not world.has_point(pt):
            return PredicateResult.undefined(f"Point {pt} does not exist")
    ang1 = WorldAngle(from_pt=p1, vertex=v1, to_pt=q1)
    ang2 = WorldAngle(from_pt=p2, vertex=v2, to_pt=q2)
    deg1 = ang1.measure_degrees(world)
    deg2 = ang2.measure_degrees(world)
    if deg1 is None or deg2 is None:
        return PredicateResult.undefined("Cannot compute angle measures")
    diff = abs(deg1 - deg2)
    if diff < tolerance:
        return PredicateResult.true_(
            f"∠{p1}{v1}{q1} = {deg1:.1f}° ≈ ∠{p2}{v2}{q2} = {deg2:.1f}°",
            dict(angle1=deg1, angle2=deg2))
    return PredicateResult.false_(
        f"∠{p1}{v1}{q1} = {deg1:.1f}° ≠ ∠{p2}{v2}{q2} = {deg2:.1f}°",
        dict(angle1=deg1, angle2=deg2, diff=diff))


def _eval_congruent(world: GeometricWorld, args: List[str], options: dict) -> PredicateResult:
    a, b, c, d, e, f = [str(x) for x in args]
    tolerance = options.get("tolerance", 2)
    angle_tol = options.get("angleTolerance", 2)
    s = [world.distance(a, b), world.distance(b, c), world.distance(c, a)]
    t = [world.distance(d, e), world.distance(e, f), world.distance(f, d)]
    if any(v is None for v in s) or any(v is None for v in t):
        return PredicateResult.undefined("Cannot compute all side lengths")
    # SSS
    s1 = sorted(s)
    t1 = sorted(t)
    if all(abs(s1[i] - t1[i]) < tolerance for i in range(3)):
        return PredicateResult.true_(f"△{a}{b}{c} ≅ △{d}{e}{f} (SSS)", dict(sides1=s, sides2=t))
    # SAS with rotations and reflections
    verts1 = [a, b, c]
    for v2 in ([d, e, f], [e, f, d], [f, d, e]):
        for flip in range(2):
            tv = v2 if flip == 0 else [v2[0], v2[2], v2[1]]
            ts2 = [world.distance(tv[0], tv[1]), world.distance(tv[1], tv[2]), world.distance(tv[2], tv[0])]
            for k in range(3):
                side_a_eq = abs(s[k] - ts2[k]) < tolerance
                side_b_eq = abs(s[(k + 2) % 3] - ts2[(k + 2) % 3]) < tolerance
                if side_a_eq and side_b_eq:
                    ang1 = _angle_at(world, verts1[k], verts1[(k + 1) % 3], verts1[(k + 2) % 3])
                    ang2 = _angle_at(world, tv[k], tv[(k + 1) % 3], tv[(k + 2) % 3])
                    if ang1 is not None and ang2 is not None and abs(ang1 - ang2) < angle_tol:
                        return PredicateResult.true_(f"△{a}{b}{c} ≅ △{d}{e}{f} (SAS)", dict(sides1=s, sides2=t))
    return PredicateResult.false_(f"△{a}{b}{c} ≇ △{d}{e}{f}", dict(sides1=s, sides2=t))


def _eval_equilateral(world: GeometricWorld, args: List[str], options: dict) -> PredicateResult:
    a, b, c = str(args[0]), str(args[1]), str(args[2])
    tolerance = options.get("tolerance", 2)
    if world.is_equilateral_triangle(a, b, c, tolerance):
        side = world.distance(a, b)
        return PredicateResult.true_(f"△{a}{b}{c} is equilateral (side length: {side:.1f})" if side else f"△{a}{b}{c} is equilateral",
                                     dict(sideLength=side))
    s1 = world.distance(a, b)
    s2 = world.distance(b, c)
    s3 = world.distance(c, a)
    return PredicateResult.false_(
        f"△{a}{b}{c} is not equilateral: |{a}{b}|={_fmt(s1)}, |{b}{c}|={_fmt(s2)}, |{c}{a}|={_fmt(s3)}",
        dict(sides=[s1, s2, s3]))


def _eval_isosceles(world: GeometricWorld, args: List[str], options: dict) -> PredicateResult:
    a, b, c = str(args[0]), str(args[1]), str(args[2])
    tolerance = options.get("tolerance", 2)
    s1 = world.distance(a, b)
    s2 = world.distance(b, c)
    s3 = world.distance(c, a)
    if s1 is None or s2 is None or s3 is None:
        return PredicateResult.undefined("Cannot compute side lengths")
    if abs(s1 - s2) < tolerance or abs(s2 - s3) < tolerance or abs(s1 - s3) < tolerance:
        return PredicateResult.true_(f"△{a}{b}{c} is isosceles")
    return PredicateResult.false_(f"△{a}{b}{c} is not isosceles: sides {s1:.1f}, {s2:.1f}, {s3:.1f}")


def _eval_right_angle(world: GeometricWorld, args: List[str], options: dict) -> PredicateResult:
    p, v, q = str(args[0]), str(args[1]), str(args[2])
    tolerance = options.get("tolerance", 2)
    for pt in (p, v, q):
        if not world.has_point(pt):
            return PredicateResult.undefined(f"Point {pt} does not exist")
    ang = WorldAngle(from_pt=p, vertex=v, to_pt=q)
    deg = ang.measure_degrees(world)
    if deg is None:
        return PredicateResult.undefined("Cannot compute angle measure")
    if abs(deg - 90) < tolerance:
        return PredicateResult.true_(f"∠{p}{v}{q} = {deg:.1f}° is a right angle")
    return PredicateResult.false_(f"∠{p}{v}{q} = {deg:.1f}° is not a right angle")


def _eval_parallel(world: GeometricWorld, args: List[str], options: dict) -> PredicateResult:
    res = _resolve_segment_pair_args(args)
    if not res["ok"]:
        return PredicateResult.undefined(res["error"])
    a, b, c, d = res["points"]
    tolerance = options.get("tolerance", 0.01)
    pA, pB, pC, pD = [world.get_point(x) for x in (a, b, c, d)]
    if not all((pA, pB, pC, pD)):
        return PredicateResult.undefined("One or more points do not exist")
    dx1, dy1 = pB.x - pA.x, pB.y - pA.y
    dx2, dy2 = pD.x - pC.x, pD.y - pC.y
    cross = dx1 * dy2 - dy1 * dx2
    mag1 = math.hypot(dx1, dy1)
    mag2 = math.hypot(dx2, dy2)
    if mag1 < 1e-9 or mag2 < 1e-9:
        return PredicateResult.undefined("Degenerate segment")
    sin_angle = abs(cross) / (mag1 * mag2)
    if sin_angle < tolerance:
        return PredicateResult.true_(f"Line {a}{b} ∥ line {c}{d}")
    return PredicateResult.false_(f"Line {a}{b} is not parallel to line {c}{d}")


def _eval_perpendicular(world: GeometricWorld, args: List[str], options: dict) -> PredicateResult:
    res = _resolve_segment_pair_args(args)
    if not res["ok"]:
        return PredicateResult.undefined(res["error"])
    a, b, c, d = res["points"]
    tolerance = options.get("tolerance", 0.02)
    pA, pB, pC, pD = [world.get_point(x) for x in (a, b, c, d)]
    if not all((pA, pB, pC, pD)):
        return PredicateResult.undefined("One or more points do not exist")
    dx1, dy1 = pB.x - pA.x, pB.y - pA.y
    dx2, dy2 = pD.x - pC.x, pD.y - pC.y
    dot = dx1 * dx2 + dy1 * dy2
    mag1 = math.hypot(dx1, dy1)
    mag2 = math.hypot(dx2, dy2)
    if mag1 < 1e-9 or mag2 < 1e-9:
        return PredicateResult.undefined("Degenerate segment")
    cos_angle = dot / (mag1 * mag2)
    if abs(cos_angle) < tolerance:
        return PredicateResult.true_(f"Line {a}{b} ⊥ line {c}{d}")
    return PredicateResult.false_(f"Line {a}{b} is not perpendicular to line {c}{d}")


def _eval_shorter(world: GeometricWorld, args: List[str], options: dict) -> PredicateResult:
    res = _resolve_segment_pair_args(args)
    if not res["ok"]:
        return PredicateResult.undefined(res["error"])
    a, b, c, d = res["points"]
    l1 = world.segment_length(a, b)
    l2 = world.segment_length(c, d)
    if l1 is None or l2 is None:
        return PredicateResult.undefined("Cannot compute segment lengths")
    if l1 < l2:
        return PredicateResult.true_(f"|{a}{b}| = {l1:.1f} < |{c}{d}| = {l2:.1f}")
    return PredicateResult.false_(f"|{a}{b}| = {l1:.1f} ≥ |{c}{d}| = {l2:.1f}")


def _eval_longer(world: GeometricWorld, args: List[str], options: dict) -> PredicateResult:
    res = _resolve_segment_pair_args(args)
    if not res["ok"]:
        return PredicateResult.undefined(res["error"])
    a, b, c, d = res["points"]
    l1 = world.segment_length(a, b)
    l2 = world.segment_length(c, d)
    if l1 is None or l2 is None:
        return PredicateResult.undefined("Cannot compute segment lengths")
    if l1 > l2:
        return PredicateResult.true_(f"|{a}{b}| = {l1:.1f} > |{c}{d}| = {l2:.1f}")
    return PredicateResult.false_(f"|{a}{b}| = {l1:.1f} ≤ |{c}{d}| = {l2:.1f}")


def _eval_equal_circle(world: GeometricWorld, args: List[str], options: dict) -> PredicateResult:
    c1, c2 = str(args[0]), str(args[1])
    tolerance = options.get("tolerance", 2)
    circ1 = world.get_circle(c1)
    circ2 = world.get_circle(c2)
    if not circ1:
        return PredicateResult.undefined(f"Circle with center {c1} does not exist")
    if not circ2:
        return PredicateResult.undefined(f"Circle with center {c2} does not exist")
    r1, r2 = circ1.radius, circ2.radius
    diff = abs(r1 - r2)
    if diff < tolerance:
        return PredicateResult.true_(f"⊙{c1} radius {r1:.1f} ≈ ⊙{c2} radius {r2:.1f}",
                                     dict(r1=r1, r2=r2, diff=diff))
    return PredicateResult.false_(f"⊙{c1} radius {r1:.1f} ≠ ⊙{c2} radius {r2:.1f} (diff: {diff:.1f})",
                                  dict(r1=r1, r2=r2, diff=diff))


def _fmt(v: Optional[float]) -> str:
    return f"{v:.1f}" if v is not None else "?"


# ═══════════════════════════════════════════════════════════════════════════
# PREDICATE REGISTRY
# ═══════════════════════════════════════════════════════════════════════════

_PREDICATES: Dict[str, Tuple[PredicateDef, Any]] = {}


def _register(defn: PredicateDef, fn: Any) -> None:
    _PREDICATES[defn.name.lower()] = (defn, fn)
    for alias in defn.aliases or []:
        _PREDICATES[alias.lower()] = (defn, fn)


# Register all predicates
_register(PredicateDef("Point", PredicateCategory.POINT, 1, "Point(p)", "Point p exists in the world"), _eval_point)
_register(PredicateDef("Segment", PredicateCategory.SEGMENT, 2, "Segment(AB) or Segment(A, B)", "Segment from p to q exists", flexible_arity=[1, 2]), _eval_segment)
_register(PredicateDef("Circle", PredicateCategory.CIRCLE, 2, "Circle(c, p)", "Circle with center c through point p", flexible_arity=[1, 2]), _eval_circle)
_register(PredicateDef("OnSegment", PredicateCategory.RELATION, 3, "OnSegment(p, AB) or OnSegment(p, A, B)", "Point p lies on segment ab", flexible_arity=[2, 3]), _eval_on_segment)
_register(PredicateDef("OnCircle", PredicateCategory.CIRCLE, 3, "OnCircle(p, c, r) or OnCircle(p, AB)", "Point p lies on circle centered at c through r", flexible_arity=[2, 3]), _eval_on_circle)
_register(PredicateDef("InsideCircle", PredicateCategory.CIRCLE, 2, "InsideCircle(p, c)", "Point p is inside circle with center c"), _eval_inside_circle)
_register(PredicateDef("Between", PredicateCategory.RELATION, 3, "Between(b, a, c)", "Point b is between points a and c on a line"), _eval_between)
_register(PredicateDef("Collinear", PredicateCategory.RELATION, 3, "Collinear(a, b, c)", "Points a, b, c lie on the same line"), _eval_collinear)
_register(PredicateDef("Equal", PredicateCategory.SEGMENT, 4, "Equal(AB, CD) or Equal(A, B, C, D)", "Segments have equal length", flexible_arity=[2, 4], aliases=["EqualSeg", "SameLength"]), _eval_equal)
_register(PredicateDef("EqualAngle", PredicateCategory.ANGLE, 6, "EqualAngle(p1, v1, q1, p2, v2, q2)", "Angle p1-v1-q1 equals angle p2-v2-q2"), _eval_equal_angle)
_register(PredicateDef("Congruent", PredicateCategory.RELATION, 6, "Congruent(a, b, c, d, e, f)", "Triangle abc is congruent to triangle def (SSS or SAS)"), _eval_congruent)
_register(PredicateDef("Equilateral", PredicateCategory.RELATION, 3, "Equilateral(a, b, c)", "Triangle abc is equilateral (all sides equal)"), _eval_equilateral)
_register(PredicateDef("Isosceles", PredicateCategory.RELATION, 3, "Isosceles(a, b, c)", "Triangle abc is isosceles (at least two sides equal)"), _eval_isosceles)
_register(PredicateDef("RightAngle", PredicateCategory.ANGLE, 3, "RightAngle(p, v, q)", "Angle p-v-q is a right angle (90°)"), _eval_right_angle)
_register(PredicateDef("Parallel", PredicateCategory.RELATION, 4, "Parallel(AB, CD) or Parallel(A, B, C, D)", "Lines ab and cd are parallel", flexible_arity=[2, 4]), _eval_parallel)
_register(PredicateDef("Perpendicular", PredicateCategory.RELATION, 4, "Perpendicular(AB, CD) or Perpendicular(A, B, C, D)", "Lines ab and cd are perpendicular", flexible_arity=[2, 4]), _eval_perpendicular)
_register(PredicateDef("Shorter", PredicateCategory.SEGMENT, 4, "Shorter(AB, CD) or Shorter(A, B, C, D)", "Segment ab is shorter than segment cd", flexible_arity=[2, 4]), _eval_shorter)
_register(PredicateDef("Longer", PredicateCategory.SEGMENT, 4, "Longer(AB, CD) or Longer(A, B, C, D)", "Segment ab is longer than segment cd", flexible_arity=[2, 4]), _eval_longer)
_register(PredicateDef("EqualCircle", PredicateCategory.CIRCLE, 2, "EqualCircle(c1, c2)", "Circles centered at c1 and c2 have equal radii"), _eval_equal_circle)


def get_predicate(name: str) -> Optional[PredicateDef]:
    entry = _PREDICATES.get(name.lower())
    return entry[0] if entry else None


def get_all_predicates() -> List[PredicateDef]:
    seen = set()
    result = []
    for defn, _ in _PREDICATES.values():
        if defn.name not in seen:
            seen.add(defn.name)
            result.append(defn)
    return result


def get_predicates_by_category(category: PredicateCategory) -> List[PredicateDef]:
    return [p for p in get_all_predicates() if p.category == category]


def evaluate_predicate(name: str, world: GeometricWorld, args: List[str],
                       options: Optional[dict] = None) -> PredicateResult:
    options = options or {}
    entry = _PREDICATES.get(name.lower())
    if not entry:
        return PredicateResult.undefined(f"Unknown predicate: {name}")
    defn, fn = entry
    if defn.flexible_arity:
        if len(args) not in defn.flexible_arity:
            return PredicateResult.undefined(
                f"{name} accepts {' or '.join(str(a) for a in defn.flexible_arity)} arguments, got {len(args)}")
    elif len(args) != defn.arity:
        return PredicateResult.undefined(f"{name} requires {defn.arity} arguments, got {len(args)}")
    return fn(world, args, options)


# ═══════════════════════════════════════════════════════════════════════════
# PREDICATE PALETTE (for UI)
# ═══════════════════════════════════════════════════════════════════════════

def get_predicate_palette() -> List[dict]:
    return [
        dict(category="Existence", predicates=[
            dict(name="Point", signature="Point(p)", arity=1),
            dict(name="Segment", signature="Segment(AB) or Segment(A, B)", arity=1),
            dict(name="Circle", signature="Circle(c, p)", arity=2),
        ]),
        dict(category="Incidence", predicates=[
            dict(name="OnSegment", signature="OnSegment(p, AB) or OnSegment(p, A, B)", arity=2),
            dict(name="OnCircle", signature="OnCircle(p, c, r) or OnCircle(p, AB)", arity=3),
            dict(name="InsideCircle", signature="InsideCircle(p, c)", arity=2),
        ]),
        dict(category="Order", predicates=[
            dict(name="Between", signature="Between(b, a, c)", arity=3),
            dict(name="Collinear", signature="Collinear(a, b, c)", arity=3),
        ]),
        dict(category="Equality", predicates=[
            dict(name="Equal", signature="Equal(AB, CD) or AB = CD", arity=2),
            dict(name="EqualAngle", signature="EqualAngle(p1,v1,q1,p2,v2,q2)", arity=6),
            dict(name="EqualCircle", signature="EqualCircle(c1, c2)", arity=2),
            dict(name="Congruent", signature="Congruent(a,b,c,d,e,f) SSS/SAS", arity=6),
        ]),
        dict(category="Shape", predicates=[
            dict(name="Equilateral", signature="Equilateral(a, b, c)", arity=3),
            dict(name="Isosceles", signature="Isosceles(a, b, c)", arity=3),
            dict(name="RightAngle", signature="RightAngle(p, v, q)", arity=3),
        ]),
        dict(category="Lines", predicates=[
            dict(name="Parallel", signature="Parallel(AB, CD) or Parallel(A, B, C, D)", arity=2),
            dict(name="Perpendicular", signature="Perpendicular(AB, CD) or Perpendicular(A, B, C, D)", arity=2),
        ]),
        dict(category="Comparison", predicates=[
            dict(name="Shorter", signature="Shorter(AB, CD) or Shorter(A, B, C, D)", arity=2),
            dict(name="Longer", signature="Longer(AB, CD) or Longer(A, B, C, D)", arity=2),
        ]),
    ]
