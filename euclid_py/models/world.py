"""
World Model — ported from worldModel.js

Tarski's World–inspired geometric world state.
Separation of geometric world (canvas) from logical sentences.
"""
from __future__ import annotations

import json
import math
import time
from dataclasses import dataclass, field
from enum import Enum
from typing import Any, Dict, List, Optional, Tuple


# ═══════════════════════════════════════════════════════════════════════════
# WORLD OBJECT TYPES
# ═══════════════════════════════════════════════════════════════════════════

class WorldObjectType(str, Enum):
    POINT = "point"
    SEGMENT = "segment"
    LINE = "line"
    RAY = "ray"
    CIRCLE = "circle"
    ANGLE = "angle"
    TRIANGLE = "triangle"
    POLYGON = "polygon"


# ═══════════════════════════════════════════════════════════════════════════
# WORLD POINT
# ═══════════════════════════════════════════════════════════════════════════

@dataclass
class WorldPoint:
    label: str
    x: float
    y: float
    type: str = WorldObjectType.POINT

    def distance_to(self, other: WorldPoint) -> float:
        return math.hypot(self.x - other.x, self.y - other.y)

    def equals(self, other: WorldPoint, tolerance: float = 0.001) -> bool:
        return abs(self.x - other.x) < tolerance and abs(self.y - other.y) < tolerance

    def __str__(self) -> str:
        return self.label


# ═══════════════════════════════════════════════════════════════════════════
# WORLD SEGMENT
# ═══════════════════════════════════════════════════════════════════════════

@dataclass
class WorldSegment:
    from_pt: str
    to_pt: str
    is_ray: bool = False
    color: Optional[str] = None
    type: str = WorldObjectType.SEGMENT

    def length(self, world: GeometricWorld) -> Optional[float]:
        p1 = world.get_point(self.from_pt)
        p2 = world.get_point(self.to_pt)
        if not p1 or not p2:
            return None
        return p1.distance_to(p2)

    def equals_length(self, other: WorldSegment, world: GeometricWorld,
                      tolerance: float = 2.0) -> bool:
        l1 = self.length(world)
        l2 = other.length(world)
        if l1 is None or l2 is None:
            return False
        return abs(l1 - l2) < tolerance

    def contains_point(self, point: Any, world: GeometricWorld,
                       tolerance: float = 2.0) -> bool:
        p1 = world.get_point(self.from_pt)
        p2 = world.get_point(self.to_pt)
        pt = world.get_point(point) if isinstance(point, str) else point
        if not p1 or not p2 or not pt:
            return False
        d1 = p1.distance_to(pt)
        d2 = pt.distance_to(p2)
        total = p1.distance_to(p2)
        return abs(d1 + d2 - total) < tolerance

    def __str__(self) -> str:
        return f"{self.from_pt}{self.to_pt}"


# ═══════════════════════════════════════════════════════════════════════════
# WORLD CIRCLE
# ═══════════════════════════════════════════════════════════════════════════

@dataclass
class WorldCircle:
    center: str
    radius: float
    radius_label: Optional[str] = None
    color: Optional[str] = None
    type: str = WorldObjectType.CIRCLE

    def contains_point(self, point: Any, world: GeometricWorld,
                       tolerance: float = 2.0) -> bool:
        center_pt = world.get_point(self.center)
        pt = world.get_point(point) if isinstance(point, str) else point
        if not center_pt or not pt:
            return False
        dist = center_pt.distance_to(pt)
        return abs(dist - self.radius) < tolerance

    def contains_point_inside(self, point: Any, world: GeometricWorld) -> bool:
        center_pt = world.get_point(self.center)
        pt = world.get_point(point) if isinstance(point, str) else point
        if not center_pt or not pt:
            return False
        return center_pt.distance_to(pt) < self.radius

    def __str__(self) -> str:
        return f"⊙{self.center}"


# ═══════════════════════════════════════════════════════════════════════════
# WORLD ANGLE
# ═══════════════════════════════════════════════════════════════════════════

@dataclass
class WorldAngle:
    from_pt: str
    vertex: str
    to_pt: str
    is_right: bool = False
    color: Optional[str] = None
    type: str = WorldObjectType.ANGLE

    def measure(self, world: GeometricWorld) -> Optional[float]:
        """Measure in radians."""
        p_from = world.get_point(self.from_pt)
        p_vertex = world.get_point(self.vertex)
        p_to = world.get_point(self.to_pt)
        if not p_from or not p_vertex or not p_to:
            return None
        ang1 = math.atan2(p_from.y - p_vertex.y, p_from.x - p_vertex.x)
        ang2 = math.atan2(p_to.y - p_vertex.y, p_to.x - p_vertex.x)
        diff = abs(ang2 - ang1)
        if diff > math.pi:
            diff = 2 * math.pi - diff
        return diff

    def measure_degrees(self, world: GeometricWorld) -> Optional[float]:
        rad = self.measure(world)
        return math.degrees(rad) if rad is not None else None

    def is_right_angle(self, world: GeometricWorld, tolerance: float = 2.0) -> bool:
        deg = self.measure_degrees(world)
        return deg is not None and abs(deg - 90) < tolerance

    def equals_angle(self, other: WorldAngle, world: GeometricWorld,
                     tolerance: float = 0.05) -> bool:
        m1 = self.measure(world)
        m2 = other.measure(world)
        if m1 is None or m2 is None:
            return False
        return abs(m1 - m2) < tolerance

    def __str__(self) -> str:
        return f"∠{self.from_pt}{self.vertex}{self.to_pt}"


# ═══════════════════════════════════════════════════════════════════════════
# GEOMETRIC WORLD
# ═══════════════════════════════════════════════════════════════════════════

class GeometricWorld:
    """
    Geometric World — a model for evaluating geometric sentences.
    Analogous to Tarski's World.
    """

    def __init__(self, name: str = "Untitled World") -> None:
        self.name = name
        self.points: Dict[str, WorldPoint] = {}
        self.segments: List[WorldSegment] = []
        self.circles: List[WorldCircle] = []
        self.angles: List[WorldAngle] = []
        self.metadata: dict = dict(createdAt=time.time(), modifiedAt=time.time())

    # ── Point operations ──────────────────────────────────────────────────

    def add_point(self, label: str, x: float, y: float) -> WorldPoint:
        pt = WorldPoint(label=label, x=x, y=y)
        self.points[label] = pt
        self.metadata["modifiedAt"] = time.time()
        return pt

    def get_point(self, label: str) -> Optional[WorldPoint]:
        return self.points.get(label)

    def has_point(self, label: str) -> bool:
        return label in self.points

    def get_all_points(self) -> List[WorldPoint]:
        return list(self.points.values())

    def remove_point(self, label: str) -> bool:
        if label not in self.points:
            return False
        del self.points[label]
        self.segments = [s for s in self.segments if s.from_pt != label and s.to_pt != label]
        self.circles = [c for c in self.circles if c.center != label]
        self.angles = [a for a in self.angles
                       if a.from_pt != label and a.vertex != label and a.to_pt != label]
        self.metadata["modifiedAt"] = time.time()
        return True

    # ── Segment operations ────────────────────────────────────────────────

    def add_segment(self, from_pt: str, to_pt: str, *,
                    is_ray: bool = False, color: Optional[str] = None) -> WorldSegment:
        seg = WorldSegment(from_pt=from_pt, to_pt=to_pt, is_ray=is_ray, color=color)
        self.segments.append(seg)
        self.metadata["modifiedAt"] = time.time()
        return seg

    def get_segment(self, from_pt: str, to_pt: str) -> Optional[WorldSegment]:
        for s in self.segments:
            if (s.from_pt == from_pt and s.to_pt == to_pt) or \
               (s.from_pt == to_pt and s.to_pt == from_pt):
                return s
        return None

    def has_segment(self, from_pt: str, to_pt: str) -> bool:
        return self.get_segment(from_pt, to_pt) is not None

    def get_all_segments(self) -> List[WorldSegment]:
        return list(self.segments)

    def remove_segment(self, from_pt: str, to_pt: str) -> bool:
        for i, s in enumerate(self.segments):
            if (s.from_pt == from_pt and s.to_pt == to_pt) or \
               (s.from_pt == to_pt and s.to_pt == from_pt):
                self.segments.pop(i)
                self.metadata["modifiedAt"] = time.time()
                return True
        return False

    # ── Circle operations ─────────────────────────────────────────────────

    def add_circle(self, center: str, radius: float,
                   radius_label: Optional[str] = None, *,
                   color: Optional[str] = None) -> WorldCircle:
        circ = WorldCircle(center=center, radius=radius, radius_label=radius_label, color=color)
        self.circles.append(circ)
        self.metadata["modifiedAt"] = time.time()
        return circ

    def get_circle(self, center: str) -> Optional[WorldCircle]:
        for c in self.circles:
            if c.center == center:
                return c
        return None

    def get_all_circles(self) -> List[WorldCircle]:
        return list(self.circles)

    def remove_circle(self, center: str) -> bool:
        for i, c in enumerate(self.circles):
            if c.center == center:
                self.circles.pop(i)
                self.metadata["modifiedAt"] = time.time()
                return True
        return False

    # ── Angle operations ──────────────────────────────────────────────────

    def add_angle(self, from_pt: str, vertex: str, to_pt: str, *,
                  is_right: bool = False, color: Optional[str] = None) -> WorldAngle:
        ang = WorldAngle(from_pt=from_pt, vertex=vertex, to_pt=to_pt,
                         is_right=is_right, color=color)
        self.angles.append(ang)
        self.metadata["modifiedAt"] = time.time()
        return ang

    def get_angle(self, from_pt: str, vertex: str, to_pt: str) -> Optional[WorldAngle]:
        for a in self.angles:
            if a.vertex == vertex and \
               ((a.from_pt == from_pt and a.to_pt == to_pt) or
                (a.from_pt == to_pt and a.to_pt == from_pt)):
                return a
        return None

    def get_all_angles(self) -> List[WorldAngle]:
        return list(self.angles)

    # ── Distance calculations ─────────────────────────────────────────────

    def distance(self, label1: str, label2: str) -> Optional[float]:
        p1 = self.get_point(label1)
        p2 = self.get_point(label2)
        if not p1 or not p2:
            return None
        return p1.distance_to(p2)

    def segment_length(self, from_pt: str, to_pt: str) -> Optional[float]:
        seg = self.get_segment(from_pt, to_pt)
        if seg:
            return seg.length(self)
        return self.distance(from_pt, to_pt)

    # ── Geometric queries ─────────────────────────────────────────────────

    def are_collinear(self, p1_label: str, p2_label: str, p3_label: str,
                      tolerance: float = 2.0) -> bool:
        p1 = self.get_point(p1_label)
        p2 = self.get_point(p2_label)
        p3 = self.get_point(p3_label)
        if not p1 or not p2 or not p3:
            return False
        area = abs((p2.x - p1.x) * (p3.y - p1.y) - (p3.x - p1.x) * (p2.y - p1.y)) / 2
        max_dist = max(p1.distance_to(p2), p2.distance_to(p3), p1.distance_to(p3))
        return max_dist > 0 and area / max_dist < tolerance

    def is_on_circle(self, point_label: str, circle_center: str,
                     tolerance: float = 2.0) -> bool:
        circ = self.get_circle(circle_center)
        if not circ:
            return False
        return circ.contains_point(point_label, self, tolerance)

    def is_on_segment(self, point_label: str, seg_from: str, seg_to: str,
                      tolerance: float = 2.0) -> bool:
        seg = self.get_segment(seg_from, seg_to)
        if not seg:
            seg = WorldSegment(from_pt=seg_from, to_pt=seg_to)
        return seg.contains_point(point_label, self, tolerance)

    def is_between(self, between_label: str, end1_label: str, end2_label: str,
                   tolerance: float = 2.0) -> bool:
        bp = self.get_point(between_label)
        e1 = self.get_point(end1_label)
        e2 = self.get_point(end2_label)
        if not bp or not e1 or not e2:
            return False
        if not self.are_collinear(end1_label, between_label, end2_label, tolerance):
            return False
        d1 = e1.distance_to(bp)
        d2 = bp.distance_to(e2)
        total = e1.distance_to(e2)
        return abs(d1 + d2 - total) < tolerance and d1 > tolerance and d2 > tolerance

    def find_triangles(self) -> List[dict]:
        triangles: List[dict] = []
        n = len(self.segments)
        for i in range(n):
            for j in range(i + 1, n):
                for k in range(j + 1, n):
                    verts = set()
                    for seg in (self.segments[i], self.segments[j], self.segments[k]):
                        verts.add(seg.from_pt)
                        verts.add(seg.to_pt)
                    if len(verts) == 3:
                        sorted_v = sorted(verts)
                        if not any(t["vertices"] == sorted_v for t in triangles):
                            triangles.append(dict(
                                vertices=sorted_v,
                                segments=[self.segments[i], self.segments[j], self.segments[k]],
                            ))
        return triangles

    def is_equilateral_triangle(self, v1: str, v2: str, v3: str,
                                tolerance: float = 2.0) -> bool:
        s1 = self.distance(v1, v2)
        s2 = self.distance(v2, v3)
        s3 = self.distance(v3, v1)
        if s1 is None or s2 is None or s3 is None:
            return False
        if s1 < 1 or s2 < 1 or s3 < 1:
            return False
        avg = (s1 + s2 + s3) / 3
        rel_tol = max(tolerance, avg * 0.01)
        return abs(s1 - s2) < rel_tol and abs(s2 - s3) < rel_tol and abs(s1 - s3) < rel_tol

    # ── Serialization ─────────────────────────────────────────────────────

    def to_json(self) -> dict:
        return dict(
            format="euclid-world",
            version="1.0.0",
            name=self.name,
            metadata=self.metadata,
            points=[dict(label=pt.label, x=pt.x, y=pt.y) for pt in self.points.values()],
            segments=[dict(from_pt=s.from_pt, to_pt=s.to_pt, isRay=s.is_ray, color=s.color)
                      for s in self.segments],
            circles=[dict(center=c.center, radius=c.radius, radiusLabel=c.radius_label,
                          color=c.color) for c in self.circles],
            angles=[dict(from_pt=a.from_pt, vertex=a.vertex, to_pt=a.to_pt,
                         isRight=a.is_right, color=a.color) for a in self.angles],
        )

    @classmethod
    def from_json(cls, data: dict) -> GeometricWorld:
        if data.get("format") != "euclid-world":
            raise ValueError(f"Unknown world format: {data.get('format')}")
        world = cls(data.get("name", "Untitled"))
        world.metadata = data.get("metadata", {})
        for pt in data.get("points", []):
            world.add_point(pt["label"], pt["x"], pt["y"])
        for seg in data.get("segments", []):
            world.add_segment(seg.get("from") or seg.get("from_pt", ""),
                              seg.get("to") or seg.get("to_pt", ""),
                              is_ray=seg.get("isRay", False),
                              color=seg.get("color"))
        for circ in data.get("circles", []):
            world.add_circle(circ["center"], circ["radius"],
                             circ.get("radiusLabel"), color=circ.get("color"))
        for ang in data.get("angles", []):
            world.add_angle(ang.get("from") or ang.get("from_pt", ""),
                            ang["vertex"],
                            ang.get("to") or ang.get("to_pt", ""),
                            is_right=ang.get("isRight", False),
                            color=ang.get("color"))
        return world

    @classmethod
    def from_canvas_data(cls, canvas_data: dict) -> GeometricWorld:
        world = cls("Canvas World")
        for pt in canvas_data.get("points", []):
            world.add_point(pt["label"], pt["x"], pt["y"])
        for seg in canvas_data.get("segments", []):
            world.add_segment(seg.get("from", ""), seg.get("to", ""),
                              is_ray=seg.get("isRay", False),
                              color=seg.get("color"))
        for circ in canvas_data.get("circles", []):
            world.add_circle(circ["center"], circ["radius"],
                             circ.get("radiusLabel"), color=circ.get("color"))
        for ang in canvas_data.get("angleMarks", canvas_data.get("angles", [])):
            world.add_angle(ang.get("from", ""), ang["vertex"], ang.get("to", ""),
                            is_right=ang.get("isRight", False),
                            color=ang.get("color"))
        return world

    def to_canvas_data(self) -> dict:
        return dict(
            points=[dict(label=pt.label, x=pt.x, y=pt.y) for pt in self.points.values()],
            segments=[dict(**{"from": s.from_pt, "to": s.to_pt}, isRay=s.is_ray, color=s.color)
                      for s in self.segments],
            circles=[dict(center=c.center, radius=c.radius, radiusLabel=c.radius_label,
                          color=c.color) for c in self.circles],
            angleMarks=[dict(**{"from": a.from_pt}, vertex=a.vertex, to=a.to_pt,
                             isRight=a.is_right, color=a.color) for a in self.angles],
        )

    def get_stats(self) -> dict:
        return dict(
            points=len(self.points),
            segments=len(self.segments),
            circles=len(self.circles),
            angles=len(self.angles),
            triangles=len(self.find_triangles()),
        )

    def clone(self) -> GeometricWorld:
        return GeometricWorld.from_json(self.to_json())


# ═══════════════════════════════════════════════════════════════════════════
# UTILITY FUNCTIONS
# ═══════════════════════════════════════════════════════════════════════════

def create_world(name: str = "Untitled World") -> GeometricWorld:
    return GeometricWorld(name)


def world_from_canvas(canvas_data: dict) -> GeometricWorld:
    return GeometricWorld.from_canvas_data(canvas_data)


def serialize_world(world: GeometricWorld) -> str:
    return json.dumps(world.to_json(), indent=2)


def deserialize_world(json_string: str) -> GeometricWorld:
    data = json.loads(json_string)
    return GeometricWorld.from_json(data)
