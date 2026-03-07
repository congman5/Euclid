"""
Geometric Expression AST — ported from geometricExpr.js

Defines the abstract syntax tree for geometric expressions,
mirroring how Aris handles logical expressions but for geometry.
"""
from __future__ import annotations

import json
from dataclasses import dataclass, field
from enum import Enum
from typing import Any, List, Optional, Set


# ═══════════════════════════════════════════════════════════════════════════
# EXPRESSION TYPES — Core geometric objects
# ═══════════════════════════════════════════════════════════════════════════

class ExprType(str, Enum):
    # Primitives
    POINT = "POINT"
    LINE = "LINE"
    SEGMENT = "SEGMENT"
    RAY = "RAY"
    CIRCLE = "CIRCLE"
    ARC = "ARC"
    ANGLE = "ANGLE"
    # Composite figures
    TRIANGLE = "TRIANGLE"
    QUADRILATERAL = "QUADRILATERAL"
    POLYGON = "POLYGON"
    # Relations / Predicates
    EQUALS = "EQUALS"
    CONGRUENT = "CONGRUENT"
    SIMILAR = "SIMILAR"
    PARALLEL = "PARALLEL"
    PERPENDICULAR = "PERPENDICULAR"
    INTERSECTS = "INTERSECTS"
    LIES_ON = "LIES_ON"
    BETWEEN = "BETWEEN"
    # Logical
    AND = "AND"
    OR = "OR"
    IMPLIES = "IMPLIES"
    NOT = "NOT"
    # Special
    ASSERTION = "ASSERTION"
    CONSTRUCTION = "CONSTRUCTION"
    CONTRADICTION = "CONTRADICTION"


# ═══════════════════════════════════════════════════════════════════════════
# Base Expression class (thin wrapper dict-like for compatibility)
# ═══════════════════════════════════════════════════════════════════════════

class Expr(dict):
    """A geometric expression stored as a dict for flexible attribute access."""

    def __getattr__(self, key: str) -> Any:
        try:
            return self[key]
        except KeyError:
            raise AttributeError(key)

    def __setattr__(self, key: str, value: Any) -> None:
        self[key] = value

    # convenience
    @property
    def expr_type(self) -> ExprType:
        return ExprType(self["type"])


# ═══════════════════════════════════════════════════════════════════════════
# PRIMITIVE CONSTRUCTORS
# ═══════════════════════════════════════════════════════════════════════════

def point(label: str, x: Optional[float] = None, y: Optional[float] = None) -> Expr:
    return Expr(type=ExprType.POINT, label=label, x=x, y=y)


def line(point1: str, point2: str) -> Expr:
    return Expr(type=ExprType.LINE, points=[point1, point2])


def segment(from_pt: str, to_pt: str) -> Expr:
    return Expr(type=ExprType.SEGMENT, **{"from": from_pt, "to": to_pt})


def ray(origin: str, through: str) -> Expr:
    return Expr(type=ExprType.RAY, origin=origin, through=through)


def circle(center: str, radius: Any) -> Expr:
    if isinstance(radius, str):
        radius_obj = Expr(type="SEGMENT", **{"from": center, "to": radius})
        return Expr(type=ExprType.CIRCLE, center=center, radius=radius_obj, radiusLabel=radius)
    return Expr(type=ExprType.CIRCLE, center=center, radius=radius, radiusLabel=None)


def arc(center: str, from_pt: str, to_pt: str) -> Expr:
    return Expr(type=ExprType.ARC, center=center, **{"from": from_pt, "to": to_pt})


def angle(from_pt: str, vertex: str, to_pt: str) -> Expr:
    return Expr(type=ExprType.ANGLE, **{"from": from_pt}, vertex=vertex, to=to_pt)


# ═══════════════════════════════════════════════════════════════════════════
# COMPOSITE FIGURE CONSTRUCTORS
# ═══════════════════════════════════════════════════════════════════════════

def triangle(a: str, b: str, c: str) -> Expr:
    return Expr(
        type=ExprType.TRIANGLE,
        vertices=[a, b, c],
        sides=[segment(a, b), segment(b, c), segment(c, a)],
        angles=[angle(c, a, b), angle(a, b, c), angle(b, c, a)],
    )


def quadrilateral(a: str, b: str, c: str, d: str) -> Expr:
    return Expr(type=ExprType.QUADRILATERAL, vertices=[a, b, c, d])


def polygon(*vertices: str) -> Expr:
    return Expr(type=ExprType.POLYGON, vertices=list(vertices), n=len(vertices))


# ═══════════════════════════════════════════════════════════════════════════
# RELATION / PREDICATE CONSTRUCTORS
# ═══════════════════════════════════════════════════════════════════════════

def equals(left: Expr, right: Expr) -> Expr:
    return Expr(type=ExprType.EQUALS, left=left, right=right)


def congruent(left: Expr, right: Expr) -> Expr:
    return Expr(type=ExprType.CONGRUENT, left=left, right=right)


def similar(left: Expr, right: Expr) -> Expr:
    return Expr(type=ExprType.SIMILAR, left=left, right=right)


def parallel(line1: Expr, line2: Expr) -> Expr:
    return Expr(type=ExprType.PARALLEL, left=line1, right=line2)


def perpendicular(line1: Expr, line2: Expr) -> Expr:
    return Expr(type=ExprType.PERPENDICULAR, left=line1, right=line2)


def intersects(obj1: Expr, obj2: Expr, result_point: Optional[str] = None) -> Expr:
    return Expr(type=ExprType.INTERSECTS, objects=[obj1, obj2], result=result_point)


def lies_on(pt: str, obj: Expr) -> Expr:
    return Expr(type=ExprType.LIES_ON, point=pt, object=obj)


def between(mid: str, end1: str, end2: str) -> Expr:
    return Expr(type=ExprType.BETWEEN, between=mid, endpoints=[end1, end2])


# ═══════════════════════════════════════════════════════════════════════════
# LOGICAL CONNECTIVES
# ═══════════════════════════════════════════════════════════════════════════

def and_expr(*exprs: Expr) -> Expr:
    return Expr(type=ExprType.AND, exprs=list(exprs))


def or_expr(*exprs: Expr) -> Expr:
    return Expr(type=ExprType.OR, exprs=list(exprs))


def implies(antecedent: Expr, consequent: Expr) -> Expr:
    return Expr(type=ExprType.IMPLIES, antecedent=antecedent, consequent=consequent)


def not_expr(operand: Expr) -> Expr:
    return Expr(type=ExprType.NOT, operand=operand)


# ═══════════════════════════════════════════════════════════════════════════
# SPECIAL EXPRESSIONS
# ═══════════════════════════════════════════════════════════════════════════

def assertion(text: str) -> Expr:
    return Expr(type=ExprType.ASSERTION, text=text)


def construction(description: str, result: Optional[Expr] = None) -> Expr:
    return Expr(type=ExprType.CONSTRUCTION, description=description, result=result)


def contradiction() -> Expr:
    return Expr(type=ExprType.CONTRADICTION, symbol="⊥")


# ═══════════════════════════════════════════════════════════════════════════
# EXPRESSION UTILITIES
# ═══════════════════════════════════════════════════════════════════════════

def get_referenced_points(expr: Optional[Expr]) -> List[str]:
    """Return all point labels referenced in an expression."""
    if not expr:
        return []

    points: Set[str] = set()

    def traverse(e: Any) -> None:
        if not e or not isinstance(e, dict):
            return
        t = e.get("type")
        if t == ExprType.POINT:
            if e.get("label"):
                points.add(e["label"])
        elif t == ExprType.SEGMENT:
            if e.get("from"):
                points.add(e["from"])
            if e.get("to"):
                points.add(e["to"])
        elif t == ExprType.RAY:
            if e.get("origin"):
                points.add(e["origin"])
            if e.get("through"):
                points.add(e["through"])
        elif t == ExprType.LINE:
            for p in e.get("points", []):
                points.add(p)
        elif t == ExprType.CIRCLE:
            if e.get("center"):
                points.add(e["center"])
            if e.get("radiusLabel"):
                points.add(e["radiusLabel"])
        elif t == ExprType.ANGLE:
            for k in ("from", "vertex", "to"):
                if e.get(k):
                    points.add(e[k])
        elif t in (ExprType.TRIANGLE, ExprType.QUADRILATERAL, ExprType.POLYGON):
            for v in e.get("vertices", []):
                points.add(v)
        elif t in (ExprType.EQUALS, ExprType.CONGRUENT, ExprType.SIMILAR,
                   ExprType.PARALLEL, ExprType.PERPENDICULAR):
            traverse(e.get("left"))
            traverse(e.get("right"))
        elif t in (ExprType.AND, ExprType.OR):
            for sub in e.get("exprs", []):
                traverse(sub)
        elif t == ExprType.IMPLIES:
            traverse(e.get("antecedent"))
            traverse(e.get("consequent"))
        elif t == ExprType.NOT:
            traverse(e.get("operand"))
        elif t == ExprType.LIES_ON:
            if e.get("point"):
                points.add(e["point"])
            traverse(e.get("object"))
        elif t == ExprType.BETWEEN:
            if e.get("between"):
                points.add(e["between"])
            for p in e.get("endpoints", []):
                points.add(p)
        elif t == ExprType.INTERSECTS:
            for o in e.get("objects", []):
                traverse(o)
            if e.get("result"):
                points.add(e["result"])
        elif t == ExprType.CONSTRUCTION:
            traverse(e.get("result"))

    traverse(expr)
    return list(points)


def expr_equals(a: Optional[Expr], b: Optional[Expr]) -> bool:
    """Check structural equality of two expressions."""
    if a is b:
        return True
    if not a or not b:
        return False
    if a.get("type") != b.get("type"):
        return False

    t = a["type"]
    if t == ExprType.POINT:
        return a.get("label") == b.get("label")
    if t == ExprType.SEGMENT:
        return (
            (a.get("from") == b.get("from") and a.get("to") == b.get("to"))
            or (a.get("from") == b.get("to") and a.get("to") == b.get("from"))
        )
    if t == ExprType.ANGLE:
        return a.get("vertex") == b.get("vertex") and (
            (a.get("from") == b.get("from") and a.get("to") == b.get("to"))
            or (a.get("from") == b.get("to") and a.get("to") == b.get("from"))
        )
    if t == ExprType.TRIANGLE:
        return set(a.get("vertices", [])) == set(b.get("vertices", []))
    if t == ExprType.CIRCLE:
        return a.get("center") == b.get("center")
    if t in (ExprType.EQUALS, ExprType.CONGRUENT, ExprType.PARALLEL, ExprType.PERPENDICULAR):
        return (
            (expr_equals(a.get("left"), b.get("left")) and expr_equals(a.get("right"), b.get("right")))
            or (expr_equals(a.get("left"), b.get("right")) and expr_equals(a.get("right"), b.get("left")))
        )
    # fallback: JSON comparison
    return json.dumps(a, sort_keys=True, default=str) == json.dumps(b, sort_keys=True, default=str)


def format_expr(expr: Any) -> str:
    """Format an expression to a human-readable string."""
    if not expr:
        return "?"
    if isinstance(expr, str):
        return expr
    if not isinstance(expr, dict):
        return str(expr)

    t = expr.get("type")
    if t == ExprType.POINT:
        return expr.get("label", "?")
    if t == ExprType.SEGMENT:
        return f"{expr.get('from', '?')}{expr.get('to', '?')}"
    if t == ExprType.RAY:
        return f"{expr.get('origin', '?')}{expr.get('through', '?')}→"
    if t == ExprType.LINE:
        return "↔" + "".join(expr.get("points", []))
    if t == ExprType.CIRCLE:
        return f"⊙{expr.get('center', '?')}"
    if t == ExprType.ANGLE:
        return f"∠{expr.get('from', '?')}{expr.get('vertex', '?')}{expr.get('to', '?')}"
    if t == ExprType.TRIANGLE:
        return "△" + "".join(expr.get("vertices", []))
    if t == ExprType.QUADRILATERAL:
        return "▢" + "".join(expr.get("vertices", []))
    if t == ExprType.EQUALS:
        return f"{format_expr(expr.get('left'))} = {format_expr(expr.get('right'))}"
    if t == ExprType.CONGRUENT:
        return f"{format_expr(expr.get('left'))} ≅ {format_expr(expr.get('right'))}"
    if t == ExprType.PARALLEL:
        return f"{format_expr(expr.get('left'))} ∥ {format_expr(expr.get('right'))}"
    if t == ExprType.PERPENDICULAR:
        return f"{format_expr(expr.get('left'))} ⊥ {format_expr(expr.get('right'))}"
    if t == ExprType.LIES_ON:
        return f"{expr.get('point', '?')} on {format_expr(expr.get('object'))}"
    if t == ExprType.BETWEEN:
        eps = expr.get("endpoints", ["?", "?"])
        return f"{eps[0]}-{expr.get('between', '?')}-{eps[1]}"
    if t == ExprType.AND:
        return " ∧ ".join(format_expr(e) for e in expr.get("exprs", []))
    if t == ExprType.OR:
        return " ∨ ".join(format_expr(e) for e in expr.get("exprs", []))
    if t == ExprType.IMPLIES:
        return f"{format_expr(expr.get('antecedent'))} → {format_expr(expr.get('consequent'))}"
    if t == ExprType.NOT:
        return f"¬{format_expr(expr.get('operand'))}"
    if t == ExprType.ASSERTION:
        return expr.get("text", "?")
    if t == ExprType.CONSTRUCTION:
        return expr.get("description", "?")
    if t == ExprType.CONTRADICTION:
        return "⊥"
    return json.dumps(expr, default=str)


def parse_simple_expr(text: str) -> Expr:
    """Parse a simple expression from text (limited parser)."""
    import re
    trimmed = text.strip()

    # Point: single letter
    if re.match(r"^[A-Z]'?$", trimmed):
        return point(trimmed)

    # Segment: two letters
    if re.match(r"^[A-Z]'?[A-Z]'?$", trimmed):
        return segment(trimmed[0], trimmed[-1])

    # Triangle: △ABC or ABC (3 letters)
    if re.match(r"^△?[A-Z]'?[A-Z]'?[A-Z]'?$", trimmed):
        letters = trimmed.replace("△", "")
        return triangle(letters[0], letters[1], letters[2])

    # Angle: ∠ABC
    if re.match(r"^∠?[A-Z]'?[A-Z]'?[A-Z]'?$", trimmed) and len(trimmed) >= 3:
        letters = trimmed.replace("∠", "")
        return angle(letters[0], letters[1], letters[2])

    # Circle: ⊙A
    if re.match(r"^⊙[A-Z]'?$", trimmed):
        return circle(trimmed[1], None)

    # Default to assertion
    return assertion(trimmed)
