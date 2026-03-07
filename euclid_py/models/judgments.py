"""
Formal Judgment System — ported from judgments.js

Implements a type-theoretic foundation for geometric proof verification.
Based on judgments of the form: Γ ⊢ φ (context Γ entails proposition φ)
"""
from __future__ import annotations

from copy import deepcopy
from dataclasses import dataclass, field
from enum import Enum
from typing import Any, Dict, List, Optional, Set, Tuple


# ═══════════════════════════════════════════════════════════════════════════
# GEOMETRIC SORTS — The types of geometric objects
# ═══════════════════════════════════════════════════════════════════════════

class Sort(str, Enum):
    POINT = "Point"
    LINE = "Line"
    SEGMENT = "Segment"
    RAY = "Ray"
    CIRCLE = "Circle"
    ANGLE = "Angle"
    MAGNITUDE = "Magnitude"
    PROPOSITION = "Prop"


# ═══════════════════════════════════════════════════════════════════════════
# TERMS — Geometric objects and their constructors
# ═══════════════════════════════════════════════════════════════════════════

class _Term:
    """A geometric term (point, segment, line, circle, etc.)."""

    def __init__(self, data: dict):
        self._data = data

    def __getattr__(self, key: str) -> Any:
        if key.startswith("_"):
            return object.__getattribute__(self, key)
        return self._data.get(key)

    def __repr__(self) -> str:
        return self._data.get("_repr", str(self._data))

    def __str__(self) -> str:
        return self.__repr__()

    def __eq__(self, other: object) -> bool:
        if isinstance(other, _Term):
            return self._data == other._data
        return NotImplemented

    def __hash__(self) -> int:
        return hash(str(self))


class _TermFactory:
    """Factory for creating term objects (mirrors JS Term namespace)."""

    @staticmethod
    def point(name: str) -> _Term:
        return _Term(dict(sort=Sort.POINT, kind="point", name=name, _repr=name))

    @staticmethod
    def segment(p1: str, p2: str) -> _Term:
        return _Term(dict(sort=Sort.SEGMENT, kind="segment", endpoints=[p1, p2],
                          _repr=f"seg({p1},{p2})"))

    @staticmethod
    def line(p1: str, p2: str) -> _Term:
        return _Term(dict(sort=Sort.LINE, kind="line", points=[p1, p2],
                          _repr=f"line({p1},{p2})"))

    @staticmethod
    def ray(origin: str, through: str) -> _Term:
        return _Term(dict(sort=Sort.RAY, kind="ray", origin=origin, through=through,
                          _repr=f"ray({origin},{through})"))

    @staticmethod
    def circle(center: str, radius_point: str) -> _Term:
        return _Term(dict(sort=Sort.CIRCLE, kind="circle", center=center,
                          radiusPoint=radius_point,
                          _repr=f"circle({center},{radius_point})"))

    @staticmethod
    def angle(p1: str, vertex: str, p2: str) -> _Term:
        return _Term(dict(sort=Sort.ANGLE, kind="angle", vertex=vertex, sides=[p1, p2],
                          _repr=f"∠{p1}{vertex}{p2}"))

    @staticmethod
    def length(seg: _Term) -> _Term:
        return _Term(dict(sort=Sort.MAGNITUDE, kind="length", of=seg,
                          _repr=f"|{seg}|"))

    @staticmethod
    def intersection(obj1: _Term, obj2: _Term) -> _Term:
        return _Term(dict(sort=Sort.POINT, kind="intersection", objects=[obj1, obj2],
                          _repr=f"({obj1} ∩ {obj2})"))


Term = _TermFactory()


# ═══════════════════════════════════════════════════════════════════════════
# PROPOSITIONS — Logical assertions about geometric objects
# ═══════════════════════════════════════════════════════════════════════════

class _Prop:
    """A logical proposition about geometric objects."""

    def __init__(self, data: dict):
        self._data = data

    def __getattr__(self, key: str) -> Any:
        if key.startswith("_"):
            return object.__getattribute__(self, key)
        return self._data.get(key)

    def __repr__(self) -> str:
        return self._data.get("_repr", str(self._data))

    def __str__(self) -> str:
        return self.__repr__()

    def __eq__(self, other: object) -> bool:
        if isinstance(other, _Prop):
            return str(self) == str(other)
        return NotImplemented

    def __hash__(self) -> int:
        return hash(str(self))


class _PropFactory:
    """Factory for creating proposition objects (mirrors JS Prop namespace)."""

    @staticmethod
    def eq(t1: _Term, t2: _Term) -> _Prop:
        return _Prop(dict(sort=Sort.PROPOSITION, kind="eq", left=t1, right=t2,
                          _repr=f"{t1} = {t2}"))

    @staticmethod
    def cong(t1: _Term, t2: _Term) -> _Prop:
        return _Prop(dict(sort=Sort.PROPOSITION, kind="cong", left=t1, right=t2,
                          _repr=f"{t1} ≅ {t2}"))

    @staticmethod
    def on(point: str, obj: _Term) -> _Prop:
        return _Prop(dict(sort=Sort.PROPOSITION, kind="on", point=point, object=obj,
                          _repr=f"{point} on {obj}"))

    @staticmethod
    def between(a: str, b: str, c: str) -> _Prop:
        return _Prop(dict(sort=Sort.PROPOSITION, kind="between", points=[a, b, c],
                          _repr=f"{a}-{b}-{c}"))

    @staticmethod
    def parallel(l1: _Term, l2: _Term) -> _Prop:
        return _Prop(dict(sort=Sort.PROPOSITION, kind="parallel", lines=[l1, l2],
                          _repr=f"{l1} ∥ {l2}"))

    @staticmethod
    def perp(l1: _Term, l2: _Term) -> _Prop:
        return _Prop(dict(sort=Sort.PROPOSITION, kind="perp", lines=[l1, l2],
                          _repr=f"{l1} ⊥ {l2}"))

    @staticmethod
    def distinct(p1: str, p2: str) -> _Prop:
        return _Prop(dict(sort=Sort.PROPOSITION, kind="distinct", points=[p1, p2],
                          _repr=f"{p1} ≠ {p2}"))

    @staticmethod
    def collinear(*points: str) -> _Prop:
        return _Prop(dict(sort=Sort.PROPOSITION, kind="collinear", points=list(points),
                          _repr=f"collinear({','.join(points)})"))

    @staticmethod
    def right_angle(angle_term: _Term) -> _Prop:
        return _Prop(dict(sort=Sort.PROPOSITION, kind="rightAngle", angle=angle_term,
                          _repr=f"right({angle_term})"))

    @staticmethod
    def and_(p1: _Prop, p2: _Prop) -> _Prop:
        return _Prop(dict(sort=Sort.PROPOSITION, kind="and", left=p1, right=p2,
                          _repr=f"({p1} ∧ {p2})"))

    @staticmethod
    def or_(p1: _Prop, p2: _Prop) -> _Prop:
        return _Prop(dict(sort=Sort.PROPOSITION, kind="or", left=p1, right=p2,
                          _repr=f"({p1} ∨ {p2})"))

    @staticmethod
    def implies(p1: _Prop, p2: _Prop) -> _Prop:
        return _Prop(dict(sort=Sort.PROPOSITION, kind="implies", antecedent=p1,
                          consequent=p2, _repr=f"({p1} → {p2})"))

    @staticmethod
    def not_(p: _Prop) -> _Prop:
        return _Prop(dict(sort=Sort.PROPOSITION, kind="not", prop=p,
                          _repr=f"¬{p}"))

    @staticmethod
    def exists(var_name: str, sort: Sort, predicate: _Prop) -> _Prop:
        return _Prop(dict(sort=Sort.PROPOSITION, kind="exists", variable=var_name,
                          varSort=sort, predicate=predicate,
                          _repr=f"∃{var_name}:{sort.value}. {predicate}"))

    @staticmethod
    def forall(var_name: str, sort: Sort, predicate: _Prop) -> _Prop:
        return _Prop(dict(sort=Sort.PROPOSITION, kind="forall", variable=var_name,
                          varSort=sort, predicate=predicate,
                          _repr=f"∀{var_name}:{sort.value}. {predicate}"))


Prop = _PropFactory()


# ═══════════════════════════════════════════════════════════════════════════
# UNION-FIND — For maintaining equality classes (congruence closure)
# ═══════════════════════════════════════════════════════════════════════════

class UnionFind:
    def __init__(self) -> None:
        self.parent: Dict[str, str] = {}
        self.rank: Dict[str, int] = {}

    def clone(self) -> UnionFind:
        uf = UnionFind()
        uf.parent = dict(self.parent)
        uf.rank = dict(self.rank)
        return uf

    def make_set(self, x: str) -> None:
        if x not in self.parent:
            self.parent[x] = x
            self.rank[x] = 0

    def find(self, x: str) -> str:
        if x not in self.parent:
            self.make_set(x)
        if self.parent[x] != x:
            self.parent[x] = self.find(self.parent[x])  # path compression
        return self.parent[x]

    def union(self, x: str, y: str) -> None:
        root_x = self.find(x)
        root_y = self.find(y)
        if root_x == root_y:
            return
        rx, ry = self.rank[root_x], self.rank[root_y]
        if rx < ry:
            self.parent[root_x] = root_y
        elif rx > ry:
            self.parent[root_y] = root_x
        else:
            self.parent[root_y] = root_x
            self.rank[root_x] = rx + 1

    def connected(self, x: str, y: str) -> bool:
        return self.find(x) == self.find(y)


# ═══════════════════════════════════════════════════════════════════════════
# CONTEXT — The collection of established facts and objects
# ═══════════════════════════════════════════════════════════════════════════

@dataclass
class _DeclInfo:
    sort: Sort
    term: _Term


@dataclass
class _DerivInfo:
    rule: str
    premises: List[str]
    prop: _Prop


class Context:
    """
    A proof context Γ containing:
    - Declared objects with their sorts
    - Established propositions (facts)
    - Equality relations (for congruence closure)
    """

    def __init__(self) -> None:
        self.declarations: Dict[str, _DeclInfo] = {}
        self.facts: Set[str] = set()
        self.equality_classes = UnionFind()
        self.derivations: Dict[str, _DerivInfo] = {}

    def clone(self) -> Context:
        ctx = Context()
        ctx.declarations = dict(self.declarations)
        ctx.facts = set(self.facts)
        ctx.equality_classes = self.equality_classes.clone()
        ctx.derivations = dict(self.derivations)
        return ctx

    def declare(self, name: str, sort: Sort, term: Optional[_Term] = None) -> Context:
        if name in self.declarations:
            raise JudgmentError(f"Object '{name}' already declared")
        self.declarations[name] = _DeclInfo(sort=sort, term=term or Term.point(name))
        self.equality_classes.make_set(name)
        return self

    def is_declared(self, name: str) -> bool:
        return name in self.declarations

    def get_sort(self, name: str) -> Optional[Sort]:
        decl = self.declarations.get(name)
        return decl.sort if decl else None

    def add_fact(self, prop: _Prop, rule: str, premises: Optional[List[str]] = None) -> Context:
        key = str(prop)
        self.facts.add(key)
        self.derivations[key] = _DerivInfo(rule=rule, premises=premises or [], prop=prop)
        if prop.kind == "eq":
            self.equality_classes.union(str(prop.left), str(prop.right))
        return self

    def has_fact(self, prop: _Prop) -> bool:
        return str(prop) in self.facts

    def are_equal(self, t1: Any, t2: Any) -> bool:
        k1 = t1 if isinstance(t1, str) else str(t1)
        k2 = t2 if isinstance(t2, str) else str(t2)
        return self.equality_classes.find(k1) == self.equality_classes.find(k2)

    def get_facts_of_kind(self, kind: str) -> List[_Prop]:
        result = []
        for key in self.facts:
            deriv = self.derivations.get(key)
            if deriv and deriv.prop.kind == kind:
                result.append(deriv.prop)
        return result

    def get_derivation(self, prop: _Prop) -> Optional[_DerivInfo]:
        return self.derivations.get(str(prop))

    def __repr__(self) -> str:
        decls = ", ".join(f"{n}:{d.sort.value}" for n, d in self.declarations.items())
        facts_list = list(self.facts)[:5]
        facts_str = "; ".join(facts_list)
        if len(self.facts) > 5:
            facts_str += "..."
        return f"Γ = {{{decls}}} ⊢ {{{facts_str}}}"


# ═══════════════════════════════════════════════════════════════════════════
# JUDGMENTS — The formal statements we can derive
# ═══════════════════════════════════════════════════════════════════════════

class JudgmentKind(str, Enum):
    WELL_FORMED = "wf"
    HAS_SORT = "hasSort"
    ENTAILS = "entails"


@dataclass
class Judgment:
    kind: JudgmentKind
    context: Context
    term: Optional[_Term] = None
    sort: Optional[Sort] = None
    proposition: Optional[_Prop] = None

    def __repr__(self) -> str:
        if self.kind == JudgmentKind.WELL_FORMED:
            return f"⊢ {self.context} wf"
        if self.kind == JudgmentKind.HAS_SORT:
            return f"{self.context} ⊢ {self.term} : {self.sort}"
        if self.kind == JudgmentKind.ENTAILS:
            return f"{self.context} ⊢ {self.proposition}"
        return f"Judgment({self.kind})"


def well_formed(ctx: Context) -> Judgment:
    return Judgment(kind=JudgmentKind.WELL_FORMED, context=ctx)


def has_sort(ctx: Context, term: _Term, sort: Sort) -> Judgment:
    return Judgment(kind=JudgmentKind.HAS_SORT, context=ctx, term=term, sort=sort)


def entails(ctx: Context, prop: _Prop) -> Judgment:
    return Judgment(kind=JudgmentKind.ENTAILS, context=ctx, proposition=prop)


# ═══════════════════════════════════════════════════════════════════════════
# JUDGMENT ERRORS
# ═══════════════════════════════════════════════════════════════════════════

class JudgmentError(Exception):
    def __init__(self, message: str, details: Optional[dict] = None):
        super().__init__(message)
        self.details = details or {}


# ═══════════════════════════════════════════════════════════════════════════
# JUDGMENT CHECKER — Verify that judgments are valid
# ═══════════════════════════════════════════════════════════════════════════

@dataclass
class SortCheckResult:
    valid: bool
    sort: Optional[Sort] = None
    error: Optional[str] = None


def check_sort(ctx: Context, term: _Term) -> SortCheckResult:
    """Check if a term is well-sorted in a context."""
    if not term:
        return SortCheckResult(valid=False, error="Term is null")

    kind = term.kind
    if kind == "point":
        if not ctx.is_declared(term.name):
            return SortCheckResult(valid=False, error=f"Point {term.name} not declared")
        return SortCheckResult(valid=True, sort=Sort.POINT)

    if kind == "segment":
        p1, p2 = term.endpoints
        c1 = check_sort(ctx, Term.point(p1))
        c2 = check_sort(ctx, Term.point(p2))
        if not c1.valid:
            return c1
        if not c2.valid:
            return c2
        return SortCheckResult(valid=True, sort=Sort.SEGMENT)

    if kind == "line":
        p1, p2 = term.points
        c1 = check_sort(ctx, Term.point(p1))
        c2 = check_sort(ctx, Term.point(p2))
        if not c1.valid:
            return c1
        if not c2.valid:
            return c2
        if p1 == p2:
            return SortCheckResult(valid=False, error="Line requires two distinct points")
        return SortCheckResult(valid=True, sort=Sort.LINE)

    if kind == "circle":
        c1 = check_sort(ctx, Term.point(term.center))
        c2 = check_sort(ctx, Term.point(term.radiusPoint))
        if not c1.valid:
            return c1
        if not c2.valid:
            return c2
        if term.center == term.radiusPoint:
            return SortCheckResult(valid=False, error="Circle radius must be non-zero")
        return SortCheckResult(valid=True, sort=Sort.CIRCLE)

    if kind == "angle":
        for p in [term.sides[0], term.vertex, term.sides[1]]:
            c = check_sort(ctx, Term.point(p))
            if not c.valid:
                return c
        return SortCheckResult(valid=True, sort=Sort.ANGLE)

    if kind == "length":
        seg_check = check_sort(ctx, term.of)
        if not seg_check.valid:
            return seg_check
        if seg_check.sort != Sort.SEGMENT:
            return SortCheckResult(valid=False, error="Length requires a segment")
        return SortCheckResult(valid=True, sort=Sort.MAGNITUDE)

    return SortCheckResult(valid=False, error=f"Unknown term kind: {kind}")


@dataclass
class PropCheckResult:
    valid: bool
    error: Optional[str] = None


def check_prop(ctx: Context, prop: _Prop) -> PropCheckResult:
    """Check if a proposition is well-formed in a context."""
    if not prop or prop.sort != Sort.PROPOSITION:
        return PropCheckResult(valid=False, error="Not a proposition")

    kind = prop.kind

    if kind in ("eq", "cong"):
        c1 = check_sort(ctx, prop.left)
        c2 = check_sort(ctx, prop.right)
        if not c1.valid:
            return PropCheckResult(valid=False, error=c1.error)
        if not c2.valid:
            return PropCheckResult(valid=False, error=c2.error)
        if c1.sort != c2.sort:
            return PropCheckResult(valid=False, error=f"Sort mismatch: {c1.sort} vs {c2.sort}")
        return PropCheckResult(valid=True)

    if kind == "on":
        pt_check = check_sort(ctx, Term.point(prop.point))
        obj_check = check_sort(ctx, prop.object)
        if not pt_check.valid:
            return PropCheckResult(valid=False, error=pt_check.error)
        if not obj_check.valid:
            return PropCheckResult(valid=False, error=obj_check.error)
        valid_sorts = {Sort.LINE, Sort.SEGMENT, Sort.RAY, Sort.CIRCLE}
        if obj_check.sort not in valid_sorts:
            return PropCheckResult(valid=False, error=f"Cannot be 'on' a {obj_check.sort}")
        return PropCheckResult(valid=True)

    if kind == "between":
        for p in prop.points:
            c = check_sort(ctx, Term.point(p))
            if not c.valid:
                return PropCheckResult(valid=False, error=c.error)
        return PropCheckResult(valid=True)

    if kind == "distinct":
        for p in prop.points:
            c = check_sort(ctx, Term.point(p))
            if not c.valid:
                return PropCheckResult(valid=False, error=c.error)
        return PropCheckResult(valid=True)

    if kind == "collinear":
        for p in prop.points:
            c = check_sort(ctx, Term.point(p))
            if not c.valid:
                return PropCheckResult(valid=False, error=c.error)
        return PropCheckResult(valid=True)

    if kind in ("parallel", "perp"):
        for l in prop.lines:
            c = check_sort(ctx, l)
            if not c.valid:
                return PropCheckResult(valid=False, error=c.error)
            if c.sort not in (Sort.LINE, Sort.SEGMENT):
                return PropCheckResult(valid=False, error=f"Expected line/segment, got {c.sort}")
        return PropCheckResult(valid=True)

    if kind == "rightAngle":
        c = check_sort(ctx, prop.angle)
        if not c.valid:
            return PropCheckResult(valid=False, error=c.error)
        if c.sort != Sort.ANGLE:
            return PropCheckResult(valid=False, error=f"Expected angle, got {c.sort}")
        return PropCheckResult(valid=True)

    if kind in ("and", "or", "implies"):
        left = prop.left if kind != "implies" else prop.antecedent
        right = prop.right if kind != "implies" else prop.consequent
        c1 = check_prop(ctx, left)
        c2 = check_prop(ctx, right)
        if not c1.valid:
            return c1
        if not c2.valid:
            return c2
        return PropCheckResult(valid=True)

    if kind == "not":
        return check_prop(ctx, prop.prop)

    if kind in ("exists", "forall"):
        ext_ctx = ctx.clone()
        ext_ctx.declare(prop.variable, prop.varSort)
        return check_prop(ext_ctx, prop.predicate)

    return PropCheckResult(valid=False, error=f"Unknown proposition kind: {kind}")


# ═══════════════════════════════════════════════════════════════════════════
# SUBSTITUTION — For instantiating universal statements
# ═══════════════════════════════════════════════════════════════════════════

def _subst_term(t: Any, var_name: str, term: _Term) -> Any:
    """Substitute a term for a variable inside a term."""
    if t is None:
        return t
    if hasattr(t, "kind") and t.kind == "point" and t.name == var_name:
        return term
    # For complex terms stored as _Term, we work with their internal dict
    data = t._data if isinstance(t, _Term) else (t if isinstance(t, dict) else None)
    if data is None:
        return t

    new_data = dict(data)
    if "endpoints" in new_data:
        new_data["endpoints"] = [term.name if e == var_name else e for e in new_data["endpoints"]]
    if "points" in new_data:
        new_data["points"] = [term.name if p == var_name else p for p in new_data["points"]]
    if new_data.get("center") == var_name:
        new_data["center"] = term.name
    if new_data.get("radiusPoint") == var_name:
        new_data["radiusPoint"] = term.name
    if isinstance(t, _Term):
        return _Term(new_data)
    return new_data


def substitute(prop: _Prop, var_name: str, term: _Term) -> _Prop:
    """Substitute a term for a variable in a proposition."""
    if prop is None:
        return prop

    kind = prop.kind
    data = prop._data
    new_data = dict(data)

    if kind in ("eq", "cong"):
        new_data["left"] = _subst_term(data["left"], var_name, term)
        new_data["right"] = _subst_term(data["right"], var_name, term)
    elif kind == "on":
        new_data["point"] = term.name if data["point"] == var_name else data["point"]
        new_data["object"] = _subst_term(data["object"], var_name, term)
    elif kind in ("between", "collinear", "distinct"):
        new_data["points"] = [term.name if p == var_name else p for p in data["points"]]
    elif kind in ("parallel", "perp"):
        new_data["lines"] = [_subst_term(l, var_name, term) for l in data["lines"]]
    elif kind == "rightAngle":
        new_data["angle"] = _subst_term(data["angle"], var_name, term)
    elif kind in ("and", "or"):
        new_data["left"] = substitute(data["left"], var_name, term)
        new_data["right"] = substitute(data["right"], var_name, term)
    elif kind == "implies":
        new_data["antecedent"] = substitute(data["antecedent"], var_name, term)
        new_data["consequent"] = substitute(data["consequent"], var_name, term)
    elif kind == "not":
        new_data["prop"] = substitute(data["prop"], var_name, term)
    elif kind in ("exists", "forall"):
        if data["variable"] == var_name:
            return prop  # don't substitute bound variable
        new_data["predicate"] = substitute(data["predicate"], var_name, term)

    # Rebuild repr
    return _rebuild_prop(new_data)


def _rebuild_prop(data: dict) -> _Prop:
    """Rebuild a _Prop with updated repr."""
    kind = data.get("kind")
    if kind == "eq":
        data["_repr"] = f"{data['left']} = {data['right']}"
    elif kind == "cong":
        data["_repr"] = f"{data['left']} ≅ {data['right']}"
    elif kind == "on":
        data["_repr"] = f"{data['point']} on {data['object']}"
    elif kind == "between":
        pts = data["points"]
        data["_repr"] = f"{pts[0]}-{pts[1]}-{pts[2]}"
    elif kind == "collinear":
        data["_repr"] = f"collinear({','.join(data['points'])})"
    elif kind == "distinct":
        pts = data["points"]
        data["_repr"] = f"{pts[0]} ≠ {pts[1]}"
    elif kind == "parallel":
        data["_repr"] = f"{data['lines'][0]} ∥ {data['lines'][1]}"
    elif kind == "perp":
        data["_repr"] = f"{data['lines'][0]} ⊥ {data['lines'][1]}"
    elif kind == "rightAngle":
        data["_repr"] = f"right({data['angle']})"
    elif kind == "and":
        data["_repr"] = f"({data['left']} ∧ {data['right']})"
    elif kind == "or":
        data["_repr"] = f"({data['left']} ∨ {data['right']})"
    elif kind == "implies":
        data["_repr"] = f"({data['antecedent']} → {data['consequent']})"
    elif kind == "not":
        data["_repr"] = f"¬{data['prop']}"
    elif kind == "exists":
        data["_repr"] = f"∃{data['variable']}:{data['varSort'].value}. {data['predicate']}"
    elif kind == "forall":
        data["_repr"] = f"∀{data['variable']}:{data['varSort'].value}. {data['predicate']}"
    return _Prop(data)
