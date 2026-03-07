"""
ast.py — Formula AST, proof structures, and formula utilities.
"""
from __future__ import annotations
from dataclasses import dataclass, field
from typing import List, Optional, Dict, Any, FrozenSet
from enum import Enum, auto


class Sort(Enum):
    POINT = auto()
    LINE = auto()


@dataclass
class SymbolInfo:
    name: str
    sort: Sort
    origin: str
    introduced_at: int = 0


@dataclass(frozen=True)
class Seg:
    p1: str
    p2: str
    def __repr__(self):
        return f"{self.p1}{self.p2}"


class Formula:
    pass


@dataclass(frozen=True)
class Pred(Formula):
    name: str
    args: tuple
    def __repr__(self):
        if not self.args:
            return self.name
        return self.name + "(" + ", ".join(str(a) for a in self.args) + ")"


@dataclass(frozen=True)
class Eq(Formula):
    left: str
    right: str
    def __repr__(self):
        return self.left + " = " + self.right


@dataclass(frozen=True)
class Neq(Formula):
    left: str
    right: str
    def __repr__(self):
        return self.left + " \u2260 " + self.right


@dataclass(frozen=True)
class Not(Formula):
    inner: Formula
    def __repr__(self):
        return "\u00ac(" + repr(self.inner) + ")"


@dataclass(frozen=True)
class And(Formula):
    left: Formula
    right: Formula
    def __repr__(self):
        return "(" + repr(self.left) + " \u2227 " + repr(self.right) + ")"


@dataclass(frozen=True)
class Or(Formula):
    left: Formula
    right: Formula
    def __repr__(self):
        return "(" + repr(self.left) + " \u2228 " + repr(self.right) + ")"


@dataclass(frozen=True)
class Iff(Formula):
    left: Formula
    right: Formula
    def __repr__(self):
        return "(" + repr(self.left) + " \u2194 " + repr(self.right) + ")"


@dataclass(frozen=True)
class Exists(Formula):
    var: str
    body: Formula
    def __repr__(self):
        return "\u2203" + self.var + "(" + repr(self.body) + ")"


@dataclass(frozen=True)
class ExistsUnique(Formula):
    var: str
    body: Formula
    def __repr__(self):
        return "\u2203!" + self.var + "(" + repr(self.body) + ")"


@dataclass(frozen=True)
class ExactlyOne(Formula):
    formulas: tuple
    def __repr__(self):
        return "ExactlyOne(" + ", ".join(repr(f) for f in self.formulas) + ")"


@dataclass(frozen=True)
class ForAll(Formula):
    var: str
    body: Formula
    def __repr__(self):
        return "\u2200" + self.var + "(" + repr(self.body) + ")"


@dataclass(frozen=True)
class Bottom(Formula):
    def __repr__(self):
        return "\u22a5"


@dataclass
class ProofLine:
    id: int
    depth: int
    statement: Optional[Formula]
    justification: str
    refs: List[int] = field(default_factory=list)
    meta: Dict[str, Any] = field(default_factory=dict)
    raw: str = ""


@dataclass
class Declarations:
    points: List[str] = field(default_factory=list)
    lines: List[str] = field(default_factory=list)


@dataclass
class Proof:
    name: str
    declarations: Declarations
    premises: List[str]
    goal: str
    lines: List[ProofLine] = field(default_factory=list)
    goal_formula: Optional[Formula] = None
    premise_formulas: List[Formula] = field(default_factory=list)


def formula_eq(a: Formula, b: Formula) -> bool:
    return a == b


def free_symbols(f: Formula, bound: FrozenSet[str] = frozenset()) -> set:
    if isinstance(f, Pred):
        out = set()
        for a in f.args:
            if isinstance(a, Seg):
                if a.p1 not in bound: out.add(a.p1)
                if a.p2 not in bound: out.add(a.p2)
            elif isinstance(a, Pred):
                out |= free_symbols(a, bound)
            elif isinstance(a, str) and a not in bound:
                out.add(a)
        return out
    if isinstance(f, (Eq, Neq)):
        out = set()
        if f.left not in bound: out.add(f.left)
        if f.right not in bound: out.add(f.right)
        return out
    if isinstance(f, Not):
        return free_symbols(f.inner, bound)
    if isinstance(f, (And, Or, Iff)):
        return free_symbols(f.left, bound) | free_symbols(f.right, bound)
    if isinstance(f, (Exists, ExistsUnique, ForAll)):
        return free_symbols(f.body, bound | {f.var})
    if isinstance(f, ExactlyOne):
        out = set()
        for sub in f.formulas:
            out |= free_symbols(sub, bound)
        return out
    return set()


def all_symbols(f: Formula) -> set:
    if isinstance(f, Pred):
        out = set()
        for a in f.args:
            if isinstance(a, Seg):
                out.update((a.p1, a.p2))
            elif isinstance(a, Pred):
                out |= all_symbols(a)
            elif isinstance(a, str):
                out.add(a)
        return out
    if isinstance(f, (Eq, Neq)):
        return {f.left, f.right}
    if isinstance(f, Not):
        return all_symbols(f.inner)
    if isinstance(f, (And, Or, Iff)):
        return all_symbols(f.left) | all_symbols(f.right)
    if isinstance(f, (Exists, ExistsUnique, ForAll)):
        return {f.var} | all_symbols(f.body)
    if isinstance(f, ExactlyOne):
        out = set()
        for sub in f.formulas:
            out |= all_symbols(sub)
        return out
    return set()


def substitute(f: Formula, var: str, replacement: str) -> Formula:
    def _sub_arg(a):
        if isinstance(a, Seg):
            return Seg(
                replacement if a.p1 == var else a.p1,
                replacement if a.p2 == var else a.p2,
            )
        if isinstance(a, Pred):
            return substitute(a, var, replacement)
        if isinstance(a, str):
            return replacement if a == var else a
        return a
    if isinstance(f, Pred):
        return Pred(f.name, tuple(_sub_arg(a) for a in f.args))
    if isinstance(f, Eq):
        return Eq(replacement if f.left == var else f.left,
                  replacement if f.right == var else f.right)
    if isinstance(f, Neq):
        return Neq(replacement if f.left == var else f.left,
                   replacement if f.right == var else f.right)
    if isinstance(f, Not):
        return Not(substitute(f.inner, var, replacement))
    if isinstance(f, And):
        return And(substitute(f.left, var, replacement),
                   substitute(f.right, var, replacement))
    if isinstance(f, Or):
        return Or(substitute(f.left, var, replacement),
                  substitute(f.right, var, replacement))
    if isinstance(f, Iff):
        return Iff(substitute(f.left, var, replacement),
                   substitute(f.right, var, replacement))
    if isinstance(f, Exists):
        if f.var == var: return f
        return Exists(f.var, substitute(f.body, var, replacement))
    if isinstance(f, ExistsUnique):
        if f.var == var: return f
        return ExistsUnique(f.var, substitute(f.body, var, replacement))
    if isinstance(f, ForAll):
        if f.var == var: return f
        return ForAll(f.var, substitute(f.body, var, replacement))
    if isinstance(f, ExactlyOne):
        return ExactlyOne(tuple(substitute(s, var, replacement) for s in f.formulas))
    return f
