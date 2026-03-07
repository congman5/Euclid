"""
rules.py — Rule schemas and registry. Kernel vs derived explicitly separated.
"""
from __future__ import annotations
from dataclasses import dataclass, field
from typing import List, Optional, Dict
from enum import Enum, auto
from .ast import Formula
from .parser import parse_formula


class RuleKind(str, Enum):
    KERNEL = "kernel"
    DERIVED = "derived"


@dataclass
class RuleSchema:
    name: str
    kind: RuleKind
    premise_patterns: List[Formula]
    conclusion_pattern: Formula
    min_refs: Optional[int] = None
    max_refs: Optional[int] = None


def _p(text: str) -> Formula:
    return parse_formula(text)


KERNEL_RULES: Dict[str, RuleSchema] = {}
ALL_RULES: Dict[str, RuleSchema] = {}


def _reg(*rules):
    for r in rules:
        ALL_RULES[r.name] = r
        if r.kind == RuleKind.KERNEL:
            KERNEL_RULES[r.name] = r


def get_rule(name: str) -> Optional[RuleSchema]:
    if name in ALL_RULES:
        return ALL_RULES[name]
    alias = RULE_ALIASES.get(name)
    if alias:
        return ALL_RULES.get(alias)
    return None


# ── Backward-compatibility aliases (old name → new canonical name) ────

RULE_ALIASES: Dict[str, str] = {
    "AndIntro": "\u2227Intro",
    "AndElimL": "\u2227Elim",
    "AndElimR": "\u2227Elim",
    "OrIntroL": "\u2228Intro",
    "OrIntroR": "\u2228Intro",
    "IffElimLR": "\u2194Elim",
    "IffElimRL": "\u2194Elim",
    "EqSym": "=Sym",
    "EqTrans": "=Trans",
    "ContrIntro": "\u22a5Intro",
    "ContrElim": "\u22a5Elim",
    "ExistsIntro": "\u2203Intro",
    "ExactlyOneContradiction": "E!\u22a5",
}


# ── Logical rules (kernel) ────────────────────────────────────────────

_reg(
    RuleSchema("Given", RuleKind.KERNEL, [], _p("phi"), 0, 0),
    RuleSchema("Reit", RuleKind.KERNEL, [_p("phi")], _p("phi"), 1, 1),
    RuleSchema("Assume", RuleKind.KERNEL, [], _p("phi"), 0, 0),
    RuleSchema("\u2227Intro", RuleKind.KERNEL, [_p("phi"), _p("psi")], _p("phi \u2227 psi"), 2, 2),
    RuleSchema("\u2227Elim", RuleKind.KERNEL, [_p("phi \u2227 psi")], _p("phi"), 1, 1),
    RuleSchema("\u2228Intro", RuleKind.KERNEL, [_p("phi")], _p("phi \u2228 psi"), 1, 1),
    RuleSchema("\u2194Elim", RuleKind.KERNEL, [_p("phi \u2194 psi"), _p("phi")], _p("psi"), 2, 2),
    RuleSchema("=Sym", RuleKind.KERNEL, [_p("X = Y")], _p("Y = X"), 1, 1),
    RuleSchema("=Trans", RuleKind.KERNEL, [_p("X = Y"), _p("Y = Z")], _p("X = Z"), 2, 2),
    RuleSchema("\u22a5Intro", RuleKind.KERNEL, [_p("phi"), _p("\u00ac(phi)")], _p("\u22a5"), 2, 2),
    RuleSchema("\u22a5Elim", RuleKind.KERNEL, [_p("\u22a5")], _p("phi"), 1, 1),
    RuleSchema("RAA", RuleKind.KERNEL, [], _p("\u00ac(phi)"), 2, 2),
    RuleSchema("\u2203Intro", RuleKind.KERNEL, [], _p("\u2203X(phi)"), 1, 1),
    RuleSchema("E!\u22a5", RuleKind.KERNEL,
               [_p("ExactlyOne(phi, psi, chi)"), _p("phi"), _p("psi")], _p("\u22a5"), 3, 3),
)

# ── Geometric kernel rules ────────────────────────────────────────────

_reg(
    RuleSchema("Inc1", RuleKind.KERNEL, [_p("A \u2260 B")],
               _p("\u2203!l(OnLine(A, l) \u2227 OnLine(B, l))"), 1, 1),
    RuleSchema("Inc2", RuleKind.KERNEL, [_p("Line(l)")],
               _p("\u2203A(\u2203B(A \u2260 B \u2227 OnLine(A, l) \u2227 OnLine(B, l)))"), 1, 1),
    RuleSchema("Inc3", RuleKind.KERNEL, [],
               _p("\u2203A(\u2203B(\u2203C(\u00ac(Collinear(A, B, C)))))"), 0, 0),
    RuleSchema("Ord1", RuleKind.KERNEL, [_p("Between(A, B, C)")],
               _p("Collinear(A, B, C)"), 1, 1),
    RuleSchema("Ord2", RuleKind.KERNEL, [_p("Between(A, B, C)")],
               _p("Between(C, B, A)"), 1, 1),
    RuleSchema("Ord3", RuleKind.KERNEL, [_p("A \u2260 B")],
               _p("\u2203C(Between(A, B, C))"), 1, 1),
    RuleSchema("Ord4", RuleKind.KERNEL,
               [_p("Collinear(A, B, C)"), _p("A \u2260 B"), _p("B \u2260 C"), _p("A \u2260 C")],
               _p("ExactlyOne(Between(A, B, C), Between(B, C, A), Between(C, A, B))"), 4, 4),
    RuleSchema("Pasch", RuleKind.KERNEL,
               [_p("Triangle(A, B, C)"), _p("Line(l)"),
                _p("EntersThroughOneSideAvoidingVertices(l, A, B, C)")],
               _p("ExitsThroughAnotherSide(l, A, B, C)"), 3, 3),
    RuleSchema("Cong1", RuleKind.KERNEL, [_p("Equal(AB, CD)")],
               _p("(A \u2260 B) \u2194 (C \u2260 D)"), 1, 1),
    RuleSchema("Cong2", RuleKind.KERNEL, [_p("Ray(A, B)"), _p("Segment(C, D)")],
               _p("\u2203!E(OnRay(E, A, B) \u2227 Equal(AE, CD))"), 2, 2),
    RuleSchema("Cong3", RuleKind.KERNEL, [_p("Equal(AB, CD)"), _p("Equal(AB, EF)")],
               _p("Equal(CD, EF)"), 2, 2),
    RuleSchema("Cong4", RuleKind.KERNEL,
               [_p("Angle(U, V, W)"), _p("Ray(A, B)"), _p("ChosenSide(P, l)")],
               _p("\u2203!E(OnRay(E, A, B) \u2227 EqualAngle(U, V, W, B, A, E) \u2227 OnChosenSide(E, P, l))"),
               3, 3),
    RuleSchema("SAS", RuleKind.KERNEL,
               [_p("Equal(AB, DE)"), _p("Equal(AC, DF)"), _p("EqualAngle(B, A, C, E, D, F)")],
               _p("Congruent(A, B, C, D, E, F)"), 3, 3),
    RuleSchema("Parallel", RuleKind.KERNEL,
               [_p("Point(P)"), _p("Line(l)"), _p("\u00ac(OnLine(P, l))")],
               _p("\u2203!m(OnLine(P, m) \u2227 Parallel(m, l))"), 3, 3),
)

# ── Proof administration rules (kernel — special-cased in checker) ────

_reg(
    RuleSchema("Witness", RuleKind.KERNEL, [], _p("phi"), 1, 1),
    RuleSchema("WitnessUnique", RuleKind.KERNEL, [], _p("phi"), 1, 1),
    RuleSchema("UniqueElim", RuleKind.KERNEL, [], _p("X = Y"), 3, 3),
)
