"""
h_ast.py — AST for Hilbert's axiom system (System H).

System H is Hilbert's axiomatization of Euclidean geometry as formalized
in GeoCoq (https://geocoq.github.io/GeoCoq/):
  GeoCoq.Axioms.hilbert_axioms.v

System H is three-sorted (dimensionless variant focuses on Points and Lines):
  - Points (A, B, C, ...): geometric points
  - Lines  (l, m, n, ...): straight lines
  - Planes (p, q, ...):    planes (used in 3D; optional for 2D)

Primitive relations:
  - IncidL(A, l):       point A lies on line l
  - IncidP(A, p):       point A lies on plane p
  - BetH(A, B, C):      B is strictly between A and C
  - CongH(A, B, C, D):  segment AB is congruent to segment CD
  - CongaH(A,B,C,D,E,F): angle ABC is congruent to angle DEF
  - EqL(l, m):          lines l and m are equal
  - EqP(p, q):          planes p and q are equal

Defined predicates (from GeoCoq):
  - ColH(A, B, C):      A, B, C are collinear
  - cut(l, A, B):       line l separates A from B
  - outH(P, A, B):      A is on ray PB
  - disjoint(A,B,C,D):  segments AB and CD share no interior point
  - same_side(A, B, l): A and B are on the same side of l
  - same_side'(A,B,X,Y):A and B on same side of every line through X,Y
  - Para(l, m):         l and m are parallel (coplanar, non-intersecting)

Reference:
  - GeoCoq hilbert_axioms.v (Hilbert_neutral_dimensionless class)
  - Hilbert, "Grundlagen der Geometrie" (1899)
  - GeoCoq tarski_to_hilbert.v / hilbert_to_tarski.v for equivalence
    with Tarski's axiom system
  - Avigad, Dean, Mumma (2009), Section 5.2 for Tarski's system T
"""
from __future__ import annotations

from dataclasses import dataclass, field
from enum import Enum, auto
from typing import Any, Dict, FrozenSet, List, Optional, Set, Tuple, Union


# ═══════════════════════════════════════════════════════════════════════
# Sorts
# ═══════════════════════════════════════════════════════════════════════

class HSort(Enum):
    """The sorts of System H."""
    POINT = auto()
    LINE = auto()
    PLANE = auto()


# ═══════════════════════════════════════════════════════════════════════
# Atomic formulas — primitive relations of System H
# ═══════════════════════════════════════════════════════════════════════

class HAtom:
    """Base class for atomic formulas in System H."""
    pass


@dataclass(frozen=True)
class IncidL(HAtom):
    """IncidL(A, l) — point A lies on line l.

    GeoCoq: IncidL : Point -> Line -> Prop
    """
    point: str
    line: str

    def __repr__(self) -> str:
        return f"IncidL({self.point}, {self.line})"


@dataclass(frozen=True)
class IncidP(HAtom):
    """IncidP(A, p) — point A lies on plane p.

    GeoCoq: IncidP : Point -> Plane -> Prop
    """
    point: str
    plane: str

    def __repr__(self) -> str:
        return f"IncidP({self.point}, {self.plane})"


@dataclass(frozen=True)
class BetH(HAtom):
    """BetH(A, B, C) — B is strictly between A and C.

    GeoCoq: BetH : Point -> Point -> Point -> Prop
    Implies A, B, C are collinear, A ≠ C (between_diff), and
    BetH(C, B, A) (between_comm).
    """
    a: str
    b: str
    c: str

    def __repr__(self) -> str:
        return f"BetH({self.a}, {self.b}, {self.c})"


@dataclass(frozen=True)
class CongH(HAtom):
    """CongH(A, B, C, D) — segment AB is congruent to segment CD.

    GeoCoq: CongH : Point -> Point -> Point -> Point -> Prop
    """
    a: str
    b: str
    c: str
    d: str

    def __repr__(self) -> str:
        return f"CongH({self.a}, {self.b}, {self.c}, {self.d})"


@dataclass(frozen=True)
class CongaH(HAtom):
    """CongaH(A, B, C, D, E, F) — angle ABC is congruent to angle DEF.

    GeoCoq: CongaH : Point -> Point -> Point -> Point -> Point -> Point -> Prop
    Vertex of first angle is B, vertex of second is E.
    """
    a: str
    b: str
    c: str
    d: str
    e: str
    f: str

    def __repr__(self) -> str:
        return f"CongaH({self.a}, {self.b}, {self.c}, {self.d}, {self.e}, {self.f})"


@dataclass(frozen=True)
class EqL(HAtom):
    """EqL(l, m) — lines l and m are equal.

    GeoCoq: EqL : Line -> Line -> Prop (equivalence relation)
    """
    left: str
    right: str

    def __repr__(self) -> str:
        return f"EqL({self.left}, {self.right})"


@dataclass(frozen=True)
class EqP(HAtom):
    """EqP(p, q) — planes p and q are equal.

    GeoCoq: EqP : Plane -> Plane -> Prop (equivalence relation)
    """
    left: str
    right: str

    def __repr__(self) -> str:
        return f"EqP({self.left}, {self.right})"


@dataclass(frozen=True)
class EqPt(HAtom):
    """A = B — points A and B are equal.

    Used for point equality / distinctness assertions.
    """
    left: str
    right: str

    def __repr__(self) -> str:
        return f"{self.left} = {self.right}"


# ═══════════════════════════════════════════════════════════════════════
# Defined predicates (derived from primitives, matching GeoCoq)
# ═══════════════════════════════════════════════════════════════════════

@dataclass(frozen=True)
class ColH(HAtom):
    """ColH(A, B, C) — A, B, C are collinear.

    GeoCoq definition:
      ColH A B C := exists l, IncidL A l /\\ IncidL B l /\\ IncidL C l
    """
    a: str
    b: str
    c: str

    def __repr__(self) -> str:
        return f"ColH({self.a}, {self.b}, {self.c})"


@dataclass(frozen=True)
class Cut(HAtom):
    """cut(l, A, B) — line l separates points A and B.

    GeoCoq definition:
      cut l A B := ~IncidL A l /\\ ~IncidL B l /\\
                   exists I, IncidL I l /\\ BetH A I B
    """
    line: str
    a: str
    b: str

    def __repr__(self) -> str:
        return f"cut({self.line}, {self.a}, {self.b})"


@dataclass(frozen=True)
class OutH(HAtom):
    """outH(P, A, B) — A is on ray from P through B (or A = B with P ≠ A).

    GeoCoq definition:
      outH P A B := BetH P A B \\/ BetH P B A \\/ (P <> A /\\ A = B)
    """
    p: str
    a: str
    b: str

    def __repr__(self) -> str:
        return f"outH({self.p}, {self.a}, {self.b})"


@dataclass(frozen=True)
class Disjoint(HAtom):
    """disjoint(A, B, C, D) — segments AB and CD share no interior point.

    GeoCoq definition:
      disjoint A B C D := ~exists P, BetH A P B /\\ BetH C P D
    """
    a: str
    b: str
    c: str
    d: str

    def __repr__(self) -> str:
        return f"disjoint({self.a}, {self.b}, {self.c}, {self.d})"


@dataclass(frozen=True)
class SameSideH(HAtom):
    """same_side(A, B, l) — A and B are on the same side of line l.

    GeoCoq definition:
      same_side A B l := exists P, cut l A P /\\ cut l B P
    """
    a: str
    b: str
    line: str

    def __repr__(self) -> str:
        return f"same_side({self.a}, {self.b}, {self.line})"


@dataclass(frozen=True)
class SameSidePrime(HAtom):
    """same_side'(A, B, X, Y) — A, B on same side of every line through X, Y.

    GeoCoq definition:
      same_side' A B X Y :=
        X <> Y /\\ forall l, IncidL X l -> IncidL Y l -> same_side A B l
    """
    a: str
    b: str
    x: str
    y: str

    def __repr__(self) -> str:
        return f"same_side'({self.a}, {self.b}, {self.x}, {self.y})"


@dataclass(frozen=True)
class Para(HAtom):
    """Para(l, m) — lines l and m are parallel.

    GeoCoq definition:
      Para l m := (~exists X, IncidL X l /\\ IncidL X m) /\\
                  exists p, IncidLP l p /\\ IncidLP m p
    """
    line1: str
    line2: str

    def __repr__(self) -> str:
        return f"Para({self.line1}, {self.line2})"


@dataclass(frozen=True)
class IncidLP(HAtom):
    """IncidLP(l, p) — line l lies on plane p.

    GeoCoq definition:
      IncidLP l p := forall A, IncidL A l -> IncidP A p
    """
    line: str
    plane: str

    def __repr__(self) -> str:
        return f"IncidLP({self.line}, {self.plane})"


# ═══════════════════════════════════════════════════════════════════════
# Literals
# ═══════════════════════════════════════════════════════════════════════

@dataclass(frozen=True)
class HLiteral:
    """A literal is an atomic formula or its negation in System H.

    polarity=True: the atom is asserted.
    polarity=False: the atom is negated.
    """
    atom: HAtom
    polarity: bool = True

    def negated(self) -> HLiteral:
        return HLiteral(self.atom, not self.polarity)

    @property
    def is_positive(self) -> bool:
        return self.polarity

    @property
    def is_negative(self) -> bool:
        return not self.polarity

    @property
    def is_incidence(self) -> bool:
        """True if this involves incidence relations (Group I)."""
        return isinstance(self.atom, (IncidL, IncidP, EqL, EqP, ColH,
                                       IncidLP))

    @property
    def is_order(self) -> bool:
        """True if this involves order relations (Group II)."""
        return isinstance(self.atom, (BetH, Cut, OutH))

    @property
    def is_congruence(self) -> bool:
        """True if this involves congruence relations (Group III)."""
        return isinstance(self.atom, (CongH, CongaH, Disjoint,
                                       SameSideH, SameSidePrime))

    def __repr__(self) -> str:
        if self.polarity:
            return repr(self.atom)
        return f"\u00ac({self.atom})"


# ═══════════════════════════════════════════════════════════════════════
# Clauses (disjunctive sets of literals, for axiom encoding)
# ═══════════════════════════════════════════════════════════════════════

@dataclass(frozen=True)
class HClause:
    """A clause is a finite set of literals, read disjunctively.

    Encoding follows the same pattern as System E (Section 3.8):
    an axiom "if φ₁, …, φₙ then ψ" becomes {¬φ₁, …, ¬φₙ, ψ}.
    """
    literals: FrozenSet[HLiteral]

    def __repr__(self) -> str:
        return " \u2228 ".join(repr(l) for l in self.literals)


# ═══════════════════════════════════════════════════════════════════════
# Sequents
# ═══════════════════════════════════════════════════════════════════════

@dataclass
class HSequent:
    """Γ ⇒ ∃x̄. Δ  — a sequent in System H.

    hypotheses: Γ — set of literals (assumptions)
    exists_vars: x̄ — existentially quantified variables
    conclusions: Δ — set of literals (derived assertions)
    """
    hypotheses: List[HLiteral] = field(default_factory=list)
    exists_vars: List[Tuple[str, HSort]] = field(default_factory=list)
    conclusions: List[HLiteral] = field(default_factory=list)

    def __repr__(self) -> str:
        hyp = ", ".join(repr(l) for l in self.hypotheses)
        conc = ", ".join(repr(l) for l in self.conclusions)
        if self.exists_vars:
            evars = ", ".join(f"{n}:{s.name}" for n, s in self.exists_vars)
            return f"{hyp} \u21d2 \u2203{evars}. {conc}"
        return f"{hyp} \u21d2 {conc}"


# ═══════════════════════════════════════════════════════════════════════
# Proof structure
# ═══════════════════════════════════════════════════════════════════════

class HStepKind(Enum):
    """The type of a proof step in System H."""
    CONSTRUCTION = auto()     # introduces new objects (line_existence, etc.)
    INCIDENCE = auto()        # Group I inference
    ORDER = auto()            # Group II inference
    CONGRUENCE = auto()       # Group III inference
    THEOREM_APP = auto()      # applies a previously proved theorem
    CASE_SPLIT = auto()       # proof by cases (e.g., pasch disjunction)
    DEFINED_PRED = auto()     # unfold/fold a defined predicate


@dataclass
class HProofStep:
    """A single step in a System H proof."""
    id: int
    kind: HStepKind
    description: str = ""
    assertions: List[HLiteral] = field(default_factory=list)
    new_vars: List[Tuple[str, HSort]] = field(default_factory=list)
    refs: List[int] = field(default_factory=list)
    split_atom: Optional[HAtom] = None
    theorem_name: str = ""
    var_map: Dict[str, str] = field(default_factory=dict)
    subproofs: List[List[HProofStep]] = field(default_factory=list)


@dataclass
class HTheorem:
    """A proved theorem in System H."""
    name: str
    statement: str
    sequent: HSequent


@dataclass
class HProof:
    """A proof in System H."""
    name: str
    hypotheses: List[HLiteral] = field(default_factory=list)
    exists_vars: List[Tuple[str, HSort]] = field(default_factory=list)
    goal: List[HLiteral] = field(default_factory=list)
    free_vars: List[Tuple[str, HSort]] = field(default_factory=list)
    steps: List[HProofStep] = field(default_factory=list)
    symbols: Dict[str, Any] = field(default_factory=dict)


# ═══════════════════════════════════════════════════════════════════════
# Utility functions
# ═══════════════════════════════════════════════════════════════════════

def h_atom_vars(atom: HAtom) -> Set[str]:
    """Return the set of variable names occurring in an atom."""
    if isinstance(atom, IncidL):
        return {atom.point, atom.line}
    if isinstance(atom, IncidP):
        return {atom.point, atom.plane}
    if isinstance(atom, BetH):
        return {atom.a, atom.b, atom.c}
    if isinstance(atom, CongH):
        return {atom.a, atom.b, atom.c, atom.d}
    if isinstance(atom, CongaH):
        return {atom.a, atom.b, atom.c, atom.d, atom.e, atom.f}
    if isinstance(atom, EqL):
        return {atom.left, atom.right}
    if isinstance(atom, EqP):
        return {atom.left, atom.right}
    if isinstance(atom, EqPt):
        return {atom.left, atom.right}
    if isinstance(atom, ColH):
        return {atom.a, atom.b, atom.c}
    if isinstance(atom, Cut):
        return {atom.line, atom.a, atom.b}
    if isinstance(atom, OutH):
        return {atom.p, atom.a, atom.b}
    if isinstance(atom, Disjoint):
        return {atom.a, atom.b, atom.c, atom.d}
    if isinstance(atom, SameSideH):
        return {atom.a, atom.b, atom.line}
    if isinstance(atom, SameSidePrime):
        return {atom.a, atom.b, atom.x, atom.y}
    if isinstance(atom, Para):
        return {atom.line1, atom.line2}
    if isinstance(atom, IncidLP):
        return {atom.line, atom.plane}
    return set()


def h_literal_vars(lit: HLiteral) -> Set[str]:
    """All variable names in a literal."""
    return h_atom_vars(lit.atom)


def h_substitute_atom(atom: HAtom, m: Dict[str, str]) -> HAtom:
    """Apply a variable renaming to an atom."""
    def s(v: str) -> str:
        return m.get(v, v)

    if isinstance(atom, IncidL):
        return IncidL(s(atom.point), s(atom.line))
    if isinstance(atom, IncidP):
        return IncidP(s(atom.point), s(atom.plane))
    if isinstance(atom, BetH):
        return BetH(s(atom.a), s(atom.b), s(atom.c))
    if isinstance(atom, CongH):
        return CongH(s(atom.a), s(atom.b), s(atom.c), s(atom.d))
    if isinstance(atom, CongaH):
        return CongaH(s(atom.a), s(atom.b), s(atom.c),
                       s(atom.d), s(atom.e), s(atom.f))
    if isinstance(atom, EqL):
        return EqL(s(atom.left), s(atom.right))
    if isinstance(atom, EqP):
        return EqP(s(atom.left), s(atom.right))
    if isinstance(atom, EqPt):
        return EqPt(s(atom.left), s(atom.right))
    if isinstance(atom, ColH):
        return ColH(s(atom.a), s(atom.b), s(atom.c))
    if isinstance(atom, Cut):
        return Cut(s(atom.line), s(atom.a), s(atom.b))
    if isinstance(atom, OutH):
        return OutH(s(atom.p), s(atom.a), s(atom.b))
    if isinstance(atom, Disjoint):
        return Disjoint(s(atom.a), s(atom.b), s(atom.c), s(atom.d))
    if isinstance(atom, SameSideH):
        return SameSideH(s(atom.a), s(atom.b), s(atom.line))
    if isinstance(atom, SameSidePrime):
        return SameSidePrime(s(atom.a), s(atom.b), s(atom.x), s(atom.y))
    if isinstance(atom, Para):
        return Para(s(atom.line1), s(atom.line2))
    if isinstance(atom, IncidLP):
        return IncidLP(s(atom.line), s(atom.plane))
    return atom


def h_substitute_literal(lit: HLiteral, mapping: Dict[str, str]) -> HLiteral:
    """Apply a variable renaming to a literal."""
    return HLiteral(h_substitute_atom(lit.atom, mapping), lit.polarity)
