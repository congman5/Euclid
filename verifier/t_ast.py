"""
t_ast.py — AST for Tarski's axiom system (System T).

System T is Tarski's axiomatization of Euclidean geometry using only
one sort (points) and two primitive relations:
  - B(a, b, c):        nonstrict betweenness — b is between a and c
                        (or equal to a or c)
  - Cong(a, b, c, d):  equidistance — segment ab is congruent to cd

Tarski's system serves as the bridge between System E (Avigad, Dean,
Mumma 2009) and System H (Hilbert), enabling the completeness proof:
  System E ↔ Tarski (T) ↔ System H

To make the axioms geometric (in the sense of Negri 2003), we add
explicit negation predicates following Paper Section 5.2:
  - NotB(a, b, c):        ¬B(a, b, c)
  - NotCong(a, b, c, d):  ¬Cong(a, b, c, d)
  - Neq(a, b):            a ≠ b

Reference:
  - Avigad, Dean, Mumma (2009), Section 5.2
  - GeoCoq tarski_axioms.v (https://geocoq.github.io/GeoCoq/)
  - Tarski & Givant (1999), "Tarski's system of geometry"
"""
from __future__ import annotations

from dataclasses import dataclass, field
from enum import Enum, auto
from typing import Any, Dict, FrozenSet, List, Optional, Set, Tuple, Union


# ═══════════════════════════════════════════════════════════════════════
# Sorts
# ═══════════════════════════════════════════════════════════════════════

class TSort(Enum):
    """The single sort of System T."""
    POINT = auto()


# ═══════════════════════════════════════════════════════════════════════
# Atomic formulas — primitive and negation predicates
# ═══════════════════════════════════════════════════════════════════════

class TAtom:
    """Base class for atomic formulas in System T."""
    pass


# ── Primitive relations ───────────────────────────────────────────────

@dataclass(frozen=True)
class B(TAtom):
    """B(a, b, c) — nonstrict betweenness: b lies between a and c.

    Tarski's betweenness is nonstrict: B(a, a, b) and B(a, b, b) hold.
    This differs from System E's strict between(a, b, c).

    GeoCoq: Bet : Tpoint -> Tpoint -> Tpoint -> Prop
    """
    a: str
    b: str
    c: str

    def __repr__(self) -> str:
        return f"B({self.a}, {self.b}, {self.c})"


@dataclass(frozen=True)
class Cong(TAtom):
    """Cong(a, b, c, d) — equidistance: segment ab ≅ segment cd.

    GeoCoq: Cong : Tpoint -> Tpoint -> Tpoint -> Tpoint -> Prop
    """
    a: str
    b: str
    c: str
    d: str

    def __repr__(self) -> str:
        return f"Cong({self.a}, {self.b}, {self.c}, {self.d})"


# ── Explicit negation predicates (Section 5.2) ───────────────────────
# These make the axiom system geometric (Negri 2003), allowing all
# axioms to be expressed as geometric rule schemes.

@dataclass(frozen=True)
class NotB(TAtom):
    """NotB(a, b, c) — negation of B(a, b, c).

    Paper Section 5.2: "expand our language to one called L(T) by
    adding predicates ≠ and B̄ and ≢"
    """
    a: str
    b: str
    c: str

    def __repr__(self) -> str:
        return f"NotB({self.a}, {self.b}, {self.c})"


@dataclass(frozen=True)
class NotCong(TAtom):
    """NotCong(a, b, c, d) — negation of Cong(a, b, c, d)."""
    a: str
    b: str
    c: str
    d: str

    def __repr__(self) -> str:
        return f"NotCong({self.a}, {self.b}, {self.c}, {self.d})"


@dataclass(frozen=True)
class Eq(TAtom):
    """Eq(a, b) — point equality: a = b."""
    left: str
    right: str

    def __repr__(self) -> str:
        return f"{self.left} = {self.right}"


@dataclass(frozen=True)
class Neq(TAtom):
    """Neq(a, b) — point disequality: a ≠ b."""
    left: str
    right: str

    def __repr__(self) -> str:
        return f"{self.left} ≠ {self.right}"


# ═══════════════════════════════════════════════════════════════════════
# Literals
# ═══════════════════════════════════════════════════════════════════════

@dataclass(frozen=True)
class TLiteral:
    """A literal is an atomic formula or its negation in System T.

    polarity=True: the atom is asserted.
    polarity=False: the atom is negated.
    """
    atom: TAtom
    polarity: bool = True

    def negated(self) -> TLiteral:
        return TLiteral(self.atom, not self.polarity)

    @property
    def is_positive(self) -> bool:
        return self.polarity

    @property
    def is_negative(self) -> bool:
        return not self.polarity

    @property
    def is_betweenness(self) -> bool:
        """True if this involves betweenness (B or NotB)."""
        return isinstance(self.atom, (B, NotB))

    @property
    def is_congruence(self) -> bool:
        """True if this involves equidistance (Cong or NotCong)."""
        return isinstance(self.atom, (Cong, NotCong))

    @property
    def is_equality(self) -> bool:
        """True if this involves point equality (Eq or Neq)."""
        return isinstance(self.atom, (Eq, Neq))

    def __repr__(self) -> str:
        if self.polarity:
            return repr(self.atom)
        return f"¬({self.atom})"


# ═══════════════════════════════════════════════════════════════════════
# Clauses (disjunctive sets of literals, for axiom encoding)
# ═══════════════════════════════════════════════════════════════════════

@dataclass(frozen=True)
class TClause:
    """A clause is a finite set of literals, read disjunctively.

    Encoding follows the same pattern as System E (Section 3.8):
    an axiom "if φ₁, …, φₙ then ψ" becomes {¬φ₁, …, ¬φₙ, ψ}.
    """
    literals: FrozenSet[TLiteral]

    def __repr__(self) -> str:
        return " ∨ ".join(repr(l) for l in self.literals)


# ═══════════════════════════════════════════════════════════════════════
# Sequents
# ═══════════════════════════════════════════════════════════════════════

@dataclass
class TSequent:
    """Γ ⇒ ∃x̄. Δ  — a sequent in System T.

    hypotheses: Γ — set of literals (assumptions)
    exists_vars: x̄ — existentially quantified point variables
    conclusions: Δ — set of literals (derived assertions)
    """
    hypotheses: List[TLiteral] = field(default_factory=list)
    exists_vars: List[Tuple[str, TSort]] = field(default_factory=list)
    conclusions: List[TLiteral] = field(default_factory=list)

    def __repr__(self) -> str:
        hyp = ", ".join(repr(l) for l in self.hypotheses)
        conc = ", ".join(repr(l) for l in self.conclusions)
        if self.exists_vars:
            evars = ", ".join(f"{n}:{s.name}" for n, s in self.exists_vars)
            return f"{hyp} ⇒ ∃{evars}. {conc}"
        return f"{hyp} ⇒ {conc}"


# ═══════════════════════════════════════════════════════════════════════
# Proof structure
# ═══════════════════════════════════════════════════════════════════════

class TStepKind(Enum):
    """The type of a proof step in System T."""
    CONSTRUCTION = auto()     # introduces new points (SC, P, PP, Int, 2L)
    DEDUCTION = auto()        # derives facts (E1–E3, B, 5S, negativity)
    CASE_SPLIT = auto()       # 2U upper-dimension disjunction or negativity
    THEOREM_APP = auto()      # applies a previously proved theorem


@dataclass
class TProofStep:
    """A single step in a System T proof."""
    id: int
    kind: TStepKind
    description: str = ""
    assertions: List[TLiteral] = field(default_factory=list)
    new_vars: List[Tuple[str, TSort]] = field(default_factory=list)
    refs: List[int] = field(default_factory=list)
    # For case splits
    split_atom: Optional[TAtom] = None
    subproofs: List[List[TProofStep]] = field(default_factory=list)
    # For theorem application
    theorem_name: str = ""
    var_map: Dict[str, str] = field(default_factory=dict)


@dataclass
class TTheorem:
    """A proved theorem in System T."""
    name: str
    statement: str
    sequent: TSequent


@dataclass
class TProof:
    """A proof in System T."""
    name: str
    hypotheses: List[TLiteral] = field(default_factory=list)
    exists_vars: List[Tuple[str, TSort]] = field(default_factory=list)
    goal: List[TLiteral] = field(default_factory=list)
    free_vars: List[Tuple[str, TSort]] = field(default_factory=list)
    steps: List[TProofStep] = field(default_factory=list)


# ═══════════════════════════════════════════════════════════════════════
# Utility functions
# ═══════════════════════════════════════════════════════════════════════

def t_atom_vars(atom: TAtom) -> Set[str]:
    """Return the set of variable names occurring in an atom."""
    if isinstance(atom, B):
        return {atom.a, atom.b, atom.c}
    if isinstance(atom, Cong):
        return {atom.a, atom.b, atom.c, atom.d}
    if isinstance(atom, NotB):
        return {atom.a, atom.b, atom.c}
    if isinstance(atom, NotCong):
        return {atom.a, atom.b, atom.c, atom.d}
    if isinstance(atom, Eq):
        return {atom.left, atom.right}
    if isinstance(atom, Neq):
        return {atom.left, atom.right}
    return set()


def t_literal_vars(lit: TLiteral) -> Set[str]:
    """All variable names in a literal."""
    return t_atom_vars(lit.atom)


def t_substitute_atom(atom: TAtom, m: Dict[str, str]) -> TAtom:
    """Apply a variable renaming to an atom."""
    def s(v: str) -> str:
        return m.get(v, v)

    if isinstance(atom, B):
        return B(s(atom.a), s(atom.b), s(atom.c))
    if isinstance(atom, Cong):
        return Cong(s(atom.a), s(atom.b), s(atom.c), s(atom.d))
    if isinstance(atom, NotB):
        return NotB(s(atom.a), s(atom.b), s(atom.c))
    if isinstance(atom, NotCong):
        return NotCong(s(atom.a), s(atom.b), s(atom.c), s(atom.d))
    if isinstance(atom, Eq):
        return Eq(s(atom.left), s(atom.right))
    if isinstance(atom, Neq):
        return Neq(s(atom.left), s(atom.right))
    return atom


def t_substitute_literal(lit: TLiteral, mapping: Dict[str, str]) -> TLiteral:
    """Apply a variable renaming to a literal."""
    return TLiteral(t_substitute_atom(lit.atom, mapping), lit.polarity)
