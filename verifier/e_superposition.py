"""
e_superposition.py — Superposition rules for System E (Section 3.7).

Superposition provides the SAS (Prop I.4) and SSS (Prop I.8) triangle
congruence rules as *elimination rules* in the sequent calculus.

Key idea: superposition allows one to "act as though" one has constructed
a congruent copy of a figure, but only for the sake of proving things
about objects *already present* in the diagram.

SAS superposition:
  Given: abc distinct and noncollinear, d on line L, g on L, h not on L.
  Assume: a' = d, ∠a'b'c' = ∠abc, on(b', L), ¬between(b', d, g),
          same-side(c', h, L)
  Then: the metric facts of the superimposed triangle can be used to
        derive conclusions about existing objects.

SSS superposition:
  Given: abc distinct and noncollinear, d on line L, g on L, h not on L.
  Assume: a' = d, ab = a'b', bc = b'c', ca = c'a', on(b', L),
          ¬between(b', d, g), same-side(c', h, L)
  Then: ditto.

In sequent form:
     Γ ⇒ ∃x̄. Δ       Γ, Δ, Θᵢ ⇒ Δ'
    ──────────────────────────────────
          Γ ⇒ ∃x̄. Δ, Δ'
"""
from __future__ import annotations

from dataclasses import dataclass, field
from typing import Dict, List, Optional, Set, Tuple

from .e_ast import (
    Sort, Literal,
    On, SameSide, Between, Equals,
    SegmentTerm, AngleTerm, AreaTerm,
    substitute_literal,
)


def _seg_eq_in_known(known: Set[Literal], a: str, b: str,
                     c: str, d: str) -> bool:
    """Check if segment equality ab=cd is in known, allowing symmetry.

    Checks all four orderings: ab=cd, ba=cd, ab=dc, ba=dc
    (Equals itself is symmetric, so ab=cd also matches cd=ab.)
    """
    for p, q in [(a, b), (b, a)]:
        for r, s in [(c, d), (d, c)]:
            if Literal(Equals(SegmentTerm(p, q),
                              SegmentTerm(r, s))) in known:
                return True
    return False


@dataclass
class SuperpositionHypotheses:
    """The hypotheses Θ of a superposition step.

    These are the "as-if" facts about the superimposed triangle a'b'c'.
    """
    # Point identifications
    vertex_eq: Literal  # a' = d

    # Line/side placement
    on_line: Literal    # on(b', L)
    direction: Literal  # ¬between(b', d, g)
    same_side: Literal  # same-side(c', h, L)

    # SAS-specific: angle equality
    angle_eq: Optional[Literal] = None  # ∠a'b'c' = ∠abc

    # SSS-specific: side equalities
    side_eqs: List[Literal] = field(default_factory=list)
    # ab = a'b', bc = b'c', ca = c'a'


def sas_hypotheses(
    a: str, b: str, c: str,       # Original triangle points
    ap: str, bp: str, cp: str,    # Superimposed triangle points (primed)
    d: str, L: str, g: str, h: str,  # Placement: d on L, g on L, h not on L
) -> SuperpositionHypotheses:
    """Construct SAS superposition hypotheses.

    The superimposed triangle a'b'c' is placed so that:
      - a' coincides with d
      - ∠a'b'c' = ∠abc
      - b' lies on L in the same direction as g from d
      - c' is on the same side of L as h
    """
    return SuperpositionHypotheses(
        vertex_eq=Literal(Equals(ap, d)),
        on_line=Literal(On(bp, L)),
        direction=Literal(Between(bp, d, g), polarity=False),
        same_side=Literal(SameSide(cp, h, L)),
        angle_eq=Literal(Equals(
            AngleTerm(ap, bp, cp), AngleTerm(a, b, c))),
    )


def sss_hypotheses(
    a: str, b: str, c: str,
    ap: str, bp: str, cp: str,
    d: str, L: str, g: str, h: str,
) -> SuperpositionHypotheses:
    """Construct SSS superposition hypotheses.

    The superimposed triangle a'b'c' is placed so that:
      - a' coincides with d
      - ab = a'b', bc = b'c', ca = c'a'
      - b' lies on L in the same direction as g from d
      - c' is on the same side of L as h
    """
    return SuperpositionHypotheses(
        vertex_eq=Literal(Equals(ap, d)),
        on_line=Literal(On(bp, L)),
        direction=Literal(Between(bp, d, g), polarity=False),
        same_side=Literal(SameSide(cp, h, L)),
        side_eqs=[
            Literal(Equals(SegmentTerm(a, b), SegmentTerm(ap, bp))),
            Literal(Equals(SegmentTerm(b, c), SegmentTerm(bp, cp))),
            Literal(Equals(SegmentTerm(c, a), SegmentTerm(cp, ap))),
        ],
    )


def superposition_literals(hyps: SuperpositionHypotheses) -> List[Literal]:
    """Get all literals assumed during the superposition step."""
    lits = [hyps.vertex_eq, hyps.on_line, hyps.direction, hyps.same_side]
    if hyps.angle_eq is not None:
        lits.append(hyps.angle_eq)
    lits.extend(hyps.side_eqs)
    return lits


def validate_superposition_prereqs(
    known: Set[Literal],
    a: str, b: str, c: str,
) -> bool:
    """Check that abc are distinct and noncollinear.

    Prerequisites for superposition:
      - a ≠ b, b ≠ c, a ≠ c
      - Triangle(a, b, c) — i.e. not all on the same line
    """
    needed = [
        Literal(Equals(a, b), polarity=False),
        Literal(Equals(b, c), polarity=False),
        Literal(Equals(a, c), polarity=False),
    ]
    return all(n in known for n in needed)


@dataclass
class SuperpositionResult:
    """Result of a superposition step.

    Contains the new conclusions that can be derived about the
    original objects (not the superimposed ones).
    """
    derived: List[Literal] = field(default_factory=list)
    # The fresh variables introduced for the superimposed triangle
    fresh_vars: List[Tuple[str, Sort]] = field(default_factory=list)
    valid: bool = True
    error: str = ""


def apply_sas_superposition(
    known: Set[Literal],
    a: str, b: str, c: str,
    d: str, e: str, f: str,
    # Metric: ab = de, ac = df, ∠bac = ∠edf
) -> SuperpositionResult:
    """Apply SAS superposition to derive congruence facts.

    Given: Equal(AB, DE), Equal(AC, DF), EqualAngle(B,A,C, E,D,F)
    Derives: All corresponding parts are equal (CPCTC)
    """
    result = SuperpositionResult()

    # Check SAS prerequisites (segment equality with symmetry)
    if not _seg_eq_in_known(known, a, b, d, e):
        result.valid = False
        result.error = f"Missing: {a}{b} = {d}{e}"
        return result
    if not _seg_eq_in_known(known, a, c, d, f):
        result.valid = False
        result.error = f"Missing: {a}{c} = {d}{f}"
        return result

    angle_eq = Literal(Equals(AngleTerm(b, a, c), AngleTerm(e, d, f)))
    if angle_eq not in known:
        result.valid = False
        result.error = f"Missing: {angle_eq}"
        return result

    # SAS conclusion: full congruence (all 6 parts equal)
    result.derived = [
        # Remaining side
        Literal(Equals(SegmentTerm(b, c), SegmentTerm(e, f))),
        # Remaining angles
        Literal(Equals(AngleTerm(a, b, c), AngleTerm(d, e, f))),
        Literal(Equals(AngleTerm(a, c, b), AngleTerm(d, f, e))),
        # Area equality (M9: full congruence → equal areas)
        Literal(Equals(AreaTerm(a, b, c), AreaTerm(d, e, f))),
    ]
    return result


def apply_sss_superposition(
    known: Set[Literal],
    a: str, b: str, c: str,
    d: str, e: str, f: str,
) -> SuperpositionResult:
    """Apply SSS superposition to derive congruence facts.

    Given: Equal(AB, DE), Equal(BC, EF), Equal(CA, FD)
    Derives: All corresponding angles are equal (CPCTC)
    """
    result = SuperpositionResult()

    # Check SSS prerequisites (segment equality with symmetry)
    if not _seg_eq_in_known(known, a, b, d, e):
        result.valid = False
        result.error = f"Missing: {a}{b} = {d}{e}"
        return result
    if not _seg_eq_in_known(known, b, c, e, f):
        result.valid = False
        result.error = f"Missing: {b}{c} = {e}{f}"
        return result
    if not _seg_eq_in_known(known, c, a, f, d):
        result.valid = False
        result.error = f"Missing: {c}{a} = {f}{d}"
        return result

    # SSS conclusion: all corresponding angles are equal + area
    result.derived = [
        Literal(Equals(AngleTerm(b, a, c), AngleTerm(e, d, f))),
        Literal(Equals(AngleTerm(a, b, c), AngleTerm(d, e, f))),
        Literal(Equals(AngleTerm(a, c, b), AngleTerm(d, f, e))),
        # Area equality (M9: full congruence → equal areas)
        Literal(Equals(AreaTerm(a, b, c), AreaTerm(d, e, f))),
    ]
    return result
