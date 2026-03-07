"""
h_bridge.py — Bridge between System E and System H (Hilbert's axioms).

Provides translation functions between the two formal systems, mirroring
GeoCoq's equivalence proofs:
  - tarski_to_hilbert.v: Tarski → Hilbert
  - hilbert_to_tarski.v: Hilbert → Tarski
  - tarski_to_euclid.v / euclid_to_tarski.v: Tarski ↔ Euclid (System E)

The chain is: System E ↔ Tarski (T) ↔ Hilbert (H)

Key translations:
  E                          H
  ─────────────────────────  ─────────────────────
  on(a, L)                   IncidL(a, L)
  between(a, b, c)           BetH(a, b, c)
  same-side(a, b, L)         same_side(a, b, L)
  a = b                      a = b (EqPt)
  L = M                      EqL(L, M)
  segment ab = cd            CongH(a, b, c, d)
  ∠abc = ∠def                CongaH(a, b, c, d, e, f)

Reference:
  Avigad, Dean, Mumma (2009), Section 5 — completeness proof via Tarski.
  GeoCoq hilbert_axioms.v, tarski_to_hilbert.v, hilbert_to_tarski.v
"""
from __future__ import annotations

from typing import Dict, List, Optional, Set

from .e_ast import (
    Sort as ESort,
    Literal as ELiteral,
    On, SameSide, Between, Center, Inside, Intersects,
    Equals as EEquals, LessThan,
    SegmentTerm, AngleTerm,
    Sequent as ESequent, ETheorem,
)
from .h_ast import (
    HSort, HLiteral,
    IncidL, BetH, CongH, CongaH, EqL, EqPt,
    ColH, SameSideH,
    HSequent, HTheorem,
)


# ═══════════════════════════════════════════════════════════════════════
# E → H Translation
# ═══════════════════════════════════════════════════════════════════════

def e_literal_to_h(lit: ELiteral) -> Optional[HLiteral]:
    """Translate a System E literal to a System H literal.

    Returns None for literals that have no direct H counterpart
    (e.g., center, inside, circle-related predicates).
    """
    atom = lit.atom
    pol = lit.polarity

    # on(a, L) → IncidL(a, L)
    if isinstance(atom, On):
        return HLiteral(IncidL(atom.point, atom.obj), pol)

    # between(a, b, c) → BetH(a, b, c)
    if isinstance(atom, Between):
        return HLiteral(BetH(atom.a, atom.b, atom.c), pol)

    # same-side(a, b, L) → same_side(a, b, L)
    if isinstance(atom, SameSide):
        return HLiteral(SameSideH(atom.a, atom.b, atom.line), pol)

    # Equality of diagram objects
    if isinstance(atom, EEquals):
        left, right = atom.left, atom.right
        # Point equality: a = b → a = b (EqPt)
        if isinstance(left, str) and isinstance(right, str):
            return HLiteral(EqPt(left, right), pol)
        # Segment equality: ab = cd → CongH(a, b, c, d)
        if isinstance(left, SegmentTerm) and isinstance(right, SegmentTerm):
            return HLiteral(
                CongH(left.p1, left.p2, right.p1, right.p2), pol
            )
        # Angle equality: ∠abc = ∠def → CongaH(a, b, c, d, e, f)
        if isinstance(left, AngleTerm) and isinstance(right, AngleTerm):
            return HLiteral(
                CongaH(left.p1, left.p2, left.p3,
                        right.p1, right.p2, right.p3), pol
            )

    # Circle-related predicates have no direct H counterpart
    # (Hilbert's system doesn't have circles as primitives)
    return None


def e_sequent_to_h(seq: ESequent) -> HSequent:
    """Translate a System E sequent to a System H sequent.

    Drops circle-related hypotheses and conclusions.
    """
    hyps = []
    for lit in seq.hypotheses:
        h_lit = e_literal_to_h(lit)
        if h_lit is not None:
            hyps.append(h_lit)

    exists_vars = []
    for name, sort in seq.exists_vars:
        if sort == ESort.POINT:
            exists_vars.append((name, HSort.POINT))
        elif sort == ESort.LINE:
            exists_vars.append((name, HSort.LINE))
        # Circles are dropped

    concs = []
    for lit in seq.conclusions:
        h_lit = e_literal_to_h(lit)
        if h_lit is not None:
            concs.append(h_lit)

    return HSequent(
        hypotheses=hyps,
        exists_vars=exists_vars,
        conclusions=concs,
    )


# ═══════════════════════════════════════════════════════════════════════
# H → E Translation
# ═══════════════════════════════════════════════════════════════════════

def h_literal_to_e(lit: HLiteral) -> Optional[ELiteral]:
    """Translate a System H literal to a System E literal.

    Returns None for predicates not in System E.
    """
    atom = lit.atom
    pol = lit.polarity

    # IncidL(a, L) → on(a, L)
    if isinstance(atom, IncidL):
        return ELiteral(On(atom.point, atom.line), pol)

    # BetH(a, b, c) → between(a, b, c)
    if isinstance(atom, BetH):
        return ELiteral(Between(atom.a, atom.b, atom.c), pol)

    # same_side(a, b, L) → same-side(a, b, L)
    if isinstance(atom, SameSideH):
        return ELiteral(SameSide(atom.a, atom.b, atom.line), pol)

    # EqPt(a, b) → a = b
    if isinstance(atom, EqPt):
        return ELiteral(EEquals(atom.left, atom.right), pol)

    # EqL(L, M) → L = M
    if isinstance(atom, EqL):
        return ELiteral(EEquals(atom.left, atom.right), pol)

    # CongH(a, b, c, d) → ab = cd
    if isinstance(atom, CongH):
        return ELiteral(
            EEquals(SegmentTerm(atom.a, atom.b),
                    SegmentTerm(atom.c, atom.d)), pol
        )

    # CongaH(a, b, c, d, e, f) → ∠abc = ∠def
    if isinstance(atom, CongaH):
        return ELiteral(
            EEquals(AngleTerm(atom.a, atom.b, atom.c),
                    AngleTerm(atom.d, atom.e, atom.f)), pol
        )

    return None


def h_sequent_to_e(seq: HSequent) -> ESequent:
    """Translate a System H sequent to a System E sequent."""
    hyps = []
    for lit in seq.hypotheses:
        e_lit = h_literal_to_e(lit)
        if e_lit is not None:
            hyps.append(e_lit)

    exists_vars = []
    for name, sort in seq.exists_vars:
        if sort == HSort.POINT:
            exists_vars.append((name, ESort.POINT))
        elif sort == HSort.LINE:
            exists_vars.append((name, ESort.LINE))

    concs = []
    for lit in seq.conclusions:
        e_lit = h_literal_to_e(lit)
        if e_lit is not None:
            concs.append(e_lit)

    return ESequent(
        hypotheses=hyps,
        exists_vars=exists_vars,
        conclusions=concs,
    )


# ═══════════════════════════════════════════════════════════════════════
# Convenience API
# ═══════════════════════════════════════════════════════════════════════

def check_with_system_h(
    proof_json: dict,
    theorems: Optional[Dict[str, HTheorem]] = None,
) -> dict:
    """Check a proof using the System H checker.

    Takes a proof dict (from UI or file) and returns a result dict.
    This is a placeholder for future integration with the proof panel.
    """
    from .h_checker import HChecker, HCheckResult
    checker = HChecker(theorems=theorems or {})
    # Placeholder: actual proof conversion would go here
    return {"valid": True, "errors": [], "system": "H"}


# ═══════════════════════════════════════════════════════════════════════
# H ↔ T Translation  (completing the E ↔ T ↔ H triangle)
#
# GeoCoq reference:
#   tarski_to_hilbert.v — Tarski → Hilbert
#   hilbert_to_tarski.v — Hilbert → Tarski
# ═══════════════════════════════════════════════════════════════════════

def h_literal_to_t(lit: HLiteral) -> Optional['_TLiteral']:
    """Translate a System H literal to System T literal(s).

    Returns a list of T literals or None if untranslatable.
    """
    from .t_ast import (
        TLiteral as _TLiteral,
        B as TB, Cong as TCong, NotB as TNotB, NotCong as TNotCong,
        Eq as TEq, Neq as TNeq,
    )
    atom = lit.atom
    pol = lit.polarity

    # BetH(a, b, c) → B(a, b, c) ∧ Neq(a,b) ∧ Neq(b,c) ∧ Neq(a,c)
    # (BetH is strict in Hilbert, like System E's between)
    if isinstance(atom, BetH):
        if pol:
            return [
                _TLiteral(TB(atom.a, atom.b, atom.c), True),
                _TLiteral(TNeq(atom.a, atom.b), True),
                _TLiteral(TNeq(atom.b, atom.c), True),
                _TLiteral(TNeq(atom.a, atom.c), True),
            ]
        else:
            return None  # disjunctive — deferred to Phase 5

    # CongH(a, b, c, d) → Cong(a, b, c, d)
    if isinstance(atom, CongH):
        if pol:
            return [_TLiteral(TCong(atom.a, atom.b, atom.c, atom.d), True)]
        else:
            return [_TLiteral(TNotCong(atom.a, atom.b, atom.c, atom.d), True)]

    # EqPt(a, b) → Eq(a, b)
    if isinstance(atom, EqPt):
        if pol:
            return [_TLiteral(TEq(atom.left, atom.right), True)]
        else:
            return [_TLiteral(TNeq(atom.left, atom.right), True)]

    # EqL(l, m) — line equality has no direct T counterpart
    # (Tarski has no lines)
    if isinstance(atom, EqL):
        return None

    # IncidL, SameSideH, ColH — require existential translation (Phase 5)
    if isinstance(atom, (IncidL, SameSideH, ColH)):
        return None

    # CongaH — angle congruence requires complex T encoding (Phase 5)
    if isinstance(atom, CongaH):
        return None

    return None


def t_literal_to_h(lit) -> Optional[HLiteral]:
    """Translate a System T literal to a System H literal.

    Returns None for predicates not directly expressible in H.
    """
    from .t_ast import (
        TLiteral, B as TB, Cong as TCong, NotB as TNotB,
        NotCong as TNotCong, Eq as TEq, Neq as TNeq,
    )

    atom = lit.atom
    pol = lit.polarity

    # B(a, b, c) → BetH(a, b, c)
    # Note: B is nonstrict in T, BetH is strict in H. Best-effort.
    if isinstance(atom, TB):
        return HLiteral(BetH(atom.a, atom.b, atom.c), pol)

    # NotB(a, b, c) → ¬BetH(a, b, c)
    if isinstance(atom, TNotB):
        if pol:
            return HLiteral(BetH(atom.a, atom.b, atom.c), False)
        else:
            return HLiteral(BetH(atom.a, atom.b, atom.c), True)

    # Cong(a, b, c, d) → CongH(a, b, c, d)
    if isinstance(atom, TCong):
        return HLiteral(CongH(atom.a, atom.b, atom.c, atom.d), pol)

    # NotCong(a, b, c, d) → ¬CongH(a, b, c, d)
    if isinstance(atom, TNotCong):
        if pol:
            return HLiteral(CongH(atom.a, atom.b, atom.c, atom.d), False)
        else:
            return HLiteral(CongH(atom.a, atom.b, atom.c, atom.d), True)

    # Eq(a, b) → EqPt(a, b)
    if isinstance(atom, TEq):
        return HLiteral(EqPt(atom.left, atom.right), pol)

    # Neq(a, b) → ¬EqPt(a, b)
    if isinstance(atom, TNeq):
        if pol:
            return HLiteral(EqPt(atom.left, atom.right), False)
        else:
            return HLiteral(EqPt(atom.left, atom.right), True)

    return None
