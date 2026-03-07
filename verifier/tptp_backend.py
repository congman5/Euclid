"""
tptp_backend.py — TPTP FOF encoding of System E axioms and proof obligations.

Encodes the diagrammatic, metric, and transfer axioms from Avigad, Dean,
Mumma (2009) §3.4–3.6 in TPTP first-order format (FOF) suitable for
E-prover, SPASS, and Vampire.

The paper (§6) notes:
  "We entered our betweenness, same-side, and Pasch axioms in the
   standard TPTP format... The consequences were verified instantaneously."

Phase 8.2 of the implementation plan.
"""
from __future__ import annotations

from typing import Dict, List, Optional, Tuple, Union

from .e_ast import (
    AngleTerm,
    AreaTerm,
    Atom,
    Between,
    Center,
    Clause,
    Equals,
    Inside,
    Intersects,
    LessThan,
    Literal,
    MagAdd,
    On,
    RightAngle,
    SameSide,
    SegmentTerm,
    Sort,
    Term,
    ZeroMag,
)


# ═══════════════════════════════════════════════════════════════════════
# TPTP NAME ENCODING
# ═══════════════════════════════════════════════════════════════════════

def _tptp_var(name: str) -> str:
    """Encode a variable name as a TPTP variable (uppercase start)."""
    sane = name.replace("'", "_p").replace("α", "Alpha").replace(
        "β", "Beta").replace("γ", "Gamma")
    if sane and sane[0].islower():
        return sane[0].upper() + sane[1:]
    return sane


def _tptp_const(name: str) -> str:
    """Encode a constant name (lowercase start in TPTP)."""
    sane = name.replace("'", "_p").replace("α", "alpha").replace(
        "β", "beta").replace("γ", "gamma")
    if sane and sane[0].isupper():
        return sane[0].lower() + sane[1:]
    return sane


# ═══════════════════════════════════════════════════════════════════════
# TERM → TPTP ENCODING
# ═══════════════════════════════════════════════════════════════════════

def _tptp_term(t: Union[str, Term], as_var: bool = True) -> str:
    """Encode a term in TPTP syntax."""
    if isinstance(t, str):
        return _tptp_var(t) if as_var else _tptp_const(t)
    if isinstance(t, SegmentTerm):
        return f"seg({_tptp_var(t.p1)},{_tptp_var(t.p2)})"
    if isinstance(t, AngleTerm):
        return f"ang({_tptp_var(t.p1)},{_tptp_var(t.p2)},{_tptp_var(t.p3)})"
    if isinstance(t, AreaTerm):
        return f"tri({_tptp_var(t.p1)},{_tptp_var(t.p2)},{_tptp_var(t.p3)})"
    if isinstance(t, MagAdd):
        return f"mag_add({_tptp_term(t.left)},{_tptp_term(t.right)})"
    if isinstance(t, ZeroMag):
        return "zero_mag"
    if isinstance(t, RightAngle):
        return "right_angle"
    return str(t)


# ═══════════════════════════════════════════════════════════════════════
# ATOM → TPTP ENCODING
# ═══════════════════════════════════════════════════════════════════════

def encode_atom_tptp(atom: Atom) -> str:
    """Encode a single E-system atom as a TPTP formula."""
    if isinstance(atom, On):
        return f"on_pl({_tptp_var(atom.point)},{_tptp_var(atom.obj)})"
    if isinstance(atom, Between):
        return f"between({_tptp_var(atom.a)},{_tptp_var(atom.b)},{_tptp_var(atom.c)})"
    if isinstance(atom, SameSide):
        return f"same_side({_tptp_var(atom.a)},{_tptp_var(atom.b)},{_tptp_var(atom.line)})"
    if isinstance(atom, Center):
        return f"center({_tptp_var(atom.point)},{_tptp_var(atom.circle)})"
    if isinstance(atom, Inside):
        return f"inside({_tptp_var(atom.point)},{_tptp_var(atom.circle)})"
    if isinstance(atom, Intersects):
        return f"intersects({_tptp_var(atom.obj1)},{_tptp_var(atom.obj2)})"
    if isinstance(atom, Equals):
        return f"eq({_tptp_term(atom.left)},{_tptp_term(atom.right)})"
    if isinstance(atom, LessThan):
        return f"lt({_tptp_term(atom.left)},{_tptp_term(atom.right)})"
    raise ValueError(f"Unknown atom type: {type(atom).__name__}")


def encode_literal_tptp(lit: Literal) -> str:
    """Encode a literal in TPTP syntax."""
    inner = encode_atom_tptp(lit.atom)
    if lit.polarity:
        return inner
    return f"~{inner}"


# ═══════════════════════════════════════════════════════════════════════
# CLAUSE → TPTP FOF
# ═══════════════════════════════════════════════════════════════════════

def _collect_tptp_vars(clause: Clause) -> List[str]:
    """Collect all variable names from a clause for universal quantification."""
    from .e_ast import literal_vars
    all_vars: set = set()
    for lit in clause.literals:
        all_vars.update(_tptp_var(v) for v in literal_vars(lit))
    return sorted(all_vars)


def encode_clause_tptp(clause: Clause, name: str) -> str:
    """Encode a clause as a TPTP FOF axiom."""
    lits = list(clause.literals)
    if len(lits) == 0:
        return f"fof({name}, axiom, $false)."
    if len(lits) == 1:
        body = encode_literal_tptp(lits[0])
    else:
        parts = " | ".join(encode_literal_tptp(l) for l in lits)
        body = f"({parts})"

    vs = _collect_tptp_vars(clause)
    if vs:
        var_list = ",".join(vs)
        return f"fof({name}, axiom, ![{var_list}]: {body})."
    return f"fof({name}, axiom, {body})."


# ═══════════════════════════════════════════════════════════════════════
# PUBLIC API
# ═══════════════════════════════════════════════════════════════════════

def encode_axioms_tptp() -> str:
    """Encode all System E axioms as a TPTP FOF script.

    Returns the full script with all axioms as fof() declarations.
    """
    from .e_axioms import ALL_AXIOMS

    lines = [
        "% System E axioms (Avigad, Dean, Mumma 2009)",
        "% §3.4 Diagrammatic + §3.5 Metric + §3.6 Transfer",
        "%",
    ]
    for i, clause in enumerate(ALL_AXIOMS):
        lines.append(encode_clause_tptp(clause, f"axiom_{i + 1}"))
    lines.append("")
    return "\n".join(lines)


def encode_query_tptp(
    known: List[Literal],
    query: Literal,
    axioms: bool = True,
) -> str:
    """Encode a proof obligation in TPTP FOF format.

    The known facts are asserted as axioms, and the query is asserted
    as a conjecture. A theorem prover should report "Theorem" if the
    query follows from the axioms + known facts.

    Args:
        known: List of literals known to hold.
        query: The literal to check.
        axioms: If True, include all System E axioms.

    Returns:
        Complete TPTP FOF script as a string.
    """
    lines = []

    if axioms:
        lines.append(encode_axioms_tptp())

    # Assert known facts as hypotheses
    for i, lit in enumerate(known):
        formula = encode_literal_tptp(lit)
        lines.append(f"fof(known_{i + 1}, hypothesis, {formula}).")

    # Assert query as conjecture
    lines.append("")
    lines.append(f"fof(query, conjecture, {encode_literal_tptp(query)}).")
    lines.append("")
    return "\n".join(lines)
