"""
matcher.py — Schema matching (unification) and instantiation.

Metavariable conventions:
  - phi, psi, chi: formula-level metavariables (bind to entire formulas)
  - Single uppercase letters (A-Z) and lowercase (l,m,n): term metavars
  - Seg pairs (AB, CD): segment metavar pairs
"""
from __future__ import annotations
from typing import Dict, Optional
from .ast import (
    Formula, Pred, Eq, Neq, Not, And, Or, Iff, Exists, ExistsUnique,
    ExactlyOne, Bottom, ForAll, Seg, formula_eq,
)

Bindings = Dict[str, object]

_FORMULA_METAVARS = frozenset(("phi", "psi", "chi"))


def match_formula(pattern: Formula, concrete: Formula,
                  bindings: Bindings = None) -> Optional[Bindings]:
    if bindings is None:
        bindings = {}
    else:
        bindings = dict(bindings)
    return _match(pattern, concrete, bindings)


def _match(pat, con, b):
    if isinstance(pat, Bottom):
        return b if isinstance(con, Bottom) else None

    if isinstance(pat, Pred) and not pat.args and pat.name in _FORMULA_METAVARS:
        return _bind_formula(pat.name, con, b)

    if isinstance(pat, Eq):
        if not isinstance(con, Eq): return None
        b2 = _bind(pat.left, con.left, b)
        return _bind(pat.right, con.right, b2) if b2 is not None else None

    if isinstance(pat, Neq):
        if not isinstance(con, Neq): return None
        b2 = _bind(pat.left, con.left, b)
        return _bind(pat.right, con.right, b2) if b2 is not None else None

    if isinstance(pat, Not):
        if not isinstance(con, Not): return None
        return _match(pat.inner, con.inner, b)

    if isinstance(pat, And):
        if not isinstance(con, And): return None
        b2 = _match(pat.left, con.left, b)
        return _match(pat.right, con.right, b2) if b2 is not None else None

    if isinstance(pat, Or):
        if not isinstance(con, Or): return None
        b2 = _match(pat.left, con.left, b)
        return _match(pat.right, con.right, b2) if b2 is not None else None

    if isinstance(pat, Iff):
        if not isinstance(con, Iff): return None
        b2 = _match(pat.left, con.left, b)
        return _match(pat.right, con.right, b2) if b2 is not None else None

    if isinstance(pat, Exists):
        if not isinstance(con, Exists): return None
        b2 = _bind(pat.var, con.var, b)
        return _match(pat.body, con.body, b2) if b2 is not None else None

    if isinstance(pat, ExistsUnique):
        if not isinstance(con, ExistsUnique): return None
        b2 = _bind(pat.var, con.var, b)
        return _match(pat.body, con.body, b2) if b2 is not None else None

    if isinstance(pat, ForAll):
        if not isinstance(con, ForAll): return None
        b2 = _bind(pat.var, con.var, b)
        return _match(pat.body, con.body, b2) if b2 is not None else None

    if isinstance(pat, ExactlyOne):
        if not isinstance(con, ExactlyOne): return None
        if len(pat.formulas) != len(con.formulas): return None
        b2 = b
        for pf, cf in zip(pat.formulas, con.formulas):
            b2 = _match(pf, cf, b2)
            if b2 is None: return None
        return b2

    if isinstance(pat, Pred):
        if not isinstance(con, Pred): return None
        if pat.name != con.name: return None
        if len(pat.args) != len(con.args): return None
        b2 = b
        for pa, ca in zip(pat.args, con.args):
            b2 = _bind_arg(pa, ca, b2)
            if b2 is None: return None
        return b2

    return None


def _bind(meta, concrete, b):
    if meta in b:
        return b if b[meta] == concrete else None
    b = dict(b); b[meta] = concrete; return b


def _bind_formula(meta, concrete, b):
    if meta in b:
        return b if formula_eq(b[meta], concrete) else None
    b = dict(b); b[meta] = concrete; return b


def _bind_arg(pa, ca, b):
    if isinstance(pa, Seg) and isinstance(ca, Seg):
        # Try direct match first
        b2 = _bind(pa.p1, ca.p1, b)
        if b2 is not None:
            b3 = _bind(pa.p2, ca.p2, b2)
            if b3 is not None:
                return b3
        # Try reversed match (segments are undirected: AB == BA)
        b2 = _bind(pa.p1, ca.p2, b)
        if b2 is not None:
            b3 = _bind(pa.p2, ca.p1, b2)
            if b3 is not None:
                return b3
        return None
    if isinstance(pa, Pred) and isinstance(ca, Pred):
        return _match(pa, ca, b)
    if isinstance(pa, str) and isinstance(ca, str):
        return _bind(pa, ca, b)
    # Allow a string metavar to bind to a nested Pred (e.g. l -> Line(A,B))
    if isinstance(pa, str) and isinstance(ca, Pred):
        return _bind_formula(pa, ca, b)
    return None


def instantiate(pattern: Formula, bindings: Bindings) -> Formula:
    if isinstance(pattern, Bottom):
        return pattern
    if isinstance(pattern, Pred):
        if not pattern.args and pattern.name in bindings:
            val = bindings[pattern.name]
            if isinstance(val, Formula):
                return val
        new_args = tuple(_inst_arg(a, bindings) for a in pattern.args)
        return Pred(pattern.name, new_args)
    if isinstance(pattern, Eq):
        return Eq(bindings.get(pattern.left, pattern.left),
                  bindings.get(pattern.right, pattern.right))
    if isinstance(pattern, Neq):
        return Neq(bindings.get(pattern.left, pattern.left),
                   bindings.get(pattern.right, pattern.right))
    if isinstance(pattern, Not):
        return Not(instantiate(pattern.inner, bindings))
    if isinstance(pattern, And):
        return And(instantiate(pattern.left, bindings),
                   instantiate(pattern.right, bindings))
    if isinstance(pattern, Or):
        return Or(instantiate(pattern.left, bindings),
                  instantiate(pattern.right, bindings))
    if isinstance(pattern, Iff):
        return Iff(instantiate(pattern.left, bindings),
                   instantiate(pattern.right, bindings))
    if isinstance(pattern, Exists):
        return Exists(bindings.get(pattern.var, pattern.var),
                      instantiate(pattern.body, bindings))
    if isinstance(pattern, ExistsUnique):
        return ExistsUnique(bindings.get(pattern.var, pattern.var),
                            instantiate(pattern.body, bindings))
    if isinstance(pattern, ForAll):
        return ForAll(bindings.get(pattern.var, pattern.var),
                      instantiate(pattern.body, bindings))
    if isinstance(pattern, ExactlyOne):
        return ExactlyOne(tuple(instantiate(f, bindings) for f in pattern.formulas))
    return pattern


def _inst_arg(arg, bindings):
    if isinstance(arg, Seg):
        return Seg(bindings.get(arg.p1, arg.p1), bindings.get(arg.p2, arg.p2))
    if isinstance(arg, Pred):
        return instantiate(arg, bindings)
    if isinstance(arg, str):
        val = bindings.get(arg, arg)
        return val  # may be str or Pred
    return arg
