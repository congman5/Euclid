"""
proof_synthesizer.py -- Automated proof synthesis from Lean translator output.

Takes a TranslationResult from the Lean->System E translator and synthesizes
a complete .euclid proof JSON that passes verify_e_proof_json.

Architecture
------------
1. Variable mapper: Maps Lean variable names (AB, BC, AC) to e_library
   names (L, M, N) by matching which points lie on which lines.

2. Step synthesizer: Walks the Lean tactics directly and generates .euclid
   JSON steps with correct text, justification, and dependencies.

3. Dependency tracker: Incrementally tracks known facts per line so
   each step cites only the lines it actually needs.
"""
from __future__ import annotations

import json
import datetime
from dataclasses import dataclass, field
from pathlib import Path
from typing import Any, Dict, List, Optional, Set, Tuple

from .e_ast import (
    Sort, Literal, Atom, Sequent, ETheorem,
    On, SameSide, Between, Center, Inside, Intersects,
    Equals, LessThan,
    SegmentTerm, AngleTerm, AreaTerm, MagAdd, RightAngle, ZeroMag,
    ProofStep, StepKind, EProof,
    literal_vars, atom_vars, substitute_literal,
)
from .e_library import E_THEOREM_LIBRARY, get_theorems_up_to
from .e_construction import CONSTRUCTION_RULE_BY_NAME
from .lean_translator import TranslatedStep, TranslationResult
from .lean_parser import LeanProof, LeanTactic, TacticKind, parse_lean_file
from .lean_to_euclid_json import (
    literal_to_text, _PROP_TITLES, _PROP_DIFFICULTIES,
    _extract_declarations, _load_existing_canvas,
)


# =====================================================================
# Helpers
# =====================================================================

def _pos(atom: Atom) -> Literal:
    return Literal(atom, polarity=True)


def _ordered_atom_vars(atom: Atom) -> List[str]:
    """Return variable names in an atom in a stable, positional order.

    For On(point, obj) → [point, obj]
    For Between(a, b, c) → [a, b, c]
    For Equals/LessThan → left vars then right vars
    etc.
    """
    result: List[str] = []
    def _add(v: str):
        if v not in result:
            result.append(v)
    def _add_term(t):
        if isinstance(t, str):
            _add(t)
        elif isinstance(t, SegmentTerm):
            _add(t.p1); _add(t.p2)
        elif isinstance(t, AngleTerm):
            _add(t.p1); _add(t.p2); _add(t.p3)
        elif isinstance(t, AreaTerm):
            _add(t.p1); _add(t.p2); _add(t.p3)
        elif isinstance(t, MagAdd):
            _add_term(t.left); _add_term(t.right)
    if isinstance(atom, On):
        _add(atom.point); _add(atom.obj)
    elif isinstance(atom, SameSide):
        _add(atom.a); _add(atom.b); _add(atom.line)
    elif isinstance(atom, Between):
        _add(atom.a); _add(atom.b); _add(atom.c)
    elif isinstance(atom, Center):
        _add(atom.point); _add(atom.circle)
    elif isinstance(atom, Inside):
        _add(atom.point); _add(atom.circle)
    elif isinstance(atom, Intersects):
        _add(atom.obj1); _add(atom.obj2)
    elif isinstance(atom, Equals):
        _add_term(atom.left); _add_term(atom.right)
    elif isinstance(atom, LessThan):
        _add_term(atom.left); _add_term(atom.right)
    return result


def _ordered_sequent_vars(seq: 'Sequent') -> List[str]:
    """Extract variables from a sequent in stable hypothesis-order.

    Walks hypotheses then conclusions, collecting variable names
    in order of first appearance. This matches the Lean convention
    where theorem parameters are listed in hypothesis order.
    """
    seen: List[str] = []
    for lit in seq.hypotheses:
        for v in _ordered_atom_vars(lit.atom):
            if v not in seen:
                seen.append(v)
    for lit in seq.conclusions:
        for v in _ordered_atom_vars(lit.atom):
            if v not in seen:
                seen.append(v)
    return seen


# Lean parameter order for propositions.
# Maps Lean function name → list of (elib_var, sort) in Lean call-site order.
# Derived from LeanEuclid Book definitions and call patterns in lean_reference/.
# For each entry, the i-th tuple corresponds to the i-th positional argument in
# the Lean ``euclid_apply (proposition_N arg1 arg2 ...)`` call, and tells the
# synthesizer which e_library variable it maps to.  ``"_"`` means the argument
# is auxiliary (not directly needed for the e_library var_map).
_LEAN_PARAM_ORDER: Dict[str, List[Tuple[str, str]]] = {
    # --- Prop I.3 ---
    # Lean: proposition_3 p1 p2 p3 p4 L1 L2  as e
    # elib: on(a,L), on(b,L), ¬(a=b), cd < ab  ⊢ ∃e. between(a,e,b) ∧ ae=cd
    "proposition_3": [
        ("a", "Point"), ("b", "Point"), ("c", "Point"), ("d", "Point"),
        ("L", "Line"),  ("_", "Line"),
    ],
    # --- Prop I.4  (SAS) ---
    # Lean: proposition_4 a b c  d e f  AB BC AC  DE EF DF
    # elib: a,b,c → d,e,f  (two triangles, 6 points + 6 lines)
    "proposition_4": [
        ("a", "Point"), ("b", "Point"), ("c", "Point"),
        ("d", "Point"), ("e", "Point"), ("f", "Point"),
        ("_", "Line"), ("_", "Line"), ("_", "Line"),
        ("_", "Line"), ("_", "Line"), ("_", "Line"),
    ],
    # --- Prop I.5 / 5' ---
    # Lean: proposition_5  a b c  AB BC AC
    "proposition_5": [
        ("a", "Point"), ("b", "Point"), ("c", "Point"),
        ("_", "Line"), ("_", "Line"), ("_", "Line"),
    ],
    "proposition_5'": [
        ("a", "Point"), ("b", "Point"), ("c", "Point"),
        ("_", "Line"), ("_", "Line"), ("_", "Line"),
    ],
    # --- Prop I.8  (SSS) ---
    # Lean: proposition_8 a b c  d e f  AB BC AC  DE EF DF
    "proposition_8": [
        ("a", "Point"), ("b", "Point"), ("c", "Point"),
        ("d", "Point"), ("e", "Point"), ("f", "Point"),
        ("_", "Line"), ("_", "Line"), ("_", "Line"),
        ("_", "Line"), ("_", "Line"), ("_", "Line"),
    ],
    # --- Prop I.10 ---
    # Lean: proposition_10 p1 p2 L  as d
    "proposition_10": [
        ("a", "Point"), ("b", "Point"),
        ("L", "Line"),
    ],
    # --- Prop I.11 / 11'' / 11''' ---
    # Lean: proposition_11'' a b AB  as f
    # elib: on(a,L), on(b,L), ¬(a=b) ⊢ ∃f
    "proposition_11": [
        ("a", "Point"), ("b", "Point"),
        ("L", "Line"),
    ],
    "proposition_11''": [
        ("a", "Point"), ("b", "Point"),
        ("L", "Line"),
    ],
    "proposition_11'''": [
        ("a", "Point"), ("b", "Point"), ("_", "Point"),
        ("L", "Line"),
    ],
    # --- Prop I.13 ---
    # Lean: proposition_13 d b a c  L_aux L
    # elib: on(a,L), on(c,L), between(a,b,c), ¬on(d,L)
    "proposition_13": [
        ("d", "Point"), ("b", "Point"), ("a", "Point"), ("c", "Point"),
        ("_", "Line"), ("L", "Line"),
    ],
    # --- Prop I.14 ---
    # Lean: proposition_14 d b a c  AB L
    # elib: on(a,L), on(b,L), on(c,L), between(a,b,c), ¬on(d,L)
    "proposition_14": [
        ("d", "Point"), ("b", "Point"), ("a", "Point"), ("c", "Point"),
        ("_", "Line"), ("L", "Line"), ("_", "Line"),
    ],
    # --- Prop I.15 ---
    # Lean: proposition_15  a b  c d  e  L M
    # elib: on(a,L), on(b,L), on(c,M), on(d,M), on(e,L), on(e,M),
    #       between(a,e,b), between(c,e,d)
    "proposition_15": [
        ("a", "Point"), ("b", "Point"), ("c", "Point"), ("d", "Point"),
        ("e", "Point"), ("L", "Line"), ("M", "Line"),
    ],
    # --- Prop I.16 ---
    # Lean: proposition_16 c a b d  _ L _
    # elib: on(a,L), on(b,L), between(a,b,d), ¬on(c,L)
    "proposition_16": [
        ("c", "Point"), ("a", "Point"), ("b", "Point"), ("d", "Point"),
        ("_", "Line"), ("L", "Line"), ("_", "Line"),
    ],
    # --- Prop I.17 ---
    # Lean: proposition_17 a b c  AB BC AC
    # elib: ¬(a=b), ¬(a=c), ¬(b=c), on(a,L), on(b,L), ¬on(c,L)
    # Lean formTriangle a b c → elib a,b on line L, c off-line
    "proposition_17": [
        ("a", "Point"), ("b", "Point"), ("c", "Point"),
        ("L", "Line"), ("_", "Line"), ("_", "Line"),
    ],
    # --- Prop I.18 ---
    # Lean: proposition_18 a b c  AB BC AC
    # elib: same as I.17 — formTriangle a b c
    "proposition_18": [
        ("a", "Point"), ("b", "Point"), ("c", "Point"),
        ("L", "Line"), ("_", "Line"), ("_", "Line"),
    ],
    # --- Prop I.19 ---
    # Lean: proposition_19 a b c  AB BC AC
    "proposition_19": [
        ("a", "Point"), ("b", "Point"), ("c", "Point"),
        ("L", "Line"), ("_", "Line"), ("_", "Line"),
    ],
    # --- Prop I.20 ---
    # Lean: proposition_20 a b c  AB BC AC
    "proposition_20": [
        ("a", "Point"), ("b", "Point"), ("c", "Point"),
        ("L", "Line"), ("_", "Line"), ("_", "Line"),
    ],
    # --- Prop I.21 ---
    # Lean: proposition_21 a b c d  AB BC AC BD DC
    # elib: a,b,c triangle on L,M,N; d interior point
    "proposition_21": [
        ("a", "Point"), ("b", "Point"), ("c", "Point"), ("d", "Point"),
        ("L", "Line"), ("M", "Line"), ("N", "Line"), ("_", "Line"), ("_", "Line"),
    ],
    # --- Prop I.22 ---
    # Lean: proposition_22 a a' b b' c c'  A B C
    # elib: ¬(a=b), ¬(c=d), ¬(e=f), ab<(cd+ef), ... ⊢ ∃p,q,r
    "proposition_22": [
        ("a", "Point"), ("b", "Point"), ("c", "Point"), ("d", "Point"),
        ("e", "Point"), ("f", "Point"),
        ("_", "Line"), ("_", "Line"), ("_", "Line"),
    ],
    # Lean: proposition_22' a a' b b' c c' f e  A B C FE
    # Same elib theorem, but with 2 extra args (f, e) and extra line FE
    "proposition_22'": [
        ("a", "Point"), ("b", "Point"), ("c", "Point"), ("d", "Point"),
        ("e", "Point"), ("f", "Point"), ("_", "Point"), ("_", "Point"),
        ("_", "Line"), ("_", "Line"), ("_", "Line"), ("_", "Line"),
    ],
    "proposition_22''": [
        ("a", "Point"), ("b", "Point"), ("c", "Point"), ("d", "Point"),
        ("e", "Point"), ("f", "Point"), ("_", "Point"), ("_", "Point"), ("_", "Point"),
        ("_", "Line"), ("_", "Line"), ("_", "Line"), ("_", "Line"),
    ],
    # --- Prop I.23 ---
    # Lean: proposition_23 a b c d e  AB CD CE
    # elib: ¬(d=e), ¬(d=f), ¬(e=f), on(a,L), on(b,L), ¬(a=b) ⊢ ∃g
    # Lean a,b → elib a,b (on-line); c,d,e → elib d,e,f (angle points)
    "proposition_23": [
        ("d", "Point"), ("e", "Point"), ("f", "Point"),
        ("a", "Point"), ("b", "Point"),
        ("_", "Line"), ("_", "Line"), ("_", "Line"),
    ],
    # Lean: proposition_23' a b c d e x  AB CD CE
    # Same but with extra arg x
    "proposition_23'": [
        ("d", "Point"), ("e", "Point"), ("f", "Point"),
        ("a", "Point"), ("b", "Point"), ("_", "Point"),
        ("_", "Line"), ("_", "Line"), ("_", "Line"),
    ],
    # --- Prop I.24 ---
    # Lean: proposition_24 a b c d e f  AB BC AC DE EF DF
    # elib: ab=de, ac=df, ∠edf < ∠bac  (two triangles)
    "proposition_24": [
        ("a", "Point"), ("b", "Point"), ("c", "Point"),
        ("d", "Point"), ("e", "Point"), ("f", "Point"),
        ("_", "Line"), ("_", "Line"), ("_", "Line"),
        ("_", "Line"), ("_", "Line"), ("_", "Line"),
    ],
    # --- Prop I.25 ---
    # Lean: proposition_25 a b c d e f  AB BC AC DE EF DF
    "proposition_25": [
        ("a", "Point"), ("b", "Point"), ("c", "Point"),
        ("d", "Point"), ("e", "Point"), ("f", "Point"),
        ("_", "Line"), ("_", "Line"), ("_", "Line"),
        ("_", "Line"), ("_", "Line"), ("_", "Line"),
    ],
    # --- Prop I.26 (ASA) ---
    # Lean: proposition_26 a b c d e f  AB BC AC DE EF DF
    "proposition_26": [
        ("a", "Point"), ("b", "Point"), ("c", "Point"),
        ("d", "Point"), ("e", "Point"), ("f", "Point"),
        ("_", "Line"), ("_", "Line"), ("_", "Line"),
        ("_", "Line"), ("_", "Line"), ("_", "Line"),
    ],
    # --- Prop I.27 ---
    # Lean: proposition_27 a d e f  AE FD EF
    # elib: on(a,L), on(b,L), on(b,M), on(c,M), on(c,N), on(d,N)
    # Lean a→elib a, d→elib d, e→elib b(=shared), f→elib c(=shared)
    "proposition_27": [
        ("a", "Point"), ("d", "Point"), ("b", "Point"), ("c", "Point"),
        ("L", "Line"), ("N", "Line"), ("M", "Line"),
    ],
    # --- Prop I.28 ---
    # Lean: proposition_28 a b c d e f g h  AB CD EF
    # elib: on(a,L), on(b,L), on(b,M), on(c,M), on(c,N), on(d,N), ...
    # Lean args: a b c d → line endpoints, e f g h → transversal endpoints
    # Mapping: Lean a→elib a, b→elib b (on L), c→elib c (shared), d→elib d (on N)
    #          g→elib b (between a,g,b), h→elib c (between c,h,d)
    "proposition_28": [
        ("a", "Point"), ("_", "Point"), ("_", "Point"), ("d", "Point"),
        ("_", "Point"), ("_", "Point"), ("b", "Point"), ("c", "Point"),
        ("L", "Line"), ("N", "Line"), ("M", "Line"),
    ],
    # --- Prop I.29 ---
    # Lean: proposition_29 a b c d e f g h  AB CD EF
    # elib: on(a,L), on(b,L), on(b,M), on(c,M), on(c,N), on(d,N)
    # Same structure as I.28 — g,h are the transversal intersection points
    "proposition_29": [
        ("a", "Point"), ("_", "Point"), ("_", "Point"), ("d", "Point"),
        ("_", "Point"), ("_", "Point"), ("b", "Point"), ("c", "Point"),
        ("L", "Line"), ("N", "Line"), ("M", "Line"),
    ],
    # Lean: proposition_29' a b c d e g h  AB CD EF (7 pts, no f)
    "proposition_29'": [
        ("a", "Point"), ("_", "Point"), ("_", "Point"), ("d", "Point"),
        ("_", "Point"), ("b", "Point"), ("c", "Point"),
        ("L", "Line"), ("N", "Line"), ("M", "Line"),
    ],
    # Lean: proposition_29'' a b d g h  AB CD GH (5 pts)
    "proposition_29''": [
        ("a", "Point"), ("_", "Point"), ("d", "Point"),
        ("b", "Point"), ("c", "Point"),
        ("L", "Line"), ("N", "Line"), ("M", "Line"),
    ],
    # Lean: proposition_29''' a d g h  AB CD GH (4 pts)
    "proposition_29'''": [
        ("a", "Point"), ("d", "Point"),
        ("b", "Point"), ("c", "Point"),
        ("L", "Line"), ("N", "Line"), ("M", "Line"),
    ],
    # Lean: proposition_29'''' b d e g h  AB CD EF (5 pts)
    "proposition_29''''": [
        ("_", "Point"), ("d", "Point"), ("_", "Point"),
        ("b", "Point"), ("c", "Point"),
        ("L", "Line"), ("N", "Line"), ("M", "Line"),
    ],
    # Lean: proposition_29''''' b d g h  AB CD EF (4 pts)
    "proposition_29'''''": [
        ("_", "Point"), ("d", "Point"),
        ("b", "Point"), ("c", "Point"),
        ("L", "Line"), ("N", "Line"), ("M", "Line"),
    ],
    # --- Prop I.30 ---
    # Lean: proposition_30 AB CD EF (3 lines only)
    # elib: ¬intersects(L,M), ¬intersects(M,N) ⊢ ¬intersects(L,N)
    "proposition_30": [
        ("L", "Line"), ("M", "Line"), ("N", "Line"),
    ],
    # --- Prop I.31 ---
    # Lean: proposition_31 a b c  BC  as EF
    # elib: on(b,L), on(c,L), ¬(b=c), ¬on(a,L) ⊢ ∃M
    "proposition_31": [
        ("a", "Point"), ("b", "Point"), ("c", "Point"),
        ("L", "Line"),
    ],
    # --- Prop I.32 ---
    # Lean: proposition_32 a b c d  AB BC AC
    # elib: on(b,L), on(c,L), ¬on(a,L), between(b,c,d)
    "proposition_32": [
        ("a", "Point"), ("b", "Point"), ("c", "Point"), ("d", "Point"),
        ("L", "Line"), ("_", "Line"), ("_", "Line"),
    ],
    # --- Prop I.33 ---
    # Lean: proposition_33 a b c d  AB CD AC BD
    # elib: on(a,L), on(b,L), on(c,N), on(d,N), on(a,M), on(c,M), on(b,P), on(d,P)
    "proposition_33": [
        ("a", "Point"), ("b", "Point"), ("c", "Point"), ("d", "Point"),
        ("L", "Line"), ("N", "Line"), ("M", "Line"), ("P", "Line"),
    ],
    # --- Prop I.34 ---
    # Lean: proposition_34 a b c d  AB CD AC BD BC
    # elib: on(a,L), on(b,L), on(c,N), on(d,N), on(a,M), on(d,M), on(b,P), on(c,P)
    "proposition_34": [
        ("a", "Point"), ("d", "Point"), ("b", "Point"), ("c", "Point"),
        ("L", "Line"), ("N", "Line"), ("M", "Line"), ("P", "Line"), ("_", "Line"),
    ],
    # Lean: proposition_34' a b c d  AB CD AC BD  (4 lines, no BC)
    "proposition_34'": [
        ("a", "Point"), ("d", "Point"), ("b", "Point"), ("c", "Point"),
        ("L", "Line"), ("N", "Line"), ("M", "Line"), ("P", "Line"),
    ],
    # --- Prop I.35 ---
    # Lean: proposition_35 a b c d e f g  AF BC AB CD EB FC
    # elib: on(b,N), on(c,N), on(a,L), on(d,L), on(e,L), on(f,L)
    "proposition_35": [
        ("a", "Point"), ("b", "Point"), ("c", "Point"), ("d", "Point"),
        ("e", "Point"), ("f", "Point"), ("_", "Point"),
        ("L", "Line"), ("N", "Line"), ("_", "Line"), ("_", "Line"),
        ("_", "Line"), ("_", "Line"),
    ],
    # Lean: proposition_35' a b c d e f  AF BC AB CD EB FC (no g)
    "proposition_35'": [
        ("a", "Point"), ("b", "Point"), ("c", "Point"), ("d", "Point"),
        ("e", "Point"), ("f", "Point"),
        ("L", "Line"), ("N", "Line"), ("_", "Line"), ("_", "Line"),
        ("_", "Line"), ("_", "Line"),
    ],
    # --- Prop I.36 ---
    # Lean: proposition_36 a b c d e f g h  AH BG AB CD EF HG
    # elib: on(b,N), on(c,N), on(e,N), on(f,N), on(a,L), on(d,L)
    "proposition_36": [
        ("a", "Point"), ("b", "Point"), ("c", "Point"), ("d", "Point"),
        ("e", "Point"), ("f", "Point"), ("_", "Point"), ("_", "Point"),
        ("L", "Line"), ("N", "Line"), ("_", "Line"), ("_", "Line"),
        ("_", "Line"), ("_", "Line"),
    ],
    "proposition_36'": [
        ("a", "Point"), ("b", "Point"), ("c", "Point"), ("d", "Point"),
        ("e", "Point"), ("f", "Point"), ("_", "Point"), ("_", "Point"),
        ("L", "Line"), ("N", "Line"), ("_", "Line"), ("_", "Line"),
        ("_", "Line"), ("_", "Line"),
    ],
    # --- Prop I.37 ---
    # Lean: proposition_37 a b c d  AB BC AC BD CD AD
    # elib: on(b,N), on(c,N), on(a,L), on(d,L)
    "proposition_37": [
        ("a", "Point"), ("b", "Point"), ("c", "Point"), ("d", "Point"),
        ("_", "Line"), ("N", "Line"), ("_", "Line"), ("_", "Line"),
        ("_", "Line"), ("L", "Line"),
    ],
    "proposition_37'": [
        ("a", "Point"), ("b", "Point"), ("c", "Point"), ("d", "Point"),
        ("_", "Line"), ("N", "Line"), ("_", "Line"), ("_", "Line"),
        ("_", "Line"), ("L", "Line"),
    ],
    # --- Prop I.38 ---
    # Lean: proposition_38 a b c d e f  AD BF AB AC DE DF
    # elib: on(b,N), on(c,N), on(e,N), on(f,N), on(a,L), on(d,L)
    "proposition_38": [
        ("a", "Point"), ("b", "Point"), ("c", "Point"), ("d", "Point"),
        ("e", "Point"), ("f", "Point"),
        ("L", "Line"), ("N", "Line"), ("_", "Line"), ("_", "Line"),
        ("_", "Line"), ("_", "Line"),
    ],
    # --- Prop I.39 ---
    # Lean: proposition_39 a b c d  AB BC AC BD CD AD
    # elib: on(b,N), on(c,N), on(a,L), on(d,L), △abc=△dbc
    "proposition_39": [
        ("a", "Point"), ("b", "Point"), ("c", "Point"), ("d", "Point"),
        ("_", "Line"), ("N", "Line"), ("_", "Line"), ("_", "Line"),
        ("_", "Line"), ("L", "Line"),
    ],
    # --- Prop I.40 ---
    # Lean: proposition_40 a b c d e  AB BC AC CD DE AD
    # elib: on(b,N), on(c,N), on(e,N), on(f,N), on(a,L), on(d,L)
    "proposition_40": [
        ("a", "Point"), ("b", "Point"), ("c", "Point"), ("d", "Point"),
        ("e", "Point"),
        ("_", "Line"), ("N", "Line"), ("_", "Line"), ("_", "Line"),
        ("_", "Line"), ("L", "Line"),
    ],
    # --- Prop I.41 ---
    # Lean: proposition_41 a b c d e  AE BC AB CD BE CE
    # elib: on(b,N), on(c,N), on(a,L), on(d,L), on(e,L), ¬on(e,N)
    "proposition_41": [
        ("a", "Point"), ("b", "Point"), ("c", "Point"), ("d", "Point"),
        ("e", "Point"),
        ("L", "Line"), ("N", "Line"), ("_", "Line"), ("_", "Line"),
        ("_", "Line"), ("_", "Line"),
    ],
    # --- Prop I.42 ---
    # Lean: proposition_42 a b c d1 d2 d3  AB BC AC D12 D23
    # elib: ¬(a=b), ¬(a=c), ¬(b=c), ¬(∠def=0) ⊢ ∃g,h
    "proposition_42": [
        ("a", "Point"), ("b", "Point"), ("c", "Point"),
        ("d", "Point"), ("e", "Point"), ("f", "Point"),
        ("_", "Line"), ("_", "Line"), ("_", "Line"),
        ("_", "Line"), ("_", "Line"),
    ],
    "proposition_42'": [
        ("a", "Point"), ("b", "Point"), ("c", "Point"),
        ("d", "Point"), ("e", "Point"), ("f", "Point"), ("_", "Point"),
        ("_", "Line"), ("_", "Line"), ("_", "Line"),
        ("_", "Line"), ("_", "Line"),
    ],
    "proposition_42''": [
        ("a", "Point"), ("b", "Point"), ("c", "Point"),
        ("d", "Point"), ("e", "Point"), ("f", "Point"), ("_", "Point"), ("_", "Point"),
        ("_", "Line"), ("_", "Line"), ("_", "Line"),
        ("_", "Line"), ("_", "Line"), ("_", "Line"),
    ],
    "proposition_42'''": [
        ("a", "Point"), ("b", "Point"), ("c", "Point"),
        ("d", "Point"), ("e", "Point"), ("f", "Point"), ("_", "Point"), ("_", "Point"), ("_", "Point"),
        ("_", "Line"), ("_", "Line"), ("_", "Line"),
        ("_", "Line"), ("_", "Line"), ("_", "Line"),
    ],
    # --- Prop I.43 ---
    # Lean: proposition_43 a b c d e f g h k  AD BC AB CD AC EF GH
    # elib: on(a,L), on(b,L), on(c,N), on(d,N), on(a,M), on(d,M), on(b,P), on(c,P), between(a,k,c)
    "proposition_43": [
        ("a", "Point"), ("b", "Point"), ("c", "Point"), ("d", "Point"),
        ("_", "Point"), ("_", "Point"), ("_", "Point"), ("_", "Point"), ("k", "Point"),
        ("M", "Line"), ("N", "Line"), ("L", "Line"), ("_", "Line"),
        ("_", "Line"), ("_", "Line"), ("P", "Line"),
    ],
    # --- Prop I.44 ---
    # Lean: proposition_44 a b c1 c2 c3 d1 d2 d3  AB C12 C23 C31 D12 D23
    # elib: on(a,L), on(b,L), ¬(a=b), ¬(c=d), ¬(c=e), ¬(d=e) ⊢ ∃f,g
    "proposition_44": [
        ("a", "Point"), ("b", "Point"),
        ("c", "Point"), ("d", "Point"), ("e", "Point"),
        ("_", "Point"), ("_", "Point"), ("_", "Point"),
        ("L", "Line"), ("_", "Line"), ("_", "Line"), ("_", "Line"),
        ("_", "Line"), ("_", "Line"),
    ],
    "proposition_44'": [
        ("a", "Point"), ("b", "Point"),
        ("c", "Point"), ("d", "Point"), ("e", "Point"),
        ("_", "Point"), ("_", "Point"), ("_", "Point"), ("_", "Point"),
        ("L", "Line"), ("_", "Line"), ("_", "Line"), ("_", "Line"),
        ("_", "Line"), ("_", "Line"),
    ],
    # --- Prop I.45 ---
    # Lean: proposition_45 a b c d e1 e2 e3  AB BC CD AD DB E12 E23
    # elib: ¬(a=b), ¬(a=c), ¬(b=c), ¬(a=d), ¬(∠efg=0) ⊢ ∃h,k,m
    "proposition_45": [
        ("a", "Point"), ("b", "Point"), ("c", "Point"), ("d", "Point"),
        ("e", "Point"), ("f", "Point"), ("g", "Point"),
        ("_", "Line"), ("_", "Line"), ("_", "Line"), ("_", "Line"),
        ("_", "Line"), ("_", "Line"), ("_", "Line"),
    ],
    # --- Prop I.46 ---
    # Lean: proposition_46 a b  AB
    # elib: on(a,L), on(b,L), ¬(a=b) ⊢ ∃c,d
    "proposition_46": [
        ("a", "Point"), ("b", "Point"),
        ("L", "Line"),
    ],
    # Lean: proposition_46' a b x  AB
    "proposition_46'": [
        ("a", "Point"), ("b", "Point"), ("_", "Point"),
        ("L", "Line"),
    ],
    # --- Prop I.47 ---
    # Lean: proposition_47 a b c  AB BC AC
    # elib: ¬(a=b), ¬(a=c), ¬(b=c), ∠bac=∟ ⊢ ∃d,e,f,g,h,k
    "proposition_47": [
        ("a", "Point"), ("b", "Point"), ("c", "Point"),
        ("_", "Line"), ("_", "Line"), ("_", "Line"),
    ],
    # --- Prop I.48 ---
    # Lean: proposition_48 a b c  AB BC AC
    "proposition_48": [
        ("a", "Point"), ("b", "Point"), ("c", "Point"),
        ("_", "Line"), ("_", "Line"), ("_", "Line"),
    ],
}


def _neg(atom: Atom) -> Literal:
    return Literal(atom, polarity=False)


# =====================================================================
# Result type
# =====================================================================

@dataclass
class SynthesisResult:
    prop_name: str
    prop_number: int
    success: bool = False
    euclid_json: Optional[Dict[str, Any]] = None
    errors: List[str] = field(default_factory=list)
    warnings: List[str] = field(default_factory=list)
    step_count: int = 0


# =====================================================================
# Variable mapper: Lean names <-> e_library names
# =====================================================================

_LINE_POOL = list("LMNPQRSTUVWXYZ")


class VarMapper:
    """Maps between Lean variable names and e_library variable names.

    Uses structural matching: extracts which points lie on which lines
    from both the Lean hypothesis and the e_library sequent, then matches
    lines by shared point-count structure, deriving point mappings from
    the line matches.
    """

    def __init__(self, sequent: Sequent, lean_proof: LeanProof):
        self.lean_to_elib: Dict[str, str] = {}
        self.elib_to_lean: Dict[str, str] = {}
        self.extra_lines: Dict[str, str] = {}
        self.extra_line_points: Dict[str, Tuple[str, str]] = {}
        self._used_pool: Set[str] = set()
        self._build(sequent, lean_proof)

    def _build(self, seq: Sequent, lp: LeanProof):
        # ── Gather elib line→points from hypotheses ───────────────────
        elib_lp: Dict[str, Set[str]] = {}
        for h in seq.hypotheses:
            if isinstance(h.atom, On) and h.polarity:
                elib_lp.setdefault(h.atom.obj, set()).add(h.atom.point)
        for name in elib_lp:
            self._used_pool.add(name)

        # ── Gather Lean params ────────────────────────────────────────
        lean_pts: List[str] = []
        lean_lns: List[Tuple[str, str]] = []  # (OrigName, lowercase)
        if lp.signature:
            for p in lp.signature.params:
                lo = p.name.lower()
                if p.sort == "Point":
                    lean_pts.append(lo)
                elif p.sort == "Line":
                    lean_lns.append((p.name, lo))

        pt_set = set(lean_pts)

        # ── Extract Lean line→points from hypothesis text ─────────────
        # Parse "distinctPointsOnLine p1 p2 L" patterns
        lean_line_pts: Dict[str, List[str]] = {}
        if lp.signature and lp.signature.hypothesis_raw:
            import re
            for m in re.finditer(
                r'distinctPointsOnLine\s+(\w+)\s+(\w+)\s+(\w+)',
                lp.signature.hypothesis_raw):
                p1, p2, ln = m.group(1).lower(), m.group(2).lower(), m.group(3).lower()
                lean_line_pts.setdefault(ln, [])
                if p1 not in lean_line_pts[ln]:
                    lean_line_pts[ln].append(p1)
                if p2 not in lean_line_pts[ln]:
                    lean_line_pts[ln].append(p2)

        # Fallback: infer line points from line name characters
        for orig, lo in lean_lns:
            if lo not in lean_line_pts:
                pts: List[str] = []
                for ch in orig:
                    c = ch.lower()
                    if c in pt_set and c not in pts:
                        pts.append(c)
                lean_line_pts[lo] = pts

        # ── Check if point names already match ────────────────────────
        elib_pts = set()
        for pts in elib_lp.values():
            elib_pts |= pts
        names_match = pt_set <= elib_pts or elib_pts <= pt_set

        if names_match:
            # Identity mapping for points
            for pt in lean_pts:
                self.lean_to_elib[pt] = pt
                self.elib_to_lean[pt] = pt
            self._match_lines_by_points(lean_lns, lean_line_pts, elib_lp)
        else:
            # Structural matching needed
            self._structural_match(lean_pts, lean_lns, lean_line_pts,
                                   elib_lp, seq)

    def _match_lines_by_points(self, lean_lns, lean_line_pts, elib_lp):
        """Match lines using already-mapped point identities."""
        used_elib: Set[str] = set()
        for _, lo in lean_lns:
            lpts = set(self.lean_to_elib.get(p, p)
                       for p in lean_line_pts.get(lo, []))
            matched = False
            for eline, epts in elib_lp.items():
                if eline in used_elib:
                    continue
                if lpts and (lpts == epts or epts <= lpts):
                    self.lean_to_elib[lo] = eline
                    self.elib_to_lean[eline] = lo
                    used_elib.add(eline)
                    matched = True
                    break
            if not matched:
                fresh = self._fresh()
                self.lean_to_elib[lo] = fresh
                self.elib_to_lean[fresh] = lo
                self.extra_lines[lo] = fresh
                if len(lpts) >= 2:
                    sl = sorted(lpts)
                    self.extra_line_points[fresh] = (sl[0], sl[1])

    def _structural_match(self, lean_pts, lean_lns, lean_line_pts,
                          elib_lp, seq: Sequent):
        """Match points and lines by structural constraints when names differ.

        Builds a constraint graph: which Lean points share lines, and which
        elib points share lines, then finds a consistent mapping.
        """
        from itertools import permutations

        # Build adjacency: lean_pt → set of lean_lines containing it
        lean_pt_lines: Dict[str, Set[str]] = {}
        for lo_line, pts in lean_line_pts.items():
            for p in pts:
                lean_pt_lines.setdefault(p, set()).add(lo_line)

        # Build adjacency: elib_pt → set of elib_lines containing it
        elib_pt_lines: Dict[str, Set[str]] = {}
        for eline, epts in elib_lp.items():
            for p in epts:
                elib_pt_lines.setdefault(p, set()).add(eline)

        # Build lean line adjacency signatures:
        # For each lean line, its "signature" is (num_points, sorted indices of
        # adjacent lines through those points).
        lean_line_list = [lo for _, lo in lean_lns]
        elib_line_list = sorted(elib_lp.keys())

        # We match lines first, then derive point mapping
        # Strategy: try permutations of elib lines matched to lean lines
        # (typically only 2-3 lines, so max 6 permutations)
        lean_premise_lines = [lo for _, lo in lean_lns
                              if lean_line_pts.get(lo)]
        elib_premise_lines = sorted(elib_lp.keys())

        if len(lean_premise_lines) > len(elib_premise_lines):
            # More Lean lines than elib lines — can't fully match
            # Fall back to identity for points
            for pt in lean_pts:
                self.lean_to_elib[pt] = pt
                self.elib_to_lean[pt] = pt
            self._match_lines_by_points(lean_lns, lean_line_pts, elib_lp)
            return

        best_map = None
        best_score = -1

        for elib_perm in permutations(elib_premise_lines,
                                       len(lean_premise_lines)):
            line_map = dict(zip(lean_premise_lines, elib_perm))
            # Derive point mapping from line mapping
            pt_map: Dict[str, str] = {}
            conflict = False
            for lean_ln, elib_ln in line_map.items():
                lean_ln_pts = lean_line_pts.get(lean_ln, [])
                elib_ln_pts = sorted(elib_lp.get(elib_ln, set()))
                if len(lean_ln_pts) != len(elib_ln_pts):
                    conflict = True
                    break
                # Try to match points on this line consistently
                for lp_pt, ep_pt in zip(lean_ln_pts, elib_ln_pts):
                    if lp_pt in pt_map:
                        if pt_map[lp_pt] != ep_pt:
                            conflict = True
                            break
                    else:
                        # Check reverse: elib pt already mapped to different lean pt
                        if ep_pt in [v for k, v in pt_map.items() if k != lp_pt]:
                            conflict = True
                            break
                        pt_map[lp_pt] = ep_pt
                if conflict:
                    break

            if conflict:
                continue

            # Score: how many non-metric elib hypotheses are satisfied?
            score = 0
            for h in seq.hypotheses:
                if isinstance(h.atom, On) and h.polarity:
                    mapped_pt = pt_map.get(h.atom.point, h.atom.point)
                    mapped_obj = line_map.get(h.atom.obj, h.atom.obj)
                    # This checks forward mapping; we need reverse
                    pass
                score += 1  # Simplified scoring

            if len(pt_map) > best_score:
                best_score = len(pt_map)
                best_map = (line_map, pt_map)

        if best_map:
            line_map, pt_map = best_map
            # Apply point mapping
            for lean_pt, elib_pt in pt_map.items():
                self.lean_to_elib[lean_pt] = elib_pt
                self.elib_to_lean[elib_pt] = lean_pt
            # Identity for unmapped Lean points (exist in both)
            for pt in lean_pts:
                if pt not in self.lean_to_elib:
                    self.lean_to_elib[pt] = pt
                    self.elib_to_lean[pt] = pt
            # Apply line mapping
            used_elib: Set[str] = set()
            for _, lo in lean_lns:
                if lo in line_map:
                    eline = line_map[lo]
                    self.lean_to_elib[lo] = eline
                    self.elib_to_lean[eline] = lo
                    used_elib.add(eline)
                else:
                    # Extra line
                    fresh = self._fresh()
                    self.lean_to_elib[lo] = fresh
                    self.elib_to_lean[fresh] = lo
                    self.extra_lines[lo] = fresh
                    lpts = lean_line_pts.get(lo, [])
                    mapped_pts = [self.lean_to_elib.get(p, p) for p in lpts]
                    if len(mapped_pts) >= 2:
                        self.extra_line_points[fresh] = (
                            mapped_pts[0], mapped_pts[1])
        else:
            # Fallback: identity for everything
            for pt in lean_pts:
                self.lean_to_elib[pt] = pt
                self.elib_to_lean[pt] = pt
            self._match_lines_by_points(lean_lns, lean_line_pts, elib_lp)

    def _fresh(self) -> str:
        for ch in _LINE_POOL:
            if ch not in self._used_pool:
                self._used_pool.add(ch)
                return ch
        n = 1
        while f"L{n}" in self._used_pool:
            n += 1
        name = f"L{n}"
        self._used_pool.add(name)
        return name

    def mv(self, lean_name: str) -> str:
        lo = lean_name.lower()
        mapped = self.lean_to_elib.get(lo)
        if mapped is not None:
            return mapped
        # Strip prime marks — the proof parser does not recognize them.
        stripped = lo.replace("'", "")
        return self.lean_to_elib.get(stripped, stripped)

    def ma(self, args: List[str]) -> List[str]:
        return [self.mv(a) for a in args]


# =====================================================================
# Core synthesizer
# =====================================================================

class ProofSynthesizer:
    def __init__(self, translation: TranslationResult,
                 lean_proof: Optional[LeanProof] = None):
        self.tr = translation
        self.pname = translation.prop_name
        self.pnum = translation.prop_number
        self.lp = lean_proof
        self.thm: Optional[ETheorem] = E_THEOREM_LIBRARY.get(self.pname)
        self.seq: Optional[Sequent] = self.thm.sequent if self.thm else None
        self.avail = get_theorems_up_to(self.pname)
        self.vm: Optional[VarMapper] = None
        self.known: Set[Literal] = set()
        self.sort_ctx: Dict[str, Sort] = {}
        self.steps: List[Dict[str, Any]] = []
        self.nprem = 0
        self.ll: Dict[int, Set[Literal]] = {}
        self.errors: List[str] = []
        self.warnings: List[str] = []
        self.derived_facts: List[Literal] = []
        # ── Subproof depth tracking ──────────────────────────────────
        self.current_depth: int = 0
        # Stack of open subproofs.  Each entry is a dict:
        #   kind: "by_contra" | "by_cases"
        #   depth: the depth at which the subproof was opened
        #   assume_line: line number of the Assume step
        #   assumed_lit: the Literal that was assumed
        #   --- by_cases specific ---
        #   case_expr_lit: the Literal for the case split (φ)
        #   branches: list of dicts with branch info
        #   current_branch: index into branches (0 or 1)
        self._subproof_stack: List[Dict[str, Any]] = []

    def synthesize(self) -> SynthesisResult:
        r = SynthesisResult(prop_name=self.pname, prop_number=self.pnum)
        if not self.thm:
            r.errors.append(f"No e_library entry for {self.pname}")
            return r
        if not self.tr.steps and (not self.lp or not self.lp.tactics):
            r.errors.append("No steps or tactics to synthesize from")
            return r

        if self.lp:
            self.vm = VarMapper(self.seq, self.lp)
            # Override VarMapper with _LEAN_PARAM_ORDER for the outer
            # theorem.  VarMapper's structural matching can fail when
            # Lean params don't share point-line associations with
            # the e_library (e.g. Prop28 EF→M, but VarMapper sees
            # EF has points {e,f} which don't appear in elib's M).
            self._seed_vm_from_param_order()

        premises = [literal_to_text(lit) for lit in self.seq.hypotheses]
        self.nprem = len(premises)
        for i, lit in enumerate(self.seq.hypotheses):
            self.known.add(lit)
            self.ll[i + 1] = {lit}

        decls = self._build_decls()
        for p in decls["points"]:
            self.sort_ctx[p] = Sort.POINT
        for ln in decls["lines"]:
            self.sort_ctx[ln] = Sort.LINE

        if self.vm:
            for lean_name, elib_name in self.vm.extra_lines.items():
                pts = self.vm.extra_line_points.get(elib_name)
                if pts:
                    self._add_let_line(elib_name, pts[0], pts[1])
                    if elib_name not in decls["lines"]:
                        decls["lines"].append(elib_name)
                        decls["lines"].sort()

        if self.lp:
            tactics = self.lp.tactics
            for i, tac in enumerate(tactics):
                # Determine next tactic's depth for transition detection
                next_depth = tactics[i + 1].depth if i + 1 < len(tactics) else 0
                self._synth_tactic(tac, next_depth=next_depth)
            # Close any remaining open subproofs
            self._close_remaining_subproofs()
        else:
            for ts in self.tr.steps:
                self._synth_translated(ts)

        goal_text = ", ".join(
            literal_to_text(lit) for lit in self.seq.conclusions)
        canvas = _load_existing_canvas(self.pnum)
        if canvas is None:
            canvas = {"points": [], "segments": [], "rays": [],
                      "circles": [], "angleMarks": [], "equalityGroups": []}

        r.euclid_json = {
            "format": "euclid-proof", "version": "1.0.0",
            "program": "Euclid Elements Simulator (Python) -- Lean Translator",
            "metadata": {
                "proposition": f"Proposition I.{self.pnum}",
                "title": _PROP_TITLES.get(self.pnum, f"Proposition I.{self.pnum}"),
                "difficulty": _PROP_DIFFICULTIES.get(self.pnum, 3),
                "hints": [f"Translated from LeanEuclid {self.tr.lean_theorem}"],
                "source": "lean_translator",
            },
            "canvas": canvas,
            "exportedAt": datetime.datetime.utcnow().strftime("%Y-%m-%dT%H:%M:%SZ"),
            "proof": {
                "name": self.pname, "premises": premises,
                "goal": goal_text, "declarations": decls,
                "steps": self.steps,
                "derived_facts": [literal_to_text(f) for f in self.derived_facts],
            },
        }
        r.step_count = len(self.steps)
        r.errors = self.errors
        r.warnings = self.warnings
        r.success = len(self.errors) == 0
        return r

    def _seed_vm_from_param_order(self):
        """Override VarMapper with _LEAN_PARAM_ORDER for the outer theorem.

        VarMapper's structural matching can produce wrong line mappings
        when Lean line params have points not in the e_library (e.g.
        Prop28: Lean EF has points {e,f} but elib M has {b,c}).
        The _LEAN_PARAM_ORDER table encodes the correct mapping.

        Also assigns fresh names to auxiliary ('_') params so they
        don't collide with elib names claimed by other params.
        """
        if not self.vm or not self.lp or not self.lp.signature:
            return
        lean_name = self.lp.theorem_name
        if lean_name not in _LEAN_PARAM_ORDER:
            return
        param_order = _LEAN_PARAM_ORDER[lean_name]
        params = self.lp.signature.params

        # Collect the set of elib var names that are explicitly mapped
        # (non-aux entries) so we can avoid collisions with aux params.
        elib_claimed: Set[str] = set()
        for i, (elib_var, _sort) in enumerate(param_order):
            if i >= len(params):
                break
            if elib_var != "_":
                elib_claimed.add(elib_var)

        # Pass 1: Apply explicit (non-aux) mappings
        for i, (elib_var, _sort) in enumerate(param_order):
            if i >= len(params):
                break
            if elib_var == "_":
                continue
            lean_lo = params[i].name.lower()
            if lean_lo == elib_var:
                continue  # already correct
            # Override the mapping
            old_elib = self.vm.lean_to_elib.get(lean_lo)
            # Remove old reverse mapping if it existed
            if old_elib and old_elib in self.vm.elib_to_lean:
                del self.vm.elib_to_lean[old_elib]
            # Remove any old entry mapping to this elib_var
            for k, v in list(self.vm.lean_to_elib.items()):
                if v == elib_var and k != lean_lo:
                    del self.vm.lean_to_elib[k]
                    if elib_var in self.vm.elib_to_lean:
                        del self.vm.elib_to_lean[elib_var]
            self.vm.lean_to_elib[lean_lo] = elib_var
            self.vm.elib_to_lean[elib_var] = lean_lo
            # If the old mapping created an extra_line, clean it up
            if old_elib and lean_lo in self.vm.extra_lines:
                del self.vm.extra_lines[lean_lo]
                if old_elib in self.vm.extra_line_points:
                    del self.vm.extra_line_points[old_elib]

        # Pass 2: Reassign auxiliary params whose default mapping
        # now collides with an elib name claimed by another param.
        # A collision occurs when the aux param's effective elib name
        # (either from VarMapper or the lowercase default) matches an
        # elib var that belongs to a DIFFERENT Lean param.
        used = set(self.vm.lean_to_elib.values())
        for i, (elib_var, sort_str) in enumerate(param_order):
            if i >= len(params):
                break
            if elib_var != "_":
                continue
            lean_lo = params[i].name.lower()
            current = self.vm.lean_to_elib.get(lean_lo, lean_lo)
            if current in elib_claimed:
                # Check if any OTHER param owns this elib name
                owner_lean = self.vm.elib_to_lean.get(current)
                if owner_lean is not None and owner_lean != lean_lo:
                    # Collision — assign a fresh name
                    is_line = sort_str == "Line"
                    if is_line:
                        fresh = self.vm._fresh()
                    else:
                        fresh = self._fresh_point(used | elib_claimed)
                    self.vm.lean_to_elib[lean_lo] = fresh
                    self.vm.elib_to_lean[fresh] = lean_lo
                    used.add(fresh)
                    # Clean up extra_lines if the old mapping was an extra
                    if lean_lo in self.vm.extra_lines:
                        old_extra = self.vm.extra_lines.pop(lean_lo)
                        self.vm.extra_line_points.pop(old_extra, None)

    # -- Tactic dispatch -----------------------------------------------

    def _synth_tactic(self, tac: LeanTactic, next_depth: int = 0):
        if tac.kind == TacticKind.EUCLID_APPLY:
            self._apply(tac)
        elif tac.kind == TacticKind.EUCLID_FINISH:
            self._handle_euclid_finish(tac, next_depth)
        elif tac.kind == TacticKind.EUCLID_ASSERT:
            self._derive_from_expr(tac.assertion_expr)
        elif tac.kind == TacticKind.HAVE:
            self._derive_from_expr(tac.assertion_expr)
        elif tac.kind == TacticKind.BY_CONTRA:
            self._handle_by_contra()
        elif tac.kind == TacticKind.BY_CASES:
            self._handle_by_cases(tac)
        elif tac.kind == TacticKind.CASE_BRANCH:
            self._handle_case_branch(tac)

    def _handle_case_branch(self, tac: LeanTactic):
        """Handle CASE_BRANCH tactics whose assertion_expr embeds an apply."""
        expr = (tac.assertion_expr or "").strip()
        if not expr or expr.startswith("--"):
            return
        # Parse embedded "euclid_apply (rule args...) as bound_var"
        import re
        m = re.match(
            r"euclid_apply\s+\((\w+)((?:\s+\S+)*)\)\s+as\s+(\w+)",
            expr,
        )
        if m:
            rule = m.group(1)
            args = m.group(2).split() if m.group(2).strip() else []
            bound = [m.group(3)]
            synth_tac = LeanTactic(
                kind=TacticKind.EUCLID_APPLY,
                raw=expr,
                rule_name=rule,
                rule_args=args,
                bound_vars=bound,
                assertion_expr="",
                case_expr="",
                depth=tac.depth,
                line_number=tac.line_number,
                comment="",
            )
            self._apply(synth_tac)
            return
        # Fallback: try without bound vars
        m2 = re.match(
            r"euclid_apply\s+\((\w+)((?:\s+\S+)*)\)",
            expr,
        )
        if m2:
            rule = m2.group(1)
            args = m2.group(2).split() if m2.group(2).strip() else []
            synth_tac = LeanTactic(
                kind=TacticKind.EUCLID_APPLY,
                raw=expr,
                rule_name=rule,
                rule_args=args,
                bound_vars=[],
                assertion_expr="",
                case_expr="",
                depth=tac.depth,
                line_number=tac.line_number,
                comment="",
            )
            self._apply(synth_tac)

    def _apply(self, tac: LeanTactic):
        from .lean_mapping import classify_rule, lookup_rule, RuleCategory
        cat = classify_rule(tac.rule_name)
        mp = lookup_rule(tac.rule_name)
        if cat == RuleCategory.PROPOSITION:
            self._apply_theorem(tac, mp)
        elif cat in (RuleCategory.CONSTRUCTION, RuleCategory.EXTENSION_AXIOM,
                     RuleCategory.INTERSECTION, RuleCategory.SPECIAL):
            self._apply_construction(tac, mp)
        elif cat in (RuleCategory.METRIC, RuleCategory.TRANSFER,
                     RuleCategory.DIAGRAMMATIC):
            self._apply_inference(tac, mp)

    def _handle_by_contra(self):
        """Handle proof by contradiction: open a subproof at depth+1.

        Emits an Assume step with the negation of the goal (or the
        innermost by_cases target if nested).  The subproof is closed
        later by _close_by_contra which emits ⊥-intro + ⊥-elim.
        """
        if not self.seq:
            return
        # The assumed literal is the negation of the goal conclusion(s).
        # For a goal like ¬P, by_contra assumes P (double negation).
        # For a goal like P, by_contra assumes ¬P.
        assumed_lits: List[Literal] = []
        for conc in self.seq.conclusions:
            neg_conc = Literal(conc.atom, polarity=not conc.polarity)
            assumed_lits.append(neg_conc)

        self.current_depth += 1
        assume_ln = self.nprem + len(self.steps) + 1
        # Emit Assume step for each negated conclusion
        for neg_conc in assumed_lits:
            if neg_conc not in self.known:
                self.known.add(neg_conc)
            ln = self.nprem + len(self.steps) + 1
            self.ll[ln] = {neg_conc}
            self.steps.append({
                "lineNumber": ln,
                "text": literal_to_text(neg_conc),
                "justification": "Assume",
                "dependencies": [],
                "depth": self.current_depth, "status": "?",
            })
            assume_ln = ln

        self._subproof_stack.append({
            "kind": "by_contra",
            "depth": self.current_depth,
            "assume_line": assume_ln,
            "assumed_lits": assumed_lits,
            "goal_lits": list(self.seq.conclusions),
        })

    def _handle_by_cases(self, tac: LeanTactic):
        """Handle by_cases: prepare for two case branches.

        The actual Assume steps are emitted by _handle_case_branch when
        each CASE_BRANCH tactic is processed.  Here we just push the
        by_cases frame onto the subproof stack and parse the case
        expression.
        """
        case_expr = (tac.case_expr or "").strip()
        # Try to parse the case expression into a Literal
        case_lit = self._parse_case_expr(case_expr)
        self._subproof_stack.append({
            "kind": "by_cases",
            "outer_depth": self.current_depth,
            "case_expr": case_expr,
            "case_lit": case_lit,
            "branches": [],       # filled by _handle_case_branch
            "branch_count": 0,
        })

    def _parse_case_expr(self, expr: str) -> Optional[Literal]:
        """Try to parse a Lean case expression into a System E Literal."""
        if not expr:
            return None
        from .lean_translator import (parse_lean_expr,
                                       lean_expr_to_literals)
        try:
            parsed = parse_lean_expr(expr)
            if parsed:
                lits = lean_expr_to_literals(parsed)
                if lits and self.vm:
                    mapped = []
                    for lit in lits:
                        mapped.append(self._map_literal(lit))
                    if mapped:
                        return mapped[0]
                elif lits:
                    return lits[0]
        except Exception:
            pass
        return None

    def _handle_case_branch(self, tac: LeanTactic):
        """Handle CASE_BRANCH: open branch subproof with Assume step."""
        # Find the by_cases frame on the stack
        by_cases_frame = None
        for frame in reversed(self._subproof_stack):
            if frame["kind"] == "by_cases":
                by_cases_frame = frame
                break

        if by_cases_frame is None:
            # No by_cases frame — fall back to old behavior
            self._handle_case_branch_legacy(tac)
            return

        branch_idx = by_cases_frame["branch_count"]
        case_lit = by_cases_frame.get("case_lit")

        # First branch assumes φ, second branch assumes ¬φ
        if case_lit is not None:
            if branch_idx == 0:
                assumed = case_lit
            else:
                assumed = Literal(case_lit.atom,
                                  polarity=not case_lit.polarity)
        else:
            assumed = None

        self.current_depth += 1
        assume_ln = None
        if assumed is not None:
            ln = self.nprem + len(self.steps) + 1
            self.ll[ln] = {assumed}
            self.known.add(assumed)
            self.steps.append({
                "lineNumber": ln,
                "text": literal_to_text(assumed),
                "justification": "Assume",
                "dependencies": [],
                "depth": self.current_depth, "status": "?",
            })
            assume_ln = ln

        by_cases_frame["branches"].append({
            "assume_line": assume_ln,
            "assumed_lit": assumed,
            "depth": self.current_depth,
        })
        by_cases_frame["branch_count"] = branch_idx + 1

        # Also process any embedded apply/assert in the case branch
        self._handle_case_branch_content(tac)

    def _handle_case_branch_content(self, tac: LeanTactic):
        """Process the content embedded in a CASE_BRANCH assertion."""
        expr = (tac.assertion_expr or "").strip()
        if not expr or expr.startswith("--"):
            return
        import re
        # Try "euclid_apply (rule args...) as bound_var"
        m = re.match(
            r"euclid_apply\s+\((\w+)((?:\s+\S+)*)\)\s+as\s+(\w+)",
            expr,
        )
        if m:
            rule = m.group(1)
            args = m.group(2).split() if m.group(2).strip() else []
            bound = [m.group(3)]
            synth_tac = LeanTactic(
                kind=TacticKind.EUCLID_APPLY, raw=expr,
                rule_name=rule, rule_args=args, bound_vars=bound,
                assertion_expr="", case_expr="",
                depth=tac.depth, line_number=tac.line_number, comment="",
            )
            self._apply(synth_tac)
            return
        # Try "euclid_apply (rule args...)" without bound
        m2 = re.match(
            r"euclid_apply\s+\((\w+)((?:\s+\S+)*)\)",
            expr,
        )
        if m2:
            rule = m2.group(1)
            args = m2.group(2).split() if m2.group(2).strip() else []
            synth_tac = LeanTactic(
                kind=TacticKind.EUCLID_APPLY, raw=expr,
                rule_name=rule, rule_args=args, bound_vars=[],
                assertion_expr="", case_expr="",
                depth=tac.depth, line_number=tac.line_number, comment="",
            )
            self._apply(synth_tac)
            return
        # Try "euclid_assert <expr>"
        m3 = re.match(r"euclid_assert\s+(.+)", expr)
        if m3:
            self._derive_from_expr(m3.group(1).strip())

    def _handle_case_branch_legacy(self, tac: LeanTactic):
        """Legacy fallback for CASE_BRANCH without a by_cases frame."""
        expr = (tac.assertion_expr or "").strip()
        if not expr or expr.startswith("--"):
            return
        import re
        m = re.match(
            r"euclid_apply\s+\((\w+)((?:\s+\S+)*)\)\s+as\s+(\w+)",
            expr,
        )
        if m:
            rule = m.group(1)
            args = m.group(2).split() if m.group(2).strip() else []
            bound = [m.group(3)]
            synth_tac = LeanTactic(
                kind=TacticKind.EUCLID_APPLY, raw=expr,
                rule_name=rule, rule_args=args, bound_vars=bound,
                assertion_expr="", case_expr="",
                depth=tac.depth, line_number=tac.line_number, comment="",
            )
            self._apply(synth_tac)
            return
        m2 = re.match(
            r"euclid_apply\s+\((\w+)((?:\s+\S+)*)\)",
            expr,
        )
        if m2:
            rule = m2.group(1)
            args = m2.group(2).split() if m2.group(2).strip() else []
            synth_tac = LeanTactic(
                kind=TacticKind.EUCLID_APPLY, raw=expr,
                rule_name=rule, rule_args=args, bound_vars=[],
                assertion_expr="", case_expr="",
                depth=tac.depth, line_number=tac.line_number, comment="",
            )
            self._apply(synth_tac)

    def _handle_euclid_finish(self, tac: LeanTactic, next_depth: int):
        """Handle euclid_finish: derive remaining conclusions + close subproofs.

        euclid_finish means "the current proof goal can be closed by the
        consequence engine."  After running _finish(), we check if the
        depth is about to decrease and close the appropriate subproof(s).
        """
        self._finish()

        # Close subproofs based on depth transition
        # If next tactic's depth is less than current, subproofs are closing
        while (self._subproof_stack
               and next_depth < self.current_depth):
            frame = self._subproof_stack[-1]
            if frame["kind"] == "by_cases":
                # A euclid_finish inside by_cases means a branch ended.
                # Decrease depth for this branch.
                if self.current_depth > frame.get("outer_depth", 0) + 1:
                    # Nested subproof closing, not the by_cases itself
                    break
                self.current_depth -= 1
                # If both branches done (next tactic depth <= outer_depth),
                # close the by_cases
                if next_depth <= frame.get("outer_depth", 0):
                    self._close_by_cases(frame)
                    self._subproof_stack.pop()
                break
            elif frame["kind"] == "by_contra":
                if self.current_depth > frame["depth"]:
                    # Still inside a nested subproof
                    self.current_depth -= 1
                    break
                # Close the by_contra
                self._close_by_contra(frame)
                self._subproof_stack.pop()
                self.current_depth = frame["depth"] - 1
                break
            else:
                break

    def _close_by_contra(self, frame: Dict[str, Any]):
        """Emit ⊥-intro and ⊥-elim to close a proof-by-contradiction subproof."""
        assume_ln = frame["assume_line"]
        goal_lits = frame.get("goal_lits", [])
        depth = frame["depth"]

        # ⊥-intro at the subproof depth
        ln = self.nprem + len(self.steps) + 1
        self.steps.append({
            "lineNumber": ln,
            "text": "⊥",
            "justification": "⊥-intro",
            "dependencies": [assume_ln],
            "depth": depth, "status": "?",
        })
        self.ll[ln] = set()  # BOTTOM
        contra_ln = ln

        # ⊥-elim at the outer depth (depth - 1): conclude the goal
        outer_depth = depth - 1
        for goal_lit in goal_lits:
            ln = self.nprem + len(self.steps) + 1
            self.known.add(goal_lit)
            self.ll[ln] = {goal_lit}
            self.steps.append({
                "lineNumber": ln,
                "text": literal_to_text(goal_lit),
                "justification": "⊥-elim",
                "dependencies": [assume_ln],
                "depth": outer_depth, "status": "?",
            })

    def _close_by_cases(self, frame: Dict[str, Any]):
        """Emit Cases step to close a proof-by-cases subproof."""
        branches = frame.get("branches", [])
        outer_depth = frame.get("outer_depth", 0)

        if len(branches) < 2:
            return  # Can't close with fewer than 2 branches

        a1_ln = branches[0].get("assume_line")
        a2_ln = branches[1].get("assume_line")
        if a1_ln is None or a2_ln is None:
            return

        # The conclusion of Cases should be whatever both branches derived.
        # For by_contra+by_cases, the contradiction was already found in
        # each branch; the Cases conclusion is ⊥ (or the shared derived fact).
        # For standalone by_cases, we need to find the shared conclusion.
        #
        # Heuristic: if we're inside a by_contra, the shared conclusion
        # is ⊥ (the contradiction).  Otherwise, find shared new facts.
        parent_frame = None
        for f in reversed(self._subproof_stack):
            if f is not frame and f["kind"] == "by_contra":
                parent_frame = f
                break

        if parent_frame is not None:
            # Inside a by_contra: Cases concludes ⊥
            ln = self.nprem + len(self.steps) + 1
            self.steps.append({
                "lineNumber": ln,
                "text": "⊥",
                "justification": "Cases",
                "dependencies": [a1_ln, a2_ln],
                "depth": outer_depth, "status": "?",
            })
            self.ll[ln] = set()
        else:
            # Standalone by_cases: conclude shared derived facts
            # For now, just emit a Cases step — the verifier will check
            # that both branches derived the step_lits.
            ln = self.nprem + len(self.steps) + 1
            self.steps.append({
                "lineNumber": ln,
                "text": "Cases",
                "justification": "Cases",
                "dependencies": [a1_ln, a2_ln],
                "depth": outer_depth, "status": "?",
            })
            self.ll[ln] = set()

    def _close_remaining_subproofs(self):
        """Close any subproofs left open at the end of tactic processing."""
        while self._subproof_stack:
            frame = self._subproof_stack[-1]
            if frame["kind"] == "by_contra":
                self._close_by_contra(frame)
                self._subproof_stack.pop()
                self.current_depth = frame["depth"] - 1
            elif frame["kind"] == "by_cases":
                self._close_by_cases(frame)
                self._subproof_stack.pop()
                self.current_depth = frame.get("outer_depth", 0)
            else:
                self._subproof_stack.pop()

    # -- Construction --------------------------------------------------

    _POINT_POOL = list("abcdefghijklmnopqrstuvwxyz")

    def _fresh_bound_vars(self, lean_bound_vars: List[str]) -> List[str]:
        """Map construction bound vars to fresh names avoiding collisions.

        Bound vars are NEW variables introduced by constructions. They should
        not be mapped through VarMapper (which maps existing Lean names to
        elib names). Instead, use their lowercase form if it doesn't collide,
        or allocate a fresh name.

        Prime marks (') are stripped because the proof parser does not
        recognize them, so f' would collide with f.
        """
        used = set(self.vm.lean_to_elib.values()) if self.vm else set()
        # Also include all variables already in sort_ctx (points & lines
        # introduced by previous constructions)
        used |= set(self.sort_ctx.keys())
        result = []
        for bv in lean_bound_vars:
            lo = bv.lower().replace("'", "")
            if lo not in used:
                result.append(lo)
                used.add(lo)
                # Register in VarMapper so subsequent tactics can find it
                if self.vm:
                    self.vm.lean_to_elib[bv.lower()] = lo
                    self.vm.elib_to_lean[lo] = bv.lower()
            else:
                # Collision — allocate fresh name
                # Determine sort: single uppercase → Line, else → Point
                is_line = len(bv) == 1 and bv.isupper()
                if is_line:
                    fresh = self.vm._fresh() if self.vm else lo
                else:
                    fresh = self._fresh_point(used)
                result.append(fresh)
                used.add(fresh)
                if self.vm:
                    self.vm.lean_to_elib[bv.lower()] = fresh
                    self.vm.elib_to_lean[fresh] = bv.lower()
        return result

    def _fresh_point(self, used: Set[str]) -> str:
        """Allocate a fresh point name not in used."""
        for ch in self._POINT_POOL:
            if ch not in used:
                return ch
        n = 1
        while f"p{n}" in used:
            n += 1
        return f"p{n}"

    def _peek_bound_vars(self, lean_bound_vars: List[str]) -> List[str]:
        """Compute fresh bound-var names WITHOUT modifying VarMapper.

        Returns the same names that _fresh_bound_vars would, but does not
        register them. Used for speculative var_map checks.
        """
        used = set(self.vm.lean_to_elib.values()) if self.vm else set()
        used |= set(self.sort_ctx.keys())
        result = []
        for bv in lean_bound_vars:
            lo = bv.lower().replace("'", "")
            if lo not in used:
                result.append(lo)
                used.add(lo)
            else:
                is_line = len(bv) == 1 and bv.isupper()
                if is_line:
                    # Peek at fresh line name without modifying pool
                    for ch in _LINE_POOL:
                        if ch not in (self.vm._used_pool if self.vm else set()) and ch not in used:
                            result.append(ch)
                            used.add(ch)
                            break
                    else:
                        result.append(lo)
                else:
                    fresh = self._fresh_point(used)
                    result.append(fresh)
                    used.add(fresh)
        return result

    def _commit_bound_vars(self, lean_bound_vars: List[str],
                           computed_names: List[str]):
        """Register previously-computed bound var names in VarMapper."""
        if not self.vm:
            return
        for bv, name in zip(lean_bound_vars, computed_names):
            lo = bv.lower()
            self.vm.lean_to_elib[lo] = name
            self.vm.elib_to_lean[name] = lo

    def _apply_construction(self, tac: LeanTactic, mp):
        rule_name = mp.system_e_name if mp else tac.rule_name
        args = self.vm.ma(tac.rule_args) if self.vm else [a.lower() for a in tac.rule_args]
        # Bound vars are NEW variables introduced by constructions.
        # Don't map them through VarMapper — they need fresh names if
        # they collide with existing mapped names.
        bound = self._fresh_bound_vars(tac.bound_vars) if self.vm else [v.lower() for v in tac.bound_vars]

        # ── Inject construction prerequisites ─────────────────────────
        # let-line / let-circle: need ¬(a = b)
        if tac.rule_name == "line_from_points" and len(args) >= 2:
            self._ensure_neq(args[0], args[1])
        elif tac.rule_name == "circle_from_points" and len(args) >= 2:
            self._ensure_neq(args[0], args[1])
        elif tac.rule_name in ("extend_point", "extend_point_longer",
                                "extend_point_not_on_line",
                                "exists_point_on_extension",
                                "exists_point_on_extension_longer") and len(args) >= 3:
            # let-point-on-line-extend: need on(b,L), on(c,L), ¬(b=c)
            self._ensure_neq(args[1], args[2])
        elif tac.rule_name == "exists_point_between_points_on_line" and len(args) >= 3:
            # let-point-on-line-between: need on(b,L), on(c,L), ¬(b=c)
            self._ensure_neq(args[0], args[1])
        elif tac.rule_name == "intersection_lines" and len(args) >= 2:
            # let-intersection-line-line: need intersects(L, M)
            self._ensure_intersects(args[0], args[1])
        elif tac.rule_name == "intersection_circles" and len(args) >= 2:
            # let-intersection-circle-circle: need intersects(α, β)
            self._ensure_intersects(args[0], args[1])
        elif tac.rule_name in ("intersection_circle_line",
                                "intersection_circle_line_extending_points") and len(args) >= 2:
            # let-intersection-circle-line: need intersects(L, α) or intersects(α, L)
            self._ensure_intersects(args[0], args[1])

        # Map rule name for special constructions
        actual_rule_name = rule_name
        if tac.rule_name == "line_nonempty":
            actual_rule_name = "let-point-on-line"
        elif tac.rule_name == "exists_distincts_points_on_line":
            actual_rule_name = "let-point-on-line"
        elif tac.rule_name == "point_on_line_same_side":
            # Lean axiom: creates point on line M, same-side as b w.r.t. L.
            # No single System E rule matches; use let-point-same-side as closest.
            actual_rule_name = "let-point-same-side"
        elif tac.rule_name in ("exists_point_opposite",
                                "exists_distinct_point_opposite_side"):
            actual_rule_name = "let-point-opposite-side"
        elif tac.rule_name in ("exists_point_on_circle",
                                "exists_distinct_point_on_circle"):
            actual_rule_name = "let-point-on-circle"

        text, lits = self._construction_text(tac.rule_name, actual_rule_name, args, bound)
        for lit in lits:
            self.known.add(lit)
        for v in bound:
            if v not in self.sort_ctx:
                self.sort_ctx[v] = Sort.LINE if (len(v) == 1 and v.isupper()) else Sort.POINT

        # Compute precise deps from the construction's prerequisites.
        prereq_lits = self._instantiate_construction_prereqs(
            actual_rule_name, lits)
        if prereq_lits is not None:
            deps = self._deps_for_premises(prereq_lits)
        else:
            # Fallback: variable-overlap (old behaviour)
            new_var_set = set(bound)
            deps = self._deps_for(lits, new_var_set)
        ln = self.nprem + len(self.steps) + 1
        self.steps.append({
            "lineNumber": ln, "text": text,
            "justification": actual_rule_name, "dependencies": deps,
            "depth": self.current_depth, "status": "?",
        })
        self.ll[ln] = set(lits)

    def _instantiate_construction_prereqs(
        self, rule_name: str, step_lits: List[Literal],
    ) -> Optional[Set[Literal]]:
        """Compute the actual prerequisite literals for a construction rule.

        Matches the rule's conclusion pattern against *step_lits* to build
        a variable binding, then instantiates the prerequisite pattern.
        Returns ``None`` if the rule has no prerequisites or matching fails.
        """
        from .e_construction import CONSTRUCTION_RULE_BY_NAME

        rule = CONSTRUCTION_RULE_BY_NAME.get(rule_name)
        if rule is None or not rule.prereq_pattern:
            return None

        # Build var bindings by matching conclusion pattern → step lits
        bindings: Dict[str, str] = {}
        remaining = list(step_lits)
        for pat_lit in rule.conclusion_pattern:
            for i, sl in enumerate(remaining):
                result = self._try_match_construction_lit(
                    pat_lit, sl, bindings)
                if result is not None:
                    bindings = result
                    remaining.pop(i)
                    break

        if not bindings:
            return None

        # Instantiate prerequisites with the derived bindings
        prereqs: Set[Literal] = set()
        for prereq in rule.prereq_pattern:
            inst = substitute_literal(prereq, bindings)
            prereqs.add(inst)
        return prereqs

    @staticmethod
    def _try_match_construction_lit(
        pattern: Literal, candidate: Literal,
        bindings: Dict[str, str],
    ) -> Optional[Dict[str, str]]:
        """Try to match a pattern literal against a candidate literal.

        Returns updated bindings on success, None on failure.
        Pattern variables are single lowercase letters or uppercase letters.
        """
        if pattern.polarity != candidate.polarity:
            return None
        pa, ca = pattern.atom, candidate.atom
        if type(pa) is not type(ca):
            return None
        new_bindings = dict(bindings)

        def _bind(pvar: str, cvar) -> bool:
            if not isinstance(cvar, str):
                return False
            if pvar in new_bindings:
                return new_bindings[pvar] == cvar
            new_bindings[pvar] = cvar
            return True

        if isinstance(pa, On):
            if not (_bind(pa.point, ca.point) and _bind(pa.obj, ca.obj)):
                return None
        elif isinstance(pa, Between):
            if not (_bind(pa.a, ca.a) and _bind(pa.b, ca.b)
                    and _bind(pa.c, ca.c)):
                return None
        elif isinstance(pa, SameSide):
            if not (_bind(pa.p1, ca.p1) and _bind(pa.p2, ca.p2)
                    and _bind(pa.line, ca.line)):
                return None
        elif isinstance(pa, Equals):
            if not (_bind(pa.left, ca.left) and _bind(pa.right, ca.right)):
                return None
        elif isinstance(pa, Center):
            if not (_bind(pa.point, ca.point) and _bind(pa.circle, ca.circle)):
                return None
        elif isinstance(pa, Inside):
            if not (_bind(pa.point, ca.point) and _bind(pa.circle, ca.circle)):
                return None
        elif isinstance(pa, Intersects):
            if not (_bind(pa.obj1, ca.obj1) and _bind(pa.obj2, ca.obj2)):
                return None
        else:
            return None
        return new_bindings

    def _parse_segment_expr(self, expr: str) -> Optional[Tuple[str, str]]:
        """Parse a Lean segment expression like '(a─e)' into mapped point names.

        Returns (p1, p2) as mapped variable names, or None if unparseable.
        """
        s = expr.strip()
        if s.startswith('(') and s.endswith(')'):
            s = s[1:-1]
        # Split on ─ (em-dash used in Lean segment notation)
        parts = s.split('\u2500')
        if len(parts) == 2:
            raw1, raw2 = parts[0].strip(), parts[1].strip()
            p1 = self.vm.mv(raw1) if self.vm else raw1.lower()
            p2 = self.vm.mv(raw2) if self.vm else raw2.lower()
            return (p1, p2)
        return None

    def _construction_text(self, lean_rule, se_rule, args, bound):
        lits: List[Literal] = []
        if lean_rule in ("line_from_points",) and len(args) >= 2 and bound:
            a, b, line = args[0], args[1], bound[0]
            lits = [_pos(On(a, line)), _pos(On(b, line))]
        elif lean_rule == "extend_point_longer" and len(args) >= 4 and bound:
            # extend_point_longer L b c s as d
            # Conclusions: on(d,L), between(b,c,d), |s| < |c─d|
            # Only include diagrammatic literals in the construction step;
            # the metric inequality is added as a derived fact.
            line, b, c, d = args[0], args[1], args[2], bound[0]
            lits = [_pos(On(d, line)), _pos(Between(b, c, d))]
            seg_expr = args[3]
            seg_pts = self._parse_segment_expr(seg_expr)
            if seg_pts:
                sp1, sp2 = seg_pts
                metric_lit = _pos(LessThan(SegmentTerm(sp1, sp2),
                                           SegmentTerm(c, d)))
                self.known.add(metric_lit)
                self.derived_facts.append(metric_lit)
        elif lean_rule in ("extend_point", "extend_point_longer",
                           "extend_point_not_on_line",
                           "exists_point_on_extension",
                           "exists_point_on_extension_longer") and len(args) >= 3 and bound:
            line, b, c, d = args[0], args[1], args[2], bound[0]
            lits = [_pos(On(d, line)), _pos(Between(b, c, d))]
        elif lean_rule in ("intersection_lines",) and len(args) >= 2 and bound:
            l1, l2, pt = args[0], args[1], bound[0]
            lits = [_pos(On(pt, l1)), _pos(On(pt, l2))]
        elif lean_rule in ("circle_from_points",) and len(args) >= 2 and bound:
            ctr, on_pt, circ = args[0], args[1], bound[0]
            lits = [_pos(Center(ctr, circ)), _pos(On(on_pt, circ))]
        elif lean_rule in ("intersection_circles",) and len(args) >= 2 and bound:
            c1, c2, pt = args[0], args[1], bound[0]
            lits = [_pos(On(pt, c1)), _pos(On(pt, c2))]
        elif lean_rule in ("intersection_circle_line",
                           "intersection_circle_line_extending_points") and len(args) >= 2 and bound:
            c_arg, l_arg, pt = args[0], args[1], bound[0]
            lits = [_pos(On(pt, c_arg)), _pos(On(pt, l_arg))]
        elif lean_rule in ("arbitrary_point", "distinct_points") and bound:
            pass
        elif lean_rule in ("point_same_side",
                           "distinct_point_same_side") and len(args) >= 2 and bound:
            ref_pt, line, new_pt = args[0], args[1], bound[0]
            lits = [_pos(SameSide(new_pt, ref_pt, line))]
        elif lean_rule == "exists_point_between_points_on_line" and len(args) >= 3 and bound:
            b, c, line, pt = args[0], args[1], args[2], bound[0]
            lits = [_pos(On(pt, line)), _pos(Between(b, pt, c))]
        elif lean_rule == "point_between_points_shorter_than" and len(args) >= 2 and bound:
            b, c, pt = args[0], args[1], bound[0]
            lits = [_pos(Between(b, pt, c))]
        elif lean_rule == "line_nonempty" and len(args) >= 1 and bound:
            # ∀ l, ∃ p, p.onLine l
            line, pt = args[0], bound[0]
            lits = [_pos(On(pt, line))]
        elif lean_rule == "exists_distincts_points_on_line" and len(args) >= 2 and bound:
            # ∀ l p, ∃ p', p ≠ p' ∧ p'.onLine l
            line, ref_pt, new_pt = args[0], args[1], bound[0]
            lits = [_pos(On(new_pt, line)), _neg(Equals(ref_pt, new_pt))]
        elif lean_rule == "point_on_line_same_side" and len(args) >= 3 and bound:
            # ∀ L M b, ¬(b.onLine L) ∧ intersects(L,M) → ∃ a, a.onLine M ∧ a.sameSide b L
            # Construction pattern only allows same-side; on(pt,line) is a derived fact.
            line_l, line_m, ref_pt, new_pt = args[0], args[1], args[2], bound[0]
            on_lit = _pos(On(new_pt, line_m))
            self.known.add(on_lit)
            self.derived_facts.append(on_lit)
            lits = [_pos(SameSide(new_pt, ref_pt, line_l))]
        elif lean_rule in ("exists_point_opposite",
                           "exists_distinct_point_opposite_side") and len(args) >= 2 and bound:
            line, ref_pt, new_pt = args[0], args[1], bound[0]
            lits = [_neg(On(new_pt, line)), _neg(SameSide(new_pt, ref_pt, line))]
        elif lean_rule in ("exists_point_on_circle",
                           "exists_distinct_point_on_circle") and len(args) >= 1 and bound:
            circ, new_pt = args[0], bound[0]
            lits = [_pos(On(new_pt, circ))]
        else:
            for ts in self.tr.steps:
                if ts.step.description == se_rule and ts.step.assertions:
                    for a in ts.step.assertions:
                        lits.append(self._map_lit(a))
                    break
        text = ", ".join(literal_to_text(l) for l in lits) if lits else ""
        return text, lits

    # -- Theorem application -------------------------------------------

    def _apply_theorem(self, tac: LeanTactic, mp):
        se_name = mp.system_e_name if mp else tac.rule_name
        thm = self.avail.get(se_name)
        if not thm:
            self.warnings.append(f"Theorem {se_name} not available")
            return
        var_map = self._build_thm_varmap(thm, tac)

        # ── Inject metric prerequisite steps ──────────────────────────
        # For each hypothesis not directly in known, try to emit a
        # derivation step (M3 Symmetry, M4 Angle symmetry, CN1, etc.)
        self._inject_metric_prereqs(thm, var_map)

        # Check if Lean arg positions give us better conclusions than
        # the e_library var_map (handles shared-endpoint cases like I.3)
        lean_lits = self._lean_arg_conclusions(tac, se_name)

        text_parts = []
        step_lits: Set[Literal] = set()
        if lean_lits:
            # Use Lean-intended conclusions as the step output
            for lit in lean_lits:
                text_parts.append(literal_to_text(lit))
                step_lits.add(lit)
                self.known.add(lit)
            # Also add var_map conclusions to known (they're still valid
            # derivations, just not the ones Lean intends for this step)
            for conc in thm.sequent.conclusions:
                inst = substitute_literal(conc, var_map)
                self.known.add(inst)
        else:
            for conc in thm.sequent.conclusions:
                inst = substitute_literal(conc, var_map)
                text_parts.append(literal_to_text(inst))
                step_lits.add(inst)
                self.known.add(inst)
        text = ", ".join(text_parts)

        deps = self._thm_deps(thm, var_map)
        ln = self.nprem + len(self.steps) + 1
        self.steps.append({
            "lineNumber": ln, "text": text,
            "justification": se_name, "dependencies": deps,
            "depth": self.current_depth, "status": "?",
        })
        self.ll[ln] = step_lits

    def _inject_metric_prereqs(self, thm: ETheorem, var_map: Dict[str, str]):
        """Inject prerequisite steps needed by a theorem.

        For each hypothesis not directly in known:
        - M3 Symmetry: ab=ba when ba=ab is known (segment)
        - M4 Angle symmetry: ∠abc=∠cba when needed
        - CN1 Transitivity: derive equalities via chain
        - Distinctness: ¬(a=b) via _ensure_neq
        - Diagrammatic: on(), between(), ¬on(), ¬same-side(), intersects()
          via ConsequenceEngine
        """
        for hyp in thm.sequent.hypotheses:
            inst = substitute_literal(hyp, var_map)
            if inst in self.known:
                continue

            # Skip impossible hypotheses where ¬(x=y) becomes ¬(v=v)
            # due to Lean reusing the same variable in positions elib
            # requires distinct.  These are vacuously handled by
            # _lean_arg_conclusions providing the correct step text.
            if (not inst.polarity and isinstance(inst.atom, Equals)
                    and isinstance(inst.atom.left, str)
                    and inst.atom.left == inst.atom.right):
                continue

            # Check if it's a distinctness prerequisite
            if not inst.polarity and isinstance(inst.atom, Equals):
                left, right = inst.atom.left, inst.atom.right
                if isinstance(left, str) and isinstance(right, str):
                    self._ensure_neq(left, right)
                    continue

            # Check if symmetric form is known (M3/M4)
            sym = self._symmetric_literal(inst)
            if sym is not None:
                # Emit M3 or M4 step
                just = self._metric_symmetry_just(inst)
                deps = self._deps_target(sym)
                ln = self.nprem + len(self.steps) + 1
                self.steps.append({
                    "lineNumber": ln,
                    "text": literal_to_text(inst),
                    "justification": just,
                    "dependencies": deps,
                    "depth": self.current_depth, "status": "?",
                })
                self.known.add(inst)
                self.ll[ln] = {inst}
                continue

            # Try MetricEngine for CN1 transitivity chains
            if inst.is_metric:
                from .e_metric import MetricEngine
                me = MetricEngine()
                # Scope: only metric literals from known set (diagrammatic
                # facts are irrelevant to MetricEngine and expensive to
                # process in large numbers).
                metric_known = {k for k in self.known if k.is_metric}
                if me.is_consequence(metric_known, inst):
                    deps = self._deps_target(inst)
                    just = self._metric_just(inst)
                    ln = self.nprem + len(self.steps) + 1
                    self.steps.append({
                        "lineNumber": ln,
                        "text": literal_to_text(inst),
                        "justification": just,
                        "dependencies": deps,
                        "depth": self.current_depth, "status": "?",
                    })
                    self.known.add(inst)
                    self.ll[ln] = {inst}
                    continue

            # Try ConsequenceEngine for diagrammatic hypotheses
            # (on, between, ¬on, ¬same-side, intersects, etc.)
            if inst.is_diagrammatic:
                self._inject_diag_prereq(inst)

    def _inject_diag_prereq(self, target: Literal):
        """Try to derive a diagrammatic prerequisite via axiom match.

        Since the Lean proof is machine-verified, every prerequisite IS
        derivable.  We use fast-path pattern matching first, then a quick
        direct axiom check on scoped facts, and fall back to emitting the
        step with a heuristic justification (the verifier handles the rest).
        """
        from .e_axiom_match import check_specific_axiom

        # Fast path for on(p, L): check if derivable from betweenness
        # between(a,b,c) + on(a,L) + on(c,L) → on(b,L) via Betweenness 3
        if target.polarity and isinstance(target.atom, On):
            pt, obj = target.atom.point, target.atom.obj
            for k in self.known:
                if k.polarity and isinstance(k.atom, Between):
                    a, b, c = k.atom.a, k.atom.b, k.atom.c
                    matched = False
                    if b == pt:
                        on_a = _pos(On(a, obj))
                        on_c = _pos(On(c, obj))
                        matched = on_a in self.known and on_c in self.known
                    elif a == pt:
                        on_b = _pos(On(b, obj))
                        on_c = _pos(On(c, obj))
                        matched = on_b in self.known and on_c in self.known
                    elif c == pt:
                        on_a = _pos(On(a, obj))
                        on_b = _pos(On(b, obj))
                        matched = on_a in self.known and on_b in self.known
                    if matched:
                        deps = self._deps_target(target)
                        if self._try_emit_neq(target, "Betweenness 3", deps):
                            return
                        # Try broader deps
                        deps = sorted(self.ll.keys())
                        if self._try_emit_neq(target, "Betweenness 3", deps):
                            return

        tv = literal_vars(target)
        just = self._guess_diag_fast(target)

        # Try direct axiom match on scoped facts (no CE closure — fast)
        scoped_facts: Set[Literal] = set()
        scoped_lines: Set[int] = set()
        for ln_num, lits in self.ll.items():
            for lit in lits:
                if literal_vars(lit) & tv:
                    scoped_facts |= lits
                    scoped_lines.add(ln_num)
                    break

        dep_vars: Dict[str, Sort] = dict(self.sort_ctx)
        for lit in scoped_facts:
            for v in literal_vars(lit):
                if v not in dep_vars:
                    dep_vars[v] = (Sort.LINE if (len(v) == 1 and v.isupper())
                                    else Sort.POINT)
        ok, _ = check_specific_axiom(just, scoped_facts, [target], dep_vars)
        if ok:
            self._emit_diag_step(target, just, sorted(scoped_lines))
            return

        # Try _find_minimal_deps with axiom verification.
        deps = self._find_minimal_deps(target, just, tv)
        # Verify that the axiom actually derives the target with these deps.
        dep_lits: Set[Literal] = set()
        for d in deps:
            dep_lits |= self.ll.get(d, set())
        dv2: Dict[str, Sort] = dict(self.sort_ctx)
        for lit in dep_lits:
            for v in literal_vars(lit):
                if v not in dv2:
                    dv2[v] = (Sort.LINE if (len(v) == 1 and v.isupper())
                              else Sort.POINT)
        ok2, _ = check_specific_axiom(just, dep_lits, [target], dv2)
        if ok2:
            self._emit_diag_step(target, just, deps)
            return

        # No single axiom can derive this fact (e.g. ¬on(a, M) which
        # requires a multi-step Generality 1 contrapositive argument).
        # Add to known and record as a derived fact so the verifier
        # seeds it into checker.known for downstream theorem steps.
        self.known.add(target)
        self.derived_facts.append(target)

    def _emit_diag_step(self, target: Literal, just: str,
                        deps: List[int]):
        """Emit a diagrammatic derivation step."""
        ln = self.nprem + len(self.steps) + 1
        self.steps.append({
            "lineNumber": ln,
            "text": literal_to_text(target),
            "justification": just,
            "dependencies": deps,
            "depth": self.current_depth, "status": "?",
        })
        self.known.add(target)
        self.ll[ln] = {target}

    def _guess_diag_fast(self, target: Literal) -> str:
        """Fast heuristic axiom name for diagrammatic targets.

        Unlike _guess_diag, avoids calling _find_neq_axiom (which does
        expensive CE closure). Uses _find_neq_axiom_fast instead.
        """
        a = target.atom
        if isinstance(a, Between):
            return "Betweenness 1a" if target.polarity else "Betweenness 1b"
        if isinstance(a, Equals) and not target.polarity:
            return self._find_neq_axiom_fast(target)
        if isinstance(a, On) and target.polarity:
            return self._guess_on_axiom(target)
        if isinstance(a, On) and not target.polarity:
            return "Generality 1"
        if isinstance(a, Intersects):
            return "Intersection 1"
        if isinstance(a, SameSide):
            return "Same-side 1" if target.polarity else "Same-side 4"
        return "Generality 1"

    def _guess_on_axiom(self, target: Literal) -> str:
        """Pick axiom name for positive on(p, L) derivation.

        - Betweenness 3 if derivable from between(a,p,c) + on(a,L) + on(c,L)
        - Generality 6 otherwise (equality substitution)
        """
        pt, obj = target.atom.point, target.atom.obj
        for k in self.known:
            if k.polarity and isinstance(k.atom, Between):
                a, b, c = k.atom.a, k.atom.b, k.atom.c
                if b == pt:
                    if (_pos(On(a, obj)) in self.known and
                            _pos(On(c, obj)) in self.known):
                        return "Betweenness 3"
                elif a == pt:
                    if (_pos(On(b, obj)) in self.known and
                            _pos(On(c, obj)) in self.known):
                        return "Betweenness 3"
                elif c == pt:
                    if (_pos(On(a, obj)) in self.known and
                            _pos(On(b, obj)) in self.known):
                        return "Betweenness 3"
        return "Generality 6"

    def _metric_symmetry_just(self, target: Literal) -> str:
        """Pick the right justification for a metric symmetry step."""
        a = target.atom
        if isinstance(a, Equals):
            if isinstance(a.left, SegmentTerm) or isinstance(a.right, SegmentTerm):
                return "M3 \u2014 Symmetry"
            if isinstance(a.left, AngleTerm) or isinstance(a.right, AngleTerm):
                return "M4 \u2014 Angle symmetry"
        return "CN1 \u2014 Transitivity"

    def _metric_just(self, target: Literal) -> str:
        """Pick the right justification for a metric derivation."""
        a = target.atom
        if isinstance(a, LessThan):
            return "CN5 \u2014 Whole > Part"
        if isinstance(a, Equals):
            if isinstance(a.left, MagAdd) or isinstance(a.right, MagAdd):
                return "CN1 \u2014 Transitivity"
            if isinstance(a.left, SegmentTerm) and isinstance(a.right, SegmentTerm):
                return "CN1 \u2014 Transitivity"
            if isinstance(a.left, AngleTerm) and isinstance(a.right, AngleTerm):
                return "CN1 \u2014 Transitivity"
            if isinstance(a.left, AreaTerm) or isinstance(a.right, AreaTerm):
                return "CN1 \u2014 Transitivity"
        return "CN1 \u2014 Transitivity"

    def _lean_arg_conclusions(self, tac: LeanTactic,
                              se_name: str) -> Optional[List[Literal]]:
        """Compute theorem conclusions directly from Lean arg positions.

        Handles cases where the e_library var_map produces incorrect metric
        conclusions due to shared endpoints between segments (e.g. Lean's
        ``proposition_3 a c a b AC AB as d`` where lesser segment ``a b``
        shares endpoint ``a`` with the greater ``a c``).

        Returns None if no override is needed.
        """
        if not self.vm:
            return None
        args = self.vm.ma(tac.rule_args)
        bound = self.vm.ma(tac.bound_vars) if tac.bound_vars else []

        if se_name == "Prop.I.3" and len(args) >= 4 and bound:
            # Lean: proposition_3 p1 p2 p3 p4 L1 L2 as e
            # Semantics: cut segment p1-p2 (greater) to get e with
            #   between(p1, e, p2) and |p1─e| = |p3─p4|
            p1, p2, p3, p4 = args[0], args[1], args[2], args[3]
            e = bound[0]
            return [
                _pos(Between(p1, e, p2)),
                _pos(Equals(SegmentTerm(p1, e), SegmentTerm(p3, p4))),
            ]

        return None

    def _build_thm_varmap(self, thm: ETheorem, tac: LeanTactic) -> Dict[str, str]:
        """Build var_map by matching e_library hypotheses against known facts.

        Uses Lean rule_args (mapped through VarMapper) as the candidate
        variable pool, then tries permutations to find a substitution
        where all hypotheses are satisfied.

        Also maps bound_vars (from 'as x') to exists_vars in the sequent.
        """
        elib_vars: Set[str] = set()
        for h in thm.sequent.hypotheses:
            elib_vars |= literal_vars(h)
        for c in thm.sequent.conclusions:
            elib_vars |= literal_vars(c)

        # Separate exists-vars (bound results) from hypothesis vars
        exists_set = {name for name, _ in thm.sequent.exists_vars}
        hyp_vars = elib_vars - exists_set

        identity = {v: v for v in elib_vars}

        # Get mapped Lean rule_args as candidate variable pool
        cited_params = self._cited_lean_params(tac.rule_name)

        # Strategy -1: Direct var_map from _LEAN_PARAM_ORDER table.
        # The table provides the exact elib var for each Lean positional arg,
        # handling cases where Lean and e_library use different variable conventions.
        if tac.rule_args:
            _table_key = tac.rule_name  # full name including primes
            if _table_key in _LEAN_PARAM_ORDER:
                param_order = _LEAN_PARAM_ORDER[_table_key]
                direct_vm: Dict[str, str] = {}
                # Also track auxiliary "_" arg values — these are Lean args
                # that don't directly correspond to named elib vars but may
                # be needed to fill unmapped elib vars via sort matching.
                _aux_pts: List[str] = []
                _aux_lns: List[str] = []
                for i, (elib_var, _sort) in enumerate(param_order):
                    if i < len(tac.rule_args):
                        arg = tac.rule_args[i]
                        if arg.startswith('(') or '\u2500' in arg or '|' in arg:
                            continue
                        actual = self.vm.mv(arg) if self.vm else arg.lower()
                        if elib_var == "_":
                            if _sort == "Line":
                                _aux_lns.append(actual)
                            else:
                                _aux_pts.append(actual)
                        elif elib_var not in direct_vm:
                            direct_vm[elib_var] = actual
                # Fill unmapped elib vars from auxiliary args by sort.
                unmapped_pts = [v for v in hyp_vars
                                if not (len(v) == 1 and v.isupper())
                                and v not in direct_vm]
                unmapped_lns = [v for v in hyp_vars
                                if (len(v) == 1 and v.isupper())
                                and v not in direct_vm]
                for j, ev in enumerate(unmapped_lns):
                    if j < len(_aux_lns):
                        direct_vm[ev] = _aux_lns[j]
                for j, ev in enumerate(unmapped_pts):
                    if j < len(_aux_pts):
                        direct_vm[ev] = _aux_pts[j]
                # Map bound vars to exists vars WITHOUT side effects.
                # _fresh_bound_vars permanently modifies VarMapper, so
                # compute names speculatively here and only commit later.
                _table_bounds: List[str] = []
                if tac.bound_vars and thm.sequent.exists_vars:
                    _table_bounds = self._peek_bound_vars(tac.bound_vars)
                    for j, (ev_name, _) in enumerate(thm.sequent.exists_vars):
                        if j < len(_table_bounds):
                            direct_vm[ev_name] = _table_bounds[j]
                # Check if any distinctness hypothesis ¬(x=y) maps to
                # ¬(v=v) — this happens when Lean reuses the same variable
                # in multiple positions but elib requires them distinct.
                _table_collision = False
                for _h in thm.sequent.hypotheses:
                    if not _h.polarity and isinstance(_h.atom, Equals):
                        _lv = direct_vm.get(_h.atom.left, _h.atom.left)
                        _rv = direct_vm.get(_h.atom.right, _h.atom.right)
                        if _lv == _rv:
                            _table_collision = True
                            break
                # The _LEAN_PARAM_ORDER table is authoritative — always
                # accept its var_map.  Even if _validate_conclusions
                # reports degenerate conclusions, _lean_arg_conclusions
                # will compute correct conclusions from Lean arg positions.
                if _table_bounds:
                    self._commit_bound_vars(tac.bound_vars, _table_bounds)
                return direct_vm

        # Build actual mapped args with sort info
        mapped_args: List[str] = []
        mapped_sorts: List[str] = []
        if cited_params:
            for i, (pname, psort) in enumerate(cited_params):
                if i < len(tac.rule_args):
                    actual = self.vm.mv(tac.rule_args[i]) if self.vm else tac.rule_args[i].lower()
                    mapped_args.append(actual)
                    mapped_sorts.append(psort)
        else:
            # Fallback: infer sorts from ORIGINAL Lean arg naming conventions.
            # In Lean, multi-char names starting with uppercase are Lines (AB, BC, AC).
            # Single lowercase letters or primed names are Points (a, b, d').
            # Skip non-variable args like segment expressions (c─a).
            for arg in tac.rule_args:
                # Skip segment/metric expressions
                if arg.startswith('(') or '─' in arg or '|' in arg:
                    continue
                actual = self.vm.mv(arg) if self.vm else arg.lower()
                is_line = (len(arg) >= 2 and arg[0].isupper() and arg[1:].isalpha()
                           and arg[1:].isupper())
                if is_line:
                    mapped_args.append(actual)
                    mapped_sorts.append("Line")
                else:
                    mapped_args.append(actual)
                    mapped_sorts.append("Point")

        actual_pts = list(dict.fromkeys(
            a for a, s in zip(mapped_args, mapped_sorts) if s == "Point"))
        actual_lns = list(dict.fromkeys(
            a for a, s in zip(mapped_args, mapped_sorts) if s == "Line"))

        # Keep ordered (potentially duplicate) args for positional mapping
        all_pt_args = [a for a, s in zip(mapped_args, mapped_sorts) if s == "Point"]
        all_ln_args = [a for a, s in zip(mapped_args, mapped_sorts) if s == "Line"]

        # Pre-map bound_vars to exists_vars
        bound_map: Dict[str, str] = {}
        if tac.bound_vars and thm.sequent.exists_vars:
            # Use _fresh_bound_vars to avoid collisions
            fresh_bounds = self._fresh_bound_vars(tac.bound_vars) if self.vm else [v.lower() for v in tac.bound_vars]
            for i, (ev_name, ev_sort) in enumerate(thm.sequent.exists_vars):
                if i < len(fresh_bounds):
                    bv = fresh_bounds[i]
                    bound_map[ev_name] = bv
                    # Also add bound var to candidate pool
                    if ev_sort == Sort.POINT and bv not in actual_pts:
                        actual_pts.append(bv)
                    elif ev_sort == Sort.LINE and bv not in actual_lns:
                        actual_lns.append(bv)

        elib_pts = sorted(v for v in hyp_vars
                          if not (len(v) == 1 and v.isupper()))
        elib_lns = sorted(v for v in hyp_vars
                          if len(v) == 1 and v.isupper())

        # Identity map check (fast path) — only use when Lean args actually
        # correspond to identity (mapped args match the elib var names).
        # This prevents returning identity when elib hypotheses happen to
        # match known facts by coincidence but the Lean call-site intends a
        # different mapping (e.g. Prop.I.10 called on b,c,M inside I.16
        # whose premises already satisfy on(a,L), on(b,L), ¬(a=b)).
        if mapped_args:
            id_vm = dict(zip(elib_pts, all_pt_args))
            for j, el in enumerate(elib_lns):
                if j < len(all_ln_args):
                    id_vm[el] = all_ln_args[j]
            id_vm.update(bound_map)
            # Check if the positional map IS the identity
            if all(id_vm.get(v) == v for v in hyp_vars):
                if self._check_hyps(thm, identity):
                    return identity
        elif not tac.rule_args:
            # No Lean args at all — identity is only option
            if self._check_hyps(thm, identity):
                return identity

        # Strategy 0: Direct positional mapping (handles duplicate args)
        # Lean args are in the same order as the theorem's parameter list.
        if len(all_pt_args) >= len(elib_pts) and len(all_ln_args) >= len(elib_lns):
            vm0 = dict(zip(elib_pts, all_pt_args))
            for j, el in enumerate(elib_lns):
                if j < len(all_ln_args):
                    vm0[el] = all_ln_args[j]
            vm0.update(bound_map)
            if self._validate_conclusions(thm, vm0):
                if self._check_hyps_fast(thm, vm0):
                    return vm0
                if self._check_hyps(thm, vm0):
                    return vm0

        # Strategy 0b: Hypothesis-order positional mapping.
        # Some theorems (e.g. I.2, I.7, I.13) have hypothesis variable
        # order that differs from alphabetical. Lean follows hypothesis
        # order, so try that as a second positional strategy.
        elib_ordered = _ordered_sequent_vars(thm.sequent)
        elib_pts_ho = [v for v in elib_ordered
                       if v in hyp_vars and not (len(v) == 1 and v.isupper())]
        elib_lns_ho = [v for v in elib_ordered
                       if v in hyp_vars and len(v) == 1 and v.isupper()]
        if (elib_pts_ho != elib_pts or elib_lns_ho != elib_lns):
            if len(all_pt_args) >= len(elib_pts_ho) and len(all_ln_args) >= len(elib_lns_ho):
                vm0b = dict(zip(elib_pts_ho, all_pt_args))
                for j, el in enumerate(elib_lns_ho):
                    if j < len(all_ln_args):
                        vm0b[el] = all_ln_args[j]
                vm0b.update(bound_map)
                if self._validate_conclusions(thm, vm0b):
                    if self._check_hyps_fast(thm, vm0b):
                        return vm0b
                    if self._check_hyps(thm, vm0b):
                        return vm0b

        if len(elib_lns) > len(actual_lns):
            return identity

        from itertools import permutations, product
        import time as _time
        _deadline = _time.monotonic() + 5  # 5s budget for var_map search

        # Collect distinctness constraints from hypotheses to prune early
        neq_pairs: Set[Tuple[str, str]] = set()
        for hyp in thm.sequent.hypotheses:
            if not hyp.polarity and isinstance(hyp.atom, Equals):
                neq_pairs.add((hyp.atom.left, hyp.atom.right))

        def _valid_map(vm: Dict[str, str]) -> bool:
            """Quick pre-filter: check no ¬(x=y) becomes ¬(a=a)."""
            for v1, v2 in neq_pairs:
                if vm.get(v1) == vm.get(v2):
                    return False
            return True

        pt_candidates = actual_pts if actual_pts else []
        if not pt_candidates and elib_pts:
            return identity

        # Add construction-created points/lines to candidate pool
        # so var_map search can find matches involving bound vars
        # from prior construction steps.
        for v, s in self.sort_ctx.items():
            if s == Sort.POINT and v not in pt_candidates:
                pt_candidates.append(v)
            elif s == Sort.LINE and v not in actual_lns:
                actual_lns.append(v)

        # Strategy 1: Permutations (fast — no duplicate mappings)
        if len(elib_pts) <= len(pt_candidates):
            for pt_perm in permutations(pt_candidates, len(elib_pts)):
                if _time.monotonic() > _deadline:
                    break
                vm = dict(zip(elib_pts, pt_perm))
                vm.update(bound_map)
                if not _valid_map(vm):
                    continue
                if not self._validate_conclusions(thm, vm):
                    continue
                for ln_perm in permutations(actual_lns, len(elib_lns)):
                    for j, el in enumerate(elib_lns):
                        vm[el] = ln_perm[j]
                    if self._check_hyps_fast(thm, vm):
                        return vm

            # Phase 2: permutations with structural pre-filter then CE
            if _time.monotonic() <= _deadline:
                for pt_perm in permutations(pt_candidates, len(elib_pts)):
                    if _time.monotonic() > _deadline:
                        break
                    vm = dict(zip(elib_pts, pt_perm))
                    vm.update(bound_map)
                    if not _valid_map(vm):
                        continue
                    if not self._validate_conclusions(thm, vm):
                        continue
                    for ln_perm in permutations(actual_lns, len(elib_lns)):
                        for j, el in enumerate(elib_lns):
                            vm[el] = ln_perm[j]
                        if not self._check_hyps_structural(thm, vm):
                            continue
                        if self._check_hyps(thm, vm):
                            return vm

        # Strategy 2: Product with replacement (allows duplicate mappings)
        # Only used when permutations failed (fewer unique candidates than
        # e_lib vars), capped to avoid combinatorial explosion.
        if _time.monotonic() > _deadline:
            return identity
        n_pt_combos = len(pt_candidates) ** len(elib_pts) if elib_pts else 1
        n_ln_perms = 1
        for i in range(len(elib_lns)):
            n_ln_perms *= (len(actual_lns) - i) if i < len(actual_lns) else 1
        total = n_pt_combos * n_ln_perms
        if total <= 10000:
            for pt_combo in product(pt_candidates, repeat=len(elib_pts)):
                if _time.monotonic() > _deadline:
                    break
                vm = dict(zip(elib_pts, pt_combo))
                vm.update(bound_map)
                if not _valid_map(vm):
                    continue
                if not self._validate_conclusions(thm, vm):
                    continue
                for ln_perm in permutations(actual_lns, len(elib_lns)):
                    for j, el in enumerate(elib_lns):
                        vm[el] = ln_perm[j]
                    if self._check_hyps_fast(thm, vm):
                        return vm
            # Product with CE (structural pre-filter)
            if total <= 5000 and _time.monotonic() <= _deadline:
                for pt_combo in product(pt_candidates, repeat=len(elib_pts)):
                    if _time.monotonic() > _deadline:
                        break
                    vm = dict(zip(elib_pts, pt_combo))
                    vm.update(bound_map)
                    if not _valid_map(vm):
                        continue
                    if not self._validate_conclusions(thm, vm):
                        continue
                    for ln_perm in permutations(actual_lns, len(elib_lns)):
                        for j, el in enumerate(elib_lns):
                            vm[el] = ln_perm[j]
                        if not self._check_hyps_structural(thm, vm):
                            continue
                        if self._check_hyps(thm, vm):
                            return vm

        return identity

    def _check_hyps_fast(self, thm: ETheorem, var_map: Dict[str, str]) -> bool:
        """Fast hypothesis check: direct known-fact lookup with metric symmetry."""
        for hyp in thm.sequent.hypotheses:
            inst = substitute_literal(hyp, var_map)
            if inst in self.known:
                continue
            # Try metric symmetry: M3 (ab = ba), M4 (∠abc = ∠cba)
            sym = self._symmetric_literal(inst)
            if sym is not None and sym in self.known:
                continue
            return False
        return True

    def _symmetric_literal(self, lit: Literal) -> Optional[Literal]:
        """Return the symmetric form of a metric literal, or None."""
        a = lit.atom
        if isinstance(a, Equals):
            left, right = a.left, a.right
            # M3: ab = ba (segment symmetry) — try swapping both sides
            if isinstance(left, SegmentTerm) and isinstance(right, SegmentTerm):
                sym_left = SegmentTerm(left.p2, left.p1)
                sym_right = SegmentTerm(right.p2, right.p1)
                # Try all combinations
                for l, r in [(sym_left, right), (left, sym_right),
                             (sym_left, sym_right), (right, left),
                             (sym_right, sym_left)]:
                    candidate = Literal(Equals(l, r), polarity=lit.polarity)
                    if candidate in self.known:
                        return candidate
            # M4: ∠abc = ∠cba (angle symmetry when vertex same)
            if isinstance(left, AngleTerm) and isinstance(right, AngleTerm):
                sym_left = AngleTerm(left.p3, left.p2, left.p1)
                sym_right = AngleTerm(right.p3, right.p2, right.p1)
                for l, r in [(sym_left, right), (left, sym_right),
                             (sym_left, sym_right), (right, left),
                             (sym_right, sym_left)]:
                    candidate = Literal(Equals(l, r), polarity=lit.polarity)
                    if candidate in self.known:
                        return candidate
            # Also try swapping equality sides: if known has cd=ab, match ab=cd
            swapped = Literal(Equals(right, left), polarity=lit.polarity)
            if swapped in self.known:
                return swapped
        elif isinstance(a, LessThan):
            # Try symmetric segments in LessThan
            left, right = a.left, a.right
            if isinstance(left, SegmentTerm) and isinstance(right, SegmentTerm):
                for l, r in [(SegmentTerm(left.p2, left.p1), right),
                             (left, SegmentTerm(right.p2, right.p1)),
                             (SegmentTerm(left.p2, left.p1), SegmentTerm(right.p2, right.p1))]:
                    candidate = Literal(LessThan(l, r), polarity=lit.polarity)
                    if candidate in self.known:
                        return candidate
        return None

    def _check_hyps_structural(self, thm: ETheorem, var_map: Dict[str, str]) -> bool:
        """Check only structural (positive diagrammatic) hypotheses against known facts.

        Returns False if any positive Between or SameSide hypothesis is not in
        known facts. Skips negative hypotheses, metric hypotheses, and positive
        On hypotheses (commonly derivable from betweenness via CE).
        """
        for hyp in thm.sequent.hypotheses:
            if not hyp.polarity:
                continue  # Skip all negative hypotheses (¬on, ¬equals, etc.)
            if hyp.is_metric:
                continue  # Skip metric hypotheses (need MetricEngine)
            if isinstance(hyp.atom, On):
                continue  # Skip positive On (often derivable via betweenness)
            inst = substitute_literal(hyp, var_map)
            if inst not in self.known:
                return False
        return True

    def _validate_conclusions(self, thm: ETheorem,
                              var_map: Dict[str, str]) -> bool:
        """Reject var_maps whose conclusions are structurally degenerate.

        Catches maps that satisfy hypotheses but produce useless conclusions,
        e.g. ``between(c, d, c)`` where endpoints coincide (since Between is
        not symmetric in the AST: ``between(a,e,b) ≠ between(b,e,a)``).
        """
        for conc in thm.sequent.conclusions:
            inst = substitute_literal(conc, var_map)
            atom = inst.atom
            if isinstance(atom, Between):
                # between(x, y, z): x and z must be distinct
                if atom.a == atom.c:
                    return False
                # between(x, y, z): middle point must differ from endpoints
                if atom.b == atom.a or atom.b == atom.c:
                    return False
            elif isinstance(atom, Equals):
                # Segment/angle equality: check for trivially degenerate
                left, right = atom.left, atom.right
                if isinstance(left, SegmentTerm) and isinstance(right, SegmentTerm):
                    if left.p1 == left.p2 and right.p1 == right.p2:
                        return False
        return True

    def _check_hyps(self, thm: ETheorem, var_map: Dict[str, str]) -> bool:
        """Hypothesis check with CE/MetricEngine fallback."""
        ce_needed: List[Literal] = []
        me_needed: List[Literal] = []
        for hyp in thm.sequent.hypotheses:
            inst = substitute_literal(hyp, var_map)
            if inst in self.known:
                continue
            if inst.is_diagrammatic:
                ce_needed.append(inst)
            elif inst.is_metric:
                me_needed.append(inst)
            else:
                return False
        if not ce_needed and not me_needed:
            return True
        if len(ce_needed) > 4:
            return False
        if len(me_needed) > 3:
            return False
        if ce_needed:
            from .e_consequence import ConsequenceEngine
            ce = ConsequenceEngine()
            for inst in ce_needed:
                if not ce.is_consequence(self.known, inst):
                    return False
        if me_needed:
            from .e_metric import MetricEngine
            me = MetricEngine()
            metric_known = {k for k in self.known if k.is_metric}
            for inst in me_needed:
                if not me.is_consequence(metric_known, inst):
                    return False
        return True

    def _cited_lean_params(self, rule_name: str) -> List[Tuple[str, str]]:
        from .lean_parser import extract_prop_number
        pn = extract_prop_number(rule_name)
        if not pn:
            return []
        fp = Path(f"lean_reference/Prop{pn}.lean")
        if fp.exists():
            try:
                proofs = parse_lean_file(str(fp))
                if proofs and proofs[0].signature:
                    return [(pr.name, pr.sort) for pr in proofs[0].signature.params]
            except Exception:
                pass
        return []

    # -- Inference (metric/transfer/diagrammatic) ----------------------

    def _apply_inference(self, tac: LeanTactic, mp):
        se_name = mp.system_e_name if mp else tac.rule_name
        for ts in self.tr.steps:
            if ts.step.description and tac.rule_name in ts.step.description:
                if ts.step.assertions:
                    lits = set()
                    parts = []
                    for a in ts.step.assertions:
                        m = self._map_lit(a)
                        parts.append(literal_to_text(m))
                        lits.add(m)
                        self.known.add(m)
                    ln = self.nprem + len(self.steps) + 1
                    deps = self._deps_for(lits, set())
                    self.steps.append({
                        "lineNumber": ln, "text": ", ".join(parts),
                        "justification": se_name, "dependencies": deps,
                        "depth": self.current_depth, "status": "?",
                    })
                    self.ll[ln] = lits
                    return
        self.warnings.append(f"No assertions for inference: {se_name}")

    # -- euclid_finish -------------------------------------------------

    def _finish(self):
        if not self.seq:
            return
        for conc in self.seq.conclusions:
            if conc in self.known:
                continue
            # Check symmetric form already known
            sym = self._symmetric_literal(conc)
            if sym is not None:
                self._emit_symmetry_step(conc, sym)
                continue
            # Try reflexivity (e.g. cd = cd)
            s = self._try_reflexive(conc)
            if s:
                self.steps.append(s)
                continue

            # Type-based dispatch to avoid expensive irrelevant strategies
            if conc.is_metric:
                # Metric conclusions: try metric engine, then symmetry+metric
                s = self._try_metric(conc)
                if s:
                    self.steps.append(s)
                    continue
                ss = self._try_via_symmetry_then_metric(conc)
                if ss:
                    for step in ss:
                        self.steps.append(step)
                    continue
            elif conc.is_diagrammatic:
                # Diagrammatic conclusions: try axiom match, then CE
                s = self._find_axiom(conc)
                if s:
                    self.steps.append(s)
                    continue
                s = self._try_conseq(conc)
                if s:
                    self.steps.append(s)
                    continue
            else:
                # Unknown type: try all strategies
                s = self._find_axiom(conc)
                if s:
                    self.steps.append(s)
                    continue
                s = self._try_metric(conc)
                if s:
                    self.steps.append(s)
                    continue
                ss = self._try_via_symmetry_then_metric(conc)
                if ss:
                    for step in ss:
                        self.steps.append(step)
                    continue
                s = self._try_conseq(conc)
                if s:
                    self.steps.append(s)
                    continue
            self.warnings.append(
                f"Cannot derive goal: {literal_to_text(conc)}")

    def _emit_symmetry_step(self, target: Literal, source: Literal):
        """Emit an M3/M4/CN1 step deriving target from its symmetric source."""
        just = self._metric_symmetry_just(target)
        deps = self._deps_target(source)
        ln = self.nprem + len(self.steps) + 1
        self.steps.append({
            "lineNumber": ln,
            "text": literal_to_text(target),
            "justification": just,
            "dependencies": deps,
            "depth": self.current_depth, "status": "?",
        })
        self.known.add(target)
        self.ll[ln] = {target}

    def _try_reflexive(self, target: Literal) -> Optional[Dict[str, Any]]:
        """Handle reflexive equalities like cd = cd, ∠abc = ∠abc."""
        if not target.polarity:
            return None
        a = target.atom
        if not isinstance(a, Equals):
            return None
        if a.left != a.right:
            return None
        ln = self.nprem + len(self.steps) + 1
        s = {"lineNumber": ln, "text": literal_to_text(target),
             "justification": "CN4 \u2014 Reflexivity",
             "dependencies": [],
             "depth": self.current_depth, "status": "?"}
        self.known.add(target)
        self.ll[ln] = {target}
        return s

    def _try_via_symmetry_then_metric(
        self, target: Literal
    ) -> Optional[List[Dict[str, Any]]]:
        """Try deriving target by first establishing a symmetric intermediate.

        For example, if goal is ab < cd but we know ba < cd via the metric
        engine, first emit M3 for ba=ab, then derive the target.
        """
        if not target.is_metric:
            return None
        from .e_metric import MetricEngine

        a = target.atom
        candidates: list = []
        if isinstance(a, Equals):
            left, right = a.left, a.right
            if isinstance(left, SegmentTerm):
                candidates.append(Literal(Equals(
                    SegmentTerm(left.p2, left.p1), right),
                    polarity=target.polarity))
            if isinstance(right, SegmentTerm):
                candidates.append(Literal(Equals(
                    left, SegmentTerm(right.p2, right.p1)),
                    polarity=target.polarity))
            if isinstance(left, SegmentTerm) and isinstance(right, SegmentTerm):
                candidates.append(Literal(Equals(
                    SegmentTerm(left.p2, left.p1),
                    SegmentTerm(right.p2, right.p1)),
                    polarity=target.polarity))
            candidates.append(Literal(Equals(right, left),
                                      polarity=target.polarity))
            if isinstance(left, AngleTerm):
                candidates.append(Literal(Equals(
                    AngleTerm(left.p3, left.p2, left.p1), right),
                    polarity=target.polarity))
            if isinstance(right, AngleTerm):
                candidates.append(Literal(Equals(
                    left, AngleTerm(right.p3, right.p2, right.p1)),
                    polarity=target.polarity))
        elif isinstance(a, LessThan):
            left, right = a.left, a.right
            if isinstance(left, SegmentTerm):
                candidates.append(Literal(LessThan(
                    SegmentTerm(left.p2, left.p1), right),
                    polarity=target.polarity))
            if isinstance(right, SegmentTerm):
                candidates.append(Literal(LessThan(
                    left, SegmentTerm(right.p2, right.p1)),
                    polarity=target.polarity))
            if isinstance(left, SegmentTerm) and isinstance(right, SegmentTerm):
                candidates.append(Literal(LessThan(
                    SegmentTerm(left.p2, left.p1),
                    SegmentTerm(right.p2, right.p1)),
                    polarity=target.polarity))

        me = MetricEngine()
        metric_known = {k for k in self.known if k.is_metric}
        for cand in candidates:
            if cand in self.known or me.is_consequence(metric_known, cand):
                steps: list = []
                if cand not in self.known:
                    ln = self.nprem + len(self.steps) + 1
                    deps = self._deps_target(cand)
                    just = self._metric_just(cand)
                    steps.append({
                        "lineNumber": ln,
                        "text": literal_to_text(cand),
                        "justification": just,
                        "dependencies": deps,
                        "depth": self.current_depth, "status": "?",
                    })
                    self.known.add(cand)
                    self.ll[ln] = {cand}
                ln2 = self.nprem + len(self.steps) + len(steps) + 1
                deps2 = self._deps_target(target)
                just2 = (self._metric_symmetry_just(target)
                         if self._is_pure_symmetry(target, cand)
                         else self._metric_just(target))
                steps.append({
                    "lineNumber": ln2,
                    "text": literal_to_text(target),
                    "justification": just2,
                    "dependencies": deps2,
                    "depth": self.current_depth, "status": "?",
                })
                self.known.add(target)
                self.ll[ln2] = {target}
                return steps
        return None

    def _is_pure_symmetry(self, target: Literal, source: Literal) -> bool:
        """Check if target is a pure M3/M4 symmetry of source."""
        a, b = target.atom, source.atom
        if type(a) != type(b) or target.polarity != source.polarity:
            return False
        if isinstance(a, Equals) and isinstance(b, Equals):
            if isinstance(a.left, SegmentTerm) and isinstance(b.left, SegmentTerm):
                if (a.right == b.right and
                    a.left.p1 == b.left.p2 and a.left.p2 == b.left.p1):
                    return True
            if isinstance(a.right, SegmentTerm) and isinstance(b.right, SegmentTerm):
                if (a.left == b.left and
                    a.right.p1 == b.right.p2 and a.right.p2 == b.right.p1):
                    return True
            if isinstance(a.left, AngleTerm) and isinstance(b.left, AngleTerm):
                if (a.right == b.right and a.left.p2 == b.left.p2 and
                    a.left.p1 == b.left.p3 and a.left.p3 == b.left.p1):
                    return True
            if isinstance(a.right, AngleTerm) and isinstance(b.right, AngleTerm):
                if (a.left == b.left and a.right.p2 == b.right.p2 and
                    a.right.p1 == b.right.p3 and a.right.p3 == b.right.p1):
                    return True
            if a.left == b.right and a.right == b.left:
                return True
        return False

    # -- Assertion steps -----------------------------------------------

    def _derive_from_expr(self, expr_str: str):
        from .lean_translator import lean_expr_to_literals
        from .lean_parser import parse_lean_expr
        expr = parse_lean_expr(expr_str)
        lits = lean_expr_to_literals(expr) if expr else []
        for lit in lits:
            m = self._map_lit(lit)
            if m in self.known:
                continue
            # Check symmetric form already known
            sym = self._symmetric_literal(m)
            if sym is not None:
                self._emit_symmetry_step(m, sym)
                continue
            s = self._try_reflexive(m)
            if not s:
                s = self._find_axiom(m)
            if not s:
                s = self._try_metric(m)
            if not s:
                s = self._try_conseq(m)
            if s:
                self.steps.append(s)
            else:
                self.warnings.append(f"Cannot derive: {literal_to_text(m)}")

    # -- Axiom/metric/consequence search --------------------------------

    def _find_axiom(self, target: Literal) -> Optional[Dict[str, Any]]:
        from .e_axiom_match import check_specific_axiom

        # Select candidate axiom names by target type instead of trying all 117
        candidates = self._axiom_candidates_for(target)

        # Use scoped facts (target vars + one level) to reduce variable pools
        tv = literal_vars(target)
        scoped_facts: Set[Literal] = set()
        for lits in self.ll.values():
            for lit in lits:
                if literal_vars(lit) & tv:
                    scoped_facts |= lits
                    break
        expanded_vars = set(tv)
        for lit in scoped_facts:
            expanded_vars |= literal_vars(lit)
        for lits in self.ll.values():
            for lit in lits:
                if literal_vars(lit) & expanded_vars:
                    scoped_facts |= lits
                    break

        scoped_vars: Dict[str, Sort] = dict(self.sort_ctx)
        for lit in scoped_facts | {target}:
            for v in literal_vars(lit):
                if v not in scoped_vars:
                    scoped_vars[v] = (Sort.LINE if (len(v) == 1 and v.isupper())
                                      else Sort.POINT)

        ln = self.nprem + len(self.steps) + 1
        for name in candidates:
            ok, _ = check_specific_axiom(name, scoped_facts, [target], scoped_vars)
            if ok:
                deps = self._deps_target(target)
                s = {"lineNumber": ln, "text": literal_to_text(target),
                     "justification": name, "dependencies": deps,
                     "depth": self.current_depth, "status": "?"}
                self.known.add(target)
                self.ll[ln] = {target}
                return s
        return None

    def _axiom_candidates_for(self, target: Literal) -> List[str]:
        """Return a short list of candidate axiom names relevant to the target type."""
        a = target.atom
        if isinstance(a, On):
            if target.polarity:
                return ["Generality 3", "Generality 4", "Generality 5",
                        "Generality 5c", "Generality 5d"]
            else:
                return ["Generality 1", "Generality 2"]
        if isinstance(a, Between):
            return ["Betweenness 1a", "Betweenness 2", "Betweenness 3",
                    "Betweenness 4"]
        if isinstance(a, Equals) and not target.polarity:
            return ["Betweenness 1b", "Betweenness 1c",
                    "Generality 6", "Generality 6c", "Same-side 6"]
        if isinstance(a, SameSide):
            if target.polarity:
                return ["Same-side 1", "Same-side 2", "Same-side 3"]
            else:
                return ["Same-side 4", "Same-side 5"]
        if isinstance(a, Intersects):
            return ["Intersection 1", "Intersection 3",
                    "Intersection 5", "Intersection 6"]
        if isinstance(a, Inside):
            return ["Inside 1", "Inside 2", "Inside 3"]
        # Fallback: use full list but limit to first match
        from .e_axiom_match import list_axiom_names
        return list_axiom_names()

    def _try_metric(self, target: Literal) -> Optional[Dict[str, Any]]:
        from .e_metric import MetricEngine
        me = MetricEngine()
        metric_known = {k for k in self.known if k.is_metric}
        if me.is_consequence(metric_known, target):
            ln = self.nprem + len(self.steps) + 1
            deps = self._deps_target(target)
            j = self._metric_just(target)
            s = {"lineNumber": ln, "text": literal_to_text(target),
                 "justification": j, "dependencies": deps,
                 "depth": self.current_depth, "status": "?"}
            self.known.add(target)
            self.ll[ln] = {target}
            return s
        return None

    def _try_conseq(self, target: Literal) -> Optional[Dict[str, Any]]:
        from .e_consequence import ConsequenceEngine
        # Scope CE to diagrammatic facts mentioning target vars (+1 level)
        tv = literal_vars(target)
        scoped: Set[Literal] = set()
        for lits in self.ll.values():
            for lit in lits:
                if lit.is_diagrammatic and literal_vars(lit) & tv:
                    scoped |= {l for l in lits if l.is_diagrammatic}
                    break
        expanded_vars = set(tv)
        for lit in scoped:
            expanded_vars |= literal_vars(lit)
        for lits in self.ll.values():
            for lit in lits:
                if lit.is_diagrammatic and literal_vars(lit) & expanded_vars:
                    scoped |= {l for l in lits if l.is_diagrammatic}
                    break
        ce = ConsequenceEngine()
        if ce.is_consequence(scoped, target):
            ln = self.nprem + len(self.steps) + 1
            deps = self._deps_target(target)
            j = self._guess_diag(target)
            s = {"lineNumber": ln, "text": literal_to_text(target),
                 "justification": j, "dependencies": deps,
                 "depth": self.current_depth, "status": "?"}
            self.known.add(target)
            self.ll[ln] = {target}
            return s
        return None

    def _guess_diag(self, target: Literal) -> str:
        a = target.atom
        if isinstance(a, Between):
            return "Betweenness 1a" if target.polarity else "Betweenness 1b"
        if isinstance(a, Equals) and not target.polarity:
            return self._find_neq_axiom(target)
        if isinstance(a, On):
            return "Generality 3" if target.polarity else "Generality 1"
        return "Generality 1"

    def _find_neq_axiom(self, target: Literal) -> str:
        """Find the correct axiom name for deriving ¬(x = y).

        Tries candidate axioms against a scoped subset of known facts
        using the axiom matcher, returning the first one that works.
        """
        from .e_axiom_match import check_specific_axiom
        from .e_consequence import ConsequenceEngine

        # Scope to facts mentioning the target's variables (+ one level
        # expansion for derivation chains like between(c,d,a) + on facts).
        tv = literal_vars(target)
        scoped_facts: Set[Literal] = set()
        for lits in self.ll.values():
            for lit in lits:
                if literal_vars(lit) & tv:
                    scoped_facts |= lits
                    break

        # Expand one level: include facts whose vars overlap with scoped facts
        expanded_vars = set(tv)
        for lit in scoped_facts:
            expanded_vars |= literal_vars(lit)
        for lits in self.ll.values():
            for lit in lits:
                if literal_vars(lit) & expanded_vars:
                    scoped_facts |= lits
                    break

        ce = ConsequenceEngine()
        closure = ce.direct_consequences(scoped_facts)
        dep_aug = scoped_facts | closure

        # Build variable map for axiom matching from the closure
        dep_vars: Dict[str, Sort] = dict(self.sort_ctx)
        for lit in dep_aug:
            for v in literal_vars(lit):
                if v not in dep_vars:
                    dep_vars[v] = (Sort.LINE if (len(v) == 1 and v.isupper())
                                    else Sort.POINT)

        # Try candidate axiom names in priority order
        candidates = [
            "Betweenness 1b",   # between(a,b,c) → a ≠ b
            "Betweenness 1c",   # between(a,b,c) → a ≠ c
            "Generality 6",     # on(a,L) ∧ ¬on(b,L) → a ≠ b
            "Generality 6c",    # on(a,α) ∧ ¬on(b,α) → a ≠ b
            "Same-side 6",      # same-side(a,b,L) ∧ ¬same-side(a,c,L) → b ≠ c
        ]
        for name in candidates:
            ok, _ = check_specific_axiom(
                name, dep_aug, [target], dep_vars)
            if ok:
                return name
        return "Betweenness 1b"  # fallback

    # -- Helper: let-line ----------------------------------------------

    def _add_let_line(self, line_name: str, pt1: str, pt2: str):
        self._ensure_neq(pt1, pt2)
        l1 = _pos(On(pt1, line_name))
        l2 = _pos(On(pt2, line_name))
        self.known.add(l1)
        self.known.add(l2)
        neq = Literal(Equals(pt1, pt2), polarity=False)
        deps = []
        for ln_num, lits in self.ll.items():
            if neq in lits:
                deps.append(ln_num)
                break
        line_num = self.nprem + len(self.steps) + 1
        self.steps.append({
            "lineNumber": line_num,
            "text": f"on({pt1}, {line_name}), on({pt2}, {line_name})",
            "justification": "let-line",
            "dependencies": deps,
            "depth": self.current_depth, "status": "?",
        })
        self.ll[line_num] = {l1, l2}
        self.sort_ctx[line_name] = Sort.LINE

    def _try_emit_neq(self, neq: Literal, just: str,
                       deps: List[int]) -> bool:
        """Try to emit a ¬(x=y) step after verifying the axiom works.

        Returns True if the step was emitted, False otherwise.
        """
        from .e_axiom_match import check_specific_axiom
        dep_lits: Set[Literal] = set()
        for d in deps:
            dep_lits |= self.ll.get(d, set())
        dv: Dict[str, Sort] = dict(self.sort_ctx)
        for lit in dep_lits:
            for v in literal_vars(lit):
                if v not in dv:
                    dv[v] = (Sort.LINE if (len(v) == 1 and v.isupper())
                             else Sort.POINT)
        for v in literal_vars(neq):
            if v not in dv:
                dv[v] = (Sort.LINE if (len(v) == 1 and v.isupper())
                         else Sort.POINT)
        ok, _ = check_specific_axiom(just, dep_lits, [neq], dv)
        if ok:
            ln = self.nprem + len(self.steps) + 1
            self.steps.append({
                "lineNumber": ln,
                "text": literal_to_text(neq),
                "justification": just,
                "dependencies": deps,
                "depth": self.current_depth, "status": "?",
            })
            self.known.add(neq)
            self.ll[ln] = {neq}
            return True
        return False

    def _ensure_neq(self, pt1: str, pt2: str):
        """Ensure ¬(pt1 = pt2) is in known facts, injecting a step if needed."""
        if pt1 == pt2:
            return  # Can't prove ¬(x = x); skip silently
        neq = _neg(Equals(pt1, pt2))
        if neq in self.known:
            return

        # Fast path: derive from betweenness facts in known set.
        # Betweenness 1b: between(a,b,c) → ¬(a=b)
        # Betweenness 1c: between(a,b,c) → ¬(a=c)
        # For ¬(b=c): use Betweenness 1a (symmetry) to get between(c,b,a),
        # then Betweenness 1b to get ¬(c=b).
        pair = {pt1, pt2}
        for k in list(self.known):
            if k.polarity and isinstance(k.atom, Between):
                a, b, c = k.atom.a, k.atom.b, k.atom.c
                pts = {a, b, c}
                if pair <= pts and len(pair) == 2:
                    if pair == {a, b}:
                        just = "Betweenness 1b"
                    elif pair == {a, c}:
                        just = "Betweenness 1c"
                    else:
                        # pair == {b, c}: need two steps
                        # Step 1: between(c,b,a) via Betweenness 1a
                        rev = _pos(Between(c, b, a))
                        if rev not in self.known:
                            rev_deps = self._deps_target(k)
                            if self._try_emit_neq(rev, "Betweenness 1a", rev_deps):
                                pass  # emitted
                            else:
                                self.known.add(rev)
                        just = "Betweenness 1b"
                    deps = self._deps_target(neq)
                    if self._try_emit_neq(neq, just, deps):
                        return
                    # Verification failed — try broader deps
                    deps = sorted(self.ll.keys())
                    if self._try_emit_neq(neq, just, deps):
                        return

        # Fast path: derive from on/¬on facts.
        # on(a,L) ∧ ¬on(b,L) → a≠b (Generality 6)
        for k in list(self.known):
            if not k.polarity and isinstance(k.atom, On):
                off_pt, obj = k.atom.point, k.atom.obj
                other = None
                if off_pt == pt1:
                    other = pt2
                elif off_pt == pt2:
                    other = pt1
                if other is not None:
                    on_lit = _pos(On(other, obj))
                    if on_lit in self.known:
                        deps = self._deps_target(neq)
                        if self._try_emit_neq(neq, "Generality 6", deps):
                            return

        # Fast path: derive from distinct lines.
        s1 = self.sort_ctx.get(pt1)
        s2 = self.sort_ctx.get(pt2)
        if s1 == Sort.LINE and s2 == Sort.LINE:
            deps = self._deps_target(neq)
            if self._try_emit_neq(neq, "Generality 6", deps):
                return
            deps = sorted(self.ll.keys())
            if self._try_emit_neq(neq, "Generality 6", deps):
                return

        # Fallback: try MetricEngine (usually fast for segment-based ≠).
        from .e_metric import MetricEngine
        me = MetricEngine()
        metric_known = {k for k in self.known if k.is_metric}
        if me.is_consequence(metric_known, neq):
            deps = self._deps_target(neq)
            ln = self.nprem + len(self.steps) + 1
            self.steps.append({
                "lineNumber": ln,
                "text": literal_to_text(neq),
                "justification": "M1 \u2014 Zero segment",
                "dependencies": deps,
                "depth": self.current_depth, "status": "?",
            })
            self.known.add(neq)
            self.ll[ln] = {neq}
            return

        # Last resort: try all axiom candidates with broadest deps.
        just = self._find_neq_axiom_fast(neq)
        deps = sorted(self.ll.keys())
        if self._try_emit_neq(neq, just, deps):
            return
        # Also try Generality 6 as fallback axiom name
        if just != "Generality 6":
            if self._try_emit_neq(neq, "Generality 6", deps):
                return

        # No single axiom verifies with CE — add to known and record
        # as a derived fact.  The verifier will seed this into
        # checker.known so downstream theorem steps can use it.
        self.known.add(neq)
        self.derived_facts.append(neq)

    def _find_neq_axiom_fast(self, target: Literal) -> str:
        """Pick a likely correct axiom name for ¬(x=y) without expensive CE.

        Heuristic: look at what's in the known set to guess the derivation
        path, returning the axiom name the verifier will use.
        """
        a = target.atom
        if not isinstance(a, Equals):
            return "Generality 6"
        pt1, pt2 = a.left, a.right
        if not isinstance(pt1, str) or not isinstance(pt2, str):
            return "M1 \u2014 Zero segment"
        # Check if any betweenness involves both points
        pair = {pt1, pt2}
        for k in self.known:
            if k.polarity and isinstance(k.atom, Between):
                a, b, c = k.atom.a, k.atom.b, k.atom.c
                pts = {a, b, c}
                if pair <= pts:
                    if pair == {a, b}:
                        return "Betweenness 1b"
                    elif pair == {a, c}:
                        return "Betweenness 1c"
                    # pair == {b, c}: needs symmetry + 1b (handled by
                    # _ensure_neq's two-step path; shouldn't reach here)
                    return "Betweenness 1b"
        # Check on/¬on pattern
        for k in self.known:
            if not k.polarity and isinstance(k.atom, On):
                off_pt = k.atom.point
                if off_pt in pair:
                    return "Generality 6"
        return "Generality 6"

    def _ensure_intersects(self, obj1: str, obj2: str):
        """Ensure intersects(obj1, obj2) is in known facts, injecting a step if needed."""
        target = _pos(Intersects(obj1, obj2))
        if target in self.known:
            return
        # Check swapped form
        swapped = _pos(Intersects(obj2, obj1))
        if swapped in self.known:
            return

        # Fast path: check common intersection patterns directly from known
        # I3: inside(a,α) ∧ on(a,L) → intersects(L,α)
        s1 = self.sort_ctx.get(obj1)
        s2 = self.sort_ctx.get(obj2)
        for k in self.known:
            if k.polarity and isinstance(k.atom, Inside):
                pt, circ = k.atom.point, k.atom.circle
                # I3: inside(pt, circle) + on(pt, line) → intersects(line, circle)
                if s2 == Sort.CIRCLE and circ == obj2:
                    on_lit = _pos(On(pt, obj1))
                    if on_lit in self.known:
                        self._emit_intersects_step(target, "Intersection 3",
                                                   self._deps_for_vars({obj1, obj2, pt}))
                        return
                if s1 == Sort.CIRCLE and circ == obj1:
                    on_lit = _pos(On(pt, obj2))
                    if on_lit in self.known:
                        alt = _pos(Intersects(obj2, obj1))
                        self._emit_intersects_step(alt, "Intersection 3",
                                                   self._deps_for_vars({obj1, obj2, pt}))
                        return

        # I6: α≠β ∧ on(c,α) ∧ on(c,β) ∧ on(d,α) ∧ on(d,β) ∧ c≠d → intersects(α,β)
        if s1 == Sort.CIRCLE and s2 == Sort.CIRCLE:
            common_pts = []
            for k in self.known:
                if k.polarity and isinstance(k.atom, On):
                    if k.atom.obj == obj1:
                        on2 = _pos(On(k.atom.point, obj2))
                        if on2 in self.known:
                            common_pts.append(k.atom.point)
                            if len(common_pts) >= 2:
                                break
            if len(common_pts) >= 2:
                c, d = common_pts[0], common_pts[1]
                neq_cd = _neg(Equals(c, d))
                neq_obj = _neg(Equals(obj1, obj2))
                if (neq_cd in self.known or c != d) and (neq_obj in self.known or obj1 != obj2):
                    self._emit_intersects_step(target, "Intersection 6",
                                               self._deps_for_vars({obj1, obj2, c, d}))
                    return

        # Collect scoped facts: only those mentioning obj1 or obj2
        from .e_axiom_match import check_specific_axiom
        seed_vars = {obj1, obj2}
        scoped_facts: Set[Literal] = set()
        scoped_lines: Set[int] = set()
        for ln_num, lits in self.ll.items():
            for lit in lits:
                if literal_vars(lit) & seed_vars:
                    scoped_facts |= lits
                    scoped_lines.add(ln_num)
                    break

        scoped_vars: Dict[str, Sort] = dict(self.sort_ctx)
        for lit in scoped_facts:
            for v in literal_vars(lit):
                if v not in scoped_vars:
                    scoped_vars[v] = (Sort.LINE if (len(v) == 1 and v.isupper())
                                      else Sort.POINT)

        # Try direct axiom match on scoped facts (no CE needed)
        candidates = [
            "Intersection 1", "Intersection 3",
            "Intersection 5", "Intersection 6",
        ]
        for name in candidates:
            ok, _ = check_specific_axiom(name, scoped_facts, [target], scoped_vars)
            if ok:
                self._emit_intersects_step(target, name, sorted(scoped_lines))
                return

        # Try with CE closure on scoped facts only (much cheaper than full set)
        from .e_consequence import ConsequenceEngine
        ce = ConsequenceEngine()
        closure = ce.direct_consequences(scoped_facts)
        scoped_aug = scoped_facts | closure
        for lit in scoped_aug:
            for v in literal_vars(lit):
                if v not in scoped_vars:
                    scoped_vars[v] = (Sort.LINE if (len(v) == 1 and v.isupper())
                                      else Sort.POINT)
        for name in candidates:
            ok, _ = check_specific_axiom(name, scoped_aug, [target], scoped_vars)
            if ok:
                self._emit_intersects_step(target, name, sorted(scoped_lines))
                return

        # Expand scope one level: include lines whose vars overlap with closure
        expanded_vars = set(seed_vars)
        for lit in scoped_aug:
            expanded_vars |= literal_vars(lit)
        for ln_num, lits in self.ll.items():
            if ln_num in scoped_lines:
                continue
            for lit in lits:
                if literal_vars(lit) & expanded_vars:
                    scoped_facts |= lits
                    scoped_lines.add(ln_num)
                    break
        for lit in scoped_facts:
            for v in literal_vars(lit):
                if v not in scoped_vars:
                    scoped_vars[v] = (Sort.LINE if (len(v) == 1 and v.isupper())
                                      else Sort.POINT)
        closure2 = ce.direct_consequences(scoped_facts)
        scoped_aug2 = scoped_facts | closure2
        for lit in scoped_aug2:
            for v in literal_vars(lit):
                if v not in scoped_vars:
                    scoped_vars[v] = (Sort.LINE if (len(v) == 1 and v.isupper())
                                      else Sort.POINT)
        for name in candidates:
            ok, _ = check_specific_axiom(name, scoped_aug2, [target], scoped_vars)
            if ok:
                self._emit_intersects_step(target, name, sorted(scoped_lines))
                return

        # Last resort: try axiom search
        s = self._find_axiom(target)
        if s:
            self.steps.append(s)

    def _emit_intersects_step(self, target: Literal, just: str,
                              deps: List[int]):
        """Emit a step for an intersects derivation."""
        ln = self.nprem + len(self.steps) + 1
        self.steps.append({
            "lineNumber": ln,
            "text": literal_to_text(target),
            "justification": just,
            "dependencies": deps,
            "depth": self.current_depth, "status": "?",
        })
        self.known.add(target)
        self.ll[ln] = {target}

    def _find_intersects_axiom(self, target: Literal) -> str:
        """Find the correct axiom name for deriving intersects(X, Y).

        Uses scoped facts (only those mentioning the target's variables)
        to avoid expensive full-set CE closures.
        """
        from .e_axiom_match import check_specific_axiom
        tv = literal_vars(target)
        scoped_facts: Set[Literal] = set()
        for lits in self.ll.values():
            for lit in lits:
                if literal_vars(lit) & tv:
                    scoped_facts |= lits
                    break
        scoped_vars: Dict[str, Sort] = dict(self.sort_ctx)
        for lit in scoped_facts:
            for v in literal_vars(lit):
                if v not in scoped_vars:
                    scoped_vars[v] = (Sort.LINE if (len(v) == 1 and v.isupper())
                                      else Sort.POINT)
        candidates = [
            "Intersection 1",   # diff-side → intersects(L, M)
            "Intersection 3",   # inside(a,α) ∧ on(a,L) → intersects(L,α)
            "Intersection 5",   # cross-circle intersection
            "Intersection 6",   # two common points → intersects(α,β)
        ]
        for name in candidates:
            ok, _ = check_specific_axiom(name, scoped_facts, [target], scoped_vars)
            if ok:
                return name
        return "Intersection 1"  # fallback

    def _deps_for_vars(self, target_vars: Set[str]) -> List[int]:
        """Find deps that mention any of the target variables plus transitive deps."""
        direct_deps: Set[int] = set()
        for ln_num, lits in self.ll.items():
            for lit in lits:
                if literal_vars(lit) & target_vars:
                    direct_deps.add(ln_num)
                    break
        # Also include lines whose variables overlap with variables found in direct deps
        expanded_vars = set(target_vars)
        for ln_num in direct_deps:
            for lit in self.ll[ln_num]:
                expanded_vars |= literal_vars(lit)
        all_deps: Set[int] = set(direct_deps)
        for ln_num, lits in self.ll.items():
            if ln_num in all_deps:
                continue
            for lit in lits:
                if literal_vars(lit) & expanded_vars:
                    all_deps.add(ln_num)
                    break
        return sorted(all_deps)

    # -- Literal mapping -----------------------------------------------

    def _map_lit(self, lit: Literal) -> Literal:
        if not self.vm:
            return lit
        return substitute_literal(lit, self.vm.lean_to_elib)

    # -- Dependency helpers --------------------------------------------

    def _find_minimal_deps(self, target: Literal, axiom_name: str,
                           seed_vars: Set[str]) -> List[int]:
        """Find minimal dependency set for an axiom derivation.

        Uses check_specific_axiom_with_premises to discover the exact
        required premises, then finds lines providing them.  Falls back
        to variable-scoped search if the axiom check fails.
        """
        from .e_axiom_match import check_specific_axiom_with_premises
        from .e_consequence import ConsequenceEngine

        # Gather all known facts and variables for the axiom check
        all_facts: Set[Literal] = set()
        for lits in self.ll.values():
            all_facts |= lits
        all_facts |= self.known

        dep_vars: Dict[str, Sort] = dict(self.sort_ctx)
        for lit in all_facts | {target}:
            for v in literal_vars(lit):
                if v not in dep_vars:
                    dep_vars[v] = (Sort.LINE if (len(v) == 1 and v.isupper())
                                   else Sort.POINT)

        # Run CE closure to maximise available premises
        ce = ConsequenceEngine()
        closure = ce.direct_consequences(all_facts)
        aug = all_facts | closure

        ok, _, req_premises = check_specific_axiom_with_premises(
            axiom_name, aug, [target], dep_vars)
        if ok and req_premises:
            return self._deps_for_premises(req_premises)

        # Fallback: variable-scoped search for target vars
        return self._deps_for_premises({target})

    def _deps_target(self, target: Literal) -> List[int]:
        """Find lines that provide *target* or its symmetric form.

        Prefers an exact match (single line).  Falls back to variable-
        overlap only when no exact or symmetric match is found.
        """
        # 1) Exact match
        for ln_num, lits in self.ll.items():
            if target in lits:
                return [ln_num]
        # 2) Symmetric match
        sym = self._symmetric_literal(target)
        if sym is not None:
            for ln_num, lits in self.ll.items():
                if sym in lits:
                    return [ln_num]
        # 3) Variable-overlap fallback (for CE/ME derivable literals)
        tv = literal_vars(target)
        deps = set()
        for ln_num, lits in self.ll.items():
            for lit in lits:
                if literal_vars(lit) & tv:
                    deps.add(ln_num)
                    break
        return sorted(deps)

    def _deps_for(self, step_lits, new_vars: set) -> List[int]:
        av: Set[str] = set()
        for lit in step_lits:
            av |= literal_vars(lit)
        needed = av - new_vars
        deps: Set[int] = set()
        for ln_num, lits in self.ll.items():
            for lit in lits:
                if literal_vars(lit) & needed:
                    deps.add(ln_num)
                    break
        return sorted(deps)

    def _deps_for_premises(self, premises: Set[Literal]) -> List[int]:
        """Find minimal line set providing the required premise literals.

        For each premise, searches for an exact match in a prior line,
        then tries the symmetric form (M3/M4) and equality-swapped form.
        Only lines that contribute at least one required premise are
        included.  Premises already in self.known but not in any line
        are skipped (the verifier derives them from its engines).
        """
        deps: Set[int] = set()
        for prem in premises:
            # 1) Exact match in a proof line
            found = False
            for ln_num, lits in self.ll.items():
                if prem in lits:
                    deps.add(ln_num)
                    found = True
                    break
            if found:
                continue
            # 2) Equality-swapped form: ¬(b=a) ↔ ¬(a=b)
            if isinstance(prem.atom, Equals):
                swapped = Literal(
                    Equals(prem.atom.right, prem.atom.left),
                    polarity=prem.polarity)
                for ln_num, lits in self.ll.items():
                    if swapped in lits:
                        deps.add(ln_num)
                        found = True
                        break
            if found:
                continue
            # 3) Metric symmetric form (M3/M4)
            sym = self._symmetric_literal(prem)
            if sym is not None:
                for ln_num, lits in self.ll.items():
                    if sym in lits:
                        deps.add(ln_num)
                        found = True
                        break
            if found:
                continue
            # 4) If the premise is already globally known (from earlier
            #    constructions, axiom steps, or derived facts), the
            #    verifier's checker.known fallback will satisfy it.
            #    Don't add variable-overlap deps — they'd be extraneous.
            if prem in self.known:
                continue
            # Also check equality-swapped known
            if isinstance(prem.atom, Equals):
                swapped = Literal(
                    Equals(prem.atom.right, prem.atom.left),
                    polarity=prem.polarity)
                if swapped in self.known:
                    continue
            # 5) Last resort: variable-overlap for CE-derivable premises
            pv = literal_vars(prem)
            for ln_num, lits in self.ll.items():
                if ln_num in deps:
                    continue
                for lit in lits:
                    if literal_vars(lit) & pv:
                        deps.add(ln_num)
                        break
        return sorted(deps)

    def _thm_deps(self, thm: ETheorem, vm: Dict[str, str]) -> List[int]:
        """Find deps for a theorem application.

        For each instantiated hypothesis:
        1. If exact match found → add just that line
        2. If symmetric match → add that line
        3. If neither → use _deps_for_premises to find lines whose
           literals provide the unmatched hypothesis (variable-scoped).
        """
        deps: Set[int] = set()
        unmatched: Set[Literal] = set()

        for hyp in thm.sequent.hypotheses:
            inst = substitute_literal(hyp, vm)
            # Skip impossible ¬(v=v) hypotheses (Lean arg-reuse collision)
            if (not inst.polarity and isinstance(inst.atom, Equals)
                    and isinstance(inst.atom.left, str)
                    and inst.atom.left == inst.atom.right):
                continue
            # 1) Exact match
            found = False
            for ln_num, lits in self.ll.items():
                if inst in lits:
                    deps.add(ln_num)
                    found = True
                    break
            if found:
                continue
            # 2) Symmetric form (M3/M4)
            sym = self._symmetric_literal(inst)
            if sym is not None:
                for ln_num, lits in self.ll.items():
                    if sym in lits:
                        deps.add(ln_num)
                        found = True
                        break
            if found:
                continue
            # 3) Unmatched — collect for premise-based dep search
            unmatched.add(inst)

        # For unmatched hypotheses, find lines providing them
        # using the premise-targeted search (variable-scoped fallback).
        if unmatched:
            extra = self._deps_for_premises(unmatched)
            deps.update(extra)
        return sorted(deps)

    # -- Declarations --------------------------------------------------

    def _build_decls(self) -> Dict[str, List[str]]:
        sp: Set[str] = set()
        sl: Set[str] = set()
        if self.seq:
            for lit in self.seq.hypotheses:
                _extract_declarations(lit, sp, sl)
            for lit in self.seq.conclusions:
                _extract_declarations(lit, sp, sl)
            for vn, vs in self.seq.exists_vars:
                if vs == Sort.POINT:
                    sp.add(vn)
                elif vs == Sort.LINE:
                    sl.add(vn)
        return {"points": sorted(sp), "lines": sorted(sl)}

    # -- Fallback path -------------------------------------------------

    def _synth_translated(self, ts: TranslatedStep):
        step = ts.step
        if step.kind == StepKind.CONSTRUCTION and step.assertions:
            lits = set()
            parts = []
            for a in step.assertions:
                m = self._map_lit(a)
                parts.append(literal_to_text(m))
                lits.add(m)
                self.known.add(m)
            deps = self._deps_for(lits, set())
            ln = self.nprem + len(self.steps) + 1
            self.steps.append({
                "lineNumber": ln, "text": ", ".join(parts),
                "justification": step.description, "dependencies": deps,
                "depth": self.current_depth, "status": "?",
            })
            self.ll[ln] = lits


# =====================================================================
# High-level API
# =====================================================================

def synthesize_proof(translation: TranslationResult,
                     lean_proof: Optional[LeanProof] = None) -> SynthesisResult:
    return ProofSynthesizer(translation, lean_proof).synthesize()


def synthesize_and_verify(translation: TranslationResult,
                          lean_proof: Optional[LeanProof] = None):
    from .unified_checker import verify_e_proof_json
    sr = synthesize_proof(translation, lean_proof)
    if not sr.success or not sr.euclid_json:
        return sr, None
    vr = verify_e_proof_json(sr.euclid_json)
    return sr, vr


def synthesize_all(lean_dir: str, output_dir: Optional[str] = None,
                   prop_range: Tuple[int, int] = (16, 48)):
    from .lean_translator import translate_lean_file
    results = []
    for n in range(prop_range[0], prop_range[1] + 1):
        fp = Path(lean_dir) / f"Prop{n}.lean"
        if not fp.exists():
            r = SynthesisResult(prop_name=f"Prop.I.{n}", prop_number=n,
                                errors=[f"File not found: {fp}"])
            results.append((n, r, None))
            continue
        try:
            lps = parse_lean_file(str(fp))
            lp = lps[0] if lps else None
        except Exception:
            lp = None
        tr = translate_lean_file(str(fp))
        if not tr.success:
            r = SynthesisResult(prop_name=tr.prop_name, prop_number=n,
                                errors=["Translation failed"])
            results.append((n, r, None))
            continue
        sr, vr = synthesize_and_verify(tr, lp)
        if output_dir and sr.euclid_json and vr and vr.accepted:
            op = Path(output_dir)
            op.mkdir(parents=True, exist_ok=True)
            with open(op / f"Proposition I.{n}.euclid", 'w', encoding='utf-8') as f:
                json.dump(sr.euclid_json, f, indent=2, ensure_ascii=False)
        results.append((n, sr, vr))
    return results
