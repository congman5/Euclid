"""
smt_backend.py — SMT-LIB 2.6 encoding of System E axioms and proof obligations.

Encodes the diagrammatic, metric, and transfer axioms from Avigad, Dean,
Mumma (2009) §3.4–3.6 in SMT-LIB format suitable for Z3 / CVC5.

The paper (§6) notes:
  "We entered all our axioms in the standard SMT format, and tested it
   with [Z3 and CVC3]. The results were promising; most inferences were
   instantaneous, and only a few required more than a few seconds."

Phase 8.1 of the implementation plan.
"""
from __future__ import annotations

import subprocess
from typing import Dict, FrozenSet, List, Optional, Set, Tuple, Union

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
# SMT-LIB SORT DECLARATIONS
# ═══════════════════════════════════════════════════════════════════════

_SORT_DECLS = """\
; --- Sorts (Paper §3.1) ---
(declare-sort Point 0)
(declare-sort Line 0)
(declare-sort Circle 0)
(declare-sort Segment 0)
(declare-sort Angle 0)
(declare-sort Area 0)
"""

_FUNC_DECLS = """\
; --- Diagrammatic predicates (§3.4) ---
(declare-fun on_point_line (Point Line) Bool)
(declare-fun on_point_circle (Point Circle) Bool)
(declare-fun between (Point Point Point) Bool)
(declare-fun same_side (Point Point Line) Bool)
(declare-fun center (Point Circle) Bool)
(declare-fun inside (Point Circle) Bool)
(declare-fun intersects_ll (Line Line) Bool)
(declare-fun intersects_lc (Line Circle) Bool)
(declare-fun intersects_cc (Circle Circle) Bool)
(declare-fun eq_point (Point Point) Bool)
(declare-fun eq_line (Line Line) Bool)

; --- Metric functions (§3.5) ---
(declare-fun seg (Point Point) Segment)
(declare-fun ang (Point Point Point) Angle)
(declare-fun tri (Point Point Point) Area)
(declare-fun right_angle () Angle)
(declare-fun zero_seg () Segment)
(declare-fun zero_area () Area)
(declare-fun seg_add (Segment Segment) Segment)
(declare-fun ang_add (Angle Angle) Angle)
(declare-fun area_add (Area Area) Area)

; --- Metric predicates (§3.5) ---
(declare-fun eq_seg (Segment Segment) Bool)
(declare-fun eq_ang (Angle Angle) Bool)
(declare-fun eq_area (Area Area) Bool)
(declare-fun lt_seg (Segment Segment) Bool)
(declare-fun lt_ang (Angle Angle) Bool)
(declare-fun lt_area (Area Area) Bool)
"""


# ═══════════════════════════════════════════════════════════════════════
# ATOM → SMT-LIB ENCODING
# ═══════════════════════════════════════════════════════════════════════

def _smt_var(name: str) -> str:
    """Sanitise a variable name for SMT-LIB (no primes, Greek, etc.)."""
    return name.replace("'", "_p").replace("α", "alpha").replace("β", "beta").replace("γ", "gamma")


def _smt_term(t: Union[str, Term]) -> str:
    """Encode a term (point name, SegmentTerm, AngleTerm, etc.)."""
    if isinstance(t, str):
        return _smt_var(t)
    if isinstance(t, SegmentTerm):
        return f"(seg {_smt_var(t.p1)} {_smt_var(t.p2)})"
    if isinstance(t, AngleTerm):
        return f"(ang {_smt_var(t.p1)} {_smt_var(t.p2)} {_smt_var(t.p3)})"
    if isinstance(t, AreaTerm):
        return f"(tri {_smt_var(t.p1)} {_smt_var(t.p2)} {_smt_var(t.p3)})"
    if isinstance(t, MagAdd):
        return f"({_mag_add_func(t)} {_smt_term(t.left)} {_smt_term(t.right)})"
    if isinstance(t, ZeroMag):
        return "zero_seg"
    if isinstance(t, RightAngle):
        return "right_angle"
    return str(t)


def _mag_add_func(t: MagAdd) -> str:
    """Pick the correct addition function based on operand types."""
    left = t.left
    if isinstance(left, SegmentTerm):
        return "seg_add"
    if isinstance(left, AngleTerm):
        return "ang_add"
    if isinstance(left, AreaTerm):
        return "area_add"
    if isinstance(left, MagAdd):
        return _mag_add_func(left)
    return "seg_add"  # fallback


def _eq_func(left: Union[str, Term], right: Union[str, Term]) -> str:
    """Pick the correct equality predicate based on operand types."""
    if isinstance(left, str) and isinstance(right, str):
        return "eq_point"
    if isinstance(left, SegmentTerm) or isinstance(right, SegmentTerm):
        return "eq_seg"
    if isinstance(left, AngleTerm) or isinstance(right, AngleTerm):
        return "eq_ang"
    if isinstance(left, AreaTerm) or isinstance(right, AreaTerm):
        return "eq_area"
    if isinstance(left, MagAdd) or isinstance(right, MagAdd):
        inner = left.left if isinstance(left, MagAdd) else right.left if isinstance(right, MagAdd) else left
        if isinstance(inner, SegmentTerm):
            return "eq_seg"
        if isinstance(inner, AngleTerm):
            return "eq_ang"
        if isinstance(inner, AreaTerm):
            return "eq_area"
    if isinstance(left, RightAngle) or isinstance(right, RightAngle):
        return "eq_ang"
    if isinstance(left, ZeroMag) or isinstance(right, ZeroMag):
        return "eq_seg"
    return "eq_point"


def _lt_func(left: Term, right: Term) -> str:
    """Pick the correct less-than predicate based on operand types."""
    if isinstance(left, SegmentTerm) or isinstance(right, SegmentTerm):
        return "lt_seg"
    if isinstance(left, AngleTerm) or isinstance(right, AngleTerm):
        return "lt_ang"
    if isinstance(left, AreaTerm) or isinstance(right, AreaTerm):
        return "lt_area"
    return "lt_seg"


def encode_atom(atom: Atom, circle_vars: Optional[Set[str]] = None) -> str:
    """Encode a single E-system atom as an SMT-LIB expression.

    Args:
        atom: The atom to encode.
        circle_vars: Optional set of variable names known to be circles.
            Used to dispatch On(point, obj) to on_point_line vs
            on_point_circle.
    """
    if isinstance(atom, On):
        p = _smt_var(atom.point)
        o = _smt_var(atom.obj)
        if circle_vars and _smt_var(atom.obj) in circle_vars:
            return f"(on_point_circle {p} {o})"
        return f"(on_point_line {p} {o})"
    if isinstance(atom, Between):
        return f"(between {_smt_var(atom.a)} {_smt_var(atom.b)} {_smt_var(atom.c)})"
    if isinstance(atom, SameSide):
        return f"(same_side {_smt_var(atom.a)} {_smt_var(atom.b)} {_smt_var(atom.line)})"
    if isinstance(atom, Center):
        return f"(center {_smt_var(atom.point)} {_smt_var(atom.circle)})"
    if isinstance(atom, Inside):
        return f"(inside {_smt_var(atom.point)} {_smt_var(atom.circle)})"
    if isinstance(atom, Intersects):
        return f"(intersects_ll {_smt_var(atom.obj1)} {_smt_var(atom.obj2)})"
    if isinstance(atom, Equals):
        f = _eq_func(atom.left, atom.right)
        return f"({f} {_smt_term(atom.left)} {_smt_term(atom.right)})"
    if isinstance(atom, LessThan):
        f = _lt_func(atom.left, atom.right)
        return f"({f} {_smt_term(atom.left)} {_smt_term(atom.right)})"
    raise ValueError(f"Unknown atom type: {type(atom).__name__}")


def encode_literal(lit: Literal, circle_vars: Optional[Set[str]] = None) -> str:
    """Encode a literal (possibly negated atom) as SMT-LIB."""
    inner = encode_atom(lit.atom, circle_vars)
    if lit.polarity:
        return inner
    return f"(not {inner})"


# ═══════════════════════════════════════════════════════════════════════
# CLAUSE → SMT-LIB (UNIVERSALLY QUANTIFIED)
# ═══════════════════════════════════════════════════════════════════════

def _infer_sorts_from_atom(
    atom: Atom,
    circle_vars: Optional[Set[str]] = None,
) -> Dict[str, str]:
    """Infer SMT sorts for variables based on atom structure."""
    result: Dict[str, str] = {}
    if isinstance(atom, On):
        result[_smt_var(atom.point)] = "Point"
        if circle_vars and _smt_var(atom.obj) in circle_vars:
            result[_smt_var(atom.obj)] = "Circle"
        else:
            result[_smt_var(atom.obj)] = "Line"
    elif isinstance(atom, Between):
        for v in (atom.a, atom.b, atom.c):
            result[_smt_var(v)] = "Point"
    elif isinstance(atom, SameSide):
        result[_smt_var(atom.a)] = "Point"
        result[_smt_var(atom.b)] = "Point"
        result[_smt_var(atom.line)] = "Line"
    elif isinstance(atom, Center):
        result[_smt_var(atom.point)] = "Point"
        result[_smt_var(atom.circle)] = "Circle"
    elif isinstance(atom, Inside):
        result[_smt_var(atom.point)] = "Point"
        result[_smt_var(atom.circle)] = "Circle"
    elif isinstance(atom, Intersects):
        result[_smt_var(atom.obj1)] = "Line"
        result[_smt_var(atom.obj2)] = "Line"
    elif isinstance(atom, Equals):
        _infer_term_sorts(atom.left, result)
        _infer_term_sorts(atom.right, result)
    elif isinstance(atom, LessThan):
        _infer_term_sorts(atom.left, result)
        _infer_term_sorts(atom.right, result)
    return result


def _infer_term_sorts(t: Union[str, Term], result: Dict[str, str]) -> None:
    """Infer sorts for variables inside a term."""
    if isinstance(t, str):
        result.setdefault(_smt_var(t), "Point")
    elif isinstance(t, SegmentTerm):
        result.setdefault(_smt_var(t.p1), "Point")
        result.setdefault(_smt_var(t.p2), "Point")
    elif isinstance(t, AngleTerm):
        for v in (t.p1, t.p2, t.p3):
            result.setdefault(_smt_var(v), "Point")
    elif isinstance(t, AreaTerm):
        for v in (t.p1, t.p2, t.p3):
            result.setdefault(_smt_var(v), "Point")
    elif isinstance(t, MagAdd):
        _infer_term_sorts(t.left, result)
        _infer_term_sorts(t.right, result)


def _detect_circle_vars(clause: Clause) -> Set[str]:
    """Detect which variables in a clause are circles.

    A variable is a circle if it appears as the circle argument in
    a Center or Inside atom within the same clause.
    """
    circles: Set[str] = set()
    for lit in clause.literals:
        if isinstance(lit.atom, Center):
            circles.add(_smt_var(lit.atom.circle))
        elif isinstance(lit.atom, Inside):
            circles.add(_smt_var(lit.atom.circle))
    return circles


def _collect_vars(clause: Clause) -> Dict[str, str]:
    """Collect all variable names with their SMT sort from a clause.

    Uses a two-pass approach: first detects circle variables from
    Center/Inside atoms, then correctly types On object variables.
    """
    circle_vars = _detect_circle_vars(clause)
    vars_: Dict[str, str] = {}
    for lit in clause.literals:
        atom_sorts = _infer_sorts_from_atom(lit.atom, circle_vars)
        for v, s in atom_sorts.items():
            vars_.setdefault(v, s)
    return vars_


def encode_clause(clause: Clause) -> str:
    """Encode a disjunctive clause as a universally-quantified SMT-LIB assertion."""
    lits = list(clause.literals)
    circle_vars = _detect_circle_vars(clause)
    if len(lits) == 0:
        return "(assert false)"
    if len(lits) == 1:
        body = encode_literal(lits[0], circle_vars)
    else:
        parts = " ".join(encode_literal(l, circle_vars) for l in lits)
        body = f"(or {parts})"

    vs = _collect_vars(clause)
    if vs:
        bindings = " ".join(f"({n} {s})" for n, s in vs.items())
        return f"(assert (forall ({bindings}) {body}))"
    return f"(assert {body})"


# ═══════════════════════════════════════════════════════════════════════
# PUBLIC API
# ═══════════════════════════════════════════════════════════════════════

def encode_axioms_smtlib() -> str:
    """Encode all System E axioms as an SMT-LIB 2.6 script.

    Returns the full script including sort declarations, function
    declarations, and all axiom assertions.
    """
    from .e_axioms import ALL_AXIOMS

    lines = [
        "(set-logic ALL)",
        "",
        _SORT_DECLS,
        _FUNC_DECLS,
        "; --- Axioms (§3.4 Diagrammatic + §3.5 Metric + §3.6 Transfer) ---",
    ]
    for i, clause in enumerate(ALL_AXIOMS):
        lines.append(f"; Axiom {i + 1}")
        lines.append(encode_clause(clause))
    lines.append("")
    return "\n".join(lines)


def encode_obligation(
    known: List[Literal],
    query: Literal,
    variables: Optional[List[Tuple[str, Sort]]] = None,
) -> str:
    """Encode a proof obligation: do *known* facts entail *query*?

    Generates an SMT-LIB script that:
      1. Declares all sorts and functions
      2. Asserts all axioms
      3. Declares the relevant variables
      4. Asserts the known facts
      5. Asserts (not query)
      6. Calls (check-sat) — UNSAT means query is entailed

    Args:
        known: List of positive/negative literals known to hold.
        query: The literal to check.
        variables: Optional variable declarations (name, sort) pairs.
                   If None, inferred from known + query.

    Returns:
        Complete SMT-LIB 2.6 script as a string.
    """
    lines = [encode_axioms_smtlib()]

    # Detect circle variables from known facts for correct On dispatch
    all_lits = known + [query]
    circle_vars: Set[str] = set()
    for lit in all_lits:
        if isinstance(lit.atom, (Center, Inside)):
            circ_attr = getattr(lit.atom, 'circle', None)
            if circ_attr:
                circle_vars.add(_smt_var(circ_attr))

    # Collect and declare variables
    if variables is None:
        variables = _infer_variables(all_lits, circle_vars)

    lines.append("; --- Variable declarations ---")
    sort_map = {
        Sort.POINT: "Point", Sort.LINE: "Line",
        Sort.CIRCLE: "Circle", Sort.SEGMENT: "Segment",
        Sort.ANGLE: "Angle", Sort.AREA: "Area",
    }
    for name, sort in variables:
        sn = _smt_var(name)
        ss = sort_map.get(sort, "Point")
        lines.append(f"(declare-const {sn} {ss})")

    # Assert known facts
    lines.append("")
    lines.append("; --- Known facts ---")
    for lit in known:
        lines.append(f"(assert {encode_literal(lit, circle_vars)})")

    # Assert negation of query (checking entailment via UNSAT)
    lines.append("")
    lines.append("; --- Query (negated for UNSAT check) ---")
    lines.append(f"(assert (not {encode_literal(query, circle_vars)}))")
    lines.append("")
    lines.append("(check-sat)")
    lines.append("(exit)")
    return "\n".join(lines)


def check_with_z3(
    script: str,
    timeout_ms: int = 5000,
    z3_path: str = "z3",
) -> Optional[bool]:
    """Run an SMT-LIB script through Z3 and return the result.

    Args:
        script: Complete SMT-LIB 2.6 script.
        timeout_ms: Z3 timeout in milliseconds.
        z3_path: Path to the Z3 binary.

    Returns:
        True if UNSAT (query is entailed),
        False if SAT (query is NOT entailed),
        None if Z3 is unavailable or errors out.
    """
    try:
        result = subprocess.run(
            [z3_path, f"-T:{timeout_ms // 1000}", "-in"],
            input=script,
            capture_output=True,
            text=True,
            timeout=timeout_ms / 1000 + 2,
        )
        output = result.stdout.strip().lower()
        if "unsat" in output:
            return True
        if "sat" in output:
            return False
        return None
    except (FileNotFoundError, subprocess.TimeoutExpired, OSError):
        return None


# ═══════════════════════════════════════════════════════════════════════
# INTEGRATION — try forward-chaining then SMT
# ═══════════════════════════════════════════════════════════════════════

def try_consequence_then_smt(
    known: List[Literal],
    query: Literal,
    variables: Optional[List[Tuple[str, Sort]]] = None,
    z3_path: str = "z3",
    timeout_ms: int = 5000,
) -> Tuple[bool, str]:
    """Try forward-chaining first; if inconclusive, query SMT solver.

    Returns:
        (result, engine) where result is True/False and engine is
        "consequence" or "smt" or "inconclusive".
    """
    # Try forward-chaining first
    try:
        from .e_consequence import EConsequenceEngine
        engine = EConsequenceEngine()
        for lit in known:
            engine.add_literal(lit)
        engine.close()
        if engine.contains(query):
            return (True, "consequence")
    except Exception:
        pass

    # Fall back to SMT
    script = encode_obligation(known, query, variables)
    result = check_with_z3(script, timeout_ms, z3_path)
    if result is True:
        return (True, "smt")
    if result is False:
        return (False, "smt")
    return (False, "inconclusive")


# ═══════════════════════════════════════════════════════════════════════
# HELPERS
# ═══════════════════════════════════════════════════════════════════════

def _infer_variables(
    literals: List[Literal],
    circle_vars: Optional[Set[str]] = None,
) -> List[Tuple[str, Sort]]:
    """Infer variable declarations from a list of literals."""
    seen: Dict[str, Sort] = {}
    sort_from_smt = {
        "Point": Sort.POINT, "Line": Sort.LINE, "Circle": Sort.CIRCLE,
        "Segment": Sort.SEGMENT, "Angle": Sort.ANGLE, "Area": Sort.AREA,
    }
    for lit in literals:
        atom_sorts = _infer_sorts_from_atom(lit.atom, circle_vars)
        for v, smt_sort in atom_sorts.items():
            if v not in seen:
                seen[v] = sort_from_smt.get(smt_sort, Sort.POINT)
    return list(seen.items())
