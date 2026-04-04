"""
lean_to_euclid_json.py — Generate .euclid JSON proof files from translations.

Converts TranslationResult objects into the .euclid JSON format used by
the solved_proofs/ and unsolved_proofs/ directories.

The .euclid format has:
  - metadata (difficulty, hints)
  - canvas (points, segments, circles, etc.)
  - proof (name, premises, goal, declarations, steps)
"""
from __future__ import annotations

import json
import datetime
from pathlib import Path
from typing import Any, Dict, List, Optional, Tuple

from .e_ast import (
    Sort, Literal, Atom, Sequent,
    On, SameSide, Between, Center, Inside, Intersects,
    Equals, LessThan,
    SegmentTerm, AngleTerm, AreaTerm, MagAdd, RightAngle, ZeroMag,
    ProofStep, StepKind, EProof,
)
from .lean_translator import TranslatedStep, TranslationResult
from .lean_mapping import PROP_DEPS


# ═══════════════════════════════════════════════════════════════════════
# Literal → text serialization (matching .euclid step format)
# ═══════════════════════════════════════════════════════════════════════

def literal_to_text(lit: Literal) -> str:
    """Serialize a Literal to the text format used in .euclid files."""
    if lit.polarity:
        return _atom_to_text(lit.atom)
    return f"¬({_atom_to_text(lit.atom)})"


def _atom_to_text(atom: Atom) -> str:
    """Serialize an Atom to text."""
    if isinstance(atom, On):
        return f"on({atom.point}, {atom.obj})"
    if isinstance(atom, SameSide):
        return f"same-side({atom.a}, {atom.b}, {atom.line})"
    if isinstance(atom, Between):
        return f"between({atom.a}, {atom.b}, {atom.c})"
    if isinstance(atom, Center):
        return f"center({atom.point}, {atom.circle})"
    if isinstance(atom, Inside):
        return f"inside({atom.point}, {atom.circle})"
    if isinstance(atom, Intersects):
        return f"intersects({atom.obj1}, {atom.obj2})"
    if isinstance(atom, Equals):
        return f"{_term_to_text(atom.left)} = {_term_to_text(atom.right)}"
    if isinstance(atom, LessThan):
        return f"{_term_to_text(atom.left)} < {_term_to_text(atom.right)}"
    return repr(atom)


def _term_to_text(term) -> str:
    """Serialize a term to text."""
    if isinstance(term, str):
        return term
    if isinstance(term, SegmentTerm):
        return f"{term.p1}{term.p2}"
    if isinstance(term, AngleTerm):
        return f"∠{term.p1}{term.p2}{term.p3}"
    if isinstance(term, AreaTerm):
        return f"△{term.p1}{term.p2}{term.p3}"
    if isinstance(term, MagAdd):
        return f"({_term_to_text(term.left)} + {_term_to_text(term.right)})"
    if isinstance(term, RightAngle):
        return "∟"
    if isinstance(term, ZeroMag):
        return "0"
    return repr(term)


# ═══════════════════════════════════════════════════════════════════════
# StepKind → justification name mapping
# ═══════════════════════════════════════════════════════════════════════

def step_kind_to_justification(step: ProofStep) -> str:
    """Map a ProofStep to a human-readable justification string."""
    if step.kind == StepKind.CONSTRUCTION:
        return step.description or "Construction"
    if step.kind == StepKind.THEOREM_APP:
        return step.theorem_name or "Theorem application"
    if step.kind == StepKind.SUPERPOSITION_SAS:
        return "SAS superposition"
    if step.kind == StepKind.SUPERPOSITION_SSS:
        return "SSS superposition"
    if step.kind == StepKind.BOT_INTRO:
        return "⊥-intro (contradiction)"
    if step.kind == StepKind.BOT_ELIM:
        return "⊥-elim (discharge)"
    if step.kind == StepKind.CASE_SPLIT_ELIM:
        return "Case split"
    if step.kind == StepKind.TRICHOTOMY:
        return "Trichotomy"
    # AXIOM_ELIM / METRIC / TRANSFER / DIAGRAMMATIC
    if step.theorem_name:
        return step.theorem_name
    return step.description or "Axiom elimination"


# ═══════════════════════════════════════════════════════════════════════
# Proposition metadata
# ═══════════════════════════════════════════════════════════════════════

_PROP_TITLES = {
    1: "Equilateral Triangle",
    2: "Copy Segment",
    3: "Cut Off Equal Segment",
    4: "SAS Congruence",
    5: "Isosceles Base Angles",
    6: "Converse of I.5",
    7: "Uniqueness Lemma",
    8: "SSS Congruence",
    9: "Bisect Angle",
    10: "Bisect Segment",
    11: "Perpendicular from Point on Line",
    12: "Perpendicular from Point off Line",
    13: "Supplementary Angles",
    14: "Converse of I.13",
    15: "Vertical Angles",
    16: "Exterior Angle Theorem",
    17: "Two Angles Less Than Two Right Angles",
    18: "Greater Side Opposite Greater Angle",
    19: "Greater Angle Opposite Greater Side",
    20: "Triangle Inequality",
    21: "Triangle Within Triangle",
    22: "Construct Triangle from Three Segments",
    23: "Copy Angle",
    24: "SAS Inequality (Open Jaw)",
    25: "Converse of I.24",
    26: "ASA and AAS Congruence",
    27: "Alternate Interior Angles Imply Parallel",
    28: "Exterior Angle + Parallel",
    29: "Parallel Implies Alternate Angles",
    30: "Transitivity of Parallelism",
    31: "Construct Parallel Through Point",
    32: "Angle Sum of Triangle",
    33: "Joining Ends of Equal Parallel Segments",
    34: "Properties of Parallelograms",
    35: "Parallelograms on Same Base",
    36: "Parallelograms on Equal Bases",
    37: "Triangles on Same Base",
    38: "Triangles on Equal Bases",
    39: "Equal Triangles Same Base → Same Parallels",
    40: "Equal Triangles Equal Bases → Same Parallels",
    41: "Parallelogram = 2× Triangle",
    42: "Construct Parallelogram = Triangle",
    43: "Complements of Parallelogram",
    44: "Apply Parallelogram to Line",
    45: "Construct Parallelogram = Polygon",
    46: "Construct Square on Segment",
    47: "Pythagorean Theorem",
    48: "Converse of Pythagorean Theorem",
}

_PROP_DIFFICULTIES = {
    1: 2, 2: 3, 3: 2, 4: 1, 5: 3, 6: 3, 7: 3, 8: 2,
    9: 2, 10: 2, 11: 3, 12: 3, 13: 2, 14: 2, 15: 2,
    16: 3, 17: 2, 18: 3, 19: 3, 20: 3, 21: 4, 22: 4,
    23: 3, 24: 4, 25: 3, 26: 4, 27: 3, 28: 3, 29: 4,
    30: 3, 31: 3, 32: 3, 33: 3, 34: 3, 35: 4, 36: 3,
    37: 3, 38: 3, 39: 3, 40: 3, 41: 3, 42: 4, 43: 3,
    44: 4, 45: 4, 46: 3, 47: 5, 48: 3,
}


# ═══════════════════════════════════════════════════════════════════════
# JSON builder
# ═══════════════════════════════════════════════════════════════════════

def translation_to_euclid_json(result: TranslationResult,
                                sequent: Optional[Sequent] = None,
                                canvas: Optional[Dict] = None) -> Dict[str, Any]:
    """Convert a TranslationResult to a .euclid JSON dict.

    Parameters:
      result: The translation result from lean_translator.
      sequent: Optional sequent from e_library for premises/goal.
               If not provided, premises/goal are left as placeholders.
      canvas: Optional canvas data from an existing .euclid file.
              If not provided, a minimal empty canvas is generated.
    """
    n = result.prop_number
    prop_name = result.prop_name

    # Metadata
    metadata = {
        "proposition": f"Proposition I.{n}",
        "title": _PROP_TITLES.get(n, f"Proposition I.{n}"),
        "difficulty": _PROP_DIFFICULTIES.get(n, 3),
        "hints": [f"Translated from LeanEuclid {result.lean_theorem}"],
        "source": "lean_translator",
        "lean_file": result.lean_theorem,
    }

    # Canvas (use provided or empty)
    if canvas is None:
        canvas = {
            "points": [],
            "segments": [],
            "rays": [],
            "circles": [],
            "angleMarks": [],
            "equalityGroups": [],
        }

    # Premises and goal from sequent
    premises = []
    goal = ""
    declarations = {"points": [], "lines": []}

    if sequent:
        premises = [literal_to_text(lit) for lit in sequent.hypotheses]
        goal = ", ".join(literal_to_text(lit) for lit in sequent.conclusions)

        # Extract point and line declarations from hypotheses
        seen_points = set()
        seen_lines = set()
        for lit in sequent.hypotheses:
            _extract_declarations(lit, seen_points, seen_lines)
        for lit in sequent.conclusions:
            _extract_declarations(lit, seen_points, seen_lines)
        # Also include existential witnesses
        for var_name, var_sort in sequent.exists_vars:
            if var_sort == Sort.POINT:
                seen_points.add(var_name)
            elif var_sort == Sort.LINE:
                seen_lines.add(var_name)

        declarations["points"] = sorted(seen_points)
        declarations["lines"] = sorted(seen_lines)

    # Steps
    json_steps = []
    premise_count = len(premises)
    for i, ts in enumerate(result.steps):
        step = ts.step
        # Compute line number (premises are numbered 1..N, steps start after)
        line_num = premise_count + i + 1

        # Step text: join assertions or use description
        if step.assertions:
            text = ", ".join(literal_to_text(lit) for lit in step.assertions)
        else:
            text = step.description

        # Justification
        justification = step_kind_to_justification(step)

        # Dependencies: reference all prior steps (simplified)
        deps = list(range(1, line_num))
        if step.refs:
            deps = step.refs

        json_step = {
            "lineNumber": line_num,
            "text": text,
            "justification": justification,
            "dependencies": deps,
            "depth": 0,
            "status": "?",
        }

        # Add notes from translation
        if ts.notes:
            json_step["_translator_notes"] = ts.notes
        if ts.warnings:
            json_step["_translator_warnings"] = ts.warnings

        json_steps.append(json_step)

    # Assemble the full .euclid document
    doc = {
        "format": "euclid-proof",
        "version": "1.0.0",
        "program": "Euclid Elements Simulator (Python) — Lean Translator",
        "metadata": metadata,
        "canvas": canvas,
        "exportedAt": datetime.datetime.utcnow().strftime("%Y-%m-%dT%H:%M:%SZ"),
        "proof": {
            "name": prop_name,
            "premises": premises,
            "goal": goal,
            "declarations": declarations,
            "steps": json_steps,
        },
    }

    return doc


def _extract_declarations(lit: Literal, points: set, lines: set):
    """Extract point and line names from a literal."""
    atom = lit.atom
    if isinstance(atom, On):
        points.add(atom.point)
        # Heuristic: single uppercase → line, lowercase → point
        if atom.obj[0].isupper() and len(atom.obj) <= 2:
            lines.add(atom.obj)
        else:
            points.add(atom.obj)
    elif isinstance(atom, SameSide):
        points.add(atom.a)
        points.add(atom.b)
        lines.add(atom.line)
    elif isinstance(atom, Between):
        points.add(atom.a)
        points.add(atom.b)
        points.add(atom.c)
    elif isinstance(atom, Equals):
        if isinstance(atom.left, str):
            points.add(atom.left)
        if isinstance(atom.right, str):
            points.add(atom.right)
        _extract_term_points(atom.left, points)
        _extract_term_points(atom.right, points)
    elif isinstance(atom, LessThan):
        _extract_term_points(atom.left, points)
        _extract_term_points(atom.right, points)


def _extract_term_points(term, points: set):
    """Extract point names from a magnitude term."""
    if isinstance(term, SegmentTerm):
        points.add(term.p1)
        points.add(term.p2)
    elif isinstance(term, AngleTerm):
        points.add(term.p1)
        points.add(term.p2)
        points.add(term.p3)
    elif isinstance(term, AreaTerm):
        points.add(term.p1)
        points.add(term.p2)
        points.add(term.p3)
    elif isinstance(term, MagAdd):
        _extract_term_points(term.left, points)
        _extract_term_points(term.right, points)


# ═══════════════════════════════════════════════════════════════════════
# File I/O
# ═══════════════════════════════════════════════════════════════════════

def write_euclid_json(result: TranslationResult,
                       output_path: str,
                       sequent: Optional[Sequent] = None,
                       canvas: Optional[Dict] = None):
    """Write a .euclid JSON file from a translation result."""
    doc = translation_to_euclid_json(result, sequent=sequent, canvas=canvas)
    path = Path(output_path)
    path.parent.mkdir(parents=True, exist_ok=True)
    with open(path, 'w', encoding='utf-8') as f:
        json.dump(doc, f, indent=2, ensure_ascii=False)


def write_all_euclid_json(results: List[TranslationResult],
                            output_dir: str):
    """Write .euclid JSON files for all translation results."""
    from .e_library import E_THEOREM_LIBRARY

    out_path = Path(output_dir)
    out_path.mkdir(parents=True, exist_ok=True)

    for result in results:
        if not result.success:
            continue

        # Try to get sequent from library
        sequent = None
        thm = E_THEOREM_LIBRARY.get(result.prop_name)
        if thm:
            sequent = thm.sequent

        # Try to get canvas from existing unsolved_proofs file
        canvas = _load_existing_canvas(result.prop_number)

        filename = f"Proposition I.{result.prop_number}.euclid"
        filepath = out_path / filename
        write_euclid_json(result, str(filepath),
                           sequent=sequent, canvas=canvas)


def _load_existing_canvas(prop_num: int) -> Optional[Dict]:
    """Try to load canvas from an existing .euclid file."""
    for prefix in ("unsolved_proofs", "solved_proofs"):
        path = Path(prefix) / f"Proposition I.{prop_num}.euclid"
        if path.exists():
            try:
                with open(path, 'r', encoding='utf-8') as f:
                    data = json.load(f)
                return data.get("canvas")
            except (json.JSONDecodeError, OSError):
                pass
    return None
