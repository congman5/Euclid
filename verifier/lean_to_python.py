"""
lean_to_python.py — Generate Python proof factory code from translations.

Converts TranslationResult objects into Python source code that matches
the _make_prop_iN() pattern used in e_proofs.py.  The generated code
can be pasted into e_proofs.py or saved as standalone modules.
"""
from __future__ import annotations

import textwrap
from typing import Dict, List, Optional, Tuple

from .e_ast import (
    Sort, Literal, Atom,
    On, SameSide, Between, Center, Inside, Intersects,
    Equals, LessThan,
    SegmentTerm, AngleTerm, AreaTerm, MagAdd, RightAngle, ZeroMag,
    ProofStep, StepKind, EProof,
)
from .lean_translator import TranslatedStep, TranslationResult


# ═══════════════════════════════════════════════════════════════════════
# AST → Python source serialization
# ═══════════════════════════════════════════════════════════════════════

_SORT_NAMES = {
    Sort.POINT: "Sort.POINT",
    Sort.LINE: "Sort.LINE",
    Sort.CIRCLE: "Sort.CIRCLE",
    Sort.SEGMENT: "Sort.SEGMENT",
    Sort.ANGLE: "Sort.ANGLE",
    Sort.AREA: "Sort.AREA",
}

_STEP_KIND_NAMES = {
    StepKind.CONSTRUCTION: "StepKind.CONSTRUCTION",
    StepKind.THEOREM_APP: "StepKind.THEOREM_APP",
    StepKind.SUPERPOSITION_SAS: "StepKind.SUPERPOSITION_SAS",
    StepKind.SUPERPOSITION_SSS: "StepKind.SUPERPOSITION_SSS",
    StepKind.BOT_INTRO: "StepKind.BOT_INTRO",
    StepKind.BOT_ELIM: "StepKind.BOT_ELIM",
    StepKind.CASE_SPLIT_ELIM: "StepKind.CASE_SPLIT_ELIM",
    StepKind.TRICHOTOMY: "StepKind.TRICHOTOMY",
    # AXIOM_ELIM covers DIAGRAMMATIC, METRIC, TRANSFER (aliases)
    # Use the readable alias names in generated code
    StepKind.AXIOM_ELIM: "StepKind.METRIC",
}


def _term_to_src(term) -> str:
    """Serialize a term to Python source."""
    if isinstance(term, str):
        return repr(term)
    if isinstance(term, SegmentTerm):
        return f'SegmentTerm("{term.p1}", "{term.p2}")'
    if isinstance(term, AngleTerm):
        return f'AngleTerm("{term.p1}", "{term.p2}", "{term.p3}")'
    if isinstance(term, AreaTerm):
        return f'AreaTerm("{term.p1}", "{term.p2}", "{term.p3}")'
    if isinstance(term, RightAngle):
        return "RightAngle()"
    if isinstance(term, ZeroMag):
        return "ZeroMag()"
    if isinstance(term, MagAdd):
        return f"MagAdd({_term_to_src(term.left)}, {_term_to_src(term.right)})"
    return repr(term)


def _atom_to_src(atom: Atom) -> str:
    """Serialize an Atom to Python source."""
    if isinstance(atom, On):
        return f'On("{atom.point}", "{atom.obj}")'
    if isinstance(atom, SameSide):
        return f'SameSide("{atom.a}", "{atom.b}", "{atom.line}")'
    if isinstance(atom, Between):
        return f'Between("{atom.a}", "{atom.b}", "{atom.c}")'
    if isinstance(atom, Center):
        return f'Center("{atom.point}", "{atom.circle}")'
    if isinstance(atom, Inside):
        return f'Inside("{atom.point}", "{atom.circle}")'
    if isinstance(atom, Intersects):
        return f'Intersects("{atom.obj1}", "{atom.obj2}")'
    if isinstance(atom, Equals):
        return f"Equals({_term_to_src(atom.left)}, {_term_to_src(atom.right)})"
    if isinstance(atom, LessThan):
        return f"LessThan({_term_to_src(atom.left)}, {_term_to_src(atom.right)})"
    return repr(atom)


def _literal_to_src(lit: Literal) -> str:
    """Serialize a Literal to Python source (_pos/_neg call)."""
    atom_src = _atom_to_src(lit.atom)
    if lit.polarity:
        return f"_pos({atom_src})"
    return f"_neg({atom_src})"


def _sort_to_src(sort: Sort) -> str:
    return _SORT_NAMES.get(sort, f"Sort.{sort.name}")


def _step_kind_to_src(kind: StepKind) -> str:
    return _STEP_KIND_NAMES.get(kind, f"StepKind.{kind.name}")


# ═══════════════════════════════════════════════════════════════════════
# ProofStep → Python source
# ═══════════════════════════════════════════════════════════════════════

def _proof_step_to_src(step: ProofStep, indent: str = "        ") -> str:
    """Serialize a ProofStep to Python source code."""
    parts = [f"{indent}ProofStep(id={step.id}"]
    parts.append(f"kind={_step_kind_to_src(step.kind)}")
    parts.append(f"description={repr(step.description)}")

    if step.theorem_name:
        parts.append(f"theorem_name={repr(step.theorem_name)}")

    if step.var_map:
        vm = ", ".join(f'"{k}": "{v}"' for k, v in step.var_map.items())
        parts.append(f"var_map={{{vm}}}")

    if step.new_vars:
        nv = ", ".join(
            f'("{n}", {_sort_to_src(s)})' for n, s in step.new_vars
        )
        parts.append(f"new_vars=[{nv}]")

    if step.assertions:
        if len(step.assertions) == 1:
            parts.append(
                f"assertions=[{_literal_to_src(step.assertions[0])}]"
            )
        else:
            alines = [f"{indent}    {_literal_to_src(a)}," for a in step.assertions]
            assertions_block = "\n".join(alines)
            parts.append(f"assertions=[\n{assertions_block}]")

    # Join with comma-space, first line has the opening
    head = ", ".join(parts[:4])
    rest = parts[4:]
    if not rest:
        return head + "),"
    lines = [head + ","]
    for p in rest:
        lines.append(f"{indent}    {p},")
    lines.append(f"{indent}),")
    return "\n".join(lines)


# ═══════════════════════════════════════════════════════════════════════
# Full factory function generation
# ═══════════════════════════════════════════════════════════════════════

def translation_to_python(result: TranslationResult) -> str:
    """Generate a _make_prop_iN() factory function from a TranslationResult."""
    n = result.prop_number
    name = result.prop_name  # e.g. "Prop.I.16"

    lines = []
    lines.append(f"def _make_prop_i{n}():")
    lines.append(f'    return _proof_from_sequent("{name}", [')

    for ts in result.steps:
        step_src = _proof_step_to_src(ts.step, indent="        ")
        lines.append(step_src)

    lines.append("    ])")
    lines.append("")

    return "\n".join(lines)


def translation_to_python_with_comments(result: TranslationResult) -> str:
    """Generate factory function with Lean source comments."""
    n = result.prop_number
    name = result.prop_name

    lines = []
    lines.append(f"# ── Prop I.{n} ──")
    lines.append(f"# Translated from LeanEuclid: {result.lean_theorem}")
    if result.warnings:
        lines.append(f"# Warnings: {len(result.warnings)}")
        for w in result.warnings[:5]:
            lines.append(f"#   - {w}")
    lines.append("")
    lines.append(f"def _make_prop_i{n}():")
    lines.append(f'    return _proof_from_sequent("{name}", [')

    for ts in result.steps:
        # Add Lean tactic source as comment
        for tactic in ts.source_tactics:
            lines.append(f"        # Lean: {tactic.kind.name} {tactic.rule_name or ''}")
        if ts.notes:
            for note in ts.notes:
                lines.append(f"        # Note: {note}")
        step_src = _proof_step_to_src(ts.step, indent="        ")
        lines.append(step_src)

    lines.append("    ])")
    lines.append("")

    return "\n".join(lines)


# ═══════════════════════════════════════════════════════════════════════
# Batch: generate a full module with all translated proofs
# ═══════════════════════════════════════════════════════════════════════

_MODULE_HEADER = '''\
"""
Generated System E proof factories — translated from LeanEuclid.

This file is auto-generated by lean_to_python.py. Each function
produces an EProof matching the pattern in e_proofs.py.
"""
from __future__ import annotations

from .e_ast import (
    Sort, Literal, Sequent,
    On, SameSide, Between, Center, Inside, Intersects,
    Equals, LessThan,
    SegmentTerm, AngleTerm, AreaTerm, MagAdd, RightAngle, ZeroMag,
    ProofStep, StepKind, EProof,
    literal_vars,
)


def _pos(atom):
    return Literal(atom, polarity=True)


def _neg(atom):
    return Literal(atom, polarity=False)


def _proof_from_sequent(name, steps, extra_free_vars=None):
    from .e_library import E_THEOREM_LIBRARY
    thm = E_THEOREM_LIBRARY[name]
    seq = thm.sequent
    free_vars = []
    seen = set()
    for lit in seq.hypotheses:
        for v in literal_vars(lit):
            if v not in seen:
                seen.add(v)
                free_vars.append((v, Sort.POINT))
    if extra_free_vars:
        for v, s in extra_free_vars:
            if v not in seen:
                seen.add(v)
                free_vars.append((v, s))
    return EProof(
        name=name,
        free_vars=free_vars,
        hypotheses=list(seq.hypotheses),
        exists_vars=list(seq.exists_vars),
        goal=list(seq.conclusions),
        steps=steps,
    )

'''


def generate_proofs_module(results: List[TranslationResult],
                           with_comments: bool = True) -> str:
    """Generate a full Python module with all translated proofs."""
    parts = [_MODULE_HEADER]

    for result in sorted(results, key=lambda r: r.prop_number):
        if not result.steps:
            parts.append(
                f"# Prop I.{result.prop_number}: SKIPPED — "
                f"no steps translated\n\n"
            )
            continue
        if with_comments:
            parts.append(translation_to_python_with_comments(result))
        else:
            parts.append(translation_to_python(result))
        parts.append("")

    # Generate the dispatch dict
    parts.append("# ── Dispatch table ──\n")
    parts.append("TRANSLATED_PROOFS = {")
    for result in sorted(results, key=lambda r: r.prop_number):
        if result.steps:
            parts.append(
                f'    "{result.prop_name}": _make_prop_i{result.prop_number},'
            )
    parts.append("}")
    parts.append("")

    return "\n".join(parts)


# ═══════════════════════════════════════════════════════════════════════
# File I/O
# ═══════════════════════════════════════════════════════════════════════

def write_python_module(results: List[TranslationResult],
                        output_path: str,
                        with_comments: bool = True) -> str:
    """Write translated proofs as a Python module."""
    from pathlib import Path
    content = generate_proofs_module(results, with_comments=with_comments)
    Path(output_path).write_text(content, encoding="utf-8")
    return output_path


def write_single_factory(result: TranslationResult,
                         output_path: str,
                         with_comments: bool = True) -> str:
    """Write a single factory function to a file."""
    from pathlib import Path
    if with_comments:
        content = translation_to_python_with_comments(result)
    else:
        content = translation_to_python(result)
    Path(output_path).write_text(content, encoding="utf-8")
    return output_path
