"""
lean_parser.py — Parse LeanEuclid .lean files into a structured IR.

Extracts theorem signatures, proof tactics (euclid_apply, euclid_assert,
euclid_finish, by_contra, by_cases, constructor, etc.), variable bindings,
and imports from LeanEuclid Book I proposition files.

This is a line-oriented regex parser — LeanEuclid proofs have a very
regular structure that doesn't require a full Lean grammar.
"""
from __future__ import annotations

import re
from dataclasses import dataclass, field
from enum import Enum, auto
from pathlib import Path
from typing import Any, Dict, List, Optional, Tuple


# ═══════════════════════════════════════════════════════════════════════
# IR data types
# ═══════════════════════════════════════════════════════════════════════

class TacticKind(Enum):
    """Kinds of proof tactics found in LeanEuclid proofs."""
    EUCLID_APPLY = auto()       # euclid_apply (rule args) as vars
    EUCLID_ASSERT = auto()      # euclid_assert (expr)
    EUCLID_FINISH = auto()      # euclid_finish
    EUCLID_INTROS = auto()      # euclid_intros
    BY_CONTRA = auto()          # by_contra
    BY_CASES = auto()           # by_cases (expr)
    CONSTRUCTOR = auto()        # constructor
    HAVE = auto()               # have : expr := by ...
    USE = auto()                # use var, var, ...
    SPLIT_ORS = auto()          # split_ors
    CASE_BRANCH = auto()        # · or . (case separator)
    COMMENT = auto()            # -- comment


@dataclass
class LeanTactic:
    """A single tactic line from a LeanEuclid proof."""
    kind: TacticKind
    raw: str                          # original line text (stripped)
    rule_name: str = ""               # for EUCLID_APPLY: the rule being applied
    rule_args: List[str] = field(default_factory=list)  # arguments to the rule
    bound_vars: List[str] = field(default_factory=list)  # "as x" bindings
    assertion_expr: str = ""          # for EUCLID_ASSERT / HAVE
    case_expr: str = ""               # for BY_CASES
    depth: int = 0                    # nesting depth (by_contra / by_cases)
    line_number: int = 0              # line number in source file
    comment: str = ""                 # for COMMENT kind


@dataclass
class LeanParam:
    """A parameter from a theorem signature."""
    name: str
    sort: str  # "Point", "Line", "Circle", "Segment", etc.


@dataclass
class LeanTheoremSig:
    """Parsed theorem signature from a LeanEuclid file."""
    name: str                                    # e.g. "proposition_16"
    params: List[LeanParam] = field(default_factory=list)
    hypothesis_raw: str = ""                     # raw hypothesis string
    conclusion_raw: str = ""                     # raw conclusion string
    full_sig: str = ""                           # full raw signature


@dataclass
class LeanProof:
    """A fully parsed LeanEuclid proof."""
    theorem_name: str                            # e.g. "proposition_16"
    file_path: str = ""
    imports: List[str] = field(default_factory=list)
    signature: Optional[LeanTheoremSig] = None
    tactics: List[LeanTactic] = field(default_factory=list)
    variants: List['LeanProof'] = field(default_factory=list)  # proposition_N' etc.
    raw_source: str = ""


# ═══════════════════════════════════════════════════════════════════════
# Regex patterns for LeanEuclid syntax
# ═══════════════════════════════════════════════════════════════════════

_RE_IMPORT = re.compile(r'^import\s+(.+)$')
_RE_NAMESPACE = re.compile(r'^namespace\s+(.+)$')
_RE_END_NAMESPACE = re.compile(r'^end\s+(.+)$')
_RE_THEOREM = re.compile(
    r'^(?:set_option\s+\w+\s+\d+\s+in\s+)?theorem\s+(\w+)\s*:'
)
_RE_EUCLID_APPLY_NO_PARENS = re.compile(
    r'euclid_apply\s+(\w+)\s*(?:as\s+\(([^)]+)\)|as\s+([\w\']+))?'
)
_RE_EUCLID_APPLY_START = re.compile(r'euclid_apply\s+\(')
_RE_EUCLID_ASSERT = re.compile(r'euclid_assert\s+(.+)$')
_RE_EUCLID_FINISH = re.compile(r'euclid_finish')
_RE_EUCLID_INTROS = re.compile(r'euclid_intros')
_RE_BY_CONTRA = re.compile(r'by_contra')
_RE_BY_CASES = re.compile(r'by_cases\s+(.+)$')
_RE_CONSTRUCTOR = re.compile(r'^constructor$')
_RE_HAVE = re.compile(r'have\s*:\s*(.+?)\s*:=\s*by')
_RE_HAVE_NAMED = re.compile(r'have\s+(\w+)\s*:\s*(.+?)\s*:=\s*by')
_RE_USE = re.compile(r'use\s+(.+)$')
_RE_SPLIT_ORS = re.compile(r'split_ors')
_RE_CASE_BRANCH = re.compile(r'^[·.]\s*(.*)')
_RE_COMMENT = re.compile(r'^--\s*(.*)')


# ═══════════════════════════════════════════════════════════════════════
# Parser
# ═══════════════════════════════════════════════════════════════════════

def parse_lean_file(filepath: str) -> List[LeanProof]:
    """Parse a LeanEuclid .lean file, returning one LeanProof per theorem."""
    path = Path(filepath)
    source = path.read_text(encoding='utf-8')
    return parse_lean_source(source, str(path))


def parse_lean_source(source: str, filepath: str = "<string>") -> List[LeanProof]:
    """Parse LeanEuclid source text into LeanProof objects."""
    lines = source.split('\n')
    proofs: List[LeanProof] = []

    # Extract imports
    imports = []
    for line in lines:
        m = _RE_IMPORT.match(line.strip())
        if m:
            imports.append(m.group(1).strip())

    # Find theorem blocks
    theorem_ranges = _find_theorem_ranges(lines)

    for thm_name, start_line, end_line in theorem_ranges:
        sig = _parse_signature(lines, start_line)
        tactics = _parse_tactics(lines, start_line, end_line)
        proof = LeanProof(
            theorem_name=thm_name,
            file_path=filepath,
            imports=imports,
            signature=sig,
            tactics=tactics,
            raw_source='\n'.join(lines[start_line:end_line]),
        )
        proofs.append(proof)

    # Group variants (proposition_N' etc.) under the base theorem
    if proofs:
        base = proofs[0]
        for p in proofs[1:]:
            base.variants.append(p)

    return proofs


def _find_theorem_ranges(lines: List[str]) -> List[Tuple[str, int, int]]:
    """Find (theorem_name, start_line_idx, end_line_idx) for each theorem."""
    ranges = []
    i = 0
    while i < len(lines):
        stripped = lines[i].strip()
        # Handle set_option ... in theorem ...
        m = _RE_THEOREM.match(stripped)
        if m:
            thm_name = m.group(1)
            start = i
            # Find the end: next theorem or end namespace
            end = _find_theorem_end(lines, i + 1)
            ranges.append((thm_name, start, end))
            i = end
        else:
            i += 1
    return ranges


def _find_theorem_end(lines: List[str], start: int) -> int:
    """Find the end of a theorem block (next theorem, end namespace, or EOF)."""
    for i in range(start, len(lines)):
        stripped = lines[i].strip()
        if _RE_THEOREM.match(stripped):
            return i
        if _RE_END_NAMESPACE.match(stripped):
            return i
    return len(lines)


def _parse_signature(lines: List[str], start: int) -> LeanTheoremSig:
    """Parse the theorem signature starting at the given line."""
    # Collect lines until we see ':=' or 'by'
    sig_lines = []
    thm_name = ""
    for i in range(start, min(start + 20, len(lines))):
        stripped = lines[i].strip()
        sig_lines.append(stripped)

        if not thm_name:
            m = _RE_THEOREM.match(stripped)
            if m:
                thm_name = m.group(1)

        if stripped.endswith('by') or ':= by' in stripped:
            break

    full_sig = ' '.join(sig_lines)

    # Parse parameters: ∀ (a b c : Point) (L M : Line) ...
    params = _extract_params(full_sig)

    # Split hypothesis and conclusion at →
    hyp_raw, concl_raw = _split_hypothesis_conclusion(full_sig)

    return LeanTheoremSig(
        name=thm_name,
        params=params,
        hypothesis_raw=hyp_raw,
        conclusion_raw=concl_raw,
        full_sig=full_sig,
    )


def _extract_params(sig: str) -> List[LeanParam]:
    """Extract typed parameters from a theorem signature."""
    params = []
    # Match patterns like (a b c : Point) or (AB BC AC : Line)
    for m in re.finditer(r'\(([^)]+)\)', sig):
        group = m.group(1)
        if ':' in group:
            parts = group.split(':')
            if len(parts) == 2:
                names_part = parts[0].strip()
                sort_part = parts[1].strip()
                for name in names_part.split():
                    name = name.strip().strip(',')
                    if name and name not in ('∀',):
                        params.append(LeanParam(name=name, sort=sort_part))
    return params


def _split_hypothesis_conclusion(sig: str) -> Tuple[str, str]:
    """Split a theorem signature into hypothesis and conclusion."""
    # Find the last → that separates hypothesis from conclusion
    # The conclusion is everything after the last →
    # But we need to be careful about nested arrows
    arrow_idx = sig.rfind('→')
    if arrow_idx == -1:
        return ("", sig)

    hyp = sig[:arrow_idx].strip()
    concl = sig[arrow_idx + 1:].strip()
    # Remove trailing ':= by' or 'by'
    concl = re.sub(r'\s*:=\s*by\s*$', '', concl).strip()
    concl = re.sub(r'\s*by\s*$', '', concl).strip()
    return (hyp, concl)


def _parse_tactics(lines: List[str], start: int, end: int) -> List[LeanTactic]:
    """Parse all tactics within a theorem block."""
    tactics = []
    depth = 0

    # Skip to 'by' line
    proof_start = start
    for i in range(start, end):
        stripped = lines[i].strip()
        if stripped.endswith('by') or ':= by' in stripped:
            proof_start = i + 1
            break

    for i in range(proof_start, end):
        raw = lines[i]
        stripped = raw.strip()
        if not stripped:
            continue

        # Track depth from indentation and case branches
        tactic = _parse_single_tactic(stripped, depth, i + 1)
        if tactic:
            tactics.append(tactic)
            # Adjust depth for nesting
            if tactic.kind == TacticKind.BY_CONTRA:
                depth += 1
            elif tactic.kind == TacticKind.BY_CASES:
                depth += 1
            elif tactic.kind == TacticKind.CASE_BRANCH:
                pass  # depth stays at current level

    return tactics


def _extract_balanced_parens(text: str, open_pos: int) -> Tuple[Optional[str], str]:
    """Extract content of balanced parentheses starting at open_pos.

    Returns (content_inside_parens, rest_of_string_after_close_paren).
    If no balanced close paren is found, returns (None, "").
    """
    if open_pos >= len(text) or text[open_pos] != '(':
        return None, ""
    depth = 0
    for i in range(open_pos, len(text)):
        if text[i] == '(':
            depth += 1
        elif text[i] == ')':
            depth -= 1
            if depth == 0:
                content = text[open_pos + 1:i]
                rest = text[i + 1:]
                return content, rest
    return None, ""


_RE_AS_BINDING = re.compile(
    r'\s*as\s+(?:\(([^)]+)\)|([\w\']+))')


def _extract_as_bindings(rest: str) -> List[str]:
    """Extract bound variable names from '... as x' or '... as (x, y)' suffix."""
    m = _RE_AS_BINDING.search(rest)
    if not m:
        return []
    group_multi = m.group(1)
    group_single = m.group(2)
    if group_multi:
        return [v.strip() for v in group_multi.split(',')]
    elif group_single:
        return [group_single]
    return []


def _parse_single_tactic(line: str, depth: int, line_number: int) -> Optional[LeanTactic]:
    """Parse a single line into a LeanTactic."""

    # Comment
    m = _RE_COMMENT.match(line)
    if m:
        return LeanTactic(kind=TacticKind.COMMENT, raw=line,
                          comment=m.group(1), depth=depth,
                          line_number=line_number)

    # Case branch marker
    m = _RE_CASE_BRANCH.match(line)
    if m:
        rest = m.group(1).strip()
        tactic = LeanTactic(kind=TacticKind.CASE_BRANCH, raw=line,
                            depth=depth, line_number=line_number)
        # If the rest of the line contains a tactic, parse it too
        if rest:
            inner = _parse_single_tactic(rest, depth, line_number)
            if inner:
                tactic.assertion_expr = inner.raw
        return tactic

    # euclid_intros
    if _RE_EUCLID_INTROS.search(line):
        return LeanTactic(kind=TacticKind.EUCLID_INTROS, raw=line,
                          depth=depth, line_number=line_number)

    # euclid_finish
    if _RE_EUCLID_FINISH.search(line):
        return LeanTactic(kind=TacticKind.EUCLID_FINISH, raw=line,
                          depth=depth, line_number=line_number)

    # euclid_apply with parenthesized arguments (balanced-paren extraction)
    m = _RE_EUCLID_APPLY_START.search(line)
    if m:
        rule_call, rest = _extract_balanced_parens(line, m.end() - 1)
        if rule_call is not None:
            rule_name, rule_args = _parse_rule_call(rule_call.strip())
            bound_vars = _extract_as_bindings(rest)
            return LeanTactic(kind=TacticKind.EUCLID_APPLY, raw=line,
                              rule_name=rule_name, rule_args=rule_args,
                              bound_vars=bound_vars, depth=depth,
                              line_number=line_number)

    # euclid_apply without parentheses (e.g. euclid_apply some_lemma)
    m = _RE_EUCLID_APPLY_NO_PARENS.search(line)
    if m:
        rule_name = m.group(1).strip()
        bound_group = m.group(2)
        bound_single = m.group(3)
        bound_vars = []
        if bound_group:
            bound_vars = [v.strip() for v in bound_group.split(',')]
        elif bound_single:
            bound_vars = [bound_single]
        return LeanTactic(kind=TacticKind.EUCLID_APPLY, raw=line,
                          rule_name=rule_name, rule_args=[],
                          bound_vars=bound_vars, depth=depth,
                          line_number=line_number)

    # euclid_assert
    m = _RE_EUCLID_ASSERT.search(line)
    if m:
        return LeanTactic(kind=TacticKind.EUCLID_ASSERT, raw=line,
                          assertion_expr=m.group(1).strip(), depth=depth,
                          line_number=line_number)

    # by_contra
    if _RE_BY_CONTRA.search(line):
        return LeanTactic(kind=TacticKind.BY_CONTRA, raw=line,
                          depth=depth, line_number=line_number)

    # by_cases
    m = _RE_BY_CASES.search(line)
    if m:
        return LeanTactic(kind=TacticKind.BY_CASES, raw=line,
                          case_expr=m.group(1).strip(), depth=depth,
                          line_number=line_number)

    # constructor
    if _RE_CONSTRUCTOR.match(line):
        return LeanTactic(kind=TacticKind.CONSTRUCTOR, raw=line,
                          depth=depth, line_number=line_number)

    # split_ors
    if _RE_SPLIT_ORS.search(line):
        return LeanTactic(kind=TacticKind.SPLIT_ORS, raw=line,
                          depth=depth, line_number=line_number)

    # have (named or unnamed)
    m = _RE_HAVE_NAMED.search(line)
    if m:
        return LeanTactic(kind=TacticKind.HAVE, raw=line,
                          rule_name=m.group(1),
                          assertion_expr=m.group(2).strip(),
                          depth=depth, line_number=line_number)
    m = _RE_HAVE.search(line)
    if m:
        return LeanTactic(kind=TacticKind.HAVE, raw=line,
                          assertion_expr=m.group(1).strip(),
                          depth=depth, line_number=line_number)

    # use
    m = _RE_USE.search(line)
    if m:
        vars_str = m.group(1).strip()
        bound = [v.strip() for v in vars_str.split(',')]
        return LeanTactic(kind=TacticKind.USE, raw=line,
                          bound_vars=bound, depth=depth,
                          line_number=line_number)

    # Fallback: unknown tactic line
    return None


def _parse_rule_call(call_str: str) -> Tuple[str, List[str]]:
    """Parse a rule call like 'proposition_16 a b c d AB BC AC'
    into (rule_name, [args])."""
    parts = call_str.split()
    if not parts:
        return ("", [])
    rule_name = parts[0]
    args = parts[1:]
    return (rule_name, args)


# ═══════════════════════════════════════════════════════════════════════
# Expression parser for Lean metric expressions
# ═══════════════════════════════════════════════════════════════════════

@dataclass
class LeanExpr:
    """A parsed Lean metric/angle/segment expression."""
    kind: str  # "angle", "segment", "area", "right_angle", "add", "eq", "gt", "lt", "neg"
    children: List[Any] = field(default_factory=list)
    points: List[str] = field(default_factory=list)
    value: str = ""


def parse_lean_expr(expr_str: str) -> Optional[LeanExpr]:
    """Parse a Lean expression like '∠ a:b:c > ∠ d:e:f' or '|(a─b)| = |(c─d)|'."""
    expr = expr_str.strip()

    # Negation
    if expr.startswith('¬'):
        inner = expr[1:].strip()
        if inner.startswith('(') and inner.endswith(')'):
            inner = inner[1:-1]
        child = parse_lean_expr(inner)
        if child:
            return LeanExpr(kind="neg", children=[child])

    # Equality
    if ' = ' in expr:
        left, right = expr.split(' = ', 1)
        l = parse_lean_expr(left.strip())
        r = parse_lean_expr(right.strip())
        if l and r:
            return LeanExpr(kind="eq", children=[l, r])

    # Greater than
    if ' > ' in expr:
        left, right = expr.split(' > ', 1)
        l = parse_lean_expr(left.strip())
        r = parse_lean_expr(right.strip())
        if l and r:
            return LeanExpr(kind="gt", children=[l, r])

    # Less than
    if ' < ' in expr:
        left, right = expr.split(' < ', 1)
        l = parse_lean_expr(left.strip())
        r = parse_lean_expr(right.strip())
        if l and r:
            return LeanExpr(kind="lt", children=[l, r])

    # Addition
    if ' + ' in expr:
        left, right = expr.split(' + ', 1)
        l = parse_lean_expr(left.strip())
        r = parse_lean_expr(right.strip())
        if l and r:
            return LeanExpr(kind="add", children=[l, r])

    # Multiplication (for area: a * a)
    if ' * ' in expr:
        left, right = expr.split(' * ', 1)
        l = parse_lean_expr(left.strip())
        r = parse_lean_expr(right.strip())
        if l and r:
            return LeanExpr(kind="mul", children=[l, r])

    # Angle: ∠ a:b:c  or  (∠ a:b:c : ℝ)
    angle_m = re.match(r'\(?∠\s*(\w+):(\w+):(\w+)(?:\s*:\s*ℝ)?\)?', expr)
    if angle_m:
        return LeanExpr(kind="angle",
                        points=[angle_m.group(1), angle_m.group(2),
                                angle_m.group(3)])

    # Right angle: ∟
    if expr.strip() in ('∟', 'rightAngle'):
        return LeanExpr(kind="right_angle")

    # Segment: |(a─b)| or |s|
    seg_m = re.match(r'\|?\(?\s*(\w+)─(\w+)\s*\)?\|?', expr)
    if seg_m:
        return LeanExpr(kind="segment",
                        points=[seg_m.group(1), seg_m.group(2)])

    # Triangle area: Triangle.area △ a:b:c
    area_m = re.match(r'Triangle\.area\s+△\s*(\w+):(\w+):(\w+)', expr)
    if area_m:
        return LeanExpr(kind="area",
                        points=[area_m.group(1), area_m.group(2),
                                area_m.group(3)])

    # Point identity: a.onLine L, a.sameSide b L, etc.
    online_m = re.match(r'(\w+)\.onLine\s+(\w+)', expr)
    if online_m:
        return LeanExpr(kind="on_line",
                        points=[online_m.group(1)],
                        value=online_m.group(2))

    sameside_m = re.match(r'(\w+)\.sameSide\s+(\w+)\s+(\w+)', expr)
    if sameside_m:
        return LeanExpr(kind="same_side",
                        points=[sameside_m.group(1), sameside_m.group(2)],
                        value=sameside_m.group(3))

    # Simple variable/identifier
    if re.match(r'^\w+$', expr):
        return LeanExpr(kind="var", value=expr)

    # 0
    if expr.strip() == '0':
        return LeanExpr(kind="zero")

    return LeanExpr(kind="unknown", value=expr)


# ═══════════════════════════════════════════════════════════════════════
# Utility: extract proposition number
# ═══════════════════════════════════════════════════════════════════════

_RE_PROP_NUM = re.compile(r'proposition_(\d+)')

def extract_prop_number(name: str) -> Optional[int]:
    """Extract the proposition number from a name like 'proposition_16'."""
    m = _RE_PROP_NUM.search(name)
    return int(m.group(1)) if m else None


def prop_system_e_name(n: int) -> str:
    """Convert a proposition number to System E naming: 'Prop.I.16'."""
    return f"Prop.I.{n}"
