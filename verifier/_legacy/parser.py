"""
parser.py — Recursive-descent formula parser and proof-file loader.
"""
from __future__ import annotations
import json, re
from typing import List, Tuple, Optional

from .ast import (
    Formula, Pred, Eq, Neq, Not, And, Or, Iff, Exists, ExistsUnique,
    ExactlyOne, Bottom, ForAll, Seg, ProofLine, Proof, Declarations,
)


class ParseError(Exception):
    def __init__(self, message: str, pos: int = -1):
        self.pos = pos
        super().__init__(message)


_KEYWORDS = frozenset(("ExactlyOne",))

_TOKEN_RE = re.compile("|".join([
    r"(?P<KW>\b(?:ExactlyOne)\b)",
    r"(?P<AND>\u2227)",              # ∧
    r"(?P<OR>\u2228)",               # ∨
    r"(?P<NOT>\u00ac)",              # ¬
    r"(?P<IFF>\u2194)",              # ↔
    r"(?P<BOTTOM>\u22a5)",           # ⊥
    r"(?P<NEQ>\u2260)",              # ≠
    r"(?P<EXISTSU>\u2203!)",         # ∃! (must precede ∃)
    r"(?P<EXISTS>\u2203)",           # ∃
    r"(?P<FORALL>\u2200)",           # ∀
    r"(?P<EQ>=)",
    r"(?P<LP>\()",
    r"(?P<RP>\))",
    r"(?P<COMMA>,)",
    r"(?P<ID>[A-Za-z_][A-Za-z0-9_]*)",
    r"(?P<WS>[ \t\r\n]+)",
]))


def _tokenize(text: str) -> List[Tuple[str, str, int]]:
    tokens = []
    for m in _TOKEN_RE.finditer(text):
        kind = m.lastgroup
        if kind == "WS":
            continue
        val = m.group()
        if kind == "ID" and val in _KEYWORDS:
            kind = "KW"
        tokens.append((kind, val, m.start()))
    return tokens


class _Parser:
    def __init__(self, tokens, raw=""):
        self.tokens = tokens
        self.pos = 0
        self.raw = raw

    def peek(self):
        return self.tokens[self.pos] if self.pos < len(self.tokens) else None

    def advance(self):
        t = self.tokens[self.pos]; self.pos += 1; return t

    def expect(self, kind, value=None):
        t = self.peek()
        if t is None:
            raise ParseError("Unexpected end of input, expected " + kind)
        if t[0] != kind or (value is not None and t[1] != value):
            raise ParseError("Expected " + kind + " but got '" + t[1] + "' at " + str(t[2]), t[2])
        return self.advance()

    def at_end(self):
        return self.pos >= len(self.tokens)

    def parse(self) -> Formula:
        return self._iff()

    def _iff(self):
        left = self._or()
        while self.peek() and self.peek()[0] == "IFF":
            self.advance()
            left = Iff(left, self._or())
        return left

    def _or(self):
        left = self._and()
        while self.peek() and self.peek()[0] == "OR":
            self.advance()
            left = Or(left, self._and())
        return left

    def _and(self):
        left = self._unary()
        while self.peek() and self.peek()[0] == "AND":
            self.advance()
            left = And(left, self._unary())
        return left

    def _unary(self):
        t = self.peek()
        if t is None:
            raise ParseError("Unexpected end of input in formula")
        # ¬ symbol — expects ¬(expr)
        if t[0] == "NOT":
            self.advance(); self.expect("LP")
            inner = self.parse()
            self.expect("RP")
            return Not(inner)
        # ⊥ symbol
        if t[0] == "BOTTOM":
            self.advance()
            return Bottom()
        # ∃ symbol — expects ∃x(...)
        if t[0] == "EXISTS":
            self.advance()
            v = self.expect("ID")
            self.expect("LP")
            body = self.parse(); self.expect("RP")
            return Exists(v[1], body)
        # ∃! symbol — expects ∃!x(...)
        if t[0] == "EXISTSU":
            self.advance()
            v = self.expect("ID")
            self.expect("LP")
            body = self.parse(); self.expect("RP")
            return ExistsUnique(v[1], body)
        # ∀ symbol — expects ∀x(...)
        if t[0] == "FORALL":
            self.advance()
            v = self.expect("ID")
            self.expect("LP")
            body = self.parse(); self.expect("RP")
            return ForAll(v[1], body)
        # ExactlyOne keyword
        if t[0] == "KW" and t[1] == "ExactlyOne":
            self.advance(); self.expect("LP")
            f1 = self.parse(); self.expect("COMMA")
            f2 = self.parse(); self.expect("COMMA")
            f3 = self.parse(); self.expect("RP")
            return ExactlyOne((f1, f2, f3))
        return self._atom()

    def _atom(self):
        t = self.peek()
        if t is None:
            raise ParseError("Unexpected end of input in atom")
        if t[0] == "LP":
            self.advance()
            f = self.parse()
            self.expect("RP")
            return f
        if t[0] != "ID":
            raise ParseError("Expected identifier but got '" + t[1] + "'", t[2])
        ident = self.advance()
        name = ident[1]
        nxt = self.peek()
        if nxt and nxt[0] == "EQ":
            self.advance()
            rhs = self.expect("ID")
            return Eq(name, rhs[1])
        if nxt and nxt[0] == "NEQ":
            self.advance()
            rhs = self.expect("ID")
            return Neq(name, rhs[1])
        if nxt and nxt[0] == "LP":
            self.advance()
            args = self._pred_args()
            self.expect("RP")
            return Pred(name, tuple(args))
        return Pred(name, ())

    def _pred_args(self):
        args = []
        if self.peek() and self.peek()[0] == "RP":
            return args
        args.append(self._one_arg())
        while self.peek() and self.peek()[0] == "COMMA":
            self.advance()
            args.append(self._one_arg())
        return args

    def _one_arg(self):
        tok = self.expect("ID")
        name = tok[1]
        # Nested predicate as argument, e.g. Line(A, B) inside ChosenSide(C, Line(A, B))
        nxt = self.peek()
        if nxt and nxt[0] == "LP":
            self.advance()
            inner_args = self._pred_args()
            self.expect("RP")
            return Pred(name, tuple(inner_args))
        if len(name) == 2 and name[0].isupper() and name[1].isupper():
            return Seg(name[0], name[1])
        return name


def parse_formula(text: str) -> Formula:
    text = text.strip()
    if not text:
        raise ParseError("Empty formula")
    tokens = _tokenize(text)
    if not tokens:
        raise ParseError("No tokens produced")
    p = _Parser(tokens, text)
    result = p.parse()
    if not p.at_end():
        rem = p.peek()
        raise ParseError("Unexpected token '" + rem[1] + "' at " + str(rem[2]), rem[2])
    return result


def parse_proof(data: dict) -> Proof:
    decl = data.get("declarations", {})
    declarations = Declarations(
        points=decl.get("points", []),
        lines=decl.get("lines", []),
    )
    premises_raw = data.get("premises", [])
    goal_raw = data.get("goal", "")

    lines = []
    for ld in data.get("lines", []):
        raw_stmt = ld.get("statement", "")
        try:
            stmt_ast = parse_formula(raw_stmt)
        except ParseError:
            stmt_ast = None
        lines.append(ProofLine(
            id=ld["id"],
            depth=ld.get("depth", 0),
            statement=stmt_ast,
            justification=ld.get("justification", ""),
            refs=ld.get("refs", []),
            meta=ld.get("meta", {}),
            raw=raw_stmt,
        ))

    premise_formulas = []
    for p in premises_raw:
        try:
            premise_formulas.append(parse_formula(p))
        except ParseError as e:
            raise ParseError("Premise: " + str(e))

    goal_formula = None
    if goal_raw:
        try:
            goal_formula = parse_formula(goal_raw)
        except ParseError as e:
            raise ParseError("Goal: " + str(e))

    return Proof(
        name=data.get("name", "untitled"),
        declarations=declarations,
        premises=premises_raw,
        goal=goal_raw,
        lines=lines,
        goal_formula=goal_formula,
        premise_formulas=premise_formulas,
    )


def load_proof(path: str) -> Proof:
    with open(path, "r", encoding="utf-8") as f:
        data = json.load(f)
    return parse_proof(data)
