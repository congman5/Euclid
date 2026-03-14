"""
e_parser.py — Parser for the formal system E (Avigad, Dean, Mumma 2009).

Parses the literal language of System E:
  - Diagrammatic: on(a,L), same-side(a,b,L), between(a,b,c),
                   center(a,α), inside(a,α), intersects(X,Y)
  - Metric:       ab = cd, ab < cd, ab + cd = ef,
                   ∠abc = ∠def, right-angle, △abc = △def
  - Negation:     ¬on(a,L), a ≠ b
  - Equality:     a = b, L = M, ab = cd
  - Sequents:     Γ ⇒ ∃x̄. Δ

Convention from the paper:
  - Lowercase a–z for points
  - Uppercase L–Z (or any uppercase) for lines
  - Greek α,β,γ (or prefixed circle_ names) for circles

For practical use (bridging from existing proofs), we also accept:
  - Uppercase point names (A, B, C) — common in Euclid
  - Any identifier for lines/circles if annotated by context
"""
from __future__ import annotations

import re
from typing import Dict, List, Optional, Set, Tuple, Union

from .e_ast import (
    Sort, Term, Var,
    SegmentTerm, AngleTerm, AreaTerm,
    MagAdd, RightAngle, ZeroMag,
    Atom, On, SameSide, Between, Center, Inside, Intersects,
    Equals, LessThan,
    Literal, Clause, Sequent, EProofLine,
    SymbolInfo,
    mag_sort,
)


# ═══════════════════════════════════════════════════════════════════════
# Exceptions
# ═══════════════════════════════════════════════════════════════════════

class EParseError(Exception):
    def __init__(self, message: str, pos: int = -1):
        self.pos = pos
        super().__init__(message)


# ═══════════════════════════════════════════════════════════════════════
# Tokenizer
# ═══════════════════════════════════════════════════════════════════════

# Unicode symbols used in System E notation
_TOKEN_RE = re.compile("|".join([
    r"(?P<ANGLE_SYM>\u2220)",             # ∠
    r"(?P<TRIANGLE_SYM>\u25b3)",          # △
    r"(?P<NOT>\u00ac)",                    # ¬
    r"(?P<NEQ>\u2260|!=)",                 # ≠ or !=
    r"(?P<LEQ>\u2264)",                    # ≤
    r"(?P<GEQ>\u2265)",                    # ≥
    r"(?P<NLEQ>\u2270)",                   # ≰
    r"(?P<SEQUENT_ARROW>\u21d2)",          # ⇒
    r"(?P<EXISTS>\u2203)",                 # ∃
    r"(?P<AND>\u2227)",                    # ∧
    r"(?P<OR>\u2228)",                     # ∨
    r"(?P<BOT>\u22a5)",                    # ⊥
    r"(?P<LT><)",
    r"(?P<GT>>)",
    r"(?P<EQ>=)",
    r"(?P<PLUS>\+)",
    r"(?P<LP>\()",
    r"(?P<RP>\))",
    r"(?P<COMMA>,)",
    r"(?P<DOT>\.)",
    r"(?P<COLON>:)",
    r"(?P<SEMICOLON>;)",
    # right-angle as a keyword
    r"(?P<RIGHT_ANGLE>right-angle\b)",
    # Hyphenated identifiers (same-side, diff-side)
    r"(?P<HYPH_ID>[a-zA-Z_][a-zA-Z0-9_]*(?:-[a-zA-Z_][a-zA-Z0-9_]*))",
    # Regular identifiers
    r"(?P<ID>[a-zA-Z_\u03b1-\u03c9\u0391-\u03a9][a-zA-Z0-9_\u03b1-\u03c9\u0391-\u03a9]*)",
    # Numeric literal (for 0)
    r"(?P<NUM>[0-9]+)",
    r"(?P<WS>[ \t\r\n]+)",
]))

Token = Tuple[str, str, int]  # (kind, value, position)


def _tokenize(text: str) -> List[Token]:
    tokens: List[Token] = []
    for m in _TOKEN_RE.finditer(text):
        kind = m.lastgroup
        if kind == "WS":
            continue
        val = m.group()
        tokens.append((kind, val, m.start()))
    return tokens


# ═══════════════════════════════════════════════════════════════════════
# Parser
# ═══════════════════════════════════════════════════════════════════════

class EParser:
    """Recursive-descent parser for System E literals and sequents."""

    def __init__(self, tokens: List[Token], raw: str = "",
                 sort_ctx: Optional[Dict[str, Sort]] = None):
        self.tokens = tokens
        self.pos = 0
        self.raw = raw
        # Known sorts for variable names (can be pre-populated)
        self.sort_ctx: Dict[str, Sort] = sort_ctx or {}

    # ── Token navigation ──────────────────────────────────────────────

    def peek(self) -> Optional[Token]:
        return self.tokens[self.pos] if self.pos < len(self.tokens) else None

    def peek_kind(self) -> Optional[str]:
        t = self.peek()
        return t[0] if t else None

    def peek_val(self) -> Optional[str]:
        t = self.peek()
        return t[1] if t else None

    def advance(self) -> Token:
        t = self.tokens[self.pos]
        self.pos += 1
        return t

    def expect(self, kind: str, value: Optional[str] = None) -> Token:
        t = self.peek()
        if t is None:
            raise EParseError(f"Unexpected end of input, expected {kind}")
        if t[0] != kind or (value is not None and t[1] != value):
            raise EParseError(
                f"Expected {kind}"
                + (f"({value})" if value else "")
                + f" but got '{t[1]}' at position {t[2]}", t[2])
        return self.advance()

    def at_end(self) -> bool:
        return self.pos >= len(self.tokens)

    # ── Top-level entry points ────────────────────────────────────────

    def parse_literal(self) -> Literal:
        """Parse a single literal (possibly negated atom)."""
        if self.peek_kind() == "NOT":
            self.advance()
            # ¬atom or ¬(atom)
            if self.peek_kind() == "LP":
                self.advance()
                atom = self._parse_atom()
                self.expect("RP")
            else:
                atom = self._parse_atom()
            return Literal(atom, polarity=False)

        # Check for a ≠ b pattern (identifier ≠ identifier)
        # We need to look ahead without consuming to detect this
        saved = self.pos
        if self.peek_kind() == "ID":
            name_tok = self.advance()
            if self.peek_kind() == "NEQ":
                self.advance()
                rhs = self._expect_name()
                return Literal(Equals(name_tok[1], rhs), polarity=False)
            # Not a ≠ pattern, restore position
            self.pos = saved

        # Inherently-negated T/H predicates → negative literal
        if self.peek_kind() == "ID" and self.peek_val() in (
                "Neq", "NotB", "NotCong", "Para"):
            atom = self._parse_atom()
            return Literal(atom, polarity=False)

        atom = self._parse_atom()
        return Literal(atom, polarity=True)

    def parse_literal_list(self) -> List[Literal]:
        """Parse a comma-separated list of literals."""
        lits: List[Literal] = []
        if self.at_end():
            return lits
        lits.append(self.parse_literal())
        while self.peek_kind() == "COMMA":
            self.advance()
            lits.append(self.parse_literal())
        return lits

    def parse_conjunction(self) -> List[Literal]:
        """Parse literals joined by ∧ (conjunction)."""
        lits: List[Literal] = []
        lits.append(self.parse_literal())
        while self.peek_kind() == "AND":
            self.advance()
            lits.append(self.parse_literal())
        return lits

    def parse_sequent(self) -> Sequent:
        """Parse a sequent: Γ ⇒ ∃x̄. Δ"""
        # Hypotheses
        hyps = self._parse_literal_set()
        self.expect("SEQUENT_ARROW")
        # Existential quantifiers
        evars: List[Tuple[str, Sort]] = []
        if self.peek_kind() == "EXISTS":
            self.advance()
            evars = self._parse_var_list()
            self.expect("DOT")
        # Conclusions
        concs = self._parse_literal_set()
        return Sequent(
            hypotheses=hyps,
            exists_vars=evars,
            conclusions=concs,
        )

    # ── Atom parsing ──────────────────────────────────────────────────

    def _parse_atom(self) -> Atom:
        """Parse an atomic formula.

        Atomic forms:
          on(a, L)              — On
          same-side(a, b, L)    — SameSide
          between(a, b, c)      — Between
          center(a, α)          — Center
          inside(a, α)          — Inside
          intersects(X, Y)      — Intersects
          a = b / L = M         — Equals (diagram sort)
          ab = cd               — Equals (segment magnitude)
          ∠abc = ∠def           — Equals (angle magnitude)
          △abc = △def           — Equals (area magnitude)
          ab < cd               — LessThan
          ab + cd = ef          — Equals with MagAdd
          right-angle           — RightAngle (as a term in equations)
        Also:
          a ≠ b                 — negated Equals (handled at literal level)
        """
        t = self.peek()
        if t is None:
            raise EParseError("Unexpected end of input in atom")

        # ⊥ (bottom / contradiction)
        if t[0] == "BOT":
            self.advance()
            return Equals("_bot", "_bot")  # sentinel for ⊥

        # ∠abc — angle magnitude (start of an equation)
        if t[0] == "ANGLE_SYM":
            return self._parse_magnitude_relation()

        # △abc — area magnitude (start of an equation)
        if t[0] == "TRIANGLE_SYM":
            return self._parse_magnitude_relation()

        # 0 — zero magnitude
        if t[0] == "NUM" and t[1] == "0":
            return self._parse_magnitude_relation()

        # right-angle
        if t[0] == "RIGHT_ANGLE":
            return self._parse_magnitude_relation()

        # Hyphenated identifier: same-side, diff-side, etc.
        if t[0] == "HYPH_ID":
            name = t[1]
            self.advance()
            if name == "same-side":
                self.expect("LP")
                a = self._expect_name()
                self.expect("COMMA")
                b = self._expect_name()
                self.expect("COMMA")
                line = self._expect_name()
                self.expect("RP")
                return SameSide(a, b, line)
            elif name == "diff-side":
                # diff-side(a, b, L) is syntactic sugar for
                # ¬on(a,L) ∧ ¬on(b,L) ∧ ¬same-side(a,b,L)
                # We represent it as ¬same-side for now
                self.expect("LP")
                a = self._expect_name()
                self.expect("COMMA")
                b = self._expect_name()
                self.expect("COMMA")
                line = self._expect_name()
                self.expect("RP")
                return SameSide(a, b, line)  # caller wraps in negation
            raise EParseError(f"Unknown hyphenated relation: {name}", t[2])

        # Regular identifier — could be a relation or a variable name
        if t[0] == "ID":
            name = t[1]

            # Named diagrammatic relations
            if name in ("on", "On"):
                self.advance()
                self.expect("LP")
                point = self._expect_name()
                self.expect("COMMA")
                obj = self._expect_name()
                self.expect("RP")
                return On(point, obj)

            if name in ("between", "Between"):
                self.advance()
                self.expect("LP")
                a = self._expect_name()
                self.expect("COMMA")
                b = self._expect_name()
                self.expect("COMMA")
                c = self._expect_name()
                self.expect("RP")
                return Between(a, b, c)

            if name in ("center", "Center"):
                self.advance()
                self.expect("LP")
                point = self._expect_name()
                self.expect("COMMA")
                circle = self._expect_name()
                self.expect("RP")
                return Center(point, circle)

            if name in ("inside", "Inside"):
                self.advance()
                self.expect("LP")
                point = self._expect_name()
                self.expect("COMMA")
                circle = self._expect_name()
                self.expect("RP")
                return Inside(point, circle)

            if name in ("intersects", "Intersects"):
                self.advance()
                self.expect("LP")
                obj1 = self._expect_name()
                self.expect("COMMA")
                obj2 = self._expect_name()
                self.expect("RP")
                return Intersects(obj1, obj2)

            # ── System T predicates (parsed into E atoms) ─────────
            if name == "B":  # B(a,b,c) → Between(a,b,c)
                self.advance()
                self.expect("LP")
                a = self._expect_name()
                self.expect("COMMA")
                b = self._expect_name()
                self.expect("COMMA")
                c = self._expect_name()
                self.expect("RP")
                return Between(a, b, c)

            if name == "Cong":  # Cong(a,b,c,d) → ab = cd
                self.advance()
                self.expect("LP")
                a = self._expect_name()
                self.expect("COMMA")
                b = self._expect_name()
                self.expect("COMMA")
                c = self._expect_name()
                self.expect("COMMA")
                d = self._expect_name()
                self.expect("RP")
                return Equals(SegmentTerm(a, b), SegmentTerm(c, d))

            if name == "Eq":  # Eq(a,b) → a = b
                self.advance()
                self.expect("LP")
                a = self._expect_name()
                self.expect("COMMA")
                b = self._expect_name()
                self.expect("RP")
                return Equals(a, b)

            if name == "Neq":  # Neq(a,b) → ¬(a = b) — return atom; caller negates
                self.advance()
                self.expect("LP")
                a = self._expect_name()
                self.expect("COMMA")
                b = self._expect_name()
                self.expect("RP")
                return Equals(a, b)  # wrapped as negative literal by caller

            if name == "NotB":  # NotB(a,b,c) → ¬between — atom; caller negates
                self.advance()
                self.expect("LP")
                a = self._expect_name()
                self.expect("COMMA")
                b = self._expect_name()
                self.expect("COMMA")
                c = self._expect_name()
                self.expect("RP")
                return Between(a, b, c)  # wrapped as negative literal by caller

            if name == "NotCong":  # NotCong(a,b,c,d) → ¬(ab=cd) — caller negates
                self.advance()
                self.expect("LP")
                a = self._expect_name()
                self.expect("COMMA")
                b = self._expect_name()
                self.expect("COMMA")
                c = self._expect_name()
                self.expect("COMMA")
                d = self._expect_name()
                self.expect("RP")
                return Equals(SegmentTerm(a, b), SegmentTerm(c, d))

            # ── System H predicates (parsed into E atoms) ─────────
            if name == "IncidL":  # IncidL(a,l) → on(a,l)
                self.advance()
                self.expect("LP")
                point = self._expect_name()
                self.expect("COMMA")
                line = self._expect_name()
                self.expect("RP")
                return On(point, line)

            if name == "BetH":  # BetH(a,b,c) → between(a,b,c)
                self.advance()
                self.expect("LP")
                a = self._expect_name()
                self.expect("COMMA")
                b = self._expect_name()
                self.expect("COMMA")
                c = self._expect_name()
                self.expect("RP")
                return Between(a, b, c)

            if name == "CongH":  # CongH(a,b,c,d) → ab = cd
                self.advance()
                self.expect("LP")
                a = self._expect_name()
                self.expect("COMMA")
                b = self._expect_name()
                self.expect("COMMA")
                c = self._expect_name()
                self.expect("COMMA")
                d = self._expect_name()
                self.expect("RP")
                return Equals(SegmentTerm(a, b), SegmentTerm(c, d))

            if name == "CongaH":  # CongaH(a,b,c,d,e,f) → ∠abc = ∠def
                self.advance()
                self.expect("LP")
                a = self._expect_name()
                self.expect("COMMA")
                b = self._expect_name()
                self.expect("COMMA")
                c = self._expect_name()
                self.expect("COMMA")
                d = self._expect_name()
                self.expect("COMMA")
                e = self._expect_name()
                self.expect("COMMA")
                f = self._expect_name()
                self.expect("RP")
                return Equals(AngleTerm(a, b, c), AngleTerm(d, e, f))

            if name == "SameSideH":  # SameSideH(a,b,l) → same-side(a,b,l)
                self.advance()
                self.expect("LP")
                a = self._expect_name()
                self.expect("COMMA")
                b = self._expect_name()
                self.expect("COMMA")
                line = self._expect_name()
                self.expect("RP")
                return SameSide(a, b, line)

            if name == "EqPt":  # EqPt(a,b) → a = b
                self.advance()
                self.expect("LP")
                a = self._expect_name()
                self.expect("COMMA")
                b = self._expect_name()
                self.expect("RP")
                return Equals(a, b)

            if name == "EqL":  # EqL(l,m) → l = m
                self.advance()
                self.expect("LP")
                a = self._expect_name()
                self.expect("COMMA")
                b = self._expect_name()
                self.expect("RP")
                return Equals(a, b)

            if name == "ColH":  # ColH(a,b,c) → between(a,b,c) (approx)
                self.advance()
                self.expect("LP")
                a = self._expect_name()
                self.expect("COMMA")
                b = self._expect_name()
                self.expect("COMMA")
                c = self._expect_name()
                self.expect("RP")
                return Between(a, b, c)

            if name == "Para":  # Para(l,m) → ¬intersects(l,m) — caller negates
                self.advance()
                self.expect("LP")
                a = self._expect_name()
                self.expect("COMMA")
                b = self._expect_name()
                self.expect("RP")
                return Intersects(a, b)  # wrapped as negative literal by caller

            # After this, it's either:
            #   - an equality/inequality:  a = b, a ≠ b
            #   - a segment magnitude:     ab = cd, ab < cd, ab + bc = ac
            #   - an identifier starting a magnitude expression

            # Check for 2-letter segment name (uppercase pair like AB, or
            # lowercase pair like ab)
            if self._is_segment_name(name):
                self.advance()
                return self._parse_magnitude_relation_from(
                    SegmentTerm(name[0], name[1]))

            # Single identifier — look ahead for = or ≠
            self.advance()
            nxt = self.peek()
            if nxt and nxt[0] == "EQ":
                self.advance()
                # Right side could be a magnitude term or a variable name
                rhs = self._parse_term_or_name()
                if isinstance(rhs, str):
                    return Equals(name, rhs)
                return Equals(name, rhs)

            if nxt and nxt[0] == "NEQ":
                self.advance()
                rhs_name = self._expect_name()
                # a ≠ b is sugar for ¬(a = b), but we return the atom;
                # caller should note the negation is at the Literal level.
                # Actually for parse purposes we return Equals and the
                # caller (parse_literal) should handle ≠ at the token level.
                # Let's represent this as Equals so the literal can negate it.
                return Equals(name, rhs_name)

            if nxt and nxt[0] == "LT":
                self.advance()
                rhs = self._parse_magnitude_term()
                return LessThan(SegmentTerm(name[0], name[1])
                                if self._is_segment_name(name)
                                else Var(name, Sort.POINT), rhs)

            # Bare identifier — could be a variable used in context
            # Return as Equals to self (identity, degenerate — shouldn't happen
            # in well-formed input)
            raise EParseError(
                f"Unexpected identifier '{name}' — expected a relation or "
                f"equation", t[2])

        # Parenthesized magnitude expression: (expr + expr) = ...
        if t[0] == "LP":
            return self._parse_magnitude_relation()

        raise EParseError(f"Unexpected token '{t[1]}' at position {t[2]}", t[2])

    # ── Magnitude expression parsing ──────────────────────────────────

    def _parse_magnitude_relation(self) -> Atom:
        """Parse a magnitude relation starting from the current position.

        E.g., ab = cd, ∠abc = ∠def, ab + bc = ac, ab < cd
        """
        lhs = self._parse_magnitude_term()
        return self._parse_magnitude_relation_from(lhs)

    @staticmethod
    def _fix_zero_sort(lhs: Term, rhs: Term) -> Tuple[Term, Term]:
        """Infer the correct sort for ZeroMag from the other operand.

        The parser creates ``ZeroMag(Sort.SEGMENT)`` as a default when
        it encounters a bare ``0``.  This method corrects the sort to
        match the other operand (e.g. ``∠abc = 0`` → ``ZeroMag(ANGLE)``).
        """
        if isinstance(rhs, ZeroMag):
            s = mag_sort(lhs)
            if s is not None and s != rhs.sort:
                rhs = ZeroMag(s)
        if isinstance(lhs, ZeroMag):
            s = mag_sort(rhs)
            if s is not None and s != lhs.sort:
                lhs = ZeroMag(s)
        return lhs, rhs

    def _parse_magnitude_relation_from(self, lhs: Term) -> Atom:
        """Given a parsed LHS term, parse the rest of the relation."""
        t = self.peek()
        if t is None:
            raise EParseError("Expected = or < after magnitude term")

        if t[0] == "EQ":
            self.advance()
            rhs = self._parse_magnitude_term()
            lhs, rhs = self._fix_zero_sort(lhs, rhs)
            return Equals(lhs, rhs)

        if t[0] == "LT":
            self.advance()
            rhs = self._parse_magnitude_term()
            lhs, rhs = self._fix_zero_sort(lhs, rhs)
            return LessThan(lhs, rhs)

        if t[0] == "LEQ":
            # a ≤ b is sugar for ¬(b < a)
            self.advance()
            rhs = self._parse_magnitude_term()
            lhs, rhs = self._fix_zero_sort(lhs, rhs)
            return LessThan(rhs, lhs)  # caller should negate

        if t[0] == "NEQ":
            self.advance()
            rhs = self._parse_magnitude_term()
            lhs, rhs = self._fix_zero_sort(lhs, rhs)
            return Equals(lhs, rhs)  # caller wraps with polarity=False

        # If we have a + next, it's part of a larger expression
        if t[0] == "PLUS":
            self.advance()
            rhs_add = self._parse_magnitude_term()
            combined = MagAdd(lhs, rhs_add)
            return self._parse_magnitude_relation_from(combined)

        raise EParseError(
            f"Expected =, <, ≤, or + after magnitude term, got '{t[1]}'", t[2])

    def _parse_magnitude_term(self) -> Term:
        """Parse a magnitude term, possibly with + additions.

        Terms: ab, ∠abc, △abc, right-angle, 0, (expr), expr + expr
        """
        left = self._parse_mag_primary()
        while self.peek_kind() == "PLUS":
            self.advance()
            right = self._parse_mag_primary()
            left = MagAdd(left, right)
        return left

    def _parse_mag_primary(self) -> Term:
        """Parse a primary magnitude term (no + at this level)."""
        t = self.peek()
        if t is None:
            raise EParseError("Expected magnitude term")

        # ∠abc
        if t[0] == "ANGLE_SYM":
            self.advance()
            name = self._expect_name()
            if len(name) >= 3:
                return AngleTerm(name[0], name[1], name[2])
            # Might be separate tokens: ∠ a b c
            a = name
            b = self._expect_name()
            c = self._expect_name()
            return AngleTerm(a, b, c)

        # △abc
        if t[0] == "TRIANGLE_SYM":
            self.advance()
            name = self._expect_name()
            if len(name) >= 3:
                return AreaTerm(name[0], name[1], name[2])
            a = name
            b = self._expect_name()
            c = self._expect_name()
            return AreaTerm(a, b, c)

        # right-angle
        if t[0] == "RIGHT_ANGLE":
            self.advance()
            return RightAngle()

        # 0
        if t[0] == "NUM" and t[1] == "0":
            self.advance()
            return ZeroMag(Sort.SEGMENT)  # sort determined by context later

        # Parenthesized expression
        if t[0] == "LP":
            self.advance()
            inner = self._parse_magnitude_term()
            self.expect("RP")
            return inner

        # Identifier — two-letter segment (ab, AB) or named variable
        if t[0] == "ID":
            name = t[1]
            if self._is_segment_name(name):
                self.advance()
                return SegmentTerm(name[0], name[1])
            # Could be a single-letter point followed by another to make
            # a segment. E.g. "a" then "b" for segment ab.
            # For now, treat unknown identifiers as variable references.
            self.advance()
            return Var(name, self.sort_ctx.get(name, Sort.POINT))

        raise EParseError(
            f"Expected magnitude term, got '{t[1]}' at position {t[2]}", t[2])

    # ── Helper methods ────────────────────────────────────────────────

    def _expect_name(self) -> str:
        """Expect and return an identifier name."""
        t = self.peek()
        if t and t[0] == "ID":
            self.advance()
            return t[1]
        if t and t[0] == "HYPH_ID":
            self.advance()
            return t[1]
        if t is None:
            raise EParseError("Unexpected end of input, expected identifier")
        raise EParseError(
            f"Expected identifier, got '{t[1]}' at position {t[2]}", t[2])

    def _parse_term_or_name(self) -> Union[str, Term]:
        """Parse either a magnitude term or a plain variable name."""
        t = self.peek()
        if t is None:
            raise EParseError("Expected term or name")
        if t[0] == "ANGLE_SYM":
            return self._parse_mag_primary()
        if t[0] == "TRIANGLE_SYM":
            return self._parse_mag_primary()
        if t[0] == "RIGHT_ANGLE":
            return self._parse_mag_primary()
        if t[0] == "NUM" and t[1] == "0":
            return self._parse_mag_primary()
        if t[0] == "ID":
            name = t[1]
            if self._is_segment_name(name):
                self.advance()
                result: Union[str, Term] = SegmentTerm(name[0], name[1])
                # Check for + continuation
                if self.peek_kind() == "PLUS":
                    self.advance()
                    rhs = self._parse_magnitude_term()
                    result = MagAdd(result, rhs)
                return result
            self.advance()
            return name
        raise EParseError(
            f"Expected term or name, got '{t[1]}'", t[2])

    def _is_segment_name(self, name: str) -> bool:
        """Check if a name looks like a 2-letter segment (e.g. 'ab', 'AB')."""
        return (len(name) == 2 and name[0].isalpha() and name[1].isalpha()
                and name[0] != name[1])

    def _parse_literal_set(self) -> List[Literal]:
        """Parse a comma-separated set of literals (for sequent form)."""
        lits: List[Literal] = []
        if self.at_end() or self.peek_kind() == "SEQUENT_ARROW":
            return lits
        lits.append(self.parse_literal())
        while self.peek_kind() == "COMMA":
            self.advance()
            lits.append(self.parse_literal())
        return lits

    def _parse_var_list(self) -> List[Tuple[str, Sort]]:
        """Parse a list of variable declarations for ∃ quantifier.

        Format: ∃a, L, α  or  ∃a:point, L:line
        """
        vars_: List[Tuple[str, Sort]] = []
        name = self._expect_name()
        sort = self._infer_sort(name)
        if self.peek_kind() == "COLON":
            self.advance()
            sort = self._parse_sort()
        vars_.append((name, sort))
        while self.peek_kind() == "COMMA":
            # Disambiguate: is the next comma separating ∃-vars or literals?
            saved = self.pos
            self.advance()
            t = self.peek()
            if t and t[0] == "ID" and not self._looks_like_literal_start():
                name = self._expect_name()
                sort = self._infer_sort(name)
                if self.peek_kind() == "COLON":
                    self.advance()
                    sort = self._parse_sort()
                vars_.append((name, sort))
            else:
                # Wasn't a variable — backtrack
                self.pos = saved
                break
        return vars_

    def _looks_like_literal_start(self) -> bool:
        """Heuristic: does the next token sequence look like a literal?"""
        t = self.peek()
        if t is None:
            return False
        if t[0] in ("NOT", "BOT", "ANGLE_SYM", "TRIANGLE_SYM"):
            return True
        if t[0] == "HYPH_ID" and t[1] in ("same-side", "diff-side"):
            return True
        if t[0] == "ID" and t[1] in (
                "on", "On", "between", "Between",
                "center", "Center", "inside", "Inside",
                "intersects", "Intersects",
                # System T
                "B", "Cong", "Eq", "Neq", "NotB", "NotCong",
                # System H
                "IncidL", "BetH", "CongH", "CongaH", "ColH",
                "EqPt", "EqL", "Para", "SameSideH",
        ):
            return True
        return False

    def _parse_sort(self) -> Sort:
        """Parse an explicit sort annotation."""
        name = self._expect_name()
        sort_map = {
            "point": Sort.POINT, "Point": Sort.POINT,
            "line": Sort.LINE, "Line": Sort.LINE,
            "circle": Sort.CIRCLE, "Circle": Sort.CIRCLE,
        }
        if name in sort_map:
            return sort_map[name]
        raise EParseError(f"Unknown sort: {name}")

    def _infer_sort(self, name: str) -> Sort:
        """Infer the sort of a variable from its name (convention-based)."""
        if name in self.sort_ctx:
            return self.sort_ctx[name]
        # Paper convention: a-z for points, L-Z for lines, Greek for circles
        if len(name) == 1:
            c = name[0]
            if c.islower():
                return Sort.POINT
            if c.isupper() and c >= 'L':
                return Sort.LINE
        # Greek letters
        if any('\u03b1' <= ch <= '\u03c9' or '\u0391' <= ch <= '\u03a9'
               for ch in name):
            return Sort.CIRCLE
        # Default: point (most common in practice)
        return Sort.POINT


# ═══════════════════════════════════════════════════════════════════════
# Public API
# ═══════════════════════════════════════════════════════════════════════

def parse_literal(text: str,
                  sort_ctx: Optional[Dict[str, Sort]] = None) -> Literal:
    """Parse a single System E literal from text."""
    text = text.strip()
    if not text:
        raise EParseError("Empty literal")
    tokens = _tokenize(text)
    if not tokens:
        raise EParseError("No tokens produced")

    # Handle ≠ at the top level: a ≠ b → Literal(Equals(a,b), polarity=False)
    if len(tokens) >= 3 and tokens[1][0] == "NEQ":
        # Simple case: name ≠ name
        lhs = tokens[0][1]
        rhs = tokens[2][1]
        return Literal(Equals(lhs, rhs), polarity=False)

    p = EParser(tokens, text, sort_ctx)
    result = p.parse_literal()
    if not p.at_end():
        rem = p.peek()
        raise EParseError(
            f"Unexpected token '{rem[1]}' at position {rem[2]}", rem[2])
    return result


def parse_literal_list(text: str,
                       sort_ctx: Optional[Dict[str, Sort]] = None
                       ) -> List[Literal]:
    """Parse a comma-separated list of System E literals."""
    text = text.strip()
    if not text:
        return []
    tokens = _tokenize(text)
    p = EParser(tokens, text, sort_ctx)
    result = p.parse_literal_list()
    if not p.at_end():
        rem = p.peek()
        raise EParseError(
            f"Unexpected token '{rem[1]}' at position {rem[2]}", rem[2])
    return result


def parse_conjunction(text: str,
                      sort_ctx: Optional[Dict[str, Sort]] = None
                      ) -> List[Literal]:
    """Parse literals joined by ∧."""
    text = text.strip()
    if not text:
        return []
    tokens = _tokenize(text)
    p = EParser(tokens, text, sort_ctx)
    result = p.parse_conjunction()
    if not p.at_end():
        rem = p.peek()
        raise EParseError(
            f"Unexpected token '{rem[1]}' at position {rem[2]}", rem[2])
    return result


def parse_sequent(text: str,
                  sort_ctx: Optional[Dict[str, Sort]] = None) -> Sequent:
    """Parse a System E sequent: Γ ⇒ ∃x̄. Δ"""
    text = text.strip()
    if not text:
        raise EParseError("Empty sequent")
    tokens = _tokenize(text)
    p = EParser(tokens, text, sort_ctx)
    result = p.parse_sequent()
    if not p.at_end():
        rem = p.peek()
        raise EParseError(
            f"Unexpected token '{rem[1]}' at position {rem[2]}", rem[2])
    return result


def parse_magnitude_eq(text: str,
                       sort_ctx: Optional[Dict[str, Sort]] = None) -> Atom:
    """Parse a magnitude equation like 'ab = cd' or 'ab + bc = ac'."""
    text = text.strip()
    if not text:
        raise EParseError("Empty magnitude equation")
    tokens = _tokenize(text)
    p = EParser(tokens, text, sort_ctx)
    atom = p._parse_magnitude_relation()
    if not p.at_end():
        rem = p.peek()
        raise EParseError(
            f"Unexpected token '{rem[1]}' at position {rem[2]}", rem[2])
    return atom
