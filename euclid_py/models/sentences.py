"""
Sentence Evaluator — ported from sentenceEvaluator.js

Parses and evaluates logical sentences containing geometric predicates.
Supports propositional logic operators and quantifiers.
"""
from __future__ import annotations

import re
import time
from dataclasses import dataclass, field
from enum import Enum
from typing import Any, Callable, Dict, List, Optional, Tuple


# ═══════════════════════════════════════════════════════════════════════════
# SENTENCE AST — Abstract syntax tree for logical sentences
# ═══════════════════════════════════════════════════════════════════════════

class SentenceType(str, Enum):
    PREDICATE = "predicate"
    AND = "and"
    OR = "or"
    NOT = "not"
    IMPLIES = "implies"
    IFF = "iff"
    FORALL = "forall"
    EXISTS = "exists"
    TRUE = "true"
    FALSE = "false"


# Sentence nodes are plain dicts for flexibility (matching JS pattern)

def predicate(name: str, args: List[str]) -> dict:
    return dict(type=SentenceType.PREDICATE, name=name, args=list(args))


def and_sent(*operands: dict) -> dict:
    return dict(type=SentenceType.AND, operands=list(operands))


def or_sent(*operands: dict) -> dict:
    return dict(type=SentenceType.OR, operands=list(operands))


def not_sent(operand: dict) -> dict:
    return dict(type=SentenceType.NOT, operand=operand)


def implies_sent(antecedent: dict, consequent: dict) -> dict:
    return dict(type=SentenceType.IMPLIES, antecedent=antecedent, consequent=consequent)


def iff_sent(left: dict, right: dict) -> dict:
    return dict(type=SentenceType.IFF, left=left, right=right)


def forall_sent(variable: str, body: dict) -> dict:
    return dict(type=SentenceType.FORALL, variable=variable, body=body)


def exists_sent(variable: str, body: dict) -> dict:
    return dict(type=SentenceType.EXISTS, variable=variable, body=body)


TRUE_CONST: dict = dict(type=SentenceType.TRUE)
FALSE_CONST: dict = dict(type=SentenceType.FALSE)


def sentence_to_str(s: Optional[dict]) -> str:
    """Format a sentence AST to a human-readable string."""
    if s is None:
        return "?"
    t = s.get("type")
    if t == SentenceType.PREDICATE:
        return f"{s['name']}({', '.join(str(a) for a in s['args'])})"
    if t == SentenceType.AND:
        return " ∧ ".join(f"({sentence_to_str(o)})" for o in s.get("operands", []))
    if t == SentenceType.OR:
        return " ∨ ".join(f"({sentence_to_str(o)})" for o in s.get("operands", []))
    if t == SentenceType.NOT:
        return f"¬({sentence_to_str(s.get('operand'))})"
    if t == SentenceType.IMPLIES:
        return f"({sentence_to_str(s.get('antecedent'))}) → ({sentence_to_str(s.get('consequent'))})"
    if t == SentenceType.IFF:
        return f"({sentence_to_str(s.get('left'))}) ↔ ({sentence_to_str(s.get('right'))})"
    if t == SentenceType.FORALL:
        return f"∀{s['variable']}. {sentence_to_str(s.get('body'))}"
    if t == SentenceType.EXISTS:
        return f"∃{s['variable']}. {sentence_to_str(s.get('body'))}"
    if t == SentenceType.TRUE:
        return "⊤"
    if t == SentenceType.FALSE:
        return "⊥"
    return str(s)


# ═══════════════════════════════════════════════════════════════════════════
# PREDICATE RESULT — Result of evaluating a predicate
# ═══════════════════════════════════════════════════════════════════════════

@dataclass
class PredicateResult:
    value: Optional[bool]
    explanation: str = ""

    @staticmethod
    def true_(explanation: str = "") -> PredicateResult:
        return PredicateResult(value=True, explanation=explanation)

    @staticmethod
    def false_(explanation: str = "") -> PredicateResult:
        return PredicateResult(value=False, explanation=explanation)

    @staticmethod
    def undefined(explanation: str = "") -> PredicateResult:
        return PredicateResult(value=None, explanation=explanation)


# ═══════════════════════════════════════════════════════════════════════════
# SENTENCE EVALUATION RESULT
# ═══════════════════════════════════════════════════════════════════════════

@dataclass
class SentenceEvaluationResult:
    sentence: Optional[dict]
    value: Optional[bool]
    explanation: str = ""
    trace: List[dict] = field(default_factory=list)

    @property
    def is_true(self) -> bool:
        return self.value is True

    @property
    def is_false(self) -> bool:
        return self.value is False

    @property
    def is_undefined(self) -> bool:
        return self.value is None

    @property
    def indicator(self) -> str:
        if self.value is True:
            return "T"
        if self.value is False:
            return "F"
        return "?"

    @property
    def color(self) -> str:
        if self.value is True:
            return "#388c46"
        if self.value is False:
            return "#c74440"
        return "#666666"


# ═══════════════════════════════════════════════════════════════════════════
# SENTENCE EVALUATOR
# ═══════════════════════════════════════════════════════════════════════════

# Type alias for the predicate evaluator callback
EvalPredicateFunc = Callable[[str, Any, List[str], dict], PredicateResult]


def evaluate_sentence(
    sentence: dict,
    world: Any,
    options: Optional[dict] = None,
    env: Optional[Dict[str, str]] = None,
    evaluate_predicate_fn: Optional[EvalPredicateFunc] = None,
) -> SentenceEvaluationResult:
    """Evaluate a sentence AST against a world."""
    options = options or {}
    env = env or {}
    trace: List[dict] = []
    result = _evaluate(sentence, world, options, env, trace, evaluate_predicate_fn)
    return SentenceEvaluationResult(sentence=sentence, value=result.value,
                                    explanation=result.explanation, trace=trace)


def _evaluate(
    sentence: dict,
    world: Any,
    options: dict,
    env: Dict[str, str],
    trace: List[dict],
    evaluate_predicate_fn: Optional[EvalPredicateFunc],
) -> PredicateResult:
    t = sentence.get("type")

    if t == SentenceType.PREDICATE:
        args = [env.get(a, a) for a in sentence["args"]]
        if evaluate_predicate_fn:
            pred_result = evaluate_predicate_fn(sentence["name"], world, args, options)
        else:
            pred_result = PredicateResult.undefined(f"No predicate evaluator for {sentence['name']}")
        trace.append(dict(
            sentence=f"{sentence['name']}({', '.join(args)})",
            value=pred_result.value,
            explanation=pred_result.explanation,
        ))
        return pred_result

    if t == SentenceType.AND:
        results = [_evaluate(op, world, options, env, trace, evaluate_predicate_fn)
                   for op in sentence.get("operands", [])]
        if any(r.value is False for r in results):
            fail = next(r for r in results if r.value is False)
            return PredicateResult.false_(f"Conjunction false: {fail.explanation}")
        if any(r.value is None for r in results):
            return PredicateResult.undefined("Conjunction undefined")
        return PredicateResult.true_("All conjuncts are true")

    if t == SentenceType.OR:
        results = [_evaluate(op, world, options, env, trace, evaluate_predicate_fn)
                   for op in sentence.get("operands", [])]
        if any(r.value is True for r in results):
            ok = next(r for r in results if r.value is True)
            return PredicateResult.true_(f"Disjunction true: {ok.explanation}")
        if all(r.value is False for r in results):
            return PredicateResult.false_("All disjuncts are false")
        return PredicateResult.undefined("Disjunction undefined")

    if t == SentenceType.NOT:
        result = _evaluate(sentence["operand"], world, options, env, trace, evaluate_predicate_fn)
        if result.value is True:
            return PredicateResult.false_("Negation of true is false")
        if result.value is False:
            return PredicateResult.true_("Negation of false is true")
        return PredicateResult.undefined("Negation of undefined")

    if t == SentenceType.IMPLIES:
        ant = _evaluate(sentence["antecedent"], world, options, env, trace, evaluate_predicate_fn)
        cons = _evaluate(sentence["consequent"], world, options, env, trace, evaluate_predicate_fn)
        if ant.value is False:
            return PredicateResult.true_("Implication vacuously true (antecedent false)")
        if ant.value is True and cons.value is True:
            return PredicateResult.true_("Implication true (both true)")
        if ant.value is True and cons.value is False:
            return PredicateResult.false_("Implication false (true → false)")
        return PredicateResult.undefined("Implication undefined")

    if t == SentenceType.IFF:
        left = _evaluate(sentence["left"], world, options, env, trace, evaluate_predicate_fn)
        right = _evaluate(sentence["right"], world, options, env, trace, evaluate_predicate_fn)
        if left.value is None or right.value is None:
            return PredicateResult.undefined("Biconditional undefined")
        if left.value == right.value:
            return PredicateResult.true_(f"Biconditional true (both {left.value})")
        return PredicateResult.false_(f"Biconditional false ({left.value} ↔ {right.value})")

    if t == SentenceType.FORALL:
        all_points = world.get_all_points() if hasattr(world, "get_all_points") else []
        if not all_points:
            return PredicateResult.true_("Universal vacuously true (empty domain)")
        var = sentence["variable"]
        for pt in all_points:
            label = pt.get("label", pt) if isinstance(pt, dict) else str(pt)
            new_env = {**env, var: label}
            result = _evaluate(sentence["body"], world, options, new_env, trace, evaluate_predicate_fn)
            if result.value is False:
                return PredicateResult.false_(f"∀{var}. ... is false: counterexample {var}={label}")
            if result.value is None:
                return PredicateResult.undefined(f"∀{var}. ... is undefined for {var}={label}")
        return PredicateResult.true_(f"∀{var}. ... is true for all {len(all_points)} points")

    if t == SentenceType.EXISTS:
        all_points = world.get_all_points() if hasattr(world, "get_all_points") else []
        if not all_points:
            return PredicateResult.false_("Existential false (empty domain)")
        var = sentence["variable"]
        has_undefined = False
        for pt in all_points:
            label = pt.get("label", pt) if isinstance(pt, dict) else str(pt)
            new_env = {**env, var: label}
            result = _evaluate(sentence["body"], world, options, new_env, trace, evaluate_predicate_fn)
            if result.value is True:
                return PredicateResult.true_(f"∃{var}. ... is true: witness {var}={label}")
            if result.value is None:
                has_undefined = True
        if has_undefined:
            return PredicateResult.undefined(f"∃{var}. ... is undefined")
        return PredicateResult.false_(f"∃{var}. ... is false: no witness among {len(all_points)} points")

    if t == SentenceType.TRUE:
        return PredicateResult.true_("⊤ is always true")

    if t == SentenceType.FALSE:
        return PredicateResult.false_("⊥ is always false")

    return PredicateResult.undefined(f"Unknown sentence type: {t}")


# ═══════════════════════════════════════════════════════════════════════════
# TOKENIZER
# ═══════════════════════════════════════════════════════════════════════════

@dataclass
class _Token:
    type: str
    value: Optional[str] = None


def _tokenize(text: str) -> List[_Token]:
    tokens: List[_Token] = []
    i = 0
    n = len(text)

    while i < n:
        ch = text[i]

        # whitespace
        if ch.isspace():
            i += 1
            continue

        # AND
        if ch == "∧" or text[i:i+2] == "/\\":
            tokens.append(_Token("AND"))
            i += 1 if ch == "∧" else 2
            continue
        if text[i:i+3].upper() == "AND" and (i+3 >= n or not text[i+3].isalnum()):
            tokens.append(_Token("AND"))
            i += 3
            continue

        # OR
        if ch == "∨" or text[i:i+2] == "\\/":
            tokens.append(_Token("OR"))
            i += 1 if ch == "∨" else 2
            continue
        if text[i:i+2].upper() == "OR" and (i+2 >= n or not text[i+2].isalnum()):
            tokens.append(_Token("OR"))
            i += 2
            continue

        # NOT_EQUALS (≠, ¬=, !=) — must check before plain ¬
        if ch == "≠":
            tokens.append(_Token("NOT_EQUALS"))
            i += 1
            continue
        if (ch == "¬" and i+1 < n and text[i+1] == "=") or text[i:i+2] == "!=":
            tokens.append(_Token("NOT_EQUALS"))
            i += 2
            continue

        # EQUALS
        if ch == "=":
            tokens.append(_Token("EQUALS"))
            i += 1
            continue

        # NOT
        if ch in ("¬", "~"):
            tokens.append(_Token("NOT"))
            i += 1
            continue
        if text[i:i+3].upper() == "NOT" and (i+3 >= n or not text[i+3].isalnum()):
            tokens.append(_Token("NOT"))
            i += 3
            continue

        # IFF (must check before IMPLIES)
        if text[i:i+3] == "<->" or ch == "↔":
            tokens.append(_Token("IFF"))
            i += 1 if ch == "↔" else 3
            continue

        # IMPLIES
        if text[i:i+2] == "->" or ch == "→":
            tokens.append(_Token("IMPLIES"))
            i += 1 if ch == "→" else 2
            continue

        # FORALL
        if ch == "∀":
            tokens.append(_Token("FORALL"))
            i += 1
            continue
        if text[i:i+6].upper() == "FORALL" and (i+6 >= n or not text[i+6].isalnum()):
            tokens.append(_Token("FORALL"))
            i += 6
            continue

        # EXISTS
        if ch == "∃":
            tokens.append(_Token("EXISTS"))
            i += 1
            continue
        if text[i:i+6].upper() == "EXISTS" and (i+6 >= n or not text[i+6].isalnum()):
            tokens.append(_Token("EXISTS"))
            i += 6
            continue

        # LPAREN / RPAREN
        if ch == "(":
            tokens.append(_Token("LPAREN"))
            i += 1
            continue
        if ch == ")":
            tokens.append(_Token("RPAREN"))
            i += 1
            continue

        # COMMA
        if ch == ",":
            tokens.append(_Token("COMMA"))
            i += 1
            continue

        # DOT
        if ch == ".":
            tokens.append(_Token("DOT"))
            i += 1
            continue

        # TRUE / FALSE constants
        if ch == "⊤":
            tokens.append(_Token("TRUE"))
            i += 1
            continue
        if text[i:i+4].upper() == "TRUE" and (i+4 >= n or not text[i+4].isalnum()):
            tokens.append(_Token("TRUE"))
            i += 4
            continue
        if ch == "⊥":
            tokens.append(_Token("FALSE"))
            i += 1
            continue
        if text[i:i+5].upper() == "FALSE" and (i+5 >= n or not text[i+5].isalnum()):
            tokens.append(_Token("FALSE"))
            i += 5
            continue

        # IDENT
        if ch.isalpha() or ch == "_":
            start = i
            while i < n and (text[i].isalnum() or text[i] in ("_", "'")):
                i += 1
            tokens.append(_Token("IDENT", text[start:i]))
            continue

        # unknown — skip
        i += 1

    return tokens


# ═══════════════════════════════════════════════════════════════════════════
# PARSER — tokens → AST
# ═══════════════════════════════════════════════════════════════════════════

class _ParseError(Exception):
    pass


def _parse_tokens(tokens: List[_Token]) -> dict:
    pos = [0]  # mutable counter

    def peek() -> Optional[_Token]:
        return tokens[pos[0]] if pos[0] < len(tokens) else None

    def consume(expected: Optional[str] = None) -> _Token:
        tok = peek()
        if expected and (tok is None or tok.type != expected):
            raise _ParseError(f"Expected {expected} but got {tok.type if tok else 'EOF'}")
        pos[0] += 1
        return tok  # type: ignore[return-value]

    def parse_formula() -> dict:
        return parse_iff()

    def parse_iff() -> dict:
        left = parse_implies()
        while peek() and peek().type == "IFF":  # type: ignore[union-attr]
            consume("IFF")
            right = parse_implies()
            left = iff_sent(left, right)
        return left

    def parse_implies() -> dict:
        left = parse_or()
        while peek() and peek().type == "IMPLIES":  # type: ignore[union-attr]
            consume("IMPLIES")
            right = parse_or()
            left = implies_sent(left, right)
        return left

    def parse_or() -> dict:
        operands = [parse_and()]
        while peek() and peek().type == "OR":  # type: ignore[union-attr]
            consume("OR")
            operands.append(parse_and())
        return operands[0] if len(operands) == 1 else or_sent(*operands)

    def parse_and() -> dict:
        operands = [parse_unary()]
        while peek() and peek().type == "AND":  # type: ignore[union-attr]
            consume("AND")
            operands.append(parse_unary())
        return operands[0] if len(operands) == 1 else and_sent(*operands)

    def parse_unary() -> dict:
        tok = peek()
        if tok and tok.type == "NOT":
            consume("NOT")
            return not_sent(parse_unary())
        if tok and tok.type == "FORALL":
            consume("FORALL")
            variable = consume("IDENT").value
            consume("DOT")
            body = parse_formula()
            return forall_sent(variable, body)
        if tok and tok.type == "EXISTS":
            consume("EXISTS")
            variable = consume("IDENT").value
            consume("DOT")
            body = parse_formula()
            return exists_sent(variable, body)
        return parse_atom()

    def parse_atom() -> dict:
        tok = peek()
        if tok and tok.type == "LPAREN":
            consume("LPAREN")
            formula = parse_formula()
            consume("RPAREN")
            return formula
        if tok and tok.type == "TRUE":
            consume("TRUE")
            return dict(TRUE_CONST)
        if tok and tok.type == "FALSE":
            consume("FALSE")
            return dict(FALSE_CONST)
        if tok and tok.type == "IDENT":
            name = consume("IDENT").value
            # Predicate call
            if peek() and peek().type == "LPAREN":  # type: ignore[union-attr]
                consume("LPAREN")
                args: List[str] = []
                if peek() and peek().type != "RPAREN":  # type: ignore[union-attr]
                    args.append(consume("IDENT").value)
                    while peek() and peek().type == "COMMA":  # type: ignore[union-attr]
                        consume("COMMA")
                        args.append(consume("IDENT").value)
                consume("RPAREN")
                node = predicate(name, args)
                # Infix = or ≠ after predicate
                if peek() and peek().type in ("EQUALS", "NOT_EQUALS"):  # type: ignore[union-attr]
                    is_neg = peek().type == "NOT_EQUALS"  # type: ignore[union-attr]
                    consume(peek().type)  # type: ignore[union-attr]
                    rhs = parse_atom()
                    eq_left = args[0] if name == "Circle" else name
                    eq_right = rhs.get("args", [None])[0] if rhs.get("args") else rhs.get("name", "")
                    eq = predicate("Equal", [eq_left, eq_right])
                    return not_sent(eq) if is_neg else eq
                return node
            # Infix = or ≠ after bare identifier
            if peek() and peek().type in ("EQUALS", "NOT_EQUALS"):  # type: ignore[union-attr]
                is_neg = peek().type == "NOT_EQUALS"  # type: ignore[union-attr]
                consume(peek().type)  # type: ignore[union-attr]
                right = consume("IDENT").value
                first_eq = predicate("Equal", [name, right])
                node = not_sent(first_eq) if is_neg else first_eq
                # Chained equality
                if not is_neg and peek() and peek().type == "EQUALS":  # type: ignore[union-attr]
                    equalities = [first_eq]
                    prev = right
                    while peek() and peek().type == "EQUALS":  # type: ignore[union-attr]
                        consume("EQUALS")
                        nxt = consume("IDENT").value
                        equalities.append(predicate("Equal", [prev, nxt]))
                        prev = nxt
                    return equalities[0] if len(equalities) == 1 else and_sent(*equalities)
                return node
            # Bare identifier → default to Point
            return predicate("Point", [name])

        raise _ParseError(f"Unexpected token: {tok.type if tok else 'EOF'}")

    ast = parse_formula()
    if pos[0] < len(tokens):
        raise _ParseError("Unexpected tokens after formula")
    return ast


def parse_sentence(text: str) -> dict:
    """Parse a sentence string to an AST."""
    tokens = _tokenize(text)
    return _parse_tokens(tokens)


# ═══════════════════════════════════════════════════════════════════════════
# SENTENCE LIST — A collection of sentences (like Tarski's sentence file)
# ═══════════════════════════════════════════════════════════════════════════

@dataclass
class _SentenceEntry:
    id: str
    text: str
    ast: Optional[dict] = None
    parse_error: Optional[str] = None
    result: Optional[SentenceEvaluationResult] = None


class SentenceList:
    """A collection of sentences to be evaluated against a world."""

    def __init__(self, name: str = "Untitled Sentences") -> None:
        self.name = name
        self.sentences: List[_SentenceEntry] = []
        self.metadata: dict = dict(
            createdAt=time.time(),
            modifiedAt=time.time(),
        )

    def add(self, text: str) -> _SentenceEntry:
        idx = len(self.sentences)
        try:
            ast = parse_sentence(text)
            entry = _SentenceEntry(id=f"sent-{idx}", text=text, ast=ast)
        except Exception as e:
            entry = _SentenceEntry(id=f"sent-{idx}", text=text, parse_error=str(e))
        self.sentences.append(entry)
        self.metadata["modifiedAt"] = time.time()
        return entry

    def remove(self, index: int) -> bool:
        if 0 <= index < len(self.sentences):
            self.sentences.pop(index)
            self.metadata["modifiedAt"] = time.time()
            return True
        return False

    def update(self, index: int, text: str) -> Optional[_SentenceEntry]:
        if 0 <= index < len(self.sentences):
            try:
                ast = parse_sentence(text)
                self.sentences[index].text = text
                self.sentences[index].ast = ast
                self.sentences[index].parse_error = None
                self.sentences[index].result = None
            except Exception as e:
                self.sentences[index].text = text
                self.sentences[index].ast = None
                self.sentences[index].parse_error = str(e)
                self.sentences[index].result = None
            self.metadata["modifiedAt"] = time.time()
            return self.sentences[index]
        return None

    def evaluate_all(
        self,
        world: Any,
        options: Optional[dict] = None,
        evaluate_predicate_fn: Optional[EvalPredicateFunc] = None,
    ) -> List[Optional[SentenceEvaluationResult]]:
        results: List[Optional[SentenceEvaluationResult]] = []
        for entry in self.sentences:
            if entry.ast:
                entry.result = evaluate_sentence(
                    entry.ast, world, options, evaluate_predicate_fn=evaluate_predicate_fn
                )
            else:
                entry.result = SentenceEvaluationResult(
                    sentence=None, value=None,
                    explanation=entry.parse_error or "Parse error"
                )
            results.append(entry.result)
        return results

    def get_summary(self) -> dict:
        true_c = sum(1 for s in self.sentences if s.result and s.result.is_true)
        false_c = sum(1 for s in self.sentences if s.result and s.result.is_false)
        undef_c = len(self.sentences) - true_c - false_c
        return dict(total=len(self.sentences), trueCount=true_c, falseCount=false_c, undefinedCount=undef_c)

    def to_json(self) -> dict:
        return dict(
            format="euclid-sentences",
            version="1.0.0",
            name=self.name,
            metadata=self.metadata,
            sentences=[dict(text=s.text) for s in self.sentences],
        )

    @classmethod
    def from_json(cls, data: dict) -> SentenceList:
        if data.get("format") != "euclid-sentences":
            raise ValueError(f"Unknown sentence list format: {data.get('format')}")
        lst = cls(data.get("name", "Untitled"))
        lst.metadata = data.get("metadata", {})
        for s in data.get("sentences", []):
            lst.add(s["text"])
        return lst


# ═══════════════════════════════════════════════════════════════════════════
# CONVENIENCE FUNCTIONS
# ═══════════════════════════════════════════════════════════════════════════

def quick_evaluate(
    sentence_text: str,
    world: Any,
    options: Optional[dict] = None,
    evaluate_predicate_fn: Optional[EvalPredicateFunc] = None,
) -> SentenceEvaluationResult:
    """Quick evaluate a sentence text against a world."""
    try:
        ast = parse_sentence(sentence_text)
        return evaluate_sentence(ast, world, options, evaluate_predicate_fn=evaluate_predicate_fn)
    except Exception as e:
        return SentenceEvaluationResult(sentence=None, value=None, explanation=f"Parse error: {e}")


def create_sentence_list(name: str, texts: List[str]) -> SentenceList:
    lst = SentenceList(name)
    for text in texts:
        lst.add(text)
    return lst
