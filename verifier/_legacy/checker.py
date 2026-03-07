"""
checker.py — Trusted proof-checking engine.
"""
from __future__ import annotations
from typing import Dict, List, Optional, Set
from itertools import permutations

from .ast import (
    Formula, Proof, ProofLine, SymbolInfo, Sort,
    Pred, Eq, Neq, Not, And, Or, Iff, Exists, ExistsUnique,
    ExactlyOne, Bottom, ForAll, Seg,
    formula_eq, free_symbols, all_symbols, substitute,
)
from verifier.diagnostics import Diagnostic, DiagCode, VerificationResult
from .scope import ScopeTracker
from .matcher import match_formula, instantiate
from .rules import RuleSchema, get_rule, ALL_RULES, RULE_ALIASES
import verifier._legacy.library  # noqa: F401 — registers derived rules


class ProofChecker:
    def __init__(self, proof: Proof):
        self.proof = proof
        self.scope = ScopeTracker()
        self.symbols: Dict[str, SymbolInfo] = {}
        self.diags: List[Diagnostic] = []
        self.derived: Dict[int, Formula] = {}
        self.goal_line: Optional[int] = None
        self._init_symbols()

    def _init_symbols(self):
        for n in self.proof.declarations.points:
            self.symbols[n] = SymbolInfo(n, Sort.POINT, "declaration")
        for n in self.proof.declarations.lines:
            self.symbols[n] = SymbolInfo(n, Sort.LINE, "declaration")

    def _diag(self, line_id: int, code: DiagCode, msg: str):
        self.diags.append(Diagnostic(line=line_id, code=code, message=msg))

    def check(self) -> VerificationResult:
        seen: Set[int] = set()
        for line in self.proof.lines:
            if line.id in seen:
                self._diag(line.id, DiagCode.DUPLICATE_LINE_ID,
                           "Duplicate line ID " + str(line.id) + ".")
            seen.add(line.id)

        prev_depth = 0
        for idx, line in enumerate(self.proof.lines):
            self.scope.add_line(line)
            if line.justification == "Assume":
                if idx > 0 and line.depth <= prev_depth:
                    self._diag(line.id, DiagCode.ASSUME_DEPTH_ERROR,
                               "Assume on line " + str(line.id) + " must increase depth.")
            elif line.depth > prev_depth + 1:
                self._diag(line.id, DiagCode.DEPTH_ERROR,
                           "Line " + str(line.id) + " jumps depth.")
            self._check_line(line)
            self._check_free_symbols(line)
            prev_depth = line.depth

        if self.proof.goal_formula is not None:
            found = False
            for line in self.proof.lines:
                if line.id in self.derived and line.depth == 0:
                    if formula_eq(self.derived[line.id], self.proof.goal_formula):
                        self.goal_line = line.id
                        found = True
                        break
            if not found:
                last = self.proof.lines[-1].id if self.proof.lines else 0
                self._diag(last, DiagCode.GOAL_NOT_DERIVED,
                           "Goal '" + self.proof.goal + "' not derived at depth 0.")

        if self.diags:
            return VerificationResult(
                accepted=False,
                first_error_line=min(d.line for d in self.diags),
                diagnostics=self.diags,
            )
        return VerificationResult(
            accepted=True,
            goal_derived_on_line=self.goal_line,
            diagnostics=[],
        )

    def _check_free_symbols(self, line: ProofLine):
        if line.statement is None:
            return
        for sym in free_symbols(line.statement):
            if sym not in self.symbols:
                self._diag(line.id, DiagCode.UNDECLARED_SYMBOL,
                           "Symbol '" + sym + "' on line " + str(line.id) +
                           " is not declared and has not been introduced by a witness rule.")

    def _check_line(self, line: ProofLine):
        if line.statement is None:
            self._diag(line.id, DiagCode.MALFORMED_FORMULA,
                       "Malformed formula on line " + str(line.id) + ": '" + line.raw + "'.")
            return
        rule = get_rule(line.justification)
        if rule is None:
            self._diag(line.id, DiagCode.UNKNOWN_JUSTIFICATION,
                       "Unknown justification '" + line.justification + "'.")
            return
        # Normalize old aliases to canonical name
        name = RULE_ALIASES.get(line.justification, line.justification)
        if name == "Given":
            self._given(line)
        elif name == "Assume":
            self._assume(line)
        elif name == "RAA":
            self._raa(line)
        elif name == "Witness":
            self._witness(line, "Exists")
        elif name == "WitnessUnique":
            self._witness(line, "ExistsUnique")
        elif name == "UniqueElim":
            self._unique_elim(line)
        elif name == "EqReflSeg":
            self._eq_refl_seg(line)
        elif name == "\u2203Intro":
            self._exists_intro(line)
        elif name == "\u2227Elim":
            self._and_elim(line)
        elif name == "\u2228Intro":
            self._or_intro(line)
        elif name == "\u2194Elim":
            self._iff_elim(line)
        else:
            self._standard(line, rule)

    def _given(self, line: ProofLine):
        for pf in self.proof.premise_formulas:
            if formula_eq(line.statement, pf):
                self.derived[line.id] = line.statement
                return
        self._diag(line.id, DiagCode.GIVEN_NOT_IN_PREMISES,
                   "'" + line.raw + "' is not among the declared premises.")

    def _assume(self, line: ProofLine):
        # Register any new symbols introduced by the assumption
        if line.statement is not None:
            for sym in free_symbols(line.statement):
                if sym not in self.symbols:
                    sort = Sort.LINE if sym[0].islower() else Sort.POINT
                    self.symbols[sym] = SymbolInfo(sym, sort, "assume", line.id)
        self.derived[line.id] = line.statement

    def _raa(self, line: ProofLine):
        if len(line.refs) != 2:
            self._diag(line.id, DiagCode.WRONG_REFERENCE_COUNT,
                       "RAA requires exactly 2 references.")
            return
        assume_ref, bottom_ref = line.refs
        al = self.scope.get_line(assume_ref)
        bl = self.scope.get_line(bottom_ref)
        if al is None:
            self._diag(line.id, DiagCode.UNKNOWN_REFERENCE,
                       "RAA: line " + str(assume_ref) + " does not exist.")
            return
        if bl is None:
            self._diag(line.id, DiagCode.UNKNOWN_REFERENCE,
                       "RAA: line " + str(bottom_ref) + " does not exist.")
            return
        if al.justification != "Assume":
            self._diag(line.id, DiagCode.RAA_ERROR,
                       "RAA: line " + str(assume_ref) + " must be an Assume.")
            return
        if bottom_ref not in self.derived:
            self._diag(line.id, DiagCode.RAA_ERROR,
                       "RAA: line " + str(bottom_ref) + " not derived.")
            return
        if not isinstance(self.derived[bottom_ref], Bottom):
            self._diag(line.id, DiagCode.RAA_ERROR,
                       "RAA: line " + str(bottom_ref) + " must derive \u22a5.")
            return
        if not self.scope.is_in_subproof(bottom_ref, assume_ref):
            self._diag(line.id, DiagCode.RAA_ERROR,
                       "RAA: line " + str(bottom_ref) + " not in subproof of " + str(assume_ref) + ".")
            return
        if line.depth != al.depth - 1:
            self._diag(line.id, DiagCode.RAA_ERROR,
                       "RAA: must be at depth " + str(al.depth - 1) + ".")
            return
        expected = Not(al.statement)
        if not formula_eq(line.statement, expected):
            self._diag(line.id, DiagCode.CONCLUSION_MISMATCH,
                       "RAA: expected \u00ac(" + al.raw + ").")
            return
        self.derived[line.id] = line.statement

    def _witness(self, line: ProofLine, existential_type: str):
        if len(line.refs) != 1:
            self._diag(line.id, DiagCode.WRONG_REFERENCE_COUNT,
                       line.justification + " requires exactly 1 reference.")
            return
        ref_id = line.refs[0]
        rl = self.scope.get_line(ref_id)
        if rl is None:
            self._diag(line.id, DiagCode.UNKNOWN_REFERENCE,
                       "Line " + str(ref_id) + " does not exist.")
            return
        if not self.scope.is_visible(line.id, ref_id):
            self._diag(line.id, DiagCode.OUT_OF_SCOPE_REFERENCE,
                       "Line " + str(ref_id) + " not visible.")
            return
        if ref_id not in self.derived:
            self._diag(line.id, DiagCode.PREMISE_PATTERN_MISMATCH,
                       "Line " + str(ref_id) + " not derived.")
            return
        ref_f = self.derived[ref_id]
        if existential_type == "Exists" and not isinstance(ref_f, Exists):
            self._diag(line.id, DiagCode.PREMISE_PATTERN_MISMATCH,
                       "Witness requires Exists premise.")
            return
        if existential_type == "ExistsUnique" and not isinstance(ref_f, ExistsUnique):
            self._diag(line.id, DiagCode.PREMISE_PATTERN_MISMATCH,
                       "WitnessUnique requires ExistsUnique premise.")
            return
        fresh = line.meta.get("fresh_symbol")
        if not fresh:
            self._diag(line.id, DiagCode.NON_FRESH_WITNESS,
                       line.justification + ": meta.fresh_symbol is required.")
            return
        if fresh in self.symbols:
            self._diag(line.id, DiagCode.NON_FRESH_WITNESS,
                       "Symbol '" + fresh + "' is not fresh.")
            return
        expected = substitute(ref_f.body, ref_f.var, fresh)
        if not formula_eq(line.statement, expected):
            self._diag(line.id, DiagCode.CONCLUSION_MISMATCH,
                       line.justification + ": conclusion mismatch after substitution.")
            return
        sort = Sort.LINE if fresh[0].islower() else Sort.POINT
        self.symbols[fresh] = SymbolInfo(fresh, sort, "witness", line.id)
        self.derived[line.id] = line.statement

    def _eq_refl_seg(self, line: ProofLine):
        """EqReflSeg: Equal(AB, BA) or Equal(AB, AB) — segment reflexivity."""
        stmt = line.statement
        if not isinstance(stmt, Pred) or stmt.name != "Equal" or len(stmt.args) != 2:
            self._diag(line.id, DiagCode.CONCLUSION_MISMATCH,
                       "EqReflSeg: expected Equal(XY, ...) form.")
            return
        a1, a2 = stmt.args
        if not isinstance(a1, Seg) or not isinstance(a2, Seg):
            self._diag(line.id, DiagCode.CONCLUSION_MISMATCH,
                       "EqReflSeg: expected segment arguments.")
            return
        if {a1.p1, a1.p2} == {a2.p1, a2.p2}:
            self.derived[line.id] = line.statement
        else:
            self._diag(line.id, DiagCode.CONCLUSION_MISMATCH,
                       "EqReflSeg: segments must have the same endpoints.")

    def _exists_intro(self, line: ProofLine):
        """ExistsIntro: from φ(t), derive ∃X φ(X).

        The statement must be Exists(X, body). We check that substituting
        some term t for X in body yields the referenced formula.
        """
        if len(line.refs) != 1:
            self._diag(line.id, DiagCode.WRONG_REFERENCE_COUNT,
                       "ExistsIntro requires exactly 1 reference.")
            return
        ref_id = line.refs[0]
        rl = self.scope.get_line(ref_id)
        if rl is None:
            self._diag(line.id, DiagCode.UNKNOWN_REFERENCE,
                       "Line " + str(ref_id) + " does not exist.")
            return
        if not self.scope.is_visible(line.id, ref_id):
            self._diag(line.id, DiagCode.OUT_OF_SCOPE_REFERENCE,
                       "Line " + str(ref_id) + " not visible.")
            return
        if ref_id not in self.derived:
            self._diag(line.id, DiagCode.PREMISE_PATTERN_MISMATCH,
                       "Line " + str(ref_id) + " not derived.")
            return
        ref_f = self.derived[ref_id]
        stmt = line.statement
        if not isinstance(stmt, Exists):
            self._diag(line.id, DiagCode.CONCLUSION_MISMATCH,
                       "ExistsIntro: conclusion must be \u2203X(...).")
            return
        # Try every symbol that appears in the referenced formula as the witness term
        for candidate in all_symbols(ref_f):
            instantiated = substitute(stmt.body, stmt.var, candidate)
            if formula_eq(instantiated, ref_f):
                self.derived[line.id] = line.statement
                return
        self._diag(line.id, DiagCode.CONCLUSION_MISMATCH,
                   "ExistsIntro: no term t found such that φ(t) matches line "
                   + str(ref_id) + ".")

    def _and_elim(self, line: ProofLine):
        """∧Elim: from φ ∧ ψ, derive φ or ψ."""
        if len(line.refs) != 1:
            self._diag(line.id, DiagCode.WRONG_REFERENCE_COUNT,
                       "\u2227Elim requires exactly 1 reference.")
            return
        ref_id = line.refs[0]
        rl = self.scope.get_line(ref_id)
        if rl is None:
            self._diag(line.id, DiagCode.UNKNOWN_REFERENCE,
                       "Line " + str(ref_id) + " does not exist.")
            return
        if not self.scope.is_visible(line.id, ref_id):
            self._diag(line.id, DiagCode.OUT_OF_SCOPE_REFERENCE,
                       "Line " + str(ref_id) + " not visible.")
            return
        if ref_id not in self.derived:
            self._diag(line.id, DiagCode.PREMISE_PATTERN_MISMATCH,
                       "Line " + str(ref_id) + " not derived.")
            return
        ref_f = self.derived[ref_id]
        if not isinstance(ref_f, And):
            self._diag(line.id, DiagCode.PREMISE_PATTERN_MISMATCH,
                       "\u2227Elim: reference must be a conjunction.")
            return
        if formula_eq(line.statement, ref_f.left) or formula_eq(line.statement, ref_f.right):
            self.derived[line.id] = line.statement
            return
        self._diag(line.id, DiagCode.CONCLUSION_MISMATCH,
                   "\u2227Elim: conclusion must be either side of the conjunction.")

    def _or_intro(self, line: ProofLine):
        """∨Intro: from φ, derive φ ∨ ψ or ψ ∨ φ."""
        if len(line.refs) != 1:
            self._diag(line.id, DiagCode.WRONG_REFERENCE_COUNT,
                       "\u2228Intro requires exactly 1 reference.")
            return
        ref_id = line.refs[0]
        rl = self.scope.get_line(ref_id)
        if rl is None:
            self._diag(line.id, DiagCode.UNKNOWN_REFERENCE,
                       "Line " + str(ref_id) + " does not exist.")
            return
        if not self.scope.is_visible(line.id, ref_id):
            self._diag(line.id, DiagCode.OUT_OF_SCOPE_REFERENCE,
                       "Line " + str(ref_id) + " not visible.")
            return
        if ref_id not in self.derived:
            self._diag(line.id, DiagCode.PREMISE_PATTERN_MISMATCH,
                       "Line " + str(ref_id) + " not derived.")
            return
        ref_f = self.derived[ref_id]
        if not isinstance(line.statement, Or):
            self._diag(line.id, DiagCode.CONCLUSION_MISMATCH,
                       "\u2228Intro: conclusion must be a disjunction.")
            return
        if formula_eq(ref_f, line.statement.left) or formula_eq(ref_f, line.statement.right):
            self.derived[line.id] = line.statement
            return
        self._diag(line.id, DiagCode.CONCLUSION_MISMATCH,
                   "\u2228Intro: the referenced formula must appear on one side of the disjunction.")

    def _iff_elim(self, line: ProofLine):
        """↔Elim: from φ ↔ ψ and φ, derive ψ (or from φ ↔ ψ and ψ, derive φ)."""
        if len(line.refs) != 2:
            self._diag(line.id, DiagCode.WRONG_REFERENCE_COUNT,
                       "\u2194Elim requires exactly 2 references.")
            return
        for rid in line.refs:
            rl = self.scope.get_line(rid)
            if rl is None:
                self._diag(line.id, DiagCode.UNKNOWN_REFERENCE,
                           "Line " + str(rid) + " does not exist.")
                return
            if not self.scope.is_visible(line.id, rid):
                self._diag(line.id, DiagCode.OUT_OF_SCOPE_REFERENCE,
                           "Line " + str(rid) + " not visible.")
                return
            if rid not in self.derived:
                self._diag(line.id, DiagCode.PREMISE_PATTERN_MISMATCH,
                           "Line " + str(rid) + " not derived.")
                return
        # Try both orderings of references
        for i, j in [(0, 1), (1, 0)]:
            iff_f = self.derived[line.refs[i]]
            other_f = self.derived[line.refs[j]]
            if isinstance(iff_f, Iff):
                if formula_eq(other_f, iff_f.left) and formula_eq(line.statement, iff_f.right):
                    self.derived[line.id] = line.statement
                    return
                if formula_eq(other_f, iff_f.right) and formula_eq(line.statement, iff_f.left):
                    self.derived[line.id] = line.statement
                    return
        self._diag(line.id, DiagCode.CONCLUSION_MISMATCH,
                   "\u2194Elim: conclusion mismatch.")

    def _unique_elim(self, line: ProofLine):
        if len(line.refs) != 3:
            self._diag(line.id, DiagCode.WRONG_REFERENCE_COUNT,
                       "UniqueElim requires exactly 3 references.")
            return
        eu_ref, c_ref, d_ref = line.refs
        for rid in line.refs:
            rl = self.scope.get_line(rid)
            if rl is None:
                self._diag(line.id, DiagCode.UNKNOWN_REFERENCE,
                           "Line " + str(rid) + " does not exist.")
                return
            if not self.scope.is_visible(line.id, rid):
                self._diag(line.id, DiagCode.OUT_OF_SCOPE_REFERENCE,
                           "Line " + str(rid) + " not visible.")
                return
            if rid not in self.derived:
                self._diag(line.id, DiagCode.PREMISE_PATTERN_MISMATCH,
                           "Line " + str(rid) + " not derived.")
                return
        eu_f = self.derived[eu_ref]
        if not isinstance(eu_f, ExistsUnique):
            self._diag(line.id, DiagCode.PREMISE_PATTERN_MISMATCH,
                       "UniqueElim: first ref must be ExistsUnique.")
            return
        c_f = self.derived[c_ref]
        d_f = self.derived[d_ref]
        c_sym = self._find_witness(eu_f.body, eu_f.var, c_f)
        d_sym = self._find_witness(eu_f.body, eu_f.var, d_f)
        if c_sym is None:
            self._diag(line.id, DiagCode.UNIQUENESS_MISMATCH,
                       "UniqueElim: line " + str(c_ref) + " doesn't match body.")
            return
        if d_sym is None:
            self._diag(line.id, DiagCode.UNIQUENESS_MISMATCH,
                       "UniqueElim: line " + str(d_ref) + " doesn't match body.")
            return
        expected = Eq(c_sym, d_sym)
        if not formula_eq(line.statement, expected):
            self._diag(line.id, DiagCode.CONCLUSION_MISMATCH,
                       "UniqueElim: expected " + c_sym + " = " + d_sym + ".")
            return
        self.derived[line.id] = line.statement

    def _find_witness(self, body, var, concrete):
        for candidate in all_symbols(concrete):
            if formula_eq(substitute(body, var, candidate), concrete):
                return candidate
        return None

    @staticmethod
    def _metavar_expected_sort(name: str) -> Optional[Sort]:
        if isinstance(name, str) and len(name) == 1:
            if name.isupper():
                return Sort.POINT
            if name.islower():
                return Sort.LINE
        return None

    def _bindings_sorts_ok(self, bindings, line_id: int) -> bool:
        for meta, val in bindings.items():
            if not isinstance(val, str):
                continue
            expected = self._metavar_expected_sort(meta)
            if expected is None:
                continue
            info = self.symbols.get(val)
            if info is None:
                continue
            if info.sort != expected:
                self._diag(line_id, DiagCode.SORT_MISMATCH,
                           "Symbol '" + val + "' has sort " + info.sort.name +
                           " but is used where " + expected.name + " is expected.")
                return False
        return True

    def _standard(self, line: ProofLine, rule: RuleSchema):
        if rule.min_refs is not None and len(line.refs) < rule.min_refs:
            self._diag(line.id, DiagCode.WRONG_REFERENCE_COUNT,
                       rule.name + " requires at least " + str(rule.min_refs) + " ref(s).")
            return
        if rule.max_refs is not None and len(line.refs) > rule.max_refs:
            self._diag(line.id, DiagCode.WRONG_REFERENCE_COUNT,
                       rule.name + " requires at most " + str(rule.max_refs) + " ref(s).")
            return
        ref_formulas = []
        for rid in line.refs:
            rl = self.scope.get_line(rid)
            if rl is None:
                self._diag(line.id, DiagCode.UNKNOWN_REFERENCE,
                           "Line " + str(rid) + " does not exist.")
                return
            if not self.scope.is_visible(line.id, rid):
                self._diag(line.id, DiagCode.OUT_OF_SCOPE_REFERENCE,
                           "Line " + str(rid) + " not visible at depth " + str(line.depth) + ".")
                return
            if rid not in self.derived:
                self._diag(line.id, DiagCode.PREMISE_PATTERN_MISMATCH,
                           "Line " + str(rid) + " not derived.")
                return
            ref_formulas.append(self.derived[rid])

        patterns = rule.premise_patterns
        if not patterns:
            ec = instantiate(rule.conclusion_pattern, {})
            if formula_eq(line.statement, ec):
                self.derived[line.id] = line.statement
                return
            # Try matching conclusion pattern against statement to derive bindings
            from .matcher import match_formula as mf
            cb = mf(rule.conclusion_pattern, line.statement, {})
            if cb is not None:
                ec2 = instantiate(rule.conclusion_pattern, cb)
                if formula_eq(line.statement, ec2):
                    self.derived[line.id] = line.statement
                    return
            self._diag(line.id, DiagCode.CONCLUSION_MISMATCH,
                       rule.name + ": conclusion mismatch.")
            return

        if self._try_match(rule, ref_formulas, line):
            self.derived[line.id] = line.statement
            return

    def _try_match(self, rule, refs, line) -> bool:
        pats = rule.premise_patterns
        if len(refs) != len(pats):
            self._diag(line.id, DiagCode.WRONG_REFERENCE_COUNT,
                       rule.name + " requires " + str(len(pats)) + " premise(s).")
            return False

        for perm in permutations(range(len(refs))):
            bindings = {}
            ok = True
            for pi, ri in enumerate(perm):
                result = match_formula(pats[pi], refs[ri], bindings)
                if result is None:
                    ok = False
                    break
                bindings = result
            if not ok:
                continue
            ec = instantiate(rule.conclusion_pattern, bindings)
            if formula_eq(line.statement, ec):
                if self._bindings_sorts_ok(bindings, line.id):
                    return True
                return False
            cb = match_formula(rule.conclusion_pattern, line.statement, bindings)
            if cb is not None:
                recheck = True
                for pi, ri in enumerate(perm):
                    r2 = match_formula(pats[pi], refs[ri], cb)
                    if r2 is None:
                        recheck = False
                        break
                    cb = r2
                if recheck:
                    fc = instantiate(rule.conclusion_pattern, cb)
                    if formula_eq(line.statement, fc):
                        if self._bindings_sorts_ok(cb, line.id):
                            return True
                        return False

        bindings = {}
        for i, (pat, ref) in enumerate(zip(pats, refs)):
            result = match_formula(pat, ref, bindings)
            if result is None:
                rl = self.scope.get_line(line.refs[i])
                self._diag(line.id, DiagCode.PREMISE_PATTERN_MISMATCH,
                           rule.name + ": premise mismatch at line " + str(line.refs[i]) + ".")
                return False
            bindings = result
        self._diag(line.id, DiagCode.CONCLUSION_MISMATCH,
                   rule.name + ": conclusion mismatch.")
        return False


def check_proof(proof: Proof) -> VerificationResult:
    return ProofChecker(proof).check()
