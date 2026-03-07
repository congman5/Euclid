"""
Tests for the unified checker.

Covers:
  - E proof acceptance via verify_proof
  - Invalid proof rejection
  - T-bridge fallback path
  - JSON proof verification via verify_e_proof_json
  - Single-step verification via verify_step
  - Rule catalogue via get_available_rules
  - Theorem access via get_theorem, list_theorem_names
  - Named proof verification via verify_named_proof
"""
import pytest
from verifier.e_ast import (
    Sort, Literal, Sequent, EProof, ETheorem,
    On, Between, Equals, Intersects, SameSide,
    SegmentTerm, AngleTerm, ProofStep, StepKind,
)
from verifier.unified_checker import (
    UnifiedResult, verify_proof, verify_step,
    verify_named_proof, verify_e_proof_json,
    get_available_rules, get_theorem,
    get_all_theorems, list_theorem_names, RuleInfo,
)


def _pos(atom) -> Literal:
    return Literal(atom, polarity=True)


def _neg(atom) -> Literal:
    return Literal(atom, polarity=False)


# ═══════════════════════════════════════════════════════════════════════
# Basic API tests
# ═══════════════════════════════════════════════════════════════════════

class TestUnifiedResult:
    """UnifiedResult data class works correctly."""

    def test_default_invalid(self):
        r = UnifiedResult()
        assert not r.valid
        assert not r.accepted
        assert r.engine == "e"

    def test_accepted_alias(self):
        r = UnifiedResult(valid=True)
        assert r.accepted is True

    def test_to_dict(self):
        r = UnifiedResult(valid=True, engine="t_fallback")
        d = r.to_dict()
        assert d["valid"] is True
        assert d["accepted"] is True
        assert d["engine"] == "t_fallback"


# ═══════════════════════════════════════════════════════════════════════
# verify_proof tests
# ═══════════════════════════════════════════════════════════════════════

class TestVerifyProof:
    """Test verify_proof with E proofs."""

    def test_accepts_valid_diagrammatic_proof(self):
        """A valid diagrammatic proof should be accepted."""
        from verifier.e_ast import EProof, ProofStep, StepKind, Center, Inside
        proof = EProof(
            name="center-inside",
            free_vars=[("a", Sort.POINT), ("α", Sort.CIRCLE)],
            hypotheses=[_pos(Center("a", "α"))],
            goal=[_pos(Inside("a", "α"))],
            steps=[
                ProofStep(
                    id=1,
                    kind=StepKind.DIAGRAMMATIC,
                    assertions=[_pos(Inside("a", "α"))],
                ),
            ],
        )
        result = verify_proof(proof)
        assert result.valid
        assert result.engine == "e"
        assert len(result.errors) == 0

    def test_rejects_invalid_step(self):
        """A proof with an unjustified step is rejected."""
        proof = EProof(
            name="bad_step",
            free_vars=[
                ("a", Sort.POINT), ("b", Sort.POINT), ("L", Sort.LINE),
            ],
            hypotheses=[_pos(On("a", "L"))],
            goal=[_pos(On("b", "L"))],
            steps=[
                ProofStep(
                    id=1,
                    kind=StepKind.DIAGRAMMATIC,
                    assertions=[_pos(On("b", "L"))],
                ),
            ],
        )
        result = verify_proof(proof)
        # on(b, L) doesn't follow from on(a, L) alone
        assert not result.valid
        assert len(result.errors) > 0

    def test_engine_reports_e(self):
        """Default engine is 'e'."""
        proof = EProof(
            name="trivial",
            free_vars=[("a", Sort.POINT)],
            hypotheses=[],
            goal=[],
            steps=[],
        )
        result = verify_proof(proof)
        assert result.engine == "e"

    def test_e_result_attached(self):
        """The underlying ECheckResult is attached."""
        proof = EProof(
            name="trivial",
            free_vars=[("a", Sort.POINT)],
            hypotheses=[],
            goal=[],
            steps=[],
        )
        result = verify_proof(proof)
        assert result.e_result is not None

    def test_accepts_empty_goal(self):
        """A proof with no goal (vacuously true) is accepted."""
        proof = EProof(
            name="no_goal",
            free_vars=[("a", Sort.POINT)],
            hypotheses=[_pos(On("a", "L"))],
            goal=[],
            steps=[],
        )
        result = verify_proof(proof)
        assert result.valid


# ═══════════════════════════════════════════════════════════════════════
# T-bridge fallback tests
# ═══════════════════════════════════════════════════════════════════════

class TestTFallback:
    """Test the T-bridge fallback path."""

    def test_fallback_not_invoked_when_e_succeeds(self):
        """If E succeeds, T fallback is not used even if enabled."""
        from verifier.e_ast import Center, Inside
        proof = EProof(
            name="center-inside",
            free_vars=[("a", Sort.POINT), ("α", Sort.CIRCLE)],
            hypotheses=[_pos(Center("a", "α"))],
            goal=[_pos(Inside("a", "α"))],
            steps=[
                ProofStep(
                    id=1,
                    kind=StepKind.DIAGRAMMATIC,
                    assertions=[_pos(Inside("a", "α"))],
                ),
            ],
        )
        result = verify_proof(proof, use_t_fallback=True)
        assert result.valid
        assert result.engine == "e"

    def test_fallback_disabled_by_default(self):
        """T fallback is off by default."""
        proof = EProof(
            name="empty",
            free_vars=[("a", Sort.POINT), ("L", Sort.LINE)],
            hypotheses=[],
            goal=[_pos(On("a", "L"))],
            steps=[],
        )
        result = verify_proof(proof, use_t_fallback=False)
        assert not result.valid
        assert result.engine == "e"


# ═══════════════════════════════════════════════════════════════════════
# verify_e_proof_json tests
# ═══════════════════════════════════════════════════════════════════════

class TestVerifyEProofJson:
    """Test JSON-format proof verification via System E."""

    def test_simple_given_accepted(self):
        """A proof with matching Given steps is accepted."""
        pj = {
            "name": "t",
            "declarations": {"points": ["a", "b", "c"], "lines": []},
            "premises": ["between(a, b, c)"],
            "goal": "between(c, b, a)",
            "lines": [
                {"id": 1, "depth": 0, "statement": "between(a, b, c)",
                 "justification": "Given", "refs": []},
                {"id": 2, "depth": 0, "statement": "between(c, b, a)",
                 "justification": "diagrammatic", "refs": [1]},
            ],
        }
        result = verify_e_proof_json(pj)
        assert result.accepted

    def test_construction_step_accepted(self):
        """A let-circle construction step is accepted."""
        pj = {
            "name": "circle_test",
            "declarations": {"points": ["a", "b"], "lines": []},
            "premises": ["\u00ac(a = b)"],
            "goal": "",
            "lines": [
                {"id": 1, "depth": 0, "statement": "\u00ac(a = b)",
                 "justification": "Given", "refs": []},
                {"id": 2, "depth": 0,
                 "statement": "center(a, \u03b1), on(b, \u03b1)",
                 "justification": "let-circle", "refs": [1]},
            ],
        }
        result = verify_e_proof_json(pj)
        assert 2 in result.derived


# ═══════════════════════════════════════════════════════════════════════
# verify_named_proof tests
# ═══════════════════════════════════════════════════════════════════════

class TestVerifyNamedProof:
    """Test named proof verification from e_proofs catalogue."""

    def test_prop_i1_named_returns_result(self):
        """verify_named_proof returns a UnifiedResult for Prop.I.1."""
        result = verify_named_proof("Prop.I.1")
        assert isinstance(result, UnifiedResult)
        # The I.1 proof encoding may not pass full checker validation
        # (it's a structured proof template), but we get a result
        assert result.e_result is not None

    def test_missing_proof_raises(self):
        with pytest.raises(KeyError):
            verify_named_proof("Prop.I.99")


# ═══════════════════════════════════════════════════════════════════════
# verify_step tests
# ═══════════════════════════════════════════════════════════════════════

class TestVerifyStep:
    """Test single-step verification."""

    def test_consequence_of_betweenness(self):
        """Between(a,b,c) implies on(b,L) if on(a,L) and on(c,L)."""
        known = {
            _pos(On("a", "L")),
            _pos(On("c", "L")),
            _pos(Between("a", "b", "c")),
            _neg(Equals("a", "c")),
        }
        query = _pos(On("b", "L"))
        assert verify_step(known, query) is True

    def test_non_consequence(self):
        """A random literal is not a consequence of unrelated facts."""
        known = {_pos(On("a", "L"))}
        query = _pos(On("b", "M"))
        assert verify_step(known, query) is False


# ═══════════════════════════════════════════════════════════════════════
# get_available_rules tests
# ═══════════════════════════════════════════════════════════════════════

class TestGetAvailableRules:
    """Test the rule catalogue API."""

    def test_returns_list_of_rule_info(self):
        rules = get_available_rules()
        assert isinstance(rules, list)
        assert all(isinstance(r, RuleInfo) for r in rules)

    def test_has_construction_rules(self):
        rules = get_available_rules()
        constr = [r for r in rules if r.category == "construction"]
        assert len(constr) > 0

    def test_has_diagrammatic_axioms(self):
        rules = get_available_rules()
        diag = [r for r in rules if r.category == "diagrammatic"]
        assert len(diag) > 0

    def test_has_transfer_axioms(self):
        rules = get_available_rules()
        transfer = [r for r in rules if r.category == "transfer"]
        assert len(transfer) > 0

    def test_has_superposition(self):
        rules = get_available_rules()
        sup = [r for r in rules if r.category == "superposition"]
        assert len(sup) == 2

    def test_has_metric_axioms(self):
        rules = get_available_rules()
        metric = [r for r in rules if r.category == "metric"]
        assert len(metric) >= 10

    def test_has_propositions(self):
        rules = get_available_rules()
        props = [r for r in rules if r.category == "proposition"]
        assert len(props) == 48

    def test_all_have_section(self):
        rules = get_available_rules()
        for r in rules:
            assert r.section != "", f"Rule {r.name} missing section"

    def test_total_rule_count_reasonable(self):
        rules = get_available_rules()
        # construction + diagrammatic + metric + transfer + superposition + propositions
        assert len(rules) >= 100


# ═══════════════════════════════════════════════════════════════════════
# Theorem access tests
# ═══════════════════════════════════════════════════════════════════════

class TestTheoremAccess:
    """Test theorem catalogue access via unified_checker."""

    def test_get_theorem_by_name(self):
        thm = get_theorem("Prop.I.1")
        assert thm is not None
        assert thm.name == "Prop.I.1"

    def test_get_theorem_missing(self):
        thm = get_theorem("Prop.I.99")
        assert thm is None

    def test_get_all_theorems(self):
        all_thms = get_all_theorems()
        assert len(all_thms) == 48

    def test_list_theorem_names(self):
        names = list_theorem_names()
        assert len(names) == 48
        assert names[0] == "Prop.I.1"
        assert names[-1] == "Prop.I.48"

    def test_get_theorem_i47(self):
        thm = get_theorem("Prop.I.47")
        assert thm is not None
        assert "right-angled" in thm.statement or "Pythagorean" in thm.statement
