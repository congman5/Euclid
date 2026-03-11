"""
Tests for the System E AST and parser.
"""
import pytest
from verifier.e_ast import (
    Sort, Var, SegmentTerm, AngleTerm, AreaTerm, MagAdd, RightAngle, ZeroMag,
    On, SameSide, Between, Center, Inside, Intersects, Equals, LessThan,
    Literal, Clause, Sequent, StepKind,
    atom_vars, literal_vars, substitute_literal, substitute_atom, mag_sort,
)
from verifier.e_parser import (
    EParseError, parse_literal, parse_literal_list, parse_conjunction,
    parse_magnitude_eq, parse_sequent,
)


# ═══════════════════════════════════════════════════════════════════════
# AST unit tests
# ═══════════════════════════════════════════════════════════════════════

class TestSorts:
    def test_diagram_sorts(self):
        from verifier.e_ast import DIAGRAM_SORTS, MAGNITUDE_SORTS
        assert Sort.POINT in DIAGRAM_SORTS
        assert Sort.LINE in DIAGRAM_SORTS
        assert Sort.CIRCLE in DIAGRAM_SORTS
        assert Sort.SEGMENT in MAGNITUDE_SORTS
        assert Sort.ANGLE in MAGNITUDE_SORTS
        assert Sort.AREA in MAGNITUDE_SORTS


class TestTerms:
    def test_segment_term(self):
        s = SegmentTerm("a", "b")
        assert s.p1 == "a" and s.p2 == "b"
        assert repr(s) == "ab"

    def test_angle_term(self):
        a = AngleTerm("a", "b", "c")
        assert repr(a) == "\u2220abc"

    def test_area_term(self):
        t = AreaTerm("a", "b", "c")
        assert repr(t) == "\u25b3abc"

    def test_mag_add(self):
        s1 = SegmentTerm("a", "b")
        s2 = SegmentTerm("b", "c")
        add = MagAdd(s1, s2)
        assert repr(add) == "(ab + bc)"

    def test_right_angle(self):
        r = RightAngle()
        assert repr(r) == "right-angle"

    def test_zero_mag(self):
        z = ZeroMag(Sort.SEGMENT)
        assert repr(z) == "0"
        assert z.sort == Sort.SEGMENT


class TestAtoms:
    def test_on_repr(self):
        assert repr(On("a", "L")) == "on(a, L)"

    def test_same_side_repr(self):
        assert repr(SameSide("a", "b", "L")) == "same-side(a, b, L)"

    def test_between_repr(self):
        assert repr(Between("a", "b", "c")) == "between(a, b, c)"

    def test_center_repr(self):
        assert repr(Center("a", "\u03b1")) == "center(a, \u03b1)"

    def test_inside_repr(self):
        assert repr(Inside("a", "\u03b1")) == "inside(a, \u03b1)"

    def test_intersects_repr(self):
        assert repr(Intersects("L", "M")) == "intersects(L, M)"

    def test_equals_diagram(self):
        e = Equals("a", "b")
        assert repr(e) == "a = b"

    def test_equals_magnitude(self):
        e = Equals(SegmentTerm("a", "b"), SegmentTerm("c", "d"))
        assert repr(e) == "ab = cd"

    def test_less_than(self):
        lt = LessThan(SegmentTerm("a", "b"), SegmentTerm("c", "d"))
        assert repr(lt) == "ab < cd"


class TestLiterals:
    def test_positive(self):
        lit = Literal(On("a", "L"))
        assert lit.is_positive
        assert not lit.is_negative
        assert lit.is_diagrammatic
        assert not lit.is_metric

    def test_negative(self):
        lit = Literal(On("a", "L"), polarity=False)
        assert lit.is_negative
        assert repr(lit) == "\u00ac(on(a, L))"

    def test_negated(self):
        lit = Literal(On("a", "L"))
        neg = lit.negated()
        assert neg.is_negative
        assert neg.negated() == lit

    def test_metric_literal(self):
        lit = Literal(Equals(SegmentTerm("a", "b"), SegmentTerm("c", "d")))
        assert lit.is_metric
        assert not lit.is_diagrammatic

    def test_diagram_equality(self):
        lit = Literal(Equals("L", "M"))
        assert lit.is_diagrammatic


class TestAtomVars:
    def test_on_vars(self):
        assert atom_vars(On("a", "L")) == {"a", "L"}

    def test_same_side_vars(self):
        assert atom_vars(SameSide("a", "b", "L")) == {"a", "b", "L"}

    def test_between_vars(self):
        assert atom_vars(Between("a", "b", "c")) == {"a", "b", "c"}

    def test_equals_segment_vars(self):
        e = Equals(SegmentTerm("a", "b"), SegmentTerm("c", "d"))
        assert atom_vars(e) == {"a", "b", "c", "d"}

    def test_less_than_vars(self):
        lt = LessThan(SegmentTerm("a", "b"), MagAdd(
            SegmentTerm("c", "d"), SegmentTerm("e", "f")))
        assert atom_vars(lt) == {"a", "b", "c", "d", "e", "f"}


class TestSubstitution:
    def test_substitute_on(self):
        atom = On("a", "L")
        result = substitute_atom(atom, {"a": "b", "L": "M"})
        assert result == On("b", "M")

    def test_substitute_between(self):
        atom = Between("a", "b", "c")
        result = substitute_atom(atom, {"b": "d"})
        assert result == Between("a", "d", "c")

    def test_substitute_segment_eq(self):
        atom = Equals(SegmentTerm("a", "b"), SegmentTerm("c", "d"))
        result = substitute_atom(atom, {"a": "x", "d": "y"})
        assert result == Equals(SegmentTerm("x", "b"), SegmentTerm("c", "y"))

    def test_substitute_literal(self):
        lit = Literal(On("a", "L"), polarity=False)
        result = substitute_literal(lit, {"a": "b"})
        assert result == Literal(On("b", "L"), polarity=False)


class TestMagSort:
    def test_segment(self):
        assert mag_sort(SegmentTerm("a", "b")) == Sort.SEGMENT

    def test_angle(self):
        assert mag_sort(AngleTerm("a", "b", "c")) == Sort.ANGLE

    def test_area(self):
        assert mag_sort(AreaTerm("a", "b", "c")) == Sort.AREA

    def test_right_angle(self):
        assert mag_sort(RightAngle()) == Sort.ANGLE

    def test_add(self):
        assert mag_sort(MagAdd(
            SegmentTerm("a", "b"), SegmentTerm("c", "d"))) == Sort.SEGMENT


# ═══════════════════════════════════════════════════════════════════════
# Parser tests
# ═══════════════════════════════════════════════════════════════════════

class TestParseLiteral:
    def test_on(self):
        lit = parse_literal("on(a, L)")
        assert lit == Literal(On("a", "L"))

    def test_on_uppercase(self):
        lit = parse_literal("On(a, L)")
        assert lit == Literal(On("a", "L"))

    def test_between(self):
        lit = parse_literal("between(a, b, c)")
        assert lit == Literal(Between("a", "b", "c"))

    def test_same_side(self):
        lit = parse_literal("same-side(a, b, L)")
        assert lit == Literal(SameSide("a", "b", "L"))

    def test_center(self):
        lit = parse_literal("center(a, \u03b1)")
        assert lit == Literal(Center("a", "\u03b1"))

    def test_inside(self):
        lit = parse_literal("inside(a, \u03b1)")
        assert lit == Literal(Inside("a", "\u03b1"))

    def test_intersects(self):
        lit = parse_literal("intersects(L, M)")
        assert lit == Literal(Intersects("L", "M"))

    def test_negation(self):
        lit = parse_literal("\u00acon(a, L)")
        assert lit == Literal(On("a", "L"), polarity=False)

    def test_negation_parens(self):
        lit = parse_literal("\u00ac(on(a, L))")
        assert lit == Literal(On("a", "L"), polarity=False)

    def test_neq(self):
        lit = parse_literal("a \u2260 b")
        assert lit == Literal(Equals("a", "b"), polarity=False)

    def test_eq_variables(self):
        lit = parse_literal("a = b")
        assert lit == Literal(Equals("a", "b"))

    def test_segment_eq(self):
        lit = parse_literal("ab = cd")
        assert lit == Literal(Equals(SegmentTerm("a", "b"),
                                     SegmentTerm("c", "d")))

    def test_segment_lt(self):
        lit = parse_literal("ab < cd")
        assert lit == Literal(LessThan(SegmentTerm("a", "b"),
                                       SegmentTerm("c", "d")))


class TestParseMagnitude:
    def test_segment_addition(self):
        atom = parse_magnitude_eq("ab + bc = ac")
        assert atom == Equals(
            MagAdd(SegmentTerm("a", "b"), SegmentTerm("b", "c")),
            SegmentTerm("a", "c"))

    def test_right_angle(self):
        atom = parse_magnitude_eq("ab = right-angle")
        # This is a type mismatch (segment vs angle) but the parser allows it;
        # type checking is separate.
        assert isinstance(atom, Equals)
        assert isinstance(atom.right, RightAngle)


class TestParseLiteralList:
    def test_comma_separated(self):
        lits = parse_literal_list("on(a, L), on(b, L), a \u2260 b")
        assert len(lits) == 3
        assert lits[0] == Literal(On("a", "L"))
        assert lits[1] == Literal(On("b", "L"))
        assert lits[2] == Literal(Equals("a", "b"), polarity=False)

    def test_empty(self):
        assert parse_literal_list("") == []


class TestParseConjunction:
    def test_and_separated(self):
        lits = parse_conjunction(
            "on(a, L) \u2227 between(a, b, c) \u2227 ab = cd")
        assert len(lits) == 3
        assert lits[0] == Literal(On("a", "L"))
        assert lits[1] == Literal(Between("a", "b", "c"))
        assert lits[2] == Literal(
            Equals(SegmentTerm("a", "b"), SegmentTerm("c", "d")))


class TestSequent:
    def test_repr(self):
        s = Sequent(
            hypotheses=[Literal(On("a", "L")), Literal(On("b", "L"))],
            exists_vars=[("c", Sort.POINT)],
            conclusions=[Literal(Between("a", "c", "b"))],
        )
        r = repr(s)
        assert "\u21d2" in r
        assert "\u2203" in r


# ═══════════════════════════════════════════════════════════════════════
# Construction rule tests
# ═══════════════════════════════════════════════════════════════════════

class TestConstructionRules:
    def test_all_rules_load(self):
        from verifier.e_construction import ALL_CONSTRUCTION_RULES
        # 9 point + 2 line/circle + 9 intersection = 20
        assert len(ALL_CONSTRUCTION_RULES) == 20

    def test_rule_by_name(self):
        from verifier.e_construction import CONSTRUCTION_RULE_BY_NAME
        assert "let-line" in CONSTRUCTION_RULE_BY_NAME
        assert "let-circle" in CONSTRUCTION_RULE_BY_NAME
        assert "let-intersection-line-line" in CONSTRUCTION_RULE_BY_NAME
        assert "let-intersection-circle-circle-same-side" in CONSTRUCTION_RULE_BY_NAME

    def test_let_line_structure(self):
        from verifier.e_construction import CONSTRUCTION_RULE_BY_NAME
        rule = CONSTRUCTION_RULE_BY_NAME["let-line"]
        assert rule.category == "line_circle"
        assert len(rule.new_vars) == 1
        assert rule.new_vars[0][1] == Sort.LINE
        # Prerequisite: a ≠ b
        assert len(rule.prereq_pattern) == 1
        assert rule.prereq_pattern[0].is_negative  # ¬(a = b)
        # Conclusion: on(a, L), on(b, L)
        assert len(rule.conclusion_pattern) == 2

    def test_let_circle_structure(self):
        from verifier.e_construction import CONSTRUCTION_RULE_BY_NAME
        rule = CONSTRUCTION_RULE_BY_NAME["let-circle"]
        assert len(rule.new_vars) == 1
        assert rule.new_vars[0][1] == Sort.CIRCLE
        # Conclusion: center(a, α), on(b, α)
        assert len(rule.conclusion_pattern) == 2
        assert isinstance(rule.conclusion_pattern[0].atom, Center)
        assert isinstance(rule.conclusion_pattern[1].atom, On)

    def test_circle_circle_intersection_same_side(self):
        from verifier.e_construction import CONSTRUCTION_RULE_BY_NAME
        rule = CONSTRUCTION_RULE_BY_NAME[
            "let-intersection-circle-circle-same-side"]
        # 6 prerequisites
        assert len(rule.prereq_pattern) == 6
        # Conclusion includes same-side
        has_same_side = any(
            isinstance(lit.atom, SameSide)
            for lit in rule.conclusion_pattern)
        assert has_same_side


# ═══════════════════════════════════════════════════════════════════════
# Diagrammatic axiom tests
# ═══════════════════════════════════════════════════════════════════════

class TestDiagrammaticAxioms:
    def test_all_axiom_sets_load(self):
        from verifier.e_axioms import (
            ALL_DIAGRAMMATIC_AXIOMS, ALL_TRANSFER_AXIOMS, ALL_AXIOMS,
        )
        assert len(ALL_DIAGRAMMATIC_AXIOMS) > 0
        assert len(ALL_TRANSFER_AXIOMS) > 0
        assert len(ALL_AXIOMS) == (
            len(ALL_DIAGRAMMATIC_AXIOMS) + len(ALL_TRANSFER_AXIOMS))

    def test_generality_axiom_count(self):
        from verifier.e_axioms import GENERALITY_AXIOMS
        assert len(GENERALITY_AXIOMS) == 7

    def test_between_axiom_count(self):
        from verifier.e_axioms import BETWEEN_AXIOMS
        # B1 splits into 4 sub-clauses, B2-B7 are 1 each = 4 + 6 = 10
        assert len(BETWEEN_AXIOMS) == 10

    def test_same_side_axiom_count(self):
        from verifier.e_axioms import SAME_SIDE_AXIOMS
        assert len(SAME_SIDE_AXIOMS) == 5

    def test_pasch_axiom_count(self):
        from verifier.e_axioms import PASCH_AXIOMS
        assert len(PASCH_AXIOMS) == 4

    def test_triple_incidence_axiom_count(self):
        from verifier.e_axioms import TRIPLE_INCIDENCE_AXIOMS
        assert len(TRIPLE_INCIDENCE_AXIOMS) == 3

    def test_circle_axiom_count(self):
        from verifier.e_axioms import CIRCLE_AXIOMS
        # C1: 1, C2: 4 variants, C3: 4 variants, C4: 1 = 10
        assert len(CIRCLE_AXIOMS) == 10

    def test_intersection_axiom_count(self):
        from verifier.e_axioms import INTERSECTION_AXIOMS
        # I1: 1, I2: 4 variants, I3: 1, I4: 2 variants, I5: 1 = 9
        assert len(INTERSECTION_AXIOMS) == 9

    def test_clause_structure(self):
        from verifier.e_axioms import BETWEEN_AXIOMS
        # B1a: between(a,b,c) → between(c,b,a)
        # Clause: {¬between(a,b,c), between(c,b,a)}
        b1a = BETWEEN_AXIOMS[0]
        assert len(b1a.literals) == 2
        # One positive, one negative
        polarities = {lit.polarity for lit in b1a.literals}
        assert polarities == {True, False}

    def test_transfer_axioms_contain_magnitudes(self):
        from verifier.e_axioms import DIAGRAM_SEGMENT_TRANSFER
        # DS1 should contain a segment term
        ds1 = DIAGRAM_SEGMENT_TRANSFER[0]
        has_segment = any(
            lit.is_metric for lit in ds1.literals)
        assert has_segment


# ═══════════════════════════════════════════════════════════════════════
# Direct consequence engine tests
# ═══════════════════════════════════════════════════════════════════════

class TestConsequenceEngine:
    def test_between_symmetry(self):
        """B1a: between(a,b,c) → between(c,b,a)"""
        from verifier.e_consequence import ConsequenceEngine
        from verifier.e_axioms import BETWEEN_AXIOMS
        engine = ConsequenceEngine(axioms=BETWEEN_AXIOMS)
        known = {Literal(Between("a", "b", "c"))}
        closure = engine.direct_consequences(known)
        # Should derive between(c,b,a)
        assert Literal(Between("c", "b", "a")) in closure

    def test_between_implies_neq(self):
        """B1b,c: between(a,b,c) → a≠b, a≠c"""
        from verifier.e_consequence import ConsequenceEngine
        from verifier.e_axioms import BETWEEN_AXIOMS
        engine = ConsequenceEngine(axioms=BETWEEN_AXIOMS)
        known = {Literal(Between("a", "b", "c"))}
        closure = engine.direct_consequences(known)
        # a≠b means ¬(a=b) — a negative literal
        assert Literal(Equals("a", "b"), polarity=False) in closure
        assert Literal(Equals("a", "c"), polarity=False) in closure

    def test_between_not_reverse(self):
        """B1d: between(a,b,c) → ¬between(b,a,c)"""
        from verifier.e_consequence import ConsequenceEngine
        from verifier.e_axioms import BETWEEN_AXIOMS
        engine = ConsequenceEngine(axioms=BETWEEN_AXIOMS)
        known = {Literal(Between("a", "b", "c"))}
        closure = engine.direct_consequences(known)
        assert Literal(Between("b", "a", "c"), polarity=False) in closure

    def test_between_collinearity(self):
        """B2: between(a,b,c) ∧ on(a,L) ∧ on(b,L) → on(c,L)"""
        from verifier.e_consequence import ConsequenceEngine
        from verifier.e_axioms import BETWEEN_AXIOMS
        engine = ConsequenceEngine(axioms=BETWEEN_AXIOMS)
        known = {
            Literal(Between("a", "b", "c")),
            Literal(On("a", "L")),
            Literal(On("b", "L")),
        }
        closure = engine.direct_consequences(known)
        assert Literal(On("c", "L")) in closure

    def test_center_implies_inside(self):
        """G3: center(a,α) → inside(a,α)"""
        from verifier.e_consequence import ConsequenceEngine
        from verifier.e_axioms import GENERALITY_AXIOMS
        engine = ConsequenceEngine(axioms=GENERALITY_AXIOMS)
        known = {Literal(Center("a", "\u03b1"))}
        closure = engine.direct_consequences(known)
        assert Literal(Inside("a", "\u03b1")) in closure

    def test_inside_not_on(self):
        """G4: inside(a,α) → ¬on(a,α)"""
        from verifier.e_consequence import ConsequenceEngine
        from verifier.e_axioms import GENERALITY_AXIOMS
        engine = ConsequenceEngine(axioms=GENERALITY_AXIOMS)
        known = {Literal(Inside("a", "\u03b1"))}
        closure = engine.direct_consequences(known)
        assert Literal(On("a", "\u03b1"), polarity=False) in closure

    def test_center_chain(self):
        """G3 + G4: center(a,α) → inside(a,α) → ¬on(a,α)"""
        from verifier.e_consequence import ConsequenceEngine
        from verifier.e_axioms import GENERALITY_AXIOMS
        engine = ConsequenceEngine(axioms=GENERALITY_AXIOMS)
        known = {Literal(Center("a", "\u03b1"))}
        closure = engine.direct_consequences(known)
        # Should chain: center → inside → ¬on
        assert Literal(Inside("a", "\u03b1")) in closure
        assert Literal(On("a", "\u03b1"), polarity=False) in closure

    def test_same_side_symmetry(self):
        """SS2: same-side(a,b,L) → same-side(b,a,L)"""
        from verifier.e_consequence import ConsequenceEngine
        from verifier.e_axioms import SAME_SIDE_AXIOMS
        engine = ConsequenceEngine(axioms=SAME_SIDE_AXIOMS)
        known = {Literal(SameSide("a", "b", "L"))}
        closure = engine.direct_consequences(known)
        assert Literal(SameSide("b", "a", "L")) in closure

    def test_same_side_not_on_line(self):
        """SS3: same-side(a,b,L) → ¬on(a,L)"""
        from verifier.e_consequence import ConsequenceEngine
        from verifier.e_axioms import SAME_SIDE_AXIOMS
        engine = ConsequenceEngine(axioms=SAME_SIDE_AXIOMS)
        known = {Literal(SameSide("a", "b", "L"))}
        closure = engine.direct_consequences(known)
        assert Literal(On("a", "L"), polarity=False) in closure

    def test_same_side_transitivity(self):
        """SS4: same-side(a,b,L) ∧ same-side(a,c,L) → same-side(b,c,L)"""
        from verifier.e_consequence import ConsequenceEngine
        from verifier.e_axioms import SAME_SIDE_AXIOMS
        engine = ConsequenceEngine(axioms=SAME_SIDE_AXIOMS)
        known = {
            Literal(SameSide("a", "b", "L")),
            Literal(SameSide("a", "c", "L")),
        }
        closure = engine.direct_consequences(known)
        assert Literal(SameSide("b", "c", "L")) in closure

    def test_pasch_between_on_line(self):
        """P3: between(a,b,c) ∧ on(b,L) → ¬same-side(a,c,L)"""
        from verifier.e_consequence import ConsequenceEngine
        from verifier.e_axioms import PASCH_AXIOMS
        engine = ConsequenceEngine(axioms=PASCH_AXIOMS)
        known = {
            Literal(Between("a", "b", "c")),
            Literal(On("b", "L")),
        }
        closure = engine.direct_consequences(known)
        assert Literal(SameSide("a", "c", "L"), polarity=False) in closure

    def test_contrapositive(self):
        """B2 contrapositive: between(a,b,c) ∧ on(a,L) ∧ ¬on(c,L)
           → ¬on(b,L)"""
        from verifier.e_consequence import ConsequenceEngine
        from verifier.e_axioms import BETWEEN_AXIOMS
        engine = ConsequenceEngine(axioms=BETWEEN_AXIOMS)
        known = {
            Literal(Between("a", "b", "c")),
            Literal(On("a", "L")),
            Literal(On("c", "L"), polarity=False),
        }
        closure = engine.direct_consequences(known)
        # By contrapositive of B2: ¬on(c,L) ∧ between ∧ on(a,L) → ¬on(b,L)
        assert Literal(On("b", "L"), polarity=False) in closure

    def test_inside_circle_intersects(self):
        """I3: inside(a,α) ∧ on(a,L) → intersects(L,α)"""
        from verifier.e_consequence import ConsequenceEngine
        from verifier.e_axioms import INTERSECTION_AXIOMS
        engine = ConsequenceEngine(axioms=INTERSECTION_AXIOMS)
        known = {
            Literal(Inside("a", "\u03b1")),
            Literal(On("a", "L")),
        }
        closure = engine.direct_consequences(known)
        assert Literal(Intersects("L", "\u03b1")) in closure


# ═══════════════════════════════════════════════════════════════════════
# Metric inference engine tests
# ═══════════════════════════════════════════════════════════════════════

class TestMetricEngine:
    def test_segment_symmetry(self):
        """M3: ab = ba"""
        from verifier.e_metric import MetricEngine
        engine = MetricEngine()
        known = {Literal(Equals(SegmentTerm("a", "b"),
                                SegmentTerm("c", "d")))}
        result = engine.process_literals(known)
        # ab = ba should be derived
        assert engine.state.are_equal(SegmentTerm("a", "b"),
                                       SegmentTerm("b", "a"))

    def test_angle_vertex_symmetry(self):
        """M4: ∠abc = ∠cba"""
        from verifier.e_metric import MetricEngine
        engine = MetricEngine()
        known = {Literal(Equals(AngleTerm("a", "b", "c"),
                                AngleTerm("d", "e", "f")))}
        engine.process_literals(known)
        assert engine.state.are_equal(AngleTerm("a", "b", "c"),
                                       AngleTerm("c", "b", "a"))

    def test_equality_transitivity(self):
        """CN1: ab = cd, cd = ef → ab = ef"""
        from verifier.e_metric import MetricEngine
        engine = MetricEngine()
        known = {
            Literal(Equals(SegmentTerm("a", "b"), SegmentTerm("c", "d"))),
            Literal(Equals(SegmentTerm("c", "d"), SegmentTerm("e", "f"))),
        }
        engine.process_literals(known)
        assert engine.state.are_equal(SegmentTerm("a", "b"),
                                       SegmentTerm("e", "f"))

    def test_inequality(self):
        """ab < cd is tracked"""
        from verifier.e_metric import MetricEngine
        engine = MetricEngine()
        known = {
            Literal(LessThan(SegmentTerm("a", "b"),
                             SegmentTerm("c", "d"))),
        }
        engine.process_literals(known)
        assert engine.state.is_less(SegmentTerm("a", "b"),
                                     SegmentTerm("c", "d"))

    def test_area_symmetry(self):
        """M8: △abc = △cab and △abc = △acb"""
        from verifier.e_metric import MetricEngine
        engine = MetricEngine()
        known = {Literal(Equals(AreaTerm("a", "b", "c"),
                                AreaTerm("d", "e", "f")))}
        engine.process_literals(known)
        assert engine.state.are_equal(AreaTerm("a", "b", "c"),
                                       AreaTerm("c", "a", "b"))
        assert engine.state.are_equal(AreaTerm("a", "b", "c"),
                                       AreaTerm("a", "c", "b"))

    def test_is_consequence(self):
        """Check query via is_consequence"""
        from verifier.e_metric import MetricEngine
        engine = MetricEngine()
        known = {
            Literal(Equals(SegmentTerm("a", "b"), SegmentTerm("c", "d"))),
        }
        # ab = ba should be a consequence
        assert engine.is_consequence(
            known,
            Literal(Equals(SegmentTerm("a", "b"), SegmentTerm("b", "a")))
        )
        # ab = cd should be a consequence (directly known)
        engine2 = MetricEngine()
        assert engine2.is_consequence(
            known,
            Literal(Equals(SegmentTerm("a", "b"), SegmentTerm("c", "d")))
        )


# ═══════════════════════════════════════════════════════════════════════
# Superposition tests
# ═══════════════════════════════════════════════════════════════════════

class TestSuperposition:
    def test_sas_valid(self):
        """SAS with all prerequisites derives 4 facts (3 equalities + area)."""
        from verifier.e_superposition import apply_sas_superposition
        known = {
            Literal(Equals(SegmentTerm("A", "B"), SegmentTerm("D", "E"))),
            Literal(Equals(SegmentTerm("A", "C"), SegmentTerm("D", "F"))),
            Literal(Equals(AngleTerm("B", "A", "C"),
                           AngleTerm("E", "D", "F"))),
        }
        result = apply_sas_superposition(known, "A", "B", "C", "D", "E", "F")
        assert result.valid
        assert len(result.derived) == 4
        # Should derive BC = EF
        assert Literal(Equals(SegmentTerm("B", "C"),
                              SegmentTerm("E", "F"))) in result.derived
        # Should derive ∠ABC = ∠DEF
        assert Literal(Equals(AngleTerm("A", "B", "C"),
                              AngleTerm("D", "E", "F"))) in result.derived
        # Should derive △ABC = △DEF
        assert Literal(Equals(AreaTerm("A", "B", "C"),
                              AreaTerm("D", "E", "F"))) in result.derived

    def test_sas_missing_prereq(self):
        """SAS with missing prerequisite fails."""
        from verifier.e_superposition import apply_sas_superposition
        known = {
            Literal(Equals(SegmentTerm("A", "B"), SegmentTerm("D", "E"))),
            # Missing: AC = DF
            Literal(Equals(AngleTerm("B", "A", "C"),
                           AngleTerm("E", "D", "F"))),
        }
        result = apply_sas_superposition(known, "A", "B", "C", "D", "E", "F")
        assert not result.valid
        assert "Missing" in result.error

    def test_sss_valid(self):
        """SSS with all prerequisites derives 4 facts (3 angles + area)."""
        from verifier.e_superposition import apply_sss_superposition
        known = {
            Literal(Equals(SegmentTerm("A", "B"), SegmentTerm("D", "E"))),
            Literal(Equals(SegmentTerm("B", "C"), SegmentTerm("E", "F"))),
            Literal(Equals(SegmentTerm("C", "A"), SegmentTerm("F", "D"))),
        }
        result = apply_sss_superposition(known, "A", "B", "C", "D", "E", "F")
        assert result.valid
        assert len(result.derived) == 4
        # Should derive △ABC = △DEF
        assert Literal(Equals(AreaTerm("A", "B", "C"),
                              AreaTerm("D", "E", "F"))) in result.derived

    def test_superposition_hypotheses(self):
        """SAS hypotheses contain expected literals."""
        from verifier.e_superposition import (
            sas_hypotheses, superposition_literals)
        hyps = sas_hypotheses("a", "b", "c", "ap", "bp", "cp",
                               "d", "L", "g", "h")
        lits = superposition_literals(hyps)
        # Should have: vertex_eq, on_line, direction, same_side, angle_eq
        assert len(lits) == 5
        assert hyps.vertex_eq == Literal(Equals("ap", "d"))
        assert hyps.on_line == Literal(On("bp", "L"))


# ═══════════════════════════════════════════════════════════════════════
# Proof checker tests
# ═══════════════════════════════════════════════════════════════════════

class TestEChecker:
    def test_simple_diagrammatic_proof(self):
        """A proof using diagrammatic axioms: center → inside → ¬on."""
        from verifier.e_checker import check_proof
        from verifier.e_ast import EProof, ProofStep, StepKind

        proof = EProof(
            name="center-inside",
            free_vars=[("a", Sort.POINT), ("\u03b1", Sort.CIRCLE)],
            hypotheses=[Literal(Center("a", "\u03b1"))],
            goal=[
                Literal(Inside("a", "\u03b1")),
                Literal(On("a", "\u03b1"), polarity=False),
            ],
            steps=[
                ProofStep(
                    id=1,
                    kind=StepKind.DIAGRAMMATIC,
                    assertions=[Literal(Inside("a", "\u03b1"))],
                ),
                ProofStep(
                    id=2,
                    kind=StepKind.DIAGRAMMATIC,
                    assertions=[
                        Literal(On("a", "\u03b1"), polarity=False)],
                ),
            ],
        )
        result = check_proof(proof)
        assert result.valid, f"Errors: {result.errors}"

    def test_invalid_step_fails(self):
        """An unjustified assertion is rejected."""
        from verifier.e_checker import check_proof
        from verifier.e_ast import EProof, ProofStep, StepKind

        proof = EProof(
            name="bad-proof",
            free_vars=[("a", Sort.POINT), ("L", Sort.LINE)],
            hypotheses=[],
            goal=[Literal(On("a", "L"))],
            steps=[
                ProofStep(
                    id=1,
                    kind=StepKind.DIAGRAMMATIC,
                    assertions=[Literal(On("a", "L"))],
                ),
            ],
        )
        result = check_proof(proof)
        assert not result.valid
        assert any("not a direct consequence" in e for e in result.errors)

    def test_goal_not_met(self):
        """Proof that doesn't establish the goal is rejected."""
        from verifier.e_checker import check_proof
        from verifier.e_ast import EProof, ProofStep, StepKind

        proof = EProof(
            name="incomplete",
            free_vars=[("a", Sort.POINT), ("\u03b1", Sort.CIRCLE)],
            hypotheses=[Literal(Center("a", "\u03b1"))],
            goal=[
                Literal(On("a", "\u03b1")),  # Wrong: on(a,α) is false!
            ],
            steps=[],
        )
        result = check_proof(proof)
        assert not result.valid
        assert any("Goal not established" in e for e in result.errors)


class TestProofOfConcept:
    """End-to-end test: verify a diagrammatic inference chain.

    Demonstrates that center(a,α) → inside(a,α) → ¬on(a,α)
    can be proved and checked in System E.
    """

    def test_center_inside_not_on_proof(self):
        """Full proof: center(a,α) entails inside(a,α) and ¬on(a,α)."""
        from verifier.e_checker import check_proof
        from verifier.e_ast import EProof, ProofStep, StepKind

        proof = EProof(
            name="G3+G4 chain",
            free_vars=[("a", Sort.POINT), ("\u03b1", Sort.CIRCLE)],
            hypotheses=[Literal(Center("a", "\u03b1"))],
            goal=[
                Literal(Inside("a", "\u03b1")),
                Literal(On("a", "\u03b1"), polarity=False),
            ],
            steps=[
                # Step 1: G3 gives inside(a,α)
                ProofStep(
                    id=1,
                    kind=StepKind.DIAGRAMMATIC,
                    description="center → inside (G3)",
                    assertions=[Literal(Inside("a", "\u03b1"))],
                ),
                # Step 2: G4 gives ¬on(a,α)
                ProofStep(
                    id=2,
                    kind=StepKind.DIAGRAMMATIC,
                    description="inside → ¬on (G4)",
                    assertions=[
                        Literal(On("a", "\u03b1"), polarity=False)],
                ),
            ],
        )
        result = check_proof(proof)
        assert result.valid, f"Proof failed: {result.errors}"

    def test_between_collinearity_proof(self):
        """Prove that between(a,b,c) ∧ on(a,L) ∧ on(b,L) → on(c,L)."""
        from verifier.e_checker import check_proof
        from verifier.e_ast import EProof, ProofStep, StepKind

        proof = EProof(
            name="B2: between collinearity",
            free_vars=[
                ("a", Sort.POINT), ("b", Sort.POINT),
                ("c", Sort.POINT), ("L", Sort.LINE),
            ],
            hypotheses=[
                Literal(Between("a", "b", "c")),
                Literal(On("a", "L")),
                Literal(On("b", "L")),
            ],
            goal=[Literal(On("c", "L"))],
            steps=[
                ProofStep(
                    id=1,
                    kind=StepKind.DIAGRAMMATIC,
                    description="B2: between + on → on",
                    assertions=[Literal(On("c", "L"))],
                ),
            ],
        )
        result = check_proof(proof)
        assert result.valid, f"Proof failed: {result.errors}"


# ═══════════════════════════════════════════════════════════════════════
# Phase 2: Integration tests — Library, Proofs, and Bridge
# ═══════════════════════════════════════════════════════════════════════

class TestELibrary:
    """Tests for the System E theorem library."""

    def test_library_loads(self):
        from verifier.e_library import E_THEOREM_LIBRARY
        assert len(E_THEOREM_LIBRARY) >= 7
        assert "Prop.I.1" in E_THEOREM_LIBRARY
        assert "Prop.I.4" in E_THEOREM_LIBRARY

    def test_prop_i1_sequent(self):
        from verifier.e_library import PROP_I_1
        seq = PROP_I_1.sequent
        # Hypothesis: a ≠ b
        assert len(seq.hypotheses) == 1
        assert seq.hypotheses[0].is_negative
        # Existential: ∃c
        assert len(seq.exists_vars) == 1
        assert seq.exists_vars[0] == ("c", Sort.POINT)
        # Conclusions include ab = ac and ab = bc
        assert len(seq.conclusions) == 4

    def test_prop_i4_sequent(self):
        from verifier.e_library import PROP_I_4
        seq = PROP_I_4.sequent
        # SAS: 3 hypotheses (ab=de, ac=df, ∠bac=∠edf)
        assert len(seq.hypotheses) == 3
        # No new objects constructed
        assert len(seq.exists_vars) == 0
        # 4 conclusions (bc=ef, ∠abc=∠def, ∠bca=∠efd, △abc=△def)
        assert len(seq.conclusions) == 4

    def test_get_theorems_up_to(self):
        from verifier.e_library import get_theorems_up_to
        # Theorems before Prop.I.4 should include I.1, I.2, I.3
        before_i4 = get_theorems_up_to("Prop.I.4")
        assert "Prop.I.1" in before_i4
        assert "Prop.I.2" in before_i4
        assert "Prop.I.3" in before_i4
        assert "Prop.I.4" not in before_i4

    def test_get_theorems_up_to_first(self):
        from verifier.e_library import get_theorems_up_to
        before_i1 = get_theorems_up_to("Prop.I.1")
        assert len(before_i1) == 0


class TestEProofs:
    """Tests for the System E proof definitions."""

    def test_prop_i1_proof_structure(self):
        from verifier.e_proofs import make_prop_i1_proof
        proof = make_prop_i1_proof()
        assert proof.name == "Prop.I.1"
        assert len(proof.free_vars) == 2
        assert len(proof.hypotheses) == 1
        assert len(proof.exists_vars) == 1
        assert len(proof.goal) == 4
        assert len(proof.steps) == 10

    def test_prop_i1_step_kinds(self):
        from verifier.e_proofs import make_prop_i1_proof
        proof = make_prop_i1_proof()
        kinds = [s.kind for s in proof.steps]
        # Steps 1,2: construction (circles)
        assert kinds[0] == StepKind.CONSTRUCTION
        assert kinds[1] == StepKind.CONSTRUCTION
        # Step 3: diagrammatic (intersection)
        assert kinds[2] == StepKind.DIAGRAMMATIC
        # Step 4: construction (intersection point)
        assert kinds[3] == StepKind.CONSTRUCTION
        # Steps 5,6: transfer (radii equality)
        assert kinds[4] == StepKind.TRANSFER
        assert kinds[5] == StepKind.TRANSFER
        # Steps 7-10: metric
        assert kinds[6] == StepKind.METRIC
        assert kinds[7] == StepKind.METRIC
        assert kinds[8] == StepKind.METRIC
        assert kinds[9] == StepKind.METRIC

    def test_get_proof(self):
        from verifier.e_proofs import get_proof
        proof = get_proof("Prop.I.1")
        assert proof.name == "Prop.I.1"

    def test_get_proof_unknown(self):
        from verifier.e_proofs import get_proof
        with pytest.raises(KeyError):
            get_proof("Prop.I.999")


class TestNewAxiomCounts:
    """Verify the new DA1, DA2, DA5 axioms are present."""

    def test_diagram_angle_transfer_count(self):
        from verifier.e_axioms import DIAGRAM_ANGLE_TRANSFER
        # DA1: 3 clauses, DA2: 3 clauses, DA3: 2 clauses,
        # DA4: 1 clause, DA5: 2 clauses = 11
        assert len(DIAGRAM_ANGLE_TRANSFER) == 11

    def test_all_transfer_axioms_increased(self):
        from verifier.e_axioms import ALL_TRANSFER_AXIOMS
        # DS: 6, DA: 11, DAr: 3, inside/outside: 2 = 22
        assert len(ALL_TRANSFER_AXIOMS) == 22

    def test_da5_parallel_postulate_present(self):
        """DA5 clauses should contain Intersects and angle sum."""
        from verifier.e_axioms import DIAGRAM_ANGLE_TRANSFER
        # The last two clauses should be DA5
        da5a = DIAGRAM_ANGLE_TRANSFER[-2]
        da5b = DIAGRAM_ANGLE_TRANSFER[-1]
        # DA5a should conclude with intersects
        has_intersects = any(
            isinstance(lit.atom, Intersects) and lit.polarity
            for lit in da5a.literals)
        assert has_intersects
        # DA5b should conclude with same-side
        has_same_side = any(
            isinstance(lit.atom, SameSide) and lit.polarity
            for lit in da5b.literals)
        assert has_same_side


class TestCircleIntersectionInference:
    """Test the I5 inference chain used in Prop I.1:
    on(b,α) ∧ inside(a,α) ∧ inside(b,β) ∧ on(a,β) → intersects(α,β)
    """

    def test_i5_circle_circle_intersection(self):
        from verifier.e_consequence import ConsequenceEngine
        from verifier.e_axioms import (
            GENERALITY_AXIOMS, INTERSECTION_AXIOMS,
        )
        engine = ConsequenceEngine(
            axioms=GENERALITY_AXIOMS + INTERSECTION_AXIOMS)
        known = {
            # center(a,α) → inside(a,α) via G3
            Literal(Center("a", "α")),
            Literal(On("b", "α")),
            # center(b,β) → inside(b,β) via G3
            Literal(Center("b", "β")),
            Literal(On("a", "β")),
        }
        closure = engine.direct_consequences(known)
        # Should derive inside(a,α) and inside(b,β) from G3
        assert Literal(Inside("a", "α")) in closure
        assert Literal(Inside("b", "β")) in closure
        # Should derive intersects(α,β) from I5
        assert Literal(Intersects("α", "β")) in closure

    def test_transfer_radii_equality(self):
        """DS3b: center(a,α) ∧ on(b,α) ∧ on(c,α) → ac = ab"""
        from verifier.e_transfer import TransferEngine
        known_diag = {
            Literal(Center("a", "α")),
            Literal(On("b", "α")),
            Literal(On("c", "α")),
        }
        known_metric: set = set()
        engine = TransferEngine()
        derived = engine.apply_transfers(
            known_diag, known_metric,
            {"a": Sort.POINT, "b": Sort.POINT, "c": Sort.POINT,
             "α": Sort.CIRCLE})
        # Should derive ac = ab
        expected = Literal(Equals(SegmentTerm("a", "c"),
                                   SegmentTerm("a", "b")))
        assert expected in derived


# ═══════════════════════════════════════════════════════════════════════
# PROPOSITION VALIDITY TESTS — all 48 Book I proofs must verify
# ═══════════════════════════════════════════════════════════════════════

import pytest


_PROP_NAMES = [f"Prop.I.{i}" for i in range(1, 49)]


class TestAllPropositionsValid:
    """Verify that every encoded Book I proposition proof is accepted."""

    @pytest.mark.parametrize("name", _PROP_NAMES)
    def test_proposition_valid(self, name):
        from verifier.unified_checker import verify_named_proof
        result = verify_named_proof(name)
        assert result.valid, (
            f"{name} failed: {result.errors[:3]}"
        )


# ═══════════════════════════════════════════════════════════════════════
# ZeroMag sort inference tests
# ═══════════════════════════════════════════════════════════════════════

class TestZeroMagSortInference:
    """Verify that the parser infers the correct ZeroMag sort from context."""

    def test_segment_zero_sort(self):
        lits = parse_literal_list("ab = 0")
        atom = lits[0].atom
        assert isinstance(atom.right, ZeroMag)
        assert atom.right.sort == Sort.SEGMENT

    def test_angle_zero_sort(self):
        lits = parse_literal_list("\u2220abc = 0")
        atom = lits[0].atom
        assert isinstance(atom.right, ZeroMag)
        assert atom.right.sort == Sort.ANGLE

    def test_area_zero_sort(self):
        lits = parse_literal_list("\u25b3abc = 0")
        atom = lits[0].atom
        assert isinstance(atom.right, ZeroMag)
        assert atom.right.sort == Sort.AREA

    def test_zero_on_left_angle(self):
        lits = parse_literal_list("0 < \u2220abc")
        atom = lits[0].atom
        assert isinstance(atom.left, ZeroMag)
        assert atom.left.sort == Sort.ANGLE

    def test_zero_on_left_segment(self):
        lits = parse_literal_list("0 < ab")
        atom = lits[0].atom
        assert isinstance(atom.left, ZeroMag)
        assert atom.left.sort == Sort.SEGMENT

    def test_zero_on_left_area(self):
        lits = parse_literal_list("0 < \u25b3abc")
        atom = lits[0].atom
        assert isinstance(atom.left, ZeroMag)
        assert atom.left.sort == Sort.AREA


# ═══════════════════════════════════════════════════════════════════════
# M1 forward direction tests
# ═══════════════════════════════════════════════════════════════════════

class TestM1Forward:
    """Verify M1: ab = 0 → a = b (forward direction)."""

    def test_ab_zero_implies_a_eq_b(self):
        from verifier.e_metric import MetricEngine
        me = MetricEngine()
        known = {Literal(Equals(SegmentTerm("a", "b"),
                                ZeroMag(Sort.SEGMENT)))}
        query = Literal(Equals("a", "b"))
        assert me.is_consequence(known, query) is True

    def test_contrapositive_still_works(self):
        from verifier.e_metric import MetricEngine
        me = MetricEngine()
        known = {Literal(Equals("a", "b"), False)}
        query = Literal(Equals(SegmentTerm("a", "b"),
                                ZeroMag(Sort.SEGMENT)), False)
        assert me.is_consequence(known, query) is True

    def test_nonzero_segment_no_point_eq(self):
        from verifier.e_metric import MetricEngine
        me = MetricEngine()
        known = {Literal(Equals("a", "b"), False)}  # a ≠ b
        query = Literal(Equals("a", "b"))  # a = b
        assert me.is_consequence(known, query) is False

    def test_cn5_whole_greater_than_part(self):
        """CN5: a + b = c, b > 0 → a < c."""
        from verifier.e_metric import MetricEngine
        me = MetricEngine()
        known = {
            Literal(Equals(MagAdd(SegmentTerm("a", "b"),
                                  SegmentTerm("b", "c")),
                           SegmentTerm("a", "c"))),
            Literal(Equals("b", "c"), False),  # b ≠ c → bc > 0
        }
        assert me.is_consequence(
            known, Literal(LessThan(SegmentTerm("a", "b"),
                                    SegmentTerm("a", "c")))) is True

    def test_cn5_symmetric(self):
        """CN5 symmetric: a + b = c, a > 0 → b < c."""
        from verifier.e_metric import MetricEngine
        me = MetricEngine()
        known = {
            Literal(Equals(MagAdd(SegmentTerm("a", "b"),
                                  SegmentTerm("b", "c")),
                           SegmentTerm("a", "c"))),
            Literal(Equals("a", "b"), False),  # a ≠ b → ab > 0
        }
        assert me.is_consequence(
            known, Literal(LessThan(SegmentTerm("b", "c"),
                                    SegmentTerm("a", "c")))) is True

    def test_cn2_addition_congruence(self):
        """CN2: a = b, c = d → a + c = b + d."""
        from verifier.e_metric import MetricEngine
        me = MetricEngine()
        known = {
            Literal(Equals(SegmentTerm("a", "b"),
                           SegmentTerm("c", "d"))),
            Literal(Equals(SegmentTerm("e", "f"),
                           SegmentTerm("g", "h"))),
        }
        query = Literal(Equals(
            MagAdd(SegmentTerm("a", "b"), SegmentTerm("e", "f")),
            MagAdd(SegmentTerm("c", "d"), SegmentTerm("g", "h"))))
        assert me.is_consequence(known, query) is True

    def test_less_through_equality(self):
        """Inequality propagates through equality: af=cd, cd<ab → af<ab."""
        from verifier.e_metric import MetricEngine
        me = MetricEngine()
        known = {
            Literal(Equals(SegmentTerm("a", "f"),
                           SegmentTerm("c", "d"))),
            Literal(LessThan(SegmentTerm("c", "d"),
                             SegmentTerm("a", "b"))),
        }
        assert me.is_consequence(
            known, Literal(LessThan(SegmentTerm("a", "f"),
                                    SegmentTerm("a", "b")))) is True

    def test_plus_monotonicity(self):
        """+ monotonicity: a < b → a + c < b + c."""
        from verifier.e_metric import MetricEngine
        me = MetricEngine()
        known = {
            Literal(LessThan(SegmentTerm("a", "b"),
                             SegmentTerm("c", "d"))),
        }
        query = Literal(LessThan(
            MagAdd(SegmentTerm("a", "b"), SegmentTerm("e", "f")),
            MagAdd(SegmentTerm("c", "d"), SegmentTerm("e", "f"))))
        assert me.is_consequence(known, query) is True


# ═══════════════════════════════════════════════════════════════════════
# Reductio step type tests
# ═══════════════════════════════════════════════════════════════════════

class TestReductioStepType:
    """Verify the Reductio step type in the JSON proof checker."""

    def test_reductio_with_contradiction(self):
        from verifier.unified_checker import verify_e_proof_json
        pj = {
            "name": "reductio_test",
            "declarations": {"points": ["a", "b"], "lines": ["L"]},
            "premises": ["on(a, L)", "on(b, L)"],
            "goal": "a = b",
            "lines": [
                {"id": 1, "depth": 0, "statement": "on(a, L)",
                 "justification": "Given", "refs": []},
                {"id": 2, "depth": 0, "statement": "on(b, L)",
                 "justification": "Given", "refs": []},
                # Assume ¬(a = b)
                {"id": 3, "depth": 1, "statement": "\u00ac(a = b)",
                 "justification": "Assume", "refs": []},
                # Derive a contradiction: on(a, L) and ¬on(a, L)
                {"id": 4, "depth": 1, "statement": "\u00ac(on(a, L))",
                 "justification": "Assume", "refs": []},
                # Reductio: conclude a = b
                {"id": 5, "depth": 0, "statement": "a = b",
                 "justification": "Reductio", "refs": [3]},
            ],
        }
        result = verify_e_proof_json(pj)
        # The assume ¬on(a,L) contradicts given on(a,L)
        assert 5 in result.derived

    def test_reductio_without_refs_fails(self):
        from verifier.unified_checker import verify_e_proof_json
        pj = {
            "name": "reductio_no_refs",
            "declarations": {"points": ["a", "b"], "lines": []},
            "premises": [],
            "goal": "",
            "lines": [
                {"id": 1, "depth": 0, "statement": "a = b",
                 "justification": "Reductio", "refs": []},
            ],
        }
        result = verify_e_proof_json(pj)
        assert 1 not in result.derived

    def test_classify_reductio(self):
        from verifier.unified_checker import _classify_justification
        from verifier.e_ast import StepKind
        assert _classify_justification("Reductio") == StepKind.REDUCTIO

    def test_classify_assume(self):
        """Assume is handled as special case, not via _classify_justification."""
        from verifier.unified_checker import _classify_justification
        # Assume is not in the classification map
        assert _classify_justification("Assume") is None

    def test_structural_rules_in_catalogue(self):
        from verifier.unified_checker import get_available_rules
        rules = get_available_rules()
        structural = [r for r in rules if r.category == "structural"]
        names = [r.name for r in structural]
        assert "Assume" in names
        assert "Reductio" in names
        assert "Reit" in names

    def test_reductio_retracts_subproof_facts(self):
        """After Reductio closes, subproof-scoped facts must not persist."""
        from verifier.unified_checker import verify_e_proof_json
        pj = {
            "name": "scoping_test",
            "declarations": {"points": ["a", "b", "c"], "lines": ["L"]},
            "premises": ["on(a, L)"],
            "goal": "",
            "lines": [
                {"id": 1, "depth": 0, "statement": "on(a, L)",
                 "justification": "Given", "refs": []},
                # Subproof: assume ¬(a = b) and also assume between(a,c,b)
                {"id": 2, "depth": 1, "statement": "\u00ac(a = b)",
                 "justification": "Assume", "refs": []},
                {"id": 3, "depth": 1, "statement": "between(a, c, b)",
                 "justification": "Assume", "refs": []},
                # Create contradiction: assume ¬on(a, L)
                {"id": 4, "depth": 1, "statement": "\u00ac(on(a, L))",
                 "justification": "Assume", "refs": []},
                # Reductio: conclude a = b
                {"id": 5, "depth": 0, "statement": "a = b",
                 "justification": "Reductio", "refs": [2]},
                # Now try to use between(a,c,b) which was only in the
                # subproof.  This should fail because it was retracted.
                {"id": 6, "depth": 0,
                 "statement": "between(a, c, b)",
                 "justification": "Diagrammatic", "refs": []},
            ],
        }
        result = verify_e_proof_json(pj)
        # Line 5 (Reductio) should succeed
        assert 5 in result.derived
        # Line 6 should fail — between(a,c,b) was retracted with the
        # subproof and cannot be re-derived at the outer depth.
        assert 6 not in result.derived
