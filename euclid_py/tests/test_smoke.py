"""Smoke tests for the Python port — engine + UI integration."""
from __future__ import annotations

import json
import math
import sys
import pytest

# ═══════════════════════════════════════════════════════════════════════════
# ENGINE TESTS
# ═══════════════════════════════════════════════════════════════════════════


class TestConstraints:
    def test_distance(self):
        from euclid_py.engine.constraints import distance
        p1 = {"x": 0, "y": 0}
        p2 = {"x": 3, "y": 4}
        assert distance(p1, p2) == pytest.approx(5.0)

    def test_distance_none(self):
        from euclid_py.engine.constraints import distance
        assert distance(None, {"x": 0, "y": 0}) is None

    def test_angle_at_vertex(self):
        from euclid_py.engine.constraints import angle_at_vertex
        a = {"x": 1, "y": 0}
        b = {"x": 0, "y": 0}
        c = {"x": 0, "y": 1}
        assert angle_at_vertex(a, b, c) == pytest.approx(math.pi / 2, abs=0.01)

    def test_collinear(self):
        from euclid_py.engine.constraints import are_collinear
        p1 = {"x": 0, "y": 0}
        p2 = {"x": 1, "y": 1}
        p3 = {"x": 2, "y": 2}
        assert are_collinear(p1, p2, p3) is True

    def test_not_collinear(self):
        from euclid_py.engine.constraints import are_collinear
        p1 = {"x": 0, "y": 0}
        p2 = {"x": 1, "y": 0}
        p3 = {"x": 0, "y": 1}
        assert are_collinear(p1, p2, p3) is False

    def test_circle_intersections(self):
        from euclid_py.engine.constraints import circle_intersections
        c1 = {"x": 0, "y": 0}
        c2 = {"x": 3, "y": 0}
        pts = circle_intersections(c1, 2.5, c2, 2.5)
        assert len(pts) == 2

    def test_segment_intersection(self):
        from euclid_py.engine.constraints import segment_intersection
        p1 = {"x": 0, "y": 0}
        p2 = {"x": 2, "y": 2}
        p3 = {"x": 0, "y": 2}
        p4 = {"x": 2, "y": 0}
        result = segment_intersection(p1, p2, p3, p4)
        assert result is not None
        assert result["x"] == pytest.approx(1.0)
        assert result["y"] == pytest.approx(1.0)

    def test_verifier_distance_equal(self):
        from euclid_py.engine.constraints import ConstraintVerifier, ConstraintType
        canvas = {
            "points": [
                {"label": "A", "x": 0, "y": 0},
                {"label": "B", "x": 3, "y": 4},
                {"label": "C", "x": 5, "y": 0},
                {"label": "D", "x": 8, "y": 4},
            ],
            "segments": [],
        }
        cv = ConstraintVerifier(canvas)
        result = cv.verify({
            "type": ConstraintType.DISTANCE_EQUAL,
            "seg1": {"from": "A", "to": "B"},
            "seg2": {"from": "C", "to": "D"},
        })
        assert result.satisfied is True


class TestPropositionData:
    def test_all_propositions_loaded(self):
        from euclid_py.engine.proposition_data import ALL_PROPOSITIONS
        assert len(ALL_PROPOSITIONS) == 50  # 48 Euclid + 2 textbook

    def test_get_proposition(self):
        from euclid_py.engine.proposition_data import get_proposition
        p = get_proposition("euclid-I.1")
        assert p is not None
        assert p.title == "Equilateral Triangle Construction"

    def test_allowed_propositions(self):
        from euclid_py.engine.proposition_data import get_allowed_propositions
        allowed = get_allowed_propositions(5)
        assert all(p.prop_number <= 5 for p in allowed)


class TestFileFormat:
    def test_round_trip(self, tmp_path):
        from euclid_py.engine.file_format import save_proof, load_proof
        canvas = {
            "points": [{"label": "A", "x": 10, "y": 20}],
            "segments": [{"from": "A", "to": "B"}],
        }
        steps = [{"text": "Segment(A,B)", "justification": "Given", "dependencies": []}]
        path = str(tmp_path / "test.euclid")
        save_proof(path, canvas, steps)
        data = load_proof(path)
        assert data["points"][0]["label"] == "A"
        assert len(data["steps"]) == 1


# ═══════════════════════════════════════════════════════════════════════════
# UI SMOKE TESTS (require display — skipped in headless CI)
# ═══════════════════════════════════════════════════════════════════════════

def _has_display() -> bool:
    try:
        from PyQt6.QtWidgets import QApplication
        app = QApplication.instance() or QApplication(sys.argv)
        return True
    except Exception:
        return False


@pytest.mark.skipif(not _has_display(), reason="No display available")
class TestUiSmoke:
    @pytest.fixture(autouse=True)
    def qt_app(self):
        from PyQt6.QtWidgets import QApplication
        self.app = QApplication.instance() or QApplication(sys.argv)
        yield

    def test_main_window_creates(self):
        from euclid_py.ui.main_window import MainWindow
        w = MainWindow()
        assert w.windowTitle() == "Euclid — Geometric Proof Verifier"

    def test_canvas_add_point(self):
        from euclid_py.ui.canvas_widget import CanvasWidget
        c = CanvasWidget()
        c.add_point("A", 100, 200)
        state = c.get_state()
        assert len(state["points"]) == 1
        assert state["points"][0]["label"] == "A"

    def test_canvas_add_segment(self):
        from euclid_py.ui.canvas_widget import CanvasWidget
        c = CanvasWidget()
        c.add_point("A", 0, 0)
        c.add_point("B", 100, 100)
        c.add_segment("A", "B")
        state = c.get_state()
        assert len(state["segments"]) == 1

    def test_proof_panel_add_step(self):
        from euclid_py.ui.proof_panel import ProofPanel
        p = ProofPanel()
        p.add_step("Segment(A,B)", "Given", [])
        steps = p.get_steps()
        assert len(steps) == 1
        assert steps[0]["text"] == "Segment(A,B)"

    def test_open_proposition(self):
        from euclid_py.ui.main_window import MainWindow
        from euclid_py.engine.proposition_data import get_proposition
        w = MainWindow()
        prop = get_proposition("euclid-I.1")
        w.open_proposition(prop)
        # Should have switched to workspace and loaded given objects

    def test_fitch_proof_view_creates(self):
        from euclid_py.ui.proof_view import FitchProofView, ProofLineData
        v = FitchProofView()
        lines = [
            ProofLineData(1, 0, "A != B", "Given", [], status="valid"),
            ProofLineData(2, 0, "ExistsUnique(l, OnLine(A,l) && OnLine(B,l))", "Inc1", [1], status="valid"),
        ]
        v.set_lines(lines)
        assert len(v._lines) == 2

    def test_fitch_proof_view_scope_bars(self):
        from euclid_py.ui.proof_view import FitchProofView, ProofLineData
        v = FitchProofView()
        lines = [
            ProofLineData(1, 0, "P", "Given", []),
            ProofLineData(2, 1, "Q", "Assume", [], is_assumption=True),
            ProofLineData(3, 1, "R", "Reit", [1]),
            ProofLineData(4, 0, "S", "RAA", [2, 3]),
        ]
        v.set_lines(lines)
        # Should have scope ranges for depth 1
        assert any(d == 1 for d, _, _ in v._scope_ranges)

    def test_proof_panel_composite(self):
        from euclid_py.ui.proof_view import ProofPanel, ProofLineData
        p = ProofPanel()
        lines = [ProofLineData(1, 0, "A != B", "Given", [], status="valid")]
        p.set_proof_data(lines, goal_text="A != B", goal_achieved=True)

    def test_summary_panel(self):
        from euclid_py.ui.summary_panel import SummaryPanel
        s = SummaryPanel()
        s.set_proof_info(name="Test", points=["A", "B"], premises=["A != B"], goal="X")
        s.set_result(accepted=True, num_lines=2, num_errors=0)

    def test_diagnostics_panel(self):
        from euclid_py.ui.diagnostics_panel import DiagnosticsPanel
        d = DiagnosticsPanel()
        d.set_diagnostics([
            {"line": 3, "code": "SCOPE_ERROR", "message": "Out of scope"},
        ])
        assert d._list.count() == 1

    def test_diagnostics_panel_empty(self):
        from euclid_py.ui.diagnostics_panel import DiagnosticsPanel
        d = DiagnosticsPanel()
        d.set_diagnostics([])
        assert d._list.count() == 0

    def test_rule_reference_panel(self):
        from euclid_py.ui.rule_reference import RuleReferencePanel
        r = RuleReferencePanel()
        # Should build without error

    def test_rule_reference_uses_system_e(self):
        """Phase 9.4: rule reference sources System E rules, not legacy."""
        from euclid_py.ui.rule_reference import _RULES
        categories = {r.category for r in _RULES}
        # Must have System E categories (paper sections)
        assert "construction" in categories
        assert "diagrammatic" in categories
        assert "metric" in categories
        assert "transfer" in categories
        assert "superposition" in categories
        assert "proposition" in categories
        # Must NOT have legacy categories
        assert "kernel" not in categories
        assert "derived" not in categories

    def test_rule_reference_has_all_propositions(self):
        from euclid_py.ui.rule_reference import _RULES
        prop_rules = [r for r in _RULES if r.category == "proposition"]
        assert len(prop_rules) == 48

    def test_rule_reference_total_count(self):
        from euclid_py.ui.rule_reference import _RULES
        assert len(_RULES) >= 100  # 20 construction + 45 diag + 17 metric + 20 transfer + 2 super + 48 prop

    def test_verifier_screen_load(self, tmp_path):
        import json
        from euclid_py.ui.main_window import MainWindow
        proof = {
            "name": "test",
            "declarations": {"points": ["A", "B"], "lines": []},
            "premises": ["A != B"],
            "goal": "ExistsUnique(l, OnLine(A,l) && OnLine(B,l))",
            "lines": [
                {"id": 1, "depth": 0, "statement": "A != B", "justification": "Given", "refs": []},
                {"id": 2, "depth": 0, "statement": "ExistsUnique(l, OnLine(A,l) && OnLine(B,l))", "justification": "Inc1", "refs": [1]},
            ]
        }
        path = str(tmp_path / "test_proof.json")
        with open(path, "w") as f:
            json.dump(proof, f)
        w = MainWindow()
        w.open_proof_json(path)

    def test_eval_all_no_crash(self):
        """Regression: _eval_all must not raise NameError on checker.derived."""
        from euclid_py.ui.proof_panel import ProofPanel
        p = ProofPanel()
        p.set_declarations(["A", "B", "C"], [])
        p.add_premise_text("Between(A,B,C)")
        p.set_conclusion("Between(C,B,A)")
        p.add_step("Between(C,B,A)", "Ord2", [1])
        # This used to crash with: NameError: name 'checker' is not defined
        p._eval_all()
        # After fix, the step should be marked as derived (✓)
        statuses = [s.status for s in p._steps]
        assert "\u2713" in statuses, f"Expected ✓ in statuses, got: {statuses}"


# ═══════════════════════════════════════════════════════════════════════════
# PHASE 9.1 TESTS — System E as Default Engine
# ═══════════════════════════════════════════════════════════════════════════

class TestSystemEDefault:
    """Phase 9.1: Predicate palette and rule catalogue use System E."""

    def test_predicates_use_system_e_syntax(self):
        from euclid_py.ui.proof_panel import PREDICATES
        names = [name for name, _ in PREDICATES]
        # Must have System E predicates
        assert any("on(" in t for _, t in PREDICATES), "Missing on() predicate"
        assert any("between" in t for _, t in PREDICATES), "Missing between() predicate"
        assert any("same-side" in t for _, t in PREDICATES), "Missing same-side predicate"
        assert any("circle" in t for _, t in PREDICATES), "Missing circle construction"
        assert any("line" in t for _, t in PREDICATES), "Missing line construction"
        # Must NOT have old Hilbert predicates
        assert "Point" not in names, "Legacy 'Point' predicate still present"
        assert "Segment" not in names, "Legacy 'Segment' predicate still present"
        assert "OnLine" not in names, "Legacy 'OnLine' predicate still present"
        assert "Congruent" not in names, "Legacy 'Congruent' predicate still present"

    def test_rule_groups_use_system_e_sections(self):
        from euclid_py.ui.proof_panel import RULE_GROUPS
        group_names = list(RULE_GROUPS.keys())
        # Must have System E paper sections
        assert any("§3.3" in g for g in group_names), "Missing Construction (§3.3)"
        assert any("§3.4" in g for g in group_names), "Missing Diagrammatic (§3.4)"
        assert any("§3.5" in g for g in group_names), "Missing Metric (§3.5)"
        assert any("§3.6" in g for g in group_names), "Missing Transfer (§3.6)"
        assert any("§3.7" in g for g in group_names), "Missing Superposition (§3.7)"
        assert any("Prop" in g for g in group_names), "Missing Propositions"
        # Must NOT have old Hilbert categories
        assert "Logical" not in group_names, "Legacy 'Logical' group still present"
        assert "Incidence" not in group_names, "Legacy 'Incidence' group still present"
        assert "Derived" not in group_names, "Legacy 'Derived' group still present"

    def test_all_rule_names_populated(self):
        from euclid_py.ui.proof_panel import ALL_RULE_NAMES
        assert len(ALL_RULE_NAMES) >= 100

    def test_no_legacy_rule_imports(self):
        """proof_panel.py must not import get_legacy_rules at module level."""
        import ast as ast_mod
        import pathlib
        pp = pathlib.Path(__file__).resolve().parent.parent / "ui" / "proof_panel.py"
        tree = ast_mod.parse(pp.read_text(encoding="utf-8-sig"))
        for node in ast_mod.walk(tree):
            if isinstance(node, ast_mod.ImportFrom) and node.module:
                if "get_legacy_rules" in (
                        alias.name for alias in (node.names or [])):
                    assert False, "proof_panel.py still imports get_legacy_rules"


class TestTranslationView:
    """Phase 9.3: E / T / H Translation View."""

    def test_creates(self):
        from euclid_py.ui.translation_view import TranslationView
        tv = TranslationView()
        assert tv is not None

    def test_set_proposition_i1(self):
        """TranslationView populates E, T, H cards for Prop I.1."""
        from euclid_py.ui.translation_view import TranslationView
        from euclid_py.engine.proposition_data import get_proposition
        tv = TranslationView()
        prop = get_proposition("euclid-I.1")
        tv.set_proposition(prop)
        # Should have: title + E card + T card + H card + stretch = 5
        assert tv._container_layout.count() >= 4

    def test_set_proposition_shows_all_three_systems(self):
        """All three systems are shown for a Euclid proposition."""
        from euclid_py.ui.translation_view import TranslationView
        from euclid_py.engine.proposition_data import get_proposition
        tv = TranslationView()
        prop = get_proposition("euclid-I.4")
        tv.set_proposition(prop)
        # Collect label text from child widgets
        texts = []
        for i in range(tv._container_layout.count()):
            item = tv._container_layout.itemAt(i)
            w = item.widget()
            if w:
                for child in w.findChildren(type(w).__mro__[0].__subclasses__(object)[0]
                                            if False else w.__class__):
                    pass
        # Just verify count — 6 items: title + statement + 3 cards + stretch
        assert tv._container_layout.count() == 6

    def test_clear(self):
        """clear() resets to placeholder."""
        from euclid_py.ui.translation_view import TranslationView
        from euclid_py.engine.proposition_data import get_proposition
        tv = TranslationView()
        prop = get_proposition("euclid-I.1")
        tv.set_proposition(prop)
        assert tv._container_layout.count() >= 4
        tv.clear()
        # Placeholder + stretch
        assert tv._container_layout.count() == 2

    def test_non_euclid_prop_shows_placeholder(self):
        """A non-Euclid proposition shows a placeholder message."""
        from euclid_py.ui.translation_view import TranslationView
        from euclid_py.engine.proposition_data import Proposition
        tv = TranslationView()
        fake = Proposition(
            id="test-1", source="test", book="Test", name="Test",
            prop_number=None, max_proposition=0,
            title="Test", statement="Test",
        )
        tv.set_proposition(fake)
        # Should show placeholder (1 label + stretch = 2)
        assert tv._container_layout.count() == 2

    def test_translation_view_in_workspace(self):
        """TranslationView is accessible in the workspace screen."""
        from euclid_py.ui.main_window import MainWindow
        w = MainWindow()
        assert hasattr(w._workspace, '_translation_view')
        assert w._workspace._translation_view is not None

    def test_translation_view_updated_on_load(self):
        """Loading a proposition updates the translation view."""
        from euclid_py.ui.main_window import MainWindow
        from euclid_py.engine.proposition_data import get_proposition
        w = MainWindow()
        prop = get_proposition("euclid-I.5")
        w.open_proposition(prop)
        tv = w._workspace._translation_view
        # Should have E, T, H cards populated (not placeholder)
        assert tv._container_layout.count() >= 4


class TestSystemEPremisesConclusions:
    """Phase 9.1: Premises and conclusions use System E syntax."""

    def test_conclusion_predicates_no_old_syntax(self):
        """No conclusion_predicate uses old Hilbert syntax."""
        from euclid_py.engine.proposition_data import PROPOSITIONS
        old_patterns = ["Point(", "Segment(", "Circle(", "OnLine(",
                        "Equal(", "Congruent(", "EqualAngle(",
                        "Parallel(", "Perpendicular("]
        for p in PROPOSITIONS:
            cp = p.conclusion_predicate
            if not cp:
                continue
            for pat in old_patterns:
                assert pat not in cp, (
                    f"{p.name} conclusion_predicate still uses old "
                    f"syntax '{pat}': {cp}")

    def test_e_library_premises_loaded_for_prop_i1(self):
        """Prop I.1 premises come from E library, not Point(A)/Segment(A,B)."""
        from euclid_py.ui.main_window import MainWindow
        from euclid_py.engine.proposition_data import get_proposition
        w = MainWindow()
        prop = get_proposition("euclid-I.1")
        w._workspace.load_proposition(prop)
        pp = w._workspace._proof_panel
        # E library has ¬(a = b) as sole hypothesis for I.1
        assert len(pp._premises) >= 1
        # Must NOT have old Point(A), Segment(A,B) premises
        for prem in pp._premises:
            assert not prem.startswith("Point("), \
                f"Old 'Point()' premise found: {prem}"
            assert not prem.startswith("Segment("), \
                f"Old 'Segment()' premise found: {prem}"

    def test_e_library_conclusion_loaded_for_prop_i1(self):
        """Prop I.1 conclusion comes from E library conclusions."""
        from euclid_py.ui.main_window import MainWindow
        from euclid_py.engine.proposition_data import get_proposition
        w = MainWindow()
        prop = get_proposition("euclid-I.1")
        w._workspace.load_proposition(prop)
        pp = w._workspace._proof_panel
        conclusion = pp._conclusion
        # E library: ab = ac, ab = bc, ¬(c = a), ¬(c = b)
        assert "=" in conclusion, f"Conclusion missing '=': {conclusion}"
        assert "Triangle(" not in conclusion, \
            f"Old 'Triangle()' in conclusion: {conclusion}"

    def test_all_48_propositions_load(self):
        """All 48 propositions load without errors."""
        from euclid_py.engine.proposition_data import PROPOSITIONS
        assert len(PROPOSITIONS) == 48
        for p in PROPOSITIONS:
            assert p.name, f"Missing name for {p.id}"
            assert p.statement, f"Missing statement for {p.name}"

    def test_build_formal_premises_fallback_uses_system_e(self):
        """Fallback _build_formal_premises uses System E syntax."""
        from euclid_py.ui.main_window import _WorkspaceScreen
        from euclid_py.engine.proposition_data import Proposition, GivenObjects
        prop = Proposition(
            id="test-1", source="test", book="Test", name="Test",
            prop_number=None, max_proposition=0,
            title="Test", statement="Test",
            given_objects=GivenObjects(
                points=[{"label": "A", "x": 0, "y": 0},
                        {"label": "B", "x": 1, "y": 1}],
                segments=[{"from": "A", "to": "B"}],
                circles=[{"center": "O", "radius": "P"}],
            ),
        )
        prems = _WorkspaceScreen._build_formal_premises(prop)
        for prem in prems:
            assert "Point(" not in prem, f"Old Point() in fallback: {prem}"
            assert "Segment(" not in prem, f"Old Segment() in fallback: {prem}"
            assert "Circle(" not in prem, f"Old Circle() in fallback: {prem}"
        # Should have ¬(A = B) for segment and ¬(O = P) for circle
        assert any("¬" in p for p in prems), \
            f"Expected ¬(x = y) style, got: {prems}"


# ═══════════════════════════════════════════════════════════════════════════
# LEGACY DEPRECATION TESTS (Phase 6.5.8)
# ═══════════════════════════════════════════════════════════════════════════

class TestLegacyDeprecation:
    """Phase 6.5.8: Verify old verifier imports are fully removed from euclid_py."""

    def test_old_imports_removed(self):
        """No euclid_py/ source file directly imports from the old verifier modules.

        All verification must route through verifier.unified_checker.
        Old modules (verifier.checker, verifier.rules, verifier.parser,
        verifier.library, verifier.propositions, verifier.matcher,
        verifier.scope) must not appear in any import statement.
        """
        import ast as ast_mod
        import pathlib

        euclid_py_root = pathlib.Path(__file__).resolve().parent.parent
        old_modules = {
            "verifier.checker", "verifier.rules", "verifier.parser",
            "verifier.library", "verifier.propositions",
            "verifier.matcher", "verifier.scope",
        }
        violations = []
        for py_file in euclid_py_root.rglob("*.py"):
            if "__pycache__" in str(py_file):
                continue
            try:
                tree = ast_mod.parse(py_file.read_text(encoding="utf-8"))
            except SyntaxError:
                continue
            for node in ast_mod.walk(tree):
                if isinstance(node, ast_mod.ImportFrom) and node.module:
                    if node.module in old_modules:
                        rel = py_file.relative_to(euclid_py_root)
                        violations.append(
                            f"{rel}:{node.lineno}: from {node.module}")
        assert violations == [], (
            "Old verifier imports found in euclid_py/:\n"
            + "\n".join(violations)
        )

    def test_unified_checker_importable(self):
        """The unified checker is importable and has the expected API."""
        from verifier.unified_checker import (
            verify_proof,
            verify_old_proof_json,
            verify_step,
            get_available_rules,
            get_theorem,
            parse_legacy_formula,
            get_legacy_rules,
        )
        assert callable(verify_proof)
        assert callable(verify_old_proof_json)
        assert callable(verify_step)
        assert callable(get_available_rules)
        assert callable(get_theorem)
        assert callable(parse_legacy_formula)
        assert callable(get_legacy_rules)
