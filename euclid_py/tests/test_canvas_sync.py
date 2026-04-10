"""
test_canvas_sync.py — Unit tests for the proof-to-canvas sync feature.

Tests the _sync_proof_to_canvas method on _WorkspaceScreen by supplying
hand-crafted step lists and asserting on the canvas scene state
(points placed, segments drawn, circles drawn).

Coverage:
  - let-circle: center + edge point placed, circle drawn
  - let-circle (reusing existing point as edge): radius computed correctly
  - let-intersection-circle-circle-one: point at geometric intersection
  - Metric/transfer step segment scan: segments inferred from "ab = cd" text
  - let-line: segment drawn between named endpoints
  - let-point-on-line-extend: point placed at line-circle intersection
  - I.1 scenario: two circles + intersection point + three triangle sides
  - I.2 partial scenario: line + circle + line-circle intersection point
"""
from __future__ import annotations

import math
import sys
import pytest


def _has_display() -> bool:
    try:
        from PyQt6.QtWidgets import QApplication
        QApplication.instance() or QApplication(sys.argv)
        return True
    except Exception:
        return False


@pytest.mark.skipif(not _has_display(), reason="No display available")
class TestCanvasSync:

    @pytest.fixture(autouse=True)
    def setup(self):
        from PyQt6.QtWidgets import QApplication
        self.app = QApplication.instance() or QApplication(sys.argv)
        from euclid_py.ui.main_window import _WorkspaceScreen
        # _WorkspaceScreen needs a parent EuclidApp — pass None and catch any
        # attribute errors from features that require a full app.
        self.ws = _WorkspaceScreen(None)
        self.scene = self.ws._canvas.scene
        yield

    # ── helpers ────────────────────────────────────────────────────────────

    class _Step:
        """Minimal ProofStep stand-in for sync tests."""
        def __init__(self, justification: str, text: str, status: str = "✓"):
            self.justification = justification
            self.text = text
            self.status = status

    def _sync(self, steps, decl_points=None, decl_lines=None, premises=None):
        self.ws._sync_proof_to_canvas(steps, decl_points or [], decl_lines or [], premises or [])

    def _points(self) -> dict[str, tuple[float, float]]:
        state = self.scene.get_state()
        return {p["label"]: (p["x"], p["y"]) for p in state["points"]}

    def _seg_pairs(self) -> set[frozenset]:
        state = self.scene.get_state()
        return {frozenset((s["from"], s["to"])) for s in state["segments"]}

    def _circles(self) -> list[dict]:
        return self.scene.get_state()["circles"]

    def _ray_pairs(self) -> set[frozenset]:
        state = self.scene.get_state()
        return {frozenset((r["from"], r["through"])) for r in state["rays"]}

    def _approx_equal(self, a: float, b: float, tol: float = 1.0) -> bool:
        return abs(a - b) <= tol

    # ── let-circle ─────────────────────────────────────────────────────────

    def test_let_circle_places_center_and_edge(self):
        """let-circle puts both center and edge point on the canvas."""
        steps = [self._Step("let-circle", "center(a, α), on(b, α)")]
        self._sync(steps)
        pts = self._points()
        assert "a" in pts, "center point a must be placed"
        assert "b" in pts, "edge point b must be placed"

    def test_let_circle_draws_circle(self):
        """let-circle produces exactly one circle."""
        steps = [self._Step("let-circle", "center(a, α), on(b, α)")]
        self._sync(steps)
        circs = self._circles()
        assert len(circs) == 1
        assert circs[0]["center"] == "a"

    def test_let_circle_radius_equals_distance(self):
        """The stored circle radius equals dist(center, edge)."""
        steps = [self._Step("let-circle", "center(a, α), on(b, α)")]
        self._sync(steps)
        pts = self._points()
        circs = self._circles()
        ax, ay = pts["a"]
        bx, by = pts["b"]
        expected_r = math.hypot(bx - ax, by - ay)
        assert self._approx_equal(circs[0]["radius"], expected_r)

    def test_let_circle_shared_edge_point(self):
        """Second let-circle reusing existing point as edge has correct radius."""
        # α: center=a, edge=b.  β: center=b, edge=a (shared existing point).
        steps = [
            self._Step("let-circle", "center(a, α), on(b, α)"),
            self._Step("let-circle", "center(b, β), on(a, β)"),
        ]
        self._sync(steps)
        pts = self._points()
        circs = self._circles()
        assert len(circs) == 2
        ax, ay = pts["a"]
        bx, by = pts["b"]
        r = math.hypot(bx - ax, by - ay)
        # Both circles should have the same radius (equidistant center↔edge)
        assert self._approx_equal(circs[0]["radius"], r)
        assert self._approx_equal(circs[1]["radius"], r)

    # ── circle-circle intersection ──────────────────────────────────────────

    def test_circ_circ_intersection_placed(self):
        """let-intersection-circle-circle-one places c at actual intersection."""
        steps = [
            self._Step("let-circle", "center(a, α), on(b, α)"),
            self._Step("let-circle", "center(b, β), on(a, β)"),
            self._Step("let-intersection-circle-circle-one",
                       "on(c, α), on(c, β)"),
        ]
        self._sync(steps)
        pts = self._points()
        assert "c" in pts, "intersection point c must be placed"

    def test_circ_circ_intersection_on_both_circles(self):
        """Intersection point c lies on circle α and circle β (within tolerance)."""
        steps = [
            self._Step("let-circle", "center(a, α), on(b, α)"),
            self._Step("let-circle", "center(b, β), on(a, β)"),
            self._Step("let-intersection-circle-circle-one",
                       "on(c, α), on(c, β)"),
        ]
        self._sync(steps)
        pts = self._points()
        circs = self._circles()
        cx, cy = pts["c"]
        for circ in circs:
            center_lbl = circ["center"]
            ox, oy = pts[center_lbl]
            dist = math.hypot(cx - ox, cy - oy)
            assert self._approx_equal(dist, circ["radius"], tol=2.0), (
                f"c not on circle centered at {center_lbl}: "
                f"dist={dist:.2f}, r={circ['radius']:.2f}"
            )

    # ── segment inference from metric steps ────────────────────────────────

    def test_metric_step_draws_segment(self):
        """Segment ab inferred from metric step text 'ac = ab'."""
        steps = [
            self._Step("let-circle", "center(a, α), on(b, α)"),
            self._Step("let-circle", "center(b, β), on(a, β)"),
            self._Step("let-intersection-circle-circle-one",
                       "on(c, α), on(c, β)"),
            self._Step("segment-transfer-3b", "ac = ab", status="✗"),
            self._Step("segment-transfer-3b", "bc = ab", status="✗"),
        ]
        self._sync(steps)
        segs = self._seg_pairs()
        assert frozenset(("a", "c")) in segs, "segment ac should be drawn"
        assert frozenset(("b", "c")) in segs, "segment bc should be drawn"
        assert frozenset(("a", "b")) in segs, "segment ab should be drawn"

    # ── I.1 full scenario ──────────────────────────────────────────────────

    def test_prop_i1_full(self):
        """I.1: two equal circles, intersection point c, and all three triangle sides."""
        steps = [
            self._Step("let-circle", "center(a, α), on(b, α)"),
            self._Step("let-circle", "center(b, β), on(a, β)"),
            self._Step("let-intersection-circle-circle-one",
                       "on(c, α), on(c, β)"),
            self._Step("segment-transfer-3b", "ac = ab", status="✗"),
            self._Step("segment-transfer-3b", "bc = ab", status="✗"),
            self._Step("metric",              "ab = ac", status="✗"),
            self._Step("metric",              "ab = bc", status="✗"),
        ]
        self._sync(steps)
        pts = self._points()
        segs = self._seg_pairs()
        circs = self._circles()

        # Three points
        assert {"a", "b", "c"} <= set(pts), "a, b, c must all be placed"
        # Two circles
        assert len(circs) == 2
        # Three triangle sides
        assert frozenset(("a", "b")) in segs, "side ab missing"
        assert frozenset(("a", "c")) in segs, "side ac missing"
        assert frozenset(("b", "c")) in segs, "side bc missing"
        # c above baseline ab in Qt coords (lower y = visually higher)
        ay = pts["a"][1]; by = pts["b"][1]; cy = pts["c"][1]
        baseline_y = (ay + by) / 2
        assert cy < baseline_y, (
            f"intersection point c (y={cy:.1f}) should be above baseline "
            f"(y={baseline_y:.1f}) [Qt: lower y = visually higher]"
        )

    # ── let-line ───────────────────────────────────────────────────────────

    def test_let_line_draws_segment(self):
        """let-line draws a segment between its two on() endpoints."""
        steps = [
            self._Step("let-circle", "center(a, α), on(b, α)"),
            self._Step("let-line",   "on(d, M), on(a, M)"),
        ]
        self._sync(steps)
        segs = self._seg_pairs()
        assert frozenset(("d", "a")) in segs, "segment da should be drawn for let-line"

    def test_let_line_no_duplicate_on_points(self):
        """let-line with on(a,L), on(b,L) places exactly two distinct points."""
        steps = [self._Step("let-line", "on(a, L), on(b, L)")]
        self._sync(steps)
        pts = self._points()
        assert "a" in pts and "b" in pts
        assert pts["a"] != pts["b"], "a and b must be at different positions"

    # ── let-point-on-line-extend (line-circle intersection) ────────────────

    def test_let_point_on_line_extend_placed_on_circle(self):
        """let-point-on-line-extend places new point at line-circle intersection."""
        steps = [
            self._Step("let-circle",              "center(a, α), on(b, α)"),
            self._Step("let-circle",              "center(b, β), on(a, β)"),
            self._Step("let-intersection-circle-circle-one",
                                                  "on(d, α), on(d, β)"),
            self._Step("let-line",                "on(d, M), on(a, M)"),
            self._Step("let-circle",              "center(b, γ), on(c, γ)"),
            self._Step("let-point-on-line-extend",
                       "on(g, M), on(g, β), ¬(g = a)"),
        ]
        self._sync(steps)
        pts = self._points()
        circs = self._circles()
        assert "g" in pts, "point g must be placed"
        # g must lie on circle β (center b)
        beta = next((ci for ci in circs if ci["center"] == "b"
                     and ci.get("radius_point") != "c"), None)
        if beta is None:
            # fall back: pick circle with center b
            beta = next((ci for ci in circs if ci["center"] == "b"), None)
        assert beta is not None, "circle β (center b) not found"
        gx, gy = pts["g"]
        bx, by = pts["b"]
        dist_bg = math.hypot(gx - bx, gy - by)
        assert self._approx_equal(dist_bg, beta["radius"], tol=3.0), (
            f"g not on circle β: dist={dist_bg:.2f}, r={beta['radius']:.2f}"
        )

    # ── theorem-app (Prop.I.1 apex) ────────────────────────────────────────

    def test_theorem_app_i1_places_apex(self):
        """theorem-app of I.1 places new point d as equilateral apex above a-b baseline."""
        steps = [
            # theorem-app self-seeds anchors a and b, then places d as apex
            self._Step("theorem-app",
                       "ab = ad, ab = bd, ¬(d = a), ¬(d = b)"),
        ]
        self._sync(steps)
        pts = self._points()
        assert "d" in pts, "d must be placed by theorem-app"
        # Qt y increases downward: visually above = lower y value.
        ay, by_ = pts["a"][1], pts["b"][1]
        baseline = (ay + by_) / 2
        assert pts["d"][1] < baseline, (
            f"d (y={pts['d'][1]:.1f}) should be above baseline (y={baseline:.1f})"
        )

    def test_theorem_app_i1_equilateral_distances(self):
        """theorem-app apex d is equidistant from a and b (equilateral triangle)."""
        steps = [
            self._Step("theorem-app",
                       "ab = ad, ab = bd, ¬(d = a), ¬(d = b)"),
        ]
        self._sync(steps)
        pts = self._points()
        ax, ay = pts["a"]; bx, by = pts["b"]; dx, dy = pts["d"]
        da = math.hypot(dx - ax, dy - ay)
        db = math.hypot(dx - bx, dy - by)
        assert self._approx_equal(da, db, tol=2.0), (
            f"d not equidistant: da={da:.1f}, db={db:.1f}"
        )

    # ── I.2 partial scenario ───────────────────────────────────────────────

    def test_prop_i2_partial(self):
        """I.2 partial: declared a,b,c seed positions; d placed collinearly; g on circle γ."""
        steps = [
            # Step 1: theorem app gives d (reflection of b through a)
            self._Step("theorem-app",
                       "ab = ad, ab = bd, ¬(d = a), ¬(d = b)"),
            # Step 2: line da
            self._Step("let-line",                "on(d, M), on(a, M)"),
            # Step 3: line db
            self._Step("let-line",                "on(d, N), on(b, N)"),
            # Step 4: circle γ center b radius bc
            self._Step("let-circle",              "center(b, γ), on(c, γ)"),
            # Step 5: g on line N and circle γ
            self._Step("let-point-on-line-extend",
                       "on(g, N), on(g, γ), ¬(g = b)"),
        ]
        # theorem-app self-seeds a and b; c is placed by let-circle
        self._sync(steps)
        pts = self._points()
        segs = self._seg_pairs()
        circs = self._circles()

        # d must be placed above baseline ab (lower y = visually above in Qt)
        assert "d" in pts, "point d must be placed"
        ay_, by_ = pts["a"][1], pts["b"][1]
        assert pts["d"][1] < (ay_ + by_) / 2, "d should be above baseline ab"

        # g must exist
        assert "g" in pts, "point g must be placed"

        # Segments da and db exist (from let-line M and N)
        segs = self._seg_pairs()
        assert frozenset(("d", "a")) in segs, "segment da missing"
        assert frozenset(("d", "b")) in segs, "segment db missing"

        # Circle γ with center b
        gamma = next((ci for ci in circs if ci["center"] == "b"), None)
        assert gamma is not None, "circle γ (center b) missing"

        # g lies on circle γ within tolerance
        gx, gy = pts["g"]
        bx, by2 = pts["b"]
        dist_bg = math.hypot(gx - bx, gy - by2)
        assert self._approx_equal(dist_bg, gamma["radius"], tol=3.0), (
            f"g not on γ: dist={dist_bg:.2f}, r={gamma['radius']:.2f}"
        )
