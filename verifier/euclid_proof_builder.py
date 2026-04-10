"""
euclid_proof_builder.py — Fluent builder for .euclid proof files.

Constructs proofs step-by-step, auto-numbering lines, tracking declarations,
and serializing to the .euclid JSON format that verify_e_proof_json accepts.

Usage:
    proof = (EuclidProofBuilder("Prop.I.16")
        .premise("on(a, L)")
        .premise("on(b, L)")
        .premise("between(a, b, d)")
        .premise("¬(on(c, L))")
        .premise("¬(a = b)")
        .premise("¬(a = c)")
        .premise("¬(b = c)")
        .goal("∠bac < ∠dbc, ∠bca < ∠dbc")
        .declare_points("a", "b", "c", "d")
        .declare_lines("L")
        .let_line("on(b, M), on(c, M)", refs=[7], new_name="M")
        .theorem("between(b, e, c), be = ec", "Prop.I.10", refs=[5, 6, 7])
        .axiom("∠bac < ∠dbc", "Angle transfer 6", refs=[...])
        .build())

    # Verify:
    from verifier.unified_checker import verify_e_proof_json
    result = verify_e_proof_json(proof)
    assert result.accepted
"""
from __future__ import annotations

import json
import datetime
from pathlib import Path
from typing import Any, Dict, List, Optional, Set


class EuclidProofBuilder:
    """Fluent builder for .euclid proof JSON documents."""

    def __init__(self, name: str):
        """Initialize with proof name (e.g. 'Prop.I.16')."""
        self._name = name
        self._premises: List[str] = []
        self._goal = ""
        self._points: List[str] = []
        self._lines: List[str] = []
        self._steps: List[Dict[str, Any]] = []
        self._next_line: Optional[int] = None  # computed from premises
        self._canvas: Optional[Dict] = None
        self._metadata: Optional[Dict] = None
        self._difficulty = 3
        self._hints: List[str] = []

    # ── Premises ──────────────────────────────────────────────────────

    def premise(self, text: str) -> "EuclidProofBuilder":
        """Add a premise (Given line). Premises are numbered 1, 2, ...."""
        self._premises.append(text)
        return self

    def premises(self, *texts: str) -> "EuclidProofBuilder":
        """Add multiple premises at once."""
        for t in texts:
            self._premises.append(t)
        return self

    # ── Goal ──────────────────────────────────────────────────────────

    def goal(self, text: str) -> "EuclidProofBuilder":
        """Set the proof goal (comma-separated literals)."""
        self._goal = text
        return self

    # ── Declarations ──────────────────────────────────────────────────

    def declare_points(self, *names: str) -> "EuclidProofBuilder":
        """Declare point variables."""
        self._points.extend(names)
        return self

    def declare_lines(self, *names: str) -> "EuclidProofBuilder":
        """Declare line variables."""
        self._lines.extend(names)
        return self

    # ── Canvas & metadata ─────────────────────────────────────────────

    def canvas(self, canvas_data: Dict) -> "EuclidProofBuilder":
        """Set custom canvas data."""
        self._canvas = canvas_data
        return self

    def difficulty(self, d: int) -> "EuclidProofBuilder":
        """Set difficulty level (1-5)."""
        self._difficulty = d
        return self

    def hint(self, text: str) -> "EuclidProofBuilder":
        """Add a hint."""
        self._hints.append(text)
        return self

    # ── Step helpers ──────────────────────────────────────────────────

    def _ensure_line_num(self) -> None:
        """Compute the next line number if not set."""
        if self._next_line is None:
            self._next_line = len(self._premises) + 1

    def _add_step(self, text: str, justification: str,
                  deps: List[int], depth: int = 0) -> int:
        """Add a proof step and return its line number."""
        self._ensure_line_num()
        line_num = self._next_line
        self._next_line += 1
        self._steps.append({
            "lineNumber": line_num,
            "text": text,
            "justification": justification,
            "dependencies": deps,
            "depth": depth,
            "status": "?",
        })
        return line_num

    @property
    def line(self) -> int:
        """Return the line number that the NEXT step will get."""
        self._ensure_line_num()
        return self._next_line

    @property
    def last(self) -> int:
        """Return the line number of the last added step."""
        if not self._steps:
            return len(self._premises)
        return self._steps[-1]["lineNumber"]

    # ── Construction steps ────────────────────────────────────────────

    def let_line(self, text: str, refs: List[int],
                 depth: int = 0) -> int:
        """Add a let-line construction step. Returns line number."""
        return self._add_step(text, "let-line", refs, depth)

    def let_circle(self, text: str, refs: List[int],
                   depth: int = 0) -> int:
        """Add a let-circle construction step. Returns line number."""
        return self._add_step(text, "let-circle", refs, depth)

    def let_point_on_line(self, text: str, refs: List[int],
                          depth: int = 0) -> int:
        """Add a let-point-on-line construction step."""
        return self._add_step(text, "let-point-on-line", refs, depth)

    def let_point_on_line_between(self, text: str, refs: List[int],
                                  depth: int = 0) -> int:
        """Add a let-point-on-line-between construction step."""
        return self._add_step(text, "let-point-on-line-between", refs, depth)

    def let_point_on_line_extend(self, text: str, refs: List[int],
                                 depth: int = 0) -> int:
        """Add a let-point-on-line-extend construction step."""
        return self._add_step(text, "let-point-on-line-extend", refs, depth)

    def let_point_same_side(self, text: str, refs: List[int],
                            depth: int = 0) -> int:
        """Add a let-point-same-side construction step."""
        return self._add_step(text, "let-point-same-side", refs, depth)

    def let_point_opposite_side(self, text: str, refs: List[int],
                                depth: int = 0) -> int:
        """Add a let-point-opposite-side construction step."""
        return self._add_step(text, "let-point-opposite-side", refs, depth)

    def let_intersection_line_line(self, text: str, refs: List[int],
                                   depth: int = 0) -> int:
        """Add a let-intersection-line-line construction step."""
        return self._add_step(text, "let-intersection-line-line", refs, depth)

    def let_intersection_line_circle_between(self, text: str, refs: List[int],
                                              depth: int = 0) -> int:
        """Add a let-intersection-line-circle-between construction step."""
        return self._add_step(text, "let-intersection-line-circle-between",
                              refs, depth)

    def let_intersection_line_circle_extend(self, text: str, refs: List[int],
                                             depth: int = 0) -> int:
        """Add a let-intersection-line-circle-extend construction step."""
        return self._add_step(text, "let-intersection-line-circle-extend",
                              refs, depth)

    def let_intersection_line_circle_other(self, text: str, refs: List[int],
                                            depth: int = 0) -> int:
        """Add a let-intersection-line-circle-other construction step."""
        return self._add_step(text, "let-intersection-line-circle-other",
                              refs, depth)

    def let_intersection_circle_circle_one(self, text: str, refs: List[int],
                                            depth: int = 0) -> int:
        """Add a let-intersection-circle-circle-one construction step."""
        return self._add_step(text, "let-intersection-circle-circle-one",
                              refs, depth)

    def let_intersection_circle_circle_two(self, text: str, refs: List[int],
                                            depth: int = 0) -> int:
        """Add a let-intersection-circle-circle-two construction step."""
        return self._add_step(text, "let-intersection-circle-circle-two",
                              refs, depth)

    def let_intersection_circle_circle_same_side(
            self, text: str, refs: List[int], depth: int = 0) -> int:
        """Add a let-intersection-circle-circle-same-side step."""
        return self._add_step(
            text, "let-intersection-circle-circle-same-side", refs, depth)

    def let_intersection_circle_circle_opposite_side(
            self, text: str, refs: List[int], depth: int = 0) -> int:
        """Add a let-intersection-circle-circle-opposite-side step."""
        return self._add_step(
            text, "let-intersection-circle-circle-opposite-side", refs, depth)

    def construction(self, text: str, rule_name: str, refs: List[int],
                     depth: int = 0) -> int:
        """Add a generic construction step with any rule name."""
        return self._add_step(text, rule_name, refs, depth)

    # ── Axiom steps (diagrammatic, metric, transfer) ──────────────────

    def axiom(self, text: str, justification: str, refs: List[int],
              depth: int = 0) -> int:
        """Add a named axiom step (e.g. 'Generality 3', 'CN1 — Transitivity')."""
        return self._add_step(text, justification, refs, depth)

    # Convenience aliases for common axiom types
    def generality(self, n: str, text: str, refs: List[int],
                   depth: int = 0) -> int:
        return self._add_step(text, f"Generality {n}", refs, depth)

    def betweenness(self, n: str, text: str, refs: List[int],
                    depth: int = 0) -> int:
        return self._add_step(text, f"Betweenness {n}", refs, depth)

    def same_side(self, n: str, text: str, refs: List[int],
                  depth: int = 0) -> int:
        return self._add_step(text, f"Same-side {n}", refs, depth)

    def pasch(self, n: str, text: str, refs: List[int],
              depth: int = 0) -> int:
        return self._add_step(text, f"Pasch {n}", refs, depth)

    def circle_axiom(self, n: str, text: str, refs: List[int],
                     depth: int = 0) -> int:
        return self._add_step(text, f"Circle {n}", refs, depth)

    def intersection_axiom(self, n: str, text: str, refs: List[int],
                           depth: int = 0) -> int:
        return self._add_step(text, f"Intersection {n}", refs, depth)

    def cn1(self, text: str, refs: List[int], depth: int = 0) -> int:
        """CN1 — Transitivity."""
        return self._add_step(text, "CN1 — Transitivity", refs, depth)

    def cn2(self, text: str, refs: List[int], depth: int = 0) -> int:
        """CN2 — Addition."""
        return self._add_step(text, "CN2 — Addition", refs, depth)

    def cn3(self, text: str, refs: List[int], depth: int = 0) -> int:
        """CN3 — Subtraction."""
        return self._add_step(text, "CN3 — Subtraction", refs, depth)

    def cn4(self, text: str, refs: List[int], depth: int = 0) -> int:
        """CN4 — Reflexivity."""
        return self._add_step(text, "CN4 — Reflexivity", refs, depth)

    def cn5(self, text: str, refs: List[int], depth: int = 0) -> int:
        """CN5 — Whole > Part."""
        return self._add_step(text, "CN5 — Whole > Part", refs, depth)

    def m1(self, text: str, refs: List[int], depth: int = 0) -> int:
        """M1 — Zero segment."""
        return self._add_step(text, "M1 — Zero segment", refs, depth)

    def m3(self, text: str, refs: List[int], depth: int = 0) -> int:
        """M3 — Symmetry."""
        return self._add_step(text, "M3 — Symmetry", refs, depth)

    def m4(self, text: str, refs: List[int], depth: int = 0) -> int:
        """M4 — Angle symmetry."""
        return self._add_step(text, "M4 — Angle symmetry", refs, depth)

    def m8(self, text: str, refs: List[int], depth: int = 0) -> int:
        """M8 — Area symmetry."""
        return self._add_step(text, "M8 — Area symmetry", refs, depth)

    def segment_transfer(self, n: str, text: str, refs: List[int],
                         depth: int = 0) -> int:
        return self._add_step(text, f"Segment transfer {n}", refs, depth)

    def angle_transfer(self, n: str, text: str, refs: List[int],
                       depth: int = 0) -> int:
        return self._add_step(text, f"Angle transfer {n}", refs, depth)

    def area_transfer(self, n: str, text: str, refs: List[int],
                      depth: int = 0) -> int:
        return self._add_step(text, f"Area transfer {n}", refs, depth)

    def trichotomy(self, text: str, refs: List[int],
                   depth: int = 0) -> int:
        """< trichotomy."""
        return self._add_step(text, "< trichotomy", refs, depth)

    # ── Superposition ─────────────────────────────────────────────────

    def sas(self, text: str, refs: List[int], depth: int = 0) -> int:
        """SAS superposition step."""
        return self._add_step(text, "SAS", refs, depth)

    def sss(self, text: str, refs: List[int], depth: int = 0) -> int:
        """SSS superposition step."""
        return self._add_step(text, "SSS", refs, depth)

    # ── Theorem application ───────────────────────────────────────────

    def theorem(self, text: str, prop_name: str, refs: List[int],
                depth: int = 0) -> int:
        """Apply a theorem (e.g. 'Prop.I.3'). Returns line number."""
        return self._add_step(text, prop_name, refs, depth)

    # ── Subproof steps (contradiction) ────────────────────────────────

    def assume(self, text: str, depth: int = 1) -> int:
        """Add an Assume step (opens a subproof). Returns line number."""
        return self._add_step(text, "Assume", [], depth)

    def contradiction(self, refs: List[int], depth: int = 1) -> int:
        """Add a ⊥-intro step. Returns line number."""
        return self._add_step("⊥", "⊥-intro", refs, depth)

    def bot_elim(self, text: str, assume_ref: int,
                 depth: int = 0) -> int:
        """Add a ⊥-elim step. Returns line number."""
        return self._add_step(text, "⊥-elim", [assume_ref], depth)

    # ── Case split ────────────────────────────────────────────────────

    def cases(self, text: str, assume_refs: List[int],
              depth: int = 0) -> int:
        """Add a Cases step. assume_refs = [assume1_lid, assume2_lid]."""
        return self._add_step(text, "Cases", assume_refs, depth)

    # ── Build ─────────────────────────────────────────────────────────

    def build(self) -> Dict[str, Any]:
        """Build and return the complete .euclid JSON document."""
        # Determine prop number for metadata
        prop_num = _extract_prop_number(self._name)

        # Canvas
        canvas = self._canvas or {
            "points": [],
            "segments": [],
            "rays": [],
            "circles": [],
            "angleMarks": [],
            "equalityGroups": [],
        }

        # Metadata
        metadata = self._metadata or {
            "difficulty": self._difficulty,
            "hints": self._hints or [],
        }

        doc = {
            "format": "euclid-proof",
            "version": "1.0.0",
            "program": "Euclid Elements Simulator (Python)",
            "metadata": metadata,
            "canvas": canvas,
            "exportedAt": datetime.datetime.now(
                datetime.timezone.utc).strftime("%Y-%m-%dT%H:%M:%SZ"),
            "proof": {
                "name": self._name,
                "premises": list(self._premises),
                "goal": self._goal,
                "declarations": {
                    "points": list(self._points),
                    "lines": list(self._lines),
                },
                "steps": list(self._steps),
            },
        }
        return doc

    def build_json(self, indent: int = 2) -> str:
        """Build and return the JSON string."""
        return json.dumps(self.build(), indent=indent, ensure_ascii=False)

    def write(self, path: str) -> None:
        """Build and write to a .euclid file."""
        p = Path(path)
        p.parent.mkdir(parents=True, exist_ok=True)
        with open(p, 'w', encoding='utf-8') as f:
            json.dump(self.build(), f, indent=2, ensure_ascii=False)

    def verify(self) -> "PanelCheckResult":
        """Build and verify using the real verifier. Returns PanelCheckResult."""
        from .unified_checker import verify_e_proof_json
        return verify_e_proof_json(self.build())

    # ── Load canvas from existing file ────────────────────────────────

    def load_canvas_from(self, path: str) -> "EuclidProofBuilder":
        """Load canvas data from an existing .euclid file."""
        try:
            with open(path, 'r', encoding='utf-8') as f:
                data = json.load(f)
            if "canvas" in data:
                self._canvas = data["canvas"]
        except (json.JSONDecodeError, OSError, FileNotFoundError):
            pass
        return self


def _extract_prop_number(name: str) -> Optional[int]:
    """Extract proposition number from 'Prop.I.16' style name."""
    import re
    m = re.search(r'\.(\d+)$', name)
    return int(m.group(1)) if m else None


# ═══════════════════════════════════════════════════════════════════════
# Helper: load an existing solved proof for reference
# ═══════════════════════════════════════════════════════════════════════

def load_existing_proof(prop_num: int) -> Optional[Dict]:
    """Load an existing .euclid proof file if it exists."""
    for prefix in ("solved_proofs", "unsolved_proofs"):
        path = Path(prefix) / f"Proposition I.{prop_num}.euclid"
        if path.exists():
            try:
                with open(path, 'r', encoding='utf-8') as f:
                    return json.load(f)
            except (json.JSONDecodeError, OSError):
                pass
    return None
