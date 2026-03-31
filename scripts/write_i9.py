"""Convert PB proof to .euclid format and write Proposition I.9."""
from __future__ import annotations
import json, sys, os
sys.path.insert(0, os.path.join(os.path.dirname(__file__), ".."))
from scripts.test_i9_arm_v4 import build_i9_arm

def main():
    pb_proof = build_i9_arm()
    pb_lines = pb_proof["lines"]

    # Convert PB format to .euclid format
    steps = []
    for line in pb_lines:
        lid = line["id"]
        stmt = line["statement"]
        just = line["justification"]
        refs = line["refs"]
        depth = line.get("depth", 0)
        # Skip given lines (premises are in the premises array)
        if just == "Given":
            continue
        steps.append({
            "lineNumber": lid,
            "text": stmt,
            "justification": just,
            "dependencies": refs,
            "depth": depth,
            "status": "?"
        })

    euclid = {
        "format": "euclid-proof",
        "version": "1.0.0",
        "program": "Euclid Elements Simulator (Python)",
        "metadata": {},
        "canvas": {
            "points": [
                {"label": "A", "x": 100, "y": 250},
                {"label": "B", "x": 550, "y": 120},
                {"label": "C", "x": 550, "y": 380},
                {"label": "D", "x": 340.18, "y": 180.62},
                {"label": "F", "x": 340.18, "y": 319.38},
                {"label": "E", "x": 220.0, "y": 250.0}
            ],
            "segments": [
                {"from": "A", "to": "B", "color": "#2d70b3"},
                {"from": "A", "to": "C", "color": "#2d70b3"},
                {"from": "A", "to": "D", "color": "#2e8b57"},
                {"from": "A", "to": "F", "color": "#2e8b57"},
                {"from": "D", "to": "F", "color": "#333333"},
                {"from": "D", "to": "E", "color": "#cc3333"},
                {"from": "F", "to": "E", "color": "#cc3333"}
            ],
            "rays": [
                {"from": "A", "through": "E", "color": "#e67e22"}
            ],
            "circles": [
                {"center": "A", "radius": 250, "radius_point": "D", "color": "#2e8b57"}
            ],
            "angleMarks": [
                {"from": "B", "vertex": "A", "to": "E", "is_right": False},
                {"from": "E", "vertex": "A", "to": "C", "is_right": False}
            ],
            "equalityGroups": [
                [1, [["A", "D"], ["A", "F"]]],
                [2, [["D", "E"], ["F", "E"]]]
            ]
        },
        "exportedAt": "2026-03-22T23:56:00Z",
        "proof": {
            "name": "Prop.I.9",
            "premises": pb_proof["premises"],
            "goal": pb_proof["goal"],
            "declarations": {
                "points": ["a", "b", "c"],
                "lines": ["M", "N"]
            },
            "steps": steps
        }
    }

    outpath = os.path.join(os.path.dirname(__file__), "..",
                           "solved_proofs", "Proposition I.9.euclid")
    with open(outpath, "w", encoding="utf-8") as f:
        json.dump(euclid, f, indent=2, ensure_ascii=False)
    print(f"Written {len(steps)} steps to {outpath}")

if __name__ == "__main__":
    main()
