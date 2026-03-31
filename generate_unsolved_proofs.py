#!/usr/bin/env python3
"""Generate unsolved_proofs/ .euclid files for all 48 Book I propositions.

Each file contains:
  - Starter canvas reflecting the assumed/given shapes
  - Correct premises from the System E library
  - Correct conclusion/goal from the System E library
  - Empty proof steps (for the user to fill in)
"""
import json
import os
import sys

# Ensure the project root is on the path
sys.path.insert(0, os.path.dirname(__file__))

from euclid_py.engine.proposition_data import PROPOSITIONS
from verifier.e_library import E_THEOREM_LIBRARY


def make_euclid_file(prop):
    """Build a .euclid JSON dict for an unsolved proposition."""
    e_name = prop.e_library_name  # e.g. "Prop.I.1"
    e_thm = E_THEOREM_LIBRARY.get(e_name)

    # --- Canvas from given_objects ---
    canvas = {
        "points": [],
        "segments": [],
        "rays": [],
        "circles": [],
        "angleMarks": [],
        "equalityGroups": [],
    }
    pt_labels = []
    if prop.given_objects:
        for pt in prop.given_objects.points:
            canvas["points"].append({
                "label": pt["label"],
                "x": pt["x"],
                "y": pt["y"],
            })
            pt_labels.append(pt["label"])
        for seg in prop.given_objects.segments:
            canvas["segments"].append({
                "from": seg["from"],
                "to": seg["to"],
                "color": "#2d70b3",
            })
        for circ in prop.given_objects.circles:
            canvas["circles"].append({
                "center": circ["center"],
                "radius": circ["radius"],
                "radius_point": circ.get("radius_point", ""),
                "color": "#2d70b3",
            })
        for am in prop.given_objects.angle_marks:
            canvas["angleMarks"].append({
                "from": am["from"],
                "vertex": am["vertex"],
                "to": am["to"],
                "isRight": am.get("is_right", False),
            })

    # --- Premises and goal from E library ---
    premises = []
    goal = ""
    if e_thm:
        premises = [str(h) for h in e_thm.sequent.hypotheses]
        if e_thm.sequent.conclusions:
            goal = ", ".join(str(c) for c in e_thm.sequent.conclusions)
    if not goal and prop.conclusion_predicate:
        goal = prop.conclusion_predicate

    # --- Declarations ---
    declarations = {"points": pt_labels, "lines": []}

    # --- Build the full .euclid structure ---
    doc = {
        "format": "euclid-proof",
        "version": "1.0.0",
        "program": "Euclid Elements Simulator (Python)",
        "metadata": {
            "proposition": prop.name,
            "title": prop.title,
            "statement": prop.statement,
        },
        "canvas": canvas,
        "proof": {
            "name": e_name or prop.name,
            "premises": premises,
            "goal": goal,
            "declarations": declarations,
            "steps": [],
        },
    }
    return doc


def main():
    out_dir = os.path.join(os.path.dirname(__file__), "unsolved_proofs")
    os.makedirs(out_dir, exist_ok=True)

    for prop in PROPOSITIONS:
        if prop.source != "euclid":
            continue
        doc = make_euclid_file(prop)
        filename = f"{prop.name}.euclid"
        path = os.path.join(out_dir, filename)
        with open(path, "w", encoding="utf-8") as f:
            json.dump(doc, f, indent=2, ensure_ascii=False)
        print(f"  wrote {filename}")

    print(f"\nGenerated {len(PROPOSITIONS)} files in {out_dir}")


if __name__ == "__main__":
    main()
