"""Identify correct specific axiom for generic lines in answer key."""
import json
import sys
sys.path.insert(0, ".")

from verifier.unified_checker import verify_e_proof_json
from verifier.e_axiom_match import list_axiom_names

ALL_AXIOMS = list_axiom_names()
CN_NAMES = ["CN1", "CN2", "CN3", "CN4", "CN5",
            "CN1 \u2014 Transitivity", "CN3 \u2014 Subtraction"]

path = "answer_key_book_1.json"
with open(path, "r", encoding="utf-8") as f:
    d = json.load(f)

GENERIC = {"Diagrammatic", "Metric", "Transfer"}

for pname in ["Prop.I.3", "Prop.I.4", "Prop.I.5", "Prop.I.8"]:
    vp = d["propositions"][pname]["verified_proof"]
    lines_data = vp["lines"]
    generic_lines = [(i, l) for i, l in enumerate(lines_data)
                     if l["justification"] in GENERIC]
    if not generic_lines:
        continue
    print(f"\n=== {pname} ===")
    for idx, line in generic_lines:
        lid = line["id"]
        stmt = line["statement"]
        refs = line.get("refs", [])
        print(f"\n  Line {lid}: {stmt} (refs={refs})")
        found = []
        for ax_name in ALL_AXIOMS + CN_NAMES:
            test_lines = []
            for l in lines_data:
                if l["id"] == lid:
                    test_lines.append({
                        "id": l["id"], "depth": l["depth"],
                        "statement": l["statement"],
                        "justification": ax_name,
                        "refs": l.get("refs", [])
                    })
                else:
                    test_lines.append(l)
            pj = {
                "name": f"test-{pname}",
                "declarations": {"points": [], "lines": []},
                "premises": vp["premises"],
                "goal": vp["goal"],
                "lines": test_lines,
            }
            r = verify_e_proof_json(pj)
            lr = r.line_results.get(lid)
            if lr and lr.valid:
                found.append(ax_name)
        if found:
            print(f"    MATCHES: {found}")
        else:
            print(f"    NO MATCH FOUND")
