"""Quick axiom finder - tests one prop at a time with early exit."""
import json, sys
sys.path.insert(0, ".")
from verifier.unified_checker import verify_e_proof_json
from verifier.e_axiom_match import list_axiom_names

ALL_NAMES = list_axiom_names() + ["CN1", "CN2", "CN3", "CN4", "CN5",
    "CN1 \u2014 Transitivity", "CN3 \u2014 Subtraction",
    "SAS", "SSS", "AAS", "Angle transfer 1", "Angle transfer 2",
    "Angle transfer 3", "Angle transfer 4", "Angle transfer 5",
    "Angle transfer 6", "Segment transfer 3a", "Segment transfer 3b",
    "Segment transfer 5", "Segment transfer 6", "Segment transfer 7"]

GENERIC = {"Diagrammatic", "Metric", "Transfer"}
d = json.load(open("answer_key_book_1.json", "r", encoding="utf-8"))
pname = sys.argv[1] if len(sys.argv) > 1 else "Prop.I.4"
vp = d["propositions"][pname]["verified_proof"]
lines_data = vp["lines"]

for line in lines_data:
    if line["justification"] not in GENERIC:
        continue
    lid = line["id"]
    print(f"Line {lid}: {line['statement'][:50]} refs={line.get('refs',[])}")
    for ax in ALL_NAMES:
        tl = []
        for l in lines_data:
            if l["id"] == lid:
                tl.append(dict(l, justification=ax))
            else:
                tl.append(l)
        pj = {"name": "t", "declarations": {"points": [], "lines": []},
              "premises": vp["premises"], "goal": vp["goal"], "lines": tl}
        r = verify_e_proof_json(pj)
        lr = r.line_results.get(lid)
        if lr and lr.valid:
            print(f"  -> {ax}")
            break
    else:
        print("  -> NO MATCH")
