import json, sys, io
sys.stdout = io.TextIOWrapper(sys.stdout.buffer, encoding='utf-8')
from verifier.unified_checker import verify_e_proof_json

with open("answer_key_book_1.json", "r", encoding="utf-8") as f:
    d = json.load(f)

for name in ["Prop.I.1","Prop.I.2","Prop.I.3","Prop.I.4","Prop.I.5",
             "Prop.I.6","Prop.I.7","Prop.I.8","Prop.I.9","Prop.I.10"]:
    p = d["propositions"][name]["verified_proof"]
    r = verify_e_proof_json(p)
    status = "PASS" if r.accepted else "FAIL"
    print(f"\n{'='*60}")
    print(f"{name}: {status}")
    if not r.accepted:
        for k, v in r.line_results.items():
            if not v.valid:
                print(f"  line {k}: {v.errors}")
        for e in r.errors:
            print(f"  GOAL: {e}")
