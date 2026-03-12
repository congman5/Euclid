"""Test original I.6/I.7/I.9/I.10 proofs with the DA4b/c/d fix."""
import json, sys, io
sys.stdout = io.TextIOWrapper(sys.stdout.buffer, encoding='utf-8')

from verifier.unified_checker import verify_e_proof_json

with open("answer_key_book_1.json", "r", encoding="utf-8") as f:
    d = json.load(f)

for name in ["Prop.I.3", "Prop.I.6", "Prop.I.7", "Prop.I.9", "Prop.I.10"]:
    p = d["propositions"][name]["verified_proof"]
    r = verify_e_proof_json(p)
    status = "PASS" if r.accepted else "FAIL"
    print(f"\n{name}: {status}")
    if not r.accepted:
        for k, v in r.line_results.items():
            if not v.valid:
                print(f"  line {k}: {v.errors}")
        for e in r.errors:
            print(f"  GOAL: {e}")
