"""Dump the full proof and known facts for each failing proposition."""
import json, sys, io
sys.stdout = io.TextIOWrapper(sys.stdout.buffer, encoding='utf-8')

from verifier.unified_checker import verify_e_proof_json
from verifier.e_library import E_THEOREM_LIBRARY

with open("answer_key_book_1.json", "r", encoding="utf-8") as f:
    d = json.load(f)

for name in ["Prop.I.3", "Prop.I.6", "Prop.I.7", "Prop.I.9", "Prop.I.10"]:
    p = d["propositions"][name]["verified_proof"]
    print(f"\n{'='*70}")
    print(f"  {name}")
    print(f"{'='*70}")
    print(f"Premises: {p['premises']}")
    print(f"Goal: {p['goal']}")
    print()
    for line in p["lines"]:
        lid = line['id']
        stmt = line['statement']
        just = line['justification']
        refs = line.get('refs', [])
        depth = line.get('depth', 0)
        print(f"  {lid:>2} (d={depth}): {stmt!r:50s}  [{just}]  refs={refs}")

    r = verify_e_proof_json(p)
    print(f"\n  Result: {'PASS' if r.accepted else 'FAIL'}")
    if not r.accepted:
        print(f"  First failing line details:")
        for k, v in r.line_results.items():
            if not v.valid:
                print(f"    line {k}: {v.errors}")
                break  # just first failure
        for e in r.errors:
            print(f"  {e}")
