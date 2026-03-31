"""Check all solved proofs with the verifier."""
import json, glob, os, sys
sys.path.insert(0, os.path.join(os.path.dirname(__file__), ".."))
from verifier.unified_checker import verify_e_proof_json

files = sorted(
    glob.glob("solved_proofs/Proposition I.*.euclid"),
    key=lambda f: int(os.path.basename(f).split("I.")[1].split(".euclid")[0]),
)

total_pass = 0
for f in files:
    pf = json.load(open(f, encoding="utf-8"))
    r = verify_e_proof_json(pf)
    bad = [k for k, v in r.line_results.items() if not v.valid]
    name = os.path.basename(f).replace(".euclid", "")
    if r.accepted:
        total_pass += 1
        print(f"{name}: PASS")
    else:
        print(f"{name}: FAIL ({len(bad)} bad lines)")
        for k in bad:
            print(f"  L{k}: {r.line_results[k].errors}")
        for e in r.errors:
            print(f"  GOAL: {e}")

print(f"\n{total_pass}/{len(files)} passing")
