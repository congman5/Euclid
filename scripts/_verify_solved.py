"""Verify all .euclid files in solved_proofs/ against the unified checker."""
from __future__ import annotations
import json, os, sys, io

sys.stdout = io.TextIOWrapper(sys.stdout.buffer, encoding='utf-8', errors='replace')
sys.path.insert(0, os.path.dirname(os.path.dirname(os.path.abspath(__file__))))

from verifier.unified_checker import verify_e_proof_json

solved_dir = os.path.join(os.path.dirname(os.path.dirname(os.path.abspath(__file__))),
                          "solved_proofs")

props = list(range(1, 16))
if len(sys.argv) > 1:
    props = [int(x) for x in sys.argv[1:]]

ok_count = 0
for i in props:
    fname = os.path.join(solved_dir, f"Proposition I.{i}.euclid")
    if not os.path.exists(fname):
        print(f"I.{i:2d}: MISSING")
        continue
    with open(fname, "r", encoding="utf-8") as f:
        data = json.load(f)
    r = verify_e_proof_json(data)
    total = len(r.line_results)
    fails = sum(1 for lr in r.line_results.values() if not lr.valid)
    status = "OK" if r.accepted else "FAIL"
    print(f"I.{i:2d}: {status:4s} f={fails}/{total}")
    if not r.accepted:
        for lid, lr in sorted(r.line_results.items()):
            if not lr.valid:
                for e in lr.errors:
                    print(f"      L{lid}: {e[:120]}")
    else:
        ok_count += 1

print(f"\n=== {ok_count}/{len(props)} verified ===")
