"""Debug I.17 line 12 CN5 verification — instrument unified_checker."""
import sys, json
sys.stdout.reconfigure(encoding='utf-8')

# Monkey-patch MetricEngine.is_consequence to trace calls
from verifier import e_metric
_orig_is_consequence = e_metric.MetricEngine.is_consequence

def _traced_is_consequence(self, known, target):
    result = _orig_is_consequence(self, known, target)
    # Only print for our target
    s = str(target)
    if 'abc' in s and 'bca' in s:
        print(f"[TRACE ME] target={target}")
        print(f"  known_count={len(known)}")
        print(f"  result={result}")
        # Check if known has the key metric facts
        for k in sorted(str(x) for x in known):
            if 'cba' in k or 'dca' in k or 'bca' in k or 'acd' in k:
                print(f"  metric_fact: {k}")
    return result

e_metric.MetricEngine.is_consequence = _traced_is_consequence

from verifier.unified_checker import verify_e_proof_json

with open('solved_proofs/Proposition I.17.euclid', 'r', encoding='utf-8') as f:
    pj = json.load(f)

vr = verify_e_proof_json(pj)
print(f"\naccepted={vr.accepted}")
for k, v in sorted(vr.line_results.items()):
    if not v.valid:
        print(f"line {k}: {v.errors[:1]}")

