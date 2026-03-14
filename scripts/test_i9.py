"""Re-test I.9 with the metric expansion fix in place."""
import json, sys, io
sys.stdout = io.TextIOWrapper(sys.stdout.buffer, encoding='utf-8')
from verifier.unified_checker import verify_e_proof_json

d = json.load(open('answer_key_book_1.json', 'r', encoding='utf-8'))
p = d['propositions']['Prop.I.9']['verified_proof']
r = verify_e_proof_json(p)

print(f"Accepted: {r.accepted}")
for lid, lr in r.line_results.items():
    if not lr.valid:
        line = next(l for l in p['lines'] if l['id'] == lid)
        print(f"  ✗ Line {lid} [{line['justification']}]: {line['statement'][:80]}")
        for e in lr.errors:
            print(f"      {e}")
