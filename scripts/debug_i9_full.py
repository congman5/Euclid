"""Check exact line-by-line results for I.9."""
import json, sys, io
sys.stdout = io.TextIOWrapper(sys.stdout.buffer, encoding='utf-8')
from verifier.unified_checker import verify_e_proof_json

d = json.load(open('answer_key_book_1.json', 'r', encoding='utf-8'))
p = d['propositions']['Prop.I.9']['verified_proof']
r = verify_e_proof_json(p)

print(f"Accepted: {r.accepted}")
for lid, lr in r.line_results.items():
    status = "✓" if lr.valid else "✗"
    line = next(l for l in p['lines'] if l['id'] == lid)
    print(f"  {status} Line {lid} [{line['justification']}]: {line['statement'][:60]}")
    if not lr.valid:
        for e in lr.errors:
            print(f"      ERROR: {e}")
