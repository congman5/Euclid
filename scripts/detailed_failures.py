"""Detailed per-line failure analysis for each failing proof."""
import json, sys, io
sys.stdout = io.TextIOWrapper(sys.stdout.buffer, encoding='utf-8')
from verifier.unified_checker import verify_e_proof_json

d = json.load(open('answer_key_book_1.json', 'r', encoding='utf-8'))

for prop in ["Prop.I.9", "Prop.I.10", "Prop.I.11", "Prop.I.13", "Prop.I.15", "Prop.I.16", "Prop.I.6", "Prop.I.7"]:
    p = d['propositions'][prop].get('verified_proof')
    if p is None:
        continue
    r = verify_e_proof_json(p)
    if r.accepted:
        print(f"\n{prop}: PASSES ✓")
        continue
    print(f"\n{'='*60}")
    print(f"{prop}: FAILS")
    for lid, lr in r.line_results.items():
        if not lr.valid:
            print(f"  Line {lid}: {lr.errors}")
    if r.errors:
        print(f"  Goal errors: {r.errors}")
