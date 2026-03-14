"""Dump JSON proofs for failing propositions."""
import json, sys, io
sys.stdout = io.TextIOWrapper(sys.stdout.buffer, encoding='utf-8')

d = json.load(open('answer_key_book_1.json', 'r', encoding='utf-8'))

for prop in ["Prop.I.6", "Prop.I.7", "Prop.I.9", "Prop.I.10", 
             "Prop.I.11", "Prop.I.13", "Prop.I.15", "Prop.I.16"]:
    p = d['propositions'][prop].get('verified_proof')
    if p is None:
        print(f"\n{prop}: NO PROOF")
        continue
    print(f"\n{'='*50}")
    print(f"{prop} ({len(p['lines'])} lines)")
    print(f"  premises: {p['premises']}")
    print(f"  goal: {p['goal']}")
    for l in p['lines']:
        depth = l.get('depth', 0)
        indent = '  ' * depth
        print(f"  {indent}{l['id']}. [{l['justification']}] refs={l['refs']}")
        print(f"  {indent}   -> {l['statement']}")
