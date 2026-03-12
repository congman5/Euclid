"""Find all proofs using Indirect justification."""
import json, sys, io
sys.stdout = io.TextIOWrapper(sys.stdout.buffer, encoding='utf-8')

d = json.load(open('answer_key_book_1.json', 'r', encoding='utf-8'))

for name, entry in sorted(d['propositions'].items()):
    p = entry.get('verified_proof')
    if p is None:
        continue
    for line in p.get('lines', []):
        just = line.get('justification', '')
        if just.startswith('Indirect'):
            print(f"{name} line {line['id']}: [{just}] -> {line['statement'][:80]}")
