"""Debug deps for a single proposition."""
import sys
sys.stdout.reconfigure(encoding='utf-8')
from verifier.lean_translator import translate_lean_file
from verifier.lean_parser import parse_lean_file
from verifier.proof_synthesizer import synthesize_proof

n = int(sys.argv[1]) if len(sys.argv) > 1 else 17
f = f'lean_reference/Prop{n}.lean'
tr = translate_lean_file(f)
lps = parse_lean_file(f)
sr = synthesize_proof(tr, lps[0] if lps else None)
prem = sr.euclid_json['proof']['premises']
for i, p in enumerate(prem, 1):
    print(f"P{i}: {p}")
print()
for s in sr.euclid_json['proof']['steps']:
    ln = s['lineNumber']
    deps = s['dependencies']
    just = s['justification']
    text = s['text'][:70]
    print(f"L{ln:2d}: deps={deps} [{just}] {text}")
