"""Print synthesized steps for a proposition."""
import sys
sys.stdout.reconfigure(encoding='utf-8')
from verifier.lean_translator import translate_lean_file
from verifier.lean_parser import parse_lean_file
from verifier.proof_synthesizer import synthesize_proof

prop_num = int(sys.argv[1]) if len(sys.argv) > 1 else 16
f = f'lean_reference/Prop{prop_num}.lean'
tr = translate_lean_file(f)
lps = parse_lean_file(f)
lp = lps[0] if lps else None
sr = synthesize_proof(tr, lp)

print(f"Prop I.{prop_num}: {sr.step_count} steps, success={sr.success}")
print(f"Premises: {sr.euclid_json['proof']['premises']}")
print(f"Declarations: {sr.euclid_json['proof']['declarations']}")
print()
for s in sr.euclid_json['proof']['steps']:
    ln = s['lineNumber']
    just = s['justification']
    deps = s['dependencies']
    text = s['text']
    print(f"L{ln:3d}: {just:40s} deps={str(deps):20s}  {text}")
print()
for w in sr.warnings:
    print(f"WARN: {w}")
for e in sr.errors:
    print(f"ERR: {e}")
