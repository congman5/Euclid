"""Debug a single proposition synthesis — show steps and warnings."""
import sys
sys.stdout.reconfigure(encoding='utf-8')
from verifier.lean_translator import translate_lean_file
from verifier.lean_parser import parse_lean_file
from verifier.proof_synthesizer import synthesize_proof

n = int(sys.argv[1]) if len(sys.argv) > 1 else 17
f = f'lean_reference/Prop{n}.lean'
tr = translate_lean_file(f)
lps = parse_lean_file(f)
lp = lps[0] if lps else None
sr = synthesize_proof(tr, lp)

print(f"=== I.{n} ===")
print(f"Success: {sr.success}")
print(f"Errors: {sr.errors}")
print(f"Warnings ({len(sr.warnings)}):")
for w in sr.warnings:
    print(f"  {w}")
print()
if sr.euclid_json:
    steps = sr.euclid_json['proof']['steps']
    print(f"Steps ({len(steps)}):")
    for s in steps:
        print(f"  L{s['lineNumber']:2d}: [{s['justification']:<35s}] {s['text'][:80]}")
