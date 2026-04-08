"""Dump Prop16 synthesis only (no verification)."""
import json
from verifier.lean_translator import translate_lean_file
from verifier.lean_parser import parse_lean_file
from verifier.proof_synthesizer import ProofSynthesizer

tr = translate_lean_file('lean_reference/Prop16.lean')
lps = parse_lean_file('lean_reference/Prop16.lean')
sr = ProofSynthesizer(tr, lps[0]).synthesize()
steps = sr.euclid_json['proof']['steps']
premises = sr.euclid_json['proof']['premises']

print("=== PREMISES ===")
for i, p in enumerate(premises):
    print(f"  P{i}: {p}")

print("\n=== STEPS ===")
for s in steps:
    ln = s['lineNumber']
    txt = s['text']
    j = s['justification']
    d = s['dependencies']
    print(f"  L{ln:2d}: {txt}")
    print(f"       just={j}  deps={d}")

print(f"\nStep count: {sr.step_count}")
print(f"Warnings: {sr.warnings}")
