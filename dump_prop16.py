"""Dump Prop16 synthesis + verification for debugging."""
import json
from verifier.lean_translator import translate_lean_file
from verifier.lean_parser import parse_lean_file
from verifier.proof_synthesizer import synthesize_and_verify

tr = translate_lean_file('lean_reference/Prop16.lean')
lps = parse_lean_file('lean_reference/Prop16.lean')
sr, vr = synthesize_and_verify(tr, lps[0])
steps = sr.euclid_json['proof']['steps']
premises = sr.euclid_json['proof']['premises']

print("=== PREMISES ===")
for p in premises:
    ln = p["lineNumber"]
    txt = p["text"]
    print(f"  L{ln}: {txt}")

print("\n=== STEPS ===")
for s in steps:
    ln = s['lineNumber']
    txt = s['text'][:80]
    j = s['justification'][:35]
    d = s['dependencies']
    lr = vr.line_results.get(ln)
    if lr and lr.errors:
        status = "ERR: " + lr.errors[0][:70]
    elif lr:
        status = "OK"
    else:
        status = "???"
    print(f"  L{ln:2d}: {txt}")
    print(f"       just={j}  deps={d}")
    print(f"       => {status}")

print(f"\nAccepted: {vr.accepted}")
print(f"Warnings: {sr.warnings}")
