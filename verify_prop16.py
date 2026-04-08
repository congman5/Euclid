"""Verify Prop16 and show only failing lines."""
import json, time
from verifier.lean_translator import translate_lean_file
from verifier.lean_parser import parse_lean_file
from verifier.proof_synthesizer import synthesize_and_verify

tr = translate_lean_file('lean_reference/Prop16.lean')
lps = parse_lean_file('lean_reference/Prop16.lean')
t0 = time.time()
sr, vr = synthesize_and_verify(tr, lps[0])
dt = time.time() - t0

steps = sr.euclid_json['proof']['steps']
print(f"Time: {dt:.1f}s  accepted: {vr.accepted}")
print()

for s in steps:
    ln = s['lineNumber']
    lr = vr.line_results.get(ln)
    if lr and lr.errors:
        print(f"L{ln:2d}: {s['text'][:80]}")
        print(f"     just={s['justification']}  deps={s['dependencies']}")
        for e in lr.errors:
            print(f"     ERR: {e}")
        print()
