"""Quick test script for Prop16 synthesis + verification."""
import sys, time, os

# Write output to file to avoid encoding issues
outfile = open('test_prop16_results.txt', 'w', encoding='utf-8')

def out(msg):
    print(msg, file=outfile, flush=True)

from verifier.lean_translator import translate_lean_file
from verifier.lean_parser import parse_lean_file
from verifier.proof_synthesizer import synthesize_and_verify

tr = translate_lean_file('lean_reference/Prop16.lean')
lps = parse_lean_file('lean_reference/Prop16.lean')

out("Running synthesize_and_verify...")
t0 = time.time()
sr, vr = synthesize_and_verify(tr, lps[0])
t1 = time.time()
out(f"Total time: {t1-t0:.1f}s")

# Show steps from the euclid_json
import json
proof = sr.euclid_json
steps = proof.get('proof', {}).get('steps', [])
out(f"\n=== Synthesized steps ({len(steps)}) ===")
for s in steps:
    ln = s.get('lineNumber', '?')
    j = s.get('justification', '?')
    t = s.get('text', '?')
    deps = s.get('dependencies', [])
    out(f"  L{ln}: [{j}] {t}  deps={deps}")

out(f"\nAccepted: {vr.accepted}")
if vr.errors:
    out(f"Global errors: {vr.errors}")

# Show failed lines
failed = [(ln, lr) for ln, lr in vr.line_results.items() if not lr.valid]
out(f"\n=== Failed lines: {len(failed)} ===")
for ln, lr in sorted(failed):
    for e in lr.errors:
        out(f"  L{ln}: {e}")

# Show passed lines
passed = [(ln, lr) for ln, lr in vr.line_results.items() if lr.valid]
out(f"\n=== Passed lines: {len(passed)} ===")
for ln, lr in sorted(passed):
    out(f"  L{ln}: OK")
