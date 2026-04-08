"""Quick synthesis-only test for Prop16."""
import sys, time
outfile = open('test_prop16_results.txt', 'w', encoding='utf-8')
def out(msg):
    print(msg, file=outfile, flush=True)

from verifier.lean_translator import translate_lean_file
from verifier.lean_parser import parse_lean_file
from verifier.proof_synthesizer import ProofSynthesizer

tr = translate_lean_file('lean_reference/Prop16.lean')
lps = parse_lean_file('lean_reference/Prop16.lean')

out("Synthesizing...")
t0 = time.time()
ps = ProofSynthesizer(tr, lps[0])
ps.synthesize()
t1 = time.time()
out(f"Synthesis: {len(ps.steps)} steps in {t1-t0:.1f}s")

for s in ps.steps:
    ln = s['lineNumber']
    j = s['justification']
    t = s['text']
    deps = s.get('dependencies', [])
    out(f"  L{ln}: [{j}] {t}  deps={deps}")

outfile.close()
print("Done - see test_prop16_results.txt")
