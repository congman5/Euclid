"""Quick test of a single proposition synthesis."""
import sys, time
sys.stdout.reconfigure(encoding='utf-8')
from verifier.lean_translator import translate_lean_file
from verifier.lean_parser import parse_lean_file
from verifier.proof_synthesizer import synthesize_and_verify

n = int(sys.argv[1]) if len(sys.argv) > 1 else 17
f = f'lean_reference/Prop{n}.lean'
print(f"Testing I.{n}...")
t0 = time.time()
tr = translate_lean_file(f)
lps = parse_lean_file(f)
lp = lps[0] if lps else None
sr, vr = synthesize_and_verify(tr, lp)
elapsed = time.time() - t0
acc = vr.accepted if vr else None
nfails = sum(1 for _, lr in vr.line_results.items() if not lr.valid) if vr else -1
print(f"I.{n}: acc={acc} fails={nfails} time={elapsed:.1f}s warns={len(sr.warnings)}")
if vr:
    for lid, lr in sorted(vr.line_results.items()):
        if not lr.valid:
            for e in lr.errors[:2]:
                print(f"  L{lid}: {e}")
    if not vr.accepted and hasattr(vr, 'goal_check') and vr.goal_check:
        gc = vr.goal_check
        if not gc.get('established', True):
            print(f"  GOAL MISSING: {gc.get('missing', [])}")
for w in sr.warnings[:5]:
    print(f"  WARN: {w}")
