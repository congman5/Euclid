"""Test verify specific propositions."""
import sys, time
sys.stdout.reconfigure(encoding='utf-8')
from verifier.lean_translator import translate_lean_file
from verifier.lean_parser import parse_lean_file
from verifier.proof_synthesizer import synthesize_and_verify

props = [int(x) for x in sys.argv[1:]] if len(sys.argv) > 1 else [17, 28, 31, 33]

for n in props:
    f = f'lean_reference/Prop{n}.lean'
    t0 = time.time()
    tr = translate_lean_file(f)
    lps = parse_lean_file(f)
    lp = lps[0] if lps else None
    sr, vr = synthesize_and_verify(tr, lp)
    elapsed = time.time() - t0
    accepted = vr.accepted if vr else None
    n_fail = sum(1 for lr in vr.line_results.values() if not lr.valid) if vr else 0
    n_total = len(vr.line_results) if vr else 0
    print(f"I.{n}: {elapsed:.1f}s  steps={sr.step_count}  verified={accepted}  fails={n_fail}/{n_total}  warns={len(sr.warnings)}")
    if vr and not vr.accepted:
        for lid, lr in sorted(vr.line_results.items()):
            if not lr.valid:
                print(f"  L{lid}: {lr.errors[0][:100]}")
