"""Batch synthesis — I.16 through I.32 quick test."""
import sys, time
sys.stdout.reconfigure(encoding='utf-8')
from pathlib import Path
from verifier.lean_translator import translate_lean_file
from verifier.lean_parser import parse_lean_file
from verifier.proof_synthesizer import synthesize_and_verify

props = list(range(16, 33))
results = []

for n in props:
    ns = str(n)
    f = Path(f'lean_reference/Prop{ns}.lean')
    if not f.exists():
        results.append((ns, 0, 'NO FILE', 0, 0))
        print(f"  I.{ns} - NO FILE")
        continue
    t0 = time.time()
    try:
        tr = translate_lean_file(str(f))
        lps = parse_lean_file(str(f))
        lp = lps[0] if lps else None
        sr, vr = synthesize_and_verify(tr, lp)
        elapsed = time.time() - t0
        if vr and vr.accepted:
            status = 'VERIFIED'
        elif sr.success:
            fails = []
            if vr:
                for lid, lr in sorted(vr.line_results.items()):
                    if not lr.valid:
                        fails.append(f"L{lid}")
            if fails:
                status = f'PARTIAL ({len(fails)} fails)'
            else:
                status = 'SYNTH_OK'
        else:
            status = f'FAIL: {sr.errors[0][:50]}' if sr.errors else 'FAIL'
        results.append((ns, sr.step_count, status, len(sr.warnings), elapsed))
        print(f"  I.{ns} done ({elapsed:.1f}s) - {status[:50]}")
    except Exception as e:
        elapsed = time.time() - t0
        results.append((ns, 0, f'ERROR: {str(e)[:50]}', 0, elapsed))
        print(f"  I.{ns} ERROR ({elapsed:.1f}s)")

print()
print(f"{'Prop':<6} {'Steps':>5} {'Time':>6}  {'W':>3}  {'Status'}")
print('-' * 80)
v = s = fl = 0
for ns, steps, status, warns, elapsed in results:
    print(f"I.{ns:<4} {steps:>5} {elapsed:>5.1f}s  {warns:>3}  {status}")
    if status == 'VERIFIED': v += 1
    elif 'PARTIAL' in status or status == 'SYNTH_OK': s += 1
    else: fl += 1
print(f"\n{v} verified, {s} partial, {fl} failed out of {len(results)}")
