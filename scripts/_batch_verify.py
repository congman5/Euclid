"""Quick batch: synthesize + verify I.16-I.48, report results."""
import sys, time
sys.stdout.reconfigure(encoding='utf-8')
from verifier.lean_translator import translate_lean_file
from verifier.lean_parser import parse_lean_file
from verifier.proof_synthesizer import synthesize_and_verify

# Only verify props that previously were OK in baseline
# to see if our changes broke/fixed anything
props = list(range(16, 49))
results = []

for n in props:
    f = f'lean_reference/Prop{n}.lean'
    t0 = time.time()
    try:
        tr = translate_lean_file(f)
        lps = parse_lean_file(f)
        lp = lps[0] if lps else None
        sr, vr = synthesize_and_verify(tr, lp)
        elapsed = time.time() - t0
        if vr and vr.accepted:
            status = 'VERIFIED'
        elif sr.success:
            n_fail = sum(1 for lr in vr.line_results.values() if not lr.valid) if vr else 0
            n_total = len(vr.line_results) if vr else 0
            status = f'SYNTH_OK ({n_fail}/{n_total} lines fail)'
        else:
            status = f'FAIL'
        results.append((n, sr.step_count, status, len(sr.warnings), elapsed))
        print(f"  I.{n} done ({elapsed:.1f}s) - {status}")
    except Exception as e:
        elapsed = time.time() - t0
        results.append((n, 0, f'ERROR: {str(e)[:50]}', 0, elapsed))
        print(f"  I.{n} ERROR ({elapsed:.1f}s) - {e}")

print()
print(f"{'Prop':<6} {'Steps':>5} {'Time':>7}  {'W':>3}  {'Status'}")
print('-' * 80)
v = s = fl = 0
for n, steps, status, warns, elapsed in results:
    print(f"I.{n:<4} {steps:>5} {elapsed:>6.1f}s  {warns:>3}  {status}")
    if status == 'VERIFIED': v += 1
    elif 'SYNTH_OK' in status: s += 1
    else: fl += 1
print(f"\n{v} verified, {s} synth-ok, {fl} failed out of {len(results)}")
