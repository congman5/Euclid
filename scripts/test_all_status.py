"""Quick batch test — summary of all props I.16-I.48 with 120s timeout per prop."""
import sys, time, json, signal
sys.stdout.reconfigure(encoding='utf-8')
from pathlib import Path
from verifier.lean_translator import translate_lean_file
from verifier.lean_parser import parse_lean_file
from verifier.proof_synthesizer import synthesize_and_verify

out_dir = Path('skeletons')
out_dir.mkdir(exist_ok=True)

results = []
for n in range(16, 49):
    f = Path(f'lean_reference/Prop{n}.lean')
    if not f.exists():
        print(f"I.{n}: NO FILE")
        continue
    t0 = time.time()
    try:
        tr = translate_lean_file(str(f))
        lps = parse_lean_file(str(f))
        lp = lps[0] if lps else None
        sr, vr = synthesize_and_verify(tr, lp)
        elapsed = time.time() - t0

        # Save skeleton
        if sr.euclid_json:
            with open(out_dir / f'Prop.I.{n}.euclid', 'w', encoding='utf-8') as fout:
                json.dump(sr.euclid_json, fout, indent=2, ensure_ascii=False)

        acc = vr.accepted if vr else False
        nfails = sum(1 for _, lr in vr.line_results.items() if not lr.valid) if vr else -1
        total_lines = len(vr.line_results) if vr else 0
        nwarn = len(sr.warnings)

        # Collect error summary
        err_types = set()
        if vr:
            for lid, lr in sorted(vr.line_results.items()):
                if not lr.valid:
                    for e in lr.errors:
                        if 'Goal not established' in e:
                            err_types.add('GOAL')
                        elif 'hypothesis not met' in e:
                            err_types.add('HYP')
                        elif 'prerequisite not met' in e:
                            err_types.add('PREREQ')
                        elif 'Parse error' in e:
                            err_types.add('PARSE')
                        elif 'does not derive' in e:
                            err_types.add('AXIOM')
                        else:
                            err_types.add('OTHER')

        status = 'PASS' if acc else f'FAIL(f={nfails}/{total_lines})'
        tag = ' '.join(sorted(err_types)) if err_types else ''
        results.append((n, acc, nfails, total_lines, nwarn, elapsed))
        print(f"I.{n:>2}: {status:<20} w={nwarn:<3} ({elapsed:>6.1f}s) {tag}")
    except Exception as e:
        elapsed = time.time() - t0
        results.append((n, False, -1, 0, 0, elapsed))
        print(f"I.{n:>2}: EXCEPTION           ({elapsed:>6.1f}s) {str(e)[:60]}")

# Summary
print("\n" + "="*60)
passed = sum(1 for _, acc, _, _, _, _ in results if acc)
total = len(results)
zero_fail = sum(1 for _, acc, nf, _, _, _ in results if not acc and nf == 0)
low_fail = sum(1 for _, acc, nf, tl, _, _ in results if not acc and nf > 0 and tl > 0 and nf <= 3)
print(f"FULLY VERIFIED:  {passed}/{total}")
print(f"0 line fails:    {zero_fail} (just missing goal)")
print(f"1-3 line fails:  {low_fail} (close to working)")
print(f"Total:           {total}")
