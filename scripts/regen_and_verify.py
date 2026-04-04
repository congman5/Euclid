"""Regenerate all 33 skeletons (I.16-I.48) and verify them."""
import sys, time, json
sys.stdout.reconfigure(encoding='utf-8')
from pathlib import Path
from verifier.lean_translator import translate_lean_file
from verifier.lean_parser import parse_lean_file
from verifier.proof_synthesizer import synthesize_and_verify

out_dir = Path('skeletons')
out_dir.mkdir(exist_ok=True)

props = list(range(16, 49))
results = []

for n in props:
    f = Path(f'lean_reference/Prop{n}.lean')
    if not f.exists():
        print(f"  I.{n} - NO FILE")
        continue
    t0 = time.time()
    try:
        tr = translate_lean_file(str(f))
        lps = parse_lean_file(str(f))
        lp = lps[0] if lps else None
        sr, vr = synthesize_and_verify(tr, lp)
        elapsed = time.time() - t0

        # Write skeleton regardless of acceptance
        if sr.euclid_json:
            with open(out_dir / f'Prop.I.{n}.euclid', 'w', encoding='utf-8') as fout:
                json.dump(sr.euclid_json, fout, indent=2, ensure_ascii=False)

        acc = vr.accepted if vr else False
        nfails = 0
        errs = []
        if vr:
            for lid, lr in sorted(vr.line_results.items()):
                if not lr.valid:
                    nfails += 1
                    for e in lr.errors:
                        errs.append(f"  L{lid}: {e}")
        # Check goal
        if vr and not vr.accepted and vr.goal_check:
            if not vr.goal_check.get('established', True):
                missing = vr.goal_check.get('missing', [])
                errs.insert(0, f"  ERR: Goal not established. Missing: {', '.join(str(m) for m in missing)}")

        status = 'PASS' if acc else f'FAIL(f={nfails})'
        results.append((n, acc, nfails, elapsed, errs))
        print(f"I.{n}: {status} ({elapsed:.1f}s)")
    except Exception as e:
        elapsed = time.time() - t0
        results.append((n, False, -1, elapsed, [f"  EXCEPTION: {e}"]))
        print(f"I.{n}: EXCEPTION ({elapsed:.1f}s) {str(e)[:80]}")

# Summary
print("\n" + "="*60)
passed = sum(1 for _, acc, _, _, _ in results if acc)
total = len(results)
print(f"PASSED: {passed}/{total}")
print()

# Write report
with open(out_dir / 'verification_report.txt', 'w', encoding='utf-8') as f:
    for n, acc, nfails, elapsed, errs in results:
        status = 'PASS' if acc else f'FAIL(f={nfails})'
        f.write(f"I.{n}: {status} ({elapsed:.1f}s)\n")
        for e in errs[:20]:  # limit errors per prop
            f.write(f"{e}\n")
    f.write(f"\nPASSED: {passed}/{total}\n")
print("Report written to skeletons/verification_report.txt")
