"""Quick batch test of propositions - summary only."""
import sys, time, json
sys.stdout.reconfigure(encoding='utf-8')
from pathlib import Path
from verifier.lean_translator import translate_lean_file
from verifier.lean_parser import parse_lean_file
from verifier.proof_synthesizer import synthesize_and_verify

start = int(sys.argv[1]) if len(sys.argv) > 1 else 16
end = int(sys.argv[2]) if len(sys.argv) > 2 else 48
out_dir = Path('skeletons')
out_dir.mkdir(exist_ok=True)

results = []
for n in range(start, end + 1):
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
        if sr.euclid_json:
            with open(out_dir / f'Prop.I.{n}.euclid', 'w', encoding='utf-8') as fout:
                json.dump(sr.euclid_json, fout, indent=2, ensure_ascii=False)
        acc = vr.accepted if vr else False
        nfails = sum(1 for _, lr in vr.line_results.items() if not lr.valid) if vr else -1
        nwarn = len(sr.warnings)
        status = 'PASS' if acc else f'f={nfails}'
        results.append((n, acc, nfails, nwarn, elapsed))
        print(f"I.{n}: {status} w={nwarn} ({elapsed:.1f}s)")
    except Exception as e:
        elapsed = time.time() - t0
        results.append((n, False, -1, 0, elapsed))
        print(f"I.{n}: ERROR ({elapsed:.1f}s) {str(e)[:60]}")

passed = sum(1 for _, acc, _, _, _ in results if acc)
total = len(results)
print(f"\nPASSED: {passed}/{total}")
