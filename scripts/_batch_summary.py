"""Batch test all 33 props with concise summary output."""
import sys, time, signal, threading
sys.stdout.reconfigure(encoding='utf-8')
from verifier.lean_translator import translate_lean_file
from verifier.lean_parser import parse_lean_file
from verifier.proof_synthesizer import synthesize_and_verify
from concurrent.futures import ThreadPoolExecutor, TimeoutError as FTError

TIMEOUT = 300  # seconds per prop

def test_one(n):
    f = f'lean_reference/Prop{n}.lean'
    tr = translate_lean_file(f)
    lps = parse_lean_file(f)
    lp = lps[0] if lps else None
    return synthesize_and_verify(tr, lp)

passed = 0
total = 0
if len(sys.argv) > 1:
    props = [int(x) for x in sys.argv[1:]]
else:
    props = list(range(16, 49))
for n in props:
    t0 = time.time()
    total += 1
    try:
        with ThreadPoolExecutor(max_workers=1) as ex:
            fut = ex.submit(test_one, n)
            sr, vr = fut.result(timeout=TIMEOUT)
        elapsed = time.time() - t0
        if vr and vr.accepted:
            passed += 1
            tag = "OK"
        else:
            nf = sum(1 for lr in vr.line_results.values() if not lr.valid) if vr else 0
            nt = len(vr.line_results) if vr else 0
            tag = f"FAIL f={nf}/{nt}"
            if vr and nf == 0:
                tag += " goal-miss"
    except FTError:
        elapsed = time.time() - t0
        tag = "TIMEOUT"
    except Exception as e:
        elapsed = time.time() - t0
        tag = f"ERR: {e}"
    print(f"I.{n:2d}: {tag:30s} {elapsed:5.1f}s", flush=True)

print(f"\n=== {passed}/{total} verified ===")
