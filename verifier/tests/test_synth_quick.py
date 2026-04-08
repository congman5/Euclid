"""
test_synth_quick.py — Quick scan of synthesizer for all props 16-48.

Phase 1: synthesis only (no verification) with 45s timeout.
Phase 2: verify only the ones that succeeded.
"""
import sys
import time
import threading
from pathlib import Path

PROJECT_ROOT = Path(__file__).resolve().parent.parent.parent
LEAN_REF = PROJECT_ROOT / "lean_reference"

if str(PROJECT_ROOT) not in sys.path:
    sys.path.insert(0, str(PROJECT_ROOT))

from verifier.lean_parser import parse_lean_file
from verifier.lean_translator import translate_lean_file
from verifier.proof_synthesizer import synthesize_proof, synthesize_and_verify


def _run_timeout(func, timeout_s=45):
    box = [None]; exc = [None]
    def wrapper():
        try: box[0] = func()
        except Exception as e: exc[0] = e
    t = threading.Thread(target=wrapper, daemon=True)
    t.start(); t.join(timeout=timeout_s)
    if t.is_alive(): raise TimeoutError(f"Timeout {timeout_s}s")
    if exc[0]: raise exc[0]
    return box[0]


def synth_only(n):
    """Return (sr, lp, tr) or raise."""
    fp = LEAN_REF / f"Prop{n}.lean"
    proofs = parse_lean_file(str(fp))
    lp = proofs[0] if proofs else None
    tr = translate_lean_file(str(fp))
    sr = synthesize_proof(tr, lp)
    return sr, lp, tr


def main():
    print("=" * 80)
    print("PHASE 1: SYNTHESIS ONLY (no verification)")
    print("=" * 80)

    synth_results = {}
    for n in range(16, 49):
        fp = LEAN_REF / f"Prop{n}.lean"
        if not fp.exists():
            print(f"  I.{n:2d}  SKIP (no .lean file)")
            continue
        print(f"  I.{n:2d}  ", end="", flush=True)
        t0 = time.monotonic()
        try:
            sr, lp, tr = _run_timeout(lambda: synth_only(n), timeout_s=45)
            dt = round(time.monotonic() - t0, 1)
            ok = sr.success
            synth_results[n] = (sr, lp, tr)
            warn_count = len(sr.warnings)
            err_count = len(sr.errors)
            tag = "OK" if ok else "FAIL"
            print(f"{tag}  steps={sr.step_count}  warns={warn_count}  errs={err_count}  [{dt}s]")
            if not ok:
                for e in sr.errors[:3]:
                    print(f"         err: {e}")
            if sr.warnings:
                for w in sr.warnings[:3]:
                    print(f"         warn: {w}")
        except TimeoutError:
            dt = round(time.monotonic() - t0, 1)
            print(f"TIMEOUT  [{dt}s]")
        except Exception as ex:
            dt = round(time.monotonic() - t0, 1)
            print(f"ERROR: {type(ex).__name__}: {ex}  [{dt}s]")

    # Phase 2: verify synthesized proofs
    successful = {n: v for n, v in synth_results.items() if v[0].success}
    if not successful:
        print("\nNo successful syntheses to verify.")
        return

    print()
    print("=" * 80)
    print(f"PHASE 2: VERIFICATION ({len(successful)} props)")
    print("=" * 80)

    verified = []
    for n in sorted(successful.keys()):
        sr, lp, tr = successful[n]
        print(f"  I.{n:2d}  ", end="", flush=True)
        t0 = time.monotonic()
        try:
            def do_verify():
                from verifier.unified_checker import verify_e_proof_json
                return verify_e_proof_json(sr.euclid_json)
            vr = _run_timeout(do_verify, timeout_s=30)
            dt = round(time.monotonic() - t0, 1)
            if vr.accepted:
                print(f"VERIFIED  [{dt}s]")
                verified.append(n)
            else:
                bad = {lid: lr.errors[:1] for lid, lr in vr.line_results.items() if not lr.valid}
                print(f"REJECTED ({len(bad)} bad lines)  [{dt}s]")
                for lid, errs in list(bad.items())[:5]:
                    print(f"         line {lid}: {errs}")
        except TimeoutError:
            dt = round(time.monotonic() - t0, 1)
            print(f"VERIFY TIMEOUT [{dt}s]")
        except Exception as ex:
            dt = round(time.monotonic() - t0, 1)
            print(f"VERIFY ERROR: {ex}  [{dt}s]")

    # Summary
    print()
    print("=" * 80)
    synth_ok = sorted(synth_results.keys())
    synth_fail = [n for n in synth_ok if not synth_results[n][0].success]
    synth_pass = [n for n in synth_ok if synth_results[n][0].success]
    print(f"Synthesis succeeded: {len(synth_pass)}/33  {synth_pass}")
    print(f"Synthesis failed:    {len(synth_fail)}/33  {synth_fail}")
    print(f"Verified:            {len(verified)}/33  {verified}")
    print("=" * 80)


if __name__ == "__main__":
    main()
