"""
test_synthesizer_all.py — Test the proof synthesizer against all propositions 16-48.

Runs synthesize_and_verify for each Lean reference file and reports:
  - Whether synthesis succeeded (valid JSON produced)
  - Whether the verifier accepted the proof
  - Step count, warnings, and errors
  - Per-line verification failures
"""
import sys
import time
from pathlib import Path

# Resolve paths
SCRIPT_DIR = Path(__file__).resolve().parent
PROJECT_ROOT = SCRIPT_DIR.parent.parent
LEAN_REFERENCE_DIR = PROJECT_ROOT / "lean_reference"

# Ensure project root is importable
if str(PROJECT_ROOT) not in sys.path:
    sys.path.insert(0, str(PROJECT_ROOT))

from verifier.lean_parser import parse_lean_file
from verifier.lean_translator import translate_lean_file
from verifier.proof_synthesizer import synthesize_proof, synthesize_and_verify


def test_one_prop(n: int):
    """Synthesize and verify one proposition, returning a result dict."""
    lean_file = LEAN_REFERENCE_DIR / f"Prop{n}.lean"
    result = {
        "prop": n,
        "lean_file_exists": lean_file.exists(),
        "translation_ok": False,
        "synthesis_ok": False,
        "synthesis_steps": 0,
        "synthesis_warnings": [],
        "synthesis_errors": [],
        "verify_ok": False,
        "verify_line_failures": {},
        "verify_errors": [],
        "time_s": 0.0,
    }
    if not lean_file.exists():
        result["synthesis_errors"] = [f"File not found: {lean_file}"]
        return result

    t0 = time.monotonic()
    import signal, threading, functools

    def _run_with_timeout(func, timeout_s=90):
        """Run func in a thread with timeout. Returns result or raises TimeoutError."""
        result_box = [None]
        exc_box = [None]
        def wrapper():
            try:
                result_box[0] = func()
            except Exception as ex:
                exc_box[0] = ex
        t = threading.Thread(target=wrapper, daemon=True)
        t.start()
        t.join(timeout=timeout_s)
        if t.is_alive():
            raise TimeoutError(f"Timed out after {timeout_s}s")
        if exc_box[0] is not None:
            raise exc_box[0]
        return result_box[0]

    try:
        def do_synth():
            # Parse Lean file
            proofs = parse_lean_file(str(lean_file))
            lp = proofs[0] if proofs else None

            # Translate
            tr = translate_lean_file(str(lean_file))
            trans_ok = bool(tr.steps) or (lp is not None and bool(lp.tactics))

            # Synthesize and verify
            sr, vr = synthesize_and_verify(tr, lp)
            return trans_ok, sr, vr

        trans_ok, sr, vr = _run_with_timeout(do_synth, timeout_s=60)
        result["translation_ok"] = trans_ok
        result["synthesis_ok"] = sr.success
        result["synthesis_steps"] = sr.step_count
        result["synthesis_warnings"] = sr.warnings[:10]  # cap for readability
        result["synthesis_errors"] = sr.errors[:10]

        if vr is not None:
            result["verify_ok"] = vr.accepted
            result["verify_errors"] = vr.errors[:10]
            # Gather per-line failures
            if hasattr(vr, 'line_results'):
                for lid, lr in vr.line_results.items():
                    if not lr.valid:
                        result["verify_line_failures"][lid] = lr.errors[:3]
    except TimeoutError as te:
        result["synthesis_errors"] = [str(te)]
    except Exception as e:
        result["synthesis_errors"] = [f"Exception: {type(e).__name__}: {e}"]

    result["time_s"] = round(time.monotonic() - t0, 2)
    return result


def main():
    """Run synthesizer on all propositions 16-48 and print a summary."""
    print("=" * 80)
    print("PROOF SYNTHESIZER TEST — Propositions I.16 through I.48")
    print("=" * 80)
    print()

    results = []
    total_start = time.monotonic()

    for n in range(16, 49):
        print(f"  Prop I.{n:2d} ... ", end="", flush=True)
        r = test_one_prop(n)
        results.append(r)

        status = ""
        if r["verify_ok"]:
            status = "VERIFIED ✓"
        elif r["synthesis_ok"]:
            status = f"SYNTH OK, VERIFY FAIL ({len(r['verify_line_failures'])} bad lines)"
        elif r["translation_ok"]:
            status = f"SYNTH FAIL: {r['synthesis_errors'][:1]}"
        else:
            status = f"NO TRANSLATION: {r['synthesis_errors'][:1]}"

        print(f"{status}  [{r['synthesis_steps']} steps, {r['time_s']}s]")

        # Print warnings/errors for non-verified props
        if not r["verify_ok"]:
            if r["synthesis_warnings"]:
                for w in r["synthesis_warnings"][:3]:
                    print(f"           warn: {w}")
            if r["synthesis_errors"]:
                for e in r["synthesis_errors"][:3]:
                    print(f"           err:  {e}")
            if r["verify_line_failures"]:
                for lid, errs in list(r["verify_line_failures"].items())[:5]:
                    print(f"           line {lid}: {errs[:1]}")

    total_time = round(time.monotonic() - total_start, 1)

    # Summary
    print()
    print("=" * 80)
    print("SUMMARY")
    print("=" * 80)

    verified = [r for r in results if r["verify_ok"]]
    synth_ok = [r for r in results if r["synthesis_ok"]]
    failed = [r for r in results if not r["synthesis_ok"]]

    print(f"  Total propositions tested:  {len(results)}")
    print(f"  Synthesis succeeded:        {len(synth_ok)}")
    print(f"  Fully verified:             {len(verified)}")
    print(f"  Synthesis failed:           {len(failed)}")
    print(f"  Total time:                 {total_time}s")
    print()

    if verified:
        names = ', '.join('I.' + str(r['prop']) for r in verified)
        print(f"  V Verified: {names}")
    if synth_ok and len(synth_ok) > len(verified):
        unverified = [r for r in synth_ok if not r["verify_ok"]]
        names = ', '.join('I.' + str(r['prop']) for r in unverified)
        print(f"  ~ Synth OK but not verified: {names}")
    if failed:
        names = ', '.join('I.' + str(r['prop']) for r in failed)
        print(f"  X Failed: {names}")

    print()

    # Detailed failure analysis
    if any(not r["verify_ok"] for r in results):
        print("=" * 80)
        print("DETAILED FAILURE ANALYSIS")
        print("=" * 80)
        for r in results:
            if r["verify_ok"]:
                continue
            print(f"\n  --- Prop I.{r['prop']} ---")
            print(f"  Synthesis: {'OK' if r['synthesis_ok'] else 'FAILED'}")
            print(f"  Steps: {r['synthesis_steps']}")
            if r["synthesis_errors"]:
                print(f"  Synth errors:")
                for e in r["synthesis_errors"]:
                    print(f"    - {e}")
            if r["synthesis_warnings"]:
                print(f"  Synth warnings:")
                for w in r["synthesis_warnings"]:
                    print(f"    - {w}")
            if r["verify_line_failures"]:
                print(f"  Verify line failures:")
                for lid, errs in r["verify_line_failures"].items():
                    for e in errs:
                        print(f"    line {lid}: {e}")
            if r["verify_errors"]:
                print(f"  Verify errors:")
                for e in r["verify_errors"]:
                    print(f"    - {e}")


if __name__ == "__main__":
    main()
