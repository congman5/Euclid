"""Quick synthesis test for a single range of propositions.

Writes all output to verifier/tests/synth_baseline_results.txt
so it can run in the background without terminal dependency.

Uses multiprocessing to enforce hard timeouts (threads can't be killed).
"""
import sys, time, datetime, multiprocessing, json
from pathlib import Path

PROJECT_ROOT = Path(__file__).resolve().parent.parent.parent
LEAN_REF = PROJECT_ROOT / "lean_reference"
RESULTS_FILE = Path(__file__).resolve().parent / "synth_baseline_results.txt"
if str(PROJECT_ROOT) not in sys.path:
    sys.path.insert(0, str(PROJECT_ROOT))


def _synth_worker(n, result_queue):
    """Run in a child process — imports happen here to avoid pickling issues."""
    try:
        from verifier.lean_parser import parse_lean_file
        from verifier.lean_translator import translate_lean_file
        from verifier.proof_synthesizer import synthesize_proof

        lean_path = str(Path(__file__).resolve().parent.parent.parent / "lean_reference" / f"Prop{n}.lean")
        proofs = parse_lean_file(lean_path)
        lp = proofs[0] if proofs else None
        tr = translate_lean_file(lean_path)
        sr = synthesize_proof(tr, lp)
        result_queue.put({
            "n": n,
            "success": sr.success,
            "step_count": sr.step_count,
            "warnings": list(sr.warnings) if sr.warnings else [],
            "errors": list(sr.errors) if sr.errors else [],
        })
    except Exception as ex:
        result_queue.put({
            "n": n,
            "exception": f"{type(ex).__name__}: {ex}",
        })


def emit(line, f):
    """Write line to both stdout and the results file."""
    print(line, flush=True)
    f.write(line + "\n")
    f.flush()


if __name__ == "__main__":
    import argparse
    parser = argparse.ArgumentParser()
    parser.add_argument("start", type=int, nargs="?", default=16)
    parser.add_argument("end", type=int, nargs="?", default=48)
    parser.add_argument("--timeout", type=int, default=45)
    args = parser.parse_args()

    ok_count = 0; fail_count = 0; timeout_count = 0; error_count = 0; skip_count = 0
    results = []

    with open(RESULTS_FILE, "w", encoding="utf-8") as f:
        header = f"=== Synthesizer Baseline  Props {args.start}-{args.end}  timeout={args.timeout}s  {datetime.datetime.now():%Y-%m-%d %H:%M:%S} ==="
        emit(header, f)
        emit("", f)

        for n in range(args.start, args.end + 1):
            fp = LEAN_REF / f"Prop{n}.lean"
            if not fp.exists():
                emit(f"I.{n:2d}  SKIP (no file)", f)
                skip_count += 1
                results.append((n, "SKIP", 0, 0, 0, 0))
                continue

            t0 = time.monotonic()
            result_queue = multiprocessing.Queue()
            proc = multiprocessing.Process(target=_synth_worker, args=(n, result_queue))
            proc.start()
            proc.join(timeout=args.timeout)
            dt = round(time.monotonic() - t0, 1)

            if proc.is_alive():
                proc.terminate()
                proc.join(timeout=5)
                if proc.is_alive():
                    proc.kill()
                    proc.join(timeout=3)
                emit(f"I.{n:2d}  TIMEOUT [{dt}s]", f)
                timeout_count += 1
                results.append((n, "TIMEOUT", 0, 0, 0, dt))
            elif not result_queue.empty():
                res = result_queue.get_nowait()
                if "exception" in res:
                    emit(f"I.{n:2d}  ERROR: {res['exception']} [{dt}s]", f)
                    error_count += 1
                    results.append((n, "ERROR", 0, 0, 0, dt))
                else:
                    tag = "OK" if res["success"] else "FAIL"
                    line = f"I.{n:2d}  {tag}  steps={res['step_count']}  warns={len(res['warnings'])}  errs={len(res['errors'])}  [{dt}s]"
                    emit(line, f)
                    if tag == "OK":
                        ok_count += 1
                    else:
                        fail_count += 1
                    results.append((n, tag, res["step_count"], len(res["warnings"]), len(res["errors"]), dt))
                    for e in res["errors"]:
                        emit(f"       err: {e}", f)
                    for w in res["warnings"]:
                        emit(f"       warn: {w}", f)
            else:
                emit(f"I.{n:2d}  ERROR: process exited with no result [{dt}s]", f)
                error_count += 1
                results.append((n, "ERROR", 0, 0, 0, dt))

        # Summary
        emit("", f)
        emit("=" * 60, f)
        emit(f"SUMMARY  (Props {args.start}-{args.end})", f)
        emit(f"  OK:       {ok_count}", f)
        emit(f"  FAIL:     {fail_count}", f)
        emit(f"  TIMEOUT:  {timeout_count}", f)
        emit(f"  ERROR:    {error_count}", f)
        emit(f"  SKIP:     {skip_count}", f)
        emit(f"  Total:    {ok_count + fail_count + timeout_count + error_count + skip_count}", f)
        emit("", f)
        emit("OK props:      " + ", ".join(f"I.{r[0]}" for r in results if r[1] == "OK"), f)
        emit("FAIL props:    " + ", ".join(f"I.{r[0]}" for r in results if r[1] == "FAIL"), f)
        emit("TIMEOUT props: " + ", ".join(f"I.{r[0]}" for r in results if r[1] == "TIMEOUT"), f)
        emit("ERROR props:   " + ", ".join(f"I.{r[0]}" for r in results if r[1] == "ERROR"), f)
        emit("", f)
        emit(f"Results saved to: {RESULTS_FILE}", f)
