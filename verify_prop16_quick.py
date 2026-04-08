"""Quick check: verify Prop16 JSON, stop early on errors."""
import json, time
from verifier.lean_translator import translate_lean_file
from verifier.lean_parser import parse_lean_file
from verifier.proof_synthesizer import ProofSynthesizer

tr = translate_lean_file('lean_reference/Prop16.lean')
lps = parse_lean_file('lean_reference/Prop16.lean')
sr = ProofSynthesizer(tr, lps[0]).synthesize()
j = sr.euclid_json

# Run verification with line-by-line callback
from verifier.unified_checker import verify_e_proof_json
t0 = time.time()
errors_seen = []
def on_line(lid, ok, errs):
    dt = time.time() - t0
    if not ok:
        errors_seen.append((lid, errs))
        print(f"  L{lid:2d} FAIL ({dt:.1f}s): {errs}")
    else:
        print(f"  L{lid:2d} OK   ({dt:.1f}s)")

vr = verify_e_proof_json(j, on_line_checked=on_line)
print(f"\nTotal: {time.time()-t0:.1f}s  accepted={vr.accepted}")
print(f"Errors: {len(errors_seen)}")
