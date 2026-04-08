"""Profile per-line verification timing using monkeypatched callback."""
import sys, time
sys.stdout.reconfigure(encoding='utf-8')
from verifier.lean_translator import translate_lean_file
from verifier.lean_parser import parse_lean_file
from verifier.proof_synthesizer import synthesize_proof
from verifier import unified_checker as uc

prop_num = int(sys.argv[1]) if len(sys.argv) > 1 else 16
f = f'lean_reference/Prop{prop_num}.lean'
tr = translate_lean_file(f)
lps = parse_lean_file(f)
lp = lps[0] if lps else None

sr = synthesize_proof(tr, lp)
if not sr.success or not sr.euclid_json:
    print("Synthesis failed"); sys.exit(1)

# Monkeypatch to time each line
_line_times = {}
_last_t = [time.time()]

def on_line(lid, valid, errors):
    now = time.time()
    dt = now - _last_t[0]
    _line_times[lid] = (dt, valid, errors)
    _last_t[0] = now

_last_t[0] = time.time()
vr = uc.verify_e_proof_json(sr.euclid_json, on_line_checked=on_line)
total = sum(dt for dt, _, _ in _line_times.values())

print(f"Total verify: {total:.2f}s  accepted={vr.accepted}")
print(f"\nSlowest lines:")
sorted_times = sorted(_line_times.items(), key=lambda x: -x[1][0])
for lid, (dt, valid, errors) in sorted_times[:20]:
    status = "OK" if valid else "FAIL"
    lr = vr.line_results.get(lid)
    just = ""
    # Get justification from the proof JSON
    pj = sr.euclid_json
    if "proof" in pj:
        for s in pj["proof"].get("steps", []):
            if s["lineNumber"] == lid:
                just = s["justification"][:40]
                break
    err = errors[0][:60] if errors else ""
    print(f"  L{lid:3d}: {dt:7.2f}s {status:4s} just={just:40s}  {err}")
