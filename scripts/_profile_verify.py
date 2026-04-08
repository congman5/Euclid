"""Profile per-line verification timing for a single proposition."""
import sys, time
sys.stdout.reconfigure(encoding='utf-8')
from verifier.lean_translator import translate_lean_file
from verifier.lean_parser import parse_lean_file
from verifier.proof_synthesizer import synthesize_proof

prop_num = int(sys.argv[1]) if len(sys.argv) > 1 else 16
f = f'lean_reference/Prop{prop_num}.lean'
tr = translate_lean_file(f)
lps = parse_lean_file(f)
lp = lps[0] if lps else None

t0 = time.time()
sr = synthesize_proof(tr, lp)
t1 = time.time()
print(f"Synthesis: {t1-t0:.2f}s  steps={sr.step_count}  success={sr.success}")

if not sr.success or not sr.euclid_json:
    print("Synthesis failed, cannot verify")
    for e in sr.errors[:5]:
        print(f"  ERR: {e[:120]}")
    sys.exit(1)

# Now profile verification line-by-line
from verifier import unified_checker as uc
from verifier.e_parser import parse_literal_list, EParseError
from verifier.e_ast import Sort

proof_json = sr.euclid_json
# Normalize
if "proof" in proof_json and "steps" in proof_json.get("proof", {}):
    inner = proof_json["proof"]
    premises = inner.get("premises", [])
    lines = []
    for i, p in enumerate(premises, 1):
        lines.append({"id": i, "depth": 0, "statement": p, "justification": "Given", "refs": []})
    for s in inner.get("steps", []):
        lines.append({"id": s["lineNumber"], "depth": s.get("depth", 0),
                       "statement": s["text"], "justification": s["justification"],
                       "refs": s.get("dependencies", [])})
    proof_json = {"name": inner.get("name", ""), "premises": premises,
                  "goal": inner.get("goal", ""),
                  "declarations": inner.get("declarations", {}), "lines": lines}

print(f"\nVerifying {len(proof_json['lines'])} lines...")
timings = []

def on_line(lid, valid, errors):
    pass

t2 = time.time()
vr = uc.verify_e_proof_json(sr.euclid_json, on_line_checked=on_line)
t3 = time.time()
print(f"Total verify: {t3-t2:.2f}s  accepted={vr.accepted}")

# Print per-line results
for lid, lr in sorted(vr.line_results.items()):
    status = "OK" if lr.valid else "FAIL"
    errs = "; ".join(lr.errors[:1]) if lr.errors else ""
    print(f"  L{lid:3d}: {status}  {errs[:100]}")
