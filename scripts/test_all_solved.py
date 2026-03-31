"""Quick test: verify all .euclid files in solved_proofs/."""
import json, os, sys, io
sys.stdout = io.TextIOWrapper(sys.stdout.buffer, encoding='utf-8')
sys.path.insert(0, os.path.join(os.path.dirname(__file__), ".."))
from verifier.unified_checker import verify_e_proof_json

SOLVED = os.path.join(os.path.dirname(__file__), "..", "solved_proofs")

def load_euclid(path):
    with open(path, "r", encoding="utf-8") as f:
        data = json.load(f)
    proof = data["proof"]
    premises = proof.get("premises", [])
    lines = []
    for i, prem in enumerate(premises, start=1):
        lines.append({"id": i, "depth": 0, "statement": prem,
                       "justification": "Given", "refs": []})
    for step in proof.get("steps", []):
        lines.append({"id": step["lineNumber"], "depth": step.get("depth", 0),
                       "statement": step["text"],
                       "justification": step["justification"],
                       "refs": step.get("dependencies", [])})
    return {"name": proof.get("name", ""), "declarations": proof.get("declarations", {}),
            "premises": premises, "goal": proof.get("goal", ""), "lines": lines}

ok = 0
fail = 0
results = []
for fn in sorted(os.listdir(SOLVED)):
    if not fn.endswith(".euclid"):
        continue
    path = os.path.join(SOLVED, fn)
    pj = load_euclid(path)
    r = verify_e_proof_json(pj)
    n = len(pj["lines"])
    nok = sum(1 for lr in r.line_results.values() if lr.valid)
    status = "PASS" if r.accepted else "FAIL"
    if r.accepted:
        ok += 1
    else:
        fail += 1
    results.append((fn, status, nok, n, r))
    print(f"  {status} {fn} ({nok}/{n} lines)")

print(f"\n=== {ok}/{ok+fail} solved proofs passing ===")
if fail:
    print("\nFailed proofs:")
    for fn, status, nok, n, r in results:
        if status == "FAIL":
            print(f"\n  {fn}:")
            for lid, lr in r.line_results.items():
                if not lr.valid:
                    print(f"    L{lid}: {lr.errors[:2]}")
            if r.errors:
                print(f"    Goals: {r.errors[:3]}")
