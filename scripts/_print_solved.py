"""Print steps from a solved proof .euclid file."""
import json, sys, os, io
sys.stdout = io.TextIOWrapper(sys.stdout.buffer, encoding='utf-8', errors='replace')

prop = int(sys.argv[1]) if len(sys.argv) > 1 else 1
fname = os.path.join("solved_proofs", f"Proposition I.{prop}.euclid")
with open(fname, "r", encoding="utf-8") as f:
    data = json.load(f)
proof = data["proof"]
for i, p in enumerate(proof.get("premises", []), 1):
    print(f"  L{i:2d}: Given                          deps=[]       {p}")
for s in proof["steps"]:
    ln = s["lineNumber"]
    just = s["justification"]
    deps = s["dependencies"]
    text = s["text"]
    print(f"  L{ln:2d}: {just:30s} deps={str(deps):20s} {text}")
