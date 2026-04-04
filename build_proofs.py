#!/usr/bin/env python3
"""Build and verify .euclid proof files for Propositions I.16-I.48."""
import json, sys, os
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from verifier.unified_checker import verify_e_proof_json

def S(num, text, just, deps, depth=0):
    return {"lineNumber": num, "text": text, "justification": just,
            "dependencies": deps, "depth": depth, "status": "?"}

def proof_json(name, premises, goal, decl, steps, meta=None):
    return {
        "format": "euclid-proof", "version": "1.0.0",
        "program": "Euclid Elements Simulator (Python)",
        "metadata": meta or {},
        "canvas": {"points":[],"segments":[],"rays":[],"circles":[],
                   "angleMarks":[],"equalityGroups":[]},
        "exportedAt": "2026-06-01T00:00:00Z",
        "proof": {"name": name, "premises": premises, "goal": goal,
                  "declarations": decl, "steps": steps}
    }

def verify(data, verbose=True):
    r = verify_e_proof_json(data)
    name = data["proof"]["name"]
    if r.accepted:
        if verbose: print(f"  PASS  {name}")
        return True
    if verbose:
        print(f"  FAIL  {name}")
        for e in r.errors[:5]:
            print(f"    ERR: {e}")
        for lid, lr in sorted(r.line_results.items()):
            tag = "OK" if lr.valid else "FAIL"
            if not lr.valid:
                for e in lr.errors[:2]:
                    print(f"    L{lid} {tag}: {e}")
            else:
                print(f"    L{lid} OK")
    return False

def save(data, directory="solved_proofs"):
    name = data["proof"]["name"]
    num = name.replace("Prop.I.", "")
    fn = os.path.join(directory, f"Proposition I.{num}.euclid")
    with open(fn, "w", encoding="utf-8") as f:
        json.dump(data, f, indent=2, ensure_ascii=False)
    return fn

if __name__ == "__main__":
    print("build_proofs.py ready")
