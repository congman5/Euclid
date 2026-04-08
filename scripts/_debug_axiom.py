"""Debug axiom step failures by tracing dep_aug and check_specific_axiom."""
import sys
import json
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent.parent))

from verifier import unified_checker as uc
from verifier.e_axiom_match import check_specific_axiom, get_axiom_clause
from verifier.e_parser import parse_literal

def main():
    prop = int(sys.argv[1])
    target_line = int(sys.argv[2])

    skel = Path(f"skeletons/Prop.I.{prop}.euclid")
    d = json.load(skel.open(encoding="utf-8"))

    steps = d["proof"]["steps"]
    premises = d["proof"].get("premises", [])

    # Build line_lits from verified results
    # First, just print the step info
    for s in steps:
        if s["lineNumber"] == target_line:
            print(f"Target step L{target_line}:")
            print(f"  justification: {s['justification']}")
            print(f"  text: {s['text']}")
            print(f"  deps: {s['dependencies']}")

            # Collect all dep facts (from premises + earlier steps)
            dep_facts = set()
            dep_lines = set(s["dependencies"])

            # Premises
            for i, p in enumerate(premises, 1):
                if i in dep_lines:
                    lit = parse_literal(p)
                    if lit:
                        dep_facts.add(lit)
                        print(f"  dep L{i} (premise): {p}")

            # Earlier steps
            for s2 in steps:
                if s2["lineNumber"] in dep_lines and s2["lineNumber"] < target_line:
                    for t in s2["text"].split(", "):
                        lit = parse_literal(t.strip())
                        if lit:
                            dep_facts.add(lit)
                    print(f"  dep L{s2['lineNumber']}: {s2['text']}")

            # Parse target conclusions
            target_lits = []
            for t in s["text"].split(", "):
                lit = parse_literal(t.strip())
                if lit:
                    target_lits.append(lit)

            print(f"\n  dep_facts ({len(dep_facts)}):")
            for f in sorted(dep_facts, key=str):
                print(f"    {f}")
            print(f"\n  target_lits:")
            for t in target_lits:
                print(f"    {t}")

            # Try check_specific_axiom
            axiom_name = s["justification"]
            print(f"\n  Checking axiom '{axiom_name}'...")

            # Get the axiom clause
            clause = get_axiom_clause(axiom_name)
            if clause:
                print(f"  Axiom clause: {clause}")

            # Try the check
            ok, msg = check_specific_axiom(
                axiom_name, dep_facts, target_lits, set())
            print(f"  Result: ok={ok}, msg={msg}")

            break

if __name__ == "__main__":
    main()
