"""
Generate .euclid files from the verified JSON answer key.

Uses answer_key_book_1.json as the authoritative source for proof steps,
and the existing .euclid files for canvas data.
For I.6, uses the working proof from scripts/_test_i6_v4.py.
"""
import ast
import json
import os
from datetime import datetime, timezone

WORKTREE = os.path.dirname(os.path.abspath(__file__))
ANSWER_KEY = os.path.join(WORKTREE, "answer_key_book_1.json")
SOLVED_DIR = os.path.join(WORKTREE, "solved_proofs")
I6_SCRIPT = os.path.join(WORKTREE, "scripts", "_test_i6_v4.py")
I9_SCRIPT = os.path.join(WORKTREE, "scripts", "test_i9_proof.py")


def load_answer_key():
    with open(ANSWER_KEY, "r", encoding="utf-8") as f:
        return json.load(f)


def load_existing_euclid(prop_name):
    """Load existing .euclid file for canvas data."""
    path = os.path.join(SOLVED_DIR, f"{prop_name}.euclid")
    if os.path.exists(path):
        with open(path, "r", encoding="utf-8") as f:
            return json.load(f)
    return None


def get_i9_proof():
    """Return the verified I.9 proof (from test_i9_proof.py)."""
    return {
        "name": "Prop.I.9",
        "premises": [
            "\u00ac(a = b)", "\u00ac(a = c)", "\u00ac(b = c)",
            "on(a, M)", "on(b, M)", "on(a, N)", "on(c, N)",
            "\u00ac(on(c, M))", "\u00ac(on(b, N))"
        ],
        "goal": "\u2220bae = \u2220cae, same-side(e, c, M), same-side(e, b, N)",
        "lines": [
            {"id": 1, "depth": 0, "statement": "\u00ac(a = b)", "justification": "Given", "refs": []},
            {"id": 2, "depth": 0, "statement": "\u00ac(a = c)", "justification": "Given", "refs": []},
            {"id": 3, "depth": 0, "statement": "\u00ac(b = c)", "justification": "Given", "refs": []},
            {"id": 4, "depth": 0, "statement": "on(a, M)", "justification": "Given", "refs": []},
            {"id": 5, "depth": 0, "statement": "on(b, M)", "justification": "Given", "refs": []},
            {"id": 6, "depth": 0, "statement": "on(a, N)", "justification": "Given", "refs": []},
            {"id": 7, "depth": 0, "statement": "on(c, N)", "justification": "Given", "refs": []},
            {"id": 8, "depth": 0, "statement": "\u00ac(on(c, M))", "justification": "Given", "refs": []},
            {"id": 9, "depth": 0, "statement": "\u00ac(on(b, N))", "justification": "Given", "refs": []},
            {"id": 10, "depth": 0, "statement": "center(a, \u03b1), on(b, \u03b1)", "justification": "let-circle", "refs": [1]},
            {"id": 11, "depth": 0, "statement": "inside(a, \u03b1)", "justification": "Generality 3", "refs": [10]},
            {"id": 12, "depth": 0, "statement": "on(d, N), between(a, d, c), on(d, \u03b1)", "justification": "let-point-on-line-between", "refs": [6, 7, 2]},
            {"id": 13, "depth": 0, "statement": "on(f, M), between(a, f, b), on(f, \u03b1)", "justification": "let-point-on-line-between", "refs": [4, 5, 1]},
            {"id": 14, "depth": 0, "statement": "ad = ab", "justification": "Transfer", "refs": [10, 12]},
            {"id": 15, "depth": 0, "statement": "af = ab", "justification": "Transfer", "refs": [10, 13]},
            {"id": 16, "depth": 0, "statement": "ad = af", "justification": "Metric", "refs": [14, 15]},
            {"id": 17, "depth": 0, "statement": "df = de, df = fe, \u00ac(e = d), \u00ac(e = f)", "justification": "Prop.I.1", "refs": [16]},
            {"id": 18, "depth": 0, "statement": "de = fe", "justification": "Metric", "refs": [17]},
            {"id": 19, "depth": 0, "statement": "ae = ae", "justification": "Metric", "refs": []},
            {"id": 20, "depth": 0, "statement": "\u2220dae = \u2220fae, \u2220ade = \u2220afe, \u2220aed = \u2220aef, \u25b3ade = \u25b3afe", "justification": "SSS", "refs": [16, 18, 19]},
            {"id": 21, "depth": 0, "statement": "\u00ac(e = a)", "justification": "Diagrammatic", "refs": []},
            {"id": 22, "depth": 0, "statement": "on(a, K), on(e, K)", "justification": "let-line", "refs": [21]},
            {"id": 23, "depth": 0, "statement": "\u2220dae = \u2220cae", "justification": "Transfer", "refs": []},
            {"id": 24, "depth": 0, "statement": "\u2220fae = \u2220bae", "justification": "Transfer", "refs": []},
            {"id": 25, "depth": 0, "statement": "\u2220bae = \u2220cae", "justification": "Metric", "refs": [20, 23, 24]},
            {"id": 26, "depth": 0, "statement": "same-side(e, c, M)", "justification": "Diagrammatic", "refs": []},
            {"id": 27, "depth": 0, "statement": "same-side(e, b, N)", "justification": "Diagrammatic", "refs": []}
        ]
    }


def load_i6_proof():
    """Extract the I.6 proof JSON from the test script."""
    with open(I6_SCRIPT, "r", encoding="utf-8") as f:
        content = f.read()
    # Extract JSON between json.loads(""" and """)
    start = content.index('json.loads("""') + len('json.loads("""')
    end = content.index('""")', start)
    raw = content[start:end]
    # The source file has Python-level escapes (\\uXXXX) that need to be
    # interpreted as Python would in a triple-quoted string
    py_string = '"""' + raw + '"""'
    actual_string = ast.literal_eval(py_string)
    return json.loads(actual_string)


def verifier_to_euclid(verified_proof, canvas_data, prop_display_name):
    """Convert verifier JSON format to .euclid format."""
    lines = verified_proof.get("lines", [])
    premises_list = verified_proof.get("premises", [])
    goal = verified_proof.get("goal", "")
    name = verified_proof.get("name", prop_display_name)

    # Separate Given lines from proof steps
    given_lines = [l for l in lines if l["justification"] == "Given"]
    step_lines = [l for l in lines if l["justification"] != "Given"]

    # Extract premises from Given lines (in order)
    premises = [l["statement"] for l in given_lines]
    # Fall back to the premises field if Given lines don't match
    if not premises and premises_list:
        premises = premises_list

    # Extract declared points and lines from premises
    points_set = set()
    lines_set = set()
    for stmt in premises:
        # Extract symbols - simple heuristic
        import re
        for sym in re.findall(r'[a-zA-Zα-ωΑ-Ω][a-zA-Z0-9]*', stmt):
            if sym in ('on', 'between', 'center', 'inside', 'intersects',
                       'same', 'side', 'right', 'angle', 'Given', 'true', 'false'):
                continue
            if len(sym) == 1 and sym.isupper():
                lines_set.add(sym)
            elif len(sym) == 1 and sym.islower():
                points_set.add(sym)

    # Convert steps
    steps = []
    for s in step_lines:
        steps.append({
            "lineNumber": s["id"],
            "text": s["statement"],
            "justification": s["justification"],
            "dependencies": s["refs"],
            "depth": s["depth"],
            "status": "?"
        })

    # Build declarations
    declarations = {
        "points": sorted(list(points_set), key=str.upper),
        "lines": sorted(list(lines_set))
    }

    # Use existing canvas or minimal canvas
    canvas = canvas_data if canvas_data else {
        "points": [],
        "segments": [],
        "rays": [],
        "circles": [],
        "angleMarks": [],
        "equalityGroups": []
    }

    return {
        "format": "euclid-proof",
        "version": "1.0.0",
        "program": "Euclid Elements Simulator (Python)",
        "metadata": {},
        "canvas": canvas,
        "exportedAt": datetime.now(timezone.utc).strftime("%Y-%m-%dT%H:%M:%SZ"),
        "proof": {
            "name": name,
            "premises": premises,
            "goal": goal,
            "declarations": declarations,
            "steps": steps
        }
    }


def main():
    ak = load_answer_key()
    props = ak["propositions"]

    # Map of proposition keys to file names
    prop_map = {
        "Prop.I.3": "Proposition I.3",
        "Prop.I.4": "Proposition I.4",
        "Prop.I.5": "Proposition I.5",
        "Prop.I.6": "Proposition I.6",
        "Prop.I.7": "Proposition I.7",
        "Prop.I.8": "Proposition I.8",
        "Prop.I.9": "Proposition I.9",
        "Prop.I.10": "Proposition I.10",
        "Prop.I.11": "Proposition I.11",
        "Prop.I.12": "Proposition I.12",
        "Prop.I.13": "Proposition I.13",
        "Prop.I.14": "Proposition I.14",
        "Prop.I.15": "Proposition I.15",
    }

    # Import real_proofs for verified proofs (answer key may have stubs)
    import sys
    sys.path.insert(0, os.path.join(WORKTREE, "scripts"))
    from real_proofs import ALL as REAL_PROOFS

    # Import canvas builders
    sys.path.insert(0, WORKTREE)
    from build_canvases import CANVAS_BUILDERS

    for prop_key, file_name in prop_map.items():
        print(f"\nProcessing {prop_key}...")

        # Get canvas data from builder if available
        canvas = None
        if file_name in CANVAS_BUILDERS:
            canvas = CANVAS_BUILDERS[file_name]()
            print(f"  Built canvas ({len(canvas['points'])} points)")
        else:
            existing = load_existing_euclid(file_name)
            canvas = existing["canvas"] if existing else None

        # Extract proposition number
        prop_num = int(prop_key.split(".")[-1])

        if prop_key == "Prop.I.6":
            i6_proof = load_i6_proof()
            euclid_data = verifier_to_euclid(i6_proof, canvas, "Prop.I.6")
            print(f"  Using working I.6 proof from test script ({len(i6_proof['lines'])} lines)")
        elif prop_key == "Prop.I.9":
            i9_proof = get_i9_proof()
            euclid_data = verifier_to_euclid(i9_proof, canvas, "Prop.I.9")
            print(f"  Using verified I.9 proof ({len(i9_proof['lines'])} lines)")
        elif prop_num in REAL_PROOFS and REAL_PROOFS[prop_num] is not None:
            # Use verified proof from real_proofs.py
            rp = REAL_PROOFS[prop_num]
            lines = rp.get("lines", [])
            non_given = [l for l in lines if l["justification"] != "Given"]
            if non_given:
                euclid_data = verifier_to_euclid(rp, canvas, prop_key)
                print(f"  {len(non_given)} proof steps from real_proofs.py")
            else:
                # Fall back to answer key
                verified = props.get(prop_key, {}).get("verified_proof", {})
                euclid_data = verifier_to_euclid(verified, canvas, prop_key)
                print(f"  Using answer key (stub)")
        else:
            verified = props.get(prop_key, {}).get("verified_proof", {})
            lines = verified.get("lines", [])
            non_given = [l for l in lines if l["justification"] != "Given"]
            euclid_data = verifier_to_euclid(verified, canvas, prop_key)
            if non_given:
                print(f"  {len(non_given)} proof steps from answer key")
            else:
                print(f"  WARNING: stub only")

        # Write the file
        out_path = os.path.join(SOLVED_DIR, f"{file_name}.euclid")
        with open(out_path, "w", encoding="utf-8") as f:
            json.dump(euclid_data, f, indent=2, ensure_ascii=False)
        print(f"  Written to {out_path}")

    print("\nDone!")


if __name__ == "__main__":
    main()
