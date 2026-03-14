"""
Diagnose sketch proof failures for all 48 propositions.

Parses the "Proof Sketch" sections from answer-key-book-I.txt,
builds proof JSON from them, runs the verifier, and categorizes
the error types.
"""
import json, sys, io, re
sys.stdout = io.TextIOWrapper(sys.stdout.buffer, encoding="utf-8")
sys.path.insert(0, ".")

from pathlib import Path
from typing import Dict, List, Optional
from collections import Counter

ROOT = Path(__file__).resolve().parent.parent


def _split_top_level(s):
    parts, depth, cur = [], 0, []
    for ch in s:
        if ch == "(": depth += 1
        elif ch == ")": depth -= 1
        if ch == "," and depth == 0:
            parts.append("".join(cur).strip()); cur = []
        else: cur.append(ch)
    if cur: parts.append("".join(cur).strip())
    return parts


_PROP_HEADER = re.compile(r"PROPOSITION I\.(\d+)")
_GIVEN_RE = re.compile(r"Given:\s*(.+)")
_PROVE_RE = re.compile(r"Prove:\s*(.+)")
_STEP_RE = re.compile(r"(\d+)\.\s+\[([^\]]+)\]\s+\[refs?:\s*([^\]]*)\]\s*$")
_STEP_RESULT_RE = re.compile(r"\u2192\s*(.+)")


def parse_sketches(path: Path) -> Dict[int, dict]:
    text = path.read_text(encoding="utf-8")
    lines = text.splitlines()
    props = {}
    cur_prop = None
    in_system_e = False
    in_sketch = False
    cur_given, cur_prove, cur_steps = [], [], []
    pending_step = None

    for line in lines:
        m = _PROP_HEADER.search(line)
        if m:
            if cur_prop is not None:
                if pending_step: cur_steps.append(pending_step)
                props[cur_prop] = {"given": cur_given, "prove": cur_prove, "steps": cur_steps}
            cur_prop = int(m.group(1))
            in_system_e = False; in_sketch = False
            cur_given, cur_prove, cur_steps = [], [], []
            pending_step = None
            continue
        if cur_prop is None: continue
        stripped = line.strip()

        if stripped == "System E:": in_system_e = True; continue
        if stripped in ("System H:", "Dependencies:", ""):
            if stripped == "System H:": in_system_e = False
            continue
        if stripped.startswith("Verified Proof"):
            in_sketch = False; continue
        if stripped.startswith("Proof Sketch"):
            in_sketch = True; continue
        if stripped.startswith("Q.E."):
            in_sketch = False; continue

        if in_system_e:
            mg = _GIVEN_RE.match(stripped)
            if mg:
                cur_given = [s.strip() for s in _split_top_level(mg.group(1))]
                continue
            mp = _PROVE_RE.match(stripped)
            if mp:
                cur_prove = [s.strip() for s in _split_top_level(mp.group(1))]
                continue

        if not in_sketch: continue

        ms = _STEP_RE.match(stripped)
        if ms:
            if pending_step: cur_steps.append(pending_step)
            refs_str = ms.group(3).strip()
            refs = [int(r.strip()) for r in refs_str.split(",") if r.strip()] if refs_str else []
            pending_step = {"num": int(ms.group(1)), "justification": ms.group(2).strip(),
                           "refs": refs, "statement": ""}
            continue
        mr = _STEP_RESULT_RE.match(stripped)
        if mr and pending_step:
            pending_step["statement"] = mr.group(1).strip()
            continue

    if cur_prop is not None:
        if pending_step: cur_steps.append(pending_step)
        props[cur_prop] = {"given": cur_given, "prove": cur_prove, "steps": cur_steps}
    return props


def build_proof_json(n, data):
    lines = []
    for step in data["steps"]:
        lines.append({"id": step["num"], "depth": 0,
                      "statement": step["statement"],
                      "justification": step["justification"],
                      "refs": step["refs"]})
    return {
        "name": f"Prop.I.{n}",
        "declarations": {"points": [], "lines": []},
        "premises": data["given"],
        "goal": ", ".join(data["prove"]),
        "lines": lines,
    }


def main():
    from verifier.unified_checker import verify_e_proof_json

    path = ROOT / "answer-key-book-I.txt"
    props = parse_sketches(path)
    print(f"Parsed {len(props)} propositions\n")

    error_cats = Counter()
    for n in range(1, 49):
        data = props.get(n)
        if not data or not data["steps"]:
            print(f"I.{n:2d}: NO SKETCH STEPS")
            error_cats["no_steps"] += 1
            continue

        pj = build_proof_json(n, data)
        try:
            r = verify_e_proof_json(pj)
        except Exception as exc:
            print(f"I.{n:2d}: EXCEPTION: {exc}")
            error_cats["exception"] += 1
            continue

        all_valid = all(lr.valid for lr in r.line_results.values())
        if all_valid and r.accepted:
            print(f"I.{n:2d}: PASS ({len(data['steps'])} steps)")
            error_cats["pass"] += 1
        else:
            errs = []
            for lid, lr in sorted(r.line_results.items()):
                if not lr.valid:
                    for e in lr.errors:
                        if "Parse error" in e:
                            error_cats["parse_error"] += 1
                            errs.append(f"  L{lid}: PARSE: {e[:80]}")
                        elif "Unknown justification" in e:
                            error_cats["unknown_just"] += 1
                            errs.append(f"  L{lid}: UNKNOWN_JUST: {e[:80]}")
                        elif "hypothesis not met" in e:
                            error_cats["hyp_not_met"] += 1
                            errs.append(f"  L{lid}: HYP_NOT_MET: {e[:80]}")
                        elif "not a direct consequence" in e or "not a consequence" in e:
                            error_cats["consequence_fail"] += 1
                            errs.append(f"  L{lid}: CONSEQUENCE: {e[:80]}")
                        elif "not derivable" in e:
                            error_cats["transfer_fail"] += 1
                            errs.append(f"  L{lid}: TRANSFER: {e[:80]}")
                        elif "prerequisite not met" in e:
                            error_cats["prereq_fail"] += 1
                            errs.append(f"  L{lid}: PREREQ: {e[:80]}")
                        elif "does not match" in e:
                            error_cats["pattern_fail"] += 1
                            errs.append(f"  L{lid}: PATTERN: {e[:80]}")
                        else:
                            error_cats["other"] += 1
                            errs.append(f"  L{lid}: OTHER: {e[:80]}")
            if not r.accepted:
                errs.append(f"  GOAL: {r.errors}")
            print(f"I.{n:2d}: FAIL ({len(data['steps'])} steps, {len(errs)} errors)")
            for e in errs[:8]:
                print(f"    {e}")
            if len(errs) > 8:
                print(f"    ... and {len(errs)-8} more")

    print(f"\n{'='*60}")
    print("Error categories:")
    for cat, count in error_cats.most_common():
        print(f"  {cat:20s}: {count}")
    print(f"{'='*60}")


if __name__ == "__main__":
    main()
