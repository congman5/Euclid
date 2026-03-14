#!/usr/bin/env python3
"""
Validate every proposition in answer-key-book-I.txt.

For each Prop.I.N this script:
  1. Parses the System E proof steps from the answer key text file.
  2. Builds a proof JSON in the format expected by verify_e_proof_json.
  3. Runs the verifier and reports pass/fail with error details.
  4. Cross-checks hypotheses/conclusions against the E library sequent.
  5. Cross-checks hypotheses/conclusions against the JSON answer key.

Usage:
    python scripts/validate_answer_key.py
"""
from __future__ import annotations

import json
import re
import sys
import io

sys.stdout = io.TextIOWrapper(sys.stdout.buffer, encoding="utf-8")

from pathlib import Path
from typing import Any, Dict, List, Optional, Tuple

ROOT = Path(__file__).resolve().parent.parent

# ---------------------------------------------------------------------------
# Parser for answer-key-book-I.txt
# ---------------------------------------------------------------------------

_PROP_HEADER = re.compile(r"PROPOSITION I\.(\d+)")
_GIVEN_RE = re.compile(r"Given:\s*(.+)")
_PROVE_RE = re.compile(r"Prove:\s*(.+)")
_CONSTRUCT_RE = re.compile(r"Construct:\s*(.+)")
_STEP_RE = re.compile(
    r"(\d+)\.\s+\[([^\]]+)\]\s+\[refs?:\s*([^\]]*)\]\s*$"
)
_STEP_RESULT_RE = re.compile(r"→\s*(.+)")


def parse_answer_key(path: Path) -> Dict[int, dict]:
    """Parse answer-key-book-I.txt into per-proposition dicts.

    Returns {prop_num: {"given": [...], "prove": [...],
                        "construct": str, "steps": [...]}}
    """
    text = path.read_text(encoding="utf-8")
    lines = text.splitlines()

    props: Dict[int, dict] = {}
    cur_prop: Optional[int] = None
    in_system_e = False
    cur_given: List[str] = []
    cur_prove: List[str] = []
    cur_construct = ""
    cur_steps: List[dict] = []
    pending_step: Optional[dict] = None

    for line in lines:
        # Detect proposition header
        m = _PROP_HEADER.search(line)
        if m:
            # Save previous
            if cur_prop is not None:
                if pending_step:
                    cur_steps.append(pending_step)
                props[cur_prop] = {
                    "given": cur_given,
                    "prove": cur_prove,
                    "construct": cur_construct,
                    "steps": cur_steps,
                }
            cur_prop = int(m.group(1))
            in_system_e = False
            in_verified = False
            in_sketch = False
            cur_given = []
            cur_prove = []
            cur_construct = ""
            cur_steps = []
            pending_step = None
            continue

        if cur_prop is None:
            continue

        stripped = line.strip()

        # Detect "System E:" section
        if stripped == "System E:":
            in_system_e = True
            continue
        if stripped in ("System H:", "Dependencies:", ""):
            if stripped == "System H:":
                in_system_e = False
            continue

        # Track verified vs sketch sections
        if stripped.startswith("Verified Proof") or stripped.startswith("Sequent Verification"):
            in_verified = True
            in_sketch = False
            continue
        if stripped.startswith("Proof Sketch"):
            in_verified = False
            in_sketch = True
            continue
        if stripped.startswith("Q.E."):
            in_verified = False
            continue

        if in_system_e:
            # Given line
            mg = _GIVEN_RE.match(stripped)
            if mg:
                cur_given = [s.strip() for s in _split_top_level(mg.group(1))
                             if s.strip()]
                continue
            # Prove line
            mp = _PROVE_RE.match(stripped)
            if mp:
                cur_prove = [s.strip() for s in _split_top_level(mp.group(1))
                             if s.strip()]
                continue
            # Construct line
            mc = _CONSTRUCT_RE.match(stripped)
            if mc:
                cur_construct = mc.group(1).strip()
                continue

        # Only parse steps from verified proof section
        if not in_verified:
            continue

        # Step line: "   N. [justification]  [refs: ...]"
        ms = _STEP_RE.match(stripped)
        if ms:
            if pending_step:
                cur_steps.append(pending_step)
            step_num = int(ms.group(1))
            just = ms.group(2).strip()
            refs_str = ms.group(3).strip()
            refs = [int(r.strip()) for r in refs_str.split(",")
                    if r.strip()] if refs_str else []
            pending_step = {
                "num": step_num,
                "justification": just,
                "refs": refs,
                "statement": "",
            }
            continue

        # Step result line: "→ statement"
        mr = _STEP_RESULT_RE.match(stripped)
        if mr and pending_step:
            pending_step["statement"] = mr.group(1).strip()
            continue

    # Save last proposition
    if cur_prop is not None:
        if pending_step:
            cur_steps.append(pending_step)
        props[cur_prop] = {
            "given": cur_given,
            "prove": cur_prove,
            "construct": cur_construct,
            "steps": cur_steps,
        }

    return props


def _split_top_level(s: str) -> List[str]:
    """Split on commas not inside parentheses."""
    parts = []
    depth = 0
    cur = []
    for ch in s:
        if ch == "(":
            depth += 1
        elif ch == ")":
            depth -= 1
        if ch == "," and depth == 0:
            parts.append("".join(cur).strip())
            cur = []
        else:
            cur.append(ch)
    if cur:
        parts.append("".join(cur).strip())
    return parts


# ---------------------------------------------------------------------------
# Build proof JSON from parsed answer key
# ---------------------------------------------------------------------------

def build_proof_json(prop_num: int, data: dict) -> dict:
    """Build a proof JSON dict from parsed answer key data."""
    premises = data["given"]
    goal_parts = data["prove"]
    goal = ", ".join(goal_parts)

    lines = []
    # First line(s): Given premises
    lid = 1
    for prem in premises:
        lines.append({
            "id": lid,
            "depth": 0,
            "statement": prem,
            "justification": "Given",
            "refs": [],
        })
        lid += 1

    # Proof steps from answer key
    for step in data["steps"]:
        lines.append({
            "id": step["num"],
            "depth": 0,
            "statement": step["statement"],
            "justification": step["justification"],
            "refs": step["refs"],
        })

    return {
        "name": f"test-Prop.I.{prop_num}",
        "declarations": {"points": [], "lines": []},
        "premises": premises,
        "goal": goal,
        "lines": lines,
    }


# ---------------------------------------------------------------------------
# Cross-check against E library
# ---------------------------------------------------------------------------

def check_e_library(prop_num: int, data: dict) -> List[str]:
    """Compare answer key hypotheses/conclusions against E library."""
    from verifier.e_library import E_THEOREM_LIBRARY

    issues = []
    name = f"Prop.I.{prop_num}"
    thm = E_THEOREM_LIBRARY.get(name)
    if thm is None:
        issues.append(f"Not in E library")
        return issues

    lib_hyps = sorted(repr(h) for h in thm.sequent.hypotheses)
    ak_hyps = sorted(data["given"])

    if lib_hyps != ak_hyps:
        issues.append(
            f"Hypotheses mismatch:\n"
            f"    Library: {lib_hyps}\n"
            f"    AnsKey:  {ak_hyps}")

    lib_concls = sorted(repr(c) for c in thm.sequent.conclusions)
    ak_concls = sorted(data["prove"])

    if lib_concls != ak_concls:
        issues.append(
            f"Conclusions mismatch:\n"
            f"    Library: {lib_concls}\n"
            f"    AnsKey:  {ak_concls}")

    return issues


# ---------------------------------------------------------------------------
# Cross-check against JSON answer key
# ---------------------------------------------------------------------------

def check_json_key(prop_num: int, data: dict, json_data: dict) -> List[str]:
    """Compare answer key hypotheses/conclusions against JSON file."""
    issues = []
    name = f"Prop.I.{prop_num}"
    entry = json_data.get("propositions", {}).get(name)
    if entry is None:
        issues.append(f"Not in JSON answer key")
        return issues

    e_sys = entry.get("system_E", {})
    json_hyps = sorted(e_sys.get("hypotheses", []))
    ak_hyps = sorted(data["given"])

    if json_hyps != ak_hyps:
        issues.append(
            f"JSON hypotheses mismatch:\n"
            f"    JSON:   {json_hyps}\n"
            f"    AnsKey: {ak_hyps}")

    json_concls = sorted(e_sys.get("conclusions", []))
    ak_concls = sorted(data["prove"])

    if json_concls != ak_concls:
        issues.append(
            f"JSON conclusions mismatch:\n"
            f"    JSON:   {json_concls}\n"
            f"    AnsKey: {ak_concls}")

    return issues


# ---------------------------------------------------------------------------
# Main
# ---------------------------------------------------------------------------

def main():
    from verifier.unified_checker import verify_e_proof_json

    ak_path = ROOT / "answer-key-book-I.txt"
    json_path = ROOT / "answer_key_book_1.json"

    if not ak_path.exists():
        print(f"ERROR: {ak_path} not found")
        return 1

    # Parse answer key
    props = parse_answer_key(ak_path)
    print(f"Parsed {len(props)} propositions from answer key\n")

    # Load JSON answer key
    json_data = {}
    if json_path.exists():
        with open(json_path, "r", encoding="utf-8") as f:
            json_data = json.load(f)

    total = 0
    verify_pass = 0
    verify_fail = 0
    lib_issues = 0
    json_issues = 0
    failures: List[Tuple[int, str, List[str]]] = []

    for n in range(1, 49):
        total += 1
        data = props.get(n)
        if data is None:
            failures.append((n, "MISSING", ["Not found in answer key"]))
            verify_fail += 1
            continue

        has_steps = bool(data["steps"])

        # --- Cross-check E library ---
        e_issues = check_e_library(n, data)
        if e_issues:
            lib_issues += 1
            for iss in e_issues:
                failures.append((n, "E_LIB", [iss]))

        # --- Cross-check JSON key ---
        j_issues = check_json_key(n, data, json_data)
        if j_issues:
            json_issues += 1
            for iss in j_issues:
                failures.append((n, "JSON", [iss]))

        # --- Verify proof if steps exist ---
        if has_steps:
            pj = build_proof_json(n, data)
            try:
                r = verify_e_proof_json(pj)
                all_valid = all(
                    lr.valid for lr in r.line_results.values())
                if all_valid and r.accepted:
                    verify_pass += 1
                    print(f"  PASS: I.{n}")
                else:
                    verify_fail += 1
                    errs = []
                    for lid, lr in sorted(r.line_results.items()):
                        if not lr.valid:
                            errs.append(f"line {lid}: {lr.errors}")
                    if not r.accepted:
                        errs.extend(r.errors)
                    failures.append((n, "VERIFY", errs))
                    print(f"  FAIL: I.{n}")
                    for e in errs:
                        print(f"    {e}")
            except Exception as exc:
                verify_fail += 1
                failures.append((n, "EXCEPTION", [str(exc)]))
                print(f"  ERROR: I.{n}: {exc}")
        else:
            # No steps — just check library/json consistency
            verify_pass += 1
            print(f"  SKIP: I.{n} (no proof steps, lib/json checked)")

    # --- Summary ---
    print(f"\n{'=' * 70}")
    print(f"  Verify: {verify_pass}/{total} passed, {verify_fail} failed")
    print(f"  E library mismatches: {lib_issues}")
    print(f"  JSON key mismatches: {json_issues}")

    if failures:
        print(f"\n  Failures:")
        for n, kind, errs in failures:
            print(f"    I.{n} [{kind}]:")
            for e in errs:
                for line in e.split("\n"):
                    print(f"      {line}")
    print(f"{'=' * 70}")

    return 0 if not failures else 1


if __name__ == "__main__":
    sys.exit(main())
