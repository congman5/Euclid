#!/usr/bin/env python3
"""Verify all .euclid proof files against verify_e_proof_json.

Usage:
    python verify_euclid_files.py [--dir solved_proofs] [--prop 16]
"""
import json
import sys
import os
import glob
import argparse

# Add parent dir to path so verifier module is importable
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))

from verifier.unified_checker import verify_e_proof_json


def verify_file(filepath):
    """Verify a single .euclid file. Returns (name, accepted, errors)."""
    with open(filepath, "r", encoding="utf-8") as f:
        data = json.load(f)

    result = verify_e_proof_json(data)

    name = data.get("proof", {}).get("name", os.path.basename(filepath))
    errors = list(result.errors)
    for lid, lr in sorted(result.line_results.items()):
        if not lr.valid:
            for e in lr.errors:
                errors.append(f"  Line {lid}: {e}")

    return name, result.accepted, errors


def main():
    # Force UTF-8 output for Unicode math symbols
    import io
    sys.stdout = io.TextIOWrapper(sys.stdout.buffer, encoding="utf-8", errors="replace")
    sys.stderr = io.TextIOWrapper(sys.stderr.buffer, encoding="utf-8", errors="replace")

    parser = argparse.ArgumentParser()
    parser.add_argument("--dir", default="solved_proofs",
                        help="Directory containing .euclid files")
    parser.add_argument("--prop", type=int, default=None,
                        help="Verify only this proposition number")
    parser.add_argument("--unsolved", action="store_true",
                        help="Also check unsolved_proofs directory")
    args = parser.parse_args()

    dirs = [args.dir]
    if args.unsolved:
        dirs.append("unsolved_proofs")

    files = []
    for d in dirs:
        pattern = os.path.join(d, "Proposition I.*.euclid")
        files.extend(sorted(glob.glob(pattern)))

    if args.prop is not None:
        files = [f for f in files
                 if f"Proposition I.{args.prop}." in f]

    if not files:
        print("No .euclid files found.")
        return

    passed = 0
    failed = 0
    for fp in files:
        name, accepted, errors = verify_file(fp)
        status = "PASS" if accepted else "FAIL"
        if accepted:
            passed += 1
            print(f"  {status}  {name} ({fp})")
        else:
            failed += 1
            print(f"  {status}  {name} ({fp})")
            for e in errors[:5]:
                print(f"         {e}")

    print(f"\n{'='*50}")
    print(f"Results: {passed} passed, {failed} failed, {passed+failed} total")


if __name__ == "__main__":
    main()
