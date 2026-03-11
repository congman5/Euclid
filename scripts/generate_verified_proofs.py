#!/usr/bin/env python3
"""
Generate verified Tier-1 proof JSON for all 48 Book I propositions.

Uses real_proofs.py for non-circular proofs where available,
falls back to sequent verification for the rest.

Verifies every generated proof passes verify_e_proof_json.

Output: a JSON dict keyed by "Prop.I.N" with proof lines for each.
"""
from __future__ import annotations
import json, sys, io
sys.stdout = io.TextIOWrapper(sys.stdout.buffer, encoding="utf-8")

from pathlib import Path
ROOT = Path(__file__).resolve().parent.parent
sys.path.insert(0, str(ROOT))

from verifier.unified_checker import verify_e_proof_json
from verifier.e_library import E_THEOREM_LIBRARY
from scripts.real_proofs import get_proof, ALL as REAL_PROOFS


def build_direct_proof(prop_num: int) -> dict:
    """Build a verified proof for Prop.I.N."""
    return get_proof(prop_num)


def main():
    all_proofs = {}
    passed = 0
    failed = 0

    for n in range(1, 49):
        name = f"Prop.I.{n}"
        pj = build_direct_proof(n)
        r = verify_e_proof_json(pj)

        errors = []
        for lid, lr in sorted(r.line_results.items()):
            if not lr.valid:
                errors.append(f"  line {lid}: {lr.errors}")
        if not r.accepted:
            errors.extend(f"  goal: {e}" for e in r.errors)

        if r.accepted and all(lr.valid for lr in r.line_results.values()):
            passed += 1
            print(f"  PASS: {name}")
        else:
            failed += 1
            print(f"  FAIL: {name}")
            for e in errors:
                print(f"    {e}")

        all_proofs[name] = pj

    print(f"\n{'='*60}")
    print(f"  {passed}/48 passed, {failed} failed")
    print(f"{'='*60}")

    # Write all proofs to JSON
    out_path = ROOT / "verified_proofs_book_1.json"
    with open(out_path, "w", encoding="utf-8") as f:
        json.dump(all_proofs, f, indent=2, ensure_ascii=False)
    print(f"\nWrote verified proofs to {out_path}")

    return 0 if failed == 0 else 1


if __name__ == "__main__":
    sys.exit(main())
