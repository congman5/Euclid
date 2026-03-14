#!/usr/bin/env python3
"""Quick script to verify all 48 named proofs via verify_named_proof."""
import sys, os, io
sys.stdout = io.TextIOWrapper(sys.stdout.buffer, encoding="utf-8")
sys.path.insert(0, os.path.join(os.path.dirname(__file__), ".."))

from verifier.unified_checker import verify_named_proof

passed = 0
failed = 0
for n in range(1, 49):
    name = f"Prop.I.{n}"
    r = verify_named_proof(name)
    if r.valid:
        passed += 1
        print(f"  PASS: {name}")
    else:
        failed += 1
        errs = "; ".join(r.errors[:3])
        print(f"  FAIL: {name} — {errs}")

print(f"\n{passed}/48 pass, {failed}/48 fail")
