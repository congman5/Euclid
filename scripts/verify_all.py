"""Verify all real proofs."""
import sys
sys.path.insert(0, '.')
from scripts.real_proofs import ALL
from verifier.unified_checker import verify_e_proof_json

for i in sorted(ALL.keys()):
    if ALL[i] is not None:
        r = verify_e_proof_json(ALL[i])
        status = 'PASS' if r.accepted else 'FAIL'
        print(f'I.{i}: {status}')
        if not r.accepted:
            for e in r.errors:
                print(f'  {e}')
