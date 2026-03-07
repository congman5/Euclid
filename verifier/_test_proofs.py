"""Quick test: check all encoded proofs."""
from verifier.e_checker import check_proof
from verifier.e_proofs import E_PROOFS, get_proof

for name in sorted(E_PROOFS.keys()):
    result = check_proof(get_proof(name))
    tag = "PASS" if result.valid else "FAIL"
    print(f"{name}: {tag}")
    if not result.valid:
        for e in result.errors[:3]:
            print(f"  {e}")
