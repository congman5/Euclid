"""
Test all 48 expanded System E proofs through the actual e_checker.

Unlike test_all_48_proofs.py (which builds trivial Given + single
theorem-application proofs from sequent definitions), this test
exercises the real multi-step ProofStep sequences in e_proofs.py
by passing each EProof to ``e_checker.check_proof()`` with the
cumulative theorem library (all earlier propositions available).
"""
import pytest

from verifier.e_proofs import get_proof
from verifier.e_checker import check_proof
from verifier.e_library import get_theorems_up_to


_PROP_NAMES = [f"Prop.I.{n}" for n in range(1, 49)]


@pytest.mark.parametrize("prop_name", _PROP_NAMES, ids=_PROP_NAMES)
def test_e_checker_proof(prop_name: str):
    """Verify expanded proof through the System E checker."""
    proof = get_proof(prop_name)
    theorems = get_theorems_up_to(prop_name)
    result = check_proof(proof, theorems)

    # Collect errors for readable failure message
    errors = []
    if not result.valid:
        errors.extend(result.errors)
    if result.errors:
        for e in result.errors:
            if e not in errors:
                errors.append(e)

    assert result.valid, (
        f"{prop_name} failed e_checker verification:\n"
        + "\n".join(f"  {e}" for e in errors)
    )
