"""Debug the VarMapper for Prop16."""
import sys
_outf = open('debug_vm2_out.txt', 'w', encoding='utf-8')
def _print(*args, **kwargs):
    print(*args, file=_outf, flush=True, **kwargs)

from verifier.lean_translator import translate_lean_file
from verifier.lean_parser import parse_lean_file
from verifier.proof_synthesizer import ProofSynthesizer, _LEAN_PARAM_ORDER

tr = translate_lean_file('lean_reference/Prop16.lean')
lps = parse_lean_file('lean_reference/Prop16.lean')
synth = ProofSynthesizer(tr, lps[0])

_print("=== VarMapper state ===")
_print(f"  lean_to_elib: {synth.vm.lean_to_elib}")
_print(f"  elib_to_lean: {synth.vm.elib_to_lean}")
_print()

# Trace each tactic
for i, tac in enumerate(lps[0].tactics):
    _print(f"Tactic [{i}]: kind={tac.kind.name} rule={tac.rule_name} args={tac.rule_args} bound={tac.bound_vars}")
    if tac.rule_args:
        mapped = [synth.vm.mv(a) for a in tac.rule_args]
        _print(f"  mapped_args: {tac.rule_args} -> {mapped}")
    if tac.bound_vars:
        _print(f"  bound_vars: {tac.bound_vars}")
    if tac.kind.name == 'CASE_BRANCH':
        _print(f"  assertion_expr: {tac.assertion_expr}")
    _print()

_outf.close()
