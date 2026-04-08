"""Debug which strategy is used for each theorem call in Prop16."""
import sys
_outf = open('debug_strategy_out.txt', 'w', encoding='utf-8')
def _print(*args, **kwargs):
    print(*args, file=_outf, flush=True, **kwargs)

from verifier.lean_translator import translate_lean_file
from verifier.lean_parser import parse_lean_file
from verifier.proof_synthesizer import ProofSynthesizer, _LEAN_PARAM_ORDER
from verifier.e_ast import substitute_literal, Equals, Literal
from verifier.lean_to_euclid_json import literal_to_text

tr = translate_lean_file('lean_reference/Prop16.lean')
lps = parse_lean_file('lean_reference/Prop16.lean')
synth = ProofSynthesizer(tr, lps[0])

# Patch _build_thm_varmap to trace strategy
_orig_build = synth._build_thm_varmap.__func__
def _traced_build(self, thm, tac):
    from verifier.lean_parser import extract_prop_number
    se_name = thm.name if hasattr(thm, 'name') else '?'
    _pn = extract_prop_number(tac.rule_name)

    # Check table path
    if tac.rule_args and _pn and _pn in _LEAN_PARAM_ORDER:
        param_order = _LEAN_PARAM_ORDER[_pn]
        direct_vm = {}
        for i, (elib_var, _sort) in enumerate(param_order):
            if i < len(tac.rule_args):
                arg = tac.rule_args[i]
                if arg.startswith('(') or '\u2500' in arg or '|' in arg:
                    continue
                actual = self.vm.mv(arg) if self.vm else arg.lower()
                if elib_var not in direct_vm:
                    direct_vm[elib_var] = actual
        if tac.bound_vars and thm.sequent.exists_vars:
            fresh_bounds = self._fresh_bound_vars(tac.bound_vars) if self.vm else [v.lower() for v in tac.bound_vars]
            for j, (ev_name, _) in enumerate(thm.sequent.exists_vars):
                if j < len(fresh_bounds):
                    direct_vm[ev_name] = fresh_bounds[j]
        vc = self._validate_conclusions(thm, direct_vm)
        _print(f"TABLE CHECK {se_name}: args={tac.rule_args}")
        _print(f"  table_vm={direct_vm}")
        _print(f"  validate_conclusions={vc}")
        # Check for distinctness collisions
        for h in thm.sequent.hypotheses:
            if not h.polarity and isinstance(h.atom, Equals):
                left_val = direct_vm.get(h.atom.left, h.atom.left)
                right_val = direct_vm.get(h.atom.right, h.atom.right)
                if left_val == right_val:
                    _print(f"  COLLISION: {h} maps to {left_val}={right_val}")

    vm = _orig_build(self, thm, tac)
    _print(f"FINAL {se_name}: var_map={vm}")
    _print()
    return vm

import types
synth._build_thm_varmap = types.MethodType(_traced_build, synth)

# Also need to run synthesize
synth.synthesize()
_outf.close()
