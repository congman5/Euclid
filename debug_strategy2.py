"""Debug which strategy is used for each theorem call in Prop16 (v2)."""
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

# Patch _build_thm_varmap to just trace the final result
_orig_build = synth._build_thm_varmap.__func__
def _traced_build(self, thm, tac):
    import types
    se_name = thm.name if hasattr(thm, 'name') else '?'
    vm = _orig_build(self, thm, tac)
    _print(f"THM {se_name}: args={tac.rule_args} bound={tac.bound_vars}")
    _print(f"  FINAL var_map={vm}")
    for h in thm.sequent.hypotheses:
        inst = substitute_literal(h, vm)
        in_known = inst in self.known
        _print(f"  hyp: {literal_to_text(inst)} {'OK' if in_known else 'MISS'}")
    for c in thm.sequent.conclusions:
        inst = substitute_literal(c, vm)
        _print(f"  conc: {literal_to_text(inst)}")
    _print()
    return vm

import types
synth._build_thm_varmap = types.MethodType(_traced_build, synth)
synth.synthesize()
_outf.close()
