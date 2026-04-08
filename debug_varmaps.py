"""Debug var_maps for Prop16 theorem applications."""
import sys, io
_outf = open('debug_vm_out.txt', 'w', encoding='utf-8')
def _print(*args, **kwargs):
    print(*args, file=_outf, flush=True, **kwargs)
from verifier.lean_translator import translate_lean_file
from verifier.lean_parser import parse_lean_file, LeanTactic, TacticKind
from verifier.proof_synthesizer import ProofSynthesizer
from verifier.e_library import E_THEOREM_LIBRARY

tr = translate_lean_file('lean_reference/Prop16.lean')
lps = parse_lean_file('lean_reference/Prop16.lean')
synth = ProofSynthesizer(tr, lps[0])

# Hook into _apply_theorem to capture var_maps
_orig = synth._apply_theorem
def _debug_apply_theorem(tac, mp):
    from verifier.lean_mapping import lookup_rule
    se_name = mp.system_e_name if mp else tac.rule_name
    thm = synth.avail.get(se_name)
    if thm:
        vm = synth._build_thm_varmap(thm, tac)
        _print(f"THM {se_name}: args={tac.rule_args} bound={tac.bound_vars}")
        _print(f"  var_map={vm}")
        # Show instantiated hypotheses
        from verifier.e_ast import substitute_literal
        from verifier.lean_to_euclid_json import literal_to_text
        for h in thm.sequent.hypotheses:
            inst = substitute_literal(h, vm)
            in_known = inst in synth.known
            _print(f"  hyp: {literal_to_text(inst)} {'OK' if in_known else 'MISSING'}")
        for c in thm.sequent.conclusions:
            inst = substitute_literal(c, vm)
            _print(f"  conc: {literal_to_text(inst)}")
    _orig(tac, mp)

synth._apply_theorem = _debug_apply_theorem
sr = synth.synthesize()
_print(f"\nSteps: {sr.step_count}")
_outf.close()
