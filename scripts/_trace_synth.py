"""Trace VarMapper and step generation for a proposition."""
import sys
sys.stdout.reconfigure(encoding='utf-8')
from verifier.lean_translator import translate_lean_file
from verifier.lean_parser import parse_lean_file
from verifier.proof_synthesizer import ProofSynthesizer

prop_num = int(sys.argv[1]) if len(sys.argv) > 1 else 28
f = f'lean_reference/Prop{prop_num}.lean'
tr = translate_lean_file(f)
lps = parse_lean_file(f)
lp = lps[0] if lps else None

ps = ProofSynthesizer(tr, lp)

# Monkeypatch _synth_tactic to trace
orig = ps._synth_tactic
def traced(tac):
    print(f"\n--- Tactic: {tac.kind.name} rule={tac.rule_name} args={tac.rule_args} bound={tac.bound_vars}")
    if ps.vm:
        print(f"    VarMapper: {dict(list(ps.vm.lean_to_elib.items())[:20])}")
    n_before = len(ps.steps)
    orig(tac)
    n_after = len(ps.steps)
    if n_after > n_before:
        for s in ps.steps[n_before:]:
            print(f"    -> L{s['lineNumber']}: {s['justification']:30s}  {s['text'][:80]}")
ps._synth_tactic = traced

r = ps.synthesize()
print(f"\nResult: steps={r.step_count} success={r.success} warns={len(r.warnings)}")
