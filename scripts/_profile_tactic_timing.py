"""Profile per-tactic timing for a single proposition."""
import sys, time
sys.stdout.reconfigure(encoding='utf-8')
from verifier.lean_translator import translate_lean_file
from verifier.lean_parser import parse_lean_file
from verifier.proof_synthesizer import ProofSynthesizer

prop_num = int(sys.argv[1]) if len(sys.argv) > 1 else 16
f = f'lean_reference/Prop{prop_num}.lean'
tr = translate_lean_file(f)
lps = parse_lean_file(f)
lp = lps[0] if lps else None

ps = ProofSynthesizer(tr, lp)

orig_synth = ps._synth_tactic

def timed_synth(tac):
    t0 = time.time()
    orig_synth(tac)
    dt = time.time() - t0
    rule = tac.rule_name or tac.assertion_expr[:30] if tac.assertion_expr else ''
    print(f"  {tac.kind.name:20s} rule={rule:30s} {dt:7.2f}s")

ps._synth_tactic = timed_synth
t0 = time.time()
r = ps.synthesize()
total = time.time() - t0
print(f"\nTotal: {total:.1f}s  steps={r.step_count}  errors={len(r.errors)}  warnings={len(r.warnings)}")
if r.errors:
    for e in r.errors[:5]:
        print(f"  ERR: {e[:100]}")
if r.warnings:
    for w in r.warnings[:5]:
        print(f"  WARN: {w[:100]}")
