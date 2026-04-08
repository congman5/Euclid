"""Detailed profiler for _inject_metric_prereqs inner paths."""
import sys, time, io
sys.stdout = io.TextIOWrapper(sys.stdout.buffer, encoding='utf-8')

from pathlib import Path
ROOT = Path(__file__).resolve().parent.parent.parent
if str(ROOT) not in sys.path:
    sys.path.insert(0, str(ROOT))

from verifier.proof_synthesizer import ProofSynthesizer
from verifier.e_ast import substitute_literal, Equals, literal_vars, On, Between, Intersects, Literal
import verifier.proof_synthesizer as ps

# Detailed timing for _inject_metric_prereqs inner paths
_orig_inject = ProofSynthesizer._inject_metric_prereqs
def _detailed_inject(self, thm, var_map):
    print(f"  _inject_metric_prereqs for {thm.name} ({len(thm.sequent.hypotheses)} hyps, known={len(self.known)})", flush=True)
    for hyp in thm.sequent.hypotheses:
        inst = substitute_literal(hyp, var_map)
        if inst in self.known:
            continue
        if (not inst.polarity and isinstance(inst.atom, Equals)
                and isinstance(inst.atom.left, str)
                and inst.atom.left == inst.atom.right):
            continue
        tag = "metric" if inst.is_metric else ("diag" if inst.is_diagrammatic else "neq/other")
        if not inst.polarity and isinstance(inst.atom, Equals):
            tag = "neq"
        print(f"    hyp not in known: {tag}: {inst}", flush=True)
    t0 = time.monotonic()
    result = _orig_inject(self, thm, var_map)
    dt = time.monotonic() - t0
    if dt > 0.5:
        print(f"    TOTAL: {dt:.1f}s", flush=True)
    return result
ProofSynthesizer._inject_metric_prereqs = _detailed_inject

# Time individual sub-methods
for method_name in ['_ensure_neq', '_inject_diag_prereq']:
    _orig = getattr(ProofSynthesizer, method_name)
    def _make_wrapper(name, orig):
        def wrapper(self, *args, **kwargs):
            t0 = time.monotonic()
            result = orig(self, *args, **kwargs)
            dt = time.monotonic() - t0
            if dt > 0.3:
                print(f"      [{dt:.1f}s] {name} args={args[:2]}", flush=True)
            return result
        return wrapper
    setattr(ProofSynthesizer, method_name, _make_wrapper(method_name, _orig))

# Time _finish
_orig_finish = ProofSynthesizer._finish
def _timed_finish(self, *args, **kwargs):
    t0 = time.monotonic()
    result = _orig_finish(self, *args, **kwargs)
    dt = time.monotonic() - t0
    if dt > 0.3:
        print(f"  [SLOW {dt:.1f}s] _finish known={len(self.known)}", flush=True)
    return result
ProofSynthesizer._finish = _timed_finish

prop_num = int(sys.argv[1]) if len(sys.argv) > 1 else 35
lean_path = str(ROOT / "lean_reference" / f"Prop{prop_num}.lean")

from verifier.lean_parser import parse_lean_file
from verifier.lean_translator import translate_lean_file

proofs = parse_lean_file(lean_path)
lp = proofs[0] if proofs else None
tr = translate_lean_file(lean_path)

print(f"Synthesizing Prop I.{prop_num}...", flush=True)
t0 = time.monotonic()
sr = ps.synthesize_proof(tr, lp)
print(f"\nDone: {time.monotonic()-t0:.1f}s  success={sr.success}  steps={sr.step_count}")
for w in sr.warnings[:8]:
    print(f"  warn: {w}")
