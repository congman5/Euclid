"""Detailed profiling for I.22 synthesis bottlenecks."""
import sys, time, io
sys.stdout = io.TextIOWrapper(sys.stdout.buffer, encoding='utf-8')

from pathlib import Path
ROOT = Path(__file__).resolve().parent.parent.parent
if str(ROOT) not in sys.path:
    sys.path.insert(0, str(ROOT))

from verifier.lean_parser import parse_lean_file
from verifier.lean_translator import translate_lean_file
from verifier.proof_synthesizer import ProofSynthesizer
import verifier.proof_synthesizer as ps

# Patch _inject_metric_prereqs with per-hyp timing
_orig_inject = ProofSynthesizer._inject_metric_prereqs
def _timed_inject(self, thm, var_map):
    from verifier.e_ast import substitute_literal, Equals, literal_vars
    print(f"  _inject_metric_prereqs for {thm.name} ({len(thm.sequent.hypotheses)} hyps, known={len(self.known)})", flush=True)
    for hyp in thm.sequent.hypotheses:
        inst = substitute_literal(hyp, var_map)
        if inst in self.known:
            continue
        t0 = time.monotonic()
        tag = "metric" if inst.is_metric else ("diag" if inst.is_diagrammatic else "other")
        # Let the original code handle it by calling the original
    t0 = time.monotonic()
    result = _orig_inject(self, thm, var_map)
    dt = time.monotonic() - t0
    print(f"    total: {dt:.2f}s", flush=True)
    return result
ProofSynthesizer._inject_metric_prereqs = _timed_inject

# Patch _inject_diag_prereq with timing
_orig_diag = ProofSynthesizer._inject_diag_prereq
def _timed_diag(self, target):
    t0 = time.monotonic()
    result = _orig_diag(self, target)
    dt = time.monotonic() - t0
    if dt > 0.1:
        print(f"    [SLOW {dt:.1f}s] _inject_diag_prereq target={target}", flush=True)
    return result
ProofSynthesizer._inject_diag_prereq = _timed_diag

# Patch _ensure_neq with timing
_orig_neq = ProofSynthesizer._ensure_neq
def _timed_neq(self, pt1, pt2):
    t0 = time.monotonic()
    result = _orig_neq(self, pt1, pt2)
    dt = time.monotonic() - t0
    if dt > 0.1:
        print(f"    [SLOW {dt:.1f}s] _ensure_neq({pt1},{pt2})", flush=True)
    return result
ProofSynthesizer._ensure_neq = _timed_neq

# Patch _ensure_intersects with timing
_orig_inter = ProofSynthesizer._ensure_intersects
def _timed_inter(self, obj1, obj2):
    t0 = time.monotonic()
    result = _orig_inter(self, obj1, obj2)
    dt = time.monotonic() - t0
    if dt > 0.1:
        print(f"    [SLOW {dt:.1f}s] _ensure_intersects({obj1},{obj2}) known={len(self.known)}", flush=True)
    return result
ProofSynthesizer._ensure_intersects = _timed_inter

prop_num = int(sys.argv[1]) if len(sys.argv) > 1 else 22
lean_path = str(ROOT / "lean_reference" / f"Prop{prop_num}.lean")

proofs = parse_lean_file(lean_path)
lp = proofs[0] if proofs else None
tr = translate_lean_file(lean_path)

print(f"Synthesizing Prop I.{prop_num}...", flush=True)
t0 = time.monotonic()
sr = ps.synthesize_proof(tr, lp)
print(f"\nDone: {time.monotonic()-t0:.1f}s  success={sr.success}  steps={sr.step_count}")
for w in sr.warnings[:5]:
    print(f"  warn: {w}")
