"""Debug which synthesis steps are slow for a given proposition."""
import sys, time, io
sys.stdout = io.TextIOWrapper(sys.stdout.buffer, encoding='utf-8')

from pathlib import Path
ROOT = Path(__file__).resolve().parent.parent.parent
if str(ROOT) not in sys.path:
    sys.path.insert(0, str(ROOT))

from verifier.lean_parser import parse_lean_file
from verifier.lean_translator import translate_lean_file
from verifier.proof_synthesizer import ProofSynthesizer, _LEAN_PARAM_ORDER
import verifier.proof_synthesizer as ps

# Monkey-patch multiple methods to find the bottleneck
for method_name in ['_build_thm_varmap', '_finish', '_inject_metric_prereqs',
                    '_ensure_neq', '_ensure_intersects', '_apply_theorem',
                    '_apply_construction']:
    _orig = getattr(ProofSynthesizer, method_name)
    def _make_wrapper(name, orig):
        def wrapper(self, *args, **kwargs):
            t0 = time.monotonic()
            result = orig(self, *args, **kwargs)
            dt = time.monotonic() - t0
            if dt > 0.5:
                extra = ""
                if args and hasattr(args[0], 'rule_name'):
                    extra = f" rule={args[0].rule_name}"
                print(f"  [SLOW {dt:.1f}s] {name}{extra}", flush=True)
            return result
        return wrapper
    setattr(ProofSynthesizer, method_name, _make_wrapper(method_name, _orig))

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

