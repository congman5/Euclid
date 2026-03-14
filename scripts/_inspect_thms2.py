"""Detailed theorem investigation for rewriting proofs."""
import sys, io
sys.stdout = io.TextIOWrapper(sys.stdout.buffer, encoding='utf-8')

from verifier.e_library import E_THEOREM_LIBRARY

for name in ["Prop.I.1", "Prop.I.2", "Prop.I.3", "Prop.I.9"]:
    thm = E_THEOREM_LIBRARY.get(name)
    if thm:
        print(f"\n=== {name} ===")
        print(f"  Hypotheses:")
        for h in thm.sequent.hypotheses:
            print(f"    {h}  (diag={h.is_diagrammatic}, metric={h.is_metric})")
        print(f"  Conclusions:")
        for c in thm.sequent.conclusions:
            print(f"    {c}  (diag={c.is_diagrammatic}, metric={c.is_metric})")
