"""Test what the verifier can derive from specific known facts."""
import sys, io
sys.stdout = io.TextIOWrapper(sys.stdout.buffer, encoding='utf-8')

from verifier.e_parser import parse_literal_list
from verifier.e_consequence import ConsequenceEngine, TransferEngine, MetricEngine
from verifier.e_ast import Sort

sort_ctx = {}

# Test Prop.I.3: Can we use Segment transfer to get what we need?
print("=== Prop.I.3 — Testing Segment transfer ===")
known_strs = [
    "on(a, L)", "on(b, L)", "¬(a = b)", "cd < ab",
]
known = set()
for s in known_strs:
    for lit in parse_literal_list(s, sort_ctx):
        known.add(lit)

ce = ConsequenceEngine()
te = TransferEngine()
me = MetricEngine()

# What can we derive from the diagrammatic facts?
diag_known = {l for l in known if l.is_diagrammatic}
metric_known = {l for l in known if l.is_metric}
vars_ = ce._extract_variables(known)
print(f"Variables: {vars_}")
print(f"Known: {known}")

# Check Prop.I.2 hypothesis requirements
from verifier.e_library import E_THEOREM_LIBRARY
thm2 = E_THEOREM_LIBRARY["Prop.I.2"]
print(f"\nProp.I.2 hypotheses: {[str(h) for h in thm2.sequent.hypotheses]}")
print(f"Prop.I.2 conclusions: {[str(c) for c in thm2.sequent.conclusions]}")

# The issue: Prop.I.3 proof uses Prop.I.2 to get af = cd, 
# but Prop.I.2 requires on(b,L), on(c,L) etc.
# The proof has c,d as segment endpoints in "cd < ab" 
# but they're not declared as being on any line.
# 
# The real Euclid proof uses Segment Transfer directly:
# Given cd < ab, use Segment Transfer to place cd onto ab.
# This doesn't need Prop.I.2 at all.
print("\n=== Alternative: use segment transfer directly ===")
# Segment transfer 1: given on(a,L), on(b,L), a≠b, cd segment → 
# there exists f on L with af = cd
# But we need a let-point-on-line or similar construction
