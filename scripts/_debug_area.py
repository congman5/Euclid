import json, sys, io
sys.stdout = io.TextIOWrapper(sys.stdout.buffer, encoding='utf-8')

from verifier.e_parser import parse_literal_list
from verifier.e_consequence import ConsequenceEngine
from verifier.e_transfer import TransferEngine
from verifier.e_ast import Sort

sort_ctx = {}
known = set()
for s in ["on(a, M)", "on(b, M)", "between(a, d, b)", "\u00ac(a = b)", "\u00ac(a = d)", "\u00ac(b = d)"]:
    for lit in parse_literal_list(s, sort_ctx):
        known.add(lit)

print("Initial known:", known)

# Compute diagrammatic closure
ce = ConsequenceEngine()
variables = ce._extract_variables(known)
print("Variables:", variables)
closure = ce.direct_consequences(known, variables)
known.update(closure)

# Check on(d,M) in closure
target_on_d_M = list(parse_literal_list("on(d, M)", sort_ctx))
for t in target_on_d_M:
    print(f"on(d,M) in known: {t in known}")

diagram_known = {l for l in known if l.is_diagrammatic}
metric_known = {l for l in known if l.is_metric}
print(f"\nDiagram known ({len(diagram_known)} items)")
print(f"Metric known ({len(metric_known)} items)")

# Apply transfers
te = TransferEngine()
derived = te.apply_transfers(diagram_known, metric_known, variables)
print(f"\nDerived ({len(derived)} items):")
for d in sorted(str(x) for x in derived):
    print(f"  {d}")

# Check for the target
target = list(parse_literal_list("(\u25b3adc + \u25b3cdb) = \u25b3acb", sort_ctx))
print("\nTarget:", target)
for t in target:
    print(f"  in derived: {t in derived}")
    print(f"  in known: {t in known}")
