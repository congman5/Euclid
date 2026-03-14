"""Check what the metric engine derives from I.9's known set."""
import sys, io
sys.stdout = io.TextIOWrapper(sys.stdout.buffer, encoding='utf-8')
from verifier.e_parser import parse_literal_list
from verifier.e_ast import Sort, Literal, Equals, SegmentTerm
from verifier.e_metric import MetricEngine

sort_ctx = {}

# Metric facts from I.9 context
metric_strs = [
    "¬(a = b)", "¬(a = c)", "¬(b = c)",
    "ad = ab", "af = ab", "ad = af",
    "¬(d = f)",
    "df = de", "df = fe", "¬(e = d)", "¬(e = f)",
    "de = fe", "ae = ae",
    "∠dae = ∠fae", "∠ade = ∠afe", "∠aed = ∠aef", "△ade = △afe",
]

metric_known = set()
for s in metric_strs:
    metric_known.update(parse_literal_list(s, sort_ctx))

engine = MetricEngine()
expanded = engine.process_literals(metric_known)

# Check point disequalities
diseq_facts = [l for l in expanded if not l.polarity 
               and isinstance(l.atom, Equals)
               and isinstance(l.atom.left, str)]
print("Point disequalities derived:")
for f in sorted(diseq_facts, key=str):
    print(f"  {f}")

# Check if ¬(a = d) and ¬(a = f) are there
for q in ["¬(a = d)", "¬(a = f)", "¬(a = e)"]:
    lits = parse_literal_list(q, sort_ctx)
    for lit in lits:
        print(f"  {lit}: {'✓' if lit in expanded else '✗'}")
