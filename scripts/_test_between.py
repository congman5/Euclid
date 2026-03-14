import sys, io
sys.stdout = io.TextIOWrapper(sys.stdout.buffer, encoding='utf-8')
from verifier.e_consequence import ConsequenceEngine
from verifier.e_parser import parse_literal_list
from verifier.e_ast import Sort

sort_ctx = {}
ce = ConsequenceEngine()

known = set()
for s in ["between(b, d, a)", "on(a, M)", "on(b, M)"]:
    for lit in parse_literal_list(s, sort_ctx):
        known.add(lit)

vars_ = ce._extract_variables(known)
derived = ce.direct_consequences(known, vars_)
print("Known:", known)
print("Derived:", derived)

# Check if between(a,d,b) is in derived
target = list(parse_literal_list("between(a, d, b)", sort_ctx))
for t in target:
    print(f"between(a,d,b) in derived: {t in derived}")
    print(f"between(a,d,b) in known|derived: {t in known or t in derived}")
