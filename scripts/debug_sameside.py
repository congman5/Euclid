"""Debug whether same-side(b, a, M) is derivable in I.10's context at line 10."""
import json, sys, io
sys.stdout = io.TextIOWrapper(sys.stdout.buffer, encoding='utf-8')
from verifier.e_parser import parse_literal_list
from verifier.e_consequence import ConsequenceEngine
from verifier.e_axioms import ALL_DIAGRAMMATIC_AXIOMS
from verifier.e_ast import SameSide, On, Literal, Sort

sort_ctx = {}

# Known facts at line 10 in Prop.I.10:
# Premises: on(a, L), on(b, L), ¬(a = b)
# From I.1: ab = ac, ab = bc, ¬(c = a), ¬(c = b)  (c = equilateral triangle point)
# CN1: ac = bc
# M1: ¬(c = a), ¬(c = b)
# let-line: on(c, M), on(a, M)
# let-line: on(c, N), on(b, N)
known_strs = [
    "on(a, L)", "on(b, L)", "¬(a = b)",
    "¬(c = a)", "¬(c = b)",
    "on(c, M)", "on(a, M)",
    "on(c, N)", "on(b, N)",
]
known = set()
for s in known_strs:
    known.update(parse_literal_list(s, sort_ctx))

# Check variables
variables = {
    'a': Sort.POINT, 'b': Sort.POINT, 'c': Sort.POINT,
    'L': Sort.LINE, 'M': Sort.LINE, 'N': Sort.LINE,
}

# Run consequence engine
engine = ConsequenceEngine(ALL_DIAGRAMMATIC_AXIOMS)
closure = engine.direct_consequences(known, variables)

# Look for same-side facts
ss_facts = [l for l in closure if isinstance(l.atom, SameSide)]
print("Same-side facts derived:")
for f in sorted(ss_facts, key=str):
    print(f"  {f}")

# Check specific queries
query = Literal(SameSide("b", "a", "M"), polarity=True)
print(f"\nsame-side(b, a, M) in closure: {query in closure}")
print(f"same-side(b, a, M) in known: {query in known}")

# Check if b is on M
query2 = Literal(On("b", "M"), polarity=True)
query2_neg = Literal(On("b", "M"), polarity=False)
print(f"\non(b, M) in closure: {query2 in closure}")
print(f"¬on(b, M) in closure: {query2_neg in closure}")

# Also check is_consequence
result = engine.is_consequence(known, query)
print(f"\nis_consequence(known, same-side(b,a,M)): {result}")
