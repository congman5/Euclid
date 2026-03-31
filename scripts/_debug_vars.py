"""Debug: does adding extra variables (l, alpha, beta) break derivation?"""
import sys; sys.path.insert(0,'.'); sys.stdout.reconfigure(encoding='utf-8')
from verifier.e_ast import *
from verifier.e_consequence import ConsequenceEngine

known = {
    Literal(On('a','L'), True),
    Literal(On('b','L'), True),
    Literal(Equals('a','b'), False),
    Literal(Equals('c','a'), False),
    Literal(On('c','M'), True),
    Literal(On('a','M'), True),
    Literal(On('c','N'), True),
    Literal(On('b','N'), True),
    Literal(Equals(AngleTerm('a','c','e'), AngleTerm('b','c','e')), True),
    Literal(SameSide('e','b','M'), True),
    Literal(SameSide('e','a','N'), True),
    Literal(Equals('c','e'), False),
    Literal(On('c','K'), True),
    Literal(On('e','K'), True),
    Literal(On('d','K'), True),
    Literal(On('d','L'), True),
}

# Same variables as before (9)
vars_small = {
    'a': Sort.POINT, 'b': Sort.POINT, 'c': Sort.POINT,
    'd': Sort.POINT, 'e': Sort.POINT,
    'L': Sort.LINE, 'M': Sort.LINE, 'N': Sort.LINE, 'K': Sort.LINE,
}

# Add extra variables like verifier has
vars_big = dict(vars_small)
vars_big['l'] = Sort.LINE
vars_big['\u03b1'] = Sort.CIRCLE
vars_big['\u03b2'] = Sort.CIRCLE

ce = ConsequenceEngine()

closure_small = ce.direct_consequences(known, vars_small)
aug_small = known | closure_small
target = Literal(Between('e','c','d'), False)
print(f'Small vars ({len(vars_small)}): {len(aug_small)} facts, neg btw(e,c,d): {target in aug_small}')

# Force cache invalidation
ce._ground_cache_key = None
ce._ground_cache = None
ce._compiled_cache_key = None
ce._compiled_cache = None

closure_big = ce.direct_consequences(known, vars_big)
aug_big = known | closure_big
print(f'Big vars ({len(vars_big)}): {len(aug_big)} facts, neg btw(e,c,d): {target in aug_big}')

# Check which axioms are being skipped due to grounding limit
from verifier.e_axioms import ALL_DIAGRAMMATIC_AXIOMS
for i, ax in enumerate(ALL_DIAGRAMMATIC_AXIOMS):
    schema = ce._clause_schema_vars(ax)
    pts = sum(1 for _, s in schema if s == Sort.POINT)
    lns = sum(1 for _, s in schema if s == Sort.LINE)
    crcs = sum(1 for _, s in schema if s == Sort.CIRCLE)
    est_small = (5**pts) * (4**lns) * (1**crcs) if crcs == 0 else (5**pts) * (4**lns) * (0**crcs)
    est_big = (5**pts) * (5**lns) * (2**crcs)
    if est_big > 50000 and est_small <= 50000:
        print(f'  Axiom {i}: skipped with big vars ({est_big}) but ok with small ({est_small})')
        for lit in ax.literals:
            print(f'    {lit}')
