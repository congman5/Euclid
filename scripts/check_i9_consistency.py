"""Check if I.9 hypotheses are contradictory."""
import sys
sys.path.insert(0, '.')

from verifier.e_consequence import ConsequenceEngine
from verifier.e_axioms import ALL_DIAGRAMMATIC_AXIOMS
from verifier.e_ast import *

eng = ConsequenceEngine(ALL_DIAGRAMMATIC_AXIOMS)
known = {
    Literal(Equals('a','b'), False),
    Literal(Equals('a','c'), False),
    Literal(Equals('b','c'), False),
    Literal(On('a','M'), True),
    Literal(On('b','M'), True),
    Literal(On('a','N'), True),
    Literal(On('c','N'), True),
    Literal(SameSide('c','b','M'), True),
    Literal(SameSide('b','c','N'), True),
}
variables = {'a': Sort.POINT, 'b': Sort.POINT, 'c': Sort.POINT,
             'M': Sort.LINE, 'N': Sort.LINE}
closure = eng.direct_consequences(known, variables)

neg_on_bM = Literal(On('b','M'), False)
on_bM = Literal(On('b','M'), True)
ss_bcM = Literal(SameSide('b','c','M'), True)
print(f"on(b,M) in closure: {on_bM in closure}")
print(f"neg on(b,M) in closure: {neg_on_bM in closure}")
print(f"same-side(b,c,M) in closure: {ss_bcM in closure}")
print(f"BOTTOM in closure: {BOTTOM in closure}")
print(f"Closure size: {len(closure)}")
