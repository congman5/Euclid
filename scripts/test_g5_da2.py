"""Test G5 axiom for L!=N derivation and DA2 firing."""
import sys, os
sys.stdout.reconfigure(encoding='utf-8')
sys.path.insert(0, os.path.dirname(os.path.dirname(os.path.abspath(__file__))))

from verifier.e_ast import *
from verifier.e_consequence import ConsequenceEngine
from verifier.e_axioms import GENERALITY_AXIOMS, ALL_DIAGRAMMATIC_AXIOMS

# Test 1: Does G5 derive L!=N from on(c,L) and not-on(c,N)?
known = set()
known.add(Literal(On('c','L')))
known.add(Literal(On('c','N'), polarity=False))
variables = {'c': Sort.POINT, 'L': Sort.LINE, 'N': Sort.LINE}
ce = ConsequenceEngine(GENERALITY_AXIOMS)
closure = ce.direct_consequences(known, variables)
print("Test 1 - G5 alone:")
print(f"  L!=N: {Literal(Equals('L','N'), polarity=False) in closure}")
for c in closure:
    print(f"  {c}")

# Test 2: Full diagrammatic closure with all I.7 facts
print("\nTest 2 - Full closure:")
known2 = set()
known2.add(Literal(On('b','L'))); known2.add(Literal(On('c','L')))
known2.add(Literal(Equals('b','c'), polarity=False))
known2.add(Literal(SameSide('a','d','L')))
known2.add(Literal(On('b','N'))); known2.add(Literal(On('a','N')))
known2.add(Literal(SameSide('c','d','N')))
known2.add(Literal(Equals('d','a'), polarity=False))
variables2 = {
    'a': Sort.POINT, 'b': Sort.POINT, 'c': Sort.POINT, 'd': Sort.POINT,
    'L': Sort.LINE, 'N': Sort.LINE
}
ce2 = ConsequenceEngine(ALL_DIAGRAMMATIC_AXIOMS)
closure2 = ce2.direct_consequences(known2, variables2)
known2.update(closure2)
print(f"  L!=N: {Literal(Equals('L','N'), polarity=False) in known2}")
print(f"  not-on(c,N): {Literal(On('c','N'), polarity=False) in known2}")
print(f"  not-on(d,L): {Literal(On('d','L'), polarity=False) in known2}")
print(f"  not-on(d,N): {Literal(On('d','N'), polarity=False) in known2}")
print(f"  b!=a: {Literal(Equals('b','a'), polarity=False) in known2}")

# Test 3: Transfer with the full closure
from verifier.e_transfer import TransferEngine
from verifier.e_axioms import DIAGRAM_ANGLE_TRANSFER
dk = {l for l in known2 if l.is_diagrammatic}
mk = {l for l in known2 if l.is_metric}
te = TransferEngine(DIAGRAM_ANGLE_TRANSFER)
derived = te.apply_transfers(dk, mk, variables2)
angle_sums = [d for d in derived if '+' in str(d)]
print("\nTest 3 - DA2 angle-sum derivations:")
for d in angle_sums:
    print(f"  {d}")
