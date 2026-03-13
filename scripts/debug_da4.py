"""Debug DA4 grounding for I.9."""
import sys
sys.path.insert(0, '.')

from verifier.e_consequence import ConsequenceEngine
from verifier.e_transfer import TransferEngine
from verifier.e_ast import *
from verifier.e_axioms import DIAGRAM_ANGLE_TRANSFER, ALL_TRANSFER_AXIOMS

# Simulate the known facts at the point where Transfer is called
known_diag = {
    Literal(On('a','N'),True), Literal(On('c','N'),True), Literal(On('d','N'),True),
    Literal(On('a','M'),True), Literal(On('b','M'),True), Literal(On('f','M'),True),
    Literal(On('a','K'),True), Literal(On('e','K'),True),
    Literal(Between('a','d','c'),True), Literal(Between('a','f','b'),True),
    Literal(SameSide('c','b','M'),True), Literal(SameSide('b','c','N'),True),
    Literal(Equals('a','b'),False), Literal(Equals('a','c'),False),
    Literal(Equals('b','c'),False),
    Literal(Equals('e','d'),False), Literal(Equals('e','f'),False),
    Literal(Equals('e','a'),False),
    Literal(Equals('N','K'),False), Literal(Equals('M','K'),False),
    Literal(Equals('M','N'),False),
}

known_metric = {
    Literal(Equals(SegmentTerm('a','d'), SegmentTerm('a','b')), True),
    Literal(Equals(SegmentTerm('a','f'), SegmentTerm('a','b')), True),
    Literal(Equals(SegmentTerm('a','d'), SegmentTerm('a','f')), True),
    Literal(Equals(SegmentTerm('d','f'), SegmentTerm('d','e')), True),
    Literal(Equals(SegmentTerm('d','e'), SegmentTerm('f','e')), True),
    Literal(Equals(AngleTerm('d','a','e'), AngleTerm('f','a','e')), True),
}

variables = {
    'a': Sort.POINT, 'b': Sort.POINT, 'c': Sort.POINT,
    'd': Sort.POINT, 'e': Sort.POINT, 'f': Sort.POINT,
    'M': Sort.LINE, 'N': Sort.LINE, 'K': Sort.LINE,
}

# First compute diagrammatic closure
ce = ConsequenceEngine()
closure = ce.direct_consequences(known_diag, variables)
all_diag = known_diag | closure

# Check key facts
print("Has negbetween(d,a,c):", Literal(Between('d','a','c'),False) in all_diag)
print("Has negbetween(f,a,b):", Literal(Between('f','a','b'),False) in all_diag)
print("Has neg(e=a):", Literal(Equals('e','a'),False) in all_diag)
print("Has neg(d=a):", Literal(Equals('d','a'),False) in all_diag)
print("Has neg(c=a):", Literal(Equals('c','a'),False) in all_diag)

# Now check DA4 specifically
# DA4 template: a,b,bp on L; a,c,cp on M; b!=a, bp!=a, c!=a, cp!=a,
#               neg between(b,a,bp), neg between(c,a,cp) => angle(b,a,c)=angle(bp,a,cp)
# 
# For angle dae = cae:
# vertex=a, L=N (d,c on N), M=K (e,e on K)
# b=d, bp=c, c=e, cp=e
# Need: on(a,N)T, on(d,N)T, on(c,N)T, on(a,K)T, on(e,K)T, on(e,K)T
#       neg(d=a)T, neg(c=a)T, neg(e=a)T, neg(e=a)T
#       neg between(d,a,c)T, neg between(e,a,e)?
#
# between(e,a,e) requires all 3 distinct, but e=e, so between(e,a,e) is undefined/false
# So neg between(e,a,e) should be trivially true

# Let me check if neg between(e,a,e) is in the closure
print("Has negbetween(e,a,e):", Literal(Between('e','a','e'),False) in all_diag)

# Check all between facts involving e
ebetween = [str(f) for f in all_diag if isinstance(f.atom, Between) and 'e' in (f.atom.a, f.atom.b, f.atom.c)]
print("Between facts with e:", ebetween)

# Now try applying transfer directly
te = TransferEngine(ALL_TRANSFER_AXIOMS)
derived = te.apply_transfers(all_diag, known_metric, variables)
angle_derived = [str(f) for f in derived if isinstance(f.atom, Equals) and isinstance(f.atom.left, AngleTerm)]
print("Angle equalities from transfer:", angle_derived[:20])

# Check for DA4 specifically
target = Literal(Equals(AngleTerm('d','a','e'), AngleTerm('c','a','e')), True)
print("Target dae=cae in derived:", target in derived)
