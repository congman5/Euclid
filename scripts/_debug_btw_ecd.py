"""Debug what facts are needed for neg between(e,c,d)."""
import sys; sys.path.insert(0,'.'); sys.stdout.reconfigure(encoding='utf-8')
from verifier.e_ast import *
from verifier.e_consequence import ConsequenceEngine

# Full dep set including L19 and L28
known = {
    Literal(On('a','L'), True),
    Literal(On('b','L'), True),
    Literal(Equals('a','b'), False),
    Literal(Equals('c','a'), False),
    Literal(On('c','L'), False),         # L19
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
    Literal(SameSide('a','b','K'), False),  # L28
    Literal(On('d','K'), True),
    Literal(On('d','L'), True),
}

variables = {
    'a': Sort.POINT, 'b': Sort.POINT, 'c': Sort.POINT,
    'd': Sort.POINT, 'e': Sort.POINT,
    'L': Sort.LINE, 'M': Sort.LINE, 'N': Sort.LINE, 'K': Sort.LINE,
}

ce = ConsequenceEngine()
closure = ce.direct_consequences(known, variables)
aug = known | closure
print(f'Total facts: {len(aug)}')
target = Literal(Between('e','c','d'), False)
print(f'neg btw(e,c,d) in closure: {target in aug}')

# Check what between facts with e,c,d exist
for l in sorted(aug, key=str):
    if isinstance(l.atom, Between):
        pts = {l.atom.a, l.atom.b, l.atom.c}
        if 'e' in pts and ('c' in pts or 'd' in pts):
            print(f'  {l}')

# Now try without L28
known2 = known - {Literal(SameSide('a','b','K'), False)}
closure2 = ce.direct_consequences(known2, variables)
aug2 = known2 | closure2
print(f'\nWithout L28: {len(aug2)} facts')
print(f'neg btw(e,c,d): {target in aug2}')

# Try without L19
known3 = known - {Literal(On('c','L'), False)}
closure3 = ce.direct_consequences(known3, variables)
aug3 = known3 | closure3
print(f'\nWithout L19: {len(aug3)} facts')
print(f'neg btw(e,c,d): {target in aug3}')

# Try without both L19 and L28
known4 = known - {Literal(On('c','L'), False), Literal(SameSide('a','b','K'), False)}
closure4 = ce.direct_consequences(known4, variables)
aug4 = known4 | closure4
print(f'\nWithout L19+L28: {len(aug4)} facts')
print(f'neg btw(e,c,d): {target in aug4}')
