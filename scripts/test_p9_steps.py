"""Diagnostic: explore reductio for ¬on(e,M) and same-side goals."""
import sys, os
sys.path.insert(0, os.path.join(os.path.dirname(__file__), ".."))
from verifier.e_ast import (
    Sort, Literal, On, SameSide, Between, Center, Inside, Intersects,
    Equals, SegmentTerm, AngleTerm,
)
from verifier.e_consequence import ConsequenceEngine

eng = ConsequenceEngine()

def pos(atom): return Literal(atom, True)
def neg(atom): return Literal(atom, False)

variables = {
    'a': Sort.POINT, 'b': Sort.POINT, 'c': Sort.POINT,
    'd': Sort.POINT, 'f': Sort.POINT, 'e': Sort.POINT,
    'M': Sort.LINE, 'N': Sort.LINE, 'K': Sort.LINE, 'L': Sort.LINE,
    'α': Sort.CIRCLE, 'β': Sort.CIRCLE, 'γ': Sort.CIRCLE,
}

facts = {
    neg(Equals('a','b')), neg(Equals('a','c')), neg(Equals('b','c')),
    pos(On('a','M')), pos(On('b','M')),
    pos(On('a','N')), pos(On('c','N')),
    neg(On('c','M')), neg(On('b','N')),
    pos(Center('a','α')), pos(On('b','α')),
    pos(Inside('a','α')),
    pos(On('d','α')), pos(On('d','N')), pos(Between('d','a','c')),
    pos(On('f','α')), pos(On('f','M')), pos(Between('f','a','b')),
    neg(Equals('d','a')), neg(Equals('M','N')), neg(On('d','M')), neg(Equals('f','d')),
    pos(Center('d','β')), pos(On('f','β')),
    pos(Center('f','γ')), pos(On('d','γ')),
    pos(Inside('d','β')), pos(Inside('f','γ')),
    pos(Intersects('β','γ')),
    pos(On('d','K')), pos(On('f','K')),
    pos(On('e','β')), pos(On('e','γ')),
    neg(SameSide('e','a','K')), neg(On('e','K')),
    neg(Equals('e','d')), neg(Equals('e','f')),
    neg(Equals('a','e')),
    neg(Equals('a','f')),
    pos(On('a','L')), pos(On('e','L')),
    neg(SameSide('d','c','M')),
    neg(SameSide('f','b','N')),
}

closure = eng.direct_consequences(facts, variables)
base_facts = facts | closure
print("Base facts size:", len(base_facts))

def multi_round(init_facts, vars, rounds=5):
    """Run multiple rounds of consequence propagation."""
    current = set(init_facts)
    for i in range(rounds):
        new = eng.direct_consequences(current, vars)
        if new <= current:
            print(f"  Fixed point after {i+1} rounds")
            break
        current = current | new
    return current

# === Test reductio for ¬on(e,M) ===
print()
print("=== Reductio for ¬on(e,M): assume on(e,M) ===")
r_facts = base_facts | {pos(On('e','M'))}
r_all = multi_round(r_facts, variables, rounds=8)

def check_r(lit, label=""):
    print(f"  {'YES' if lit in r_all else 'no '}: {label or str(lit)}")

check_r(pos(Equals('L','M')), "L=M")
check_r(pos(On('b','L')), "on(b,L)")
check_r(pos(On('f','L')), "on(f,L)")
check_r(neg(Equals('L','N')), "L≠N")
check_r(neg(Equals('L','K')), "L≠K")
check_r(neg(On('d','L')), "¬on(d,L)")
check_r(neg(On('e','K')), "¬on(e,K) still?")
check_r(pos(On('e','K')), "on(e,K) contradiction?")
# With L=M and on(b,L) and on(f,L) and on(d,K) and on(f,K):
# Can we show L=K?
check_r(pos(Equals('L','K')), "L=K?")
check_r(pos(On('e','N')), "on(e,N)?")
check_r(neg(SameSide('e','a','K')), "¬ss(e,a,K) still?")
# If L=M and on(d,K) on(d,N) on(d,L=M)?? no d not on M
check_r(pos(On('d','L')), "on(d,L=M)?")

print()
print("Looking for contradiction (contradictory pair):")
# A contradiction would be lit and ¬lit both in r_all
contradictions = []
for lit in r_all:
    neg_lit = Literal(lit.atom, not lit.polarity)
    if neg_lit in r_all:
        contradictions.append(lit)
for c in contradictions[:10]:
    print(f"  CONTRADICTION: {c} and {Literal(c.atom, not c.polarity)}")

# === Test reductio for ¬on(e,N) ===
print()
print("=== Reductio for ¬on(e,N): assume on(e,N) ===")
r2_facts = base_facts | {pos(On('e','N'))}
r2_all = multi_round(r2_facts, variables, rounds=8)

def check_r2(lit, label=""):
    print(f"  {'YES' if lit in r2_all else 'no '}: {label or str(lit)}")

check_r2(pos(Equals('L','N')), "L=N")
check_r2(pos(On('c','L')), "on(c,L)")
check_r2(neg(Equals('L','M')), "L≠M")
check_r2(neg(On('d','K')), "¬on(d,K) contradiction?")
contradictions2 = []
for lit in r2_all:
    neg_lit = Literal(lit.atom, not lit.polarity)
    if neg_lit in r2_all:
        contradictions2.append(lit)
for c in contradictions2[:10]:
    print(f"  CONTRADICTION: {c} and {Literal(c.atom, not c.polarity)}")

# === Test ¬ss(e,d,M) derivation ===
print()
print("=== After adding ¬on(e,M) explicitly - can we get ¬ss(e,d,M)? ===")
facts_with_not_on_eM = base_facts | {neg(On('e','M'))}
all_with = multi_round(facts_with_not_on_eM, variables, rounds=5)
def check_w(lit, label=""):
    print(f"  {'YES' if lit in all_with else 'no '}: {label or str(lit)}")
check_w(neg(SameSide('e','d','M')), "¬ss(e,d,M)")
check_w(pos(SameSide('e','c','M')), "ss(e,c,M)")
check_w(neg(SameSide('d','e','M')), "¬ss(d,e,M)")


