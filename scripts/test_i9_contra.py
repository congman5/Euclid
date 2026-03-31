"""Test: does ss(e,d,M) + ss(e,f,N) + all other facts lead to contradiction?"""
import sys, os
sys.path.insert(0, os.path.join(os.path.dirname(__file__), ".."))
os.environ["PYTHONIOENCODING"] = "utf-8"
from verifier.e_ast import *
from verifier.e_consequence import ConsequenceEngine
from verifier.e_axioms import ALL_DIAGRAMMATIC_AXIOMS

def _pos(a): return Literal(a, polarity=True)
def _neg(a): return Literal(a, polarity=False)

base_facts = {
    _neg(Equals("a","b")), _neg(Equals("a","c")), _neg(Equals("b","c")),
    _pos(On("a","M")), _pos(On("b","M")),
    _pos(On("a","N")), _pos(On("c","N")),
    _neg(On("c","M")), _neg(On("b","N")),
    _pos(On("d","N")), _pos(Between("d","a","c")),
    _pos(On("f","M")), _pos(Between("f","a","b")),
    _neg(Equals("d","a")), _neg(Equals("M","N")),
    _neg(On("d","M")), _neg(Equals("f","d")),
    _pos(On("d","K")), _pos(On("f","K")),
    _neg(SameSide("e","a","K")), _neg(On("e","K")),
    _neg(Equals("e","d")), _neg(Equals("e","f")),
    _neg(Equals("a","e")), _neg(Equals("a","f")),
    _pos(On("a","L")), _pos(On("e","L")),
    _neg(On("f","N")), _neg(Equals("K","M")), _neg(Equals("K","N")),
    _neg(On("e","M")), _neg(On("e","N")),
    _neg(SameSide("d","c","M")), _neg(SameSide("f","b","N")),
    _neg(On("a","K")),
    _pos(SameSide("a","c","K")), _pos(SameSide("a","b","K")),
    _neg(SameSide("d","f","L")),  # I.7
}

variables = {
    "a": Sort.POINT, "b": Sort.POINT, "c": Sort.POINT,
    "d": Sort.POINT, "e": Sort.POINT, "f": Sort.POINT,
    "M": Sort.LINE, "N": Sort.LINE, "K": Sort.LINE, "L": Sort.LINE,
}

ce = ConsequenceEngine(ALL_DIAGRAMMATIC_AXIOMS)

# Case: e outside on BOTH sides (ss(e,d,M) + ss(e,f,N))
print("=== Case: ss(e,d,M) + ss(e,f,N) ===")
facts_case = base_facts | {
    _pos(SameSide("e","d","M")),
    _pos(SameSide("e","f","N")),
}
closure = ce.direct_consequences(facts_case, variables)
allfacts = facts_case | closure
print(f"Closure: {len(closure)}")
# Check for BOTTOM
has_bottom = BOTTOM in allfacts
print(f"BOTTOM in closure: {has_bottom}")
# Check for contradictions manually
contra_count = 0
for lit in allfacts:
    neg = lit.negated()
    if neg in allfacts:
        if contra_count < 10:
            print(f"  CONTRADICTION: {lit}  vs  {neg}")
        contra_count += 1
print(f"Total contradictions: {contra_count}")

# Case: ss(e,d,M) only (¬ss(e,c,M) reductio, e still on correct side of N)
print("\n=== Case: ss(e,d,M) only ===")
facts_case2 = base_facts | {_pos(SameSide("e","d","M"))}
closure2 = ce.direct_consequences(facts_case2, variables)
allfacts2 = facts_case2 | closure2
print(f"Closure: {len(closure2)}")
contra_count2 = 0
for lit in allfacts2:
    neg = lit.negated()
    if neg in allfacts2:
        contra_count2 += 1
        if contra_count2 <= 5:
            print(f"  CONTRADICTION: {lit}  vs  {neg}")
print(f"Total contradictions: {contra_count2}")

# Case: ss(e,f,N) only (¬ss(e,b,N) reductio)
print("\n=== Case: ss(e,f,N) only ===")
facts_case3 = base_facts | {_pos(SameSide("e","f","N"))}
closure3 = ce.direct_consequences(facts_case3, variables)
allfacts3 = facts_case3 | closure3
print(f"Closure: {len(closure3)}")
contra_count3 = 0
for lit in allfacts3:
    neg = lit.negated()
    if neg in allfacts3:
        contra_count3 += 1
        if contra_count3 <= 5:
            print(f"  CONTRADICTION: {lit}  vs  {neg}")
print(f"Total contradictions: {contra_count3}")

# Case: DIRECT assumption ¬ss(e,c,M) (what if consequence engine resolves SS5?)
print("\n=== Case: ¬ss(e,c,M) assumed ===")
facts_case4 = base_facts | {_neg(SameSide("e","c","M"))}
closure4 = ce.direct_consequences(facts_case4, variables)
allfacts4 = facts_case4 | closure4
print(f"Closure: {len(closure4)}")
print(f"ss(e,d,M) derived: {_pos(SameSide('e','d','M')) in allfacts4}")
contra_count4 = 0
for lit in allfacts4:
    neg = lit.negated()
    if neg in allfacts4:
        contra_count4 += 1
        if contra_count4 <= 5:
            print(f"  CONTRADICTION: {lit}  vs  {neg}")
print(f"Total contradictions: {contra_count4}")
