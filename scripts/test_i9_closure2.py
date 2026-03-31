"""Test what additional facts enable ss(e,c,M) derivation."""
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
    _neg(SameSide("d","f","L")),  # from I.7
}

variables = {
    "a": Sort.POINT, "b": Sort.POINT, "c": Sort.POINT,
    "d": Sort.POINT, "e": Sort.POINT, "f": Sort.POINT,
    "M": Sort.LINE, "N": Sort.LINE, "K": Sort.LINE, "L": Sort.LINE,
}

ce = ConsequenceEngine(ALL_DIAGRAMMATIC_AXIOMS)

target_ecM = _pos(SameSide("e","c","M"))
target_ebN = _pos(SameSide("e","b","N"))

def test(label, extra):
    facts = base_facts | extra
    closure = ce.direct_consequences(facts, variables)
    allfacts = facts | closure
    ecM = target_ecM in allfacts
    ebN = target_ebN in allfacts
    print(f"{label}: ss(e,c,M)={ecM}  ss(e,b,N)={ebN}  closure={len(closure)}")
    return allfacts

print("=== Testing what extra facts enable the goals ===\n")

test("Baseline (no extra)", set())
test("+ ¬ss(e,f,N)", {_neg(SameSide("e","f","N"))})
test("+ ¬ss(e,d,M)", {_neg(SameSide("e","d","M"))})
test("+ both ¬ss(e,f,N) + ¬ss(e,d,M)", {
    _neg(SameSide("e","f","N")),
    _neg(SameSide("e","d","M")),
})
test("+ ss(e,d,M)", {_pos(SameSide("e","d","M"))})
test("+ ss(e,f,N)", {_pos(SameSide("e","f","N"))})

# Check if ¬on(d,L) or ¬on(f,L) help
print()
all0 = test("Baseline with check", set())
print(f"  ¬on(d,L): {_neg(On('d','L')) in all0}")
print(f"  ¬on(f,L): {_neg(On('f','L')) in all0}")
print(f"  ¬(L=M): {_neg(Equals('L','M')) in all0}")
print(f"  ¬(L=N): {_neg(Equals('L','N')) in all0}")
print(f"  on(b,L): {_pos(On('b','L')) in all0}")
print(f"  on(c,L): {_pos(On('c','L')) in all0}")

# Try adding L≠M and L≠N
print()
test("+ L≠M + L≠N", {_neg(Equals("L","M")), _neg(Equals("L","N"))})

# What about adding ¬on(d,L) (d not on line ae — very plausible)
print()
test("+ ¬on(d,L)", {_neg(On("d","L"))})
test("+ ¬on(f,L)", {_neg(On("f","L"))})
test("+ ¬on(d,L) + ¬on(f,L)", {_neg(On("d","L")), _neg(On("f","L"))})

# Both ¬on + L≠M,L≠N
print()
all_extra = {
    _neg(On("d","L")), _neg(On("f","L")),
    _neg(Equals("L","M")), _neg(Equals("L","N")),
}
af = test("+ ¬on(d,L) + ¬on(f,L) + L≠M + L≠N", all_extra)

# Check what TI-relevant facts are now available
print(f"  ss(c,f,L): {_pos(SameSide('c','f','L')) in af}")
print(f"  ss(d,b,L): {_pos(SameSide('d','b','L')) in af}")
print(f"  ¬ss(e,f,N): {_neg(SameSide('e','f','N')) in af}")
print(f"  ¬ss(e,d,M): {_neg(SameSide('e','d','M')) in af}")
