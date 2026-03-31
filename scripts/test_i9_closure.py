"""
Quick test: can TI2 derive ss(e,c,M) from available facts?

TI2: on(a,L)∧on(a,M_ax)∧on(a,N_ax)∧on(b_ax,L)∧on(c_ax,M_ax)∧on(d_ax,N_ax)
     ∧ss(c_ax,d_ax,L)∧¬ss(b_ax,d_ax,M_ax)∧¬on(d_ax,M_ax)∧b_ax≠a
     → ss(b_ax,c_ax,N_ax)

We want conclusion ss(e,c,M). So b_ax=e, c_ax=c, N_ax=M.
Then L=L_ae (e is on it), M_ax=N (c is on it), a=a.
d_ax = point on M = b or f.

With d_ax=f:
  ss(c,f,L_ae) needed — is it derivable?
  ¬ss(e,f,N) needed — is it derivable?
  ¬on(f,N) ✓
  e≠a ✓

Let's check what the consequence engine gives for ¬ss(e,f,N).
"""
from __future__ import annotations
import sys, os
sys.path.insert(0, os.path.join(os.path.dirname(__file__), ".."))
os.environ["PYTHONIOENCODING"] = "utf-8"

from verifier.e_ast import (
    Literal, On, SameSide, Between, Equals, Inside, Center, Intersects,
    SegmentTerm, AngleTerm, Sort,
)
from verifier.e_consequence import ConsequenceEngine
from verifier.e_axioms import ALL_DIAGRAMMATIC_AXIOMS

def _pos(atom): return Literal(atom, polarity=True)
def _neg(atom): return Literal(atom, polarity=False)

# All facts known by step 66 (angle proof done, plus P3/P2 facts)
facts = {
    # Premises
    _neg(Equals("a","b")), _neg(Equals("a","c")), _neg(Equals("b","c")),
    _pos(On("a","M")), _pos(On("b","M")),
    _pos(On("a","N")), _pos(On("c","N")),
    _neg(On("c","M")), _neg(On("b","N")),
    # Construction
    _pos(On("d","N")), _pos(Between("d","a","c")),
    _pos(On("f","M")), _pos(Between("f","a","b")),
    _neg(Equals("d","a")), _neg(Equals("M","N")),
    _neg(On("d","M")), _neg(Equals("f","d")),
    _pos(On("d","K")), _pos(On("f","K")),
    _neg(SameSide("e","a","K")), _neg(On("e","K")),
    _neg(Equals("e","d")), _neg(Equals("e","f")),
    _neg(Equals("a","e")),
    _neg(Equals("a","f")),  # from B1b on between(f,a,b)
    _pos(On("a","L")), _pos(On("e","L")),  # L = line(a,e)
    # Derived
    _neg(On("f","N")),  # G1
    _neg(Equals("K","M")), _neg(Equals("K","N")),  # G5
    _neg(On("e","M")),  # reductio
    _neg(On("e","N")),  # reductio
    # P3 results
    _neg(SameSide("d","c","M")),  # between(d,a,c)∧on(a,M)
    _neg(SameSide("f","b","N")),  # between(f,a,b)∧on(a,N)
    # P2 results (a not on K)
    _neg(On("a","K")),  # G1
    _pos(SameSide("a","c","K")),  # P2: between(d,a,c)∧on(d,K)∧¬on(a,K)
    _pos(SameSide("a","b","K")),  # P2: between(f,a,b)∧on(f,K)∧¬on(a,K)
}

# Variables
variables = {
    "a": Sort.POINT, "b": Sort.POINT, "c": Sort.POINT,
    "d": Sort.POINT, "e": Sort.POINT, "f": Sort.POINT,
    "M": Sort.LINE, "N": Sort.LINE, "K": Sort.LINE, "L": Sort.LINE,
}

ce = ConsequenceEngine(ALL_DIAGRAMMATIC_AXIOMS)
closure = ce.direct_consequences(facts, variables)
all_facts = facts | closure

print(f"Input facts: {len(facts)}")
print(f"Closure size: {len(closure)}")
print(f"Total: {len(all_facts)}")
print()

# Check specific facts we care about
queries = [
    ("ss(e,c,M)", _pos(SameSide("e","c","M"))),
    ("ss(e,b,N)", _pos(SameSide("e","b","N"))),
    ("¬ss(e,c,M)", _neg(SameSide("e","c","M"))),
    ("¬ss(e,b,N)", _neg(SameSide("e","b","N"))),
    ("¬ss(e,f,N)", _neg(SameSide("e","f","N"))),
    ("ss(e,f,N)", _pos(SameSide("e","f","N"))),
    ("¬ss(e,d,M)", _neg(SameSide("e","d","M"))),
    ("ss(e,d,M)", _pos(SameSide("e","d","M"))),
    ("ss(c,f,L)", _pos(SameSide("c","f","L"))),
    ("ss(f,c,L)", _pos(SameSide("f","c","L"))),
    ("ss(d,b,L)", _pos(SameSide("d","b","L"))),
    ("ss(b,d,L)", _pos(SameSide("b","d","L"))),
    ("¬ss(d,f,L)", _neg(SameSide("d","f","L"))),
    ("¬ss(d,c,L)", _neg(SameSide("d","c","L"))),
    ("¬ss(f,b,L)", _neg(SameSide("f","b","L"))),
    ("¬ss(b,c,L)", _neg(SameSide("b","c","L"))),
    ("ss(c,b,K)", _pos(SameSide("c","b","K"))),
    ("ss(b,c,K)", _pos(SameSide("b","c","K"))),
    ("¬ss(e,a,K)", _neg(SameSide("e","a","K"))),
    ("¬ss(a,e,K)", _neg(SameSide("a","e","K"))),
    ("¬ss(e,c,K)", _neg(SameSide("e","c","K"))),
    ("¬ss(e,b,K)", _neg(SameSide("e","b","K"))),
    ("ss(e,d,K)", _pos(SameSide("e","d","K"))),
    ("ss(e,f,K)", _pos(SameSide("e","f","K"))),
]

print("Key facts in closure:")
for name, lit in queries:
    print(f"  {name}: {lit in all_facts}")

# Check if adding I.7 result ¬ss(d,f,L) changes things
print("\n--- Adding I.7 result: ¬ss(d,f,L) ---")
facts2 = facts | {_neg(SameSide("d","f","L"))}
closure2 = ce.direct_consequences(facts2, variables)
all_facts2 = facts2 | closure2
print(f"Closure size: {len(closure2)}")

print("\nKey facts with I.7:")
for name, lit in queries:
    in1 = lit in all_facts
    in2 = lit in all_facts2
    marker = " <<< NEW" if in2 and not in1 else ""
    if in2:
        print(f"  {name}: {in2}{marker}")

# Now check what TI2 needs
print("\n--- TI2 analysis for ss(e,c,M) ---")
print("Assignment: L=L_ae, M_ax=N, N_ax=M, a=a, b_ax=e, c_ax=c, d_ax=f")
print(f"  on(a,L): {_pos(On('a','L')) in all_facts2}")
print(f"  on(a,N): {_pos(On('a','N')) in all_facts2}")
print(f"  on(a,M): {_pos(On('a','M')) in all_facts2}")
print(f"  on(e,L): {_pos(On('e','L')) in all_facts2}")
print(f"  on(c,N): {_pos(On('c','N')) in all_facts2}")
print(f"  on(f,M): {_pos(On('f','M')) in all_facts2}")
print(f"  ss(c,f,L): {_pos(SameSide('c','f','L')) in all_facts2}")
print(f"  ¬ss(e,f,N): {_neg(SameSide('e','f','N')) in all_facts2}")
print(f"  ¬on(f,N): {_neg(On('f','N')) in all_facts2}")
print(f"  e≠a: {_neg(Equals('e','a')) in all_facts2}")
print(f"  (alt) a≠e: {_neg(Equals('a','e')) in all_facts2}")
