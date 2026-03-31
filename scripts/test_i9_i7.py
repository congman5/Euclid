"""
Test: Can I.7 derive a contradiction inside a reductio?

Strategy for ss(e,c,M):
  1. Assume ¬ss(e,c,M)
  2. SS5 resolves to ss(e,d,M) (since ¬ss(d,c,M) known)
  3. Apply I.7 on line M with endpoints a,f:
     on(a,M), on(f,M), a≠f, ss(e,d,M), ae=ad?, fe=fd?
     → e=d (contradicts e≠d)

  Problem: we need ae=ad and fe=fd for this to work.
  We have: ad=af (circle radii), de=fe (SSS), ae=ae, fe=fd (Seg transfer).
  fe=fd ✓ (L29). But ae=ad? NOT directly available.

Alternative: I.7 on line M with endpoints b,f:
  on(b,M), on(f,M), b≠f, ss(e,d,M), be=bd?, fe=fd?
  We have fe=fd ✓ but not be=bd.

Alternative: I.7 on line N with endpoints c,d:
  on(c,N), on(d,N), c≠d, ss(e,f,N), ce=cf?, de=df?
  We have de=df ✓ (L28: de=df). But not ce=cf.

Hmm. What about using SAS/SSS INSIDE the reductio to derive new
equalities? Inside ¬ss(e,c,M), we have ss(e,d,M).

With ss(e,d,M) + ¬ss(d,f,L) (I.7 result): 
Could we apply DA2 (angle addition) or other transfer axioms?

Actually, let me think about TI2 more carefully.
TI2 for ss(e,c,M): needs ¬ss(e,f,N).
TI2 for ss(e,b,N): needs ¬ss(e,d,M).

These are MUTUAL: each needs the other's negated form.
But what if we can derive ONE of them independently?

The key: can we derive ¬ss(e,d,M) OR ¬ss(e,f,N) from I.7?

I.7 on L (line through a,e):
  on(a,L), on(e,L), a≠e, ss(d,f,L)? NO — ¬ss(d,f,L).

I.7's CONTRAPOSITIVE: if d≠f AND (bd=ba ∧ cd=ca), then ¬ss(d,f,L).
We used this already. But the forward form: ss(d,f,L) ∧ ... → d=f.
Since ¬ss(d,f,L), forward I.7 on L doesn't fire.

What if we try I.7 on a DIFFERENT line?

I.7 on K: on(d,K), on(f,K), d≠f. Need ss(X,Y,K) with dX=dY, fX=fY → X=Y.
  - ss(a,b,K) ✓. da=db? No. fa=fb? No.
  - ss(a,c,K) ✓. da=dc? No. fa=fc? No.
  - ss(c,b,K) ✓. dc=db? No. fc=fb? No.

I.7 on M: on(a,M), on(b,M), on(f,M). Pick two endpoints.
  - a,b: ss(e,d,M) (inside reductio). ae=ad? NO. be=bd? NO.
  - a,f: ss(e,d,M). ae=ad? NO. fe=fd? YES ✓. But still need ae=ad.
  - b,f: ss(e,d,M). be=bd? NO. fe=fd? YES ✓. But need be=bd.

I.7 on N: on(a,N), on(c,N), on(d,N).
  - Similar issues with missing equalities.

The problem is clear: we only have distance equalities involving
{a,d,e,f} from the construction (ad=af, de=fe=df=fd, ae=ae).
We don't have distances from b or c to e.

So I.7 can't fire inside the reductio to give a useful contradiction.

This means the proof needs a DIFFERENT approach entirely for the
same-side goals. Let me look at whether there's a way to derive
ss(e,c,M) using the construction rule's guarantees more directly.

Actually... what if the opposite-side construction already implies
something about which side of M and N the point e is on?
Let me check what the construction rule actually guarantees.
"""
import sys, os
sys.path.insert(0, os.path.join(os.path.dirname(__file__), ".."))
os.environ["PYTHONIOENCODING"] = "utf-8"

# Check what opposite-side construction actually provides
from verifier.e_construction import construct_opposite_side
print("Checking opposite-side construction docs/signature...")
import inspect
sig = inspect.signature(construct_opposite_side)
print(f"  Signature: {sig}")
print()
src = inspect.getsource(construct_opposite_side)
# Print first 80 lines
for i, line in enumerate(src.split('\n')[:80]):
    print(f"  {i+1}: {line}")
