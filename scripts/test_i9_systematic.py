"""
Systematic exploration of I.9 proof strategies.

The paper (footnote 8) says I.7 contrapositive gives ¬ss(d,f,L).
This "immediately rules out two cases." We need to understand which
cases and how to derive ss(e,c,M) and ss(e,b,N).

Three concurrent lines through a:
  L = line(a,e)    -- the bisector
  M = line(a,b,f)  -- one leg (between(f,a,b))
  N = line(a,c,d)  -- other leg (between(d,a,c))

Known facts include:
  ¬ss(d,f,L)  from I.7 contrapositive
  ¬ss(e,a,K)  from construction (opposite side of K from a)
  ¬on(e,K)    from construction

TI axioms with L,M,N through a:
  TI1: on(b,L) ∧ on(c,M) ∧ on(d,N) ∧ ss(c,d,L) ∧ ss(b,c,N) → ¬ss(b,d,M)

Let's try ALL possible TI1 instantiations with points on the three lines.
"""

import sys, os
sys.path.insert(0, os.path.join(os.path.dirname(__file__), ".."))

from verifier.e_consequence import ConsequenceEngine
from verifier.e_axioms import ALL_DIAGRAMMATIC_AXIOMS
from verifier.e_parser import parse_literal_list
from verifier.e_ast import Sort

def parse(s, ctx):
    return set(parse_literal_list(s, ctx))

ctx = {}

# All known facts
base_facts_strs = [
    # Premises
    "¬(a = b)", "¬(a = c)", "¬(b = c)",
    "on(a, M)", "on(b, M)", "on(a, N)", "on(c, N)",
    "¬(on(c, M))", "¬(on(b, N))",

    # Construction: circle α with center a through b
    # d on N extending beyond a from c: between(d,a,c)
    "on(d, N)", "between(d, a, c)",
    # f on M extending beyond a from b: between(f,a,b)
    "on(f, M)", "between(f, a, b)",
    # d and f on circle α
    "on(d, α)", "on(f, α)", "center(a, α)",
    # ad = af (equal radii)
    "ad = af",

    # d ≠ a, f ≠ a from betweenness
    "¬(d = a)", "¬(a = f)",
    # M ≠ N
    "¬(M = N)",
    # d not on M (since d on N, a on both, M≠N, d≠a)
    "¬(on(d, M))",
    # f not on N (symmetric)
    "¬(on(f, N))",
    # f ≠ d
    "¬(f = d)",

    # Circles β (center d, through f) and γ (center f, through d)
    "center(d, β)", "on(f, β)",
    "center(f, γ)", "on(d, γ)",
    "inside(d, β)", "inside(f, γ)",
    "intersects(β, γ)",

    # Line K through d and f
    "on(d, K)", "on(f, K)",

    # Point e: intersection of β,γ opposite side of K from a
    "on(e, β)", "on(e, γ)",
    "¬(same-side(e, a, K))", "¬(on(e, K))",

    # Metric facts from circles
    "de = df", "fe = fd", "de = fe",

    # e ≠ d, e ≠ f, a ≠ e
    "¬(e = d)", "¬(e = f)", "¬(a = e)",

    # Line L through a and e
    "on(a, L)", "on(e, L)",

    # SSS gives ∠dae = ∠fae
    # (We'll add this as a metric fact)
    "ae = ae",

    # I.7 contrapositive: ad=af, de=fe, d≠f → ¬ss(d,f,L)
    "¬(same-side(d, f, L))",

    # From Pasch 3 on between(d,a,c) with line M:
    "¬(same-side(d, c, M))",
    # From Pasch 3 on between(f,a,b) with line N:
    "¬(same-side(f, b, N))",

    # K ≠ M, K ≠ N (from G5: d on K but not on M; f on K but not on N)
    "¬(K = M)", "¬(K = N)",

    # ¬on(a, K) — a not on line through d,f (since d on N, f on M, M≠N, so d,f,a not collinear unless a on K)
    # Actually we need to verify this. If a were on K, then K=line(d,a) and since d on N and a on N, K=N.
    # But f on K and f not on N, contradiction. So ¬on(a,K).
    "¬(on(a, K))",
]

base = set()
for s in base_facts_strs:
    base |= parse(s, ctx)

# Also add: L ≠ M, L ≠ N, L ≠ K
# e on L, e not on K → if L=K then e on K, contradiction. So L≠K.
# b on M, b not on... hmm, is b on L? Not necessarily.
# Let's check: if L=M, then e on M. But we don't know ¬on(e,M) yet.
# We'll add these only if we can derive them.

print("=" * 70)
print("PHASE 1: Base closure (without ¬on(e,M), ¬on(e,N))")
print("=" * 70)

ce = ConsequenceEngine(ALL_DIAGRAMMATIC_AXIOMS)
closure = ce.direct_consequences(base, ctx)
augmented = base | closure

# Check what we have
targets = [
    "same-side(e, c, M)", "same-side(e, b, N)",
    "¬(same-side(e, d, M))", "¬(same-side(e, f, N))",
    "¬(on(e, M))", "¬(on(e, N))",
    "same-side(e, d, M)", "same-side(e, f, N)",
    "¬(same-side(d, f, L))",
    "same-side(c, f, L)", "same-side(d, b, L)",
    "¬(same-side(b, c, L))",
    "same-side(a, c, K)", "same-side(a, b, K)",
    "¬(L = M)", "¬(L = N)", "¬(L = K)",
    "¬(on(b, L))", "¬(on(c, L))", "¬(on(d, L))", "¬(on(f, L))",
    "¬(on(e, M))", "¬(on(e, N))",
    "¬(on(b, K))", "¬(on(c, K))",
    "same-side(d, e, N)", "same-side(f, e, M)",
    "¬(same-side(d, e, N))", "¬(same-side(f, e, M))",
    "same-side(c, e, L)", "same-side(b, e, L)",
    "same-side(d, e, L)", "same-side(f, e, L)",
    "¬(same-side(c, e, L))", "¬(same-side(b, e, L))",
    "¬(same-side(d, e, L))", "¬(same-side(f, e, L))",
    "same-side(e, a, K)", "same-side(a, e, K)",
    "same-side(d, a, M)", "same-side(a, d, M)",
    "same-side(f, a, N)", "same-side(a, f, N)",
    "same-side(c, d, L)", "same-side(d, c, L)",
    "same-side(b, f, L)", "same-side(f, b, L)",
]

for t in targets:
    lits = parse(t, ctx)
    found = all(l in augmented for l in lits)
    if found:
        print(f"  ✓ {t}")

print()
print("Missing key targets:")
for t in ["same-side(e, c, M)", "same-side(e, b, N)", 
          "¬(same-side(e, d, M))", "¬(same-side(e, f, N))",
          "¬(on(e, M))", "¬(on(e, N))"]:
    lits = parse(t, ctx)
    found = all(l in augmented for l in lits)
    if not found:
        print(f"  ✗ {t}")

print()
print(f"  Closure size: {len(augmented)}")

# ──────────────────────────────────────────────────────────
print()
print("=" * 70)
print("PHASE 2: Add ¬on(e,M) and ¬on(e,N) (derivable via reductio)")
print("=" * 70)

extra = parse("¬(on(e, M))", ctx) | parse("¬(on(e, N))", ctx)
base2 = base | extra

closure2 = ce.direct_consequences(base2, ctx)
aug2 = base2 | closure2

for t in targets:
    lits = parse(t, ctx)
    found = all(l in aug2 for l in lits)
    if found:
        print(f"  ✓ {t}")

print()
print("Key targets:")
for t in ["same-side(e, c, M)", "same-side(e, b, N)", 
          "¬(same-side(e, d, M))", "¬(same-side(e, f, N))"]:
    lits = parse(t, ctx)
    found = all(l in aug2 for l in lits)
    print(f"  {'✓' if found else '✗'} {t}")

print(f"  Closure size: {len(aug2)}")

# ──────────────────────────────────────────────────────────
print()
print("=" * 70)
print("PHASE 3: Also add L≠M, L≠N (in case these help TI)")
print("=" * 70)

extra3 = parse("¬(L = M)", ctx) | parse("¬(L = N)", ctx) | parse("¬(L = K)", ctx)
base3 = base2 | extra3

closure3 = ce.direct_consequences(base3, ctx)
aug3 = base3 | closure3

for t in targets:
    lits = parse(t, ctx)
    found = all(l in aug3 for l in lits)
    if found:
        print(f"  ✓ {t}")

print()
print("Key targets:")
for t in ["same-side(e, c, M)", "same-side(e, b, N)", 
          "¬(same-side(e, d, M))", "¬(same-side(e, f, N))"]:
    lits = parse(t, ctx)
    found = all(l in aug3 for l in lits)
    print(f"  {'✓' if found else '✗'} {t}")

print(f"  Closure size: {len(aug3)}")

# ──────────────────────────────────────────────────────────
# Now try specific TI1 instantiations manually.
# TI1: on(a,L1) ∧ on(a,L2) ∧ on(a,L3) ∧ on(p,L1) ∧ on(q,L2) ∧ on(r,L3) 
#      ∧ ss(q,r,L1) ∧ ss(p,q,L3) → ¬ss(p,r,L2)
#
# Three lines through a: L, M, N
# Points on L: e (and a)
# Points on M: b, f (and a)
# Points on N: c, d (and a)
#
# We want ¬ss(e,d,M).  That means p=e on L1, r=d on L3, L2=M.
# So L1=L, L3=N, L2=M: on(e,L), on(q,M), on(d,N)
# q must be on M and not a. Options: b or f.
# Need: ss(q,d,L) ∧ ss(e,q,N)
#
# Case q=b: need ss(b,d,L) ∧ ss(e,b,N)
# Case q=f: need ss(f,d,L) ∧ ss(e,f,N)
#
# We want ¬ss(e,f,N).  That means p=e on L1, r=f on L3, L2=N.
# So L1=L, L3=M, L2=N: on(e,L), on(q,N), on(f,M)
# q must be on N. Options: c or d.
# Need: ss(q,f,L) ∧ ss(e,q,M)
#
# Case q=c: need ss(c,f,L) ∧ ss(e,c,M)
# Case q=d: need ss(d,f,L) ∧ ss(e,d,M)  -- but we have ¬ss(d,f,L)!

print()
print("=" * 70)
print("PHASE 4: TI1 analysis — what's needed for each target")
print("=" * 70)
print()
print("To derive ¬ss(e,d,M) via TI1 (L1=L, L2=M, L3=N):")
print("  Option A: q=b → need ss(b,d,L) ∧ ss(e,b,N)")
print("  Option B: q=f → need ss(f,d,L) ∧ ss(e,f,N)")
print()
print("To derive ¬ss(e,f,N) via TI1 (L1=L, L2=N, L3=M):")
print("  Option C: q=c → need ss(c,f,L) ∧ ss(e,c,M)")
print("  Option D: q=d → need ss(d,f,L) ∧ ss(e,d,M)  [but ¬ss(d,f,L) known!]")
print()

# Check which of these prerequisites we have
for t in ["same-side(b, d, L)", "same-side(e, b, N)",
          "same-side(f, d, L)", "same-side(e, f, N)",
          "same-side(c, f, L)", "same-side(e, c, M)",
          "same-side(d, f, L)"]:
    lits = parse(t, ctx)
    found = all(l in aug3 for l in lits)
    print(f"  {'✓' if found else '✗'} {t}")

print()
print("Observation: Options A and C both require the TARGET ss(e,b,N) / ss(e,c,M)")
print("Option B requires ss(e,f,N) — also a target")
print("Option D is impossible — ¬ss(d,f,L) blocks it")
print()
print("CONCLUSION: TI1 is circular for ALL options.")

# ──────────────────────────────────────────────────────────
# Try TI2 instead
# TI2: on(a,L1)∧on(a,L2)∧on(a,L3) ∧ on(p,L1)∧on(q,L2)∧on(r,L3)
#      ∧ ss(q,r,L1) ∧ ¬ss(p,r,L2) ∧ ¬on(r,L2) ∧ p≠a → ss(p,q,L3)
print()
print("=" * 70)
print("PHASE 5: TI2 analysis")
print("=" * 70)
print()
print("TI2: ss(q,r,L1) ∧ ¬ss(p,r,L2) ∧ ¬on(r,L2) ∧ p≠a → ss(p,q,L3)")
print()
print("To derive ss(e,b,N) via TI2: p=e, q=b, L3=N")
print("  Need L1,L2 through a, e on L1, b on L2")
print("  L1=L, L2=M: need ss(b,r,L) ∧ ¬ss(e,r,M) ∧ ¬on(r,M) ∧ e≠a")
print("  r on N: options c or d")
print("    r=c: ss(b,c,L)... ", end="")
bc_L = parse("same-side(b, c, L)", ctx)
print("¬ss(b,c,L) known" if all(l.negated() in aug3 for l in bc_L) else 
      ("ss(b,c,L) known" if all(l in aug3 for l in bc_L) else "unknown"))
print("    r=d: ss(b,d,L) ∧ ¬ss(e,d,M) ∧ ¬on(d,M) ∧ e≠a")

bd_L = parse("same-side(b, d, L)", ctx)
print(f"      ss(b,d,L): {all(l in aug3 for l in bd_L)}")
print(f"      ¬on(d,M): True (known)")
print(f"      e≠a: True (known)")
ed_M = parse("¬(same-side(e, d, M))", ctx)
print(f"      ¬ss(e,d,M): {all(l in aug3 for l in ed_M)}")

print()
print("To derive ss(e,c,M) via TI2: p=e, q=c, L3=M")
print("  L1=L, L2=N: need ss(c,r,L) ∧ ¬ss(e,r,N) ∧ ¬on(r,N) ∧ e≠a")
print("  r on M (L2=N means r on ???)")
print("  Actually let me re-derive. TI2 has L1,L2,L3 through a:")
print("  on(p,L1), on(q,L2), on(r,L3)")
print("  ss(q,r,L1) ∧ ¬ss(p,r,L2) ∧ ¬on(r,L2) ∧ p≠a → ss(p,q,L3)")
print()
print("  For ss(e,c,M): p=e, q=c, L3=M means q on L2=?")
print("  q=c on L2 → L2=N (c on N). p=e on L1 → L1=L (e on L).")
print("  r on L3=M → r ∈ {b, f}.")
print("  Need ss(c,r,L) ∧ ¬ss(e,r,N) ∧ ¬on(r,N) ∧ e≠a")
print("    r=b: ss(c,b,L) ∧ ¬ss(e,b,N) ∧ ¬on(b,N) ∧ e≠a")

cb_L = parse("same-side(c, b, L)", ctx)  # same as ss(b,c,L)
not_bc_L = parse("¬(same-side(b, c, L))", ctx)
print(f"      ss(c,b,L) = ss(b,c,L) via SS2: ", end="")
print("known ¬ss(b,c,L)" if all(l in aug3 for l in not_bc_L) else "unknown")

print("    r=f: ss(c,f,L) ∧ ¬ss(e,f,N) ∧ ¬on(f,N) ∧ e≠a")
cf_L = parse("same-side(c, f, L)", ctx)
print(f"      ss(c,f,L): {all(l in aug3 for l in cf_L)}")
ef_N = parse("¬(same-side(e, f, N))", ctx)
print(f"      ¬ss(e,f,N): {all(l in aug3 for l in ef_N)}")
print(f"      ¬on(f,N): True (known)")

print()
print("=" * 70)
print("PHASE 6: What if we try PASCH axioms to get ¬ss(e,d,M)?")
print("=" * 70)
print()
print("Pasch 1 (P1): between(a,b,c) ∧ on(a,L) ∧ on(b,L) → ¬ss(a,c,L)")
print("  We have between(d,a,c) on N. But we need e involved somehow.")
print()
print("Pasch 2 (P2): between(a,b,c) ∧ ss(a,d,L) → ss(b,d,L) (if ¬on(b,L))")
print("  We have between(d,a,c). If ss(d,e,M) then ss(a,e,M) (wrong direction)")
print()
print("Pasch 3 (P3): between(a,b,c) ∧ on(a,L) → ¬ss(a,c,L)")
print("  between(d,a,c) ∧ on(d,?):")
print("  on(d,N) → ¬ss(d,c,N) — trivially, both on N")
print("  on(d,K) → ¬ss(d,c,K) — useful?")

dc_K = parse("¬(same-side(d, c, K))", ctx)
print(f"  ¬ss(d,c,K): {all(l in aug3 for l in dc_K)}")

print()
print("Pasch 4 (P4): between(a,b,c) ∧ on(a,L) ∧ on(c,L) ∧ ¬on(b,L) → on(b,L)")
print("  This is just: if between(a,b,c) and a,c on L then b on L")
print()

# What about using the fact that ¬ss(e,a,K)?
# We have between(d,a,c). between(f,a,b).
# Can we derive between(e,a,?) for some point?
# If between(e,a,x) and on(e,M) (hypothetical) then... no.

# Let me check: what does Pasch 3 give from between(d,a,c)?
# P3: between(d,a,c) ∧ on(d,L') → ¬ss(d,c,L')
# on(d,K) → ¬ss(d,c,K) ✓
# on(d,N) → ¬ss(d,c,N) (trivial, both on N)
# P3: between(f,a,b) ∧ on(f,L') → ¬ss(f,b,L')
# on(f,K) → ¬ss(f,b,K) ✓
# on(f,M) → ¬ss(f,b,M) (trivial, both on M)

fb_K = parse("¬(same-side(f, b, K))", ctx)
print(f"  ¬ss(f,b,K): {all(l in aug3 for l in fb_K)}")

print()
print("=" * 70)
print("PHASE 7: SS5 with K instead of M/N")
print("=" * 70)
print()
print("SS5: ¬on(a,L)∧¬on(b,L)∧¬on(c,L)∧¬ss(a,b,L) → ss(a,c,L)∨ss(b,c,L)")
print()
print("On line K: we have ¬ss(e,a,K), ¬on(e,K), ¬on(a,K)")
print("  SS5 with a=e, b=a, c=?, L=K:")
print("  ¬on(e,K)✓ ∧ ¬on(a,K)✓ ∧ ¬on(?,K) ∧ ¬ss(e,a,K)✓")
print("  → ss(e,?,K) ∨ ss(a,?,K)")
print()
print("  c=b: ¬on(b,K)?")

b_K = parse("¬(on(b, K))", ctx)
print(f"    ¬on(b,K): {all(l in aug3 for l in b_K)}")
c_K = parse("¬(on(c, K))", ctx)
print(f"    ¬on(c,K): {all(l in aug3 for l in c_K)}")
e_M = parse("¬(on(e, M))", ctx)
print(f"    ¬on(e,M): {all(l in aug3 for l in e_M)}")

# Check if b and c are on K
print()
print("  If ¬on(b,K): SS5 → ss(e,b,K) ∨ ss(a,b,K)")
print("  If ¬on(c,K): SS5 → ss(e,c,K) ∨ ss(a,c,K)")
print()

# Can we get ¬on(b,K) and ¬on(c,K)?
# K is line through d and f. b is on M, c is on N.
# If b were on K, then K = line(f,b) since f on K and b on K and f on M and b on M → K=M.
# But K≠M (known). So ¬on(b,K).
# Similarly if c on K, then K = line(d,c) since d on K and c on K and d on N and c on N → K=N.
# But K≠N. So ¬on(c,K).
# But can the VERIFIER derive this? It needs G1 or similar.

print("Can we derive ¬on(b,K) via G1?")
print("  G1: on(x,L) ∧ on(y,L) ∧ on(x,M) ∧ x≠y ∧ L≠M → ¬on(y,M)")
print("  on(f,K) ∧ on(f,M) ∧ on(b,M) ∧ f≠b? ∧ K≠M → ¬on(b,K)")

# f≠b: between(f,a,b) → f≠b via B1b
fb = parse("¬(f = b)", ctx)
print(f"  ¬(f=b): {all(l in aug3 for l in fb)}")

print()
print("Can we derive ¬on(c,K) via G1?")
print("  on(d,K) ∧ on(d,N) ∧ on(c,N) ∧ d≠c? ∧ K≠N → ¬on(c,K)")
dc = parse("¬(d = c)", ctx)
print(f"  ¬(d=c): {all(l in aug3 for l in dc)}")

print()
print("=" * 70)
print("PHASE 8: Full test with ¬on(b,K), ¬on(c,K), ¬on(e,M), ¬on(e,N)")
print("=" * 70)

extra8 = set()
for s in ["¬(on(b, K))", "¬(on(c, K))", "¬(on(e, M))", "¬(on(e, N))",
          "¬(f = b)", "¬(d = c)"]:
    extra8 |= parse(s, ctx)
base8 = base | extra8

closure8 = ce.direct_consequences(base8, ctx)
aug8 = base8 | closure8

print()
print("Key targets:")
for t in ["same-side(e, c, M)", "same-side(e, b, N)", 
          "¬(same-side(e, d, M))", "¬(same-side(e, f, N))",
          "same-side(e, b, K)", "same-side(a, b, K)",
          "same-side(e, c, K)", "same-side(a, c, K)",
          "same-side(e, d, K)", "same-side(e, f, K)",
          "¬(same-side(e, d, K))", "¬(same-side(e, f, K))",
          "same-side(a, b, K)", "same-side(a, c, K)",
          "¬(on(b, K))", "¬(on(c, K))",
          "¬(same-side(d, c, K))", "¬(same-side(f, b, K))",
          ]:
    lits = parse(t, ctx)
    found = all(l in aug8 for l in lits)
    if found:
        print(f"  ✓ {t}")
    else:
        print(f"  ✗ {t}")

print(f"  Closure size: {len(aug8)}")

# ──────────────────────────────────────────────────────────
# Now the key insight: with ss(e,b,K) or ss(e,c,K) from SS5 on K,
# plus TI axioms on L/M/N through a, can we derive what we need?
# 
# But wait — K doesn't go through a! TI requires three CONCURRENT lines.
# K goes through d and f, not through a.
#
# So we can't use TI with K as one of the three lines.
# We need a different approach.

print()
print("=" * 70)
print("PHASE 9: Alternative — use Pasch with between + same-side")
print("=" * 70)
print()
print("P2: between(a,b,c) ∧ ss(a,d,L) ∧ ¬on(b,L) → ss(b,d,L)")
print("    between(a,b,c) ∧ on(a,L) means ¬ss(a,c,L) [P3]")
print()
print("Key betweenness facts: between(d,a,c), between(f,a,b)")
print()
print("Consider between(d,a,c):")
print("  P2: between(d,a,c) ∧ ss(d,X,L') ∧ ¬on(a,L') → ss(a,X,L')")
print("  if ss(d,e,M) then ss(a,e,M)... but ¬on(a,M) is FALSE (a IS on M)")
print()
print("  P2 reversed: between(c,a,d)? No, between is specific: between(d,a,c).")
print("  P2 with c: between(d,a,c) ∧ ss(d,X,L') ∧ ¬on(a,L') → ss(a,X,L')")
print()
print("Actually, Pasch 2 says: between(a,b,c) ∧ same-side(a,d,L) → same-side(b,d,L)")
print("provided ¬on(b,L).")
print()
print("So between(d,a,c) with:")
print("  If ss(d,e,K), then ss(a,e,K) [since ¬on(a,K)]")
print("  But we have ¬ss(e,a,K), i.e., ¬ss(a,e,K) [by SS2]")
print("  So ¬ss(d,e,K) by contrapositive!")

# Wait — P2 is an implication, not a biconditional. The contrapositive would be:
# ¬ss(b,d,L) → ¬between(a,b,c) ∨ ¬ss(a,d,L) ∨ on(b,L)
# i.e., between(a,b,c) ∧ ¬ss(b,d,L) ∧ ¬on(b,L) → ¬ss(a,d,L)
# Wait no, P2 clause form:
# ¬between(a,b,c) ∨ ¬ss(a,d,L) ∨ on(b,L) ∨ ss(b,d,L)
# Contrapositive: ¬ss(b,d,L) ∧ between(a,b,c) ∧ ¬on(b,L) → ¬ss(a,d,L)

print()
print("P2 contrapositive: between(a,b,c) ∧ ¬ss(b,d,L) ∧ ¬on(b,L) → ¬ss(a,d,L)")
print()
print("between(d,a,c): a=d, b=a, c=c in P2 pattern")
print("  P2: between(d,a,c) ∧ ss(d,e,K) ∧ ¬on(a,K) → ss(a,e,K)")
print("  Contrapos: between(d,a,c) ∧ ¬ss(a,e,K) ∧ ¬on(a,K) → ¬ss(d,e,K)")
print("  We have: between(d,a,c)✓, ¬ss(a,e,K)✓ [=¬ss(e,a,K) by SS2], ¬on(a,K)✓")
print("  → ¬ss(d,e,K) ✓✓✓")
print()
print("Similarly between(f,a,b):")
print("  P2 contrapos: between(f,a,b) ∧ ¬ss(a,e,K) ∧ ¬on(a,K) → ¬ss(f,e,K)")
print("  → ¬ss(f,e,K) ✓✓✓")
print()

# Verify these are in the closure
de_K = parse("¬(same-side(d, e, K))", ctx)
fe_K = parse("¬(same-side(f, e, K))", ctx)
print(f"  ¬ss(d,e,K) in closure: {all(l in aug8 for l in de_K)}")
print(f"  ¬ss(f,e,K) in closure: {all(l in aug8 for l in fe_K)}")

print()
print("Now: SS5 on line K with ¬ss(d,e,K):")
print("  ¬on(d,K)? NO — d IS on K. So SS5 doesn't apply with d.")
print()
print("Hmm. d is ON K, so SS5 can't use d as one of the three points.")
print("Same for f — f is on K.")
print()
print("So ¬ss(d,e,K) and ¬ss(f,e,K) are TRIVIALLY true (d,f on K → ss undefined)")
print("These are not useful for SS5.")

print()
print("=" * 70)
print("PHASE 10: What about using ¬on(e,M), ¬on(e,N) with SS5 on M?")
print("=" * 70)
print()
print("SS5 on line M: ¬on(X,M) ∧ ¬on(Y,M) ∧ ¬on(Z,M) ∧ ¬ss(X,Y,M)")
print("  → ss(X,Z,M) ∨ ss(Y,Z,M)")
print()
print("We want ss(e,c,M). Points not on M: e, c, d.")
print("  X=e, Y=d, Z=c: need ¬ss(e,d,M) → ss(e,c,M) ∨ ss(d,c,M)")
print("  We have ¬ss(d,c,M) [Pasch 3], so → ss(e,c,M) ✓")
print("  BUT we need ¬ss(e,d,M)!")
print()
print("  X=d, Y=e, Z=c: need ¬ss(d,e,M) → ss(d,c,M) ∨ ss(e,c,M)")
print("  same thing")
print()

# So the fundamental question is: how to derive ¬ss(e,d,M)?
# d is on N and K. e is not on K, not on M (via reductio), not on N (via reductio).
# 
# What if we use TI with lines L, M, N through a?
# We need some same-side facts involving e on these lines.
# The problem: we don't have ANY same-side facts involving e on L, M, or N.
#
# What if we use SS5 on line L?
# Points not on L: b?, c?, d?, f?
# We have ¬ss(d,f,L). If ¬on(d,L) and ¬on(f,L):
#   SS5: ¬on(d,L) ∧ ¬on(f,L) ∧ ¬on(X,L) ∧ ¬ss(d,f,L) → ss(d,X,L) ∨ ss(f,X,L)

print()
print("SS5 on line L with ¬ss(d,f,L):")
print("  Need ¬on(d,L), ¬on(f,L)")

d_L = parse("¬(on(d, L))", ctx)
f_L = parse("¬(on(f, L))", ctx)
print(f"  ¬on(d,L) in closure: {all(l in aug8 for l in d_L)}")
print(f"  ¬on(f,L) in closure: {all(l in aug8 for l in f_L)}")

print()
print("If we have ¬on(d,L) and ¬on(f,L):")
print("  X=e: ¬on(e,L)? NO — e IS on L!")
print("  X=b: ¬ss(d,f,L) → ss(d,b,L) ∨ ss(f,b,L)")
print("  X=c: ¬ss(d,f,L) → ss(d,c,L) ∨ ss(f,c,L)")

print()
print("=" * 70)
print("PHASE 11: What if ¬on(d,L) and ¬on(f,L) are derivable?")
print("=" * 70)

# ¬on(d,L): d on N, a on N, a on L, e on L. If d on L, then L = N (since d,a both on L and N, d≠a).
# But is L≠N? L has a and e. N has a and c. If L=N then e on N. But we derive ¬on(e,N) via reductio.
# So L≠N, hence ¬on(d,L). Same logic: L≠M (else e on M, contradiction), hence ¬on(f,L).

# But to derive L≠N we need ¬on(e,N) first (which requires a reductio).
# And to derive L≠M we need ¬on(e,M).
# So the chain is: reductio → ¬on(e,M), ¬on(e,N) → L≠M, L≠N → ¬on(d,L), ¬on(f,L)
# Then SS5 on L: ¬ss(d,f,L) ∧ ¬on(d,L) ∧ ¬on(f,L) ∧ ¬on(b,L) → ss(d,b,L) ∨ ss(f,b,L)

# Can we get ¬on(b,L)?
# b on M, a on M, a on L. If b on L then L=M (b,a both on L and M, b≠a). But L≠M. So ¬on(b,L).
# Similarly ¬on(c,L).

extra11 = set()
for s in ["¬(on(d, L))", "¬(on(f, L))", "¬(on(b, L))", "¬(on(c, L))",
          "¬(L = M)", "¬(L = N)"]:
    extra11 |= parse(s, ctx)
base11 = base8 | extra11

closure11 = ce.direct_consequences(base11, ctx)
aug11 = base11 | closure11

print()
print("With ¬on(d,L), ¬on(f,L), ¬on(b,L), ¬on(c,L), L≠M, L≠N added:")
print()
for t in ["same-side(e, c, M)", "same-side(e, b, N)", 
          "¬(same-side(e, d, M))", "¬(same-side(e, f, N))",
          "same-side(d, b, L)", "same-side(f, b, L)",
          "same-side(d, c, L)", "same-side(f, c, L)",
          "¬(same-side(d, b, L))", "¬(same-side(f, b, L))",
          "same-side(c, f, L)", "same-side(d, b, L)",
          "¬(same-side(b, c, L))"]:
    lits = parse(t, ctx)
    found = all(l in aug11 for l in lits)
    if found:
        print(f"  ✓ {t}")
    else:
        print(f"  ✗ {t}")

print(f"  Closure size: {len(aug11)}")

# Check if ss(d,b,L) and ss(c,f,L) are derived (these are what I.7 + SS5 give)
print()
print("From ¬ss(d,f,L):")
print("  SS5(d,f,b,L): → ss(d,b,L) ∨ ss(f,b,L)")
print("  SS5(d,f,c,L): → ss(d,c,L) ∨ ss(f,c,L)")
print()

# Now with ss(d,b,L) and ss(c,f,L), can TI give us what we need?
# TI1: on(a,L1)∧on(a,L2)∧on(a,L3)∧on(p,L1)∧on(q,L2)∧on(r,L3)
#      ∧ss(q,r,L1)∧ss(p,q,L3) → ¬ss(p,r,L2)
#
# Three lines: L, M, N. all through a.
# For ¬ss(e,d,M): p=e(L), r=d(N), L2=M, q on M = {b,f}
#   q=b: ss(b,d,L)∧ss(e,b,N) → ¬ss(e,d,M)  — need ss(e,b,N)!
#   q=f: ss(f,d,L)∧ss(e,f,N) → ¬ss(e,d,M)  — need ss(e,f,N)! And ss(f,d,L)?

fd_L = parse("same-side(f, d, L)", ctx)
print(f"  ss(f,d,L): {all(l in aug11 for l in fd_L)}")

print()
print("=" * 70) 
print("PHASE 12: What NEW same-side facts are in the closure?")
print("=" * 70)
print()

# Print all same-side facts in aug11
ss_facts = []
for lit in sorted(aug11, key=str):
    s = str(lit)
    if "same-side" in s or "same_side" in s:
        ss_facts.append(s)
for f in sorted(ss_facts):
    print(f"  {f}")

print()
print("=" * 70)
print("PHASE 13: TI1 with ss(d,b,L) — what does it give?")
print("=" * 70)
print()
# TI1 with L1=L, L2=M, L3=N, a=a, p=d(on L? NO, d not on L)")
# Wait, TI needs on(p,L1). d is NOT on L. So d can't be p for L1=L.
#
# Let me be systematic. For TI with L1=L, L2=M, L3=N:
#   on(p,L) means p ∈ {a,e}. But p≠a (often implicit). So p=e.
#   on(q,M) means q ∈ {a,b,f}. q should ≠a. So q ∈ {b,f}.
#   on(r,N) means r ∈ {a,c,d}. r should ≠a. So r ∈ {c,d}.
#
# TI1(e, q, r): ss(q,r,L) ∧ ss(e,q,N) → ¬ss(e,r,M)
#   (e,b,c): ss(b,c,L) ∧ ss(e,b,N) → ¬ss(e,c,M)  — BUT we WANT ss(e,c,M)!
#   (e,b,d): ss(b,d,L) ∧ ss(e,b,N) → ¬ss(e,d,M)  ← this is what we want!
#   (e,f,c): ss(f,c,L) ∧ ss(e,f,N) → ¬ss(e,c,M)  — wrong direction
#   (e,f,d): ss(f,d,L) ∧ ss(e,f,N) → ¬ss(e,d,M)  ← also useful

print("TI1 with L1=L, L2=M, L3=N, p=e:")
print("  (e,b,d): ss(b,d,L) ∧ ss(e,b,N) → ¬ss(e,d,M)")
print("  (e,f,d): ss(f,d,L) ∧ ss(e,f,N) → ¬ss(e,d,M)")
print("  Both need a TARGET (ss(e,b,N) or ss(e,f,N)) as prerequisite!")
print()
print("TI2: ss(q,r,L1) ∧ ¬ss(p,r,L2) ∧ ¬on(r,L2) ∧ p≠a → ss(p,q,L3)")
print("  L1=L, L2=M, L3=N, p=e, q ∈{b,f}, r ∈{c,d}")
print("  (e,b,d): ss(b,d,L) ∧ ¬ss(e,d,M) ∧ ¬on(d,M) ∧ e≠a → ss(e,b,N)")
print("  (e,f,c): ss(f,c,L) ∧ ¬ss(e,c,M) ∧ ¬on(c,M) ∧ e≠a → ss(e,f,N)")
print()
print("TI2(e,b,d) gives ss(e,b,N) from ss(b,d,L) ∧ ¬ss(e,d,M)")
print("TI2(e,f,c) gives ss(e,f,N) from ss(f,c,L) ∧ ¬ss(e,c,M)")
print()
print("STILL CIRCULAR: need ¬ss(e,d,M) to get ss(e,b,N), and vice versa")

print()
print("=" * 70)
print("PHASE 14: What about L1=L, L2=N, L3=M?")
print("=" * 70)
print()
print("TI1: on(p,L), on(q,N), on(r,M): ss(q,r,L) ∧ ss(p,q,M) → ¬ss(p,r,N)")
print("  p=e, q∈{c,d}, r∈{b,f}")
print("  (e,c,f): ss(c,f,L) ∧ ss(e,c,M) → ¬ss(e,f,N)")
print("  (e,d,b): ss(d,b,L) ∧ ss(e,d,M)??? → ¬ss(e,b,N)  WRONG direction")
print("  (e,c,b): ss(c,b,L) ∧ ss(e,c,M) → ¬ss(e,b,N)  WRONG + need ¬ss(b,c,L)")
print("  (e,d,f): ss(d,f,L) ∧ ss(e,d,M) → ¬ss(e,f,N)  but ¬ss(d,f,L)!")
print()
print("TI2 with L1=L, L2=N, L3=M:")
print("  ss(q,r,L) ∧ ¬ss(p,r,N) ∧ ¬on(r,N) ∧ p≠a → ss(p,q,M)")
print("  p=e, q∈{c,d}, r∈{b,f}")
print("  (e,c,f): ss(c,f,L) ∧ ¬ss(e,f,N) ∧ ¬on(f,N) ∧ e≠a → ss(e,c,M)")
print("  (e,d,b): ss(d,b,L) ∧ ¬ss(e,b,N) ∧ ¬on(b,N) ∧ e≠a → ss(e,d,M)")

print()
print("KEY: TI2(e,c,f) on (L,N,M):")
print("  ss(c,f,L) ∧ ¬ss(e,f,N) ∧ ¬on(f,N) ∧ e≠a → ss(e,c,M)")
print()
print("AND TI2(e,b,d) on (L,M,N):")
print("  ss(b,d,L) ∧ ¬ss(e,d,M) ∧ ¬on(d,M) ∧ e≠a → ss(e,b,N)")
print()
print("So if we had BOTH ¬ss(e,f,N) AND ¬ss(e,d,M), TI2 would give us both goals!")
print("But SS5 gives goals FROM these, and TI2 gives goals FROM these.")
print("The problem remains: how to get ¬ss(e,d,M) or ¬ss(e,f,N)?")

print()
print("=" * 70)
print("PHASE 15: Case split / reductio approach")
print("=" * 70)
print()
print("What if we assume ss(e,d,M) and derive a contradiction?")
print()
print("If ss(e,d,M):")
print("  SS4: ss(e,d,M) ∧ ss(e,X,M) → ss(d,X,M)")
print("  TI1(e,b,d) on (L,M,N): need ss(b,d,L)✓ ∧ ss(e,b,N)")
print("  TI1 gives ¬ss(e,d,M) — direct contradiction with assumption!")
print("  BUT only if we have ss(e,b,N).")
print()
print("If ss(e,f,N):")
print("  TI1(e,c,f) on (L,N,M): ss(c,f,L)✓ ∧ ss(e,c,M)")
print("  → ¬ss(e,f,N) — contradiction!")
print("  BUT only if we have ss(e,c,M).")
print()
print("So: assume ss(e,d,M) AND ss(e,f,N):")
print("  From ss(e,d,M): via TI2(e,c,f)(L,N,M) with ¬ss(e,f,N)?")
print("  NO, we assumed ss(e,f,N), not ¬ss(e,f,N)!")
print()
print("Wait — assume ss(e,d,M):")
print("  TI2(e,b,d)(L,M,N): ss(b,d,L) ∧ ¬ss(e,d,M) needed — but we ASSUMED ss(e,d,M)!")
print("  So TI2 doesn't fire.")
print()
print("Assume ss(e,d,M). What can we derive?")

# Let's actually test this
print()
extra15 = parse("same-side(e, d, M)", ctx)
base15 = base11 | extra15

closure15 = ce.direct_consequences(base15, ctx)
aug15 = base15 | closure15

print("With ss(e,d,M) assumed:")
for t in ["same-side(e, c, M)", "same-side(e, b, N)",
          "¬(same-side(e, c, M))", "¬(same-side(e, b, N))",
          "¬(same-side(e, d, M))", "¬(same-side(e, f, N))",
          "same-side(e, f, N)", "same-side(e, f, M)",
          "same-side(d, c, M)", "same-side(e, a, M)",
          "same-side(d, e, M)", "same-side(a, e, M)",
          "same-side(e, b, L)", "same-side(e, c, L)",
          "same-side(e, d, L)", "same-side(e, f, L)",
          ]:
    lits = parse(t, ctx)
    found = all(l in aug15 for l in lits)
    if found:
        print(f"  ✓ {t}")

# Check contradiction
neg_set15 = {l.negated() for l in aug15}
contra15 = aug15 & neg_set15
if contra15:
    print(f"\n  CONTRADICTION FOUND: {contra15}")
else:
    print(f"\n  No contradiction found.")
print(f"  Closure size: {len(aug15)}")

# Now try: assume ss(e,d,M), and also add ss(b,d,L) which we should have
print()
print("With ss(e,d,M) assumed, checking all ss facts:")
ss15 = [str(l) for l in sorted(aug15, key=str) if "same-side" in str(l) or "same_side" in str(l)]
for f in sorted(ss15):
    print(f"  {f}")

# The issue might be that TI1 needs the exact variable setup.
# Let me manually check: do we have all prereqs for TI1?
# TI1: on(a,L) ∧ on(a,M) ∧ on(a,N) ∧ on(b',L) ∧ on(c',M) ∧ on(d',N) ∧ 
#      ss(c',d',L) ∧ ss(b',c',N) → ¬ss(b',d',M)
# 
# With b'=e, c'=b, d'=d: on(e,L)✓ on(b,M)✓ on(d,N)✓
# ss(b,d,L)✓ ∧ ss(e,b,N)??? → ¬ss(e,d,M)

print()
print("For TI1 to give ¬ss(e,d,M), need ss(b,d,L) AND ss(e,b,N).")
print("ss(e,b,N) is one of the GOALS. Circular again.")
print()
print("For TI1 to give ¬ss(e,f,N), need ss(c,f,L) AND ss(e,c,M).")  
print("ss(e,c,M) is one of the GOALS. Circular again.")
print()
print("FUNDAMENTAL ISSUE: every path to ¬ss(e,d,M) or ¬ss(e,f,N)")
print("requires one of the goals as a prerequisite.")
print()
print("The only way to break the cycle is a proof by contradiction or cases")
print("that produces a contradiction from the WRONG side assumption.")

print()
print("=" * 70)
print("PHASE 16: Assume ¬ss(e,c,M) — derive contradiction?")
print("=" * 70)
print()
print("If ¬ss(e,c,M):")
print("  SS5(e,c,d,M): ¬on(e,M)∧¬on(c,M)∧¬on(d,M)∧¬ss(e,c,M) → ss(e,d,M)∨ss(c,d,M)")
print("  We have ¬ss(c,d,M)=¬ss(d,c,M) via SS2. So → ss(e,d,M).")
print()
print("  Now we have ss(e,d,M). What does TI give?")
print("  TI1(L,N,M) with p=e(L), q=d(N), r=b(M): ss(d,b,N)?? ∧ ss(e,d,M)✓ → ¬ss(e,b,N)")

# Hmm wait, let me recheck.
# Actually I keep getting confused with the variable names. Let me be very precise.
# TI1 clause: ¬on(a,L)∧¬on(a,M)∧¬on(a,N)∧¬on(b,L)∧¬on(c,M)∧¬on(d,N)
#             ∧¬ss(c,d,L)∧¬ss(b,c,N)∧¬ss(b,d,M)
# This is an ALL-NEGATIVE clause. It's the negation of:
# on(a,L)∧on(a,M)∧on(a,N)∧on(b,L)∧on(c,M)∧on(d,N)∧ss(c,d,L)∧ss(b,c,N) → ¬ss(b,d,M)
# Wait no — all negative means it's a disjunction of negative literals.
# Actually in clause form: ¬A ∨ ¬B ∨ ... 
# Which means: A ∧ B ∧ ... → ⊥
# But that can't be right for an axiom.

# Let me re-read the clause definition carefully.
print("Let me re-read TI1 carefully...")
print()
print("TI1 clause (from e_axioms.py line 212):")
print("  _clause(¬on(a,L), ¬on(a,M), ¬on(a,N), ¬on(b,L), ¬on(c,M), ¬on(d,N),")
print("          ¬ss(c,d,L), ¬ss(b,c,N), ¬ss(b,d,M))")
print()
print("This is a disjunction: ¬on(a,L) ∨ ¬on(a,M) ∨ ... ∨ ¬ss(b,d,M)")
print("Equivalently: on(a,L)∧on(a,M)∧on(a,N)∧on(b,L)∧on(c,M)∧on(d,N)")
print("              ∧ss(c,d,L)∧ss(b,c,N) → ¬ss(b,d,M)")
print()
print("Wait, ¬ss(b,d,M) is NEGATIVE, so the last literal is ALSO negative.")
print("All 9 literals are negative. The clause is:")
print("  ¬on(a,L) ∨ ¬on(a,M) ∨ ¬on(a,N) ∨ ¬on(b,L) ∨ ¬on(c,M) ∨ ¬on(d,N)")
print("  ∨ ¬ss(c,d,L) ∨ ¬ss(b,c,N) ∨ ¬ss(b,d,M)")
print()
print("Reading as implication: if 8 of them are false (their atoms are true),")
print("the 9th must be true (its atom must be false).")
print("So: on(a,L)∧on(a,M)∧on(a,N)∧on(b,L)∧on(c,M)∧on(d,N)")
print("    ∧ss(c,d,L)∧ss(b,c,N) → ¬ss(b,d,M)   [negating the 9th]")
print()
print("BUT ALSO: on(a,L)∧on(a,M)∧on(a,N)∧on(b,L)∧on(c,M)∧on(d,N)")
print("    ∧ss(c,d,L)∧ss(b,d,M) → ¬ss(b,c,N)   [negating the 8th]")
print()
print("AND: on(a,L)∧on(a,M)∧on(a,N)∧on(b,L)∧on(c,M)∧on(d,N)")
print("    ∧ss(b,c,N)∧ss(b,d,M) → ¬ss(c,d,L)   [negating the 7th]")
print()
print("TI1 is SYMMETRIC in which conclusion you draw!")

# So with ss(e,d,M) assumed:
# TI1 with a=a, L=L, M=M, N=N, b=e(on L), c=b(on M), d=d(on N):
# Need: ss(b,d,L)✓ ∧ ss(e,b,N)? → ¬ss(e,d,M)
# OR: ss(b,d,L)✓ ∧ ss(e,d,M)✓(assumed) → ¬ss(e,b,N)

print()
print("=" * 70)
print("TI1 with ss(e,d,M) ASSUMED:")
print("  on(a,L)✓ on(a,M)✓ on(a,N)✓ on(e,L)✓ on(b,M)✓ on(d,N)✓")
print("  ss(b,d,L)✓ ∧ ss(e,d,M)✓ → ¬ss(e,b,N)")
print()
print("So assuming ss(e,d,M) gives ¬ss(e,b,N)!")
print("And ¬ss(e,b,N) is the NEGATION of one of our goals.")
print("=" * 70)

# But we want ss(e,b,N), not ¬ss(e,b,N).
# So ¬ss(e,c,M) leads to ss(e,d,M) leads to ¬ss(e,b,N).
# Can ¬ss(e,b,N) then give us a contradiction?

print()
print("Chain: ¬ss(e,c,M) → [SS5] ss(e,d,M) → [TI1] ¬ss(e,b,N)")
print()
print("Now with ¬ss(e,b,N), apply SS5 on N:")
print("  SS5(e,b,f,N): ¬on(e,N)∧¬on(b,N)∧¬on(f,N)∧¬ss(e,b,N) → ss(e,f,N)∨ss(b,f,N)")
print("  We have ¬ss(b,f,N)=¬ss(f,b,N) [Pasch 3]. So → ss(e,f,N).")
print()
print("Now with ss(e,f,N):")
print("  TI1 on (L,N,M): on(e,L), on(c,N), on(f,M)")
print("  ss(c,f,L)✓ ∧ ss(e,f,N)✓ → ... wait, let me match variables.")
print()
print("  TI1 clause vars: a,L,M,N,b,c,d")
print("  Map: a→a, L→L, M→N, N→M (SWAPPING M and N)")
print("  b→e(on L), c→c(on N), d→f(on M)")
print("  ss(c,d,L) = ss(c,f,L)✓")
print("  ss(b,c,N) = ss(e,c,N)???") 
print("  Hmm, we need ss(e,c,N), not ss(e,f,N).")
print()

# Let me try the other TI1 reading:
# TI1: on(a,L)∧on(a,M')∧on(a,N')∧on(b,L)∧on(c,M')∧on(d,N')
#      The clause is symmetric in which 3 of the 9 negative lits you "resolve"
# Actually it's not fully symmetric. Let me be precise with the clause:
#   {¬on(a,L), ¬on(a,M), ¬on(a,N), ¬on(b,L), ¬on(c,M), ¬on(d,N),
#    ¬ss(c,d,L), ¬ss(b,c,N), ¬ss(b,d,M)}

# For unit propagation: we provide positive facts, and negative literals get satisfied.
# The clause fires when all-but-one literal is falsified (its atom known positive for negative lit).
# The remaining literal must be true.

# With L1=L, L2=N, L3=M:
# Map TI1 vars: axiom-a→our-a, axiom-L→L, axiom-M→N, axiom-N→M
# axiom-b→e (on axiom-L=L), axiom-c→? (on axiom-M=N), axiom-d→? (on axiom-N=M)
# axiom-c on N: c or d. axiom-d on M: b or f.
# TI1 clause becomes:
# {¬on(a,L), ¬on(a,N), ¬on(a,M), ¬on(e,L), ¬on(axiom-c,N), ¬on(axiom-d,M),
#  ¬ss(axiom-c, axiom-d, L), ¬ss(e, axiom-c, M), ¬ss(e, axiom-d, N)}
# 
# Option: axiom-c=c, axiom-d=f:
# ss(c,f,L) ∧ ss(e,c,M) ∧ ss(e,f,N) → (one must be false)
# If we have ss(c,f,L)✓ and ss(e,f,N)✓, then → ¬ss(e,c,M)
# That's the WRONG direction! That would give ¬ss(e,c,M)!
#
# But wait, we assumed ¬ss(e,c,M) which gave us ss(e,d,M) → ¬ss(e,b,N) → ss(e,f,N).
# Now TI1 with ss(c,f,L) ∧ ss(e,f,N) → ¬ss(e,c,M). 
# That's consistent with our assumption, not a contradiction.

# Option: axiom-c=d, axiom-d=f:
# ss(d,f,L) ∧ ss(e,d,M) ∧ ss(e,f,N) → false
# But ¬ss(d,f,L) is known! So ss(d,f,L) is false. Clause already satisfied.

# Option: axiom-c=c, axiom-d=b:
# ss(c,b,L) ∧ ss(e,c,M) ∧ ss(e,b,N) → false
# ¬ss(b,c,L) is known. So ss(c,b,L) is false. Clause satisfied.

# Option: axiom-c=d, axiom-d=b:
# ss(d,b,L) ∧ ss(e,d,M) ∧ ss(e,b,N) → one must be false
# ss(d,b,L)✓, ss(e,d,M)✓(assumed→derived) → ¬ss(e,b,N) ✓ (already derived)

print()
print("Full chain from ¬ss(e,c,M):")
print("  1. ¬ss(e,c,M) + SS5 → ss(e,d,M)")
print("  2. ss(e,d,M) + ss(b,d,L) + TI1 → ¬ss(e,b,N)")
print("  3. ¬ss(e,b,N) + SS5 → ss(e,f,N)")
print("  4. ss(e,f,N) + ss(c,f,L) + TI1 → ¬ss(e,c,M)")  
print("  Step 4 confirms our assumption — no contradiction!")
print()
print("The system is SELF-CONSISTENT: ¬ss(e,c,M) is consistent with all axioms.")
print("Similarly, ss(e,c,M) would be self-consistent.")
print()
print("Without metric information linking same-side to distances,")
print("the diagrammatic axioms cannot distinguish the two cases.")

print()
print("=" * 70)
print("PHASE 17: WHAT IF WE CONSTRUCT e ON THE SAME SIDE?")
print("=" * 70)
print()
print("The current proof uses let-intersection-circle-circle-opposite-side")
print("to construct e on the opposite side of K from a.")
print("What if we instead use let-intersection-circle-circle-same-side")
print("to construct e on the SAME side of K as a?")
print()
print("Same-side gives: on(e,β), on(e,γ), ss(e,a,K)")
print("Then P2: between(d,a,c) ∧ ss(a,e,K) ∧ ¬on(... wait")
print()
print("Actually, with ss(e,a,K):")
print("  We need ¬on(e,K) separately (same-side construction doesn't give it)")
print("  But ss(e,a,K) → ¬on(e,K) via SS3 ✓")
print()
print("P2: between(d,a,c) ∧ ss(d,e,K) → ss(a,e,K) [if ¬on(a,K)]")
print("Contrapos: ¬ss(a,e,K) → (¬between(d,a,c) ∨ ¬ss(d,e,K) ∨ on(a,K))")
print()
print("But with ss(e,a,K) = ss(a,e,K) via SS2, the contrapositive doesn't help.")
print()
print("What FORWARD derivations from ss(e,a,K)?")
print("  between(d,a,c): P2 says between(d,a,c) ∧ ss(d,X,L') → ss(a,X,L')")
print("  Here X=e, L'=K: between(d,a,c) ∧ ss(d,e,K) → ss(a,e,K)")
print("  This is trivial — d is ON K, so ss(d,e,K) is ill-defined (d on K).")
print()

# Actually wait: can we use ss(e,a,K) with Pasch in the REVERSE direction?
# P2: between(A,B,C) ∧ ss(A,D,L) ∧ ¬on(B,L) → ss(B,D,L)
# 
# I need between(X,Y,Z) where X or Z has a known ss relation with e on some line.
# 
# between(d,a,c): if ss(d,e,M) then... d on K not on M, e not on M.
# No, P2 needs between and same-side on the SAME line.
# 
# Actually P2: between(d,a,c) tells us about points on line N.
# And the same-side is about a DIFFERENT line.
# between(d,a,c) ∧ ss(d, e, M) ∧ ¬on(a, M) → ss(a, e, M)
# But a IS on M! So this doesn't apply.

# What about new betweenness facts? Can we derive any betweenness involving e?
# Probably not without more construction.

print()
print("=" * 70)
print("PHASE 18: Can we use Prop I.7 with e differently?")
print("=" * 70)
print()
print("I.7: If on(c,L) ∧ on(d,L) ∧ ss(a,b,L) ∧ ac=bc ∧ ad=bd ∧ ¬(c=d)")
print("     → ⊥ (contradiction)")
print("Contrapositive: ac=bc ∧ ad=bd ∧ c≠d → ¬ss(a,b,L)")
print()
print("We have: ad=af, de=fe. What about ae?")
print("  ae = ae (reflexive) — not useful for I.7 directly")
print()
print("For I.7 on line L (through a,e):")
print("  Need two points p,q on L with xp=yp and xq=yq for points x,y same-side of L")
print("  Points on L: a, e")
print("  xa=ya and xe=ye for some x,y")
print("  We have: da=fa (ad=af) ✓")
print("  We have: de=fe ✓")
print("  So x=d, y=f, p=a, q=e → d and f on same side of L → contradiction")
print("  I.7: ¬ss(d,f,L) ← already known!")
print()
print("For I.7 on line M:")
print("  Points on M: a, b, f")
print("  Need xp=yp, xq=yq for p,q on M")
print("  x,y not on M. Candidates: e, d, c")
print("  ea=da? We have ad=af but not ad=ae")
print("  ed=? We don't have ed compared to anything on M")
print()
print("For I.7 on line K:")
print("  Points on K: d, f")
print("  dd=fd? → 0 = fd? No.")
print("  de=fe ✓, df=ff? → df=0? No.")

print()
print("=" * 70)
print("FINAL ANALYSIS")  
print("=" * 70)
print()
print("The diagrammatic axioms alone CANNOT determine whether e is")
print("on the same side of M as c or as d. Both are consistent.")
print()
print("This means either:")
print("1. The construction rule needs to provide more information")
print("2. There's a metric/transfer axiom that bridges the gap")
print("3. The proof requires a fundamentally different approach")
print()
print("Checking: does the paper discuss what transfer rules give for I.9?")
print("The paper says (line 1964-1981) that I.7 contrapositive rules out cases.")
print("But our analysis shows I.7 only gives ¬ss(d,f,L), which is insufficient.")
