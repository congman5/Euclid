"""Find which single axiom can derive a target literal from given facts."""
import io, sys, os, json
sys.stdout = io.TextIOWrapper(sys.stdout.buffer, encoding='utf-8', errors='replace')
sys.path.insert(0, '.')

from verifier.e_axiom_match import check_specific_axiom_with_premises, _AXIOM_REGISTRY, _build_registry
from verifier.e_ast import *
from verifier.e_parser import parse_literal

_build_registry()

L = Literal


def find_axiom_for(target_str, fact_strs):
    """Find which registered axiom derives target from given facts."""
    target = parse_literal(target_str)
    facts = set()
    for fs in fact_strs:
        facts.add(parse_literal(fs))

    print(f"\nTarget: {target}")
    found = []
    for name, clause in sorted(_AXIOM_REGISTRY.items()):
        ok, err, prems = check_specific_axiom_with_premises(
            name, facts, {target}, {})
        if ok:
            found.append((name, prems))

    if found:
        for name, prems in found:
            print(f"  {name}:")
            for p in sorted(prems, key=str):
                print(f"    premise: {p}")
    else:
        print(f"  NO axiom found")
    return found


# I.12 L10: ¬on(d, L) - needs Betweenness 1a first to get between(d,a,p)
print("=== I.12 L10 ===")
find_axiom_for("¬(on(d, L))", [
    "on(a, L)", "on(b, L)", "¬(a = b)", "¬(on(p, L))",
    "¬(a = p)", "on(p, M)", "on(a, M)", "on(d, M)",
    "between(p, a, d)", "¬(p = d)",
    "¬(same-side(p, d, L))",
    "between(d, a, p)",  # from B1a on L7
    "¬(a = d)",          # from B1b on between(d,a,p)
])

# I.12 L13: intersects(L, α) via Intersection 2c
# Intersection 3: inside(a,α) ∧ on(a,L) → intersects(L,α)
# But L12 gives inside(p,α) and L4 gives ¬on(p,L)... 
# Intersection 2c is: on(a,α) ∧ on(b,α) ∧ ¬on(a,L) ∧ ¬on(b,L) ∧ ¬same-side(a,b,L) → intersects(L,α)
# deps=[12, 11, 4, 10, 9]
# L12: inside(p, α)
# L11: center(p, α), on(d, α)
# L4: ¬on(p, L)
# L10: ¬on(d, L) [if fixed]
# L9: ¬same-side(p, d, L)
print("\n=== I.12 L13 ===")
find_axiom_for("intersects(L, α)", [
    "inside(p, α)", "center(p, α)", "on(d, α)",
    "¬(on(p, L))", "¬(on(d, L))", "¬(same-side(p, d, L))",
])

# I.12 L15: pe = pd via Segment transfer 3b
# deps=[11, 14]
# L11: center(p, α), on(d, α)
# L14: on(e, α), on(e, L), on(f, α), on(f, L), ¬(e = f)
print("\n=== I.12 L15 ===")
find_axiom_for("pe = pd", [
    "center(p, α)", "on(d, α)", "on(e, α)", "on(e, L)",
    "on(f, α)", "on(f, L)", "¬(e = f)",
])

# I.12 L19: on(h, L) via Betweenness 3
# deps=[18, 14]: between(e, h, f) ∧ on(e, L) ∧ on(f, L) → on(h, L)
print("\n=== I.12 L19 ===")
find_axiom_for("on(h, L)", [
    "between(e, h, f)", "eh = hf",
    "on(e, α)", "on(e, L)", "on(f, α)", "on(f, L)", "¬(e = f)",
])

# I.12 L23: ∠ehp = right-angle via Angle transfer 3a
# AT3a: on(a,L) ∧ on(b,L) ∧ between(a,c,b) ∧ ¬on(d,L) ∧ ∠acd = ∠dcb → ∠acd = ∟
# deps=[14, 18, 4, 21]
print("\n=== I.12 L23 ===")
find_axiom_for("∠ehp = right-angle", [
    "on(e, L)", "on(f, L)", "¬(e = f)",
    "between(e, h, f)", "eh = hf",
    "¬(on(p, L))",
    "∠eph = ∠fph", "∠peh = ∠pfh", "∠ehp = ∠fhp",
])

# I.12 L24: ¬(h = p) via Generality 6
# G6: on(a,L) ∧ ¬on(b,L) → a ≠ b
# deps=[19, 4]: on(h, L) ∧ ¬on(p, L) → ¬(h = p)
print("\n=== I.12 L24 ===")
find_axiom_for("¬(h = p)", [
    "on(h, L)", "¬(on(p, L))",
])

# I.12 L25: ¬(e = h) via Betweenness 1b
# B1b: between(a,b,c) → a ≠ b
# deps=[18]: between(e, h, f) → ¬(e = h)
print("\n=== I.12 L25 ===")
find_axiom_for("¬(e = h)", [
    "between(e, h, f)", "eh = hf",
])

