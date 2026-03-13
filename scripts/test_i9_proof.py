"""Test I.9 proof."""
import sys, json
sys.path.insert(0, '.')

from scripts.real_proofs import PB

def p9_test():
    b = PB("Prop.I.9",
           ["\u00ac(a = b)", "\u00ac(a = c)", "\u00ac(b = c)",
            "on(a, M)", "on(b, M)", "on(a, N)", "on(c, N)",
            "\u00ac(on(c, M))", "\u00ac(on(b, N))"],
           "\u2220bae = \u2220cae, same-side(e, c, M), same-side(e, b, N)")
    gids = b.auto_given()
    # Circle α center a, radius ab
    s10 = b.s("center(a, \u03b1), on(b, \u03b1)", "let-circle", [gids["\u00ac(a = b)"]])
    # inside(a, α) from Generality 3
    s11 = b.s("inside(a, \u03b1)", "Generality 3", [s10])
    # d on N between a and c, also on α (extra assertion)
    s12 = b.s("on(d, N), between(a, d, c), on(d, \u03b1)",
              "let-point-on-line-between", [gids["on(a, N)"], gids["on(c, N)"], gids["\u00ac(a = c)"]])
    # f on M between a and b, also on α (extra assertion)
    s13 = b.s("on(f, M), between(a, f, b), on(f, \u03b1)",
              "let-point-on-line-between", [gids["on(a, M)"], gids["on(b, M)"], gids["\u00ac(a = b)"]])
    # ad = ab from radius (Transfer: center(a,α), on(b,α), on(d,α) → ad=ab)
    s14 = b.s("ad = ab", "Transfer", [s10, s12])
    # af = ab from radius
    s15 = b.s("af = ab", "Transfer", [s10, s13])
    # ad = af
    s16 = b.s("ad = af", "Metric", [s14, s15])
    # Equilateral triangle on df (I.1) → point e
    s17 = b.s("df = de, df = fe, \u00ac(e = d), \u00ac(e = f)",
              "Prop.I.1", [s16])
    # de = fe
    s18 = b.s("de = fe", "Metric", [s17])
    # ae = ae
    s19 = b.s("ae = ae", "Metric", [])
    # SSS → ∠dae = ∠fae
    s20 = b.s("\u2220dae = \u2220fae, \u2220ade = \u2220afe, \u2220aed = \u2220aef, \u25b3ade = \u25b3afe",
              "SSS", [s16, s18, s19])
    # Need a line through a and e for DA4
    s21 = b.s("\u00ac(e = a)", "Diagrammatic", [])
    s22 = b.s("on(a, K), on(e, K)", "let-line", [s21])
    # DA4: ∠dae = ∠cae (d,c on N, vertex a; e on K)
    s23 = b.s("\u2220dae = \u2220cae", "Transfer", [])
    # DA4: ∠fae = ∠bae (f,b on M, vertex a; e on K)
    s24 = b.s("\u2220fae = \u2220bae", "Transfer", [])
    # ∠bae = ∠cae
    s25 = b.s("\u2220bae = \u2220cae", "Metric", [s20, s23, s24])
    # same-side goals
    s26 = b.s("same-side(e, c, M)", "Diagrammatic", [])
    s27 = b.s("same-side(e, b, N)", "Diagrammatic", [])
    return b.build()

proof = p9_test()

# Verify
from verifier.unified_checker import verify_e_proof_json
result = verify_e_proof_json(proof)
print(f"\nAccepted: {result.accepted}")
if result.errors:
    for e in result.errors:
        print(f"  Error: {e}")
for lid, lr in result.line_results.items():
    if not lr.valid:
        print(f"  Line {lid}: INVALID - {lr.errors}")
    else:
        print(f"  Line {lid}: OK")
