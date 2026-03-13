"""Test new I.9 proof approach with DA4 fix."""
import sys
sys.path.insert(0, '.')

from scripts.real_proofs import PB
from verifier.unified_checker import verify_e_proof_json

b = PB("Prop.I.9",
    ["\u00ac(a = b)", "\u00ac(a = c)", "\u00ac(b = c)",
     "on(a, M)", "on(b, M)", "on(a, N)", "on(c, N)",
     "same-side(c, b, M)", "same-side(b, c, N)"],
    "\u2220bae = \u2220cae, same-side(e, c, M), same-side(e, b, N)")
gids = b.auto_given()

# Circle centered at a through b
s10 = b.s("center(a, \u03b1), on(b, \u03b1)", "let-circle", [1])
s11 = b.s("inside(a, \u03b1)", "Generality 3", [s10])

# d on circle and line N, between a and c (same side of a as c)
s12 = b.s("on(d, \u03b1), on(d, N), between(a, d, c)",
          "let-intersection-line-circle-between", [s11, 6, 7])

# f on circle and line M, between a and b (same side of a as b)
s13 = b.s("on(f, \u03b1), on(f, M), between(a, f, b)",
          "let-intersection-line-circle-between", [s11, 4, 5])

# Radii equal: ad = ab, af = ab => ad = af
s14 = b.s("ad = ab", "Transfer", [s10, s12])
s15 = b.s("af = ab", "Transfer", [s10, s13])
s16 = b.s("ad = af", "Metric", [s14, s15])

# Equilateral triangle on df (I.1)
s17 = b.s("df = de, df = fe, \u00ac(e = d), \u00ac(e = f)",
          "Prop.I.1", [s16])
s18 = b.s("de = fe", "Metric", [s17])
s19 = b.s("ae = ae", "Metric", [])

# SSS on triangles ade and afe
s20 = b.s("\u2220dae = \u2220fae, \u2220ade = \u2220afe, "
          "\u2220aed = \u2220aef, \u25b3ade = \u25b3afe",
          "SSS", [s16, s18, s19])

# Line through a and e for DA4
s20b = b.s("on(a, K), on(e, K)", "let-line", [])

# DA4: d,c on same ray from a on line N, e on line K through a
s21 = b.s("\u2220dae = \u2220cae", "Transfer", [])

# DA4: f,b on same ray from a on line M, e on line K through a
s22 = b.s("\u2220fae = \u2220bae", "Transfer", [])

# Combine via metric: dae=fae + dae=cae + fae=bae => bae=cae
s23 = b.s("\u2220bae = \u2220cae", "Metric", [s20, s21, s22])

# same-side goals
s24 = b.s("same-side(e, c, M)", "Diagrammatic", [])
s25 = b.s("same-side(e, b, N)", "Diagrammatic", [])

proof = b.build()
r = verify_e_proof_json(proof)
for lid, lr in sorted(r.line_results.items()):
    status = "OK" if lr.valid else f"FAIL {lr.errors}"
    print(f"  L{lid}: {status}")
print(f"Accepted: {r.accepted}")
print(f"Errors: {r.errors}")
