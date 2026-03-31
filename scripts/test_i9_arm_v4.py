"""Test I.9 proof with arm construction — g instead of d' to avoid parser issues."""
from __future__ import annotations
import sys, os
sys.path.insert(0, os.path.join(os.path.dirname(__file__), ".."))
os.environ["PYTHONIOENCODING"] = "utf-8"
from scripts.real_proofs import PB
from verifier.unified_checker import verify_e_proof_json


def build_i9_arm():
    pb = PB(
        "Prop.I.9",
        [
            "¬(a = b)", "¬(a = c)", "¬(b = c)",
            "on(a, M)", "on(b, M)",
            "on(a, N)", "on(c, N)",
            "¬(on(c, M))", "¬(on(b, N))",
        ],
        "∠bae = ∠cae, same-side(e, c, M), same-side(e, b, N)",
    )
    G = pb.auto_given()

    L10 = pb.s("center(a, α), on(b, α)", "let-circle", [G["¬(a = b)"]])
    L11 = pb.s("inside(a, α)", "Generality 3", [L10])
    L12 = pb.s("on(g, α), on(g, N), between(g, a, c)",
               "let-intersection-line-circle-extend",
               [L11, G["on(a, N)"], G["¬(a = c)"], G["on(c, N)"]])
    L13 = pb.s("on(d, α), on(d, N), between(g, a, d)",
               "let-intersection-line-circle-other",
               [L12, L12, L11, G["on(a, N)"]])
    L14 = pb.s("on(f, α), on(f, M), between(f, a, b)",
               "let-intersection-line-circle-extend",
               [L11, G["on(a, M)"], G["¬(a = b)"], G["on(b, M)"]])
    L15 = pb.s("ad = ab", "Segment transfer 3b", [L10, L13])
    L16 = pb.s("¬(g = a)", "Betweenness 1b", [L12])
    L17 = pb.s("¬(d = a)", "Betweenness 1b", [L13])
    L18 = pb.s("¬(M = N)", "Generality 5", [G["on(b, M)"], G["¬(on(b, N))"]])
    L19 = pb.s("¬(on(d, M))", "Generality 1",
               [G["on(a, M)"], G["on(a, N)"], L13, L17, L18])
    L20 = pb.s("¬(on(g, M))", "Generality 1",
               [G["on(a, M)"], G["on(a, N)"], L12, L16, L18])
    L21 = pb.s("¬(a = f)", "Betweenness 1b", [L14])
    L22 = pb.s("¬(on(f, N))", "Generality 1",
               [G["on(a, M)"], G["on(a, N)"], L14, L21, L18])
    L23 = pb.s("¬(d = b)", "Generality 6", [G["on(b, M)"], L19])
    L24 = pb.s("on(d, K), on(b, K)", "let-line", [L23])
    L25 = pb.s("center(d, β), on(b, β)", "let-circle", [L23])
    L26 = pb.s("center(b, γ), on(d, γ)", "let-circle", [L23])
    L27 = pb.s("inside(d, β)", "Generality 3", [L25])
    L28 = pb.s("inside(b, γ)", "Generality 3", [L26])
    L29 = pb.s("intersects(β, γ)", "Intersection 5", [L25, L26, L27, L28])
    L30 = pb.s("¬(K = N)", "Generality 5", [L24, G["¬(on(b, N))"]])
    L31 = pb.s("¬(K = M)", "Generality 5", [L24, L19])
    L32 = pb.s("¬(on(a, K))", "Generality 1", [L24, G["on(a, N)"], L13, L17, L30])
    L33 = pb.s("on(e, β), on(e, γ), ¬(same-side(e, a, K)), ¬(on(e, K))",
               "let-intersection-circle-circle-opposite-side",
               [L29, L25, L26, L24, L32])
    L34 = pb.s("de = db", "Segment transfer 3b", [L25, L33])
    L35 = pb.s("be = bd", "Segment transfer 3b", [L26, L33])
    L36 = pb.s("db = bd", "M3 — Symmetry", [])
    L37 = pb.s("de = be", "CN1 — Transitivity", [L34, L35, L36])
    L38 = pb.s("¬(e = d)", "Generality 6", [L24, L33])
    L39 = pb.s("¬(e = b)", "Generality 6", [L24, L33])
    L40 = pb.s("¬(a = e)", "Same-side 6", [L33, L24, G["on(a, N)"], L13, L17, L30])
    L41 = pb.s("ae = ae", "CN4 — Reflexivity", [])
    L42 = pb.s("∠dae = ∠bae, ∠ade = ∠abe, ∠aed = ∠aeb, △ade = △abe",
               "SSS", [L15, L37, L41])
    L43 = pb.s("on(a, L), on(e, L)", "let-line", [L40])

    # Reductio: not on(e, M)
    Lasm1 = pb.assume("on(e, M)")
    Lp4a = pb.s("between(a, b, e)", "Pasch 4",
                 [L31, L24, Lasm1, G["on(a, M)"], G["on(b, M)"], G["¬(a = b)"], L39, L33])
    Lb1a = pb.s("between(b, a, f)", "Betweenness 1a", [L14])
    Lb1b = pb.s("between(e, b, a)", "Betweenness 1a", [Lp4a])
    Lb5a = pb.s("between(e, b, f)", "Betweenness 5", [Lb1b, Lb1a])
    pb.s("¬(between(b, a, f))", "Betweenness 7", [Lb1b, Lb5a])
    pb.s("⊥", "⊥-intro", [Lasm1])
    Lnot_eM = pb.reductio("¬(on(e, M))", Lasm1)
    pb._lines[-1]["justification"] = "⊥-elim"

    # Reductio: not on(e, N)
    Lasm2 = pb.assume("on(e, N)")
    Lp4b = pb.s("between(a, d, e)", "Pasch 4",
                 [L30, L24, Lasm2, G["on(a, N)"], L13, L17, L38, L33])
    Lb5b = pb.s("between(g, a, e)", "Betweenness 5", [L13, Lp4b])
    pb.s("¬(between(a, d, e))", "Betweenness 7", [L13, Lb5b])
    pb.s("⊥", "⊥-intro", [Lasm2])
    Lnot_eN = pb.reductio("¬(on(e, N))", Lasm2)
    pb._lines[-1]["justification"] = "⊥-elim"

    # DA6 supplementary angles
    Lda6a = pb.s("∠gae + ∠eac = right-angle + right-angle",
                  "Angle transfer 6", [L12, G["on(c, N)"], L12, Lnot_eN, L40])
    Lda6b = pb.s("∠gae + ∠ead = right-angle + right-angle",
                  "Angle transfer 6", [L12, L13, L13, Lnot_eN, L40])
    Lcn1a = pb.s("∠gae + ∠eac = ∠gae + ∠ead",
                  "CN1 — Transitivity", [Lda6a, Lda6b])
    Lcn3a = pb.s("∠eac = ∠ead", "CN3 — Subtraction", [Lcn1a, Lda6a])
    Langle = pb.s("∠bae = ∠cae", "CN1 — Transitivity", [Lcn3a, L42])

    # Same-side(d, c, M) via P3+SS5
    Lnss_gd = pb.s("¬(same-side(g, d, M))", "Pasch 3", [L13, G["on(a, M)"]])
    Lnss_gc = pb.s("¬(same-side(g, c, M))", "Pasch 3", [L12, G["on(a, M)"]])
    Lss_dcM = pb.s("same-side(d, c, M)", "Same-side 5",
                    [L20, L19, G["¬(on(c, M))"], Lnss_gd, Lnss_gc])

    Lnss_fb = pb.s("¬(same-side(f, b, N))", "Pasch 3", [L14, G["on(a, N)"]])
    Lg_ne_d = pb.s("¬(g = d)", "Betweenness 1c", [L13])
    Lnot_gK = pb.s("¬(on(g, K))", "Generality 1",
                    [L13, L24, L12, Lg_ne_d, L30])

    # C5 application 1: ss(e, d, M)
    Lss_edM = pb.s("same-side(e, d, M)", "Circle 5",
                    [L26, L25, L26, L25, L33, L33,
                     L24, L24, L32, L33, L33,
                     G["on(a, M)"], G["on(b, M)"], L19, Lnot_eM, L15])

    # SS2 + SS4: ss(e,d,M) + ss(d,c,M) → ss(e,c,M)
    Lss_deM = pb.s("same-side(d, e, M)", "Same-side 2", [Lss_edM])
    Lss_ecM = pb.s("same-side(e, c, M)", "Same-side 4", [Lss_deM, Lss_dcM])

    # C5 application 2: ss(e, b, N)
    Lss_ebN = pb.s("same-side(e, b, N)", "Circle 5",
                    [L25, L26, L25, L26, L33, L33,
                     L24, L24, L32, L33, L33,
                     G["on(a, N)"], L13, G["¬(on(b, N))"], Lnot_eN, L15])

    return pb.build()


def main():
    proof = build_i9_arm()
    result = verify_e_proof_json(proof)
    lines = proof.get("lines", [])
    n = len(lines)
    ok = sum(1 for lr in result.line_results.values() if lr.valid)
    fail = n - ok
    print(f"\n=== {ok}/{n} lines verified ({fail} failures) ===\n")
    for line in lines:
        lid = line["id"]
        stmt = line["statement"][:70]
        lr = result.line_results.get(lid)
        if lr and lr.valid:
            print(f"  \u2713 L{lid}: {stmt}")
        else:
            errs = lr.errors if lr else ["not checked"]
            print(f"  \u2717 L{lid}: {stmt}")
            for e in errs[:2]:
                print(f"        {e[:100]}")
    if result.errors:
        print("\nGlobal errors:")
        for e in result.errors[:5]:
            print(f"  {e[:120]}")


if __name__ == "__main__":
    main()
