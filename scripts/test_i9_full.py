"""
Test complete I.9 proof strategy.

Approach:
  Steps 10-38: Construction + SSS (already verified working)
  Steps 39-40: DA6 supplementary angles (replaces failing DA4)
  Step  41:    CN1 transitivity  (∠dae + ∠eac = ∠fae + ∠eab)
  Step  42:    CN3 subtraction   (∠eac = ∠eab, since ∠dae = ∠fae)
  Step  43:    M4  angle symmetry (∠eac = ∠cae)
  Step  44:    M4  angle symmetry (∠eab = ∠bae)
  Step  45:    CN1 transitivity  (∠bae = ∠cae)
  Then same-side derivation via reductio:
  Steps 46-47: P3 for ¬ss(d,c,M) and ¬ss(f,b,N)
  Steps 48-49: G5 for K≠M and K≠N
  Steps 50-56: Reductio ¬on(e,M)
  Steps 57-63: Reductio ¬on(e,N)
  Step  64:    G1 ¬on(a,K)
  Step  65-66: P2 for ss(a,c,K) and ss(a,b,K)
  Steps 67-74: Reductio ss(e,c,M) via I.7
  Steps 75-82: Reductio ss(e,b,N) via I.7
"""
from __future__ import annotations
import sys, os
sys.path.insert(0, os.path.join(os.path.dirname(__file__), ".."))
os.environ["PYTHONIOENCODING"] = "utf-8"

from scripts.real_proofs import PB
from verifier.unified_checker import verify_e_proof_json


def build_i9():
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

    # --- Construction (steps 10-27, same as current proof) ---
    L10 = pb.s("center(a, α), on(b, α)", "let-circle", [G["¬(a = b)"]])
    L11 = pb.s("inside(a, α)", "Generality 3", [L10])
    L12 = pb.s("on(d, α), on(d, N), between(d, a, c)",
               "let-intersection-line-circle-extend",
               [L11, G["on(a, N)"], G["¬(a = c)"], G["on(c, N)"]])
    L13 = pb.s("on(f, α), on(f, M), between(f, a, b)",
               "let-intersection-line-circle-extend",
               [L11, G["on(a, M)"], G["¬(a = b)"], G["on(b, M)"]])
    L14 = pb.s("ad = ab", "Segment transfer 3b", [L10, L12])
    L15 = pb.s("af = ab", "Segment transfer 3b", [L10, L13])
    L16 = pb.s("ad = af", "CN1 — Transitivity", [L14, L15])
    L17 = pb.s("¬(d = a)", "Betweenness 1b", [L12])
    L18 = pb.s("¬(M = N)", "Generality 5", [G["on(b, M)"], G["¬(on(b, N))"]])
    L19 = pb.s("¬(on(d, M))", "Generality 1",
               [G["on(a, M)"], G["on(a, N)"], L12, L17, L18])
    L20 = pb.s("¬(f = d)", "Generality 6", [L13, L19])
    L21 = pb.s("center(d, β), on(f, β)", "let-circle", [L20])
    L22 = pb.s("center(f, γ), on(d, γ)", "let-circle", [L20])
    L23 = pb.s("inside(d, β)", "Generality 3", [L21])
    L24 = pb.s("inside(f, γ)", "Generality 3", [L22])
    L25 = pb.s("intersects(β, γ)", "Intersection 5", [L21, L22, L23, L24])
    L26 = pb.s("on(d, K), on(f, K)", "let-line", [L20])
    L27 = pb.s("on(e, β), on(e, γ), ¬(same-side(e, a, K)), ¬(on(e, K))",
               "let-intersection-circle-circle-opposite-side",
               [L25, L21, L22, L26, L12, L13,
                G["on(b, M)"], G["on(a, N)"], G["¬(on(b, N))"],
                L17, L18, L19, G["on(a, M)"]])

    # --- Metric (steps 28-36) ---
    L28 = pb.s("de = df", "Segment transfer 3b", [L21, L27])
    L29 = pb.s("fe = fd", "Segment transfer 3b", [L22, L27])
    L30 = pb.s("df = fd", "M3 — Symmetry", [])
    L31 = pb.s("de = fe", "CN1 — Transitivity", [L28, L29, L30])
    L32 = pb.s("¬(e = d)", "Generality 6", [L26, L27])
    L33 = pb.s("¬(e = f)", "Generality 6", [L26, L27])
    L34 = pb.s("¬(a = e)", "Same-side 6",
               [L27, L26, G["on(a, N)"], L12, L17, L18])
    L35 = pb.s("ae = ae", "CN4 — Reflexivity", [])
    L36 = pb.s("∠dae = ∠fae, ∠ade = ∠afe, ∠aed = ∠aef, △ade = △afe",
               "SSS", [L16, L31, L35])
    L37 = pb.s("¬(a = f)", "Betweenness 1b", [L13])

    # --- Let line L (through a and e) ---
    L38 = pb.s("on(a, L), on(e, L)", "let-line", [L34])

    # =========================================================
    # ANGLE PART — DA6 supplementary angles approach
    # =========================================================
    # DA6: between(d,a,c) ∧ on(d,N) ∧ on(c,N) ∧ ¬on(e,N) ∧ a≠e
    #      → ∠dae + ∠eac = R + R
    # Need: ¬(on(e, N)) — derive via G1 similar to ¬(on(d, M))
    # between(f,a,b) and on(f,M), on(b,M) → on(f,M) already.
    # For ¬on(e,N): need N≠K or similar reasoning
    # Actually we need to get ¬(on(f,N)) for G5/G1, or get ¬(on(e,N)) directly.
    # Let's try to derive ¬(on(f, N)) first.
    L_fneqa = pb.s("¬(f = a)", "Betweenness 1b", [L13])  # wait already L37
    # Actually we need ¬(on(f,N)). f is on M. If f were on N too, then
    # on(f,M) ∧ on(f,N) ∧ on(a,M) ∧ on(a,N) ∧ f≠a → M=N. But M≠N. So ¬on(f,N).
    # This is G1 contrapositive: on(a,M)∧on(a,N)∧on(f,M)∧f≠a∧M≠N → ¬on(f,N)
    L39 = pb.s("¬(on(f, N))", "Generality 1",
               [G["on(a, M)"], G["on(a, N)"], L13, L37, L18])

    # Similarly ¬(on(e,N)): we can use a different path.
    # Let's get N≠K first via G5.
    L40 = pb.s("¬(N = K)", "Generality 5", [G["on(c, N)"], G["¬(on(c, M))"],
               L12, L13, L26, G["on(a, N)"], G["on(a, M)"]])
    # Hmm, G5 is: on(a,L)∧¬on(a,M)→L≠M. We need on(X,N)∧¬on(X,K)→N≠K.
    # d is on N. Is d on K? d IS on K (from L26: on(d,K)).
    # c is on N. Is c on K? Maybe not. Let's check.
    # f is on K (L26). d is on K (L26). c is on N but probably not on K.
    # Actually we can't easily prove ¬on(c,K) without more work.
    # 
    # Let me think differently. For ¬on(e,N), we can try:
    # e is on K (no, ¬on(e,K) from L27). e is on β and γ.
    # 
    # Alternative: use reductio like we do for ¬on(e,M).
    # Or: derive N≠K, then note on(e,K) is false (¬on(e,K)), but that gives K≠N
    # if e is on N — but we're trying to prove e is NOT on N.
    #
    # Actually let me just use the same reductio approach for ¬on(e,N).
    # But wait — do we even need ¬on(e,N) for the DA6 step? DA6 is about line N.
    # DA6: on(a,L')∧on(b',L')∧between(a,c',b')∧¬on(d',L')∧c'≠d'
    #      → (∠a'c'd' + ∠d'c'b') = (R + R)
    # 
    # For ∠dae + ∠eac = R + R:
    #   The "line" in DA6 is N (the line with d,a,c collinear)
    #   a_DA6 = d, b_DA6 = c (on N, with between(d,a,c) — a is between them)
    #   c_DA6 = a (the vertex of the angles)
    #   d_DA6 = e (the point not on N)
    #   So: on(d,N), on(c,N), between(d,a,c), ¬on(e,N), a≠e
    #        → ∠dae + ∠eac = R + R
    #
    # We need ¬on(e,N). Let me try to derive this.
    # 
    # Hmm, this is getting complex. Let me first try without ¬on(e,N) and see
    # what the test gives us, or use the reductio approach.

    # Actually, let's just test the reductio approach for ¬on(e,M) and ¬on(e,N)
    # BEFORE the angle stuff. Then use those results.

    # Let me restart with a cleaner ordering...
    pass


def build_i9_v2():
    """Build I.9 with correct ordering."""
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

    # ── Construction (10-27) ──────────────────────────────────────
    L10 = pb.s("center(a, α), on(b, α)", "let-circle", [G["¬(a = b)"]])
    L11 = pb.s("inside(a, α)", "Generality 3", [L10])
    L12 = pb.s("on(d, α), on(d, N), between(d, a, c)",
               "let-intersection-line-circle-extend",
               [L11, G["on(a, N)"], G["¬(a = c)"], G["on(c, N)"]])
    L13 = pb.s("on(f, α), on(f, M), between(f, a, b)",
               "let-intersection-line-circle-extend",
               [L11, G["on(a, M)"], G["¬(a = b)"], G["on(b, M)"]])
    L14 = pb.s("ad = ab", "Segment transfer 3b", [L10, L12])
    L15 = pb.s("af = ab", "Segment transfer 3b", [L10, L13])
    L16 = pb.s("ad = af", "CN1 — Transitivity", [L14, L15])
    L17 = pb.s("¬(d = a)", "Betweenness 1b", [L12])
    L18 = pb.s("¬(M = N)", "Generality 5",
               [G["on(b, M)"], G["¬(on(b, N))"]])
    L19 = pb.s("¬(on(d, M))", "Generality 1",
               [G["on(a, M)"], G["on(a, N)"], L12, L17, L18])
    L20 = pb.s("¬(f = d)", "Generality 6", [L13, L19])
    L21 = pb.s("center(d, β), on(f, β)", "let-circle", [L20])
    L22 = pb.s("center(f, γ), on(d, γ)", "let-circle", [L20])
    L23 = pb.s("inside(d, β)", "Generality 3", [L21])
    L24 = pb.s("inside(f, γ)", "Generality 3", [L22])
    L25 = pb.s("intersects(β, γ)", "Intersection 5",
               [L21, L22, L23, L24])
    L26 = pb.s("on(d, K), on(f, K)", "let-line", [L20])
    L27 = pb.s(
        "on(e, β), on(e, γ), ¬(same-side(e, a, K)), ¬(on(e, K))",
        "let-intersection-circle-circle-opposite-side",
        [L25, L21, L22, L26, L12, L13,
         G["on(b, M)"], G["on(a, N)"], G["¬(on(b, N))"],
         L17, L18, L19, G["on(a, M)"]])

    # ── Metric equalities + distinctness (28-37) ──────────────────
    L28 = pb.s("de = df", "Segment transfer 3b", [L21, L27])
    L29 = pb.s("fe = fd", "Segment transfer 3b", [L22, L27])
    L30 = pb.s("df = fd", "M3 — Symmetry", [])
    L31 = pb.s("de = fe", "CN1 — Transitivity", [L28, L29, L30])
    L32 = pb.s("¬(e = d)", "Generality 6", [L26, L27])
    L33 = pb.s("¬(e = f)", "Generality 6", [L26, L27])
    L34 = pb.s("¬(a = e)", "Same-side 6",
               [L27, L26, G["on(a, N)"], L12, L17, L18])
    L35 = pb.s("ae = ae", "CN4 — Reflexivity", [])
    L36 = pb.s(
        "∠dae = ∠fae, ∠ade = ∠afe, ∠aed = ∠aef, △ade = △afe",
        "SSS", [L16, L31, L35])
    L37 = pb.s("¬(a = f)", "Betweenness 1b", [L13])

    # ── Let line L (ae) ───────────────────────────────────────────
    L38 = pb.s("on(a, L), on(e, L)", "let-line", [L34])

    # ── Distinctness / not-on facts needed later ──────────────────
    # ¬(on(f, N)) via G1: on(a,M)∧on(a,N)∧on(f,M)∧f≠a∧M≠N → ¬on(f,N)
    L39 = pb.s("¬(on(f, N))", "Generality 1",
               [G["on(a, M)"], G["on(a, N)"], L13, L37, L18])

    # K≠M: on(d,K)∧¬on(d,M) → K≠M
    L40 = pb.s("¬(K = M)", "Generality 5", [L26, L19])
    # K≠N: on(f,K)∧¬on(f,N) → K≠N
    L41 = pb.s("¬(K = N)", "Generality 5", [L26, L39])

    # ── Reductio: ¬on(e, M) ──────────────────────────────────────
    # Assume on(e,M). P4 gives between(a,f,e) [since on(f,M), on(e,M),
    # on(a,M), f≠a, e≠a... wait, ¬ss(a,e,K) + on(f,K) → ¬ss(a,e,K).
    # Need more thought. Let me use the verified chain from the summary:
    # Assume on(e,M) → P4(between(a,f,e)) → B1a→B5 give between(b,a,e)
    # → B7 gives ¬between(a,f,e) → ⊥ → ¬on(e,M)
    #
    # Actually for P4: L≠M, on(f,L)∧on(f,M)∧on(a,M)∧on(e,M)∧a≠f∧e≠f
    #                  ∧¬ss(a,e,L) → between(a,f,e)
    # Here L=K, M=M: K≠M ✓, on(f,K) ✓, on(f,M) ✓, on(a,M) ✓,
    #                on(e,M)=assumed, a≠f ✓, e≠f ✓
    #                ¬ss(a,e,K): we have ¬ss(e,a,K) from L27, by SS2
    #                contrapositive → ¬ss(a,e,K) should be in closure
    Lasm1 = pb.assume("on(e, M)")
    Lp4_1 = pb.s("between(a, f, e)", "Pasch 4",
                  [L40, L26, Lasm1, G["on(a, M)"], L13, L37, L33, L27])
    # B1a: between(a,f,e) → between(e,f,a)
    Lb1_1 = pb.s("between(e, f, a)", "Betweenness 1a", [Lp4_1])
    # B5: between(f,a,b) ∧ between(a,f,e) → ... wait
    # between(f,a,b) from L13. between(a,f,e) from Lp4_1.
    # B5: between(a,b,c) ∧ between(b,c,d) → between(a,b,d)
    # We have between(a,f,e) and between(f,a,b).
    # B4: between(a,b,c) ∧ between(a,d,b) → between(a,d,c)
    # between(f,a,b) ∧ between(f,?,a)... hmm let me be careful.
    #
    # from B1a: between(f,a,b) → between(b,a,f)
    # between(b,a,f) and between(a,f,e)
    # B5: between(a,b,c) ∧ between(b,c,d) → between(a,b,d)
    # With a=b, b=a, c=f, d=e: between(b,a,f)∧between(a,f,e) → between(b,a,e)
    Lb1_2 = pb.s("between(b, a, f)", "Betweenness 1a", [L13])
    Lb5_1 = pb.s("between(b, a, e)", "Betweenness 5", [Lb1_2, Lp4_1])
    # B7: between(a,b,c)∧between(a,b,d) → ¬between(b,c,d)
    # We want ¬between(a,f,e). Use:
    # between(b,a,f) and between(b,a,e) → ¬between(a,f,e)  [B7 with a=b,b=a,c=f,d=e]
    Lb7_1 = pb.s("¬(between(a, f, e))", "Betweenness 7", [Lb5_1, Lb1_2])
    # ⊥-intro: between(a,f,e) ∧ ¬between(a,f,e)
    Lbot1 = pb.s("⊥", "⊥-intro", [Lasm1])
    # ⊥-elim: conclude ¬on(e,M)
    Lnot_eM = pb.reductio("¬(on(e, M))", Lasm1)
    # Fix justification from "Reductio" to "⊥-elim"
    pb._lines[-1]["justification"] = "⊥-elim"

    # ── Reductio: ¬on(e, N) ──────────────────────────────────────
    # Same pattern with d instead of f, N instead of M
    # P4: K≠N, on(d,K), on(d,N), on(a,N), on(e,N)=assumed,
    #     a≠d, e≠d, ¬ss(a,e,K) → between(a,d,e)
    Lasm2 = pb.assume("on(e, N)")
    Lp4_2 = pb.s("between(a, d, e)", "Pasch 4",
                  [L41, L26, Lasm2, G["on(a, N)"], L12, L17, L32, L27])
    Lb1_3 = pb.s("between(e, d, a)", "Betweenness 1a", [Lp4_2])
    # between(d,a,c) from L12. B1a: between(c,a,d)
    Lb1_4 = pb.s("between(c, a, d)", "Betweenness 1a", [L12])
    # B5: between(c,a,d)∧between(a,d,e) → between(c,a,e)
    Lb5_2 = pb.s("between(c, a, e)", "Betweenness 5", [Lb1_4, Lp4_2])
    # B7: between(c,a,d)∧between(c,a,e) → ¬between(a,d,e)
    Lb7_2 = pb.s("¬(between(a, d, e))", "Betweenness 7", [Lb5_2, Lb1_4])
    Lbot2 = pb.s("⊥", "⊥-intro", [Lasm2])
    Lnot_eN = pb.reductio("¬(on(e, N))", Lasm2)
    pb._lines[-1]["justification"] = "⊥-elim"

    # ── DA6 supplementary angles ──────────────────────────────────
    # DA6: on(a',L')∧on(b',L')∧between(a',c',b')∧¬on(d',L')∧c'≠d'
    #      → (∠a'c'd' + ∠d'c'b') = (R + R)
    #
    # For ∠dae + ∠eac = R+R:
    #   Line is N. d,a,c on N with between(d,a,c).
    #   a_DA6=d, b_DA6=c, c_DA6=a (vertex), d_DA6=e (not on N)
    #   → ∠dae + ∠eac = R + R
    L_da6_1 = pb.s("∠dae + ∠eac = right-angle + right-angle",
                    "Angle transfer 6",
                    [L12, G["on(c, N)"], L12, Lnot_eN, L34])
    # For ∠fae + ∠eab = R+R:
    #   Line is M. f,a,b on M with between(f,a,b).
    #   a_DA6=f, b_DA6=b, c_DA6=a (vertex), d_DA6=e (not on M)
    #   → ∠fae + ∠eab = R + R
    L_da6_2 = pb.s("∠fae + ∠eab = right-angle + right-angle",
                    "Angle transfer 6",
                    [L13, G["on(b, M)"], L13, Lnot_eM, L34])

    # CN1: both = R+R, so ∠dae + ∠eac = ∠fae + ∠eab
    L_cn1_1 = pb.s("∠dae + ∠eac = ∠fae + ∠eab",
                    "CN1 — Transitivity", [L_da6_1, L_da6_2])

    # From SSS (L36): ∠dae = ∠fae
    # CN3 subtraction: ∠dae + ∠eac = ∠dae + ∠eab → ∠eac = ∠eab
    # (since ∠dae = ∠fae, substitute into LHS)
    # Actually CN3 says: a+c = b+c → a=b
    # We have ∠dae + ∠eac = ∠fae + ∠eab and ∠dae = ∠fae
    # So effectively: X + ∠eac = X + ∠eab → ∠eac = ∠eab
    L_cn3 = pb.s("∠eac = ∠eab",
                  "CN3 — Subtraction", [L_cn1_1, L36])

    # M4: ∠eac = ∠cae, ∠eab = ∠bae
    L_m4_1 = pb.s("∠cae = ∠eac", "M4 — Angle symmetry", [])
    L_m4_2 = pb.s("∠bae = ∠eab", "M4 — Angle symmetry", [])

    # CN1: ∠bae = ∠eab = ∠eac = ∠cae
    L_goal_angle = pb.s("∠bae = ∠cae", "CN1 — Transitivity",
                        [L_m4_2, L_cn3, L_m4_1])

    # ── Same-side setup ───────────────────────────────────────────
    # P3: between(d,a,c) ∧ on(a,M) → ¬ss(d,c,M)
    L_nss_dc_M = pb.s("¬(same-side(d, c, M))", "Pasch 3",
                       [L12, G["on(a, M)"]])
    # P3: between(f,a,b) ∧ on(a,N) → ¬ss(f,b,N)
    L_nss_fb_N = pb.s("¬(same-side(f, b, N))", "Pasch 3",
                       [L13, G["on(a, N)"]])

    # ¬on(a,K) via G1: on(a,M)∧on(a,N)... wait, a,d on N and a on M.
    # If on(a,K) then on(a,K)∧on(d,K)∧on(a,N)∧on(d,N)∧a≠d → K=N.
    # But K≠N. So ¬on(a,K).
    L_not_aK = pb.s("¬(on(a, K))", "Generality 1",
                     [L26, G["on(a, N)"], L12, L17, L41])

    # P2: between(d,a,c) ∧ on(a,K) ∧ ¬on(... — wait, P2 is:
    # between(a,b,c) ∧ on(a,L) ∧ ¬on(b,L) → ss(b,c,L)
    # For ss(d,c,K): we'd need between(X,d,c) with on(X,K)∧¬on(d,K).
    # But on(d,K) IS true. So P2 can't directly give ss(d,c,K).
    #
    # Hmm. Actually for P2 applied to K:
    # between(d,a,c) ∧ on(d,K) ∧ ¬on(a,K) → ss(a,c,K)
    L_ss_ac_K = pb.s("same-side(a, c, K)", "Pasch 2",
                      [L12, L26, L_not_aK])
    # between(f,a,b) ∧ on(f,K) ∧ ¬on(a,K) → ss(a,b,K)
    L_ss_ab_K = pb.s("same-side(a, b, K)", "Pasch 2",
                      [L13, L26, L_not_aK])

    # ── Reductio: ss(e, c, M) ────────────────────────────────────
    # Assume ¬ss(e,c,M)
    # SS5: ¬on(e,M)∧¬on(c,M)∧¬on(d,M)∧¬ss(e,c,M) → ss(e,d,M)∨ss(c,d,M)
    # ¬ss(d,c,M) known → ¬ss(c,d,M) via SS2 → resolves to ss(e,d,M)
    # Then apply I.7 on line K: on(d,K), on(f,K), d≠f,
    #   ss(e,a,K)? No... we need ss(X,Y,K) with distances matching.
    #
    # Actually, let's think about what contradiction we can get from ss(e,d,M).
    # 
    # TI1 with L=K, M=M, N=N, a=a... wait a is not on K.
    # TI axioms require three lines meeting at ONE point.
    # K passes through d and f, NOT through a.
    # So TI with L_ae, M, N meeting at a is the right setup.
    #
    # With ss(e,d,M) inside reductio:
    # TI1: on(a,L_ae)∧on(a,M)∧on(a,N)∧on(e,L_ae)∧on(b,M)∧on(d,N)
    #       ∧ss(b,d,L_ae)∧ss(e,b,N) → ¬ss(e,d,M)
    # We need ss(b,d,L_ae) and ss(e,b,N) — but ss(e,b,N) is what we're
    # trying to prove! Circular.
    #
    # TI1 with different assignment:
    # on(a,L_ae)∧on(a,N)∧on(a,M)∧on(e,L_ae)∧on(c,N)∧on(b,M)
    #   ∧ss(c,b,L_ae)∧ss(e,c,M) → ¬ss(e,b,N)
    # But ss(c,b,L_ae) is false (opposite sides) and ¬ss(e,c,M) is assumed.
    #
    # Hmm. Let me think about using I.7 differently.
    # I.7: on(b',L')∧on(c',L')∧b'≠c'∧ss(a',d',L')∧b'd'=b'a'∧c'd'=c'a' → d'=a'
    # 
    # We want to derive e=a or d=f or similar contradiction.
    # 
    # On line M: on(b,M), on(f,M), b≠f (since between(f,a,b))
    # We have ss(e,d,M) (from reductio hypothesis + SS5).
    # For I.7: b'=b, c'=f on M. ss(e,d,M).
    # Need: be=bd and fe=fd → e=d (contradicts e≠d!)
    # Do we have be=bd? Hmm... not directly.
    #
    # Actually from ad=af and SSS giving triangles dae≅fae:
    # We do NOT directly have be=bd or fe=fd.
    #
    # On line N: on(c,N), on(d,N), c≠d
    # ss(e,d,M)... but we'd need ss on N, not M.
    #
    # On line L_ae: on(a,L_ae), on(e,L_ae), a≠e
    # ss(?,?,L_ae)... 
    #
    # Let me try I.7 on line L_ae!
    # on(a,L_ae), on(e,L_ae), a≠e, ss(d,f,L_ae)?
    # We showed ¬ss(d,f,L_ae) (from I.7 itself). So ss(d,f,L_ae) is false.
    #
    # What about ss(d,d,L_ae)? That's just ¬on(d,L_ae).
    # Is d on L_ae? Not necessarily. Actually probably not.
    #
    # I think the reductio for ss(e,c,M) requires a longer chain.
    # Let me try TI2 instead.
    #
    # TI2: on(a,L')∧on(a,M')∧on(a,N')∧on(b',L')∧on(c',M')∧on(d',N')
    #       ∧ss(c',d',L')∧¬ss(b',d',M')∧¬on(d',M')∧b'≠a → ss(b',c',N')
    #
    # We want ss(e,c,M). Map: b'=e, c'=c, N'=M (conclusion ss(e,c,M)).
    # Then L'=L_ae (e on it), M'=N (c on it).
    # a=a (meeting point).
    # d' on N'=M → b on M.
    # ss(c,b,L_ae)? FALSE (opposite sides). ✗
    #
    # Map: b'=e, c'=b, N'=M. Then conclusion is ss(e,b,M) not ss(e,c,M). ✗
    #
    # Let me try with d'=f on M:
    # b'=e, c'=c, N'=M, d'=f, L'=L_ae, M'=N
    # ss(c,f,L_ae)? YES! ss(f,c,L_ae) from I.7+SS5, so ss(c,f,L_ae) by SS2. ✓
    # ¬ss(e,f,N)? Need this.
    # ¬on(f,N)? YES (L39). ✓
    # e≠a? YES (L34). ✓
    #
    # So we need: ¬ss(e,f,N) to apply TI2.
    # Do we have it? Hmm, not directly. But inside the reductio we have
    # ss(e,d,M). Can we derive ¬ss(e,f,N) from ss(e,d,M)?
    #
    # TI1 with L=L_ae, M=N, N=M, a=a, b=e, c=d, d=f:
    #   (paper vars → concrete)
    #   on(a,L_ae)∧on(a,N)∧on(a,M)∧on(e,L_ae)∧on(d,N)∧on(f,M)
    #   ∧ss(d,f,L_ae)∧ss(e,d,M) → ¬ss(e,f,N)
    # But ss(d,f,L_ae) is FALSE (we proved ¬ss(d,f,L_ae)).
    #
    # TI1 with b=e, c=c, d=b:
    #   on(a,L_ae)∧on(a,N)∧on(a,M)∧on(e,L_ae)∧on(c,N)∧on(b,M)
    #   ∧ss(c,b,L_ae)∧ss(e,c,M) → ¬ss(e,b,N)
    # ss(c,b,L_ae) is false. ✗
    #
    # This is really tricky. Let me check if maybe the approach is to
    # do BOTH reductios simultaneously — assume ¬ss(e,c,M) AND ¬ss(e,b,N),
    # and derive contradiction from both together. But that would need
    # a different logical structure.
    #
    # Actually wait — let me re-examine the TI2 approach where we DON'T
    # need a reductio. Maybe we can get ss(e,c,M) DIRECTLY via TI2
    # if we have the right facts.
    #
    # TI2 for ss(e,c,M):
    #   conclusion ss(b',c',N') = ss(e,c,M)
    #   So b'=e, c'=c, N'=M
    #   L' has e → L_ae, M' has c → N
    #   a=a, d' on M → point on M
    #   Need: ss(c, d', L_ae) ∧ ¬ss(e, d', N) ∧ ¬on(d',N) ∧ e≠a
    #
    #   d'=f (on M):
    #     ss(c, f, L_ae)? ss(f,c,L_ae) by SS2 = ss(c,f,L_ae) ✓
    #     ¬ss(e, f, N)? 🔴 DON'T HAVE
    #     ¬on(f,N) ✓
    #     e≠a ✓
    #
    #   d'=b (on M):
    #     ss(c, b, L_ae)? ✗ (opposite sides)
    #
    # So we need ¬ss(e,f,N). Similarly for the symmetric case.
    #
    # Can we derive ¬ss(e,f,N)?
    # P3: between(f,a,b) ∧ on(a,N) → ¬ss(f,b,N)
    # That gives ¬ss(f,b,N), not ¬ss(e,f,N).
    #
    # What about I.7 on line N?
    # I.7: on(c,N)∧on(d,N)∧c≠d∧ss(e,f,N)∧ce=cf∧de=df → f=e
    # Wait, we need the distances to match. Do we have ce=cf and de=df?
    # de=df is from L28 (de=df ✓). ce=cf? Not directly.
    #
    # Hmm, from SSS of △dae≅△fae: ae=ae, ad=af, de=fe.
    # We do NOT have any facts about distances from c or b to e.
    #
    # What if we apply I.7 on line K (through d,f)?
    # on(d,K), on(f,K), d≠f, ss(a,e,K)?
    # We have ¬ss(e,a,K) → ¬ss(a,e,K). So ss(a,e,K) is false. ✗ for I.7.
    #
    # Hmm, what about ss(X,Y,K) for other X,Y?
    # ss(c,b,K)? ss(b,c,K)? Not known.
    # ss(a,c,K) ✓, ss(a,b,K) ✓ (from P2 steps above).
    # SS4: ss(a,c,K) ∧ ss(a,b,K) → ss(c,b,K) ✓! 
    #
    # So ss(c,b,K) is derivable!
    # Now I.7 on K: on(d,K)∧on(f,K)∧d≠f∧ss(c,b,K)∧dc=db∧fc=fb → b=c
    # But b≠c (premise). So if dc=db and fc=fb, we get contradiction!
    # But do we have dc=db and fc=fb? No, we don't have those equalities.
    #
    # What about I.7 with different point assignments?
    # on(d,K)∧on(f,K)∧d≠f∧ss(a,e,K)∧... but ¬ss(a,e,K). ✗
    # on(d,K)∧on(f,K)∧d≠f∧ss(c,c,K)∧... trivial, dc=dc, fc=fc → c=c. Useless.
    #
    # Let me try I.7 with a and e:
    # ss(a,e,K) is FALSE. Can't use I.7 with a and e on same side.
    #
    # What about ¬ss(e,f,N) via TI1?
    # TI1: three lines meeting at a point.
    # Lines L_ae, M, N meeting at a.
    # TI1: on(a,L_ae)∧on(a,M)∧on(a,N)∧on(e,L_ae)∧on(X,M)∧on(Y,N)
    #       ∧ss(X,Y,L_ae)∧ss(e,X,N) → ¬ss(e,Y,M)
    # Hmm that gives ¬ss on M not N.
    #
    # TI1 with L=L_ae, M=N, N=M:
    # on(a,L_ae)∧on(a,N)∧on(a,M)∧on(e,L_ae)∧on(Y,N)∧on(X,M)
    #   ∧ss(Y,X,L_ae)∧ss(e,Y,M) → ¬ss(e,X,N)
    # We want ¬ss(e,f,N), so X=f. Then Y on N.
    # ss(Y,f,L_ae) and ss(e,Y,M).
    # Y=c on N: ss(c,f,L_ae)=ss(f,c,L_ae) ✓
    #          ss(e,c,M)? 🔴 That's what we're trying to prove!
    # Y=d on N: ss(d,f,L_ae) ✗ (false)
    #
    # Circular again. The pattern keeps requiring one ss to prove the other.
    #
    # OK let me take a COMPLETELY different approach. 
    # What if we DON'T need TI at all, and instead use a NESTED reductio?
    #
    # Outer reductio: assume ¬ss(e,c,M)
    #   From SS5+P3: ss(e,d,M) (resolve disjunction)  
    #   Inner reductio: assume ¬ss(e,b,N)
    #     From SS5+P3: ss(e,f,N) (resolve disjunction)
    #     Now we have ss(e,d,M) AND ss(e,f,N).
    #     TI1 with L=L_ae, M=M, N=N: on(e,L_ae), on(b,M), on(c,N)
    #       ss(b,c,L_ae)?? Still false!
    #
    #     TI1 with L=L_ae, M=N, N=M: on(e,L_ae), on(c,N), on(b,M)
    #       ss(c,b,L_ae)?? Still false!
    #
    # The fundamental problem: b and c are always on opposite sides of L_ae
    # (because between(d,a,c) puts d,c opposite on N through a,
    #  and between(f,a,b) puts f,b opposite on M through a,
    #  and we showed d,b same side of L_ae, f,c same side of L_ae,
    #  so b and c are on opposite sides of L_ae.)
    #
    # TI1 ALWAYS needs ss(X,Y,L_ae) for two points on the other two lines,
    # and those points are always on opposite sides of L_ae.
    #
    # Maybe we need to use d,f (on K) instead of b,c?
    # TI1 with L=K, M=?, N=?... but K doesn't pass through a!
    # TI requires three lines meeting at ONE point.
    #
    # Wait — what about using L_ae, M, K meeting at... L_ae∩M?
    # L_ae passes through a. M passes through a. So L_ae ∩ M = a.
    # K passes through d and f. Does K pass through a? 
    # Only if a, d, f are collinear. In general they're not (d on N, f on M,
    # a is the vertex). So K does NOT pass through a.
    # So L_ae, M, K don't all meet at one point. ✗
    #
    # What about M, N, K? M∩N = a. But K doesn't pass through a. ✗
    #
    # So the only triple of lines through a is {L_ae, M, N}.
    # And TI always needs same-side facts on L_ae between b/f (on M) and c/d (on N),
    # which are always on opposite sides of L_ae.
    #
    # THIS is the fundamental geometric fact making the proof hard.
    # The TI axioms can't help directly.
    #
    # Let me re-read the paper more carefully about what "case analysis" means
    # for I.9. The paper says (line 1969-1973):
    # "Though one may stipulate that f falls on the side of the segment de 
    #  opposite the point a, one cannot assume anything about a's position 
    #  with respect to the sides of the angle. One must consider the cases 
    #  where f falls on or outside the angle, and show that they are impossible."
    #
    # So the case analysis is about showing e (called f in the paper's notation)
    # is INSIDE the angle. The paper says: consider cases where e is ON a side
    # of the angle (handled by ¬on(e,M), ¬on(e,N) reductios) or OUTSIDE the angle.
    #
    # "Outside" means ¬ss(e,c,M) or ¬ss(e,b,N). And footnote 8 says I.7
    # contrapositive rules out two cases. Let me look at this more carefully.
    #
    # The paper says: "the contrapositive of Proposition 7 shows that if 
    # ad is equal to ae, df is equal to ef, and d and e are distinct, 
    # then d and e cannot lie on the same side of af."
    #
    # In our notation: d and f cannot lie on same side of L_ae. ✓ We proved that.
    #
    # But how does that rule out e being "outside"? Let me think geometrically...
    #
    # If e were on the wrong side of M (¬ss(e,c,M)), then by SS5 we'd have
    # ss(e,d,M). Combined with the fact that e is on the opposite side of K from a...
    #
    # Actually, maybe the answer is simpler than I thought. Let me check if
    # there's a way to use the opposite-side construction directly.
    #
    # From the construction: ¬ss(e,a,K) and ¬on(e,K).
    # Also: ¬on(a,K) (derived).
    # So e and a are on opposite sides of K.
    # K passes through d and f.
    #
    # Now, if we assume ¬ss(e,c,M), we get ss(e,d,M) (from SS5).
    # We also know ss(a,c,K) (from P2).
    # And ss(a,b,K) (from P2).
    #
    # Since ¬ss(e,a,K), and ss(a,c,K), by SS4 contrapositive:
    # ¬ss(e,a,K) and ss(a,c,K) → ... hmm SS4 doesn't have a useful
    # contrapositive here directly.
    # 
    # But: ¬ss(e,a,K) means e and a are on opposite sides of K.
    # ss(a,c,K) means a and c are on same side of K.
    # Therefore e and c are on opposite sides of K: ¬ss(e,c,K).
    # This follows from SS4 contrapositive: if ss(e,c,K) and ss(a,c,K),
    # then ss(e,a,K) by transitivity — contradiction with ¬ss(e,a,K).
    # So ¬ss(e,c,K) follows.
    #
    # Similarly, ss(a,b,K) and ¬ss(e,a,K) → ¬ss(e,b,K).
    #
    # Now I have:
    # - ss(e,d,M) (from reductio + SS5)
    # - ¬ss(e,c,K) (derived above)
    # - on(d,K), on(f,K), on(e,?) — e NOT on K
    #
    # TI2 with lines K, M, N meeting at... they don't meet at one point!
    # K goes through d,f. M goes through a,b,f. N goes through a,c,d.
    # K∩M = f. K∩N = d. M∩N = a. Three different intersection points.
    # So no triple of our lines meets at a single point (except L_ae,M,N at a).
    #
    # Hmm. What about using construction to create additional lines?
    # We already have L_ae (line through a,e). 
    #
    # What if we use f as the meeting point of K and M?
    # Lines K, M meet at f. We need a third line through f.
    # Line through f and e? f and e are both... well, we could construct it.
    # But that adds complexity.
    #
    # Actually, wait. Let me re-read the ⊥-intro rule. It just needs 
    # ANY φ and ¬φ in scope. What if the contradiction comes from
    # METRIC facts rather than diagrammatic?
    #
    # Inside the reductio assuming ¬ss(e,c,M):
    # ss(e,d,M) from SS5.
    # ¬ss(e,c,K) derived.
    # 
    # What if we can derive that e is on the same side of L_ae as d?
    # ss(e,d,L_ae)? If so, then ss(e,d,L_ae) + ss(d,b,L_ae) → ss(e,b,L_ae)
    # by SS4. And then... hmm still not obviously contradictory.
    #
    # Let me try yet another approach. What if we use P1?
    # P1: between(a,b,c) ∧ ss(a,c,L) → ss(a,b,L)
    #
    # Or: think about what ss(e,d,M) means geometrically.
    # e and d are on the same side of M. M goes through a and b.
    # d is on N (the other ray of the angle from a).
    # So d is "outside" M on the c-side... wait no. d is on the
    # OPPOSITE side from c through a on N: between(d,a,c).
    # So d is on the opposite side of a from c on line N.
    # P3: between(d,a,c) ∧ on(a,M) → ¬ss(d,c,M). 
    # So d and c are on opposite sides of M. ✓
    # ss(e,d,M) means e is on d's side of M, hence opposite from c.
    # This is exactly what our assumption ¬ss(e,c,M) implies!
    # So the facts are all consistent within the reductio — no obvious
    # metric contradiction from diagrammatic facts alone.
    #
    # The contradiction MUST come from I.7 or some metric argument.
    # The paper says so explicitly. Let me think about what I.7 can give.
    #
    # I.7 on line K: on(d,K), on(f,K), d≠f, ss(X,Y,K), dX=dY, fX=fY → X=Y
    #
    # We have ss(a,c,K) and ss(a,b,K). What about ss(c,b,K)?
    # SS4: ss(a,c,K) ∧ ss(a,b,K) → ss(c,b,K). ✓
    #
    # I.7 with X=c, Y=b on K: dc=db ∧ fc=fb → c=b. Contradicts c≠b!
    # Do we have dc=db? 
    # d is on N at distance ad=ab from a (circle radius).
    # between(d,a,c) means a is between d and c.
    # dc = da + ac (additivity of segments with betweenness).
    # db is the distance from d to b — need this.
    # 
    # We don't have dc=db. But actually... hmm.
    #
    # I.7 with different points:
    # What if X and Y are such that their distances to d and f match?
    # From SSS: ad=af, de=fe, ae=ae. These are distances from/to d,f,a,e.
    # So: da=fa and de=fe. 
    # I.7 on K with X=a, Y=e: ss(a,e,K)? NO, ¬ss(a,e,K).
    # I.7 requires same-side. ✗
    #
    # The only pair with matching distances from d and f is (a,e), but they're
    # on opposite sides of K. So I.7 can't fire on K with known distances.
    #
    # Unless... we can get additional distance equalities INSIDE the reductio.
    # With ss(e,d,M) inside the reductio, can we derive any new metric facts?
    # 
    # DA2: angle addition. If ss(e,d,M) and other conditions...
    # DA2 forward: on(a,L')∧on(a,M')∧on(b',L')∧on(c',M')∧a≠b'∧a≠c'
    #   ∧¬on(d',L')∧¬on(d',M')∧L'≠M'∧ss(b',d',M')∧ss(c',d',L')
    #   → ∠b'ac' = ∠b'ad' + ∠d'ac'
    #
    # With L'=M, M'=N, a=a, b'=b, c'=c, d'=e:
    #   on(a,M)✓ on(a,N)✓ on(b,M)✓ on(c,N)✓ a≠b✓ a≠c✓
    #   ¬on(e,M)✓ ¬on(e,N)✓ M≠N✓
    #   ss(b,e,N)? 🔴 DON'T HAVE (it's what we're trying to prove)
    #   ss(c,e,M)? 🔴 DON'T HAVE (assumed false in reductio)
    #
    # With d'=d:
    #   ss(b,d,N)? between(d,a,c)∧on(a,N) → ¬ss(d,c,N)... 
    #   Actually ss(d,d,N)=¬on(d,N) but on(d,N) is TRUE. So ss(d,anything,N)
    #   requires ¬on(d,N) which is false. ✗
    #
    # This isn't working. Let me take a step back and look at the problem
    # from the perspective of what the paper says:
    # 
    # "one must consider the cases where f falls on or outside the angle,
    #  and show that they are impossible"
    #
    # Case 1: e on M → contradicts ¬on(e,M) (reductio) ✓
    # Case 2: e on N → contradicts ¬on(e,N) (reductio) ✓  
    # Case 3: e outside angle (¬ss(e,c,M)) → need to show impossible
    # Case 4: e outside angle (¬ss(e,b,N)) → need to show impossible
    #
    # The footnote says I.7 contrapositive "immediately rules out two cases."
    # The two cases being: d and f on same side of L_ae → d=f → contradiction
    # (since d≠f). But we already proved ¬ss(d,f,L_ae)!
    #
    # Hmm wait, that rules out d=f cases. But the paper says it rules out
    # two of the cases for e. Let me re-read footnote 8:
    # "if ad is equal to ae, df is equal to ef, and d and e are distinct,
    #  then d and e cannot lie on the same side of af"
    #
    # In paper notation: a=vertex, d and e are on the two rays, f is the 
    # triangle vertex. In OUR notation: a=a, d=d, e=f, f=e.
    # Paper says d and e can't be on same side of af = line(a,f) = line(a,e) = L_ae.
    # So in our notation: d and f can't be on same side of L_ae. ✓
    #
    # But how does ¬ss(d,f,L_ae) rule out cases 3 & 4?
    # ss(d,b,L_ae) and ss(f,c,L_ae). Since ¬ss(d,f,L_ae):
    # d is on b's side, f is on c's side. So b's side ≠ c's side w.r.t. L_ae.
    # 
    # Hmm. The "two cases" might be about the TWO possible positions 
    # from the circle-circle intersection. We chose e on the opposite side 
    # of K from a. The OTHER intersection point e' would be on the SAME side
    # as a. The paper might be saying that choosing the wrong intersection
    # point leads to d and f being on the same side of the bisector line,
    # which I.7 rules out.
    #
    # In that case, our e (opposite side from a) is already the CORRECT one,
    # and the "case analysis" the paper refers to is about showing the other
    # intersection point doesn't work. Since we chose opposite-side, we may
    # already be in the good case.
    #
    # But then how do we derive ss(e,c,M) and ss(e,b,N)?
    #
    # Let me look at the problem from TI2 perspective one more time.
    # TI2 conclusion ss(e,c,M) requires ¬ss(e,f,N). 
    # What if ¬ss(e,f,N) is derivable from facts we have?
    #
    # e and a are on opposite sides of K.
    # f is on K.
    # P3: if between(X,f,Y) and on(f,N)... wait, is f on N? We showed ¬on(f,N).
    #
    # Hmm. Let me check: can we get ¬ss(e,f,N) from ¬on(f,N)?
    # f is NOT on N. e is NOT on N (from reductio). So both are off N.
    # The question is whether they're on the same side.
    #
    # We know: ss(a,c,K), ss(a,b,K), ¬ss(e,a,K).
    # From ¬ss(e,a,K): e and a are on opposite sides of K.
    # f is ON K. So f is not on either side.
    #
    # Does the consequence engine derive ¬ss(e,f,N) automatically?
    # ss(e,f,N): e and f on same side of N. 
    # f is not on N (¬on(f,N)). e is not on N (to be proven / assumed false).
    # Without ¬on(e,N), we don't even know if e is off N.
    # WITH ¬on(e,N) (from reductio), we know both are off N.
    #
    # But SS2+SS3+SS4+SS5 with e,f and line N:
    # Either ss(e,f,N) or ¬ss(e,f,N). We need specific reasoning.
    #
    # Since between(f,a,b) and on(a,N) and ¬on(f,N):
    # P2: between(f,a,b) ∧ on(f,?) ∧ ¬on(a,?)... no, P2 is:
    # between(a,b,c) ∧ on(a,L) ∧ ¬on(b,L) → ss(b,c,L)
    # P2 with between(f,a,b), line N, on(f,N)? But ¬on(f,N). ✗
    # 
    # Let me try P1: between(a,b,c) ∧ ss(a,c,L) → ss(a,b,L)
    # If between(f,a,b) and ss(f,b,N)? But ¬ss(f,b,N). ✗
    #
    # I think I need to actually run the consequence engine to see
    # what's derivable. Let me just output what we have and test it.

    print("This test is for analysis only — the full proof strategy")
    print("needs more work on the ss(e,c,M) / ss(e,b,N) derivation.")
    return None


# Try a minimalist approach: just test the angle part and see if it works.
def build_i9_angle_test():
    """Test just the angle derivation via DA6."""
    pb = PB(
        "Prop.I.9",
        [
            "¬(a = b)", "¬(a = c)", "¬(b = c)",
            "on(a, M)", "on(b, M)",
            "on(a, N)", "on(c, N)",
            "¬(on(c, M))", "¬(on(b, N))",
        ],
        "∠bae = ∠cae",
    )
    G = pb.auto_given()

    # Construction (same as current proof, steps 10-38)
    L10 = pb.s("center(a, α), on(b, α)", "let-circle", [G["¬(a = b)"]])
    L11 = pb.s("inside(a, α)", "Generality 3", [L10])
    L12 = pb.s("on(d, α), on(d, N), between(d, a, c)",
               "let-intersection-line-circle-extend",
               [L11, G["on(a, N)"], G["¬(a = c)"], G["on(c, N)"]])
    L13 = pb.s("on(f, α), on(f, M), between(f, a, b)",
               "let-intersection-line-circle-extend",
               [L11, G["on(a, M)"], G["¬(a = b)"], G["on(b, M)"]])
    L14 = pb.s("ad = ab", "Segment transfer 3b", [L10, L12])
    L15 = pb.s("af = ab", "Segment transfer 3b", [L10, L13])
    L16 = pb.s("ad = af", "CN1 — Transitivity", [L14, L15])
    L17 = pb.s("¬(d = a)", "Betweenness 1b", [L12])
    L18 = pb.s("¬(M = N)", "Generality 5",
               [G["on(b, M)"], G["¬(on(b, N))"]])
    L19 = pb.s("¬(on(d, M))", "Generality 1",
               [G["on(a, M)"], G["on(a, N)"], L12, L17, L18])
    L20 = pb.s("¬(f = d)", "Generality 6", [L13, L19])
    L21 = pb.s("center(d, β), on(f, β)", "let-circle", [L20])
    L22 = pb.s("center(f, γ), on(d, γ)", "let-circle", [L20])
    L23 = pb.s("inside(d, β)", "Generality 3", [L21])
    L24 = pb.s("inside(f, γ)", "Generality 3", [L22])
    L25 = pb.s("intersects(β, γ)", "Intersection 5",
               [L21, L22, L23, L24])
    L26 = pb.s("on(d, K), on(f, K)", "let-line", [L20])
    L27 = pb.s(
        "on(e, β), on(e, γ), ¬(same-side(e, a, K)), ¬(on(e, K))",
        "let-intersection-circle-circle-opposite-side",
        [L25, L21, L22, L26, L12, L13,
         G["on(b, M)"], G["on(a, N)"], G["¬(on(b, N))"],
         L17, L18, L19, G["on(a, M)"]])
    L28 = pb.s("de = df", "Segment transfer 3b", [L21, L27])
    L29 = pb.s("fe = fd", "Segment transfer 3b", [L22, L27])
    L30 = pb.s("df = fd", "M3 — Symmetry", [])
    L31 = pb.s("de = fe", "CN1 — Transitivity", [L28, L29, L30])
    L32 = pb.s("¬(e = d)", "Generality 6", [L26, L27])
    L33 = pb.s("¬(e = f)", "Generality 6", [L26, L27])
    L34 = pb.s("¬(a = e)", "Same-side 6",
               [L27, L26, G["on(a, N)"], L12, L17, L18])
    L35 = pb.s("ae = ae", "CN4 — Reflexivity", [])
    L36 = pb.s(
        "∠dae = ∠fae, ∠ade = ∠afe, ∠aed = ∠aef, △ade = △afe",
        "SSS", [L16, L31, L35])
    L37 = pb.s("¬(a = f)", "Betweenness 1b", [L13])
    L38 = pb.s("on(a, L), on(e, L)", "let-line", [L34])

    # Derive ¬on(f,N) and ¬on(e,N) and ¬on(e,M) for DA6
    L39 = pb.s("¬(on(f, N))", "Generality 1",
               [G["on(a, M)"], G["on(a, N)"], L13, L37, L18])
    # K≠M and K≠N
    L40 = pb.s("¬(K = M)", "Generality 5", [L26, L19])
    L41 = pb.s("¬(K = N)", "Generality 5", [L26, L39])

    # Reductio ¬on(e,M)
    Lasm1 = pb.assume("on(e, M)")
    Lp4_1 = pb.s("between(a, f, e)", "Pasch 4",
                  [L40, L26, Lasm1, G["on(a, M)"], L13, L37, L33, L27])
    Lb1_2 = pb.s("between(b, a, f)", "Betweenness 1a", [L13])
    Lb5_1 = pb.s("between(b, a, e)", "Betweenness 5", [Lb1_2, Lp4_1])
    Lb7_1 = pb.s("¬(between(a, f, e))", "Betweenness 7", [Lb5_1, Lb1_2])
    Lbot1 = pb.s("⊥", "⊥-intro", [Lasm1])
    Lnot_eM = pb.reductio("¬(on(e, M))", Lasm1)
    pb._lines[-1]["justification"] = "⊥-elim"

    # Reductio ¬on(e,N)
    Lasm2 = pb.assume("on(e, N)")
    Lp4_2 = pb.s("between(a, d, e)", "Pasch 4",
                  [L41, L26, Lasm2, G["on(a, N)"], L12, L17, L32, L27])
    Lb1_4 = pb.s("between(c, a, d)", "Betweenness 1a", [L12])
    Lb5_2 = pb.s("between(c, a, e)", "Betweenness 5", [Lb1_4, Lp4_2])
    Lb7_2 = pb.s("¬(between(a, d, e))", "Betweenness 7", [Lb5_2, Lb1_4])
    Lbot2 = pb.s("⊥", "⊥-intro", [Lasm2])
    Lnot_eN = pb.reductio("¬(on(e, N))", Lasm2)
    pb._lines[-1]["justification"] = "⊥-elim"

    # ∠dae + ∠eac = R+R via DA6
    # DA6: on(a',L')∧on(b',L')∧between(a',c',b')∧¬on(d',L')∧c'≠d'
    #   → (∠a'c'd' + ∠d'c'b') = (R + R)
    # Map: L'=N, a'=d, b'=c, c'=a, d'=e
    #   on(d,N)✓ on(c,N)✓ between(d,a,c)✓ ¬on(e,N)✓ a≠e✓
    #   → (∠dae + ∠eac) = (R + R)
    L_da6_1 = pb.s("∠dae + ∠eac = right-angle + right-angle",
                    "Angle transfer 6",
                    [L12, G["on(c, N)"], L12, Lnot_eN, L34])
    # Map: L'=M, a'=f, b'=b, c'=a, d'=e
    #   on(f,M)✓ on(b,M)✓ between(f,a,b)✓ ¬on(e,M)✓ a≠e✓
    #   → (∠fae + ∠eab) = (R + R)
    L_da6_2 = pb.s("∠fae + ∠eab = right-angle + right-angle",
                    "Angle transfer 6",
                    [L13, G["on(b, M)"], L13, Lnot_eM, L34])

    # CN1: ∠dae + ∠eac = ∠fae + ∠eab
    L_cn1_1 = pb.s("∠dae + ∠eac = ∠fae + ∠eab",
                    "CN1 — Transitivity", [L_da6_1, L_da6_2])

    # CN3: ∠dae + ∠eac = ∠dae + ∠eab (since ∠dae = ∠fae from SSS)
    # Actually CN3: a+c = b+c → a=b. We have X+A = X+B (with X=∠dae=∠fae).
    # So ∠eac = ∠eab.
    L_cn3 = pb.s("∠eac = ∠eab",
                  "CN3 — Subtraction", [L_cn1_1, L36])

    # M4 + CN1 to get ∠bae = ∠cae
    L_m4_1 = pb.s("∠cae = ∠eac", "M4 — Angle symmetry", [])
    L_m4_2 = pb.s("∠bae = ∠eab", "M4 — Angle symmetry", [])
    L_goal = pb.s("∠bae = ∠cae", "CN1 — Transitivity",
                   [L_m4_2, L_cn3, L_m4_1])

    return pb.build()


if __name__ == "__main__":
    print("=== Testing I.9 angle part (DA6 approach) ===")
    proof = build_i9_angle_test()
    if proof is None:
        print("Build returned None")
        sys.exit(1)
    result = verify_e_proof_json(proof)
    lrs = result.line_results  # Dict[int, LineCheckResult]
    total = len(lrs)
    passed = sum(1 for lr in lrs.values() if lr.valid)
    print(f"\n{passed}/{total} lines valid  (accepted={result.accepted})")
    # Match line ids back to the proof lines for display
    line_map = {line["id"]: line for line in proof["lines"]}
    for lid in sorted(lrs):
        lr = lrs[lid]
        tag = "✓" if lr.valid else "✗"
        line = line_map.get(lid, {})
        stmt = line.get("statement", "?")[:60]
        just = line.get("justification", "?")
        print(f"  {tag} L{lid}: [{just}] {stmt}")
        if not lr.valid:
            for e in lr.errors:
                print(f"      ERROR: {e}")
