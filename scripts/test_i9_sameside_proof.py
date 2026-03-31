"""
Test I.9 with same-side construction: ss(e,a,K) instead of ¬ss(e,a,K).
Check what consequences flow and whether ss(e,c,M)/ss(e,b,N) are derivable.
"""
from __future__ import annotations
import sys, os
sys.path.insert(0, os.path.join(os.path.dirname(__file__), ".."))
os.environ["PYTHONIOENCODING"] = "utf-8"

from scripts.real_proofs import PB
from verifier.unified_checker import verify_e_proof_json


def build_i9_sameside():
    """
    I.9 with same-side construction for e.
    Uses ss(e,a,K) instead of ¬ss(e,a,K).
    """
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

    # ── SAME-SIDE construction for e ──────────────────────────────
    # Use same-side instead of opposite-side
    # Prerequisites: intersects(β,γ), center(d,β), center(f,γ), on(d,K), on(f,K), ¬on(a,K)
    # Need ¬on(a,K) first
    # G1: on(a,N)∧on(d,N)∧on(a,M)∧... wait, we need ¬on(a,K).
    # If on(a,K)∧on(d,K)∧on(a,N)∧on(d,N)∧a≠d → K=N.
    # We'll need K≠N. G5: on(f,K)∧¬on(f,N) → K≠N.
    # Need ¬on(f,N): G1: on(a,M)∧on(a,N)∧on(f,M)∧f≠a∧M≠N → ¬on(f,N)
    L_fa = pb.s("¬(a = f)", "Betweenness 1b", [L13])
    L_notfN = pb.s("¬(on(f, N))", "Generality 1",
                   [G["on(a, M)"], G["on(a, N)"], L13, L_fa, L18])
    L_KneN = pb.s("¬(K = N)", "Generality 5", [L26, L_notfN])
    L_notaK = pb.s("¬(on(a, K))", "Generality 1",
                   [L26, G["on(a, N)"], L12, L17, L_KneN])

    # Same-side construction: e on same side of K as a
    L27 = pb.s("on(e, β), on(e, γ), same-side(e, a, K)",
               "let-intersection-circle-circle-same-side",
               [L25, L21, L22, L26, L_notaK])

    # ── Metric equalities + distinctness (28-37) ──────────────────
    L28 = pb.s("de = df", "Segment transfer 3b", [L21, L27])
    L29 = pb.s("fe = fd", "Segment transfer 3b", [L22, L27])
    L30 = pb.s("df = fd", "M3 — Symmetry", [])
    L31 = pb.s("de = fe", "CN1 — Transitivity", [L28, L29, L30])

    # e≠d: need ¬on(e,K) or use G6
    # Actually with same-side, we don't get ¬on(e,K) directly.
    # But ss(e,a,K) → ¬on(e,K) via SS3.
    # SS3: ss(a,b,L) → ¬on(a,L). So ss(e,a,K) → ¬on(e,K). Automatic in closure.
    # G6: on(d,K) ∧ ¬on(e,K) → ... wait G6 is on(a,L)∧¬on(b,L)→a≠b
    # But we need e≠d. G6: on(d,K)∧ss(e,a,K)... hmm.
    # SS3 gives ¬on(e,K) from ss(e,a,K). G6: on(d,K)∧¬on(e,K)→d≠e? No, G6 is a≠b from on(a,L)∧¬on(b,L).
    # So G6: on(d,K) (positive), ¬on(e,K) (from SS3) → d≠e. But wait, G6 gives ¬(a=b),
    # and the clause is ¬on(a,L)∨on(b,L)∨¬(a=b), i.e. on(a,L)∧¬on(b,L)→a≠b.
    # Hmm the current G6 in the axioms might be different. Let me just try.
    L32 = pb.s("¬(e = d)", "Generality 6", [L26, L27])
    L33 = pb.s("¬(e = f)", "Generality 6", [L26, L27])

    # a≠e: SS6 or similar. ss(e,a,K) means both are not on K.
    # We need a≠e separately.
    # Method: if a=e then ss(a,a,K) which means ¬on(a,K) from SS1 converse... 
    # Actually ss(e,a,K) already implies ¬on(e,K) and ¬on(a,K).
    # But a=e is still possible with ss(e,a,K) if a is not on K. Hmm.
    # Use SS6: ss(e,a,K) ∧ ¬ss(e,X,K) → a≠X. Can we get ¬ss(e,X,K) for some X?
    # Or: if a=e then from ad=af and de=fe:
    #   de=fe becomes ae=fe, and ad=af. Since a=e: ee=fe → 0=fe → f=e.
    #   But f≠e (L33). Contradiction. But this is metric, not diagrammatic.
    # Let me just try M1 zero segment: if a=e then ae=0. But ae is not necessarily 0...
    # Actually a≠e can be derived from: ad=af, de=fe, d≠f, on(d,K), on(f,K), ss(e,a,K).
    # I.7 contrapositive: on(d,K)∧on(f,K)∧d≠f∧dd'=da∧fd'=fa∧d'≠a → ¬ss(d',a,K).
    # With d'=e: on(d,K)∧on(f,K)∧d≠f∧de=da∧fe=fa∧e≠a → ¬ss(e,a,K).
    # But we have ss(e,a,K)! So by contradiction: ¬(e≠a), i.e., wait that's wrong direction.
    # I.7: ss(e,a,K) ∧ de=da ∧ fe=fa → e=a
    # We DON'T have de=da or fe=fa. We have de=df and fe=fd. And ad=af.
    # de=df, ad=af. So de=df and da=fa... hmm.
    # For I.7: on(d,K)∧on(f,K)∧d≠f∧ss(a,e,K)∧da=de∧fa=fe → a=e
    # We need da=de. We have de=df. And da=ab=af. So da=af and de=df.
    # If af=df... that's equilateral. Actually that's not guaranteed.
    # Let me just use a different approach for a≠e.
    # Actually, SS6: ss(a,b,L) ∧ ¬ss(a,c,L) → b≠c
    # We don't have ¬ss(a,X,K) for any X besides e.
    # Let's try a metric approach.
    # If a=e then center(d,β) on(f,β) on(a,β): da = df (radius of β = df).
    # And ad = ab (from L14). So df = ab.
    # Similarly center(f,γ) on(d,γ) on(a,γ): fa = fd.
    # And af = ab (from L15). So fd = ab.
    # So df = fd = ab. And de = df → ae = df → ae = ab.
    # But if a=e then ae = 0. So ab = 0 → a=b. Contradiction with a≠b!
    # So a≠e from metric: ae=de=df=ab by substitution, and if a=e then ab=0.
    # Let me try using M1:
    L34 = pb.s("¬(a = e)", "M1 — Zero segment", [G["¬(a = b)"], L14, L28])
    # Hmm, M1 is about a≠b ↔ ab≠0. The exact match might be tricky.
    # Let me try a simpler approach: just use that de>0 from e≠d.
    # Actually, from ¬(e = d) and de = df: if d≠e then de ≠ 0, so df ≠ 0, so d≠f (already known).
    # And from ad = ab and a≠b: ad ≠ 0, so a≠d (already known).
    # For a≠e: let me try ae = ae (reflexivity) and see if the engine can figure it out.
    # Actually, I'll use the same approach as before: SS6
    # SS6: ss(e,a,K) → e not on K → a not on K → ... 
    # Hmm, let me just try submitting and see what happens.

    L35 = pb.s("ae = ae", "CN4 — Reflexivity", [])
    L36 = pb.s(
        "∠dae = ∠fae, ∠ade = ∠afe, ∠aed = ∠aef, △ade = △afe",
        "SSS", [L16, L31, L35])

    # ── Let line L (ae) ───────────────────────────────────────────
    L38 = pb.s("on(a, L), on(e, L)", "let-line", [L34])

    # ── Distinctness / not-on facts ───────────────────────────────
    L40 = pb.s("¬(K = M)", "Generality 5", [L26, L19])

    # ── Reductio: ¬on(e, M) ──────────────────────────────────────
    # P4: K≠M, on(f,K), on(f,M), on(a,M), on(e,M)=assumed, a≠f, e≠f
    #     ¬ss(a,e,K)? No! We have ss(a,e,K) now!
    # So P4 doesn't apply (it needs ¬ss(a,e,K) but we have ss(a,e,K)).
    # Hmm. This is different from the opposite-side case.
    # With same-side, P4 doesn't fire. We need a different approach for ¬on(e,M).
    # 
    # Actually, ¬on(e,M) might be derivable from ss(e,a,K) combined with
    # on(f,K)∧on(f,M)∧on(a,M)∧¬on(a,K) via some axiom.
    # 
    # Assume on(e,M). Then on(e,M)∧on(f,M)∧on(a,M). 
    # We have ss(e,a,K). But e is on M, a is on M. 
    # If on(e,M) then since on(f,M)∧on(f,K), and K≠M, we get...
    # P4: K≠M, on(f,K), on(f,M), on(a,M), on(e,M), a≠f, e≠f, ¬ss(a,e,K) → between(a,f,e)
    # But we have ss(a,e,K), not ¬ss! P4 doesn't fire.
    #
    # Actually wait: ss(a,e,K) means a and e are on the same side of K.
    # If both a and e are on M, and f is the intersection of K and M,
    # then a,e,f are all on M. a and e being on the same side of K means
    # f is NOT between a and e (since f is on K, crossing K would change sides).
    # So either a is between f and e, or e is between f and a, or a=f or e=f.
    # Since a≠f and e≠f, we have either between(f,a,e) or between(f,e,a) or between(a,e,f)...
    # Hmm, actually if a and e are on the same side of K and f is on K, then
    # f is NOT between a and e. So by P4 contrapositive or something...
    #
    # This is getting complicated. Let me just try to build what we can and test.
    pass

    # Actually, let me try a completely different approach.
    # Instead of reductio for ¬on(e,M), let's see if we can derive
    # ss(e,c,M) DIRECTLY using TI2.
    #
    # TI2: on(a,L)∧on(a,M)∧on(a,N)∧on(b,L)∧on(c,M)∧on(d,N)
    #      ∧ss(c,d,L)∧¬ss(b,d,M)∧¬on(d,M)∧b≠a → ss(b,c,N)
    #
    # Goal: ss(e,c,M). Map to TI2: b=e, c=c, N=M (conclusion).
    # Then: L has e → L_ae, M has c → line_N, a=a.
    # TI2: on(a,L_ae)∧on(a,N_line)∧on(a,M)∧on(e,L_ae)∧on(c,N_line)∧on(d',M)
    #      ∧ss(c,d',L_ae)∧¬ss(e,d',N_line)∧¬on(d',N_line)∧e≠a → ss(e,c,M)
    #
    # d' on M → could be b or f.
    # If d'=f: on(f,M)✓, ¬on(f,N_line)=¬on(f,N)✓, 
    #          ss(c,f,L_ae)? Need to check.
    #          ¬ss(e,f,N)? This is what we want to derive too!
    # If d'=b: on(b,M)✓, ¬on(b,N)✓,
    #          ss(c,b,L_ae)? Are c and b on the same side of L?
    #          ¬ss(e,b,N)? Also what we want.
    # 
    # Circular again...
    #
    # TI1: on(a,L)∧on(a,M)∧on(a,N)∧on(b,L)∧on(c,M)∧on(d,N)
    #      ∧ss(c,d,L)∧ss(b,c,N) → ¬ss(b,d,M)
    #
    # With L_ae, M, N, b=e, c=b_point, d=c_point:
    # on(a,L_ae)∧on(a,M)∧on(a,N)∧on(e,L_ae)∧on(b,M)∧on(c,N)
    # ∧ss(b,c,L_ae)∧ss(e,b,N) → ¬ss(e,c,M)
    # 
    # We want ss(e,c,M), not ¬ss(e,c,M)! This gives the OPPOSITE.
    # TI1 contrapositive: ss(e,c,M) → ¬ss(b,c,L_ae) ∨ ¬ss(e,b,N)
    # Not directly useful.

    # Let me try yet another TI1 instantiation:
    # L_ae, N, M: on(a,L_ae), on(a,N), on(a,M), on(e,L_ae), on(c,N), on(b,M)
    # ss(c,b,L_ae)∧ss(e,c,M) → ¬ss(e,b,N)
    # Again gives ¬ss(e,b,N) from ss(e,c,M). If we knew ss(e,c,M) this gives us... well it constrains.

    # TI2 reversed: from known ¬ss(d,f,L) (from I.7), can we get ss goals?
    # ¬ss(d,f,L) means d and f on opposite sides of L=line(a,e).
    # TI2 with L=L_ae, M=M, N=N, a=a, b=e, c=d, d'=f:
    # wait d is on N, f is on M. Let me be careful.
    # TI2: on(a,L)∧on(a,M)∧on(a,N)∧on(b,L)∧on(c,M)∧on(d,N)
    #      ∧ss(c,d,L)∧¬ss(b,d,M)∧¬on(d,M)∧b≠a → ss(b,c,N)
    #
    # Assignment: L=L_ae, M=M_line, N=N_line
    # b=e (on L_ae), c=f (on M), d=d (on N)
    # ss(f,d,L_ae)? this is ss(f,d,L) — but we know ¬ss(d,f,L)!
    # ss(f,d,L) = ss(d,f,L) by SS2. So ¬ss(f,d,L). FAILS.

    # Assignment: L=L_ae, M=N_line, N=M_line  
    # b=e (on L_ae), c=d (on N), d'=f (on M)
    # ss(d,f,L_ae)? = ¬ss(d,f,L) — FALSE! FAILS.

    # Hmm. ¬ss(d,f,L) means TI2 with ss(c,d,L) = ss(d,f,L) fails.

    # What about swapping: ss(d,f,L) is false, but what about ss(c,d,L)
    # where c is something else?
    # 
    # OK let me try TI2 with different points:
    # Goal: ss(e,c,M)
    # TI2: ss(b_M, d_N, L_ae) ∧ ¬ss(e, d_N, M') ∧ ¬on(d_N, M') ∧ e≠a → ss(e, b_M, N')
    # where M' and N' are specific lines.
    #
    # Let me use: L=L_ae, M=M (arm), N=N (arm)
    # b=e, c=f (on M), d=d (on N)
    # Need ss(f,d,L_ae) — FALSE (¬ss(d,f,L))
    # 
    # So TI with ¬ss(d,f,L) makes all the "good" TI2 instantiations fail.

    # WHAT IF we use TI2 with line K instead of L_ae?
    # L=K, M=M, N=N, a=??? K doesn't pass through a. TI needs all 3 lines through one point.
    # K passes through d and f. M passes through a. These don't share a point (unless f is on M,
    # which it IS: on(f,M) and on(f,K). So f is the common point!
    # 
    # TI2 with a=f (common point), L=K, M=M, N=N:
    # on(f,K)✓, on(f,M)✓, on(f,N)? NO! ¬on(f,N)!
    # So we can't use f as the triple-incidence point with K,M,N.
    #
    # What about a as common point of M,N with L_ae?
    # on(a,L_ae)✓, on(a,M)✓, on(a,N)✓
    # b on L_ae → e
    # c on M → b or f
    # d on N → c or d
    # 
    # TI2: ss(c_M, d_N, L_ae) ∧ ¬ss(e, d_N, M) ∧ ¬on(d_N, M) ∧ e≠a → ss(e, c_M, N)
    #
    # With c_M=b, d_N=c: ss(b,c,L_ae)∧¬ss(e,c,M)∧¬on(c,M)∧e≠a → ss(e,b,N)
    # We have ¬on(c,M)✓, e≠a (if provable), ¬ss(e,c,M) — this is inside reductio!
    # And ss(b,c,L_ae) — are b and c on the same side of L_ae?
    #
    # This is promising! If inside a reductio assuming ¬ss(e,c,M), and we can
    # show ss(b,c,L_ae), then TI2 gives ss(e,b,N).
    # Similarly, from ¬ss(e,b,N) assumed (second reductio), TI2 might give ss(e,c,M).
    #
    # But we need BOTH ss(e,c,M) and ss(e,b,N). Each reductio would give
    # one from the negation of the other, but that's circular.
    #
    # UNLESS we can derive a contradiction from having BOTH ¬ss(e,c,M) and ¬ss(e,b,N).
    # Or: derive ss(e,b,N) from ¬ss(e,c,M) using TI2, then derive contradiction with 
    # something else.

    # Let me think about this more carefully...
    # 
    # Reductio: assume ¬ss(e,c,M)
    # If ss(b,c,L_ae) then TI2 → ss(e,b,N)
    # With ss(e,b,N), can we derive contradiction?
    # TI1: ss(b,c,L_ae)∧ss(e,b,N) → ¬ss(e,c,M)  — consistent, no contradiction!
    #
    # So even with ss(b,c,L_ae), TI2 gives ss(e,b,N) but TI1 confirms ¬ss(e,c,M).
    # No contradiction.
    #
    # What if we try TI2 with c_M=f, d_N=d:
    # ss(f,d,L_ae)∧¬ss(e,d,M)∧¬on(d,M)∧e≠a → ss(e,f,N)
    # ¬ss(d,f,L_ae) is known → ss(f,d,L_ae) is false. TI2 doesn't fire.

    return pb.build()


if __name__ == "__main__":
    proof = build_i9_sameside()
    result = verify_e_proof_json(proof)
    for lr in result.line_results:
        status = "PASS" if lr.valid else "FAIL"
        print(f"  L{lr.line_number:3d}: [{status}] {lr.text[:60]}")
        if not lr.valid:
            for e in lr.errors:
                print(f"        ERROR: {e}")
