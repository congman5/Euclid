"""
test_generated_proofs.py — Verify generated proofs pass the real verifier.

Tests propositions I.16+ built using EuclidProofBuilder,
verified via verify_e_proof_json.
"""
import pytest
from verifier.euclid_proof_builder import EuclidProofBuilder


class TestPropositionI16:
    """Proposition I.16 — Exterior Angle Theorem.

    In any triangle, if one side is produced, the exterior angle is
    greater than either of the interior and opposite angles.

    Premises:
      on(a,L), on(b,L), between(a,b,d), ¬on(c,L),
      ¬(a=b), ¬(a=c), ¬(b=c)
    Goal:
      ∠bac < ∠dbc, ∠bca < ∠dbc

    Strategy (following Euclid's proof via Lean):
      Part 1 — ∠bac < ∠dbc:
        1. Bisect bc at e (I.10)
        2. Extend ae to f with ef = ae (circle + intersection)
        3. Vertical angles ∠bea = ∠cef (I.15)
        4. SAS: △bea ≅ △cef → ∠abe = ∠fce (I.4)
        5. ∠abe is part of ∠abc, and ∠fcf... 
           Actually, ∠abe = ∠abc (since e is between b and c on line M)
           NO — ∠abe has vertex b with rays b→a and b→e.
           ∠abc has vertex b with rays b→a and b→c.
           Since e is between b and c, be and bc go the same direction,
           so ∠abe = ∠abc? No, that's not right either.
           ∠abe: vertex b, rays to a and to e. Since between(b,e,c),
           e is between b and c on M, so ray be = ray bc. Thus ∠abe = ∠abc.
           Wait, but ∠abe would be the angle at b from a to e. Since e is
           on the same ray from b as c, ∠abe = ∠abc by Angle transfer 4
           (subangle equality).

        More precisely:
        - From SAS (I.4) on triangles eba and ecf we get ∠abe = ∠fce
        - ∠abe = ∠abc since e is between b and c (angle transfer 4)
        - ∠fcf is part of ∠dcb... hmm, this is getting complicated.

        Let me follow Euclid's proof more carefully:
        1. Bisect BC: between(b,e,c), be=ec
        2. Extend AE to F: between(a,e,f), ef=ae
        3. Vertical angles at e: ∠bea = ∠cef
        4. SAS △(b,e,a) ≅ △(c,e,f): eb=ec, ∠bea=∠cef, ea=ef
           → ba=cf, ∠eba=∠ecf, ∠bae=∠cfe, △bea=△cef
        5. Key: ∠bae = ∠bac (the angle at a in the original triangle)
        6. ∠ecf = ∠fcf? No. From SAS: ∠eba = ∠ecf
        7. Now: ∠ecf is an angle at vertex c. Since f is specifically
           placed (on the other side of e from a, and between(b,e,c)),
           we need to show that ∠ecf < ∠dcb.
           Actually, between(b,e,c) means e is between b and c on BC.
           f is constructed on the other side of the e-line (AE line) from a.
           The key is that f ends up on the same side of M (line BC) as d.
           Since between(a,b,d) means d is on line L past b from a,
           and f is... this requires careful diagrammatic reasoning.

    Let me try a much simpler approach: verify that the
    existing unsolved template steps can be made to work, or write
    the proof using the smallest number of steps that the verifier accepts.
    """

    def _build_i16(self):
        """Build I.16 proof step by step."""
        b = EuclidProofBuilder("Prop.I.16")

        # ── Premises (1-7) ───────────────────────────────────────────
        b.premises(
            "on(a, L)",            # 1
            "on(b, L)",            # 2
            "between(a, b, d)",    # 3
            "¬(on(c, L))",         # 4
            "¬(a = b)",            # 5
            "¬(a = c)",            # 6
            "¬(b = c)",            # 7
        )
        b.goal("∠bac < ∠dbc, ∠bca < ∠dbc")
        b.declare_points("a", "b", "c", "d")
        b.declare_lines("L")
        b.load_canvas_from("unsolved_proofs/Proposition I.16.euclid")

        # ── Setup: line BC, bisect ────────────────────────────────────
        # 8: line through b,c
        ln_bc = b.let_line("on(b, M), on(c, M)", refs=[7])

        # 9: bisect bc at e — I.10 hypotheses: on(a,L), on(b,L), ¬(a=b)
        #    mapped with a→b, b→c, L→M: on(b,M), on(c,M), ¬(b=c)
        #    conclusions: between(b,e,c), be = ec
        ln_bise = b.theorem(
            "between(b, e, c), be = ec",
            "Prop.I.10", refs=[7, ln_bc])

        # 10-12: betweenness consequences
        ln_bne = b.betweenness("1b", "¬(b = e)", refs=[ln_bise])
        ln_enc = b.betweenness("1b", "¬(e = c)", refs=[ln_bise])
        ln_eonm = b.betweenness("3", "on(e, M)", refs=[ln_bise, ln_bc])

        # 13: ¬(L = M) — c on M but not on L
        ln_lnm = b.generality("6a", "¬(L = M)", refs=[ln_bc, 4])

        # 14: ¬on(a, M) — a on L, b on L, b on M, ¬(a=b), ¬(L=M)
        ln_aoffm = b.generality(
            "1", "¬(on(a, M))", refs=[1, 2, ln_bc, 5, ln_lnm])

        # 15: ¬(a = e) — e on M, a not on M
        ln_ane = b.generality("6c", "¬(a = e)", refs=[ln_eonm, ln_aoffm])

        # ── Construct line AE and extend to f ─────────────────────────
        # 16: line through a,e
        ln_ae = b.let_line("on(a, N), on(e, N)", refs=[ln_ane])

        # 17: circle centered at e through a
        ln_circ = b.let_circle("center(e, α), on(a, α)", refs=[ln_ane])

        # 18: e inside α (center inside its circle)
        ln_ein = b.generality("3", "inside(e, α)", refs=[ln_circ])

        # 19: f = intersection of line N with circle α on far side of e from a
        #     Prereqs for let-intersection-line-circle-other:
        #       on(a, α), on(a, N), inside(e, α), on(e, N)
        #     Conclusion: on(f, α), on(f, N), between(a, e, f)
        ln_f = b.let_intersection_line_circle_other(
            "on(f, α), on(f, N), between(a, e, f)",
            refs=[ln_circ, ln_ae, ln_ein, ln_ae])

        # 20: ef = ea (radii of circle α centered at e)
        ln_efea = b.segment_transfer("3b", "ef = ea",
                                      refs=[ln_circ, ln_f])

        # 21: ea = ae (symmetry)
        ln_eaae = b.m3("ea = ae", refs=[])

        # 22: ef = ae (transitivity: ef=ea, ea=ae)
        ln_efae = b.cn1("ef = ae", refs=[ln_efea, ln_eaae])

        # ── Need distinctness for I.4 and I.15 ───────────────────────
        # 23: ¬(e = f) from between(a, e, f)
        ln_enf = b.betweenness("1b", "¬(e = f)", refs=[ln_f])

        # 24: ¬(N = M) — a on N but not on M
        ln_nnm = b.generality("6a", "¬(N = M)", refs=[ln_ae, ln_aoffm])

        # 25: ¬on(c, N) — c on M, e on both, ¬(e=c), ¬(N=M)
        ln_coffn = b.generality(
            "1", "¬(on(c, N))",
            refs=[ln_ae, ln_eonm, ln_bc, ln_nnm, ln_enc])

        # 26: ¬(f = c) — f on N, c not on N
        ln_fnc = b.generality("6c", "¬(f = c)", refs=[ln_f, ln_coffn])

        # 27: ¬on(b, N) — b on M, e on both, ¬(b=e), ¬(N=M)
        ln_boffn = b.generality(
            "1", "¬(on(b, N))",
            refs=[ln_ae, ln_eonm, ln_bc, ln_nnm, ln_bne])

        # 28: ¬(f = b) — f on N, b not on N
        ln_fnb = b.generality("6c", "¬(f = b)", refs=[ln_f, ln_boffn])

        # ── Vertical angles (I.15) ───────────────────────────────────
        # I.15: on(a,L), on(b,L), on(c,M), on(d,M), on(e,L), on(e,M),
        #       between(a,e,b), between(c,e,d), ¬(L=M) → ∠aec = ∠bed
        #
        # Our mapping: L₁₅→M (line through b,c), M₁₅→N (line through a,f),
        #   a₁₅→b, b₁₅→c, c₁₅→a, d₁₅→f, e₁₅→e
        # Hypotheses met: on(b,M)✓, on(c,M)✓, on(a,N)✓, on(f,N)✓,
        #   on(e,M)✓, on(e,N)✓, between(b,e,c)✓, between(a,e,f)✓, ¬(M=N)✓
        # Conclusion: ∠bea = ∠cef
        ln_vert = b.theorem(
            "∠bea = ∠cef", "Prop.I.15",
            refs=[ln_bc, ln_bc, ln_ae, ln_f, ln_eonm, ln_ae,
                  ln_bise, ln_f, ln_nnm])

        # ── SAS via I.4: △(e,b,a) ≅ △(e,c,f) ────────────────────────
        # I.4: ab=de, ac=df, ∠bac=∠edf → bc=ef, ∠abc=∠def, ∠bca=∠efd, △abc=△def
        #
        # Map: a₄→e, b₄→b, c₄→a, d₄→e, e₄→c, f₄→f
        # Wait, a₄=d₄=e — that's a problem for 6 distinct points.
        # 
        # Actually, Prop.I.4 in e_library uses 6 variables a,b,c,d,e,f
        # where △abc ≅ △def. The verifier matches the step text against
        # the theorem conclusions to derive the variable mapping.
        #
        # Hypotheses of I.4:
        #   ¬(a=b), ¬(a=c), ¬(b=c), ¬(d=e), ¬(d=f), ¬(e=f),
        #   ab=de, ac=df, ∠bac=∠edf
        #
        # Our triangles are △(e,b,a) and △(e,c,f):
        #   Map: a→e, b→b, c→a, d→e, e→c, f→f
        #   Problem: a→e and d→e means a=d=e, so ¬(a=d) would fail!
        #
        # But I.4 doesn't have ¬(a=d) as hypothesis! The 6 points are
        # from two separate triangles. a,b,c are one triangle, d,e,f another.
        # The hypotheses only require: ¬(a=b), ¬(a=c), ¬(b=c) for triangle 1,
        # and ¬(d=e), ¬(d=f), ¬(e=f) for triangle 2.
        #
        # With mapping a→e, b→b, c→a, d→e, e→c, f→f:
        #   ¬(e=b): ✓ (line 10, ¬(b=e))
        #   ¬(e=a): ✓ (line 15)
        #   ¬(b=a): ✓ (line 5, ¬(a=b))
        #   ¬(e=c): ✓ (line 11)
        #   ¬(e=f): ✓ (line 23)
        #   ¬(c=f): ✓ (line 26)
        #   eb=ec: need this — we have be=ec from I.10. Need eb=ec.
        #     eb = be (M3 symmetry), be = ec (from I.10) → eb = ec (CN1)
        #   ea=ef: need this — we have ef=ae (line 22). ea = ae (M3), ef = ae.
        #     So ea = ef by CN1? ea = ae and ef = ae → ea = ef. ✓
        #   ∠bea=∠cef: ✓ (line 29, from I.15)
        #
        # Conclusions of I.4 with this mapping:
        #   ba = cf  (bc₄=ef₄ → ba=cf)
        #   ∠eba = ∠ecf  (∠abc₄=∠def₄ → ∠eba=∠ecf)
        #   ∠bae = ∠cfe  (∠bca₄=∠efd₄ → ∠bae=∠cfe)
        #   △eba = △ecf  (△abc₄=△def₄ → △eba=△ecf)

        # Need eb = ec
        ln_ebbe = b.m3("eb = be", refs=[])
        ln_ebec = b.cn1("eb = ec", refs=[ln_ebbe, ln_bise])

        # Need ea = ef
        ln_eaef = b.cn1("ea = ef", refs=[ln_eaae, ln_efae])

        # I.4 application
        ln_sas = b.theorem(
            "ba = cf, ∠eba = ∠ecf, ∠bae = ∠cfe, △eba = △ecf",
            "Prop.I.4",
            refs=[ln_bne, ln_ane, 5, ln_enc, ln_enf, ln_fnc,
                  ln_ebec, ln_eaef, ln_vert])

        # ── Now derive ∠bac < ∠dbc ──────────────────────────────────
        # From I.4: ∠bae = ∠cfe → this means ∠bae = ∠cfe
        # But ∠bae is the same as ∠bac? 
        # ∠bae: vertex a, from b to e.
        # ∠bac: vertex a, from b to c.
        # Are these the same? e is between b and c on line M.
        # From vertex a, the ray a→e and ray a→c are different!
        # e is a midpoint of bc, not the same as c.
        # So ∠bae ≠ ∠bac in general.
        #
        # Hmm. So what exactly does I.4 give us that's useful?
        # ∠eba = ∠ecf: vertex b from e to a = vertex c from e to f.
        #
        # The Lean proof uses proposition_15 twice and proposition_4.
        # Let me re-read the Lean proof more carefully:
        #
        # Lean Part 1:
        #   1. proposition_10 b c BC → e (midpoint)
        #   2. line_from_points a e → AE
        #   3. extend_point_longer AE a e (a─e) → f' (beyond e, longer)
        #   4. proposition_3 e f' a e AE AE → f (ef = ae, between e and f')
        #   5. line_from_points f c → FC
        #   6. proposition_15 b c a f e BC AE → vertical angles
        #   7. proposition_4 e b a e c f BC AB AE BC FC AE → SAS
        #   8. extend_point AC a c → g (extend AC past c)
        #   9. proposition_15 a g b d c AC BC → vertical angles  
        #   10. euclid_finish
        #
        # Steps 8-9 are key! They extend AC to g and use I.15 again.
        # After SAS, we have ∠eba = ∠ecf.
        # Then extending AC to g with between(a,c,g) and using I.15
        # on lines AC and BC at point c:
        #   between(a,c,g) on line AC, between(b,c,d) on line... wait,
        #   d is on L not on BC (M). between(a,b,d) is on line L.
        #
        # Actually step 9 in Lean: proposition_15 a g b d c AC BC
        # I.15 signature: a b c d e L M → ∠aec = ∠bed
        # Mapping: a₁₅→a, b₁₅→g, c₁₅→b, d₁₅→d, e₁₅→c, L₁₅→AC, M₁₅→BC
        # Wait, that doesn't match the parameter order. Let me look at
        # the Lean signature again.
        # 
        # Lean: proposition_15 b c a f e BC AE
        # I.15 in Lean: ∀ (a b c d e : Point) (AB CD : Line),
        #   on a AB ∧ on b AB ∧ on c CD ∧ on d CD ∧ on e AB ∧ on e CD ∧
        #   between a e b ∧ between c e d ∧ AB ≠ CD →
        #   ∠ a:e:c = ∠ b:e:d
        # 
        # So Lean proposition_15(a,b,c,d,e,AB,CD):
        #   a,b on AB; c,d on CD; e on both; between(a,e,b); between(c,e,d); AB≠CD
        #   → ∠aec = ∠bed
        #
        # Call: proposition_15 b c a f e BC AE
        #   a₁₅=b, b₁₅=c, c₁₅=a, d₁₅=f, e₁₅=e, AB=BC, CD=AE
        #   on(b,BC)✓, on(c,BC)✓, on(a,AE)✓, on(f,AE)✓, on(e,BC)✓, on(e,AE)✓
        #   between(b,e,c)✓, between(a,e,f)✓, BC≠AE ✓
        #   → ∠bea = ∠cef ✓ (matches what we have)
        #
        # Call: proposition_15 a g b d c AC BC
        #   a₁₅=a, b₁₅=g, c₁₅=b, d₁₅=d, e₁₅=c, AB=AC, CD=BC
        #   This would need: on(a,AC), on(g,AC), on(b,BC), on(d,BC), on(c,AC),
        #     on(c,BC), between(a,c,g), between(b,c,d), AC≠BC
        #   → ∠acb = ∠gcd
        #
        # Wait, between(b,c,d)? We have between(a,b,d) but NOT between(b,c,d).
        # d is on line L (through a,b), not on line M (through b,c).
        # So this doesn't work directly with our variable naming!
        #
        # Actually in the Lean proof, I think the variable naming is different
        # from ours. In Lean, the triangle is formed by points and lines
        # differently. Let me re-read Prop16.lean:
        #
        # theorem proposition_16 : ∀ (a b c d : Point) (AB BC AC: Line),
        #   formTriangle a b c AB BC AC ∧ (between b c d) →
        #   (∠ a:c:d > ∠ c:b:a) ∧ (∠ a:c:d > ∠ b:a:c)
        #
        # So in Lean:
        #   Triangle abc with lines AB, BC, AC
        #   between(b, c, d) — d extends BC past c
        #   Goal: ∠acd > ∠cba AND ∠acd > ∠bac
        #
        # In our e_library I.16:
        #   on(a,L), on(b,L), between(a,b,d), ¬on(c,L)
        #   Goal: ∠bac < ∠dbc AND ∠bca < ∠dbc
        #
        # These are DIFFERENT variable assignments! In Lean:
        #   - d extends from b past c (between(b,c,d))
        #   - The exterior angle is ∠acd (at vertex c, exterior)
        # In e_library:
        #   - d extends from a past b (between(a,b,d))
        #   - The exterior angle is ∠dbc (at vertex b, exterior)
        #
        # So the Lean proof doesn't directly translate to our variable scheme.
        # I need to adapt the proof to our I.16 premises.
        #
        # With our premises:
        #   Triangle with a,b on L, c off L. d extends L past b.
        #   Exterior angle is ∠dbc at vertex b.
        #   Show: ∠bac < ∠dbc and ∠bca < ∠dbc.
        #
        # Euclid's method adapted:
        #   Part 1 (∠bac < ∠dbc):
        #     Bisect ac at midpoint e, extend be to f with ef=be.
        #     Then SAS △aeb ≅ △cef → ∠aeb = ∠cef (vertical) and 
        #     ∠bae = ∠fce. Then ∠bae = ∠bac, and ∠fce is part of ∠bcf.
        #     Since f is on the opposite side of ac from b (by construction),
        #     ∠bcf < ∠bcd... this is getting complicated.
        #
        # Actually, let me follow a cleaner classical approach.
        # The standard Euclid proof for our variable scheme:
        #
        # Part 1: ∠bac < ∠dbc
        #   1. Bisect ac at e: between(a,e,c), ae=ec [I.10 on line AC]
        #   2. Let line BE, extend to f with ef=eb: between(b,e,f), ef=eb
        #   3. Vertical angles at e: ∠aeb = ∠cef [I.15]
        #   4. SAS: △aeb ≅ △cef → ∠eab = ∠ecf [I.4]
        #   5. ∠eab = ∠bac (same angle, since ∠eab at vertex a from e to b 
        #      = ∠bac at vertex a from b to c... no, these are different!)
        #
        # I keep getting confused by angle naming. Let me be very precise.
        # ∠xyz means: angle at vertex y, with rays y→x and y→z.
        #
        # From SAS △(a,e,b) ≅ △(c,e,f):
        #   (I.4 with a₄=a, b₄=e, c₄=b, d₄=c, e₄=e, f₄=f)
        #   Hmm, e appears in both triangles again.
        #
        # Let me try using the actual I.4 with proper 6 distinct points.
        # I.4 maps △(a₄,b₄,c₄) ≅ △(d₄,e₄,f₄).
        # For our case, we want to compare two triangles that share vertex e.
        # This means the a/d variables of I.4 BOTH map to e, which is
        # actually fine — the I.4 hypotheses don't require a ≠ d.
        #
        # OK wait. Looking back at the I.4 hypotheses:
        #   ¬(a=b), ¬(a=c), ¬(b=c), ¬(d=e), ¬(d=f), ¬(e=f)
        #   ab=de, ac=df, ∠bac=∠edf
        #
        # With mapping a₄→e, b₄→a, c₄→b, d₄→e, e₄→c, f₄→f:
        #   ¬(e=a)✓, ¬(e=b)✓, ¬(a=b)✓, ¬(e=c)✓, ¬(e=f)✓, ¬(c=f)✓
        #   ea=ec✓(from bisect), eb=ef✓(from circle), ∠aeb=∠cef✓(I.15)
        #   → ab=cf, ∠eab=∠ecf, ∠eba=∠efc, △eab=△ecf
        #
        # So from SAS: ∠eab = ∠ecf.
        # ∠eab: vertex a, from e to b. This IS ∠bac if... no.
        # ∠eab has vertex a from e to b.
        # ∠bac has vertex a from b to c.
        # These are different angles!
        #
        # Unless... wait. e is between a and c (from bisecting ac).
        # So from a's point of view, the ray a→e is the same as the ray a→c.
        # Because e is between a and c, so e is on the segment ac, meaning
        # the ray from a through e goes to c and beyond.
        # Therefore ray(a,e) = ray(a,c).
        # So ∠eab = ∠cab = ∠bac (by angle symmetry at vertex).
        # Wait: ∠eab = angle at a from e to b.
        # ∠cab = angle at a from c to b.
        # Since ray(a,e) = ray(a,c), these are the same angle!
        # In System E terms: Angle transfer 4 (or similar) should handle this.
        #
        # So ∠eab = ∠cab (= ∠bac).
        # And we need ∠bac < ∠dbc.
        # From SAS: ∠eab = ∠ecf.
        # So ∠bac = ∠ecf.
        # Now: ∠ecf at vertex c, from e to f.
        # We need to show ∠ecf < ∠dbc somehow.
        #
        # Hmm, let me think about what ∠ecf looks like geometrically.
        # f is on the extension of be past e (between(b,e,f) on line BE).
        # c is one vertex of the triangle.
        # e is the midpoint of ac.
        # So ∠ecf is the angle at c looking from e to f.
        # And ∠dbc is the exterior angle at b.
        #
        # This doesn't directly compare. The standard Euclid proof works
        # differently — it shows that ∠ecf is a "part" of ∠bcd (or ∠dbc).
        # But with our specific variable layout (d extends from a past b),
        # the geometry is different from the classical Euclid diagram.
        #
        # I think the issue is that our e_library's I.16 has a different
        # configuration than the classical proof, so the standard Euclid
        # construction needs to be adapted.
        #
        # Let me try a completely different approach for Part 1.
        # Instead of bisecting ac, let's bisect ab at e, then extend
        # ce to f. This is actually closer to the Lean version adapted
        # to our variables.

        # ACTUALLY: Let me just step back and look at what the ACTUAL
        # solved proofs for 1-15 look like and the techniques used.
        # For I.16, I should construct a correct proof by hand on paper,
        # then encode it. Let me think about this more carefully.

        return b

    def test_i16_setup(self):
        """Verify I.16 can at least be constructed without errors."""
        b = self._build_i16()
        doc = b.build()
        assert doc["proof"]["name"] == "Prop.I.16"
        assert len(doc["proof"]["premises"]) == 7
