"""Test rewritten Prop.I.6 proof."""
import json, sys, io
sys.stdout = io.TextIOWrapper(sys.stdout.buffer, encoding='utf-8')
from verifier.unified_checker import verify_e_proof_json

# Prop.I.6: ∠abc = ∠acb, ¬(a=b), ¬(a=c), ¬(b=c) → ab = ac
# The key fix: Replace Angle transfer 9 with Angle transfer 1 + 4
# at lines 12 and 26 (and for 2nd subproof at line 26).

i6 = {
    "name": "Prop.I.6",
    "premises": ["∠abc = ∠acb", "¬(a = b)", "¬(a = c)", "¬(b = c)"],
    "goal": "ab = ac",
    "lines": [
        {"id": 1, "depth": 0, "statement": "∠abc = ∠acb", "justification": "Given", "refs": []},
        {"id": 2, "depth": 0, "statement": "¬(a = b)", "justification": "Given", "refs": []},
        {"id": 3, "depth": 0, "statement": "¬(a = c)", "justification": "Given", "refs": []},
        {"id": 4, "depth": 0, "statement": "¬(b = c)", "justification": "Given", "refs": []},
        {"id": 5, "depth": 0, "statement": "on(a, M), on(b, M)", "justification": "let-line", "refs": [2]},
        # --- Subproof 1: assume ac < ab, derive contradiction ---
        {"id": 6, "depth": 1, "statement": "ac < ab", "justification": "Assume", "refs": []},
        # Use Prop.I.3: need on(a,M), on(b,M), ¬(a=b), ac < ab, plus ¬(c=...?)
        # Prop.I.3 hyps: on(a,L), on(b,L), ¬(a=b), cd<ab, ¬(c=d), ¬(a=c), ¬(a=d)
        # Here cd maps to ac, so c→a, d→c, giving: on(a,M), on(b,M), ¬(a=b), ac<ab, ¬(a=c), ¬(a=a)?
        # No, that's wrong. Let me re-think the mapping.
        # Prop.I.3 conclusion: between(a,e,b), ae = cd
        # We want: between(a,d,b), ad = ac
        # So: theorem's e → our d, theorem's cd → our ac
        # theorem's cd maps to ac: theorem c→a, theorem d→c
        # Wait, the theorem conclusion says ae = cd. Our line says ad = ac.
        # So theorem e→d, and cd→ac means theorem's c→a, d→c.
        # Theorem hypotheses become: on(a,M), on(b,M), ¬(a=b), ac<ab, ¬(a=c), ¬(a=a), ¬(a=c)
        # ¬(a=a) is always false! This is a problem.
        # 
        # Actually, the variable mapping in the theorem uses its OWN variable names:
        # Prop.I.3: on(a,L), on(b,L), ¬(a=b), cd<ab → between(a,e,b), ae=cd
        # The theorem uses variables a,b,c,d,e,L.
        # When applied, the var_map matches conclusion variables to step variables.
        # Step says: between(a,d,b), ad = ac
        # Conclusion says: between(a,e,b), ae = cd
        # Match: a→a, e→d, b→b, c→a(?), d→c(?)
        # This gives c→a which makes ¬(a=c) → ¬(a=a) which is false.
        #
        # So the PROOF is wrong for this variable mapping!
        # The statement "ad = ac" creates a bad mapping because c in cd maps to a.
        #
        # Let me try instead: we need a DIFFERENT variable for the shorter segment.
        # Instead of "ad = ac", use a fresh magnitude.
        # Actually, looking at the text answer key line 7: "between(a, d, b), ad = ac"
        # This is the text key's version too. The issue is that Prop.I.3's c,d
        # variables get mapped such that one becomes a.
        #
        # SOLUTION: Use Prop.I.3 differently. Instead of writing the conclusion
        # as "ad = ac", write it as "between(a, d, b), ad = ca" 
        # (using M3 symmetry: ac = ca). Then cd→ca maps c→c, d→a...
        # Still bad: d→a gives ¬(a=d) → ¬(a=a).
        # 
        # The real issue is that Prop.I.3 has hypothesis ¬(a=c), ¬(a=d)
        # where c,d are the segment endpoints. When one endpoint IS a,
        # we can't apply the theorem.
        # 
        # This means the proof needs a different approach. We can use the
        # segment as "between(a,d,b), ad = ca" where ca = ac by M3.
        # But Prop.I.3 matching tries to derive ae=cd where cd is the
        # given segment. Let me check: if step says "ad = ca", does
        # the var_map put c→c, d→a? Then ¬(a=d) → ¬(a=a) still fails.
        #
        # Alternative: use Prop.I.3 with a DIFFERENT point name for the
        # second segment. For example, use a separate segment fg = ac 
        # first, then apply Prop.I.3 with fg < ab.
        # But that's circular — we'd need Prop.I.2 to construct fg = ac.
        #
        # Actually, the most direct approach: Just avoid Prop.I.3.
        # Instead, construct the cutoff directly using circles, which is
        # what Prop.I.3 internally does anyway.
        # 
        # Or: check if the verifier would accept Prop.I.3 refs that include
        # the right hyps directly without the bad mapping.
        # The theorem matcher tries to match step literals (between(a,d,b), ad=ac)
        # against theorem conclusions (between(a,e,b), ae=cd).
        # Match: a→a, e→d, b→b, and ae→ad means a→a, e→d.
        # Then ae=cd → ad=cd, so cd→ac means we need c→a, d→c.
        # Hyp ¬(a=c) → ¬(a=a) is FALSE. So this theorem application is invalid.
        #
        # The correct fix: rewrite the proof to avoid this bad mapping.
        # Use premise ¬(a=c) from the Given, construct line on(a,P), on(c,P),
        # then apply Prop.I.3 on line P with segment ac cutoff from ab
        # mapped so that the "cd" in I.3 becomes a different segment.
        #
        # Wait: actually the problem is that Prop.I.3 says "cut cd from ab".
        # In I.6 we want to "cut ac from ab". Since a is already an endpoint
        # of ab, and the segment to cut is ac where a is a shared point,
        # the mapping breaks.
        #
        # The simplest fix: restructure to cut off a segment equal to ac
        # using a FRESH segment name. E.g.:
        # 1. By M3 Symmetry: ac = ca
        # 2. ca < ab (from ac < ab and ac = ca)  
        # 3. Apply Prop.I.3 with "ca" as the segment: between(a,d,b), ad = ca
        #    Here cd→ca maps c→c, d→a... still c→c, d→a, ¬(a=d)→¬(a=a). Doh.
        #
        # I think the fundamental issue is that whenever you want ad = XY where
        # a is endpoint of both the target and the line, X or Y will map to a.
        #
        # The REAL solution: the proof should use a helper construction.
        # Use Prop.I.2 to get a fresh segment fg = ac at some other point,
        # then use Prop.I.3 with fg < ab.
        # Or: just use direct circle construction (what I.3 does internally).

        # APPROACH: Skip Prop.I.3, use direct circle cutoff
        # Given ac < ab, we can construct d on M between a and b with ad = ac:
        # - ¬(a = c) → let circle α at a, radius ac: center(a,α), on(c,α)... 
        #   but c isn't on M necessarily
        # - Actually: let-circle requires ¬(a = c), gives center(a,α), on(c,α)
        # - inside(a,α) from Generality 3
        # - ac < ab → ¬(inside(b,α)), ¬(on(b,α)) [Segment transfer 6 + 5]
        # - let-intersection-line-circle-between: inside(a,α) ∧ on(a,M) ∧ 
        #   ¬(inside(b,α)) ∧ ¬(on(b,α)) ∧ on(b,M) → on(d,α), on(d,M), between(a,d,b)
        # - Segment transfer 4: center(a,α) ∧ on(c,α) ∧ on(d,α) → ad = ac

        {"id": 7, "depth": 1, "statement": "center(a, α), on(c, α)", "justification": "let-circle", "refs": [3]},
        {"id": 8, "depth": 1, "statement": "inside(a, α)", "justification": "Generality 3", "refs": [7]},
        {"id": 9, "depth": 1, "statement": "¬(inside(b, α)), ¬(on(b, α))", "justification": "Segment transfer 6", "refs": [7, 6]},
        {"id": 10, "depth": 1, "statement": "on(d, α), on(d, M), between(a, d, b)", "justification": "let-intersection-line-circle-between", "refs": [8, 5, 9]},
        {"id": 11, "depth": 1, "statement": "ad = ac", "justification": "Segment transfer 4", "refs": [7, 10]},
        {"id": 12, "depth": 1, "statement": "¬(d = a)", "justification": "Betweenness 2", "refs": [10]},
        {"id": 13, "depth": 1, "statement": "¬(d = b)", "justification": "Betweenness 3", "refs": [10]},
        # Fix: use Angle transfer 1+4 instead of Angle transfer 9
        # ∠dba = 0 from collinear a,d,b at vertex b (not between(d,b,a))
        {"id": 14, "depth": 1, "statement": "on(b, N), on(c, N)", "justification": "let-line", "refs": [4]},
        {"id": 15, "depth": 1, "statement": "∠dba = 0", "justification": "Angle transfer 1", "refs": [5, 10]},
        {"id": 16, "depth": 1, "statement": "∠dbc = ∠abc", "justification": "Angle transfer 4", "refs": [5, 10, 14, 15]},
        {"id": 17, "depth": 1, "statement": "∠dbc = ∠acb", "justification": "CN1 — Transitivity", "refs": [16, 1]},
        {"id": 18, "depth": 1, "statement": "bc = cb", "justification": "M3 — Symmetry", "refs": []},
        {"id": 19, "depth": 1, "statement": "ad = ca", "justification": "M3 — Symmetry", "refs": [11]},
        {"id": 20, "depth": 1, "statement": "dc = ab, ∠bdc = ∠cab, ∠bcd = ∠cba, △dbc = △acb", "justification": "SAS-elim", "refs": [19, 17, 18]},
        {"id": 21, "depth": 1, "statement": "△acb = △abc", "justification": "M8 — Area symmetry", "refs": []},
        {"id": 22, "depth": 1, "statement": "△dbc = △abc", "justification": "CN1 — Transitivity", "refs": [20, 21]},
        {"id": 23, "depth": 1, "statement": "(△adc + △dcb) = △adb", "justification": "Area transfer 3", "refs": [10, 5]},
        {"id": 24, "depth": 1, "statement": "△dbc < △abc", "justification": "CN5 — Whole > Part", "refs": [23]},
        {"id": 25, "depth": 1, "statement": "⊥", "justification": "⊥-intro", "refs": [22, 24]},
        {"id": 26, "depth": 0, "statement": "¬(ac < ab)", "justification": "⊥-elim", "refs": [6]},
        # --- Subproof 2: assume ab < ac, derive contradiction ---
        {"id": 27, "depth": 1, "statement": "ab < ac", "justification": "Assume", "refs": []},
        # Same approach: direct circle cutoff for between(a,d2,c), ad2 = ab
        # But here we cut ab from ac, so we need on(a,P), on(c,P) line
        {"id": 28, "depth": 1, "statement": "on(c, P), on(a, P)", "justification": "let-line", "refs": [3]},
        {"id": 29, "depth": 1, "statement": "center(a, β), on(b, β)", "justification": "let-circle", "refs": [2]},
        {"id": 30, "depth": 1, "statement": "inside(a, β)", "justification": "Generality 3", "refs": [29]},
        {"id": 31, "depth": 1, "statement": "¬(inside(c, β)), ¬(on(c, β))", "justification": "Segment transfer 6", "refs": [29, 27]},
        {"id": 32, "depth": 1, "statement": "on(d2, β), on(d2, P), between(a, d2, c)", "justification": "let-intersection-line-circle-between", "refs": [30, 28, 31]},
        {"id": 33, "depth": 1, "statement": "ad2 = ab", "justification": "Segment transfer 4", "refs": [29, 32]},
        # Fix: Angle transfer 1+4 for ∠d2ca = ∠acb... wait, we need ∠d2cb = ∠acb
        # d2 is between a and c on line P. Vertex is c.
        # on(c,P), on(d2,P), on(a,P), between(a,d2,c)
        # ∠d2ca = 0 from collinear at vertex c (¬between(d2,c,a) from between(a,d2,c))
        # Hmm, ∠d2ca is the angle at vertex c from d2 to a. Since d2,c,a are collinear
        # and NOT between(d2,c,a), ∠d2ca = 0.
        # Then ∠d2cb = ∠acb via angle addition (with ∠d2ca = 0).
        # Wait: ∠acb = ∠acd2 + ∠d2cb? No, angle addition at vertex c:
        # ∠acb with d2 between a and c... 
        # Actually we want ∠d2cb = ∠acb since d2 is on the same ray as a from c.
        {"id": 34, "depth": 1, "statement": "∠d2ca = 0", "justification": "Angle transfer 1", "refs": [28, 32]},
        {"id": 35, "depth": 1, "statement": "∠d2cb = ∠acb", "justification": "Angle transfer 4", "refs": [28, 32, 14, 34]},
        {"id": 36, "depth": 1, "statement": "∠d2cb = ∠abc", "justification": "CN1 — Transitivity", "refs": [35, 1]},
        {"id": 37, "depth": 1, "statement": "cb = bc", "justification": "M3 — Symmetry", "refs": []},
        {"id": 38, "depth": 1, "statement": "ad2 = ba", "justification": "M3 — Symmetry", "refs": [33]},
        {"id": 39, "depth": 1, "statement": "d2b = ac, ∠cd2b = ∠bac, ∠cbd2 = ∠abc, △d2cb = △abc", "justification": "SAS-elim", "refs": [38, 36, 37]},
        {"id": 40, "depth": 1, "statement": "△d2cb < △acb", "justification": "CN5 — Whole > Part", "refs": [32]},
        {"id": 41, "depth": 1, "statement": "△acb = △abc", "justification": "M8 — Area symmetry", "refs": []},
        {"id": 42, "depth": 1, "statement": "△d2cb = △acb", "justification": "CN1 — Transitivity", "refs": [39, 41]},
        {"id": 43, "depth": 1, "statement": "⊥", "justification": "⊥-intro", "refs": [42, 40]},
        {"id": 44, "depth": 0, "statement": "¬(ab < ac)", "justification": "⊥-elim", "refs": [27]},
        {"id": 45, "depth": 0, "statement": "ab = ac", "justification": "< trichotomy", "refs": [26, 44]},
    ],
}

r = verify_e_proof_json(i6)
print("I.6:", "PASS" if r.accepted else "FAIL")
if not r.accepted:
    for k, v in r.line_results.items():
        if not v.valid:
            print(f"  line {k}: {v.errors}")
    for e in r.errors:
        print(f"  GOAL: {e}")
