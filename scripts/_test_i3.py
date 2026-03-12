"""Iteratively build and test rewritten proofs for I.3, I.6, I.7, I.9, I.10."""
import json, sys, io
sys.stdout = io.TextIOWrapper(sys.stdout.buffer, encoding='utf-8')

from verifier.unified_checker import verify_e_proof_json

def test_proof(name, proof_json):
    r = verify_e_proof_json(proof_json)
    status = "PASS" if r.accepted else "FAIL"
    print(f"\n{name}: {status}")
    if not r.accepted:
        for k, v in r.line_results.items():
            if not v.valid:
                print(f"  line {k}: {v.errors}")
        for e in r.errors:
            print(f"  GOAL: {e}")
    return r.accepted

# =====================================================================
# Prop.I.3 — Cut off cd from ab
# =====================================================================
# Premises: on(a,L), on(b,L), ¬(a=b), cd < ab
# Goal: between(a,e,b), ae = cd
#
# Strategy: Instead of Prop.I.2 (which needs c,d on a line etc.),
# use direct circle construction:
# 1. Derive ¬(c=d) from cd < ab
# 2. Construct line N through c and d  
# 3. We need a,c distinct and a,d distinct for Prop.I.2...
#    OR skip Prop.I.2 entirely and use Prop.I.1 to get a helper point.
# 
# Actually the simplest approach that avoids Prop.I.2:
# We have cd < ab. We want to place cd on L starting at a.
# 1. Need a point f with af = cd. Use Prop.I.2 for that - but we need 
#    c,d on a line, distinct from a.
# 
# The cleanest fix: Add ¬(a=c) and ¬(a=d) to the hypotheses.
# But that changes the theorem. Let's check if the e_library already
# has those...
#
# Looking at Prop.I.3 hypotheses: on(a,L), on(b,L), ¬(a=b), cd < ab
# These are exactly the 4 hypotheses. No extra distinctness.
#
# The issue is that c and d are "abstract" — they appear only in the 
# magnitude cd. The verifier doesn't know their sorts or positions.
#
# Alternative: construct a segment equal to cd using circles directly.
# - From cd < ab we get cd > 0 (non-degenerate), so ¬(c=d)
# - let-line on c,d gives us a line N  
# - But we still can't use Prop.I.2 without ¬(a=c), ¬(a=d)
#
# Real Euclid I.3: "Given two unequal straight lines, to cut off from 
# the greater a part equal to the less." He uses I.2 to place a copy.
# But formally, I.2 needs the segment endpoints on a line, which is fine
# (c and d can be placed on their own line), but also needs a≠c and a≠d.
#
# Since cd < ab and ab ≥ 0, we know cd > 0, so c≠d.
# But a might equal c or d. In practice it doesn't matter because af = cd
# is a magnitude equation. If a=c, then af = ad... still fine.
#
# The verifier is too strict here. Let me try a proof that works around
# the Prop.I.2 issue by using segment transfer directly.
#
# Key insight: we can skip Prop.I.2 and use the segment transfer axioms
# directly with a circle:
# 1. ¬(c=d) from cd < ab [M1]
# 2. let-line(c,d) → on(c,N), on(d,N) 
# 3. Let's just assume we have a point f with af = cd (via Prop.I.2)
#    and see if we can satisfy the hypotheses...
#
# Actually, let me try adding the missing premises to make Prop.I.2 work.
# The proof currently has refs=[1,2,3,4] for Prop.I.2.
# Prop.I.2 maps: theorem (a,b,c,L) → proof vars.
# conclusion: af = bc. So bc maps to cd, meaning b→c, c→d.
# Then L must be a line with c,d on it.
# a stays as a. So we need: on(c,L_cd), on(d,L_cd), ¬(c=d), ¬(a=c), ¬(a=d)
# We have ¬(c=d) from M1. We need on(c,something), on(d,something).
# We need ¬(a=c) and ¬(a=d). We DON'T have these from premises.
#
# FUNDAMENTAL ISSUE: The proof is unprovable as stated without knowing a≠c, a≠d.
# Unless we handle the edge cases where a=c or a=d separately.
#
# But Euclid's version assumes general position. For a formal proof,
# we need either:
# (a) Additional premises ¬(a=c), ¬(a=d) — changes the theorem statement
# (b) A proof approach that doesn't need them
#
# Approach (b): Use the circle construction directly, skipping Prop.I.2.
# Instead of "get a point f with af=cd then use circle at a radius af",
# use the fact that segment magnitudes exist abstractly. 
#
# Wait — what if we just use segment transfer 3 directly?
# "center(a,α) ∧ on(b,α) ∧ ac = ab → on(c,α)"
# But we need a circle first.
#
# Let me try a completely different proof:
# The simplest correct proof of I.3 that the verifier accepts would be
# to skip Prop.I.2 and use the Segment Transfer axiom to directly 
# construct the cutoff.
#
# Actually, let me try just adding the distinctness assertions as 
# "obvious" diagrammatic facts that the verifier might accept.

# ATTEMPT 1: Add explicit ¬(a=c), ¬(a=d), and line for c,d
i3_v1 = {
    "name": "Prop.I.3",
    "premises": ["on(a, L)", "on(b, L)", "¬(a = b)", "cd < ab"],
    "goal": "between(a, e, b), ae = cd",
    "lines": [
        {"id": 1, "depth": 0, "statement": "on(a, L)", "justification": "Given", "refs": []},
        {"id": 2, "depth": 0, "statement": "on(b, L)", "justification": "Given", "refs": []},
        {"id": 3, "depth": 0, "statement": "¬(a = b)", "justification": "Given", "refs": []},
        {"id": 4, "depth": 0, "statement": "cd < ab", "justification": "Given", "refs": []},
        {"id": 5, "depth": 0, "statement": "¬(c = d)", "justification": "M1 — Zero segment", "refs": [4]},
        {"id": 6, "depth": 0, "statement": "on(c, N), on(d, N)", "justification": "let-line", "refs": [5]},
        # Now we need ¬(a=c) and ¬(a=d) to use Prop.I.2.
        # We can't derive these from our premises alone.
        # Let's see what Prop.I.2 var_map does with:
        # step literal: "af = cd", theorem conclusion: "af = bc"
        # This maps b→c, c→d. Hypotheses become:
        # on(c, L_new), on(d, L_new), ¬(c=d), ¬(a=c), ¬(a=d)
        # We have on(c,N), on(d,N), ¬(c=d). Missing: ¬(a=c), ¬(a=d).
        # These should be constructible from the fact that a is on L 
        # and c,d may or may not be on L. But we can't prove it...
        # 
        # Let me try a COMPLETELY different approach for I.3.
        # Skip Prop.I.2. Use Prop.I.1 to get a helper equilateral triangle,
        # then use circle constructions.
        #
        # Actually the simplest thing: just assume we can construct a new
        # point f with af = cd using let-point + segment transfer.
        # 
        # Hmm, there's no "let-point-at-distance" construction rule.
        # The available constructions are intersection-based.
        # 
        # I think the cleanest fix is to add the needed distinctness 
        # to the I.3 theorem hypotheses in the e_library, or to change
        # the proof to avoid needing Prop.I.2.
    ],
}

# Let me try the absolutely minimal fix: 
# Instead of using Prop.I.2, use a circle at a with some known radius point.
# We have cd < ab. We want ae = cd.
# 
# If we construct a point f using Prop.I.1 from c,d, we get cf = cd = df.
# Then f is at distance cd from c. If we can place a circle at a with 
# radius = af... no, that's circular.
#
# Actually the easiest approach may be to declare a new point g 
# at distance cd from a, using let-point + the abstract segment.
# But the verifier construction rules need concrete geometric 
# intersections, not abstract magnitude placement.
#
# Let me just check: does the EXISTING Prop.I.3 proof work if we 
# add the distinctness assertions as Given?

i3_with_extra_premises = {
    "name": "Prop.I.3",
    "premises": ["on(a, L)", "on(b, L)", "¬(a = b)", "cd < ab", "¬(a = c)", "¬(a = d)"],
    "goal": "between(a, e, b), ae = cd",
    "lines": [
        {"id": 1, "depth": 0, "statement": "on(a, L)", "justification": "Given", "refs": []},
        {"id": 2, "depth": 0, "statement": "on(b, L)", "justification": "Given", "refs": []},
        {"id": 3, "depth": 0, "statement": "¬(a = b)", "justification": "Given", "refs": []},
        {"id": 4, "depth": 0, "statement": "cd < ab", "justification": "Given", "refs": []},
        {"id": 5, "depth": 0, "statement": "¬(a = c)", "justification": "Given", "refs": []},
        {"id": 6, "depth": 0, "statement": "¬(a = d)", "justification": "Given", "refs": []},
        {"id": 7, "depth": 0, "statement": "¬(c = d)", "justification": "M1 — Zero segment", "refs": [4]},
        {"id": 8, "depth": 0, "statement": "on(c, N), on(d, N)", "justification": "let-line", "refs": [7]},
        {"id": 9, "depth": 0, "statement": "af = cd", "justification": "Prop.I.2", "refs": [8, 5, 6, 7]},
        {"id": 10, "depth": 0, "statement": "¬(a = f)", "justification": "M1 — Zero segment", "refs": [4, 9]},
        {"id": 11, "depth": 0, "statement": "center(a, α), on(f, α)", "justification": "let-circle", "refs": [10]},
        {"id": 12, "depth": 0, "statement": "inside(a, α)", "justification": "Generality 3", "refs": [11]},
        {"id": 13, "depth": 0, "statement": "af < ab", "justification": "CN1 — Transitivity", "refs": [4, 9]},
        {"id": 14, "depth": 0, "statement": "¬(inside(b, α)), ¬(on(b, α))", "justification": "Segment transfer 6", "refs": [11, 13]},
        {"id": 15, "depth": 0, "statement": "on(e, α), on(e, L), between(a, e, b)", "justification": "let-intersection-line-circle-between", "refs": [12, 1, 14, 2]},
        {"id": 16, "depth": 0, "statement": "ae = af", "justification": "Segment transfer 4", "refs": [11, 15]},
        {"id": 17, "depth": 0, "statement": "ae = cd", "justification": "CN1 — Transitivity", "refs": [16, 9]},
    ],
}
test_proof("I.3 with extra premises", i3_with_extra_premises)
