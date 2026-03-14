"""Test rewritten proofs through the verifier."""
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
# Prop.I.3 rewrite
# =====================================================================
# Problem: Line 5 uses Prop.I.2 but its hypotheses aren't met.
# Prop.I.2 needs: on(b,L), on(c,L), ¬(b=c), ¬(a=b), ¬(a=c)
# But our premises only have on(a,L), on(b,L), ¬(a=b), cd < ab
# 
# The fix: Don't use Prop.I.2. Instead use segment transfer directly.
# Segment transfer 1: on(a,L), on(b,L), ¬(a=b) → segment ab exists
# Then use segment construction via circle.
# 
# Simpler approach: The original Euclid proof cuts off cd from ab.
# We can do: circle centered at a with radius cd, intersect with L.

i3_proof = {
    "name": "Prop.I.3",
    "premises": ["on(a, L)", "on(b, L)", "¬(a = b)", "cd < ab"],
    "goal": "between(a, e, b), ae = cd",
    "lines": [
        {"id": 1, "depth": 0, "statement": "on(a, L)", "justification": "Given", "refs": []},
        {"id": 2, "depth": 0, "statement": "on(b, L)", "justification": "Given", "refs": []},
        {"id": 3, "depth": 0, "statement": "¬(a = b)", "justification": "Given", "refs": []},
        {"id": 4, "depth": 0, "statement": "cd < ab", "justification": "Given", "refs": []},
        # We need ¬(c = d) from cd < ab (if cd were 0, cd < ab couldn't hold with cd = 0)
        # Actually, we can use M1: if c=d then cd=0, but cd < ab means cd is nonzero
        # Let's try: use Segment transfer 1 to place the segment
        # Actually the simplest approach: use let-circle with radius matching cd
        # But we need a point at distance cd from a... 
        # 
        # The real issue: Prop.I.2 constructs a segment at a equal to cd.
        # We need the variables to match: on(c, L2), on(d, L2) for some line.
        # Actually, Prop.I.2 just needs on(b,L), on(c,L) for the SOURCE segment endpoints,
        # not the target. Let me re-read:
        # Prop.I.2 hypotheses: on(b,L), on(c,L), ¬(b=c), ¬(a=b), ¬(a=c)
        # conclusion: af = bc
        # So it creates at point a, a segment af equal to bc.
        # The source segment is bc (both on L), target is at point a.
        # 
        # For our case: we want af = cd. So we'd need:
        #   on(c, L2), on(d, L2), ¬(c=d), ¬(a=c), ¬(a=d)
        # We don't have c,d on any line. But we CAN construct one:
        #   let-line from ¬(c=d) gives us a line with c and d on it.
        # But first we need ¬(c=d) — from cd < ab via M1.

        # Step 5: derive ¬(c=d) from cd < ab
        {"id": 5, "depth": 0, "statement": "¬(c = d)", "justification": "M1 — Zero segment", "refs": [4]},
        # Step 6: construct line through c,d
        {"id": 6, "depth": 0, "statement": "on(c, N), on(d, N)", "justification": "let-line", "refs": [5]},
        # Step 7: need ¬(a=c) and ¬(a=d)... hmm, we don't know these.
        # This is the fundamental issue with Prop.I.3 — we don't know
        # the relationship of a to c and d.
        # 
        # Alternative approach: Use circle construction directly.
        # Given cd as a magnitude and a as center, construct circle α.
        # But we need a concrete radius point...
        # 
        # Actually, let's try Prop.I.2 with the variables we have.
        # We map: theorem's (a,b,c,L) → our (a,c,d,N)
        # Needs: on(c,N), on(d,N), ¬(c=d), ¬(a=c), ¬(a=d)
        # We have ¬(c=d) and on(c,N), on(d,N).
        # We need ¬(a=c) and ¬(a=d). These may not be provable...
        # 
        # This is why the original proof is wrong. In Euclid's original,
        # I.3 uses I.2 but assumes the points are in "general position".
        # The formal proof needs additional distinctness premises or
        # a different construction approach.
        #
        # Let me try a more direct approach:
        # Use segment transfer axiom directly without Prop.I.2.
        # Segment transfer 1: from ¬(inside(b,α)) ∧ on(a,L) ∧ on(b,L) ∧ ...
        # This gives us a point on L at distance ae = af from a.
        #
        # Simplest fix: add ¬(a=c) and ¬(a=d) to premises.
        # But that changes the theorem statement...
        #
        # Another approach: use the fact that cd > 0 (from cd < ab)
        # and construct using circles directly.
    ],
}

# Let me try the simplest possible I.3 proof structure
i3_v2 = {
    "name": "Prop.I.3",
    "premises": ["on(a, L)", "on(b, L)", "¬(a = b)", "cd < ab"],
    "goal": "between(a, e, b), ae = cd",
    "lines": [
        {"id": 1, "depth": 0, "statement": "on(a, L)", "justification": "Given", "refs": []},
        {"id": 2, "depth": 0, "statement": "on(b, L)", "justification": "Given", "refs": []},
        {"id": 3, "depth": 0, "statement": "¬(a = b)", "justification": "Given", "refs": []},
        {"id": 4, "depth": 0, "statement": "cd < ab", "justification": "Given", "refs": []},
        # Derive ¬(c=d) from cd < ab
        {"id": 5, "depth": 0, "statement": "¬(c = d)", "justification": "M1 — Zero segment", "refs": [4]},
        # Construct circle at a with radius cd — but we need a point at that distance.
        # Actually, segment transfer 1 says: on(a,L), ¬(on(c,L)), cd > 0 →
        # there's a point e on L between with ae = cd.
        # Hmm no, that's not how it works.
        # 
        # Let me look at what constructions are available...
        # The answer key uses: let-circle with a point at the right distance.
        # We need: center(a, α) and on(f, α) where af = cd.
        # For let-circle, we need ¬(a = f). But we have cd as an abstract magnitude.
        # 
        # I think the correct approach for I.3 is:
        # We assume cd and ab are segment magnitudes.
        # cd < ab means we can cut off cd from ab.
        # Using the segment transfer axioms:
        # - place cd along L starting at a, giving point e with ae = cd, between(a,e,b)
        #
        # This should be: Segment transfer 2 or a construction rule.
        # Let me check what the construction rules offer.
    ],
}

# Just test if the basic structure works
print("Testing basic verifier interaction...")
basic = {
    "name": "test",
    "premises": ["on(a, L)", "on(b, L)", "¬(a = b)"],
    "goal": "on(a, L)",
    "lines": [
        {"id": 1, "depth": 0, "statement": "on(a, L)", "justification": "Given", "refs": []},
        {"id": 2, "depth": 0, "statement": "on(b, L)", "justification": "Given", "refs": []},
        {"id": 3, "depth": 0, "statement": "¬(a = b)", "justification": "Given", "refs": []},
    ]
}
test_proof("basic", basic)
