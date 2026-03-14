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

# Test: can we derive ¬on(c, M) from angle facts?
# If on(c,M) and on(a,M) and on(b,M), then a,b,c collinear.
# From DA1: ∠abc = 0 or between(a,b,c). 
# If ∠abc = 0 and ∠acb = 0 and ∠abc = ∠acb, that's fine.
# We can't derive ¬on(c,M) from the premises alone.
# We need a non-degeneracy premise.

# Alternative: add ¬on(c, M) as a premise.
# But that changes the theorem.

# Actually, the text answer key I.6 doesn't need this. Let me look at what
# the text answer key's I.6 does for Area transfer 3.
# Text key line 19: (△adc + △dcb) = △adb  [Area transfer 3] refs: [7, 5]
# Line 7: between(a, d, b), ad = ac  [Prop.I.3]
# Line 5: on(a, M), on(b, M)
# 
# The area transfer needs ¬on(c,M). But the text key doesn't establish this either!
# This means the text key was verified with a MORE PERMISSIVE checker that
# doesn't require ¬on(d,L) for area transfer.
#
# Let me check: maybe the area transfer axiom should not require ¬on(d,L).
# Actually in some formulations, area transfer 3 is just:
# between(a,c,b) → △acd + △dcb = △adb (for any d)
# The ¬on(d,L) condition ensures d is not collinear (triangle is non-degenerate).
# If d IS on L, both sides are 0, so the equation holds trivially.
# Therefore the axiom should work without the ¬on(d,L) condition!

# Let me test: remove ¬on(d,L) from DAr2a and see if things work.
print("Testing just area transfer...")
test = {
    "name": "test_area",
    "premises": ["on(a, M)", "on(b, M)", "between(a, d, b)", "on(d, M)"],
    "goal": "(\\u25b3adc + \\u25b3cdb) = \\u25b3acb",
    "lines": [
        {"id": 1, "depth": 0, "statement": "on(a, M)", "justification": "Given", "refs": []},
        {"id": 2, "depth": 0, "statement": "on(b, M)", "justification": "Given", "refs": []},
        {"id": 3, "depth": 0, "statement": "between(a, d, b)", "justification": "Given", "refs": []},
        {"id": 4, "depth": 0, "statement": "on(d, M)", "justification": "Given", "refs": []},
        {"id": 5, "depth": 0, "statement": "(\\u25b3adc + \\u25b3cdb) = \\u25b3acb", "justification": "Area transfer 3", "refs": [3, 1, 2, 4]},
    ],
}
test_proof("area_test", test)
