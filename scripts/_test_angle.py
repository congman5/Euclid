"""Test angle derivation approach for I.6 line 12."""
import json, sys, io
sys.stdout = io.TextIOWrapper(sys.stdout.buffer, encoding='utf-8')
from verifier.unified_checker import verify_e_proof_json

# Simplified test: can we derive angle dbc = angle abc from the between condition?
test = {
    "name": "test_angle",
    "premises": ["on(a, M)", "on(b, M)", "¬(a = b)", "¬(b = c)", "on(b, N)", "on(c, N)",
                 "between(a, d, b)", "¬(d = a)", "¬(d = b)", "on(d, M)"],
    "goal": "∠dbc = ∠abc",
    "lines": [
        {"id": 1, "depth": 0, "statement": "on(a, M)", "justification": "Given", "refs": []},
        {"id": 2, "depth": 0, "statement": "on(b, M)", "justification": "Given", "refs": []},
        {"id": 3, "depth": 0, "statement": "¬(a = b)", "justification": "Given", "refs": []},
        {"id": 4, "depth": 0, "statement": "¬(b = c)", "justification": "Given", "refs": []},
        {"id": 5, "depth": 0, "statement": "on(b, N)", "justification": "Given", "refs": []},
        {"id": 6, "depth": 0, "statement": "on(c, N)", "justification": "Given", "refs": []},
        {"id": 7, "depth": 0, "statement": "between(a, d, b)", "justification": "Given", "refs": []},
        {"id": 8, "depth": 0, "statement": "¬(d = a)", "justification": "Given", "refs": []},
        {"id": 9, "depth": 0, "statement": "¬(d = b)", "justification": "Given", "refs": []},
        {"id": 10, "depth": 0, "statement": "on(d, M)", "justification": "Given", "refs": []},
        # Step: ∠dba = 0 via Angle transfer 1 (collinear zero angle)
        # on(d,M) ∧ on(b,M) ∧ on(a,M) → ∠dba = 0 ∨ between(d,b,a)
        # We know ¬between(d,b,a) from between(a,d,b) + B7
        {"id": 11, "depth": 0, "statement": "∠dba = 0", "justification": "Angle transfer 1", "refs": [2, 10, 1, 7]},
        # Now use the fact that ∠abc = ∠abd + ∠dbc via angle addition
        # But ∠abd = ∠dba by M4, so ∠abd = 0
        # Therefore ∠abc = 0 + ∠dbc = ∠dbc
        {"id": 12, "depth": 0, "statement": "∠dbc = ∠abc", "justification": "Angle transfer 4", "refs": [2, 10, 1, 5, 6, 7, 11]},
    ],
}

r = verify_e_proof_json(test)
print("Test angle:", "PASS" if r.accepted else "FAIL")
if not r.accepted:
    for k, v in r.line_results.items():
        if not v.valid:
            print(f"  line {k}: {v.errors}")
    for e in r.errors:
        print(f"  GOAL: {e}")
