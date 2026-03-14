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

test = json.loads("""{
    "name": "area_test",
    "premises": ["on(a, M)", "on(b, M)", "between(a, d, b)", "on(d, M)", "\\u00ac(a = b)", "\\u00ac(a = d)", "\\u00ac(b = d)"],
    "goal": "(\\u25b3adc + \\u25b3cdb) = \\u25b3acb",
    "lines": [
        {"id": 1, "depth": 0, "statement": "on(a, M)", "justification": "Given", "refs": []},
        {"id": 2, "depth": 0, "statement": "on(b, M)", "justification": "Given", "refs": []},
        {"id": 3, "depth": 0, "statement": "between(a, d, b)", "justification": "Given", "refs": []},
        {"id": 4, "depth": 0, "statement": "on(d, M)", "justification": "Given", "refs": []},
        {"id": 5, "depth": 0, "statement": "\\u00ac(a = b)", "justification": "Given", "refs": []},
        {"id": 6, "depth": 0, "statement": "\\u00ac(a = d)", "justification": "Given", "refs": []},
        {"id": 7, "depth": 0, "statement": "\\u00ac(b = d)", "justification": "Given", "refs": []},
        {"id": 8, "depth": 0, "statement": "(\\u25b3adc + \\u25b3cdb) = \\u25b3acb", "justification": "Area transfer 3", "refs": [1, 2, 3, 4]}
    ]
}""")
test_proof("area_test", test)
