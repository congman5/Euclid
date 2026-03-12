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

i6 = json.loads("""{
    "name": "Prop.I.6",
    "premises": ["\\u2220abc = \\u2220acb", "\\u00ac(a = b)", "\\u00ac(a = c)", "\\u00ac(b = c)"],
    "goal": "ab = ac",
    "lines": [
        {"id": 1, "depth": 0, "statement": "\\u2220abc = \\u2220acb", "justification": "Given", "refs": []},
        {"id": 2, "depth": 0, "statement": "\\u00ac(a = b)", "justification": "Given", "refs": []},
        {"id": 3, "depth": 0, "statement": "\\u00ac(a = c)", "justification": "Given", "refs": []},
        {"id": 4, "depth": 0, "statement": "\\u00ac(b = c)", "justification": "Given", "refs": []},
        {"id": 5, "depth": 0, "statement": "on(a, M), on(b, M)", "justification": "let-line", "refs": [2]},
        {"id": 6, "depth": 1, "statement": "ac < ab", "justification": "Assume", "refs": []},
        {"id": 7, "depth": 1, "statement": "on(a, P), on(c, P)", "justification": "let-line", "refs": [3]},
        {"id": 8, "depth": 1, "statement": "bg = ac", "justification": "Prop.I.2", "refs": [7, 2, 4]},
        {"id": 9, "depth": 1, "statement": "bg < ab", "justification": "CN1 \\u2014 Transitivity", "refs": [6, 8]},
        {"id": 10, "depth": 1, "statement": "ab = ba", "justification": "M3 \\u2014 Symmetry", "refs": []},
        {"id": 11, "depth": 1, "statement": "bg < ba", "justification": "CN1 \\u2014 Transitivity", "refs": [9, 10]},
        {"id": 12, "depth": 1, "statement": "\\u00ac(b = g)", "justification": "M1 \\u2014 Zero segment", "refs": [3, 8]},
        {"id": 13, "depth": 1, "statement": "center(b, \\u03b1), on(g, \\u03b1)", "justification": "let-circle", "refs": [12]},
        {"id": 14, "depth": 1, "statement": "inside(b, \\u03b1)", "justification": "Generality 3", "refs": [13]},
        {"id": 15, "depth": 1, "statement": "\\u00ac(inside(a, \\u03b1)), \\u00ac(on(a, \\u03b1))", "justification": "Segment transfer 6", "refs": [13, 11]},
        {"id": 16, "depth": 1, "statement": "on(d, \\u03b1), on(d, M), between(b, d, a)", "justification": "let-intersection-line-circle-between", "refs": [14, 5, 15]},
        {"id": 17, "depth": 1, "statement": "bd = bg", "justification": "Segment transfer 4", "refs": [13, 16]},
        {"id": 18, "depth": 1, "statement": "bd = ac", "justification": "CN1 \\u2014 Transitivity", "refs": [17, 8]},
        {"id": 19, "depth": 1, "statement": "\\u00ac(d = b)", "justification": "Betweenness 2", "refs": [16]},
        {"id": 20, "depth": 1, "statement": "\\u00ac(d = a)", "justification": "Betweenness 3", "refs": [16]},
        {"id": 21, "depth": 1, "statement": "on(b, N), on(c, N)", "justification": "let-line", "refs": [4]},
        {"id": 22, "depth": 1, "statement": "\\u2220dba = 0", "justification": "Angle transfer 1", "refs": [5, 16]},
        {"id": 23, "depth": 1, "statement": "\\u2220dbc = \\u2220abc", "justification": "Angle transfer 4", "refs": [5, 16, 21, 22]},
        {"id": 24, "depth": 1, "statement": "\\u2220dbc = \\u2220acb", "justification": "CN1 \\u2014 Transitivity", "refs": [23, 1]},
        {"id": 25, "depth": 1, "statement": "bc = cb", "justification": "M3 \\u2014 Symmetry", "refs": []},
        {"id": 26, "depth": 1, "statement": "bd = ca", "justification": "M3 \\u2014 Symmetry", "refs": [18]},
        {"id": 27, "depth": 1, "statement": "dc = ab, \\u2220bdc = \\u2220cab, \\u2220bcd = \\u2220cba, \\u25b3dbc = \\u25b3acb", "justification": "SAS-elim", "refs": [26, 24, 25]},
        {"id": 28, "depth": 1, "statement": "\\u25b3acb = \\u25b3abc", "justification": "M8 \\u2014 Area symmetry", "refs": []},
        {"id": 29, "depth": 1, "statement": "\\u25b3dbc = \\u25b3abc", "justification": "CN1 \\u2014 Transitivity", "refs": [27, 28]},
        {"id": 30, "depth": 1, "statement": "(\\u25b3adc + \\u25b3cdb) = \\u25b3acb", "justification": "Area transfer 3", "refs": [16, 5]},
        {"id": 31, "depth": 1, "statement": "\\u25b3cdb < \\u25b3acb", "justification": "CN5 \\u2014 Whole > Part", "refs": [30]},
        {"id": 32, "depth": 1, "statement": "\\u25b3dbc = \\u25b3cdb", "justification": "M8 \\u2014 Area symmetry", "refs": []},
        {"id": 33, "depth": 1, "statement": "\\u25b3dbc < \\u25b3acb", "justification": "CN1 \\u2014 Transitivity", "refs": [32, 31]},
        {"id": 34, "depth": 1, "statement": "\\u25b3dbc < \\u25b3abc", "justification": "CN1 \\u2014 Transitivity", "refs": [33, 28]},
        {"id": 35, "depth": 1, "statement": "\\u22a5", "justification": "\\u22a5-intro", "refs": [29, 34]},
        {"id": 36, "depth": 0, "statement": "\\u00ac(ac < ab)", "justification": "\\u22a5-elim", "refs": [6]},
        {"id": 37, "depth": 1, "statement": "ab < ac", "justification": "Assume", "refs": []},
        {"id": 38, "depth": 1, "statement": "on(c, Q), on(a, Q)", "justification": "let-line", "refs": [3]},
        {"id": 39, "depth": 1, "statement": "ch = ab", "justification": "Prop.I.2", "refs": [5, 3, 4]},
        {"id": 40, "depth": 1, "statement": "ch < ac", "justification": "CN1 \\u2014 Transitivity", "refs": [37, 39]},
        {"id": 41, "depth": 1, "statement": "ac = ca", "justification": "M3 \\u2014 Symmetry", "refs": []},
        {"id": 42, "depth": 1, "statement": "ch < ca", "justification": "CN1 \\u2014 Transitivity", "refs": [40, 41]},
        {"id": 43, "depth": 1, "statement": "\\u00ac(c = h)", "justification": "M1 \\u2014 Zero segment", "refs": [2, 39]},
        {"id": 44, "depth": 1, "statement": "center(c, \\u03b2), on(h, \\u03b2)", "justification": "let-circle", "refs": [43]},
        {"id": 45, "depth": 1, "statement": "inside(c, \\u03b2)", "justification": "Generality 3", "refs": [44]},
        {"id": 46, "depth": 1, "statement": "\\u00ac(inside(a, \\u03b2)), \\u00ac(on(a, \\u03b2))", "justification": "Segment transfer 6", "refs": [44, 42]},
        {"id": 47, "depth": 1, "statement": "on(d2, \\u03b2), on(d2, Q), between(c, d2, a)", "justification": "let-intersection-line-circle-between", "refs": [45, 38, 46]},
        {"id": 48, "depth": 1, "statement": "cd2 = ch", "justification": "Segment transfer 4", "refs": [44, 47]},
        {"id": 49, "depth": 1, "statement": "cd2 = ab", "justification": "CN1 \\u2014 Transitivity", "refs": [48, 39]},
        {"id": 50, "depth": 1, "statement": "cd2 = ba", "justification": "M3 \\u2014 Symmetry", "refs": [49]},
        {"id": 51, "depth": 1, "statement": "\\u2220d2ca = 0", "justification": "Angle transfer 1", "refs": [38, 47]},
        {"id": 52, "depth": 1, "statement": "on(b, N2), on(c, N2)", "justification": "let-line", "refs": [4]},
        {"id": 53, "depth": 1, "statement": "\\u2220d2cb = \\u2220acb", "justification": "Angle transfer 4", "refs": [38, 47, 52, 51]},
        {"id": 54, "depth": 1, "statement": "\\u2220d2cb = \\u2220abc", "justification": "CN1 \\u2014 Transitivity", "refs": [53, 1]},
        {"id": 55, "depth": 1, "statement": "cb = bc", "justification": "M3 \\u2014 Symmetry", "refs": []},
        {"id": 56, "depth": 1, "statement": "d2b = ac, \\u2220cd2b = \\u2220bac, \\u2220cbd2 = \\u2220bca, \\u25b3d2cb = \\u25b3abc", "justification": "SAS-elim", "refs": [50, 54, 55]},
        {"id": 57, "depth": 1, "statement": "(\\u25b3ad2c + \\u25b3cd2b) = \\u25b3acb", "justification": "Area transfer 3", "refs": [47, 38]},
        {"id": 58, "depth": 1, "statement": "\\u25b3cd2b < \\u25b3acb", "justification": "CN5 \\u2014 Whole > Part", "refs": [57]},
        {"id": 59, "depth": 1, "statement": "\\u25b3d2cb = \\u25b3cd2b", "justification": "M8 \\u2014 Area symmetry", "refs": []},
        {"id": 60, "depth": 1, "statement": "\\u25b3d2cb < \\u25b3acb", "justification": "CN1 \\u2014 Transitivity", "refs": [59, 58]},
        {"id": 61, "depth": 1, "statement": "\\u25b3acb = \\u25b3abc", "justification": "M8 \\u2014 Area symmetry", "refs": []},
        {"id": 62, "depth": 1, "statement": "\\u25b3d2cb = \\u25b3acb", "justification": "CN1 \\u2014 Transitivity", "refs": [56, 61]},
        {"id": 63, "depth": 1, "statement": "\\u22a5", "justification": "\\u22a5-intro", "refs": [62, 60]},
        {"id": 64, "depth": 0, "statement": "\\u00ac(ab < ac)", "justification": "\\u22a5-elim", "refs": [37]},
        {"id": 65, "depth": 0, "statement": "ab = ac", "justification": "< trichotomy", "refs": [36, 64]}
    ]
}""")

test_proof("I.6", i6)
