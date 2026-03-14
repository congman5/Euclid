"""Quick test for I.7 approaches."""
import sys, os
sys.stdout.reconfigure(encoding='utf-8')
sys.path.insert(0, os.path.dirname(os.path.dirname(os.path.abspath(__file__))))

from verifier.unified_checker import verify_e_proof_json

test = {
    "name": "i7-case1",
    "declarations": {"points": [], "lines": []},
    "premises": [
        "on(b, L)", "on(c, L)", "\u00ac(b = c)",
        "same-side(a, d, L)", "bd = ba", "cd = ca",
        "same-side(c, d, N)",
    ],
    "goal": "\u2220dba = 0",
    "lines": [
        {"id": 1, "depth": 0, "statement": "on(b, L)", "justification": "Given", "refs": []},
        {"id": 2, "depth": 0, "statement": "on(c, L)", "justification": "Given", "refs": []},
        {"id": 3, "depth": 0, "statement": "\u00ac(b = c)", "justification": "Given", "refs": []},
        {"id": 4, "depth": 0, "statement": "same-side(a, d, L)", "justification": "Given", "refs": []},
        {"id": 5, "depth": 0, "statement": "bd = ba", "justification": "Given", "refs": []},
        {"id": 6, "depth": 0, "statement": "cd = ca", "justification": "Given", "refs": []},
        {"id": 7, "depth": 0, "statement": "ba = bd", "justification": "Metric", "refs": [5]},
        {"id": 8, "depth": 0, "statement": "ca = cd", "justification": "Metric", "refs": [6]},
        {"id": 9, "depth": 0, "statement": "bc = bc", "justification": "Metric", "refs": []},
        {"id": 10, "depth": 0, "statement":
            "\u2220abc = \u2220dbc, \u2220bca = \u2220bcd, "
            "\u2220bac = \u2220bdc, \u25b3abc = \u25b3dbc",
            "justification": "SSS", "refs": [7, 8, 9]},
        {"id": 11, "depth": 0, "statement": "on(b, N), on(a, N)", "justification": "let-line", "refs": [3]},
        {"id": 12, "depth": 0, "statement": "same-side(c, d, N)", "justification": "Given", "refs": []},
        {"id": 13, "depth": 0, "statement":
            "\u2220cba = (\u2220cbd + \u2220dba)",
            "justification": "Transfer", "refs": []},
        {"id": 14, "depth": 0, "statement": "\u2220dba = 0",
            "justification": "Metric", "refs": [13, 10]},
    ]
}

r = verify_e_proof_json(test)
for lid, lr in sorted(r.line_results.items()):
    if not lr.valid:
        print(f"L{lid}: FAIL {lr.errors}")
    else:
        print(f"L{lid}: OK")
print(f"Accepted: {r.accepted}")

# Debug: check what transfer derives with the full known set
from verifier.e_ast import *
from verifier.e_consequence import ConsequenceEngine
from verifier.e_transfer import TransferEngine
from verifier.e_axioms import ALL_DIAGRAMMATIC_AXIOMS, ALL_TRANSFER_AXIOMS, DIAGRAM_ANGLE_TRANSFER

known = set()
known.add(Literal(On('b','L'))); known.add(Literal(On('c','L')))
known.add(Literal(Equals('b','c'), polarity=False))
known.add(Literal(SameSide('a','d','L')))
known.add(Literal(On('b','N'))); known.add(Literal(On('a','N')))
known.add(Literal(SameSide('c','d','N')))
# Angle from SSS
known.add(Literal(Equals(AngleTerm('a','b','c'), AngleTerm('d','b','c'))))

variables = {
    'a': Sort.POINT, 'b': Sort.POINT, 'c': Sort.POINT, 'd': Sort.POINT,
    'L': Sort.LINE, 'N': Sort.LINE
}

ce = ConsequenceEngine(ALL_DIAGRAMMATIC_AXIOMS)
closure = ce.direct_consequences(known, variables)
known.update(closure)

dk = {l for l in known if l.is_diagrammatic}
mk = {l for l in known if l.is_metric}

print("\n--- Diag known ---")
for f in sorted(dk, key=str):
    s = str(f)
    if 'same-side' in s or 'on(' in s.lower():
        print(f"  {f}")

print("\n--- DA2 axiom check ---")
# DA2a schema: on(a,L), on(a,M), on(b,L), on(c,M),
#              a!=b, a!=c, not(on(d,L)), not(on(d,M)), L!=M,
#              same-side(b,d,M), same-side(c,d,L)
# Mapping: vertex=b, L_da2 -> L, M_da2 -> N
# a_da2=b, b_da2=c, c_da2=a, d_da2=d
# Check: on(b,L)=on(a_da2,L_da2) ✓
#         on(b,N)=on(a_da2,M_da2) ✓
#         on(c,L)=on(b_da2,L_da2) ✓
#         on(a,N)=on(c_da2,M_da2) ✓
#         b!=c = a_da2!=b_da2 ✓
#         b!=a = a_da2!=c_da2 ✓
#         not(on(d,L)) = not(on(d_da2,L_da2))
#         not(on(d,N)) = not(on(d_da2,M_da2))
#         L!=N = L_da2!=M_da2
#         same-side(c,d,N) = same-side(b_da2,d_da2,M_da2) ✓
#         same-side(a,d,L) = same-side(c_da2,d_da2,L_da2) ✓

print(f"  not(on(d,L)): {Literal(On('d','L'), polarity=False) in dk}")
print(f"  not(on(d,N)): {Literal(On('d','N'), polarity=False) in dk}")
print(f"  L!=N: {Literal(Equals('L','N'), polarity=False) in dk}")
print(f"  b!=a: {Literal(Equals('b','a'), polarity=False) in dk}")

# Try running transfer on just DA2
te = TransferEngine(DIAGRAM_ANGLE_TRANSFER)
derived = te.apply_transfers(dk, mk, variables)
angle_derived = [d for d in derived if 'MagAdd' in repr(d.atom) or '+' in str(d)]
print("\n--- DA2 angle-sum derivations ---")
for d in angle_derived:
    print(f"  {d}")

