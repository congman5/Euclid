"""Debug transfer engine for I.9 line 22: ∠bae = ∠cae."""
import json, sys, io
sys.stdout = io.TextIOWrapper(sys.stdout.buffer, encoding='utf-8')
from verifier.unified_checker import verify_e_proof_json, EChecker
from verifier.e_parser import parse_literal_list
from verifier.e_ast import (Sort, Literal, SameSide, On, Between, Equals, 
                             AngleTerm, Center, Inside, SegmentTerm, AreaTerm)
from verifier.e_transfer import TransferEngine
from verifier.e_consequence import ConsequenceEngine
from verifier.e_axioms import ALL_DIAGRAMMATIC_AXIOMS, ALL_TRANSFER_AXIOMS

sort_ctx = {}

# Build up the known set as the checker would have it at line 22
# (all lines 1-21 pass, so their conclusions are in known)
known_strs = [
    # Premises (lines 1-9)
    "¬(a = b)", "¬(a = c)", "¬(b = c)",
    "on(a, M)", "on(b, M)", "on(a, N)", "on(c, N)",
    "same-side(c, b, M)", "same-side(b, c, N)",
    # Line 10: let-circle
    "center(a, α)", "on(b, α)",
    # Line 11
    "inside(a, α)",
    # Line 12 (let-point-on-line constructs d)
    "on(d, α)", "on(d, N)",
    # Line 13: Segment transfer 4
    "ad = ab",
    # Line 14 (let-point-on-line constructs f)
    "on(f, α)", "on(f, M)",
    # Line 15: Segment transfer 4
    "af = ab",
    # Line 16: CN1
    "ad = af",
    # Line 17: Generality 1
    "¬(d = f)",
    # Line 18: Prop.I.1 on d,f
    "df = de", "df = fe", "¬(e = d)", "¬(e = f)",
    # Line 19: CN1
    "de = fe",
    # Line 20: CN4
    "ae = ae",
    # Line 21: SSS-elim
    "∠dae = ∠fae", "∠ade = ∠afe", "∠aed = ∠aef", "△ade = △afe",
]

known = set()
for s in known_strs:
    known.update(parse_literal_list(s, sort_ctx))

variables = {
    'a': Sort.POINT, 'b': Sort.POINT, 'c': Sort.POINT,
    'd': Sort.POINT, 'e': Sort.POINT, 'f': Sort.POINT,
    'M': Sort.LINE, 'N': Sort.LINE,
    'α': Sort.CIRCLE,
}

# First compute diagrammatic closure
diag_engine = ConsequenceEngine(ALL_DIAGRAMMATIC_AXIOMS)
closure = diag_engine.direct_consequences(known, variables)
known.update(closure)

# Check key facts
print("Key diagrammatic facts:")
for fact_str in ["¬(between(a, b, f))", "¬(between(a, f, b))", 
                 "¬(between(a, c, d))", "¬(between(a, d, c))",
                 "¬(on(e, M))", "¬(on(e, N))",
                 "¬(a = d)", "¬(a = f)", "¬(a = e)",
                 "same-side(e, b, M)", "same-side(e, c, N)",
                 "same-side(e, c, M)", "same-side(e, b, N)"]:
    lits = parse_literal_list(fact_str, sort_ctx)
    for lit in lits:
        print(f"  {lit}: {'✓' if lit in known else '✗'}")

# Now run transfer engine
diagram_known = {l for l in known if l.is_diagrammatic}
metric_known = {l for l in known if l.is_metric}
transfer = TransferEngine()
derived = transfer.apply_transfers(diagram_known, metric_known, variables)

print(f"\nTransfer derived {len(derived)} facts")
# Look for angle equalities
angle_facts = [l for l in derived if isinstance(l.atom, Equals) 
               and (isinstance(l.atom.left, AngleTerm) or isinstance(l.atom.right, AngleTerm))]
print("Angle facts derived by transfer:")
for f in sorted(angle_facts, key=str):
    print(f"  {f}")

# Check the specific query
query_str = "∠bae = ∠cae"
query_lits = parse_literal_list(query_str, sort_ctx)
for q in query_lits:
    print(f"\n{q}: {'✓ DERIVED' if q in derived or q in known else '✗ NOT DERIVED'}")
