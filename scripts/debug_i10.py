"""Debug theorem variable mapping for I.10 line 10 (Prop.I.9 application)."""
import json, sys, io
sys.stdout = io.TextIOWrapper(sys.stdout.buffer, encoding='utf-8')
from verifier.e_parser import parse_literal_list
from verifier.e_library import E_THEOREM_LIBRARY
from verifier.e_ast import literal_vars, substitute_literal

sort_ctx = {}

# Get Prop.I.9 theorem
thm = E_THEOREM_LIBRARY['Prop.I.9']
print("Prop.I.9 hypotheses:")
for h in thm.sequent.hypotheses:
    print(f"  {h}  vars={literal_vars(h)}")
print("Prop.I.9 conclusions:")
for c in thm.sequent.conclusions:
    print(f"  {c}  vars={literal_vars(c)}")

# The step at line 10 says:
# [Prop.I.9] refs=[6, 7, 4, 8, 9]
# -> ∠ace = ∠bce, same-side(e, b, M), same-side(e, a, N)
step_stmt = "∠ace = ∠bce, same-side(e, b, M), same-side(e, a, N)"
step_lits = parse_literal_list(step_stmt, sort_ctx)
print(f"\nStep literals:")
for lit in step_lits:
    print(f"  {lit}  vars={literal_vars(lit)}")

# Now try matching
from verifier.unified_checker import _match_theorem_var_map, _try_match_literal
bindings = {}
remaining = list(step_lits)
for conc in thm.sequent.conclusions:
    for i, step_lit in enumerate(remaining):
        result = _try_match_literal(conc, step_lit, bindings)
        if result is not None:
            bindings = result
            remaining.pop(i)
            break

print(f"\nBindings after conclusion matching: {bindings}")
print(f"Remaining step lits: {remaining}")

# Now check hypotheses with these bindings
print("\nHypothesis check with bindings:")
for hyp in thm.sequent.hypotheses:
    inst = substitute_literal(hyp, bindings)
    print(f"  {hyp} -> {inst}")

# Full match
known_strs = [
    "¬(c = a)", "¬(c = b)", "ab = ac", "ab = bc", "¬(c = a)", "¬(c = b)",
    "ac = bc",
    "on(c, M)", "on(a, M)",
    "on(c, N)", "on(b, N)",
]
known = set()
for s in known_strs:
    known.update(parse_literal_list(s, sort_ctx))

var_map = _match_theorem_var_map(thm, step_lits, known=known)
print(f"\nFull var_map: {var_map}")

print("\nHypothesis instantiation with full var_map:")
for hyp in thm.sequent.hypotheses:
    inst = substitute_literal(hyp, var_map)
    in_known = inst in known
    print(f"  {hyp} -> {inst}  {'✓' if in_known else '✗'}")
