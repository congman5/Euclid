"""Diagnose I.17 Prop.I.16 var_map issue."""
import sys, time
sys.stdout.reconfigure(encoding='utf-8')

from verifier.lean_translator import translate_lean_file
from verifier.lean_parser import parse_lean_file
from verifier.proof_synthesizer import ProofSynthesizer, VarMapper
from verifier.e_library import E_THEOREM_LIBRARY, get_theorems_up_to
from verifier.e_ast import Sort, literal_vars, substitute_literal

lps = parse_lean_file('lean_reference/Prop17.lean')
t = translate_lean_file('lean_reference/Prop17.lean')
ps = ProofSynthesizer(t, lps[0])
thm = E_THEOREM_LIBRARY['Prop.I.17']
ps.thm = thm
ps.seq = thm.sequent
ps.vm = VarMapper(thm.sequent, lps[0])
ps.avail = get_theorems_up_to('Prop.I.17')

for i, lit in enumerate(thm.sequent.hypotheses):
    ps.known.add(lit)
    ps.ll[i+1] = {lit}
ps.nprem = len(thm.sequent.hypotheses)
decls = ps._build_decls()
for p in decls['points']:
    ps.sort_ctx[p] = Sort.POINT
for ln in decls['lines']:
    ps.sort_ctx[ln] = Sort.LINE
for lean_name, elib_name in ps.vm.extra_lines.items():
    pts = ps.vm.extra_line_points.get(elib_name)
    if pts:
        ps._add_let_line(elib_name, pts[0], pts[1])

# Step 9: extend_point BC b c -> d
from verifier.e_ast import On, Between, Literal
ps.known.add(Literal(On('d', 'M'), polarity=True))
ps.known.add(Literal(Between('b', 'c', 'd'), polarity=True))
ln = ps.nprem + len(ps.steps) + 1
ps.steps.append({"lineNumber": ln, "text": "...", "justification": "let-point-on-line-extend",
                  "dependencies": [], "depth": 0, "status": "?"})
ps.ll[ln] = {Literal(On('d', 'M'), polarity=True), Literal(Between('b', 'c', 'd'), polarity=True)}

print("Known facts (%d):" % len(ps.known))
for k in sorted(str(k) for k in ps.known):
    print("  ", k)

# Now test I.16 var_map
thm16 = ps.avail.get('Prop.I.16')
tac = [t2 for t2 in lps[0].tactics if t2.rule_name == 'proposition_16'][0]
print("\ntac:", tac.rule_name, tac.rule_args, "bound:", tac.bound_vars)

# Cited params
params = ps._cited_lean_params('proposition_16')
print("cited_params:", params)

# Manual check of expected map
expected = {'a': 'b', 'b': 'c', 'c': 'a', 'd': 'd', 'L': 'M'}
print("\nExpected map:", expected)
for hyp in thm16.sequent.hypotheses:
    inst = substitute_literal(hyp, expected)
    found = inst in ps.known
    print("  %s -> %s  found=%s" % (hyp, inst, found))

# Time the actual build
s = time.time()
vm = ps._build_thm_varmap(thm16, tac)
print("\nActual var_map: %s (%.1fs)" % (vm, time.time() - s))
