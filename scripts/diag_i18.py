"""Debug I.18 Prop.I.3 var_map."""
import sys
sys.stdout.reconfigure(encoding='utf-8')

from verifier.lean_translator import translate_lean_file
from verifier.lean_parser import parse_lean_file
from verifier.proof_synthesizer import ProofSynthesizer, VarMapper
from verifier.e_ast import Sort, substitute_literal
from verifier.lean_to_euclid_json import literal_to_text, _extract_declarations

tr = translate_lean_file('lean_reference/Prop18.lean')
lps = parse_lean_file('lean_reference/Prop18.lean')
ps = ProofSynthesizer(tr, lps[0])
ps.vm = VarMapper(ps.seq, lps[0]) if lps[0] else None

for i, lit in enumerate(ps.seq.hypotheses):
    ps.known.add(lit)
    ps.ll[i + 1] = {lit}
ps.nprem = len(ps.seq.hypotheses)
decls = ps._build_decls()
for p in decls['points']:
    ps.sort_ctx[p] = Sort.POINT
for ln in decls['lines']:
    ps.sort_ctx[ln] = Sort.LINE
if ps.vm:
    for lean_name, elib_name in ps.vm.extra_lines.items():
        pts = ps.vm.extra_line_points.get(elib_name)
        if pts:
            ps._add_let_line(elib_name, pts[0], pts[1])

# I.3 tactic
tac = lps[0].tactics[1]
print(f'tac: {tac.rule_name} {tac.rule_args} bound: {tac.bound_vars}')

# VarMapper info
print(f'vm.lean_to_elib: {ps.vm.lean_to_elib}')

thm3 = ps.avail.get('Prop.I.3')
vm = ps._build_thm_varmap(thm3, tac)
print(f'var_map: {vm}')

print('\nI.3 conclusions with this var_map:')
for c in thm3.sequent.conclusions:
    inst = substitute_literal(c, vm)
    print(f'  {c} -> {inst} = {literal_to_text(inst)}')

print('\nI.3 hypotheses check:')
for h in thm3.sequent.hypotheses:
    inst = substitute_literal(h, vm)
    in_known = inst in ps.known
    print(f'  {h} -> {inst} in_known={in_known}')

print('\nKnown facts:')
for k in sorted(str(x) for x in ps.known):
    print(f'  {k}')
