"""Debug DA4 matching for I.10 L31."""
import sys, json
sys.path.insert(0, '.')
sys.stdout.reconfigure(encoding='utf-8')
from verifier.e_ast import *

# Patch check_specific_axiom to print debug info
import verifier.unified_checker as uc
from verifier.e_axiom_match import check_specific_axiom as orig_fn

def debug_check(name, dep_aug, target_lits, variables):
    if name == 'Angle transfer 4':
        print(f'DA4 check: dep_aug has {len(dep_aug)} facts')
        print(f'  variables keys: {sorted(variables.keys())}')
        print(f'  neg(d=c): {Literal(Equals("d","c"), False) in dep_aug}')
        print(f'  neg(c=d): {Literal(Equals("c","d"), False) in dep_aug}')
        print(f'  neg between(a,c,a): {Literal(Between("a","c","a"), False) in dep_aug}')
        print(f'  neg between(e,c,d): {Literal(Between("e","c","d"), False) in dep_aug}')
        print(f'  on(c,M): {Literal(On("c","M"), True) in dep_aug}')
        print(f'  on(a,M): {Literal(On("a","M"), True) in dep_aug}')
        print(f'  on(d,K): {Literal(On("d","K"), True) in dep_aug}')
        print(f'  on(e,K): {Literal(On("e","K"), True) in dep_aug}')
        print(f'  on(c,K): {Literal(On("c","K"), True) in dep_aug}')
        # Count diag/metric
        ndiag = sum(1 for l in dep_aug if l.is_diagrammatic)
        nmet = sum(1 for l in dep_aug if l.is_metric)
        print(f'  diag={ndiag}, metric={nmet}')
    return orig_fn(name, dep_aug, target_lits, variables)

uc.check_specific_axiom = debug_check

data = json.load(open('solved_proofs/Proposition I.10.euclid', encoding='utf-8'))
proof = data['proof']
premises = proof.get('premises', [])
lines = []
for i, prem in enumerate(premises, start=1):
    lines.append({'id': i, 'depth': 0, 'statement': prem, 'justification': 'Given', 'refs': []})
for step in proof.get('steps', []):
    lines.append({'id': step['lineNumber'], 'depth': step.get('depth',0),
                  'statement': step['text'], 'justification': step['justification'],
                  'refs': step.get('dependencies',[])})
pj = {'name': proof.get('name'), 'declarations': proof.get('declarations',{}),
      'premises': premises, 'goal': proof.get('goal',''), 'lines': lines}
result = uc.verify_e_proof_json(pj)
bad = [lid for lid,lr in result.line_results.items() if not lr.valid]
print(f'Accepted: {result.accepted}, bad={bad}')
