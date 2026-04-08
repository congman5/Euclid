"""Inspect Lean parser output for a given prop."""
import sys
sys.stdout.reconfigure(encoding='utf-8')
sys.path.insert(0, '.')
from verifier.lean_parser import parse_lean_file

n = int(sys.argv[1]) if len(sys.argv) > 1 else 27
f = f'lean_reference/Prop{n}.lean'
lps = parse_lean_file(f)
lp = lps[0]
print(f"=== Prop {n} ===")
print(f"Goal: {lp.signature}")
print(f"Tactics: {len(lp.tactics)}")
for i, t in enumerate(lp.tactics):
    ce = getattr(t, 'case_expr', None)
    ae = getattr(t, 'assertion_expr', None)
    d = getattr(t, 'depth', '?')
    extra = ""
    if ce:
        extra += f" case_expr={ce}"
    if ae:
        extra += f" assert={ae}"
    children = None
    if children:
        extra += f" children={len(children)}"
    print(f"  [{i}] {t.kind.name} depth={d} rule={t.rule_name}{extra}")
    if children:
        for j, c in enumerate(children):
            cd = getattr(c, 'depth', '?')
            cce = getattr(c, 'case_expr', None)
            cae = getattr(c, 'assertion_expr', None)
            cextra = ""
            if cce:
                cextra += f" case_expr={cce}"
            if cae:
                cextra += f" assert={cae}"
            subchildren = getattr(c, 'children', None)
            if subchildren:
                cextra += f" children={len(subchildren)}"
            print(f"    [{j}] {c.tactic_name} depth={cd}{cextra}")
            if subchildren:
                for k, sc in enumerate(subchildren):
                    scd = getattr(sc, 'depth', '?')
                    print(f"      [{k}] {sc.tactic_name} depth={scd}")
