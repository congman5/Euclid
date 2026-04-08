import io,sys,os
sys.stdout = io.TextIOWrapper(sys.stdout.buffer, encoding='utf-8', errors='replace')
sys.path.insert(0, '.')
from verifier.e_axiom_match import get_axiom_clause
for n in ['Generality 5','Generality 5c','Generality 5d','Generality 6','Generality 6c']:
    c = get_axiom_clause(n)
    if c:
        print(f"{n}: {c}")
        for lit in c.literals:
            print(f"  {lit} (neg={lit.is_negative})")



