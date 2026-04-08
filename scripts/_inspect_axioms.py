"""Inspect axiom clause structures."""
import sys
sys.stdout.reconfigure(encoding='utf-8')
sys.path.insert(0, '.')
from verifier.e_axiom_match import get_axiom_clause

axioms = [
    'Generality 3', 'Generality 6', 'Betweenness 1b', 'Betweenness 3',
    'Same-side 2', 'Pasch 3', 'CN1', 'CN5',
    'Segment transfer 3b', 'Intersection 5',
]
for name in axioms:
    c = get_axiom_clause(name)
    if c is None:
        print(f"{name}: NOT FOUND")
        continue
    print(f"\n{name}:")
    for i, lit in enumerate(c.literals):
        neg = lit.negated()
        print(f"  [{i}] {lit}  (premise if negated: {neg})")
    # Identify premises vs conclusion
    # In a clause A ∨ B ∨ ¬C ∨ ¬D, to derive A we need C and D
    # Premises = positive literals (their negation must be known)
    # + negated negative literals (they themselves must be known)
    print(f"  Total literals: {len(c.literals)}")
