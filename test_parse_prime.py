"""Check if f' variable is parsed correctly."""
from verifier.e_parser import parse_literal_list
from verifier.e_ast import Sort

ctx = {'e': Sort.POINT, "f'": Sort.POINT}
try:
    lits = parse_literal_list("¬(e = f')", ctx)
    print('parsed:', lits)
    for l in lits:
        print(f'  atom vars: {l.atom.left}, {l.atom.right}')
except Exception as ex:
    print(f'parse error: {ex}')

# Also check the unicode not
try:
    lits2 = parse_literal_list("not(e = f')", ctx)
    print('parsed2:', lits2)
except Exception as ex:
    print(f'parse error2: {ex}')
