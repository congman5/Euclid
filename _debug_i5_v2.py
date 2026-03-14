"""Debug I.5 step 5 path through approach 8."""
import json, sys
sys.path.insert(0, '.')
from verifier.e_parser import parse_literal_list
from verifier.e_ast import Literal, Equals, SegmentTerm, AngleTerm, AreaTerm
from verifier.e_metric import MetricEngine

with open('verified_proofs_book_1.json', encoding='utf-8') as f:
    vp = json.load(f)

proof = vp['Prop.I.5']
all_known = []
for prem_text in proof.get('premises', []):
    try:
        all_known.extend(parse_literal_list(prem_text))
    except Exception:
        pass
prior_step_map = {}
for ln in proof['lines']:
    if ln['id'] < 5:
        try:
            all_known.extend(parse_literal_list(ln['statement']))
        except Exception:
            pass
        prior_step_map[ln['id']] = ln['statement']

refs = [1]
ref_lits = []
for ref_num in refs:
    for ln in proof['lines']:
        if ln['id'] == ref_num:
            try:
                ref_lits.extend(parse_literal_list(ln['statement']))
            except Exception:
                pass

print("ref_lits:")
for lit in ref_lits:
    print(f"  {repr(lit)} polarity={lit.polarity} atom_type={type(lit.atom).__name__}")
    if isinstance(lit.atom, Equals):
        print(f"    left={repr(lit.atom.left)} [{type(lit.atom.left).__name__}]")
        print(f"    right={repr(lit.atom.right)} [{type(lit.atom.right).__name__}]")

ref_eqs = []
for lit in ref_lits:
    if not lit.polarity or not isinstance(lit.atom, Equals):
        print(f"  SKIPPED: polarity={lit.polarity} atom_type={type(lit.atom).__name__}")
        continue
    a = lit.atom
    if isinstance(a.left, (SegmentTerm, AngleTerm, AreaTerm)):
        ref_eqs.append((a.left, a.right))
        print(f"  ADDED: {repr(a.left)} = {repr(a.right)} [{type(a.left).__name__}]")
    else:
        print(f"  SKIPPED (not magnitude): left_type={type(a.left).__name__}")

print(f"\nref_eqs count: {len(ref_eqs)}")
print(f"multi_ref: {len(refs) >= 2 and len(ref_eqs) >= 2}")

# Check Pattern 2
print("\n--- Pattern 2 check ---")
for left, right in reversed(ref_eqs):
    print(f"  left={repr(left)} isinstance(AngleTerm)={isinstance(left, AngleTerm)}")

# Check known_texts for 'ac = ab'
known_texts = set()
for lit in all_known:
    known_texts.add(repr(lit))
for prem in proof.get('premises', []):
    known_texts.add(prem.strip())
for s_text in prior_step_map.values():
    known_texts.add(s_text.strip())

print(f"\n'ac = ab' in known_texts: {'ac = ab' in known_texts}")

# Check non_ref_eq_canons
def _term_canon(t):
    if isinstance(t, SegmentTerm):
        return ('seg', frozenset([t.p1, t.p2]))
    if isinstance(t, AngleTerm):
        return ('ang', t.p2, frozenset([t.p1, t.p3]))
    if isinstance(t, AreaTerm):
        return ('area', frozenset([t.p1, t.p2, t.p3]))
    return ('pt', t) if isinstance(t, str) else ('o', repr(t))

def _eq_canon(atom):
    return frozenset([_term_canon(atom.left), _term_canon(atom.right)])

# The swap ac = ab has canon:
swap_canon = _eq_canon(Equals(SegmentTerm('a','c'), SegmentTerm('a','b')))
print(f"swap canon: {swap_canon}")

# Check non_ref_eq_canons
non_ref_eq_canons = set()
for prem in proof.get('premises', []):
    try:
        for lit in parse_literal_list(prem):
            if isinstance(lit.atom, Equals) and lit.polarity:
                if isinstance(lit.atom.left, (SegmentTerm, AngleTerm, AreaTerm)):
                    c = _eq_canon(lit.atom)
                    non_ref_eq_canons.add(c)
                    print(f"  from premise '{prem}': canon={c}")
    except Exception:
        pass

ref_set = set(refs)
for sid, s_text in prior_step_map.items():
    if sid in ref_set:
        continue
    try:
        for lit in parse_literal_list(s_text):
            if isinstance(lit.atom, Equals) and lit.polarity:
                if isinstance(lit.atom.left, (SegmentTerm, AngleTerm, AreaTerm)):
                    c = _eq_canon(lit.atom)
                    non_ref_eq_canons.add(c)
                    print(f"  from step {sid} '{s_text}': canon={c}")
    except Exception:
        pass

print(f"\nswap_canon in non_ref_eq_canons: {swap_canon in non_ref_eq_canons}")
