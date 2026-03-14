"""Test _autofill_metric (6th iteration) against all Metric steps."""
import json, sys, os
sys.path.insert(0, '.')

from verifier.e_parser import parse_literal_list
from verifier.e_ast import Literal, Equals, SegmentTerm, AngleTerm, AreaTerm
from verifier.e_metric import MetricEngine
from itertools import permutations

with open('verified_proofs_book_1.json', encoding='utf-8') as f:
    vp = json.load(f)

_AUTOFILL_FAIL = 'FAIL'


def _variants(t):
    out = [t]
    if isinstance(t, SegmentTerm):
        out.append(SegmentTerm(t.p2, t.p1))
    elif isinstance(t, AngleTerm):
        out.append(AngleTerm(t.p3, t.p2, t.p1))
    elif isinstance(t, AreaTerm):
        out.append(AreaTerm(t.p3, t.p1, t.p2))
        out.append(AreaTerm(t.p1, t.p3, t.p2))
    return out


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


def autofill_metric(step_refs, ref_lits, all_known, premises, prior_steps):
    known_set = set(all_known)
    known_texts = set()
    for lit in all_known:
        known_texts.add(repr(lit))
    for prem in premises:
        known_texts.add(prem.strip())
    for s_text in prior_steps:
        known_texts.add(s_text.strip())

    known_eq_canons = set()
    known_diseq_canons = set()
    for lit in all_known:
        if isinstance(lit.atom, Equals):
            c = _eq_canon(lit.atom)
            if lit.polarity:
                known_eq_canons.add(c)
            else:
                known_diseq_canons.add(c)

    engine = MetricEngine()
    engine.process_literals(known_set)

    ref_eqs = []
    for lit in ref_lits:
        if not lit.polarity or not isinstance(lit.atom, Equals):
            continue
        a = lit.atom
        if isinstance(a.left, (SegmentTerm, AngleTerm, AreaTerm)):
            ref_eqs.append((a.left, a.right))

    for left, right in ref_eqs:
        for t in _variants(left) + _variants(right):
            engine.state.add_term(t)
    engine._apply_rules()

    seen = set()
    multi_ref = len(ref_eqs) >= 2 and len(step_refs) >= 2

    # PHASE 1
    if not multi_ref:
        phase1_swaps = []
        phase1_angles = []
        for left, right in ref_eqs:
            lv = _variants(left)
            rv = _variants(right)
            lit = Literal(Equals(right, left))
            text = repr(lit)
            if text not in known_texts and text not in seen:
                seen.add(text)
                bucket = (phase1_angles
                          if isinstance(left, (AngleTerm, AreaTerm))
                          else phase1_swaps)
                bucket.append(text)
            if isinstance(left, (AngleTerm, AreaTerm)):
                for vi in range(1, min(len(lv), len(rv))):
                    for a, b in [(lv[vi], rv[vi]), (rv[vi], lv[vi])]:
                        lit = Literal(Equals(a, b))
                        text = repr(lit)
                        if text not in known_texts and text not in seen:
                            seen.add(text)
                            phase1_angles.append(text)
        phase1 = phase1_angles if phase1_angles else phase1_swaps
        if phase1:
            return ', '.join(phase1[:4])

    # PHASE 2
    phase2 = []
    if len(ref_eqs) >= 2:
        endpoint_terms = []
        ep_reprs = set()
        for left, right in ref_eqs:
            for t in _variants(left) + _variants(right):
                r = repr(t)
                if r not in ep_reprs:
                    ep_reprs.add(r)
                    endpoint_terms.append(t)
        for i, t1 in enumerate(endpoint_terms):
            for t2 in endpoint_terms[i + 1:]:
                if not engine.state.are_equal(t1, t2):
                    continue
                for a, b in [(t1, t2), (t2, t1)]:
                    lit = Literal(Equals(a, b))
                    text = repr(lit)
                    if text in known_texts or text in seen:
                        continue
                    canon = _eq_canon(lit.atom)
                    if canon in known_eq_canons:
                        continue
                    seen.add(text)
                    phase2.append((text, lit, 30))

    # M1 disequality
    ref_seg_points = set()
    for left, right in ref_eqs:
        for t in [left, right]:
            if isinstance(t, SegmentTerm) and t.p1 != t.p2:
                ref_seg_points.add((t.p1, t.p2))
                ref_seg_points.add((t.p2, t.p1))
    for p, q in ref_seg_points:
        lit = Literal(Equals(p, q), polarity=False)
        text = repr(lit)
        if text in known_texts or text in seen:
            continue
        canon = _eq_canon(lit.atom)
        if canon in known_diseq_canons:
            continue
        if engine._check_literal(lit):
            seen.add(text)
            phase2.append((text, lit, 20))

    # Angle consequences
    ref_points = set()
    for left, right in ref_eqs:
        for t in [left, right]:
            if isinstance(t, SegmentTerm):
                ref_points.add(t.p1)
                ref_points.add(t.p2)
            elif isinstance(t, AngleTerm):
                ref_points.update([t.p1, t.p2, t.p3])
    if len(ref_points) >= 3:
        angle_terms = []
        angle_reprs = set()
        for perm in permutations(sorted(ref_points), 3):
            at = AngleTerm(perm[0], perm[1], perm[2])
            r = repr(at)
            if r not in angle_reprs:
                angle_reprs.add(r)
                angle_terms.append(at)
                engine.state.add_term(at)
        engine._apply_rules()
        for i, a1 in enumerate(angle_terms):
            for a2 in angle_terms[i + 1:]:
                if not engine.state.are_equal(a1, a2):
                    continue
                if (a1.p2 == a2.p2
                        and {a1.p1, a1.p3} == {a2.p1, a2.p3}):
                    continue
                for left, right in [(a1, a2), (a2, a1)]:
                    lit = Literal(Equals(left, right))
                    text = repr(lit)
                    if text in known_texts or text in seen:
                        continue
                    canon = _eq_canon(lit.atom)
                    if canon in known_eq_canons:
                        continue
                    seen.add(text)
                    phase2.append((text, lit, 10))

    if phase2:
        phase2.sort(key=lambda c: c[2], reverse=True)
        top = phase2[0][2]
        selected = [t for t, _, p in phase2 if p == top][:4]
        return ', '.join(selected)

    return _AUTOFILL_FAIL


# Run tests
test_cases = [
    ('Prop.I.1', 10, 'ab = ac'),
    ('Prop.I.1', 11, 'ab = bc'),
    ('Prop.I.1', 12, '\u00ac(c = a)'),
    ('Prop.I.1', 13, '\u00ac(c = b)'),
    ('Prop.I.4', 5, '\u2220bca = \u2220efd'),
    ('Prop.I.5', 5, 'ac = ab'),
    ('Prop.I.5', 6, '\u2220bac = \u2220cab'),
    ('Prop.I.8', 5, '\u2220bca = \u2220efd'),
]

for prop_name, step_num, expected in test_cases:
    proof = vp[prop_name]
    all_known = []
    for prem_text in proof.get('premises', []):
        try:
            all_known.extend(parse_literal_list(prem_text))
        except Exception:
            pass
    prior_texts = []
    for ln in proof['lines']:
        if ln['id'] < step_num:
            try:
                all_known.extend(parse_literal_list(ln['statement']))
            except Exception:
                pass
            prior_texts.append(ln['statement'])
    cur_line = [ln for ln in proof['lines'] if ln['id'] == step_num][0]
    refs = cur_line.get('refs', [])
    ref_lits = []
    for ref_num in refs:
        for ln in proof['lines']:
            if ln['id'] == ref_num:
                try:
                    ref_lits.extend(parse_literal_list(ln['statement']))
                except Exception:
                    pass
    try:
        result = autofill_metric(
            refs, ref_lits, all_known,
            proof.get('premises', []), prior_texts)
        ok = (result == expected)
        mark = 'OK' if ok else 'FAIL'
        print(f'[{mark}] {prop_name} step {step_num}: got [{result}] expected [{expected}]')
    except Exception as e:
        import traceback
        print(f'[ERROR] {prop_name} step {step_num}: {e}')
        traceback.print_exc()
