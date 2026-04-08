"""Trace _match_theorem_var_map for a proposition."""
import sys, time
sys.stdout.reconfigure(encoding='utf-8')

import verifier.unified_checker as uc
from verifier.e_ast import literal_vars, substitute_literal, Equals

def patched_match(thm, step_lits, known=None, checker=None):
    """Full re-implementation with tracing for Prop.I.16."""
    trace = thm.name in ('Prop.I.16', 'Prop.I.13')

    bindings = {}
    remaining = list(step_lits)
    for conc in thm.sequent.conclusions:
        for i, step_lit in enumerate(remaining):
            result = uc._try_match_literal(conc, step_lit, bindings)
            if result is not None:
                bindings = result
                remaining.pop(i)
                break

    if trace:
        print('  [%s] After conclusion matching: %s' % (thm.name, bindings))

    if known is not None:
        conc_vars = set()
        for conc in thm.sequent.conclusions:
            conc_vars |= literal_vars(conc)

        all_hyp_vars = set()
        for hyp in thm.sequent.hypotheses:
            all_hyp_vars |= literal_vars(hyp)
        unbound_vars = all_hyp_vars - set(bindings.keys())

        if trace:
            print('  [%s] unbound_vars: %s' % (thm.name, unbound_vars))

        if unbound_vars:
            # Try identity
            identity = dict(bindings)
            for v in unbound_vars:
                identity[v] = v
            all_met = True
            for hyp in thm.sequent.hypotheses:
                inst = substitute_literal(hyp, identity)
                if inst not in known:
                    if trace:
                        print('  [%s] Identity FAIL: %s -> %s not in known' % (thm.name, hyp, inst))
                    all_met = False
                    break
            if all_met:
                if trace:
                    print('  [%s] Identity SUCCESS' % thm.name)
                return identity

            # Backtracking
            hyps_needing_bind = []
            for hyp in thm.sequent.hypotheses:
                hyp_vars = literal_vars(hyp)
                if hyp_vars - set(bindings.keys()) - conc_vars:
                    hyps_needing_bind.append(hyp)

            if trace:
                print('  [%s] hyps_needing_bind: %s' % (thm.name, hyps_needing_bind))

            def _validate(candidate):
                for h in thm.sequent.hypotheses:
                    inst = substitute_literal(h, candidate)
                    if (not inst.polarity and isinstance(inst.atom, Equals)
                            and isinstance(inst.atom.left, str)
                            and inst.atom.left == inst.atom.right):
                        continue
                    if inst not in known:
                        inst_vars = literal_vars(inst)
                        fully_bound = all(v in candidate.values() for v in inst_vars)
                        if fully_bound:
                            if inst.is_metric:
                                continue
                            if inst.is_diagrammatic and checker is not None:
                                if checker.consequence_engine.is_consequence(known, inst):
                                    continue
                            if trace:
                                print('  [%s] Validate FAIL: %s -> %s' % (thm.name, h, inst))
                            return False
                return True

            def _backtrack(idx, current):
                if idx >= len(hyps_needing_bind):
                    return current if _validate(current) else None
                hyp = hyps_needing_bind[idx]
                hyp_vars = literal_vars(hyp)
                unbound = hyp_vars - set(current.keys()) - conc_vars
                if not unbound:
                    return _backtrack(idx + 1, current)

                found_any = False
                for kf in known:
                    candidate = uc._try_match_literal(hyp, kf, current)
                    if candidate is not None:
                        found_any = True
                        if trace:
                            print('  [%s] bt[%d] hyp=%s matched kf=%s -> %s' % (thm.name, idx, hyp, kf, candidate))
                        result = _backtrack(idx + 1, candidate)
                        if result is not None:
                            return result
                if not found_any and trace:
                    print('  [%s] bt[%d] hyp=%s NO MATCHES found, skipping' % (thm.name, idx, hyp))
                return _backtrack(idx + 1, current)

            if hyps_needing_bind:
                result = _backtrack(0, dict(bindings))
                if result is not None:
                    bindings = result
                elif trace:
                    print('  [%s] Backtracking FAILED' % thm.name)

    return bindings

uc._match_theorem_var_map = patched_match

from verifier.lean_translator import translate_lean_file
from verifier.lean_parser import parse_lean_file
from verifier.proof_synthesizer import synthesize_and_verify

prop_num = int(sys.argv[1]) if len(sys.argv) > 1 else 17
f = 'lean_reference/Prop%d.lean' % prop_num
tr = translate_lean_file(f)
lps = parse_lean_file(f)
lp = lps[0] if lps else None
sr, vr = synthesize_and_verify(tr, lp)
accepted = vr.accepted if vr else None
n_fail = sum(1 for lr in vr.line_results.values() if not lr.valid) if vr else 0
n_total = len(vr.line_results) if vr else 0
print('I.%d: verified=%s fails=%d/%d' % (prop_num, accepted, n_fail, n_total))
if vr and not vr.accepted:
    for lid, lr in sorted(vr.line_results.items()):
        if not lr.valid:
            msg = lr.errors[0][:100] if lr.errors else 'unknown'
            print('  L%d: %s' % (lid, msg))
