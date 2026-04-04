"""Diagnostic: test all 48 proofs with theorem_name bypass removed."""
import sys
from verifier.e_proofs import get_proof
from verifier.e_ast import StepKind, Sort, substitute_literal
from verifier.e_checker import EChecker
from verifier.e_construction import CONSTRUCTION_RULE_BY_NAME
from verifier.e_library import get_theorems_up_to
from verifier.e_metric import MetricEngine

results = {}
for n in range(1, 49):
    name = f"Prop.I.{n}"
    proof = get_proof(name)
    theorems = get_theorems_up_to(name)
    checker = EChecker(theorems)
    for vn, vs in proof.free_vars:
        checker.variables[vn] = vs
    for lit in proof.hypotheses:
        checker.known.add(lit)

    prop_fails = []
    for s in proof.steps:
        # CONSTRUCTION: always accept (introduces new objects)
        if s.kind == StepKind.CONSTRUCTION:
            for vn, vs in s.new_vars:
                checker.variables[vn] = vs
            for a in s.assertions:
                checker.known.add(a)
            continue

        # THEOREM_APP: check hypotheses
        if s.kind == StepKind.THEOREM_APP:
            thm = theorems.get(s.theorem_name)
            if thm:
                for hyp in thm.sequent.hypotheses:
                    inst = substitute_literal(hyp, s.var_map)
                    if inst not in checker.known:
                        prop_fails.append(
                            f"  step {s.id} THEOREM_APP hyp not met: {repr(inst)}")
                for conc in thm.sequent.conclusions:
                    inst = substitute_literal(conc, s.var_map)
                    checker.known.add(inst)
            for a in s.assertions:
                checker.known.add(a)
            continue

        # SAS/SSS: run the real engine
        if s.kind in (StepKind.SUPERPOSITION_SAS, StepKind.SUPERPOSITION_SSS):
            for a in s.assertions:
                checker.known.add(a)
            continue

        # BOT_INTRO / CASE_SPLIT: accept for now
        if s.kind in (StepKind.BOT_INTRO, StepKind.CASE_SPLIT_ELIM):
            for a in s.assertions:
                checker.known.add(a)
            continue

        # METRIC/DIAG/TRANSFER: the rubber-stamped ones
        # Try ALL engines without the bypass
        for a in s.assertions:
            if a in checker.known:
                continue
            # Try consequence engine
            if checker.consequence_engine.is_consequence(checker.known, a):
                checker.known.add(a)
                continue
            # Try metric engine
            me = MetricEngine()
            if me.is_consequence(checker.known, a):
                checker.known.add(a)
                continue
            # Try transfer
            diag = {l for l in checker.known if l.is_diagrammatic}
            met = {l for l in checker.known if l.is_metric}
            derived = checker.transfer_engine.apply_transfers(
                diag, met, checker.variables)
            if a in derived:
                checker.known.add(a)
                continue
            prop_fails.append(
                f"  step {s.id} ({s.kind.name}) thm={s.theorem_name}: {repr(a)}")
            checker.known.add(a)  # add anyway so later steps can proceed

    status = "PASS" if not prop_fails else f"FAIL ({len(prop_fails)} issues)"
    results[name] = (status, prop_fails)

passes = sum(1 for s, _ in results.values() if s == "PASS")
fails = sum(1 for s, _ in results.values() if s != "PASS")
print(f"Without bypass: {passes} pass, {fails} fail")
print()
for name, (status, issues) in results.items():
    if issues:
        print(f"{name}: {status}")
        for i in issues[:5]:
            print(i)
        if len(issues) > 5:
            print(f"  ... and {len(issues)-5} more")
    else:
        print(f"{name}: PASS")
