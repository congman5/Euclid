"""Diagnose strict-dep failures: for each failing axiom line, show
what premises the axiom needs vs what the deps actually provide,
and identify specifically which required premises are missing."""
import json, sys, os, io
sys.stdout = io.TextIOWrapper(sys.stdout.buffer, encoding='utf-8', errors='replace')
sys.path.insert(0, os.path.dirname(os.path.dirname(os.path.abspath(__file__))))

from verifier.unified_checker import verify_e_proof_json
from verifier.e_axiom_match import (
    get_axiom_clause, check_specific_axiom_with_premises,
)
from verifier.e_ast import Literal, Sort, literal_vars
from verifier.e_parser import parse_literal


def _get_var_names(lit):
    try:
        return {v.name for v in literal_vars(lit)}
    except Exception:
        return set()


def diagnose(path):
    with open(path, "r", encoding="utf-8") as f:
        data = json.load(f)

    name = data.get("proposition", os.path.basename(path))
    proof = data.get("proof", data)
    premises = proof.get("premises", [])
    steps = proof.get("steps", [])

    line_lits = {}
    for i, prem_text in enumerate(premises, 1):
        lits = set()
        for part in prem_text.split(","):
            part = part.strip()
            if part:
                try:
                    lits.add(parse_literal(part))
                except Exception:
                    pass
        line_lits[i] = lits

    for step in steps:
        lid = step.get("lineNumber", step.get("line"))
        text = step.get("text", step.get("statement", ""))
        lits = set()
        for part in text.split(","):
            part = part.strip()
            if part:
                try:
                    lits.add(parse_literal(part))
                except Exception:
                    pass
        line_lits[lid] = lits

    result = verify_e_proof_json(data)

    failing_lines = sorted(lid for lid, lr in result.line_results.items() if lr.errors)
    if not failing_lines:
        print(f"{name}: OK")
        return

    print(f"\n{'='*70}")
    print(f"{name}: {len(failing_lines)} failing lines: {failing_lines}")
    print(f"{'='*70}")

    # Build variables dict from all known facts
    all_known = set()
    for lits in line_lits.values():
        all_known.update(lits)
    variables = {}
    for lit in all_known:
        for vn in _get_var_names(lit):
            if len(vn) == 1 and vn.isupper():
                variables[vn] = Sort.LINE
            else:
                variables[vn] = Sort.POINT

    for step in steps:
        lid = step.get("lineNumber", step.get("line"))
        if lid not in failing_lines:
            continue

        just = step.get("justification", step.get("rule", ""))
        deps = step.get("dependencies", step.get("deps", []))
        text = step.get("text", step.get("statement", ""))
        errors = result.line_results[lid].errors

        clause = get_axiom_clause(just)
        if clause is None:
            print(f"\n  L{lid}: {just} [{text}] deps={deps}  (not registered)")
            for e in errors:
                print(f"    ERR: {e}")
            continue

        dep_facts = set()
        for d in deps:
            dep_facts.update(line_lits.get(d, set()))

        step_lits = line_lits.get(lid, set())

        ok_strict, _, prems_strict = check_specific_axiom_with_premises(
            just, dep_facts, step_lits, variables)

        ok_all, _, prems_all = check_specific_axiom_with_premises(
            just, all_known, step_lits, variables)

        print(f"\n  L{lid}: {just} [{text}] deps={deps}")
        print(f"    strict={ok_strict}, with_all_known={ok_all}")

        if ok_all and prems_all:
            print(f"    Required premises ({len(prems_all)}):")
            for p in sorted(prems_all, key=str):
                in_deps = p in dep_facts
                tag = 'OK' if in_deps else 'MISSING'
                print(f"      {tag}: {p}")
                if not in_deps:
                    sources = [l for l, lits in line_lits.items() if p in lits]
                    if sources:
                        print(f"        -> from line(s): {sources}")
                    else:
                        print(f"        -> NOT in any line (needs new step)")
        elif not ok_all:
            print(f"    Cannot match even with ALL known facts!")
            for e in errors:
                print(f"    ERR: {e}")


if __name__ == "__main__":
    import glob
    props = sys.argv[1:] if len(sys.argv) > 1 else None
    for path in sorted(glob.glob("solved_proofs/Proposition I.*.euclid")):
        if props:
            bname = os.path.basename(path)
            num = bname.split("I.")[1].split(".euclid")[0]
            if num not in props:
                continue
        diagnose(path)
