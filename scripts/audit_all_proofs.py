"""Full audit of all Book I proofs against the verifier."""
import json, sys, io
sys.stdout = io.TextIOWrapper(sys.stdout.buffer, encoding='utf-8')
from verifier.unified_checker import verify_e_proof_json

d = json.load(open('answer_key_book_1.json', 'r', encoding='utf-8'))

total = 0
passing = 0
failing_details = {}

for name, entry in d['propositions'].items():
    p = entry.get('verified_proof')
    if p is None:
        continue
    total += 1
    r = verify_e_proof_json(p)
    if r.accepted:
        passing += 1
    else:
        fails = []
        for k, v in r.line_results.items():
            if not v.valid:
                fails.append((k, v.errors))
        goal_errs = r.errors
        failing_details[name] = (fails, goal_errs)

print(f"Total propositions with proofs: {total}")
print(f"Passing: {passing}")
print(f"Failing: {len(failing_details)}")
print()

# Categorize failures by root cause
root_causes = {}
for name, (fails, goal_errs) in failing_details.items():
    causes = set()
    for line_id, errs in fails:
        for e in errs:
            if "Angle transfer" in e or "transfer 9" in e.lower():
                causes.add("angle_transfer")
            elif "Area transfer" in e:
                causes.add("area_transfer")
            elif "Segment transfer" in e and "not derivable" in e:
                causes.add("segment_transfer")
            elif "Theorem" in e and "hypothesis not met" in e:
                causes.add("theorem_hyp_mismatch")
            elif "SAS failed" in e or "SSS failed" in e:
                causes.add("sas_sss")
            elif "Metric assertion" in e and "not a consequence" in e:
                causes.add("metric_inference")
            elif "Diagrammatic assertion" in e and "not a direct consequence" in e:
                causes.add("diagrammatic_inference")
            elif "intro" in e or "elim" in e:
                causes.add("logic_cascade")
            elif "Construction prerequisite" in e:
                causes.add("construction_prereq")
            else:
                causes.add("other: " + e[:60])
    failing_details[name] = (fails, goal_errs, causes)

print("=" * 70)
print("FAILURE ROOT CAUSES")
print("=" * 70)
cause_counts = {}
for name, (fails, goal_errs, causes) in failing_details.items():
    for c in causes:
        cause_counts.setdefault(c, []).append(name)

for cause, props in sorted(cause_counts.items(), key=lambda x: -len(x[1])):
    print(f"\n{cause} ({len(props)} props):")
    for p in props:
        print(f"  {p}")

print()
print("=" * 70)
print("DETAILED FAILURES (first error per proposition)")
print("=" * 70)
for name, (fails, goal_errs, causes) in failing_details.items():
    print(f"\n{name} [{', '.join(sorted(causes))}]:")
    for line_id, errs in fails[:5]:
        print(f"  line {line_id}: {errs[0][:120]}")
    if len(fails) > 5:
        print(f"  ... and {len(fails)-5} more failing lines")
