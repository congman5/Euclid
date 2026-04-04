"""Quick verification of all skeleton files. Saves results to skeletons/verification_report.txt"""
import json, sys, os
sys.path.insert(0, ".")
from verifier.unified_checker import verify_e_proof_json

lines = []
summary = []
for n in range(16, 49):
    fp = f"skeletons/Prop.I.{n}.euclid"
    if not os.path.exists(fp):
        lines.append(f"I.{n}: MISSING")
        continue
    pj = json.loads(open(fp, encoding="utf-8").read())
    vr = verify_e_proof_json(pj)
    fails = {ln: r for ln, r in vr.line_results.items() if not r.valid}
    nsteps = len(vr.line_results)
    hdr = f"I.{n}: accepted={vr.accepted} steps={nsteps} fails={len(fails)}"
    lines.append(hdr)
    summary.append((n, vr.accepted, len(fails)))
    if not vr.accepted:
        for e in vr.errors:
            lines.append(f"  ERR: {e}")
        for ln, r in fails.items():
            for err in r.errors:
                lines.append(f"  L{ln}: {err}")

# Summary
lines.append("")
lines.append("=== SUMMARY ===")
passed = [n for n, a, _ in summary if a]
failed = [n for n, a, _ in summary if not a]
lines.append(f"Passed ({len(passed)}): {passed}")
lines.append(f"Failed ({len(failed)}): {failed}")

report = "\n".join(lines)
with open("skeletons/verification_report.txt", "w", encoding="utf-8") as f:
    f.write(report)
print(f"Report saved to skeletons/verification_report.txt")
print(f"Passed: {len(passed)}/{len(summary)}")
for n, a, nf in summary:
    tag = "PASS" if a else "FAIL"
    print(f"  I.{n}: {tag} (fails={nf})")
