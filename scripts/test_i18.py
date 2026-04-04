"""Test I.18 synthesis after var_map fix."""
import sys
sys.stdout.reconfigure(encoding='utf-8')
from verifier.lean_translator import translate_lean_file
from verifier.lean_parser import parse_lean_file
from verifier.proof_synthesizer import synthesize_and_verify

tr = translate_lean_file('lean_reference/Prop18.lean')
lps = parse_lean_file('lean_reference/Prop18.lean')
sr, vr = synthesize_and_verify(tr, lps[0])
print(f"success: {sr.success}, steps: {sr.step_count}")
print(f"warnings: {sr.warnings}")
print(f"accepted: {vr.accepted if vr else 'N/A'}")
if vr:
    for lid, lr in sorted(vr.line_results.items()):
        if not lr.valid:
            print(f"  L{lid}: FAIL  {lr.errors}")
