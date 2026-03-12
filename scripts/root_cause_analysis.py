"""
Systematic root-cause analysis of all 8 failing proofs.
For each failing line, determine: is this a VERIFIER bug or a PROOF bug?

VERIFIER bug = the proof step is mathematically correct and uses a
  justification the verifier should accept, but the verifier rejects it.

PROOF bug = the proof step is genuinely wrong or incomplete — it claims
  something that doesn't follow from the cited justification and refs.
"""
import json, sys, io
sys.stdout = io.TextIOWrapper(sys.stdout.buffer, encoding='utf-8')

# Manual classification based on the detailed failure analysis:

analysis = {
    "Prop.I.11": {
        "summary": "Proof uses 'Metric' for construction steps (ad=ab from ¬(a=b))",
        "lines": {
            4: ("PROOF", "ad=ab is a CONSTRUCTION (circle + intersect), not metric derivation"),
            5: ("PROOF", "Cascades from line 4: ¬(d=b) not known because d doesn't exist"),
            6: ("PROOF", "Cascades: ∠baf=right-angle needs SSS/SAS, not bare Metric"),
            7: ("PROOF", "Cascades"),
            8: ("PROOF", "Cascades"),
        },
        "fix": "REWRITE PROOF with explicit constructions"
    },
    "Prop.I.13": {
        "summary": "Proof uses 'Metric' for angle sum = 2·right-angle",
        "lines": {
            7: ("VERIFIER", "∠abd+∠dbc = right+right is a TRANSFER axiom consequence (DA3+DA2), not pure metric"),
        },
        "fix": "FIX VERIFIER: Metric step should try transfer engine as fallback, OR change proof justification"
    },
    "Prop.I.15": {
        "summary": "Theorem hypothesis mismatch + metric cascade",
        "lines": {
            11: ("VERIFIER", "Prop.I.13 var mapping fails: maps theorem's 'c' to proof's 'c' but I.13 needs on(c,L) where c=line endpoint, not the crossing line's point. Variable mapper picks wrong binding."),
            12: ("PROOF", "Cascades from 11"),
        },
        "fix": "FIX VERIFIER: theorem var mapper needs to try all valid bindings, not just first match"
    },
    "Prop.I.16": {
        "summary": "Theorem hypothesis mismatch + bare Metric for constructions",
        "lines": {
            8: ("VERIFIER", "Prop.I.10 needs on(a,L),on(b,L),¬(a=b) but var mapper maps wrong variables"),
            9: ("PROOF", "ae=ef and between(a,e,f) are CONSTRUCTIONS, not metric"),
            10: ("PROOF", "Cascades"),
            11: ("PROOF", "Cascades"),
        },
        "fix": "FIX VERIFIER var mapper + REWRITE PROOF"
    },
    "Prop.I.9": {
        "summary": "Transfer DA4 multi-hop not working",
        "lines": {
            22: ("VERIFIER", "∠bae=∠cae via DA4 chain (b/f same ray, c/d same ray, ∠dae=∠fae known). Transfer engine can't compose DA4+DA4+CN1."),
            23: ("VERIFIER", "same-side(e,c,M) is diagrammatically derivable but consequence engine doesn't derive it (needs SS4 transitivity through same-side chains)"),
        },
        "fix": "FIX VERIFIER: transfer engine DA4 composition + consequence engine same-side derivation"
    },
    "Prop.I.10": {
        "summary": "Theorem hypothesis (same-side) not derivable + cascades",
        "lines": {
            10: ("VERIFIER", "Prop.I.9 hypothesis same-side(b,a,M) should be derivable from the triangle configuration but consequence engine can't derive it"),
            11: ("PROOF", "Cascades"),
            12: ("PROOF", "Cascades"),
            13: ("PROOF", "Cascades"),
            14: ("PROOF", "Cascades"),
        },
        "fix": "FIX VERIFIER: consequence engine same-side derivation from non-collinearity"
    },
    "Prop.I.6": {
        "summary": "Theorem var mapping + transfer DA4 + area transfer + reductio cascade",
        "lines": {
            7: ("VERIFIER", "Prop.I.3 var mapping: maps c→a causing ¬(a=a). Need smarter backtracking."),
            8: ("VERIFIER", "¬(d=a) derivable from between(a,d,b) via Betweenness 2 but consequence engine doesn't have between yet (line 7 failed)"),
            9: ("VERIFIER", "Cascades from 7"),
            10: ("VERIFIER", "on(d,M) derivable from between(a,d,b)+on(a,M)+on(b,M) via Betweenness 6, but cascades"),
            12: ("VERIFIER", "DA4 same-ray: ∠dbc=∠abc needs d,b on same ray from b... actually this is DA4 on the other vertex"),
            19: ("VERIFIER", "Area transfer (△adc+△dcb)=△adb needs DAr2a which was fixed"),
        },
        "fix": "FIX VERIFIER: theorem var mapper backtracking + transfer DA4; proof structure is OK"
    },
    "Prop.I.7": {
        "summary": "Transfer DA2 (angle decomposition) not working + reductio cascade",
        "lines": {
            14: ("VERIFIER", "DA2a: ∠bdc=(∠bda+∠adc) needs same-side facts. Transfer engine can't find the grounding."),
            15: ("VERIFIER", "Same as 14 for ∠bac"),
            16: ("VERIFIER", "Cascades from 14-15"),
            17: ("PROOF", "SAS var mapping wrong (ab=de but should be bd=ba)"),
            18: ("VERIFIER", "Cascades"),
            19: ("VERIFIER", "Cascades"),
            20: ("VERIFIER", "Cascades"),
        },
        "fix": "FIX VERIFIER: DA2a same-side grounding in transfer engine"
    },
}

verifier_bugs = 0
proof_bugs = 0
for prop, info in analysis.items():
    for lid, (kind, desc) in info["lines"].items():
        if kind == "VERIFIER":
            verifier_bugs += 1
        else:
            proof_bugs += 1

print(f"VERIFIER bugs: {verifier_bugs} lines across {len(analysis)} props")
print(f"PROOF bugs: {proof_bugs} lines across {len(analysis)} props")
print()

# Group by verifier fix needed
fixes = {}
for prop, info in analysis.items():
    fix = info["fix"]
    fixes.setdefault(fix, []).append(prop)

print("FIXES NEEDED:")
print("=" * 60)
for fix, props in sorted(fixes.items()):
    print(f"\n{fix}")
    for p in props:
        print(f"  {p}: {analysis[p]['summary']}")
