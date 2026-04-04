"""Debug theorem deps for a specific proposition and step."""
import sys, os
os.environ.setdefault("PYTHONHASHSEED", "0")
sys.path.insert(0, ".")
sys.stdout.reconfigure(encoding='utf-8')

from verifier.lean_translator import translate_lean_file
from verifier.lean_parser import parse_lean_file
from verifier.proof_synthesizer import synthesize_and_verify, ProofSynthesizer
from verifier.e_ast import literal_vars, substitute_literal

pnum = int(sys.argv[1]) if len(sys.argv) > 1 else 17

lean_path = f"lean_reference/Prop{pnum}.lean"
tr = translate_lean_file(lean_path)
lps = parse_lean_file(lean_path)
lp = lps[0] if lps else None

# Monkey-patch _thm_deps to add debug output
orig_thm_deps = ProofSynthesizer._thm_deps

def debug_thm_deps(self, thm, vm):
    print(f"\n=== _thm_deps for {thm.name} ===")
    for hyp in thm.sequent.hypotheses:
        inst = substitute_literal(hyp, vm)
        # Check exact match
        found_exact = None
        for ln_num, lits in self.ll.items():
            if inst in lits:
                found_exact = ln_num
                break
        # Check symmetric
        sym = self._symmetric_literal(inst)
        found_sym = None
        if sym and not found_exact:
            for ln_num, lits in self.ll.items():
                if sym in lits:
                    found_sym = ln_num
                    break
        # Variable overlap
        hv = literal_vars(inst)
        overlap_lines = []
        for ln_num, lits in self.ll.items():
            for lit in lits:
                if literal_vars(lit) & hv:
                    overlap_lines.append(ln_num)
                    break
        status = f"EXACT@L{found_exact}" if found_exact else (
            f"SYM@L{found_sym}" if found_sym else f"OVERLAP:{overlap_lines}")
        print(f"  hyp: {inst}  -> {status}")
    result = orig_thm_deps(self, thm, vm)
    print(f"  RESULT deps: {result}")
    return result

ProofSynthesizer._thm_deps = debug_thm_deps

sr, vr = synthesize_and_verify(tr, lp)
acc = vr.accepted if vr else None
nfails = sum(1 for _, lr in vr.line_results.items() if not lr.valid) if vr else -1
print(f"\nI.{pnum}: acc={acc} fails={nfails}")
