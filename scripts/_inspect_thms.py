import json, sys, io
sys.stdout = io.TextIOWrapper(sys.stdout.buffer, encoding='utf-8')

with open("answer_key_book_1.json", "r", encoding="utf-8") as f:
    d = json.load(f)

# Show Prop.I.3 proof
p = d["propositions"]["Prop.I.3"]["verified_proof"]
print("=== Prop.I.3 ===")
print("Premises:", p["premises"])
print("Goal:", p["goal"])
for line in p["lines"]:
    print(f"  {line['id']} (d={line.get('depth',0)}): {line['statement']!r}  [{line['justification']}]  refs={line.get('refs',[])}")

# Show Prop.I.2 theorem hypotheses
from verifier.e_library import E_THEOREM_LIBRARY
thm = E_THEOREM_LIBRARY.get("Prop.I.2")
if thm:
    print("\n=== Prop.I.2 theorem ===")
    print("Hypotheses:", [str(h) for h in thm.sequent.hypotheses])
    print("Conclusions:", [str(c) for c in thm.sequent.conclusions])

# Show Prop.I.3 theorem hypotheses
thm3 = E_THEOREM_LIBRARY.get("Prop.I.3")
if thm3:
    print("\n=== Prop.I.3 theorem ===")
    print("Hypotheses:", [str(h) for h in thm3.sequent.hypotheses])
    print("Conclusions:", [str(c) for c in thm3.sequent.conclusions])

# Show Prop.I.9 theorem hypotheses
thm9 = E_THEOREM_LIBRARY.get("Prop.I.9")
if thm9:
    print("\n=== Prop.I.9 theorem ===")
    print("Hypotheses:", [str(h) for h in thm9.sequent.hypotheses])
    print("Conclusions:", [str(c) for c in thm9.sequent.conclusions])
