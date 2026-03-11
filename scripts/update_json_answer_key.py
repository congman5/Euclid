#!/usr/bin/env python3
"""Add verified_proof lines to each proposition in answer_key_book_1.json."""
import json, sys
sys.path.insert(0, ".")
from scripts.generate_verified_proofs import build_direct_proof

json_path = "answer_key_book_1.json"

with open(json_path, "r", encoding="utf-8") as f:
    data = json.load(f)

for n in range(1, 49):
    name = f"Prop.I.{n}"
    pj = build_direct_proof(n)
    if name in data["propositions"]:
        data["propositions"][name]["verified_proof"] = {
            "premises": pj["premises"],
            "goal": pj["goal"],
            "lines": pj["lines"],
        }

with open(json_path, "w", encoding="utf-8") as f:
    json.dump(data, f, indent=2, ensure_ascii=False)

print(f"Updated {json_path} with verified proofs for 48 propositions")
