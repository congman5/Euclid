"""
cli.py — Command-line entry point.
Usage: python -m verifier proof.json [proof2.json ...]
"""
from __future__ import annotations
import sys, json
from .unified_checker import verify_e_proof_json


def main():
    if len(sys.argv) < 2:
        print("Usage: python -m verifier <proof.json> [...]", file=sys.stderr)
        sys.exit(1)
    any_failed = False
    for path in sys.argv[1:]:
        try:
            with open(path, "r", encoding="utf-8") as f:
                data = json.load(f)
        except (json.JSONDecodeError, FileNotFoundError) as e:
            result_dict = {
                "file": path, "accepted": False,
                "diagnostics": [{"line": 0, "code": "PARSE_ERROR",
                                 "message": str(e)}],
            }
            print(json.dumps(result_dict, indent=2))
            any_failed = True
            continue
        result = verify_e_proof_json(data)
        output = {
            "file": path,
            "accepted": result.accepted,
            "errors": result.errors,
            "derived": sorted(result.derived),
        }
        print(json.dumps(output, indent=2))
        if not result.accepted:
            any_failed = True
    sys.exit(1 if any_failed else 0)


if __name__ == "__main__":
    main()
