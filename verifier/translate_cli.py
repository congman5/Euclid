"""
translate_cli.py — CLI entry point for the Lean→System E translator.

Usage:
    python -m verifier.translate_cli [options]

Examples:
    # Translate a single file
    python -m verifier.translate_cli --file lean_reference/Prop16.lean

    # Translate a range of propositions
    python -m verifier.translate_cli --range 16 48

    # Translate all and write output files
    python -m verifier.translate_cli --range 16 48 --out-json translated/ --out-python translated_proofs.py

    # Compare translations with existing e_proofs.py
    python -m verifier.translate_cli --range 16 48 --compare
"""
from __future__ import annotations

import argparse
import json
import sys
from pathlib import Path

# Ensure the parent directory is importable
if __name__ == "__main__":
    sys.path.insert(0, str(Path(__file__).resolve().parent.parent))

from verifier.lean_translator import (
    translate_lean_file,
    translate_all_propositions,
    compare_with_existing,
    TranslationResult,
)
from verifier.lean_to_euclid_json import (
    translation_to_euclid_json,
    write_euclid_json,
    write_all_euclid_json,
)
from verifier.lean_to_python import (
    translation_to_python_with_comments,
    generate_proofs_module,
    write_python_module,
)


def _print_result(result: TranslationResult, verbose: bool = False) -> None:
    status = "OK" if result.success else "FAIL"
    print(f"  [{status}] {result.prop_name} ({result.lean_theorem})")
    print(f"         Steps: {len(result.steps)}  Warnings: {len(result.warnings)}")
    if verbose or not result.success:
        for w in result.warnings:
            print(f"         ⚠ {w}")
    if verbose:
        for ts in result.steps:
            kind = ts.step.kind.name
            desc = ts.step.description
            print(f"         {ts.step.id}. [{kind}] {desc}")


def cmd_translate_file(args: argparse.Namespace) -> int:
    """Translate a single .lean file."""
    result = translate_lean_file(args.file)
    print(f"\n=== Translation: {args.file} ===\n")
    _print_result(result, verbose=args.verbose)

    if args.out_json:
        path = write_euclid_json(result, args.out_json)
        print(f"\n  → JSON written to {path}")

    if args.out_python:
        code = translation_to_python_with_comments(result)
        Path(args.out_python).write_text(code, encoding="utf-8")
        print(f"  → Python written to {args.out_python}")

    if args.compare:
        diff = compare_with_existing(result)
        print(f"\n  Comparison: {diff}")

    return 0 if result.success else 1


def cmd_translate_range(args: argparse.Namespace) -> int:
    """Translate a range of propositions."""
    lean_dir = args.lean_dir
    start, end = args.range_start, args.range_end

    print(f"\n=== Translating Prop I.{start}–I.{end} from {lean_dir} ===\n")

    report = translate_all_propositions(lean_dir, prop_range=(start, end))

    for result in report.results:
        _print_result(result, verbose=args.verbose)

    print(f"\n{report.summary()}")

    # Write JSON files
    if args.out_json:
        out_dir = Path(args.out_json)
        out_dir.mkdir(parents=True, exist_ok=True)
        successful = [r for r in report.results if r.success]
        written = write_all_euclid_json(successful, str(out_dir))
        print(f"\n  → {len(written)} JSON files written to {out_dir}/")

    # Write Python module
    if args.out_python:
        successful = [r for r in report.results if r.success]
        write_python_module(successful, args.out_python)
        print(f"  → Python module written to {args.out_python}")

    # Compare with existing
    if args.compare:
        print("\n--- Comparison with existing e_proofs.py ---")
        for result in report.results:
            if result.success:
                diff = compare_with_existing(result)
                ex = diff.get("existing_steps", "?")
                tr = diff.get("translated_steps", "?")
                print(f"  {result.prop_name}: existing={ex}, translated={tr}")

    failed = sum(1 for r in report.results if not r.success)
    return 1 if failed > 0 else 0


def main() -> int:
    parser = argparse.ArgumentParser(
        prog="translate_cli",
        description="Translate LeanEuclid proofs to System E format",
    )
    parser.add_argument(
        "-v", "--verbose", action="store_true",
        help="Show detailed step-by-step output",
    )
    parser.add_argument(
        "--compare", action="store_true",
        help="Compare translations with existing e_proofs.py",
    )
    parser.add_argument(
        "--out-json", type=str, default=None,
        help="Output directory for .euclid JSON files",
    )
    parser.add_argument(
        "--out-python", type=str, default=None,
        help="Output path for Python proof module",
    )

    group = parser.add_mutually_exclusive_group(required=True)
    group.add_argument(
        "--file", type=str,
        help="Path to a single .lean file to translate",
    )
    group.add_argument(
        "--range", nargs=2, type=int, metavar=("START", "END"),
        help="Range of proposition numbers to translate (e.g. 16 48)",
    )

    parser.add_argument(
        "--lean-dir", type=str, default="lean_reference",
        help="Directory containing LeanEuclid .lean files (default: lean_reference)",
    )

    args = parser.parse_args()

    if args.file:
        return cmd_translate_file(args)
    elif args.range:
        args.range_start, args.range_end = args.range
        return cmd_translate_range(args)

    return 0


if __name__ == "__main__":
    sys.exit(main())
