#!/usr/bin/env python
"""
build_exe.py — Build a standalone Windows .exe for Euclid.

Usage:
    python build_exe.py            Build the app (one-dir mode)
    python build_exe.py --onefile  Build as a single .exe file
    python build_exe.py --clean    Remove previous build artifacts first

Requirements:
    pip install pyinstaller>=6.0

Output:
    dist/Euclid/Euclid.exe   (one-dir mode, default)
    dist/Euclid.exe           (one-file mode, with --onefile)
"""
from __future__ import annotations

import argparse
import os
import shutil
import subprocess
import sys


ROOT = os.path.dirname(os.path.abspath(__file__))
SPEC = os.path.join(ROOT, "euclid.spec")


def _check_pyinstaller():
    """Ensure PyInstaller is installed."""
    try:
        import PyInstaller  # noqa: F401
    except ImportError:
        print("ERROR: PyInstaller is not installed.")
        print("       Install it with:  pip install pyinstaller>=6.0")
        print("       Or:               pip install -e .[dev]")
        sys.exit(1)


def _clean():
    """Remove previous build artifacts."""
    for d in ["build", "dist"]:
        p = os.path.join(ROOT, d)
        if os.path.isdir(p):
            print(f"  Removing {d}/")
            shutil.rmtree(p)
    print("  Clean complete.\n")


def build(*, onefile: bool = False):
    """Run PyInstaller to produce the executable."""
    _check_pyinstaller()

    cmd = [
        sys.executable, "-m", "PyInstaller",
        "--noconfirm",
        "--clean",
    ]

    if onefile:
        # Single-file mode: override the spec's one-dir COLLECT with
        # --onefile flag directly instead of using the spec.
        cmd += [
            "--onefile",
            "--windowed",
            "--name", "Euclid",
            "--icon", os.path.join(ROOT, "Euclid.ico"),
            "--add-data", f"{os.path.join(ROOT, 'Euclid Logo.png')}{os.pathsep}.",
            "--add-data", f"{os.path.join(ROOT, 'Euclid.ico')}{os.pathsep}.",
            os.path.join(ROOT, "launch_euclid.pyw"),
        ]
        print("Building Euclid.exe (single-file mode)...\n")
    else:
        cmd.append(SPEC)
        print("Building Euclid (one-directory mode)...\n")

    result = subprocess.run(cmd, cwd=ROOT)
    if result.returncode != 0:
        print(f"\nBuild FAILED (exit code {result.returncode})")
        sys.exit(result.returncode)

    # Report output location
    if onefile:
        exe = os.path.join(ROOT, "dist", "Euclid.exe")
    else:
        exe = os.path.join(ROOT, "dist", "Euclid", "Euclid.exe")

    if os.path.exists(exe):
        size_mb = os.path.getsize(exe) / (1024 * 1024)
        print(f"\n{'='*60}")
        print(f"  BUILD SUCCESSFUL")
        print(f"  Executable: {exe}")
        print(f"  Size:       {size_mb:.1f} MB")
        print(f"{'='*60}")
    else:
        print(f"\nWARNING: Expected executable not found at {exe}")


def main():
    parser = argparse.ArgumentParser(
        description="Build Euclid as a standalone .exe")
    parser.add_argument(
        "--onefile", action="store_true",
        help="Produce a single .exe instead of a directory")
    parser.add_argument(
        "--clean", action="store_true",
        help="Remove build/ and dist/ before building")
    args = parser.parse_args()

    if args.clean:
        _clean()

    build(onefile=args.onefile)


if __name__ == "__main__":
    main()
