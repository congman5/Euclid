#!/usr/bin/env python3
"""
Regenerate answer-key-book-I.txt with verified Tier-1 proofs.

For each Prop.I.N:
  - Preserves: statement, System E/H data, dependencies
  - Tier 1 (Verified Proof): machine-verified steps from E library
  - Tier 2 (Proof Sketch): original detailed steps preserved as reference

Reads the existing answer key to extract sketch steps and metadata,
then writes the new file with both tiers.
"""
from __future__ import annotations
import json, sys, os, re, textwrap
os.environ["PYTHONIOENCODING"] = "utf-8"

from pathlib import Path
ROOT = Path(__file__).resolve().parent.parent
sys.path.insert(0, str(ROOT))

from verifier.e_library import E_THEOREM_LIBRARY


# ── Parse existing answer key for metadata + sketch steps ──

def parse_existing(path: Path) -> dict:
    """Extract per-proposition metadata from existing answer key."""
    text = path.read_text(encoding="utf-8")
    lines = text.splitlines()

    HEADER = re.compile(r"={5,}")
    PROP_RE = re.compile(r"PROPOSITION I\.(\d+)\s*[—–-]\s*(.+)")

    props = {}
    i = 0
    while i < len(lines):
        m = PROP_RE.search(lines[i])
        if m:
            num = int(m.group(1))
            title = m.group(2).strip()

            # Find the block for this prop: from here to next prop header or EOF
            start = i
            i += 1
            while i < len(lines):
                if PROP_RE.search(lines[i]):
                    break
                i += 1
            block = lines[start:i]
            props[num] = _parse_block(num, title, block)
        else:
            i += 1

    return props


def _parse_block(num: int, title: str, block: list) -> dict:
    """Parse a single proposition block."""
    result = {
        "num": num,
        "title": title,
        "statement": "",
        "system_e_given": [],
        "system_e_construct": "",
        "system_e_prove": [],
        "system_h_given": [],
        "system_h_construct": "",
        "system_h_prove": [],
        "dependencies": "",
        "sketch_lines": [],
    }

    section = None  # "E" | "H" | "deps" | "proof"
    sketch_buf = []

    for line in block:
        s = line.strip()

        if s.startswith("Statement:"):
            result["statement"] = s[len("Statement:"):].strip()
            continue
        if s == "System E:":
            section = "E"
            continue
        if s == "System H:":
            section = "H"
            continue
        if s.startswith("Dependencies:"):
            result["dependencies"] = s[len("Dependencies:"):].strip()
            section = "deps"
            continue
        if s.startswith("Proof (") or s.startswith("Proof:"):
            section = "proof"
            continue
        if s.startswith("────"):
            continue

        if section == "E":
            if s.startswith("Given:"):
                result["system_e_given"] = s[len("Given:"):].strip()
            elif s.startswith("Construct:"):
                result["system_e_construct"] = s[len("Construct:"):].strip()
            elif s.startswith("Prove:"):
                result["system_e_prove"] = s[len("Prove:"):].strip()
        elif section == "H":
            if s.startswith("Given:"):
                result["system_h_given"] = s[len("Given:"):].strip()
            elif s.startswith("Construct:"):
                result["system_h_construct"] = s[len("Construct:"):].strip()
            elif s.startswith("Prove:"):
                result["system_h_prove"] = s[len("Prove:"):].strip()
        elif section == "proof":
            if s and not s.startswith("Q.E."):
                sketch_buf.append(line)

    result["sketch_lines"] = sketch_buf
    return result


# ── Generate verified proof lines ──

def _prop_i_1_verified_lines():
    """Prop.I.1 expanded construction proof (13 steps)."""
    return [
        (1, "Given", [], "\u00ac(a = b)"),
        (2, "let-circle", [1], "center(a, \u03b1), on(b, \u03b1)"),
        (3, "let-circle", [1], "center(b, \u03b2), on(a, \u03b2)"),
        (4, "Generality 3", [2], "inside(a, \u03b1)"),
        (5, "Generality 3", [3], "inside(b, \u03b2)"),
        (6, "Intersection 9", [2, 3, 4, 5], "intersects(\u03b1, \u03b2)"),
        (7, "let-intersection-circle-circle-one", [6],
         "on(c, \u03b1), on(c, \u03b2)"),
        (8, "Segment transfer 4", [2, 7], "ac = ab"),
        (9, "Segment transfer 4", [3, 7], "bc = ba"),
        (10, "Metric", [8], "ab = ac"),
        (11, "Metric", [9, 10], "ab = bc"),
        (12, "Metric", [10], "\u00ac(c = a)"),
        (13, "Metric", [11], "\u00ac(c = b)"),
    ]


def make_verified_lines(num: int):
    """Generate Tier-1 verified proof lines for Prop.I.N.

    Uses generate_verified_proofs.build_direct_proof to get the proof
    JSON, then converts to (lid, justification, refs, statement) tuples.
    """
    from scripts.generate_verified_proofs import build_direct_proof
    pj = build_direct_proof(num)
    return [
        (line["id"], line["justification"], line["refs"], line["statement"])
        for line in pj["lines"]
    ]


# ── Write new answer key ──

def write_answer_key(path: Path, props: dict):
    """Write the new answer-key-book-I.txt."""
    out = []

    # Header
    out.append("=" * 80)
    out.append("  ANSWER KEY \u2014 Euclid's Elements Book I, Propositions I.1\u2013I.48")
    out.append("  Formal Systems E + H (Avigad/Dean/Mumma 2009, Hilbert 1899)")
    out.append("=" * 80)
    out.append("")
    out.append("  Proof Tiers")
    out.append("  \u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500")
    out.append("  Verified Proof:       Axiom-level proof from construction rules,")
    out.append("                        diagrammatic/metric axioms, and SAS/SSS.")
    out.append("                        Props I.1, I.4, I.8 have these.")
    out.append("  Sequent Verification: Confirms the E library sequent is well-formed")
    out.append("                        (hypotheses entail conclusions).  Uses the")
    out.append("                        established theorem as justification.")
    out.append("  Proof Sketch:         Informal outline for human reference.")
    out.append("                        May use prose or unverified steps.")
    out.append("")
    out.append("  System E Notation")
    out.append("  \u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500")
    out.append("  ab               = segment from point a to point b")
    out.append("  \u2220abc              = angle at vertex b with rays ba, bc")
    out.append("  \u25b3abc              = area of triangle abc")
    out.append("  ab + cd           = magnitude addition (MagAdd)")
    out.append("  right-angle       = a right angle magnitude")
    out.append("  on(p, L)          = point p lies on line L")
    out.append("  between(a,b,c)    = b is strictly between a and c")
    out.append("  same-side(a,b,L)  = a and b on the same side of line L")
    out.append("  center(a, \u03b1)      = a is the center of circle \u03b1")
    out.append("  on(p, \u03b1)          = p is on circle \u03b1 (circumference)")
    out.append("  inside(p, \u03b1)      = p is inside circle \u03b1")
    out.append("  intersects(\u03b1, \u03b2)  = circles \u03b1 and \u03b2 intersect")
    out.append("  \u00ac(intersects(L,M)) = lines L and M are parallel")
    out.append("  \u00ac(a = b)          = a and b are distinct points")
    out.append("  ab < cd           = segment ab strictly less than cd")
    out.append("  \u2220abc < \u2220def       = angle abc strictly less than def")
    out.append("")
    out.append("  System H Notation")
    out.append("  \u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500")
    out.append("  IncidL(a, l)           = point a lies on line l")
    out.append("  BetH(a, b, c)          = b is strictly between a and c")
    out.append("  CongH(a, b, c, d)      = segment ab \u2245 segment cd")
    out.append("  CongaH(a,b,c,d,e,f)    = \u2220abc \u2245 \u2220def")
    out.append("  ColH(a, b, c)           = a, b, c are collinear")
    out.append("  outH(a, b, c)           = c is on ray ab")
    out.append("  SameSideH(a, b, l)      = a and b on same side of l")
    out.append("  Cut(l, a, b)            = line l separates a and b")
    out.append("  Para(l, m)              = lines l and m are parallel")
    out.append("  \u00ac(a = b)               = a and b are distinct points")
    out.append("")
    out.append("  Justification Names (for refs)")
    out.append("  \u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500")
    out.append("  Given                           \u2014 premise")
    out.append("  let-line                        \u2014 construct line (\u00a73.3)")
    out.append("  let-circle                      \u2014 construct circle (\u00a73.3)")
    out.append("  let-point-on-line               \u2014 introduce point on line (\u00a73.3)")
    out.append("  let-point-on-circle             \u2014 introduce point on circle (\u00a73.3)")
    out.append("  let-intersection-*              \u2014 intersection constructions (\u00a73.3)")
    out.append("  Diagrammatic                    \u2014 diagram axioms (\u00a73.4)")
    out.append("  Generality N                    \u2014 named diag. axiom (\u00a73.4)")
    out.append("  Betweenness N                   \u2014 named betweenness axiom (\u00a73.4)")
    out.append("  Intersection N                  \u2014 named intersection axiom (\u00a73.4)")
    out.append("  Metric                          \u2014 metric axioms (\u00a73.5)")
    out.append("  Transfer                        \u2014 transfer axioms (\u00a73.6)")
    out.append("  Segment transfer N              \u2014 named transfer axiom (\u00a73.6)")
    out.append("  SAS                             \u2014 SAS superposition (\u00a73.7)")
    out.append("  SSS                             \u2014 SSS superposition (\u00a73.7)")
    out.append("  Prop.I.N                        \u2014 apply proved proposition")
    out.append("")
    out.append("")

    for n in range(1, 49):
        data = props.get(n, {})
        title = data.get("title", f"Proposition I.{n}")

        out.append("=" * 80)
        out.append(f"  PROPOSITION I.{n} \u2014 {title}")
        out.append("=" * 80)
        out.append("")
        if data.get("statement"):
            out.append(f"  Statement: {data['statement']}")
            out.append("")

        # System E
        out.append("  System E:")
        if data.get("system_e_given"):
            out.append(f"    Given:     {data['system_e_given']}")
        if data.get("system_e_construct"):
            out.append(f"    Construct: {data['system_e_construct']}")
        if data.get("system_e_prove"):
            out.append(f"    Prove:     {data['system_e_prove']}")
        out.append("")

        # System H
        if data.get("system_h_given") or data.get("system_h_prove"):
            out.append("  System H:")
            if data.get("system_h_given"):
                out.append(f"    Given:     {data['system_h_given']}")
            if data.get("system_h_construct"):
                out.append(f"    Construct: {data['system_h_construct']}")
            if data.get("system_h_prove"):
                out.append(f"    Prove:     {data['system_h_prove']}")
            out.append("")

        # Dependencies
        deps = data.get("dependencies", "(none)")
        out.append(f"  Dependencies: {deps}")
        out.append("")

        # Tier 1: Verified Proof
        vlines = make_verified_lines(n)
        # Propositions with full non-circular proofs
        from scripts.real_proofs import ALL as _REAL
        if n in _REAL:
            out.append(f"  Verified Proof ({len(vlines)} steps):")
        else:
            out.append(f"  Sequent Verification ({len(vlines)} steps):")
        out.append("  " + "\u2500" * 30)
        for lid, just, refs, stmt in vlines:
            refs_str = ", ".join(str(r) for r in refs) if refs else ""
            out.append(f"   {lid:2d}. [{just}]  [refs: {refs_str}]")
            out.append(f"       \u2192 {stmt}")
        out.append("")
        out.append("  Q.E.D. \u25a0")
        out.append("")

        # Tier 2: Sketch (if exists)
        sketch = data.get("sketch_lines", [])
        if sketch:
            out.append("  Proof Sketch (unverified reference):")
            out.append("  " + "\u2500" * 38)
            for sl in sketch:
                out.append(sl)
            out.append("")

        out.append("")

    path.write_text("\n".join(out), encoding="utf-8")
    print(f"Wrote {path}")


def main():
    ak_path = ROOT / "answer-key-book-I.txt"
    props = parse_existing(ak_path)
    print(f"Parsed {len(props)} propositions from existing answer key")

    write_answer_key(ak_path, props)
    print("Done!")


if __name__ == "__main__":
    main()
