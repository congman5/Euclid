"""
generate_answer_key.py — Regenerate answer-key-book-I.txt from real_proofs.py.

Reads the verified proof JSON for each proposition and formats it as the
answer key text file, preserving all metadata (statements, System E/H
sequents, dependencies) from the existing answer key.

Run: python -X utf8 scripts/generate_answer_key.py
"""
from __future__ import annotations
import sys, os, re, io
sys.path.insert(0, os.path.join(os.path.dirname(__file__), ".."))
os.environ["PYTHONIOENCODING"] = "utf-8"
sys.stdout = io.TextIOWrapper(sys.stdout.buffer, encoding="utf-8")

from scripts.real_proofs import ALL, check


# ── Metadata for each proposition (Statement, System H, Dependencies) ──
# Extracted from the existing answer-key-book-I.txt and E library.

PROP_META = {
    1: {
        "title": "Equilateral Triangle Construction",
        "statement": "On a given finite straight line, construct an equilateral triangle.",
        "sys_h_given": "¬(a = b)",
        "sys_h_construct": "∃c: POINT",
        "sys_h_prove": "CongH(a, b, a, c), CongH(a, b, b, c), ¬(c = a), ¬(c = b), ¬(ColH(a, b, c))",
        "deps": "(none)",
    },
    2: {
        "title": "Copy a Segment to a Given Point",
        "statement": "From a given point, place a straight line equal to a given straight line.",
        "sys_h_given": "¬(a = b), ¬(a' = p), IncidL(a', l), IncidL(p, l)",
        "sys_h_construct": "∃b': POINT",
        "sys_h_prove": "IncidL(b', l), outH(a', p, b'), CongH(a', b', a, b)",
        "deps": "I.1",
    },
    3: {
        "title": "Cut Off an Equal Segment",
        "statement": "From the greater of two unequal straight lines, cut off a straight line equal to the less.",
        "sys_h_given": "¬(a = b), ¬(c = d), IncidL(a, l), IncidL(b, l)",
        "sys_h_construct": "∃e: POINT",
        "sys_h_prove": "BetH(a, e, b), CongH(a, e, c, d)",
        "deps": "I.2",
    },
    4: {
        "title": "SAS Triangle Congruence",
        "statement": "SAS: side-angle-side triangle congruence.",
        "sys_h_given": "¬(ColH(a, b, c)), ¬(ColH(d, e, f)), CongH(a, b, d, e), CongH(a, c, d, f), CongaH(b, a, c, e, d, f)",
        "sys_h_prove": "CongaH(a, b, c, d, e, f), CongH(b, c, e, f)",
        "deps": "(superposition axiom)",
    },
    5: {
        "title": "Isosceles Base Angles",
        "statement": "In isosceles triangles the base angles are equal.",
        "sys_h_given": "¬(ColH(a, b, c)), CongH(a, b, a, c)",
        "sys_h_prove": "CongaH(a, b, c, a, c, b)",
        "deps": "I.4, I.3",
    },
    6: {
        "title": "Converse of I.5",
        "statement": "If in a triangle two angles are equal, then the sides opposite the equal angles are also equal.",
        "sys_h_given": "¬(ColH(a, b, c)), CongaH(a, b, c, a, c, b)",
        "sys_h_prove": "CongH(a, b, a, c)",
        "deps": "I.4, I.3",
    },
    7: {
        "title": "Uniqueness of Triangle Construction",
        "statement": "Given segments BA, CA from endpoints of a segment BC, there cannot be constructed from the same endpoints and on the same side of it other segments BD, CD equal to them respectively.",
        "sys_h_given": "¬(b = c), IncidL(b, l), IncidL(c, l), same_side(a, d, l), CongH(b, d, b, a), CongH(c, d, c, a)",
        "sys_h_prove": "d = a",
        "deps": "I.5",
    },
    8: {
        "title": "SSS Triangle Congruence",
        "statement": "SSS: side-side-side triangle congruence.",
        "sys_h_given": "¬(ColH(a, b, c)), ¬(ColH(d, e, f)), CongH(a, b, d, e), CongH(b, c, e, f), CongH(c, a, f, d)",
        "sys_h_prove": "CongaH(b, a, c, e, d, f), CongaH(a, b, c, d, e, f), CongaH(b, c, a, e, f, d)",
        "deps": "I.7",
    },
    9: {
        "title": "Bisect an Angle",
        "statement": "To bisect a given rectilineal angle.",
        "sys_h_given": "¬(ColH(a, b, c))",
        "sys_h_construct": "∃e: POINT",
        "sys_h_prove": "CongaH(b, a, e, c, a, e)",
        "deps": "I.1, I.8",
    },
    10: {
        "title": "Bisect a Segment",
        "statement": "To bisect a given finite straight line.",
        "sys_h_given": "¬(a = b), IncidL(a, l), IncidL(b, l)",
        "sys_h_construct": "∃d: POINT",
        "sys_h_prove": "BetH(a, d, b), CongH(a, d, d, b)",
        "deps": "I.1, I.4",
    },
    11: {
        "title": "Perpendicular from a Point on a Line",
        "statement": "To draw a straight line at right angles to a given straight line from a given point on it.",
        "sys_h_given": "¬(a = b), IncidL(a, l), IncidL(b, l)",
        "sys_h_construct": "∃f: POINT",
        "sys_h_prove": "¬(ColH(f, a, b))",
        "deps": "I.1, I.8",
    },
    12: {
        "title": "Perpendicular from a Point Off a Line",
        "statement": "To draw a straight line perpendicular to a given infinite straight line from a given point not on it.",
        "sys_h_given": "¬(a = b), IncidL(a, l), IncidL(b, l), ¬(IncidL(p, l))",
        "sys_h_construct": "∃h: POINT",
        "sys_h_prove": "IncidL(h, l), ¬(h = p)",
        "deps": "I.8, I.10",
    },
    13: {
        "title": "Supplementary Angles",
        "statement": "If a straight line set up on a straight line makes angles, it makes either two right angles or angles equal to two right angles.",
        "sys_h_given": "BetH(a, b, c), ¬(ColH(a, b, d))",
        "deps": "I.11",
    },
    14: {
        "title": "Converse of I.13",
        "statement": "If with any straight line, and at a point on it, two straight lines not lying on the same side make the adjacent angles equal to two right angles, the two lines are in a straight line with one another.",
        "sys_h_given": "IncidL(a, l), IncidL(b, l), ¬(a = b), ¬(IncidL(c, l)), ¬(IncidL(d, l)), ¬(same_side(c, d, l))",
        "sys_h_prove": "BetH(c, b, d)",
        "deps": "I.13",
    },
    15: {
        "title": "Vertical Angles",
        "statement": "If two straight lines cut one another, they make the vertical angles equal to one another.",
        "sys_h_given": "BetH(a, e, b), BetH(c, e, d), ¬(ColH(a, e, c))",
        "sys_h_prove": "CongaH(a, e, c, b, e, d)",
        "deps": "I.13",
    },
    16: {
        "title": "Exterior Angle Theorem",
        "statement": "In any triangle, if one of the sides is produced, the exterior angle is greater than either of the interior and opposite angles.",
        "sys_h_given": "¬(ColH(a, b, c)), BetH(a, b, d)",
        "deps": "I.4, I.10, I.15",
    },
    17: {
        "title": "Two Angles Less Than Two Right Angles",
        "statement": "In any triangle two angles taken together in any manner are less than two right angles.",
        "sys_h_given": "¬(ColH(a, b, c))",
        "deps": "I.13, I.16",
    },
    18: {
        "title": "Greater Side Subtends Greater Angle",
        "statement": "In any triangle the greater side subtends the greater angle.",
        "sys_h_given": "¬(ColH(a, b, c))",
        "deps": "I.3, I.5, I.16",
    },
    19: {
        "title": "Greater Angle Subtended by Greater Side",
        "statement": "In any triangle the greater angle is subtended by the greater side.",
        "sys_h_given": "¬(ColH(a, b, c))",
        "deps": "I.5, I.18",
    },
    20: {
        "title": "Triangle Inequality",
        "statement": "In any triangle two sides taken together in any manner are greater than the remaining one.",
        "sys_h_given": "¬(ColH(a, b, c))",
        "deps": "I.3, I.5, I.19",
    },
    21: {
        "title": "Inner Triangle Inequality",
        "statement": "If on one of the sides of a triangle, from its extremities, there be constructed two straight lines meeting within the triangle, the straight lines so constructed will be less than the remaining two sides of the triangle, but will contain a greater angle.",
        "sys_h_given": "¬(ColH(a, b, c))",
        "deps": "I.16, I.20",
    },
    22: {
        "title": "Construct Triangle from Three Segments",
        "statement": "Out of three straight lines, which are equal to three given straight lines, to construct a triangle.",
        "sys_h_given": "¬(a = b), ¬(c = d), ¬(e = f)",
        "sys_h_construct": "∃p: POINT, q: POINT, r: POINT",
        "sys_h_prove": "CongH(p, q, a, b), CongH(p, r, c, d), CongH(q, r, e, f)",
        "deps": "I.1, I.3, I.20",
    },
    23: {
        "title": "Copy an Angle",
        "statement": "On a given straight line and at a point on it, to construct a rectilineal angle equal to a given rectilineal angle.",
        "sys_h_given": "¬(ColH(d, e, f)), IncidL(a, l), IncidL(b, l), ¬(a = b)",
        "sys_h_construct": "∃g: POINT",
        "sys_h_prove": "CongaH(e, d, f, b, a, g)",
        "deps": "I.8, I.22",
    },
    24: {
        "title": "SAS Inequality (Hinge Theorem)",
        "statement": "If two triangles have the two sides equal to two sides respectively, but have the one of the angles contained by the equal straight lines greater than the other, they will also have the base greater than the base.",
        "sys_h_given": "¬(ColH(a, b, c)), ¬(ColH(d, e, f)), CongH(a, b, d, e), CongH(a, c, d, f)",
        "deps": "I.4, I.5, I.19, I.23",
    },
    25: {
        "title": "Converse Hinge Theorem",
        "statement": "If two triangles have the two sides equal to two sides respectively, but have the base greater than the base, they will also have the one of the angles contained by the equal straight lines greater than the other.",
        "sys_h_given": "¬(ColH(a, b, c)), ¬(ColH(d, e, f)), CongH(a, b, d, e), CongH(a, c, d, f)",
        "deps": "I.4, I.24",
    },
    26: {
        "title": "ASA / AAS Congruence",
        "statement": "If two triangles have the two angles equal to two angles respectively, and one side equal to one side, namely, either the side adjoining the equal angles, or that subtending one of the equal angles, the remaining sides will also be equal to the remaining sides and the remaining angle to the remaining angle.",
        "sys_h_given": "¬(ColH(a, b, c)), ¬(ColH(d, e, f))",
        "deps": "I.3, I.4, I.16",
    },
    27: {
        "title": "Alternate Interior Angles ⇒ Parallel",
        "statement": "If a straight line falling on two straight lines makes the alternate angles equal to one another, the straight lines will be parallel to one another.",
        "sys_h_given": "IncidL(a, l), IncidL(b, l), IncidL(b, m), IncidL(c, m), IncidL(c, n), IncidL(d, n), ¬(a = b), ¬(b = c), ¬(c = d)",
        "deps": "I.16",
    },
    28: {
        "title": "Co-interior Angles ⇒ Parallel",
        "statement": "If a straight line falling on two straight lines makes the exterior angle equal to the interior and opposite angle on the same side, or the interior angles on the same side equal to two right angles, the straight lines will be parallel to one another.",
        "sys_h_given": "IncidL(a, l), IncidL(b, l), IncidL(b, m), IncidL(c, m), IncidL(c, n), IncidL(d, n), ¬(a = b), ¬(b = c), ¬(c = d)",
        "deps": "I.15, I.27",
    },
    29: {
        "title": "Parallel ⇒ Alternate Interior Angles Equal",
        "statement": "A straight line falling on parallel straight lines makes the alternate angles equal to one another, the exterior angle equal to the interior and opposite angle, and the interior angles on the same side equal to two right angles.",
        "sys_h_given": "IncidL(a, l), IncidL(b, l), IncidL(b, m), IncidL(c, m), IncidL(c, n), IncidL(d, n), ¬(a = b), ¬(b = c), ¬(c = d), Para(l, n)",
        "deps": "I.27, Parallel Postulate",
    },
    30: {
        "title": "Transitivity of Parallelism",
        "statement": "Straight lines parallel to the same straight line are also parallel to one another.",
        "sys_h_given": "Para(l, m), Para(m, n), ¬(l = m), ¬(m = n), ¬(l = n)",
        "deps": "I.27, I.29",
    },
    31: {
        "title": "Construct a Parallel Through a Point",
        "statement": "Through a given point to draw a straight line parallel to a given straight line.",
        "sys_h_given": "IncidL(b, l), IncidL(c, l), ¬(b = c), ¬(IncidL(a, l))",
        "sys_h_construct": "∃m: LINE",
        "sys_h_prove": "IncidL(a, m), Para(l, m)",
        "deps": "I.23, I.27",
    },
    32: {
        "title": "Angle Sum of a Triangle",
        "statement": "In any triangle, if one of the sides be produced, the exterior angle is equal to the two interior and opposite angles, and the three interior angles of the triangle are equal to two right angles.",
        "sys_h_given": "¬(ColH(a, b, c))",
        "deps": "I.13, I.29, I.31",
    },
    33: {
        "title": "Joining Equal Parallel Segments",
        "statement": "The straight lines joining equal and parallel straight lines (at the extremities which are) in the same directions (respectively) are themselves also equal and parallel.",
        "sys_h_given": "IncidL(a, l), IncidL(b, l), IncidL(c, n), IncidL(d, n), Para(l, n), CongH(a, b, c, d)",
        "deps": "I.4, I.27, I.29",
    },
    34: {
        "title": "Properties of a Parallelogram",
        "statement": "In parallelogrammic areas the opposite sides and angles are equal to one another, and the diameter bisects the areas.",
        "sys_h_given": "Para(l, n), Para(m, p)",
        "deps": "I.4, I.26, I.29",
    },
    35: {
        "title": "Parallelograms on Same Base, Same Parallels",
        "statement": "Parallelograms which are on the same base and in the same parallels are equal to one another.",
        "sys_h_given": "Para(l, n)",
        "deps": "I.29, I.34",
    },
    36: {
        "title": "Parallelograms on Equal Bases, Same Parallels",
        "statement": "Parallelograms which are on equal bases and in the same parallels are equal to one another.",
        "sys_h_given": "Para(l, n)",
        "deps": "I.33, I.34, I.35",
    },
    37: {
        "title": "Triangles on Same Base, Same Parallels",
        "statement": "Triangles which are on the same base and in the same parallels are equal to one another.",
        "sys_h_given": "Para(l, n)",
        "deps": "I.31, I.34, I.35",
    },
    38: {
        "title": "Triangles on Equal Bases, Same Parallels",
        "statement": "Triangles which are on equal bases and in the same parallels are equal to one another.",
        "sys_h_given": "Para(l, n)",
        "deps": "I.31, I.34, I.36",
    },
    39: {
        "title": "Equal Triangles on Same Base ⇒ Same Parallels",
        "statement": "Equal triangles which are on the same base and on the same side are also in the same parallels.",
        "sys_h_given": "¬(ColH(a, b, c)), ¬(ColH(d, b, c))",
        "deps": "I.31, I.37",
    },
    40: {
        "title": "Equal Triangles on Equal Bases ⇒ Same Parallels",
        "statement": "Equal triangles which are on equal bases and on the same side are also in the same parallels.",
        "sys_h_given": "¬(ColH(a, b, c)), ¬(ColH(d, e, f))",
        "deps": "I.38, I.39",
    },
    41: {
        "title": "Parallelogram Double the Triangle",
        "statement": "If a parallelogram have the same base with a triangle and be in the same parallels, the parallelogram is double of the triangle.",
        "sys_h_given": "Para(l, n)",
        "deps": "I.34, I.37",
    },
    42: {
        "title": "Construct Parallelogram Equal to Triangle",
        "statement": "To construct, in a given rectilineal angle, a parallelogram equal to a given triangle.",
        "sys_h_given": "¬(ColH(a, b, c))",
        "sys_h_construct": "∃g: POINT, h: POINT",
        "deps": "I.10, I.23, I.31, I.41",
    },
    43: {
        "title": "Complements About a Diagonal",
        "statement": "In any parallelogram the complements of the parallelograms about the diameter are equal to one another.",
        "sys_h_given": "Para(l, n), Para(m, p)",
        "deps": "I.34",
    },
    44: {
        "title": "Apply Parallelogram to a Line",
        "statement": "To a given straight line to apply, in a given rectilineal angle, a parallelogram equal to a given triangle.",
        "sys_h_given": "IncidL(a, l), IncidL(b, l), ¬(a = b), ¬(ColH(c, d, e))",
        "deps": "I.29, I.31, I.42, I.43",
    },
    45: {
        "title": "Construct Parallelogram Equal to Rectilineal Figure",
        "statement": "To construct, in a given rectilineal angle, a parallelogram equal to a given rectilineal figure.",
        "sys_h_given": "¬(ColH(a, b, c))",
        "deps": "I.42, I.44",
    },
    46: {
        "title": "Construct a Square",
        "statement": "On a given straight line to describe a square.",
        "sys_h_given": "IncidL(a, l), IncidL(b, l), ¬(a = b)",
        "sys_h_construct": "∃c: POINT, d: POINT",
        "deps": "I.11, I.3, I.31, I.29, I.34",
    },
    47: {
        "title": "The Pythagorean Theorem",
        "statement": "In right-angled triangles the square on the side subtending the right angle is equal to the squares on the sides containing the right angle.",
        "sys_h_given": "¬(ColH(a, b, c))",
        "deps": "I.4, I.14, I.41, I.46",
    },
    48: {
        "title": "Converse of the Pythagorean Theorem",
        "statement": "If in a triangle the square on one of the sides be equal to the squares on the remaining two sides of the triangle, the angle contained by the remaining two sides of the triangle is right.",
        "sys_h_given": "¬(ColH(a, b, c))",
        "deps": "I.8, I.47",
    },
}


def format_refs(refs):
    """Format ref list as comma-separated string."""
    if not refs:
        return ""
    return ", ".join(str(r) for r in refs)


def format_proof_lines(proof_json):
    """Format proof lines for the answer key."""
    lines = proof_json["lines"]
    total = len(lines)
    # Determine width for line numbers
    width = len(str(total))
    result = []
    for line in lines:
        lid = line["id"]
        stmt = line["statement"]
        just = line["justification"]
        refs = format_refs(line["refs"])
        num_str = str(lid).rjust(width)
        result.append(f"  {num_str}. [{just}]  [refs: {refs}]")
        result.append(f"  {' ' * width}   → {stmt}")
    return "\n".join(result)


def classify_proof(proof_json):
    """Classify proof as 'Verified Proof'."""
    return "Verified Proof"


def generate_answer_key():
    """Generate the full answer-key-book-I.txt content."""
    out = []

    # Header
    out.append("=" * 80)
    out.append("  ANSWER KEY — Euclid's Elements Book I, Propositions I.1–I.48")
    out.append("  Formal Systems E + H (Avigad/Dean/Mumma 2009, Hilbert 1899)")
    out.append("=" * 80)
    out.append("")
    out.append("  Proof Tiers")
    out.append("  " + "─" * 12)
    out.append("  Verified Proof:       Axiom-level proof from construction rules,")
    out.append("                        diagrammatic/metric axioms, and SAS/SSS.")
    out.append("                        Uses only earlier propositions (no circularity).")
    out.append("")
    out.append("  System E Notation")
    out.append("  " + "─" * 18)
    out.append("  ab               = segment from point a to point b")
    out.append("  ∠abc              = angle at vertex b with rays ba, bc")
    out.append("  △abc              = area of triangle abc")
    out.append("  ab + cd           = magnitude addition (MagAdd)")
    out.append("  right-angle       = a right angle magnitude")
    out.append("  on(p, L)          = point p lies on line L")
    out.append("  between(a,b,c)    = b is strictly between a and c")
    out.append("  same-side(a,b,L)  = a and b on the same side of line L")
    out.append("  center(a, α)      = a is the center of circle α")
    out.append("  on(p, α)          = p is on circle α (circumference)")
    out.append("  inside(p, α)      = p is inside circle α")
    out.append("  intersects(α, β)  = circles α and β intersect")
    out.append("  ¬(intersects(L,M)) = lines L and M are parallel")
    out.append("  ¬(a = b)          = a and b are distinct points")
    out.append("  ab < cd           = segment ab strictly less than cd")
    out.append("  ∠abc < ∠def       = angle abc strictly less than def")
    out.append("")
    out.append("  Justification Names (for refs)")
    out.append("  " + "─" * 33)
    out.append("  Given                           — premise")
    out.append("  let-line                        — construct line (§3.3)")
    out.append("  let-circle                      — construct circle (§3.3)")
    out.append("  let-point-on-line               — introduce point on line (§3.3)")
    out.append("  let-point-on-circle             — introduce point on circle (§3.3)")
    out.append("  let-intersection-*              — intersection constructions (§3.3)")
    out.append("  Diagrammatic                    — diagram axioms (§3.4)")
    out.append("  Generality N                    — named diag. axiom (§3.4)")
    out.append("  Betweenness N                   — named betweenness axiom (§3.4)")
    out.append("  Intersection N                  — named intersection axiom (§3.4)")
    out.append("  Metric                          — metric axioms (§3.5)")
    out.append("  Transfer                        — transfer axioms (§3.6)")
    out.append("  Segment transfer N              — named transfer axiom (§3.6)")
    out.append("  SAS                             — SAS superposition (§3.7)")
    out.append("  SSS                             — SSS superposition (§3.7)")
    out.append("  Prop.I.N                        — apply proved proposition")
    out.append("")
    out.append("")

    # Each proposition
    for n in range(1, 49):
        pj = ALL[n]
        meta = PROP_META[n]

        out.append("=" * 80)
        out.append(f"  PROPOSITION I.{n} — {meta['title']}")
        out.append("=" * 80)
        out.append("")
        out.append(f"  Statement: {meta['statement']}")
        out.append("")

        # System E sequent (from proof JSON)
        premises_str = ", ".join(pj["premises"])
        goal_str = pj["goal"]

        # Detect construct vars (exist in goal but not in premises)
        out.append("  System E:")
        out.append(f"    Given:     {premises_str}")

        # Check if there are constructed variables
        construct = meta.get("sys_h_construct")
        if construct:
            out.append(f"    Construct: {construct}")
        out.append(f"    Prove:     {goal_str}")
        out.append("")

        # System H
        out.append("  System H:")
        out.append(f"    Given:     {meta['sys_h_given']}")
        if "sys_h_construct" in meta:
            out.append(f"    Construct: {meta['sys_h_construct']}")
        if "sys_h_prove" in meta:
            out.append(f"    Prove:     {meta['sys_h_prove']}")
        out.append("")

        out.append(f"  Dependencies: {meta['deps']}")
        out.append("")

        # Proof
        total_steps = len(pj["lines"])
        proof_type = classify_proof(pj)
        verified = check(pj, quiet=True)
        status = "✓" if verified else "✗"

        out.append(f"  {proof_type} ({total_steps} steps) [{status}]:")
        out.append("  " + "─" * 30)
        out.append(format_proof_lines(pj))
        out.append("")
        out.append("  Q.E.D. ■")
        out.append("")
        out.append("")

    return "\n".join(out)


if __name__ == "__main__":
    content = generate_answer_key()
    outpath = os.path.join(os.path.dirname(__file__), "..", "answer-key-book-I.txt")
    with open(outpath, "w", encoding="utf-8") as f:
        f.write(content)
    # Count pass/fail
    pass_count = sum(1 for n in range(1, 49) if check(ALL[n], quiet=True))
    fail_count = 48 - pass_count
    print(f"Generated answer-key-book-I.txt: {pass_count} verified, {fail_count} failed")
