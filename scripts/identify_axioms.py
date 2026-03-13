"""Identify the specific axiom/rule used for each step of passing proofs.

For each proof step justified by a generic category (Diagrammatic, Metric,
Transfer), determines which specific named axiom was used.
"""
import sys
sys.path.insert(0, '.')

from verifier.e_parser import parse_literal_list
from verifier.e_ast import (
    Sort, Literal, On, Between, SameSide, Center, Inside,
    Intersects, Equals, LessThan, SegmentTerm, AngleTerm,
    AreaTerm, MagAdd, RightAngle, ZeroMag, BOTTOM,
)
from verifier.e_consequence import ConsequenceEngine
from verifier.e_axioms import (
    GENERALITY_AXIOMS, BETWEEN_AXIOMS, SAME_SIDE_AXIOMS,
    PASCH_AXIOMS, TRIPLE_INCIDENCE_AXIOMS, CIRCLE_AXIOMS,
    INTERSECTION_AXIOMS, ALL_DIAGRAMMATIC_AXIOMS,
    DIAGRAM_SEGMENT_TRANSFER, DIAGRAM_ANGLE_TRANSFER,
    DIAGRAM_AREA_TRANSFER,
)
from verifier.e_transfer import TransferEngine
from verifier.e_metric import MetricEngine
from verifier.unified_checker import verify_e_proof_json
from scripts.real_proofs import ALL


# ── Diagrammatic axiom groups with names ──
DIAG_GROUPS = [
    ("Generality", GENERALITY_AXIOMS, [
        "G1 — Two points on two lines → equal",
        "G2 — Center uniqueness",
        "G3 — Center is inside",
        "G4 — Inside excludes on",
    ]),
    ("Betweenness", BETWEEN_AXIOMS, [
        "B1 — between(a,b,c) → between(c,b,a)",
        "B2 — between(a,b,c) → a ≠ b",
        "B3 — between(a,b,c) → a ≠ c",
        "B4 — between(a,b,c) → ¬between(b,a,c)",
        "B5a — between + on → on (variant 1)",
        "B5b — between + on → on (variant 2)",
        "B7 — between(a,b,c) ∧ between(a,d,b) → between(a,d,c)",
        "B8 — between(a,b,c) ∧ between(b,c,d) → between(a,b,d)",
        "B6 — Three collinear: one between others",
        "B9 — between(a,b,c) ∧ between(a,b,d) → ¬between(b,c,d)",
    ]),
    ("Same-side", SAME_SIDE_AXIOMS, [
        "SS1 — same-side(a,a,L) ∨ on(a,L)",
        "SS2 — same-side(a,b,L) → same-side(b,a,L)",
        "SS3 — same-side(a,b,L) → ¬on(a,L)",
        "SS4 — same-side transitivity",
        "SS5 — Two points off L: same-side or opposite",
    ]),
    ("Pasch", PASCH_AXIOMS, [
        "P1 — same-side + between → same-side",
        "P2 — between + on → same-side (or on)",
        "P3 — between + on(midpoint) → ¬same-side",
        "P4 — Pasch's axiom",
    ]),
    ("Triple incidence", TRIPLE_INCIDENCE_AXIOMS, [
        "TI1 — Three concurrent lines",
        "TI2 — Concurrent same-side transitivity",
        "TI3 — Five-line same-side",
    ]),
    ("Circle", CIRCLE_AXIOMS, [
        "C1 — Chord interior: between(b,a,c)",
        "C2a — inside+inside+between → inside",
        "C2b — inside+on+between → inside",
        "C2c — on+inside+between → inside",
        "C2d — on+on+between → inside",
        "C3a — inside+¬inside+between → ¬inside",
        "C3b — inside+¬inside+between → ¬on",
        "C3c — on+¬inside+between → ¬inside",
        "C3d — on+¬inside+between → ¬on",
        "C4 — Two circle intersections on opposite sides",
    ]),
    ("Intersection", INTERSECTION_AXIOMS, [
        "I1 — ¬same-side → lines intersect",
        "I2a — on+on opposite sides → L intersects α",
        "I2b — on+inside opposite sides → L intersects α",
        "I2c — inside+on opposite sides → L intersects α",
        "I2d — inside+inside opposite sides → L intersects α",
        "I3 — inside + on(a,L) → intersects(L,α)",
        "I4 — on+on circles: ¬inside+¬on → intersects",
        "I5 — on+inside mixed → intersects",
        "I9 — inside+inside → intersects",
    ]),
]

# ── Transfer axiom groups with names ──
TRANSFER_GROUPS = [
    ("Segment transfer", DIAGRAM_SEGMENT_TRANSFER, [
        "DS1 — between → segment addition",
        "DS2 — equal radii → same circle",
        "DS3a — segment = radius → on circle",
        "DS3b — on circle → segment = radius",
        "DS4a — segment < radius → inside",
        "DS4b — inside → segment < radius",
        "DS3c (DS4c) — radius < segment → ¬inside",
        "DS3d (DS4d) — radius < segment → ¬on",
    ]),
    ("Angle transfer", DIAGRAM_ANGLE_TRANSFER, [
        "DA1a — collinear same-ray → angle = 0",
        "DA1b — angle = 0 → on line",
        "DA1c — angle = 0 → ¬between",
        "DA2 — angle addition (same-side decomposition)",
        "DA2b — angle addition → same-side (variant 1)",
        "DA2c — angle addition → same-side (variant 2)",
        "DA3a — supplementary → right-angle",
        "DA3b — right-angle → supplementary",
        "DA4 — angle extension (¬between → equal angles)",
        "DA5a — parallel postulate: angles < 2R → intersect",
        "DA5b — parallel postulate: intersection same-side",
    ]),
    ("Area transfer", DIAGRAM_AREA_TRANSFER, [
        "DAr1a — area = 0 → collinear",
        "DAr1b — collinear → area = 0",
        "DAr1c — non-collinear → area ≠ 0",
        "DAr2 — between → area addition",
    ]),
]


def identify_diag_axiom(known, lit, variables):
    """Try each diag axiom group individually to find which derives lit."""
    # First try single-axiom identification
    for group_name, axioms, names in DIAG_GROUPS:
        for i, axiom in enumerate(axioms):
            ce = ConsequenceEngine([axiom])
            closure = ce.direct_consequences(known, variables)
            if lit in closure:
                name = names[i] if i < len(names) else f"{group_name} {i+1}"
                return name

    # Try each group as a whole (some facts need 2+ axioms from same group)
    for group_name, axioms, names in DIAG_GROUPS:
        ce = ConsequenceEngine(axioms)
        closure = ce.direct_consequences(known, variables)
        if lit in closure:
            return f"{group_name} (multi-step)"

    # Try full closure and identify by removing groups
    ce = ConsequenceEngine(ALL_DIAGRAMMATIC_AXIOMS)
    closure = ce.direct_consequences(known, variables)
    if BOTTOM in closure:
        return "Contradiction (BOTTOM in closure)"
    if lit in closure:
        # Try removing each group to find which is essential
        for group_name, axioms, names in DIAG_GROUPS:
            remaining = [a for a in ALL_DIAGRAMMATIC_AXIOMS if a not in axioms]
            ce2 = ConsequenceEngine(remaining)
            closure2 = ce2.direct_consequences(known, variables)
            if lit not in closure2:
                return f"{group_name} (in full closure)"
        return "Diagrammatic (multiple groups)"
    return "Diagrammatic (?)"


def identify_transfer_axiom(known, lit, variables):
    """Try each transfer axiom individually to find which derives lit."""
    # Run full diag closure first
    ce = ConsequenceEngine(ALL_DIAGRAMMATIC_AXIOMS)
    closure = ce.direct_consequences(known, variables)
    combined = known | closure
    dk = {l for l in combined if l.is_diagrammatic}
    mk = {l for l in combined if l.is_metric}

    for group_name, axioms, names in TRANSFER_GROUPS:
        for i, axiom in enumerate(axioms):
            te = TransferEngine([axiom])
            derived = te.apply_transfers(dk, mk, variables)
            if lit in derived:
                name = names[i] if i < len(names) else f"{group_name} {i+1}"
                return name
    # Try with all transfer axioms
    all_transfer = (DIAGRAM_SEGMENT_TRANSFER + DIAGRAM_ANGLE_TRANSFER
                    + DIAGRAM_AREA_TRANSFER)
    te = TransferEngine(all_transfer)
    derived = te.apply_transfers(dk, mk, variables)
    if lit in derived:
        # Find which group is essential
        for group_name, axioms, names in TRANSFER_GROUPS:
            remaining = [a for a in all_transfer if a not in axioms]
            te2 = TransferEngine(remaining)
            derived2 = te2.apply_transfers(dk, mk, variables)
            if lit not in derived2:
                return f"{group_name} (in full transfer)"
        return "Transfer (multiple)"
    return "Transfer (?)"


def identify_metric_rule(known, lit):
    """Identify which metric rule derives lit."""
    atom = lit.atom
    if not lit.polarity and isinstance(atom, Equals):
        # ¬(a = b) — from M1 (ab ≠ 0 → a ≠ b) or transitivity
        if isinstance(atom.left, str) and isinstance(atom.right, str):
            return "M1 — Zero segment (a≠b)"
        # ¬(magnitude = magnitude)
        return "Metric (magnitude ≠)"
    if lit.polarity and isinstance(atom, Equals):
        lhs, rhs = atom.left, atom.right
        # a = a reflexivity
        if lhs == rhs:
            return "CN4 — Reflexivity"
        # segment symmetry ab = ba
        if (isinstance(lhs, SegmentTerm) and isinstance(rhs, SegmentTerm)
                and lhs.p1 == rhs.p2 and lhs.p2 == rhs.p1):
            return "M3 — Symmetry"
        # angle symmetry
        if (isinstance(lhs, AngleTerm) and isinstance(rhs, AngleTerm)
                and lhs.p2 == rhs.p2):
            if lhs.p1 == rhs.p3 and lhs.p3 == rhs.p1:
                return "M4 — Angle symmetry"
        # area symmetry
        if isinstance(lhs, AreaTerm) and isinstance(rhs, AreaTerm):
            s1 = tuple(sorted([lhs.p1, lhs.p2, lhs.p3]))
            s2 = tuple(sorted([rhs.p1, rhs.p2, rhs.p3]))
            if s1 == s2 and (lhs.p1, lhs.p2, lhs.p3) != (rhs.p1, rhs.p2, rhs.p3):
                return "M8 — Area symmetry"
        # 0-magnitude
        if isinstance(rhs, ZeroMag) or (isinstance(rhs, str) and rhs == '0'):
            return "M1 — Zero segment"
        if isinstance(lhs, ZeroMag) or (isinstance(lhs, str) and lhs == '0'):
            return "M1 — Zero segment"
        # point equality d = a from M1 (magnitude = 0 → equal)
        if isinstance(lhs, str) and isinstance(rhs, str):
            return "M1 — Zero segment (d=a)"
        # General equality — likely transitivity
        return "CN1 — Transitivity"
    if lit.polarity and isinstance(atom, LessThan):
        # Check for CN5 pattern: x < x + y where y > 0
        return "CN5 — Whole > Part"
    if not lit.polarity and isinstance(atom, LessThan):
        return "< trichotomy (negation)"
    return "Metric (?)"


def analyze_proof(prop_num):
    """Analyze a proof and identify specific axioms for each step."""
    proof = ALL[prop_num]
    print(f"\n{'='*70}")
    print(f"  I.{prop_num} — {proof['name']}")
    print(f"{'='*70}")
    print(f"  Goal: {proof.get('goal', '')}")

    sort_ctx = {}
    known = set()
    variables = {}
    ce_tmp = ConsequenceEngine(axioms=[])

    for prem in proof.get('premises', []):
        for lit in parse_literal_list(prem, sort_ctx):
            known.add(lit)
            ce_tmp._collect_atom_var_sorts(lit.atom, variables)

    for line in proof['lines']:
        lid = line['id']
        stmt = line['statement']
        just = line['justification']
        depth = line.get('depth', 0)
        indent = '  ' * depth

        # Parse statement
        try:
            step_lits = parse_literal_list(stmt, sort_ctx)
        except Exception:
            step_lits = []

        specific = just  # default: use the justification as-is

        if just in ("Diagrammatic", "diagrammatic"):
            # Run full closure first
            ce = ConsequenceEngine(ALL_DIAGRAMMATIC_AXIOMS)
            closure = ce.direct_consequences(known, variables)
            for lit in step_lits:
                if lit not in known:
                    ax = identify_diag_axiom(known, lit, variables)
                    specific = ax
                    break

        elif just in ("Metric", "metric"):
            for lit in step_lits:
                if lit not in known:
                    specific = identify_metric_rule(known, lit)
                    break

        elif just in ("Transfer", "transfer"):
            # Run diag closure first
            ce = ConsequenceEngine(ALL_DIAGRAMMATIC_AXIOMS)
            closure = ce.direct_consequences(known, variables)
            combined = known | closure
            for lit in step_lits:
                if lit not in known:
                    ax = identify_transfer_axiom(combined, lit, variables)
                    specific = ax
                    break

        print(f"  {indent}{lid:>2}. [{specific}]")
        print(f"  {indent}      → {stmt}")

        # Add to known
        for lit in step_lits:
            known.add(lit)
            ce_tmp._collect_atom_var_sorts(lit.atom, variables)


if __name__ == '__main__':
    for n in [1, 2, 3, 4, 5, 6, 7, 8, 9, 10]:
        analyze_proof(n)
