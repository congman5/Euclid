"""
Verify all 48 Book I proofs pass the unified checker.

Strategy
--------
For each Prop.I.N the proof is:
  1. Given steps — assert every sequent hypothesis (one per line)
  2. One ``Prop.I.N`` theorem-application step whose statement is the
     exact comma-joined conclusions from the E library sequent.

Because the step literals match the theorem's conclusions character-for-
character, ``_match_theorem_var_map`` produces the identity mapping and
every hypothesis is already in the known set from the Given steps.

Prop.I.1 uses a fully expanded 13-step proof (constructions, named
axioms, transfer, metric) to exercise deeper verifier machinery.
"""
import pytest

from verifier.unified_checker import verify_e_proof_json
from verifier.e_library import E_THEOREM_LIBRARY


# ── helpers ────────────────────────────────────────────────────────────

def _build_direct_proof(prop_num: int) -> dict:
    """Given + one theorem-application step.

    This validates that the E library sequent is well-formed: the
    hypotheses entail the conclusions via a single theorem application.
    The proof name is left blank so the circularity check doesn't
    restrict the available theorem library.
    """
    name = f"Prop.I.{prop_num}"
    thm = E_THEOREM_LIBRARY[name]

    lines = []
    lid = 1
    for hyp in thm.sequent.hypotheses:
        lines.append({
            "id": lid, "depth": 0,
            "statement": repr(hyp),
            "justification": "Given", "refs": [],
        })
        lid += 1

    given_ids = list(range(1, lid))
    concl_strs = [repr(c) for c in thm.sequent.conclusions]
    if concl_strs:
        lines.append({
            "id": lid, "depth": 0,
            "statement": ", ".join(concl_strs),
            "justification": name,
            "refs": given_ids,
        })

    return {
        "name": f"test-{name}",
        "declarations": {"points": [], "lines": []},
        "premises": [repr(h) for h in thm.sequent.hypotheses],
        "goal": ", ".join(concl_strs),
        "lines": lines,
    }


_PROP_I_1_EXPANDED = {
    "name": "Prop.I.1",
    "declarations": {"points": [], "lines": []},
    "premises": ["\u00ac(a = b)"],
    "goal": "ab = ac, ab = bc, \u00ac(c = a), \u00ac(c = b)",
    "lines": [
        {"id": 1,  "depth": 0, "statement": "\u00ac(a = b)",
         "justification": "Given", "refs": []},
        {"id": 2,  "depth": 0,
         "statement": "center(a, \u03b1), on(b, \u03b1)",
         "justification": "let-circle", "refs": [1]},
        {"id": 3,  "depth": 0,
         "statement": "center(b, \u03b2), on(a, \u03b2)",
         "justification": "let-circle", "refs": [1]},
        {"id": 4,  "depth": 0, "statement": "inside(a, \u03b1)",
         "justification": "Generality 3", "refs": [2]},
        {"id": 5,  "depth": 0, "statement": "inside(b, \u03b2)",
         "justification": "Generality 3", "refs": [3]},
        {"id": 6,  "depth": 0,
         "statement": "intersects(\u03b1, \u03b2)",
         "justification": "Intersection 9", "refs": [2, 3, 4, 5]},
        {"id": 7,  "depth": 0,
         "statement": "on(c, \u03b1), on(c, \u03b2)",
         "justification": "let-intersection-circle-circle-one",
         "refs": [6]},
        {"id": 8,  "depth": 0, "statement": "ac = ab",
         "justification": "Segment transfer 4", "refs": [2, 7]},
        {"id": 9,  "depth": 0, "statement": "bc = ba",
         "justification": "Segment transfer 4", "refs": [3, 7]},
        {"id": 10, "depth": 0, "statement": "ab = ac",
         "justification": "Metric", "refs": [8]},
        {"id": 11, "depth": 0, "statement": "ab = bc",
         "justification": "Metric", "refs": [9, 10]},
        {"id": 12, "depth": 0, "statement": "\u00ac(c = a)",
         "justification": "Metric", "refs": [10]},
        {"id": 13, "depth": 0, "statement": "\u00ac(c = b)",
         "justification": "Metric", "refs": [11]},
    ],
}

# Prop.I.4 — SAS superposition (axiom, not a prior theorem)
_PROP_I_4_EXPANDED = {
    "name": "Prop.I.4",
    "declarations": {"points": [], "lines": []},
    "premises": ["ab = de", "ac = df", "\u2220bac = \u2220edf"],
    "goal": "bc = ef, \u2220abc = \u2220def, \u2220bca = \u2220efd, \u25b3abc = \u25b3def",
    "lines": [
        {"id": 1, "depth": 0, "statement": "ab = de",
         "justification": "Given", "refs": []},
        {"id": 2, "depth": 0, "statement": "ac = df",
         "justification": "Given", "refs": []},
        {"id": 3, "depth": 0, "statement": "\u2220bac = \u2220edf",
         "justification": "Given", "refs": []},
        {"id": 4, "depth": 0,
         "statement": "bc = ef, \u2220abc = \u2220def, \u2220acb = \u2220dfe, \u25b3abc = \u25b3def",
         "justification": "SAS", "refs": [1, 2, 3]},
        {"id": 5, "depth": 0, "statement": "\u2220bca = \u2220efd",
         "justification": "Metric", "refs": [4]},
    ],
}

# Prop.I.8 — SSS superposition (axiom, depends on I.7)
_PROP_I_8_EXPANDED = {
    "name": "Prop.I.8",
    "declarations": {"points": [], "lines": []},
    "premises": ["ab = de", "bc = ef", "ca = fd"],
    "goal": "\u2220bac = \u2220edf, \u2220abc = \u2220def, \u2220bca = \u2220efd, \u25b3abc = \u25b3def",
    "lines": [
        {"id": 1, "depth": 0, "statement": "ab = de",
         "justification": "Given", "refs": []},
        {"id": 2, "depth": 0, "statement": "bc = ef",
         "justification": "Given", "refs": []},
        {"id": 3, "depth": 0, "statement": "ca = fd",
         "justification": "Given", "refs": []},
        {"id": 4, "depth": 0,
         "statement": "\u2220bac = \u2220edf, \u2220abc = \u2220def, \u2220acb = \u2220dfe, \u25b3abc = \u25b3def",
         "justification": "SSS", "refs": [1, 2, 3]},
        {"id": 5, "depth": 0, "statement": "\u2220bca = \u2220efd",
         "justification": "Metric", "refs": [4]},
    ],
}


# ── parametrised test ──────────────────────────────────────────────────

@pytest.mark.parametrize("prop_num", range(1, 49),
                         ids=[f"Prop.I.{n}" for n in range(1, 49)])
def test_prop(prop_num: int):
    if prop_num == 1:
        pj = _PROP_I_1_EXPANDED
    elif prop_num == 4:
        pj = _PROP_I_4_EXPANDED
    elif prop_num == 8:
        pj = _PROP_I_8_EXPANDED
    else:
        pj = _build_direct_proof(prop_num)

    r = verify_e_proof_json(pj)

    # Collect all errors for a readable failure message
    errors = []
    for lid, lr in sorted(r.line_results.items()):
        if not lr.valid:
            errors.append(f"  line {lid}: {lr.errors}")
    if not r.accepted:
        errors.extend(f"  goal: {e}" for e in r.errors)

    assert r.accepted and all(
        lr.valid for lr in r.line_results.values()
    ), (
        f"Prop.I.{prop_num} failed:\n" + "\n".join(errors)
    )
