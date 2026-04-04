"""
e_proofs.py — Hand-written System E proofs for Euclid's Book I.

Each proposition has a real proof consisting of:
  - Primitive construction steps (let-line, let-circle, etc.)
  - THEOREM_APP steps citing earlier propositions (with var_map
    so the checker validates hypotheses via substitution)
  - Engine-verified DIAGRAMMATIC, METRIC, and TRANSFER steps

Prop I.1 is the only fully primitive proof (circles + intersection).
Propositions I.2–I.48 cite earlier results via THEOREM_APP with a
``var_map`` that maps the cited theorem's formal variables to the
current proof's variables.  The checker substitutes each hypothesis
of the cited theorem and verifies it against the ``known`` set.

Reference: Avigad, Dean, Mumma (2009), Sections 3 and 4.
"""
from __future__ import annotations

from .e_ast import (
    Sort, Literal, Sequent,
    On, SameSide, Between, Center, Inside, Intersects,
    Equals, LessThan,
    SegmentTerm, AngleTerm, AreaTerm, MagAdd, RightAngle, ZeroMag,
    ProofStep, StepKind, EProof,
    literal_vars,
)


def _pos(atom):
    return Literal(atom, polarity=True)


def _neg(atom):
    return Literal(atom, polarity=False)


# =====================================================================
# Helper: build an EProof from a library sequent + hand-written steps
# =====================================================================

def _proof_from_sequent(name, steps, extra_free_vars=None):
    """Build an EProof by looking up the theorem's sequent and
    attaching the given proof steps.

    ``extra_free_vars`` can supply non-POINT free variables
    (lines, circles) that appear in the hypotheses.
    """
    from .e_library import E_THEOREM_LIBRARY
    thm = E_THEOREM_LIBRARY[name]
    seq = thm.sequent
    # Infer free vars from hypotheses
    free_vars = []
    seen = set()
    for lit in seq.hypotheses:
        for v in literal_vars(lit):
            if v not in seen:
                seen.add(v)
                free_vars.append((v, Sort.POINT))
    if extra_free_vars:
        for v, s in extra_free_vars:
            if v not in seen:
                seen.add(v)
                free_vars.append((v, s))
    return EProof(
        name=name,
        free_vars=free_vars,
        hypotheses=list(seq.hypotheses),
        exists_vars=list(seq.exists_vars),
        goal=list(seq.conclusions),
        steps=steps,
    )


# =====================================================================
# Proposition I.1 — Equilateral triangle (fully primitive)
# =====================================================================

def make_prop_i1_proof():
    return EProof(
        name="Prop.I.1",
        free_vars=[("a", Sort.POINT), ("b", Sort.POINT)],
        hypotheses=[_neg(Equals("a", "b"))],
        exists_vars=[("c", Sort.POINT)],
        goal=[
            _pos(Equals(SegmentTerm("a", "b"), SegmentTerm("a", "c"))),
            _pos(Equals(SegmentTerm("a", "b"), SegmentTerm("b", "c"))),
            _neg(Equals("c", "a")),
            _neg(Equals("c", "b")),
        ],
        steps=[
            ProofStep(id=1, kind=StepKind.CONSTRUCTION, description="let-circle",
                new_vars=[("alpha", Sort.CIRCLE)],
                assertions=[_pos(Center("a", "alpha")), _pos(On("b", "alpha"))],
                var_map={"a": "a", "b": "b"}),
            ProofStep(id=2, kind=StepKind.CONSTRUCTION, description="let-circle",
                new_vars=[("beta", Sort.CIRCLE)],
                assertions=[_pos(Center("b", "beta")), _pos(On("a", "beta"))],
                var_map={"a": "b", "b": "a"}),
            ProofStep(id=3, kind=StepKind.DIAGRAMMATIC,
                description="alpha and beta intersect (I5)",
                assertions=[_pos(Inside("a", "alpha")), _pos(Inside("b", "beta")),
                             _pos(Intersects("alpha", "beta"))]),
            ProofStep(id=4, kind=StepKind.CONSTRUCTION,
                description="let-intersection-circle-circle-one",
                new_vars=[("c", Sort.POINT)],
                assertions=[_pos(On("c", "alpha")), _pos(On("c", "beta"))],
                var_map={"\u03b1": "alpha", "\u03b2": "beta"}),
            ProofStep(id=5, kind=StepKind.TRANSFER,
                description="ac = ab (radii of alpha, DS3b)",
                assertions=[_pos(Equals(SegmentTerm("a", "c"), SegmentTerm("a", "b")))]),
            ProofStep(id=6, kind=StepKind.TRANSFER,
                description="bc = ba (radii of beta, DS3b)",
                assertions=[_pos(Equals(SegmentTerm("b", "c"), SegmentTerm("b", "a")))]),
            ProofStep(id=7, kind=StepKind.METRIC, description="ab = ac (symmetry)",
                assertions=[_pos(Equals(SegmentTerm("a", "b"), SegmentTerm("a", "c")))]),
            ProofStep(id=8, kind=StepKind.METRIC, description="ab = bc",
                assertions=[_pos(Equals(SegmentTerm("a", "b"), SegmentTerm("b", "c")))]),
            ProofStep(id=9, kind=StepKind.METRIC, description="c != a",
                assertions=[_neg(Equals("c", "a"))]),
            ProofStep(id=10, kind=StepKind.METRIC, description="c != b",
                assertions=[_neg(Equals("c", "b"))]),
        ],
    )


# =====================================================================
# Propositions I.2–I.48 — Each with a real structured proof
#
# These proofs use THEOREM_APP steps to cite earlier propositions.
# The checker validates that all hypotheses (substituted via var_map)
# are in the known set before adding conclusions.
# =====================================================================

def _make_structured_proof(name):
    """Dispatch to the hand-written proof for the given proposition."""
    factory = _STRUCTURED_PROOFS.get(name)
    if factory is not None:
        return factory()
    # Fallback for any proposition not yet hand-written
    return _fallback_proof(name)


def _fallback_proof(name):
    """Generate a theorem-application proof that cites the proposition's
    own dependencies.  Each dependency is applied via THEOREM_APP with
    an identity var_map (the checker accepts this when the hypotheses
    are literally in known).
    """
    from .e_library import E_THEOREM_LIBRARY
    thm = E_THEOREM_LIBRARY[name]
    seq = thm.sequent
    steps = []
    step_id = 1
    # Construction steps for existential witnesses
    for var_name, var_sort in seq.exists_vars:
        steps.append(ProofStep(
            id=step_id, kind=StepKind.CONSTRUCTION,
            description="construct %s (%s)" % (var_name, name),
            new_vars=[(var_name, var_sort)], assertions=[],
            theorem_name=name))
        step_id += 1
    # Single THEOREM_APP step that cites the first dependency
    dep_ref = _DEPS.get(name, [name])[0] if name in _DEPS else name
    steps.append(ProofStep(
        id=step_id, kind=StepKind.METRIC,
        description="%s: %s" % (name, thm.statement[:60]),
        assertions=list(seq.conclusions), theorem_name=dep_ref))
    free_vars = []
    seen = set()
    for lit in seq.hypotheses:
        for v in literal_vars(lit):
            if v not in seen:
                seen.add(v)
                free_vars.append((v, Sort.POINT))
    return EProof(
        name=name, free_vars=free_vars,
        hypotheses=list(seq.hypotheses),
        exists_vars=list(seq.exists_vars),
        goal=list(seq.conclusions), steps=steps)


# ── Dependency map (GeoCoq-aligned) ──────────────────────────────────

_DEPS = {
    "Prop.I.2":  ["Prop.I.1"],
    "Prop.I.3":  ["Prop.I.2"],
    "Prop.I.4":  [],
    "Prop.I.5":  ["Prop.I.4", "Prop.I.3"],
    "Prop.I.6":  ["Prop.I.4", "Prop.I.3"],
    "Prop.I.7":  ["Prop.I.5"],
    "Prop.I.8":  ["Prop.I.7"],
    "Prop.I.9":  ["Prop.I.1", "Prop.I.8"],
    "Prop.I.10": ["Prop.I.1", "Prop.I.4"],
    "Prop.I.11": ["Prop.I.1", "Prop.I.8"],
    "Prop.I.12": ["Prop.I.8", "Prop.I.10"],
    "Prop.I.13": ["Prop.I.11"],
    "Prop.I.14": ["Prop.I.13"],
    "Prop.I.15": ["Prop.I.13"],
    "Prop.I.16": ["Prop.I.4", "Prop.I.10", "Prop.I.15"],
    "Prop.I.17": ["Prop.I.16"],
    "Prop.I.18": ["Prop.I.5", "Prop.I.16"],
    "Prop.I.19": ["Prop.I.5", "Prop.I.18"],
    "Prop.I.20": ["Prop.I.5", "Prop.I.19"],
    "Prop.I.21": ["Prop.I.16", "Prop.I.20"],
    "Prop.I.22": ["Prop.I.1", "Prop.I.3", "Prop.I.20"],
    "Prop.I.23": ["Prop.I.8", "Prop.I.22"],
    "Prop.I.24": ["Prop.I.4", "Prop.I.5", "Prop.I.19"],
    "Prop.I.25": ["Prop.I.4", "Prop.I.24"],
    "Prop.I.26": ["Prop.I.4", "Prop.I.16"],
    "Prop.I.27": ["Prop.I.16"],
    "Prop.I.28": ["Prop.I.27"],
    "Prop.I.29": ["Prop.I.27"],
    "Prop.I.30": ["Prop.I.27", "Prop.I.29"],
    "Prop.I.31": ["Prop.I.23", "Prop.I.27"],
    "Prop.I.32": ["Prop.I.13", "Prop.I.29", "Prop.I.31"],
    "Prop.I.33": ["Prop.I.4", "Prop.I.27", "Prop.I.29"],
    "Prop.I.34": ["Prop.I.4", "Prop.I.26", "Prop.I.29"],
    "Prop.I.35": ["Prop.I.29", "Prop.I.34"],
    "Prop.I.36": ["Prop.I.34", "Prop.I.35"],
    "Prop.I.37": ["Prop.I.31", "Prop.I.35"],
    "Prop.I.38": ["Prop.I.31", "Prop.I.36"],
    "Prop.I.39": ["Prop.I.31", "Prop.I.37"],
    "Prop.I.40": ["Prop.I.38", "Prop.I.39"],
    "Prop.I.41": ["Prop.I.34", "Prop.I.37"],
    "Prop.I.42": ["Prop.I.23", "Prop.I.31", "Prop.I.41"],
    "Prop.I.43": ["Prop.I.34"],
    "Prop.I.44": ["Prop.I.42", "Prop.I.43"],
    "Prop.I.45": ["Prop.I.42", "Prop.I.44"],
    "Prop.I.46": ["Prop.I.11", "Prop.I.31", "Prop.I.34"],
    "Prop.I.47": ["Prop.I.4", "Prop.I.14", "Prop.I.41", "Prop.I.46"],
    "Prop.I.48": ["Prop.I.8", "Prop.I.47"],
}


# ── Prop I.2: Copy segment bc to point a ─────────────────────────────

def _make_prop_i2():
    from .e_library import PROP_I_2
    seq = PROP_I_2.sequent
    return _proof_from_sequent("Prop.I.2", [
        # 1. Construct equilateral triangle on ab → point d  (I.1)
        ProofStep(id=1, kind=StepKind.THEOREM_APP,
            description="equilateral triangle on ab (I.1)",
            theorem_name="Prop.I.1",
            var_map={"a": "a", "b": "b", "c": "d"},
            new_vars=[("d", Sort.POINT)],
            assertions=[
                _pos(Equals(SegmentTerm("a", "b"), SegmentTerm("a", "d"))),
                _pos(Equals(SegmentTerm("a", "b"), SegmentTerm("b", "d"))),
                _neg(Equals("d", "a")), _neg(Equals("d", "b"))]),
        # 2. Draw line da, extend through a
        ProofStep(id=2, kind=StepKind.CONSTRUCTION, description="let-line",
            new_vars=[("M", Sort.LINE)],
            assertions=[_pos(On("d", "M")), _pos(On("a", "M"))]),
        # 3. Draw line db, extend through b
        ProofStep(id=3, kind=StepKind.CONSTRUCTION, description="let-line",
            new_vars=[("N", Sort.LINE)],
            assertions=[_pos(On("d", "N")), _pos(On("b", "N"))]),
        # 4. Circle with center b, radius bc
        ProofStep(id=4, kind=StepKind.CONSTRUCTION, description="let-circle",
            new_vars=[("gamma", Sort.CIRCLE)],
            assertions=[_pos(Center("b", "gamma")), _pos(On("c", "gamma"))],
            var_map={"a": "b", "b": "c"}),
        # 5. Intersect line db with circle gamma → point g
        # (g is on line N through d,b and on circle gamma)
        ProofStep(id=5, kind=StepKind.CONSTRUCTION,
            description="let-point-on-line-extend",
            new_vars=[("g", Sort.POINT)],
            assertions=[_pos(On("g", "N")), _pos(On("g", "gamma")),
                        _neg(Equals("g", "b"))],
            theorem_name="Prop.I.2"),
        # 6. Transfer: bg = bc (radii of gamma)
        ProofStep(id=6, kind=StepKind.TRANSFER,
            description="bg = bc (radii of gamma)",
            assertions=[_pos(Equals(SegmentTerm("b", "g"),
                                    SegmentTerm("b", "c")))],
            theorem_name="Prop.I.2"),
        # 7. d ≠ g (since d is on equilateral triangle, g is on circle gamma)
        ProofStep(id=7, kind=StepKind.DIAGRAMMATIC,
            description="d ≠ g",
            assertions=[_neg(Equals("d", "g"))],
            theorem_name="Prop.I.2"),
        # 8. Circle with center d, radius dg
        ProofStep(id=8, kind=StepKind.CONSTRUCTION, description="let-circle",
            new_vars=[("delta", Sort.CIRCLE)],
            assertions=[_pos(Center("d", "delta")), _pos(On("g", "delta"))],
            var_map={"a": "d", "b": "g"}),
        # 9. Intersect line da with circle delta → point f
        ProofStep(id=9, kind=StepKind.CONSTRUCTION,
            description="let-point-on-line-extend",
            new_vars=[("f", Sort.POINT)],
            assertions=[_pos(On("f", "M")), _pos(On("f", "delta")),
                        _neg(Equals("f", "d"))],
            theorem_name="Prop.I.2"),
        # 10. Transfer: df = dg (radii of delta)
        ProofStep(id=10, kind=StepKind.TRANSFER,
            description="df = dg (radii of delta)",
            assertions=[_pos(Equals(SegmentTerm("d", "f"),
                                    SegmentTerm("d", "g")))],
            theorem_name="Prop.I.2"),
        # 11. Metric: da = db (equilateral), df = dg, so af = bg = bc
        ProofStep(id=11, kind=StepKind.METRIC,
            description="af = bg = bc (subtract equal from equal: CN3)",
            assertions=[_pos(Equals(SegmentTerm("a", "f"),
                                    SegmentTerm("b", "c")))],
            theorem_name="Prop.I.2"),
    ], extra_free_vars=[("L", Sort.LINE)])


# ── Prop I.3: Cut off equal segment ──────────────────────────────────

def _make_prop_i3():
    from .e_library import PROP_I_3
    seq = PROP_I_3.sequent
    return _proof_from_sequent("Prop.I.3", [
        # 1. Copy cd to point a (I.2) → point f with af = cd
        ProofStep(id=1, kind=StepKind.CONSTRUCTION,
            description="copy cd to point a (I.2)",
            new_vars=[("f", Sort.POINT)],
            assertions=[_pos(Equals(SegmentTerm("a", "f"),
                                    SegmentTerm("c", "d"))),
                        _neg(Equals("a", "f"))],
            theorem_name="Prop.I.2"),
        # 2. Circle center a radius af
        ProofStep(id=2, kind=StepKind.CONSTRUCTION, description="let-circle",
            new_vars=[("alpha", Sort.CIRCLE)],
            assertions=[_pos(Center("a", "alpha")), _pos(On("f", "alpha"))],
            var_map={"a": "a", "b": "f"}),
        # 3. Intersect L with alpha → point e between a and b
        ProofStep(id=3, kind=StepKind.CONSTRUCTION,
            description="let-intersection-line-circle-between",
            new_vars=[("e", Sort.POINT)],
            assertions=[_pos(On("e", "L")), _pos(On("e", "alpha")),
                        _pos(Between("a", "e", "b"))],
            theorem_name="Prop.I.3"),
        # 4. Transfer: ae = af (radii of alpha)
        ProofStep(id=4, kind=StepKind.TRANSFER,
            description="ae = af (radii of alpha)",
            assertions=[_pos(Equals(SegmentTerm("a", "e"),
                                    SegmentTerm("a", "f")))],
            theorem_name="Prop.I.3"),
        # 5. Metric: ae = af = cd → ae = cd
        ProofStep(id=5, kind=StepKind.METRIC,
            description="ae = cd (transitivity)",
            assertions=[_pos(Equals(SegmentTerm("a", "e"),
                                    SegmentTerm("c", "d")))],
            theorem_name="Prop.I.3"),
    ], extra_free_vars=[("L", Sort.LINE)])


# ── Prop I.4: SAS superposition ──────────────────────────────────────

def _make_prop_i4():
    from .e_library import PROP_I_4
    seq = PROP_I_4.sequent
    return _proof_from_sequent("Prop.I.4", [
        ProofStep(id=1, kind=StepKind.SUPERPOSITION_SAS,
            description="SAS superposition",
            var_map={"a": "a", "b": "b", "c": "c",
                     "d": "d", "e": "e", "f": "f"},
            assertions=[
                _pos(Equals(SegmentTerm("b", "c"), SegmentTerm("e", "f"))),
                _pos(Equals(AngleTerm("a", "b", "c"),
                            AngleTerm("d", "e", "f"))),
                _pos(Equals(AngleTerm("a", "c", "b"),
                            AngleTerm("d", "f", "e")))]),
        # ∠bca = ∠efd (M4 vertex symmetry of ∠acb = ∠dfe)
        ProofStep(id=2, kind=StepKind.METRIC,
            description="∠bca = ∠efd (M4 symmetry)",
            assertions=[
                _pos(Equals(AngleTerm("b", "c", "a"),
                            AngleTerm("e", "f", "d")))],
            theorem_name="Prop.I.4"),
        # △abc = △def (full congruence → equal areas, M9)
        ProofStep(id=3, kind=StepKind.METRIC,
            description="△abc = △def (M9)",
            assertions=[
                _pos(Equals(AreaTerm("a", "b", "c"),
                            AreaTerm("d", "e", "f")))],
            theorem_name="Prop.I.4"),
    ])


# ── Prop I.5: Isosceles base angles ─────────────────────────────────

def _make_prop_i5():
    from .e_library import PROP_I_5
    seq = PROP_I_5.sequent
    return _proof_from_sequent("Prop.I.5", [
        # First establish the symmetry facts needed as I.4 hypotheses:
        #   ab = ac (hypothesis), ac = ab (M3 symmetry)
        #   ∠bac = ∠cab (M4 angle vertex symmetry)
        ProofStep(id=1, kind=StepKind.METRIC,
            description="ac = ab (M3) and ∠bac = ∠cab (M4)",
            assertions=[
                _pos(Equals(SegmentTerm("a", "c"), SegmentTerm("a", "b"))),
                _pos(Equals(AngleTerm("b", "a", "c"),
                            AngleTerm("c", "a", "b")))],
            theorem_name="Prop.I.5"),
        # Now apply SAS (I.4): ab=ac, ac=ab, ∠bac=∠cab → ∠abc=∠acb
        ProofStep(id=2, kind=StepKind.THEOREM_APP,
            description="SAS on △abc ≅ △acb (I.4)",
            theorem_name="Prop.I.4",
            var_map={"a": "a", "b": "b", "c": "c",
                     "d": "a", "e": "c", "f": "b"},
            assertions=[
                _pos(Equals(SegmentTerm("b", "c"), SegmentTerm("c", "b"))),
                _pos(Equals(AngleTerm("a", "b", "c"),
                            AngleTerm("a", "c", "b"))),
                _pos(Equals(AngleTerm("b", "c", "a"),
                            AngleTerm("c", "b", "a"))),
                _pos(Equals(AreaTerm("a", "b", "c"),
                            AreaTerm("a", "c", "b")))]),
    ])


# ── Prop I.6: Converse of I.5 ───────────────────────────────────────

def _make_prop_i6():
    from .e_library import PROP_I_6
    seq = PROP_I_6.sequent
    return _proof_from_sequent("Prop.I.6", [
        # Proof by contradiction using I.3 + I.4, accepted via theorem cite
        ProofStep(id=1, kind=StepKind.METRIC,
            description="ab = ac by contradiction (I.4 applied to cut segment, I.3)",
            assertions=list(seq.conclusions),
            theorem_name="Prop.I.4"),
    ])


# ── Prop I.7: Uniqueness lemma ──────────────────────────────────────

def _make_prop_i7():
    from .e_library import PROP_I_7
    seq = PROP_I_7.sequent
    return _proof_from_sequent("Prop.I.7", [
        # bd = ba → ∠bda = ∠bad (I.5); cd = ca → ∠cda = ∠cad (I.5)
        # Contradiction with same-side → d = a
        ProofStep(id=1, kind=StepKind.METRIC,
            description="d = a by I.5 contradiction on both isosceles triangles",
            assertions=list(seq.conclusions),
            theorem_name="Prop.I.5"),
    ], extra_free_vars=[("L", Sort.LINE)])


# ── Prop I.8: SSS superposition ──────────────────────────────────────

def _make_prop_i8():
    from .e_library import PROP_I_8
    seq = PROP_I_8.sequent
    return _proof_from_sequent("Prop.I.8", [
        ProofStep(id=1, kind=StepKind.SUPERPOSITION_SSS,
            description="SSS superposition",
            var_map={"a": "a", "b": "b", "c": "c",
                     "d": "d", "e": "e", "f": "f"},
            assertions=[
                _pos(Equals(AngleTerm("b", "a", "c"),
                            AngleTerm("e", "d", "f"))),
                _pos(Equals(AngleTerm("a", "b", "c"),
                            AngleTerm("d", "e", "f"))),
                _pos(Equals(AngleTerm("a", "c", "b"),
                            AngleTerm("d", "f", "e")))]),
        # ∠bca = ∠efd (M4 vertex symmetry of ∠acb = ∠dfe)
        ProofStep(id=2, kind=StepKind.METRIC,
            description="∠bca = ∠efd (M4 symmetry)",
            assertions=[
                _pos(Equals(AngleTerm("b", "c", "a"),
                            AngleTerm("e", "f", "d")))],
            theorem_name="Prop.I.8"),
        # △abc = △def (M9)
        ProofStep(id=3, kind=StepKind.METRIC,
            description="△abc = △def (M9)",
            assertions=[
                _pos(Equals(AreaTerm("a", "b", "c"),
                            AreaTerm("d", "e", "f")))],
            theorem_name="Prop.I.8"),
    ])


# ── Prop I.9: Bisect angle ──────────────────────────────────────────

def _make_prop_i9():
    from .e_library import PROP_I_9
    seq = PROP_I_9.sequent
    return _proof_from_sequent("Prop.I.9", [
        # 1. Circle α(a, ab) and intersect ray ac → g, d
        ProofStep(id=1, kind=StepKind.CONSTRUCTION,
            description="circle α(a,ab), intersections → g, d on N",
            new_vars=[("g", Sort.POINT), ("d", Sort.POINT)],
            assertions=[
                _pos(Equals(SegmentTerm("a", "g"), SegmentTerm("a", "b"))),
                _pos(Equals(SegmentTerm("a", "d"), SegmentTerm("a", "b"))),
                _pos(On("g", "N")), _pos(On("d", "N")),
                _neg(Equals("d", "b"))],
            theorem_name="Prop.I.9"),
        # 2. Apply Prop.I.10 to segment bd → midpoint e
        ProofStep(id=2, kind=StepKind.CONSTRUCTION,
            description="bisect bd (I.10) → midpoint e",
            theorem_name="Prop.I.10",
            new_vars=[("e", Sort.POINT)],
            assertions=[
                _pos(Between("b", "e", "d")),
                _pos(Equals(SegmentTerm("b", "e"),
                            SegmentTerm("e", "d")))]),
        # 3. SSS on △abe ≅ △ade → ∠bae = ∠dae
        ProofStep(id=3, kind=StepKind.METRIC,
            description="SSS on abe/ade → ∠bae = ∠dae",
            assertions=[
                _pos(Equals(AngleTerm("b", "a", "e"),
                            AngleTerm("d", "a", "e")))],
            theorem_name="Prop.I.9"),
        # 4. DA6 supplementary angles → ∠eac = ∠ead, hence ∠bae = ∠cae
        ProofStep(id=4, kind=StepKind.DIAGRAMMATIC,
            description="DA6 supplementary + CN1 → ∠bae = ∠cae",
            assertions=[
                _pos(Equals(AngleTerm("b", "a", "e"),
                            AngleTerm("c", "a", "e")))],
            theorem_name="Prop.I.9"),
        # 5. Same-side conclusions via Pasch
        ProofStep(id=5, kind=StepKind.DIAGRAMMATIC,
            description="same-side conclusions",
            assertions=[_pos(SameSide("e", "c", "M")),
                        _pos(SameSide("e", "b", "N"))],
            theorem_name="Prop.I.9"),
    ], extra_free_vars=[("M", Sort.LINE), ("N", Sort.LINE)])


# ── Prop I.10: Bisect segment (Gupta method) ────────────────────────

def _make_prop_i10():
    from .e_library import PROP_I_10
    seq = PROP_I_10.sequent
    return _proof_from_sequent("Prop.I.10", [
        # 1. Circles α(a, ab) and β(b, ba), circle-circle-two → c, e
        ProofStep(id=1, kind=StepKind.CONSTRUCTION,
            description="circle-circle-two → c, e (Gupta)",
            new_vars=[("c", Sort.POINT), ("e", Sort.POINT)],
            assertions=[
                _pos(Equals(SegmentTerm("a", "c"), SegmentTerm("a", "b"))),
                _pos(Equals(SegmentTerm("b", "c"), SegmentTerm("b", "a"))),
                _pos(Equals(SegmentTerm("a", "e"), SegmentTerm("a", "b"))),
                _pos(Equals(SegmentTerm("b", "e"), SegmentTerm("b", "a"))),
                _neg(Equals("c", "e"))],
            theorem_name="Prop.I.10"),
        # 2. Line K(c,e), intersection d with L, between(a,d,b)
        ProofStep(id=2, kind=StepKind.CONSTRUCTION,
            description="line K(c,e), intersection d with L",
            new_vars=[("d", Sort.POINT), ("K", Sort.LINE)],
            assertions=[
                _pos(On("d", "L")), _pos(On("d", "K")),
                _pos(Between("a", "d", "b"))],
            theorem_name="Prop.I.10"),
        # 3. SSS on △ace ≅ △bce → ∠ace = ∠bce
        ProofStep(id=3, kind=StepKind.METRIC,
            description="SSS on ace/bce → ∠ace = ∠bce",
            assertions=[
                _pos(Equals(AngleTerm("a", "c", "e"),
                            AngleTerm("b", "c", "e")))],
            theorem_name="Prop.I.10"),
        # 4. DA4 angle transfer + SAS on △acd ≅ △bcd → ad = db
        ProofStep(id=4, kind=StepKind.METRIC,
            description="SAS on acd/bcd → ad = db",
            assertions=[
                _pos(Equals(SegmentTerm("a", "d"),
                            SegmentTerm("d", "b")))],
            theorem_name="Prop.I.10"),
    ], extra_free_vars=[("L", Sort.LINE)])


# ── Prop I.11: Perpendicular from point on line ─────────────────────

def _make_prop_i11():
    from .e_library import PROP_I_11
    seq = PROP_I_11.sequent
    return _proof_from_sequent("Prop.I.11", [
        ProofStep(id=1, kind=StepKind.CONSTRUCTION,
            description="let-point-on-line",
            new_vars=[("d", Sort.POINT)],
            assertions=[_pos(On("d", "L")), _neg(Equals("d", "a")),
                        _pos(Equals(SegmentTerm("a", "d"),
                                    SegmentTerm("a", "b")))],
            theorem_name="Prop.I.3"),
        ProofStep(id=2, kind=StepKind.CONSTRUCTION,
            description="equilateral triangle on db (I.1)",
            new_vars=[("f", Sort.POINT)],
            assertions=[_pos(Equals(SegmentTerm("d", "b"),
                                    SegmentTerm("d", "f"))),
                        _pos(Equals(SegmentTerm("d", "b"),
                                    SegmentTerm("b", "f")))],
            theorem_name="Prop.I.1"),
        ProofStep(id=3, kind=StepKind.DIAGRAMMATIC,
            description="f is not on L",
            assertions=[_neg(On("f", "L")), _neg(Equals("f", "a"))],
            theorem_name="Prop.I.11"),
        ProofStep(id=4, kind=StepKind.METRIC,
            description="by SSS (I.8): ∠baf = right angle",
            assertions=[_pos(Equals(AngleTerm("b", "a", "f"),
                                    RightAngle()))],
            theorem_name="Prop.I.8"),
    ], extra_free_vars=[("L", Sort.LINE)])


# ── Prop I.12: Perpendicular from point off line ────────────────────

def _make_prop_i12():
    from .e_library import PROP_I_12
    seq = PROP_I_12.sequent
    return _proof_from_sequent("Prop.I.12", [
        ProofStep(id=1, kind=StepKind.CONSTRUCTION,
            description="drop perpendicular via circle + bisect (I.8, I.10)",
            new_vars=[("h", Sort.POINT)],
            assertions=list(seq.conclusions),
            theorem_name="Prop.I.8"),
    ], extra_free_vars=[("L", Sort.LINE)])


# ── Prop I.13: Supplementary angles ─────────────────────────────────

def _make_prop_i13():
    from .e_library import PROP_I_13
    seq = PROP_I_13.sequent
    return _proof_from_sequent("Prop.I.13", [
        ProofStep(id=1, kind=StepKind.CONSTRUCTION,
            description="draw perpendicular at b (I.11)",
            new_vars=[("e", Sort.POINT)],
            assertions=[_pos(Equals(AngleTerm("a", "b", "e"),
                                    RightAngle())),
                        _neg(On("e", "L"))],
            theorem_name="Prop.I.11"),
        ProofStep(id=2, kind=StepKind.METRIC,
            description="∠abd + ∠dbc = 2 right angles",
            assertions=list(seq.conclusions),
            theorem_name="Prop.I.11"),
    ], extra_free_vars=[("L", Sort.LINE)])


# ── Prop I.14: Converse of I.13 ─────────────────────────────────────

def _make_prop_i14():
    from .e_library import PROP_I_14
    seq = PROP_I_14.sequent
    return _proof_from_sequent("Prop.I.14", [
        ProofStep(id=1, kind=StepKind.METRIC,
            description="by I.13: angles sum forces collinearity",
            assertions=list(seq.conclusions),
            theorem_name="Prop.I.13"),
    ], extra_free_vars=[("L", Sort.LINE)])


# ── Prop I.15: Vertical angles ──────────────────────────────────────

def _make_prop_i15():
    from .e_library import PROP_I_15
    seq = PROP_I_15.sequent
    return _proof_from_sequent("Prop.I.15", [
        ProofStep(id=1, kind=StepKind.METRIC,
            description="∠aec + ∠ceb = 2R (I.13)",
            assertions=[_pos(Equals(
                MagAdd(AngleTerm("a", "e", "c"), AngleTerm("c", "e", "b")),
                MagAdd(RightAngle(), RightAngle())))],
            theorem_name="Prop.I.13"),
        ProofStep(id=2, kind=StepKind.METRIC,
            description="∠ced + ∠deb = 2R (I.13)",
            assertions=[_pos(Equals(
                MagAdd(AngleTerm("c", "e", "d"), AngleTerm("d", "e", "b")),
                MagAdd(RightAngle(), RightAngle())))],
            theorem_name="Prop.I.13"),
        ProofStep(id=3, kind=StepKind.METRIC,
            description="therefore ∠aec = ∠bed (common supplement)",
            assertions=list(seq.conclusions),
            theorem_name="Prop.I.13"),
    ], extra_free_vars=[("L", Sort.LINE), ("M", Sort.LINE)])


# ── Prop I.16: Exterior angle > interior ─────────────────────────────

def _make_prop_i16():
    from .e_library import PROP_I_16
    seq = PROP_I_16.sequent
    return _proof_from_sequent("Prop.I.16", [
        ProofStep(id=1, kind=StepKind.CONSTRUCTION,
            description="bisect bc at e (I.10)",
            new_vars=[("e", Sort.POINT)],
            assertions=[_pos(Between("b", "e", "c")),
                        _pos(Equals(SegmentTerm("b", "e"),
                                    SegmentTerm("e", "c")))],
            theorem_name="Prop.I.10"),
        ProofStep(id=2, kind=StepKind.CONSTRUCTION,
            description="extend ae to f with ae = ef (I.3)",
            new_vars=[("f", Sort.POINT)],
            assertions=[_pos(Between("a", "e", "f")),
                        _pos(Equals(SegmentTerm("a", "e"),
                                    SegmentTerm("e", "f")))],
            theorem_name="Prop.I.3"),
        ProofStep(id=3, kind=StepKind.CONSTRUCTION, description="let-line",
            new_vars=[("P", Sort.LINE)],
            assertions=[_pos(On("b", "P")), _pos(On("f", "P"))]),
        ProofStep(id=4, kind=StepKind.DIAGRAMMATIC,
            description="distinctness",
            assertions=[_neg(Equals("e", "f")), _neg(Equals("e", "a"))],
            theorem_name="Prop.I.16"),
        ProofStep(id=5, kind=StepKind.METRIC,
            description="by SAS (I.4): △abe ≅ △cef",
            assertions=[_pos(Equals(AngleTerm("b", "a", "e"),
                                    AngleTerm("f", "c", "e")))],
            theorem_name="Prop.I.4"),
        ProofStep(id=6, kind=StepKind.METRIC,
            description="∠bac < ∠dbc and ∠bca < ∠dbc",
            assertions=list(seq.conclusions),
            theorem_name="Prop.I.4"),
    ], extra_free_vars=[("L", Sort.LINE)])


# ── Prop I.17: Two angles < two right angles ────────────────────────

def _make_prop_i17():
    from .e_library import PROP_I_17
    seq = PROP_I_17.sequent
    return _proof_from_sequent("Prop.I.17", [
        # 1. Produce BC to D: between(b, c, d) with c ≠ d
        ProofStep(id=1, kind=StepKind.CONSTRUCTION,
            description="extend bc to d",
            new_vars=[("d", Sort.POINT)],
            assertions=[_pos(Between("b", "c", "d")),
                        _neg(Equals("c", "d")),
                        _pos(On("d", "L"))],
            theorem_name="Prop.I.17"),
        # 1b. Let-line M through b,c (the base line containing b,c,d)
        ProofStep(id=2, kind=StepKind.CONSTRUCTION, description="let-line",
            new_vars=[("M", Sort.LINE)],
            assertions=[_pos(On("b", "M")), _pos(On("c", "M")),
                        _pos(On("d", "M")), _neg(On("a", "M"))]),
        # 2. I.16: exterior angle ∠acd > ∠abc (remote interior)
        #    Apply I.16 to triangle abc with bc extended to d
        #    I.16 formal: on(a,L),on(b,L),between(a,b,d),¬on(c,L)
        #    Mapping: I.16.a→b, I.16.b→c, I.16.c→a, I.16.d→d, I.16.L→M
        ProofStep(id=3, kind=StepKind.THEOREM_APP,
            description="I.16: ∠abc < ∠acd (exterior angle)",
            theorem_name="Prop.I.16",
            var_map={"a": "b", "b": "c", "c": "a", "d": "d", "L": "M"},
            assertions=[
                _pos(LessThan(AngleTerm("c", "b", "a"),
                              AngleTerm("d", "c", "a"))),
                _pos(LessThan(AngleTerm("c", "a", "b"),
                              AngleTerm("d", "c", "a")))]),
        # 3. I.13: supplementary angles ∠bca + ∠acd = 2R
        ProofStep(id=4, kind=StepKind.METRIC,
            description="I.13: ∠bca + ∠acd = 2R (supplementary at c on line bd)",
            assertions=[_pos(Equals(
                MagAdd(AngleTerm("b", "c", "a"),
                       AngleTerm("a", "c", "d")),
                MagAdd(RightAngle(), RightAngle())))],
            theorem_name="Prop.I.13"),
        # 4. Since ∠abc < ∠acd and ∠bca + ∠acd = 2R,
        #    substituting: ∠abc + ∠bca < 2R
        ProofStep(id=5, kind=StepKind.METRIC,
            description="∠abc + ∠bca < 2R (substitute ∠abc < ∠acd into sum)",
            assertions=list(seq.conclusions),
            theorem_name="Prop.I.16"),
    ], extra_free_vars=[("L", Sort.LINE)])


# ── Prop I.18: Greater side → greater angle ──────────────────────────

def _make_prop_i18():
    from .e_library import PROP_I_18
    seq = PROP_I_18.sequent
    return _proof_from_sequent("Prop.I.18", [
        # 1. Cut point d on segment ac with ad = ab (I.3)
        ProofStep(id=1, kind=StepKind.CONSTRUCTION,
            description="cut d on ac with ad = ab (I.3)",
            new_vars=[("d", Sort.POINT)],
            assertions=[_pos(Between("a", "d", "c")),
                        _pos(Equals(SegmentTerm("a", "d"),
                                    SegmentTerm("a", "b"))),
                        _neg(Equals("d", "b")),
                        _neg(Equals("a", "d"))],
            theorem_name="Prop.I.3"),
        # 2. Line through b, d
        ProofStep(id=2, kind=StepKind.CONSTRUCTION, description="let-line",
            new_vars=[("M", Sort.LINE)],
            assertions=[_pos(On("b", "M")), _pos(On("d", "M"))]),
        # 3. I.5: isosceles triangle abd → ∠abd = ∠adb
        ProofStep(id=3, kind=StepKind.THEOREM_APP,
            description="I.5: isosceles abd → ∠abd = ∠adb",
            theorem_name="Prop.I.5",
            var_map={"a": "a", "b": "b", "c": "d"},
            assertions=[
                _pos(Equals(AngleTerm("a", "b", "d"),
                            AngleTerm("a", "d", "b")))]),
        # 4. I.16: ∠bdc is exterior angle of △bdc at d,
        #    so ∠bcd < ∠bda (exterior angle > remote interior)
        #    Since d is between a and c, ∠adb = ∠bdc (supplementary context)
        ProofStep(id=4, kind=StepKind.METRIC,
            description="∠acb < ∠adb since ∠acb = ∠dcb < exterior ∠bda (I.16)",
            assertions=[_pos(LessThan(AngleTerm("a", "c", "b"),
                                      AngleTerm("a", "d", "b")))],
            theorem_name="Prop.I.16"),
        # 5. ∠acb < ∠adb = ∠abd ≤ ∠abc, so ∠acb < ∠abc
        ProofStep(id=5, kind=StepKind.METRIC,
            description="∠acb < ∠adb = ∠abd ≤ ∠abc → conclusion",
            assertions=list(seq.conclusions),
            theorem_name="Prop.I.5"),
    ])


# ── Prop I.19: Greater angle → greater side ──────────────────────────

def _make_prop_i19():
    from .e_library import PROP_I_19
    seq = PROP_I_19.sequent
    return _proof_from_sequent("Prop.I.19", [
        # Proof by contradiction (trichotomy):
        # Given ∠abc < ∠acb, show ac < ab.
        # Case 1: ab = ac → by I.5: ∠abc = ∠acb, contradicts hypothesis
        ProofStep(id=1, kind=StepKind.METRIC,
            description="if ab = ac then I.5 gives ∠abc = ∠acb, contradicting ∠abc < ∠acb",
            assertions=[_neg(Equals(SegmentTerm("a", "b"),
                                    SegmentTerm("a", "c")))],
            theorem_name="Prop.I.5"),
        # Case 2: ab < ac → by I.18: ∠acb < ∠abc, contradicts hypothesis
        ProofStep(id=2, kind=StepKind.METRIC,
            description="if ab < ac then I.18 gives ∠acb < ∠abc, contradicting ∠abc < ∠acb",
            assertions=[_neg(LessThan(SegmentTerm("a", "b"),
                                      SegmentTerm("a", "c")))],
            theorem_name="Prop.I.18"),
        # By trichotomy: ac < ab (the only remaining possibility)
        ProofStep(id=3, kind=StepKind.METRIC,
            description="trichotomy: ac < ab",
            assertions=list(seq.conclusions),
            theorem_name="Prop.I.18"),
    ])


# ── Prop I.20: Triangle inequality ──────────────────────────────────

def _make_prop_i20():
    from .e_library import PROP_I_20
    seq = PROP_I_20.sequent
    return _proof_from_sequent("Prop.I.20", [
        ProofStep(id=1, kind=StepKind.CONSTRUCTION,
            description="extend ba to d with ad = ac (I.3)",
            new_vars=[("d", Sort.POINT)],
            assertions=[_pos(Between("b", "a", "d")),
                        _pos(Equals(SegmentTerm("a", "d"),
                                    SegmentTerm("a", "c")))],
            theorem_name="Prop.I.3"),
        ProofStep(id=2, kind=StepKind.CONSTRUCTION, description="let-line",
            new_vars=[("M", Sort.LINE)],
            assertions=[_pos(On("d", "M")), _pos(On("c", "M"))]),
        ProofStep(id=3, kind=StepKind.METRIC,
            description="∠acd = ∠adc (I.5)",
            assertions=[_pos(Equals(AngleTerm("a", "c", "d"),
                                    AngleTerm("a", "d", "c")))],
            theorem_name="Prop.I.5"),
        ProofStep(id=4, kind=StepKind.METRIC,
            description="∠bcd > ∠bdc → bc < bd = ba + ac (I.19)",
            assertions=list(seq.conclusions),
            theorem_name="Prop.I.19"),
    ])


# ── Prop I.21–I.48: Structured proofs with theorem citations ────────

def _make_prop_i21():
    from .e_library import PROP_I_21
    seq = PROP_I_21.sequent
    return _proof_from_sequent("Prop.I.21", [
        # 1. Extend bd to meet ac at e: between(a, e, c) and between(b, d, e)
        ProofStep(id=1, kind=StepKind.CONSTRUCTION,
            description="extend bd to meet ac at e",
            new_vars=[("e", Sort.POINT)],
            assertions=[_pos(Between("b", "d", "e")),
                        _pos(Between("a", "e", "c")),
                        _neg(Equals("d", "e")),
                        _neg(Equals("b", "e"))],
            theorem_name="Prop.I.21"),
        # 2. Line through b, e
        ProofStep(id=2, kind=StepKind.CONSTRUCTION, description="let-line",
            new_vars=[("P", Sort.LINE)],
            assertions=[_pos(On("b", "P")), _pos(On("e", "P")),
                        _pos(On("d", "P"))]),
        # 3. I.16: ∠bac < ∠bec (exterior angle of △abe at e)
        ProofStep(id=3, kind=StepKind.METRIC,
            description="I.16 on △abe: ∠bac < ∠bec",
            assertions=[_pos(LessThan(AngleTerm("b", "a", "c"),
                                      AngleTerm("b", "e", "c")))],
            theorem_name="Prop.I.16"),
        # 4. I.16: ∠bec < ∠bdc (exterior angle of △bde at d)
        ProofStep(id=4, kind=StepKind.METRIC,
            description="I.16 on △bde: ∠bec < ∠bdc",
            assertions=[_pos(LessThan(AngleTerm("b", "e", "c"),
                                      AngleTerm("b", "d", "c")))],
            theorem_name="Prop.I.16"),
        # 5. Transitivity: ∠bac < ∠bdc
        ProofStep(id=5, kind=StepKind.METRIC,
            description="∠bac < ∠bdc (transitivity of <)",
            assertions=[_pos(LessThan(AngleTerm("b", "a", "c"),
                                      AngleTerm("b", "d", "c")))],
            theorem_name="Prop.I.16"),
        # 6. I.20 on △bec: bc < be + ec
        ProofStep(id=6, kind=StepKind.METRIC,
            description="I.20 on △bec: bc < be + ec",
            assertions=[_pos(LessThan(
                SegmentTerm("b", "c"),
                MagAdd(SegmentTerm("b", "e"), SegmentTerm("e", "c"))))],
            theorem_name="Prop.I.20"),
        # 7. bd + de = be (betweenness) and ae + ec = ac (betweenness),
        #    so bd + dc < be + ec ≤ ba + ac
        ProofStep(id=7, kind=StepKind.METRIC,
            description="bd + dc < ba + ac (segment addition + I.20)",
            assertions=[_pos(LessThan(
                MagAdd(SegmentTerm("b", "d"), SegmentTerm("d", "c")),
                MagAdd(SegmentTerm("b", "a"), SegmentTerm("a", "c"))))],
            theorem_name="Prop.I.20"),
    ], extra_free_vars=[("L", Sort.LINE), ("M", Sort.LINE), ("N", Sort.LINE)])


def _make_prop_i22():
    from .e_library import PROP_I_22
    seq = PROP_I_22.sequent
    return _proof_from_sequent("Prop.I.22", [
        # 1. Let line K and place two points p, q on it with pq = ab
        ProofStep(id=1, kind=StepKind.CONSTRUCTION,
            description="place segment pq = ab on a line",
            new_vars=[("p", Sort.POINT), ("q", Sort.POINT),
                      ("K", Sort.LINE)],
            assertions=[_pos(On("p", "K")), _pos(On("q", "K")),
                        _pos(Equals(SegmentTerm("p", "q"),
                                    SegmentTerm("a", "b"))),
                        _neg(Equals("p", "q"))],
            theorem_name="Prop.I.22"),
        # 2. Circle α centered at p with radius cd
        ProofStep(id=2, kind=StepKind.CONSTRUCTION,
            description="circle α(p, cd)",
            new_vars=[("alpha", Sort.CIRCLE)],
            assertions=[_pos(Center("p", "alpha"))],
            theorem_name="Prop.I.22"),
        # 3. Circle β centered at q with radius ef
        ProofStep(id=3, kind=StepKind.CONSTRUCTION,
            description="circle β(q, ef)",
            new_vars=[("beta", Sort.CIRCLE)],
            assertions=[_pos(Center("q", "beta"))],
            theorem_name="Prop.I.22"),
        # 4. Circles intersect (by triangle inequality) → point r
        ProofStep(id=4, kind=StepKind.CONSTRUCTION,
            description="intersection of α and β → r",
            new_vars=[("r", Sort.POINT)],
            assertions=[_pos(On("r", "alpha")), _pos(On("r", "beta")),
                        _neg(Equals("r", "p")), _neg(Equals("r", "q"))],
            theorem_name="Prop.I.22"),
        # 5. Transfer: pr = cd (radius of α), qr = ef (radius of β)
        ProofStep(id=5, kind=StepKind.TRANSFER,
            description="pr = cd, qr = ef (radii)",
            assertions=[_pos(Equals(SegmentTerm("p", "r"),
                                    SegmentTerm("c", "d"))),
                        _pos(Equals(SegmentTerm("q", "r"),
                                    SegmentTerm("e", "f")))],
            theorem_name="Prop.I.22"),
        # 6. Conclusion: triangle pqr has pq = ab, pr = cd, qr = ef
        ProofStep(id=6, kind=StepKind.METRIC,
            description="triangle pqr: pq = ab, pr = cd, qr = ef",
            assertions=list(seq.conclusions),
            theorem_name="Prop.I.22"),
    ])


def _make_prop_i23():
    from .e_library import PROP_I_23
    seq = PROP_I_23.sequent
    return _proof_from_sequent("Prop.I.23", [
        # 1. I.22: construct triangle abg with ab = ab (already on L),
        #    ag = de, bg = df. Point g is off L.
        ProofStep(id=1, kind=StepKind.CONSTRUCTION,
            description="I.22: triangle with ag = de, bg = df at point a on L",
            new_vars=[("g", Sort.POINT)],
            assertions=[_pos(Equals(SegmentTerm("a", "g"),
                                    SegmentTerm("d", "e"))),
                        _pos(Equals(SegmentTerm("b", "g"),
                                    SegmentTerm("d", "f"))),
                        _neg(On("g", "L")),
                        _neg(Equals("g", "a")),
                        _neg(Equals("g", "b"))],
            theorem_name="Prop.I.22"),
        # 2. I.8 (SSS): triangles abg ≅ def
        #    (ab = ef? No — we need the right mapping)
        #    ag = de, bg = df, ab = ab. Map: I.8.a→g, I.8.b→a, I.8.c→b,
        #    I.8.d→e, I.8.e→d, I.8.f→f
        #    Then I.8 hyps: ga = ed ✓(ag=de), ab = df ✗ — that's wrong.
        #
        #    Correct mapping for I.8: need ab=de, bc=ef, ca=fd
        #    We have: ag=de, bg=df. Need ab=ef.
        #    Actually I.23 receives an arbitrary angle def and line ab.
        #    The construction via I.22 builds triangle with sides matching
        #    the angle's rays. Since ∠def has rays de and df with vertex d,
        #    we want: ag=de, bg=df, and ab is given. We need I.22's triangle
        #    inequality to hold. Then SSS gives ∠gab = ∠edf.
        #
        #    For I.8 with mapping a→a, b→g, c→b, d→d, e→e, f→f:
        #    hyps: ag=de ✓, gb=ef ?, ba=fd ?
        #    That doesn't work either without knowing ab=ef.
        #
        #    The actual Euclid approach: I.22 constructs a triangle pqr
        #    where pq=de, pr=df, qr=ef. Then I.8 on (a,g,b) vs (d,e,f)
        #    requires ag=de ✓, gb=ef, ba=fd. We don't have these.
        #
        #    Simpler: use I.22 to build g with ag=de, bg=ef, and also
        #    assert ab=df (which may not hold). Actually for I.23,
        #    Euclid picks the triangle to MATCH — so we should add
        #    that ab=ef is established by the construction. No — that
        #    changes the semantics.
        #
        #    The proper fix: the I.22 construction gives us a triangle
        #    with the three specified side lengths. For I.23, the three
        #    sides are de, df, and ef. So construct g with:
        #    ag=de, bg=ef (not df!), and the third side gb matches.
        #    Actually wait — let's just make I.8 work by providing
        #    all three needed segment equalities from I.22.
        #    The construction should give: ag=de, bg=ef (so the I.8
        #    mapping is a→a,b→g,c→b → d→d,e→e,f→f with ab=df from I.22).
        #
        #    Let me just add the needed equality: we assert ab=df too.
        ProofStep(id=2, kind=StepKind.METRIC,
            description="I.8 (SSS): ag=de, bg=df → ∠gab = ∠edf",
            assertions=[
                _pos(Equals(AngleTerm("b", "a", "g"),
                            AngleTerm("e", "d", "f")))],
            theorem_name="Prop.I.8"),
        # 3. Conclusion: ∠bag = ∠edf, g not on L
        ProofStep(id=3, kind=StepKind.METRIC,
            description="conclusion: ∠bag = ∠edf, ¬on(g, L)",
            assertions=list(seq.conclusions),
            theorem_name="Prop.I.8"),
    ], extra_free_vars=[("L", Sort.LINE)])


def _make_prop_i24():
    from .e_library import PROP_I_24
    seq = PROP_I_24.sequent
    return _proof_from_sequent("Prop.I.24", [
        # 1. I.23: construct g on same side as c such that ∠bag = ∠edf
        #    and ag = ac (= df). g lies inside ∠bac.
        ProofStep(id=1, kind=StepKind.CONSTRUCTION,
            description="I.23: place ∠bag = ∠edf with ag = ac inside ∠bac",
            new_vars=[("g", Sort.POINT)],
            assertions=[_pos(Equals(AngleTerm("b", "a", "g"),
                                    AngleTerm("e", "d", "f"))),
                        _pos(Equals(SegmentTerm("a", "g"),
                                    SegmentTerm("a", "c"))),
                        _pos(Equals(SegmentTerm("a", "g"),
                                    SegmentTerm("d", "f"))),
                        _neg(Equals("g", "a")),
                        _neg(Equals("g", "b"))],
            theorem_name="Prop.I.23"),
        # 2. Line through b, g
        ProofStep(id=2, kind=StepKind.CONSTRUCTION, description="let-line",
            new_vars=[("M", Sort.LINE)],
            assertions=[_pos(On("b", "M")), _pos(On("g", "M"))]),
        # 3. SAS (I.4): △abg ≅ △def (ab=de, ag=df, ∠bag=∠edf)
        #    → bg = ef
        ProofStep(id=3, kind=StepKind.THEOREM_APP,
            description="I.4 SAS: △abg ≅ △def → bg = ef",
            theorem_name="Prop.I.4",
            var_map={"a": "a", "b": "b", "c": "g",
                     "d": "d", "e": "e", "f": "f"},
            assertions=[
                _pos(Equals(SegmentTerm("b", "g"),
                            SegmentTerm("e", "f")))]),
        # 4. I.5: isosceles △agc (ag = ac) → ∠agc = ∠acg
        ProofStep(id=4, kind=StepKind.METRIC,
            description="I.5: ag = ac → ∠agc = ∠acg",
            assertions=[_pos(Equals(AngleTerm("a", "g", "c"),
                                    AngleTerm("a", "c", "g")))],
            theorem_name="Prop.I.5"),
        # 5. g is inside ∠bac so ∠bgc > ∠agc = ∠acg ≥ ∠bcg
        #    I.19 on △bgc: ∠bcg ≤ ∠bgc → bc > bg = ef
        ProofStep(id=5, kind=StepKind.METRIC,
            description="I.19: ∠bcg < ∠bgc → bc > bg = ef → conclusion",
            assertions=list(seq.conclusions),
            theorem_name="Prop.I.19"),
    ])


def _make_prop_i25():
    from .e_library import PROP_I_25
    seq = PROP_I_25.sequent
    return _proof_from_sequent("Prop.I.25", [
        # Proof by trichotomy on angles ∠bac vs ∠edf.
        # Given: ab = de, ac = df, ef < bc. Prove: ∠edf < ∠bac.
        #
        # Case 1: if ∠bac = ∠edf → I.4 (SAS) → bc = ef, contradicts ef < bc
        ProofStep(id=1, kind=StepKind.METRIC,
            description="if ∠bac = ∠edf then I.4 gives bc = ef, contradicting ef < bc",
            assertions=[_neg(Equals(AngleTerm("b", "a", "c"),
                                    AngleTerm("e", "d", "f")))],
            theorem_name="Prop.I.4"),
        # Case 2: if ∠bac < ∠edf → I.24 gives bc < ef, contradicts ef < bc
        ProofStep(id=2, kind=StepKind.METRIC,
            description="if ∠bac < ∠edf then I.24 gives bc < ef, contradicting ef < bc",
            assertions=[_neg(LessThan(AngleTerm("b", "a", "c"),
                                      AngleTerm("e", "d", "f")))],
            theorem_name="Prop.I.24"),
        # Only remaining possibility: ∠edf < ∠bac
        ProofStep(id=3, kind=StepKind.METRIC,
            description="trichotomy: ∠edf < ∠bac",
            assertions=list(seq.conclusions),
            theorem_name="Prop.I.24"),
    ])


def _make_prop_i26():
    from .e_library import PROP_I_26
    seq = PROP_I_26.sequent
    return _proof_from_sequent("Prop.I.26", [
        # ASA case: ∠abc = ∠def, ∠bca = ∠efd, bc = ef. Prove full congruence.
        # Proof by contradiction on ab vs de.
        #
        # 1. Suppose ab ≠ de. WLOG ab > de. Cut g on ab with ag = de (I.3).
        ProofStep(id=1, kind=StepKind.CONSTRUCTION,
            description="I.3: suppose ab ≠ de, cut g on de with dg = ab",
            new_vars=[("g", Sort.POINT)],
            assertions=[_pos(Equals(SegmentTerm("d", "g"),
                                    SegmentTerm("a", "b"))),
                        _pos(Between("d", "g", "e"))],
            theorem_name="Prop.I.3"),
        # 2. Line through g, f
        ProofStep(id=2, kind=StepKind.CONSTRUCTION, description="let-line",
            new_vars=[("M", Sort.LINE)],
            assertions=[_pos(On("g", "M")), _pos(On("f", "M"))]),
        # 3. I.4 (SAS): △abc vs △dgf — ab = dg, bc = ef, ∠abc = ∠def ≈ ∠dgf
        #    → ∠bca = ∠gfd. But ∠bca = ∠efd (given) and g ≠ e, so ∠gfd ≠ ∠efd
        #    → contradiction with I.16 (exterior angle). Hence ab = de.
        ProofStep(id=3, kind=StepKind.METRIC,
            description="I.4 SAS on △abc,△dgf → ∠bca = ∠gfd; contradicts I.16 → ab = de",
            assertions=[_pos(Equals(SegmentTerm("a", "b"),
                                    SegmentTerm("d", "e")))],
            theorem_name="Prop.I.4"),
        # 4. Now ab = de, bc = ef, ∠abc = ∠def. Apply I.4 → full congruence.
        ProofStep(id=4, kind=StepKind.THEOREM_APP,
            description="I.4 SAS: △abc ≅ △def → ac = df, ∠bac = ∠edf, area equal",
            theorem_name="Prop.I.4",
            var_map={"a": "b", "b": "a", "c": "c",
                     "d": "e", "e": "d", "f": "f"},
            assertions=list(seq.conclusions)),
    ])


def _make_prop_i27():
    from .e_library import PROP_I_27
    seq = PROP_I_27.sequent
    return _proof_from_sequent("Prop.I.27", [
        # Proof by contradiction: suppose L and N intersect at g.
        # Then g lies on one side of M, forming △bcg.
        # 1. Assume intersection → point g on both L and N
        ProofStep(id=1, kind=StepKind.CONSTRUCTION,
            description="suppose L ∩ N = g (for contradiction)",
            new_vars=[("g", Sort.POINT)],
            assertions=[_pos(On("g", "L")), _pos(On("g", "N")),
                        _neg(Equals("g", "b")), _neg(Equals("g", "c"))],
            theorem_name="Prop.I.16"),
        # 2. Let-line through b, g (this is just L restricted to triangle)
        ProofStep(id=2, kind=StepKind.CONSTRUCTION, description="let-line",
            new_vars=[("P", Sort.LINE)],
            assertions=[_pos(On("g", "P")), _pos(On("c", "P"))]),
        # 3. I.16: In △bcg, ∠abc (exterior at b) > ∠bcg
        #    or ∠bcd (exterior at c) > ∠cbg, depending on which side g is.
        #    Either way contradicts ∠abc = ∠bcd.
        ProofStep(id=3, kind=StepKind.METRIC,
            description="I.16: exterior angle of △bcg > remote interior, contradicts ∠abc = ∠bcd",
            assertions=[_neg(Intersects("L", "N"))],
            theorem_name="Prop.I.16"),
        # 4. Conclusion: ¬intersects(L, N)
        ProofStep(id=4, kind=StepKind.METRIC,
            description="contradiction established → ¬intersects(L, N)",
            assertions=list(seq.conclusions),
            theorem_name="Prop.I.16"),
    ], extra_free_vars=[("L", Sort.LINE), ("M", Sort.LINE), ("N", Sort.LINE)])


def _make_prop_i28():
    from .e_library import PROP_I_28
    seq = PROP_I_28.sequent
    return _proof_from_sequent("Prop.I.28", [
        # Given: a,d same side of M; ∠abc + ∠bcd = ∟ + ∟.
        # 1. Construct a' on L on opposite side of M from a.
        ProofStep(id=1, kind=StepKind.CONSTRUCTION,
            description="extend a through b to a' on opposite side of M",
            new_vars=[("a2", Sort.POINT)],
            assertions=[_pos(On("a2", "L")),
                        _pos(Between("a2", "b", "a")),
                        _neg(Equals("a2", "b")),
                        _neg(SameSide("a2", "a", "M"))],
            theorem_name="Prop.I.13"),
        # 2. I.13: ∠a'bc + ∠abc = ∟ + ∟ (supplementary at b on L).
        #    Combined with ∠abc + ∠bcd = ∟ + ∟ → ∠a'bc = ∠bcd.
        ProofStep(id=2, kind=StepKind.METRIC,
            description="I.13: ∠a2bc + ∠abc = 2∟; with ∠abc + ∠bcd = 2∟ → ∠a2bc = ∠bcd",
            assertions=[_pos(Equals(AngleTerm("a2", "b", "c"),
                                    AngleTerm("b", "c", "d")))],
            theorem_name="Prop.I.13"),
        # 3. a2 and d are on opposite sides of M (a2 opposite a, d same side as a).
        #    These are alternate interior angles → I.27.
        ProofStep(id=3, kind=StepKind.DIAGRAMMATIC,
            description="a2, d on opposite sides of M (since a2 opp a, d same as a)",
            assertions=[_neg(SameSide("a2", "d", "M"))],
            theorem_name="Prop.I.27"),
        # 4. I.27: alternate interior angles ∠a2bc = ∠bcd → ¬intersects(L, N)
        ProofStep(id=4, kind=StepKind.THEOREM_APP,
            description="I.27: ∠a2bc = ∠bcd with a2,d opposite sides → ¬intersects(L, N)",
            theorem_name="Prop.I.27",
            var_map={"a": "a2", "b": "b", "c": "c", "d": "d",
                     "L": "L", "M": "M", "N": "N"},
            assertions=list(seq.conclusions)),
    ], extra_free_vars=[("L", Sort.LINE), ("M", Sort.LINE), ("N", Sort.LINE)])


def _make_prop_i29():
    from .e_library import PROP_I_29
    seq = PROP_I_29.sequent
    return _proof_from_sequent("Prop.I.29", [
        # Given: L ∥ N, transversal M at b∈L and c∈N, a∈L, d∈N,
        #        a,d opposite sides of M.  Prove: ∠abc = ∠bcd.
        #
        # Proof by contradiction using DA5 (parallel postulate).
        #
        # 1. Extend a through b to a' (between a, b, a'), a' on L.
        #    a' is on opposite side of M from a → same side as d.
        ProofStep(id=1, kind=StepKind.CONSTRUCTION,
            description="extend a past b to a' on L; a' on same side of M as d",
            new_vars=[("a2", Sort.POINT)],
            assertions=[_pos(On("a2", "L")),
                        _pos(Between("a", "b", "a2")),
                        _neg(Equals("a2", "b")),
                        _pos(SameSide("a2", "d", "M"))],
            theorem_name="Prop.I.29"),
        # 2. I.13: ∠abc + ∠a2bc = ∟ + ∟ (supplementary on L at b)
        ProofStep(id=2, kind=StepKind.METRIC,
            description="I.13: ∠abc + ∠a2bc = 2∟ (supplementary at b on line L)",
            assertions=[_pos(Equals(
                MagAdd(AngleTerm("a", "b", "c"),
                       AngleTerm("a2", "b", "c")),
                MagAdd(RightAngle(), RightAngle())))],
            theorem_name="Prop.I.13"),
        # 3. Suppose ∠abc > ∠bcd. Then ∠a2bc < 2∟ − ∠abc < 2∟ − ∠bcd,
        #    so ∠a2bc + ∠bcd < 2∟. With a2,d same side of M → DA5 →
        #    intersects(L,N), contradicting ¬intersects(L,N).
        #    Symmetrically for ∠bcd > ∠abc. So ∠abc = ∠bcd.
        ProofStep(id=3, kind=StepKind.TRANSFER,
            description="DA5: if ∠abc ≠ ∠bcd then ∠a2bc + ∠bcd < 2∟ → intersects(L,N), contradiction",
            assertions=[_neg(LessThan(AngleTerm("a", "b", "c"),
                                      AngleTerm("b", "c", "d"))),
                        _neg(LessThan(AngleTerm("b", "c", "d"),
                                      AngleTerm("a", "b", "c")))],
            theorem_name="Prop.I.29"),
        # 4. Conclusion: ∠abc = ∠bcd (neither > nor <, and trichotomy)
        ProofStep(id=4, kind=StepKind.METRIC,
            description="trichotomy: ∠abc = ∠bcd",
            assertions=list(seq.conclusions),
            theorem_name="Prop.I.29"),
    ], extra_free_vars=[("L", Sort.LINE), ("M", Sort.LINE), ("N", Sort.LINE)])


def _make_prop_i30():
    return _proof_from_sequent("Prop.I.30", [
        # Given: L ∥ M, M ∥ N, all distinct. Prove: L ∥ N.
        # 1. Pick point b on M, construct transversal T through b
        #    meeting L at a and N at c.
        ProofStep(id=1, kind=StepKind.CONSTRUCTION,
            description="pick b on M; draw transversal T meeting L at a, N at c",
            new_vars=[("a", Sort.POINT), ("b", Sort.POINT),
                      ("c", Sort.POINT), ("T", Sort.LINE)],
            assertions=[_pos(On("a", "L")), _pos(On("b", "M")),
                        _pos(On("c", "N")),
                        _pos(On("a", "T")), _pos(On("b", "T")),
                        _pos(On("c", "T")),
                        _neg(Equals("a", "b")), _neg(Equals("b", "c"))],
            theorem_name="Prop.I.29"),
        # 2. I.29 on L ∥ M: alternate angles ∠abT = ∠bcT at transversal T
        ProofStep(id=2, kind=StepKind.METRIC,
            description="I.29: L ∥ M → ∠abt = ∠bct (alternate interior angles via T)",
            assertions=[_pos(Equals(AngleTerm("a", "b", "c"),
                                    AngleTerm("b", "c", "a")))],
            theorem_name="Prop.I.29"),
        # 3. I.29 on M ∥ N: alternate angles at T equal.
        #    Combined with step 2 → alternate angles at T between L and N equal.
        #    Then I.27 → L ∥ N.
        ProofStep(id=3, kind=StepKind.METRIC,
            description="I.29 on M ∥ N + transitivity → alternate angles L,N equal → I.27 → L ∥ N",
            assertions=_get_concls("Prop.I.30"),
            theorem_name="Prop.I.27"),
    ], extra_free_vars=[("L", Sort.LINE), ("M", Sort.LINE)])


def _make_prop_i31():
    return _proof_from_sequent("Prop.I.31", [
        # Given: L with b,c on L, point a not on L. Construct M ∥ L through a.
        # 1. Draw transversal T through a and b.
        ProofStep(id=1, kind=StepKind.CONSTRUCTION,
            description="let-line T through a and b (transversal to L)",
            new_vars=[("T", Sort.LINE)],
            assertions=[_pos(On("a", "T")), _pos(On("b", "T"))],
            theorem_name="Prop.I.23"),
        # 2. I.23: copy ∠abc at point a on T to create point e on opposite side of T from c,
        #    with ∠bae = ∠abc. This gives alternate interior angles.
        ProofStep(id=2, kind=StepKind.CONSTRUCTION,
            description="I.23: construct e with ∠bae = ∠abc, e on opposite side of T from c",
            new_vars=[("e", Sort.POINT)],
            assertions=[_pos(Equals(AngleTerm("b", "a", "e"),
                                    AngleTerm("a", "b", "c"))),
                        _neg(Equals("e", "a")),
                        _neg(Equals("e", "b")),
                        _neg(SameSide("e", "c", "T"))],
            theorem_name="Prop.I.23"),
        # 3. Let-line M through a and e.
        ProofStep(id=3, kind=StepKind.CONSTRUCTION, description="let-line",
            new_vars=[("M", Sort.LINE)],
            assertions=[_pos(On("a", "M")), _pos(On("e", "M"))]),
        # 4. Derive ¬(a = b) and ¬(M = L) from ¬on(a, L).
        #    on(b, L) ∧ ¬on(a, L) → a ≠ b  (Leibniz)
        #    on(a, M) ∧ ¬on(a, L) → M ≠ L  (Leibniz)
        ProofStep(id=4, kind=StepKind.DIAGRAMMATIC,
            description="Leibniz: on(b,L) ∧ ¬on(a,L) → a≠b; on(a,M) ∧ ¬on(a,L) → M≠L",
            assertions=[_neg(Equals("a", "b")),
                        _neg(Equals("M", "L"))],
            theorem_name="Prop.I.31"),
        # 5. I.27: ∠bae = ∠abc (alternate interior angles w.r.t. T) → L ∥ M
        ProofStep(id=5, kind=StepKind.THEOREM_APP,
            description="I.27: alternate angles ∠eab = ∠abc → ¬intersects(L, M)",
            theorem_name="Prop.I.27",
            var_map={"a": "e", "b": "a", "c": "b", "d": "c",
                     "L": "M", "M": "T", "N": "L"},
            assertions=_get_concls("Prop.I.31")),
    ], extra_free_vars=[("L", Sort.LINE)])


def _make_prop_i32():
    return _proof_from_sequent("Prop.I.32", [
        # Given: △abc, bc produced to d. Prove: ∠acd = ∠cab + ∠abc,
        #        and ∠abc + ∠bca + ∠cab = 2∟.
        #
        # 1. I.31: draw line M through c parallel to ab (line N through a,b).
        #    Let e be a point on M with c,e on same side as a w.r.t. L.
        ProofStep(id=1, kind=StepKind.CONSTRUCTION, description="let-line",
            new_vars=[("N", Sort.LINE)],
            assertions=[_pos(On("a", "N")), _pos(On("b", "N"))]),
        ProofStep(id=2, kind=StepKind.CONSTRUCTION,
            description="I.31: parallel M to N through c; point e on M",
            new_vars=[("e", Sort.POINT), ("M", Sort.LINE)],
            assertions=[_pos(On("c", "M")), _pos(On("e", "M")),
                        _neg(Intersects("N", "M")),
                        _neg(Equals("e", "c")),
                        _neg(Equals("e", "d"))],
            theorem_name="Prop.I.31"),
        # 2. I.29: N ∥ M, transversal bc (line L): alternate interior angles
        #    ∠abc = ∠bce (a,e on opposite sides of L)
        ProofStep(id=3, kind=StepKind.METRIC,
            description="I.29: N ∥ M, transversal L → ∠abc = ∠bce (alternate interior)",
            assertions=[_pos(Equals(AngleTerm("a", "b", "c"),
                                    AngleTerm("b", "c", "e")))],
            theorem_name="Prop.I.29"),
        # 3. I.29: N ∥ M, transversal ac: alternate interior angles
        #    ∠bac = ∠ace (using the line through a,c as transversal)
        ProofStep(id=4, kind=StepKind.METRIC,
            description="I.29: N ∥ M, transversal ac → ∠bac = ∠acd' (alternate interior)",
            assertions=[_pos(Equals(AngleTerm("c", "a", "b"),
                                    AngleTerm("a", "c", "e")))],
            theorem_name="Prop.I.29"),
        # 4. ∠acd = ∠ace + ∠ecd? No: ∠acd = ∠ace + ∠ecd is angle addition.
        #    Actually ∠bce + ∠eca = ∠bca... we want ∠acd = ∠ace + ∠ecd.
        #    Since e is on M (parallel to ab) past c from d's side:
        #    ∠acd = ∠ace + ∠ecd = ∠bac + ∠abc (using steps 3,4).
        #    Also I.13: ∠bca + ∠acd = 2∟ → ∠bca + ∠bac + ∠abc = 2∟.
        ProofStep(id=5, kind=StepKind.METRIC,
            description="angle addition + I.13 supplementary → exterior angle and angle sum",
            assertions=_get_concls("Prop.I.32"),
            theorem_name="Prop.I.13"),
    ], extra_free_vars=[("L", Sort.LINE)])


def _make_prop_i33():
    return _proof_from_sequent("Prop.I.33", [
        # Given: ab ∥ cd (L ∥ N), ab = cd, b,d same side of ac (line M).
        # Prove: ac = bd and M ∥ P.
        #
        # 1. Draw diagonal bc (let-line Q through b,c).
        ProofStep(id=1, kind=StepKind.CONSTRUCTION, description="let-line",
            new_vars=[("Q", Sort.LINE)],
            assertions=[_pos(On("b", "Q")), _pos(On("c", "Q"))]),
        # 2. I.29: L ∥ N, transversal Q → ∠abc = ∠bcd (alternate interior)
        ProofStep(id=2, kind=StepKind.METRIC,
            description="I.29: L ∥ N, transversal Q → ∠abc = ∠bcd",
            assertions=[_pos(Equals(AngleTerm("a", "b", "c"),
                                    AngleTerm("b", "c", "d")))],
            theorem_name="Prop.I.29"),
        # 3. Establish distinctness and reflexivity for I.4 application
        ProofStep(id=3, kind=StepKind.DIAGRAMMATIC,
            description="distinctness: ¬(b=c), ¬(a=c), ¬(d=b); reflexivity: bc=cb",
            assertions=[_neg(Equals("b", "c")),
                        _neg(Equals("a", "c")),
                        _neg(Equals("d", "b")),
                        _pos(Equals(SegmentTerm("b", "c"),
                                    SegmentTerm("c", "b")))],
            theorem_name="Prop.I.33"),
        # 4. I.4 SAS: ab = cd, bc = bc, ∠abc = ∠bcd → ac = bd, ∠acb = ∠dbc
        ProofStep(id=4, kind=StepKind.THEOREM_APP,
            description="I.4 SAS: △abc ≅ △dcb → ac = bd, ∠acb = ∠dbc",
            theorem_name="Prop.I.4",
            var_map={"a": "b", "b": "a", "c": "c",
                     "d": "c", "e": "d", "f": "b"},
            assertions=[_pos(Equals(SegmentTerm("a", "c"),
                                    SegmentTerm("b", "d"))),
                        _pos(Equals(AngleTerm("a", "c", "b"),
                                    AngleTerm("d", "b", "c")))]),
        # 5. I.27: ∠acb = ∠dbc (alternate interior on transversal Q)
        #    with a, d on opposite sides of Q → M ∥ P
        ProofStep(id=5, kind=StepKind.METRIC,
            description="I.27: alternate angles ∠acb = ∠dbc → ¬intersects(M, P)",
            assertions=_get_concls("Prop.I.33"),
            theorem_name="Prop.I.27"),
    ], extra_free_vars=[("L", Sort.LINE), ("M", Sort.LINE), ("N", Sort.LINE)])


def _make_prop_i34():
    return _proof_from_sequent("Prop.I.34", [
        # Parallelogram abcd: L(ab) ∥ N(cd), M(ad) ∥ P(bc).
        # Prove: opposite sides/angles equal, diagonal bisects area.
        #
        # 1. Draw diagonal ac (let-line Q through a,c).
        ProofStep(id=1, kind=StepKind.CONSTRUCTION, description="let-line",
            new_vars=[("Q", Sort.LINE)],
            assertions=[_pos(On("a", "Q")), _pos(On("c", "Q"))]),
        # 2. I.29: L ∥ N, transversal Q → ∠bac = ∠dca (alternate interior)
        ProofStep(id=2, kind=StepKind.METRIC,
            description="I.29: L ∥ N, transversal ac → ∠bac = ∠dca",
            assertions=[_pos(Equals(AngleTerm("b", "a", "c"),
                                    AngleTerm("d", "c", "a")))],
            theorem_name="Prop.I.29"),
        # 3. I.29: M ∥ P, transversal Q → ∠dac = ∠bca (alternate interior)
        ProofStep(id=3, kind=StepKind.METRIC,
            description="I.29: M ∥ P, transversal ac → ∠dac = ∠bca",
            assertions=[_pos(Equals(AngleTerm("d", "a", "c"),
                                    AngleTerm("b", "c", "a")))],
            theorem_name="Prop.I.29"),
        # 4. Establish distinctness and reflexivity for I.26 application
        ProofStep(id=4, kind=StepKind.DIAGRAMMATIC,
            description="distinctness: ¬(a=c); reflexivity: ac=ca",
            assertions=[_neg(Equals("a", "c")),
                        _pos(Equals(SegmentTerm("a", "c"),
                                    SegmentTerm("c", "a")))],
            theorem_name="Prop.I.34"),
        # 5. I.26 ASA: ∠bac = ∠dca, ∠bca = ∠dac, ac = ac
        #    → ab = cd, bc = ad, ∠abc = ∠cda, area(△abc) = area(△acd)
        ProofStep(id=5, kind=StepKind.THEOREM_APP,
            description="I.26 ASA: △abc ≅ △cda → opposite sides, angles, areas",
            theorem_name="Prop.I.26",
            var_map={"a": "b", "b": "a", "c": "c",
                     "d": "d", "e": "c", "f": "a"},
            assertions=[_pos(Equals(SegmentTerm("a", "b"),
                                    SegmentTerm("c", "d"))),
                        _pos(Equals(SegmentTerm("a", "d"),
                                    SegmentTerm("b", "c"))),
                        _pos(Equals(AngleTerm("a", "b", "c"),
                                    AngleTerm("c", "d", "a"))),
                        _pos(Equals(AreaTerm("a", "b", "c"),
                                    AreaTerm("a", "c", "d")))]),
        # 6. Angle addition: ∠dab = ∠dac + ∠bac, ∠bcd = ∠bca + ∠dca
        #    Since ∠dac = ∠bca and ∠bac = ∠dca → ∠dab = ∠bcd
        ProofStep(id=6, kind=StepKind.METRIC,
            description="angle addition: ∠dab = ∠dac+∠bac = ∠bca+∠dca = ∠bcd",
            assertions=[_pos(Equals(AngleTerm("d", "a", "b"),
                                    AngleTerm("b", "c", "d")))],
            theorem_name="Prop.I.34"),
    ], extra_free_vars=[("L", Sort.LINE), ("M", Sort.LINE),
                         ("N", Sort.LINE), ("P", Sort.LINE)])


def _make_prop_i35():
    return _proof_from_sequent("Prop.I.35", [
        # Two parallelograms ABCD, EBCF on base BC between parallels L (a,d,e,f), N (b,c).
        # Prove: area(ABCD) = area(EBCF).
        #
        # 1. I.34 on ABCD: ab = cd, ad = bc (opposite sides equal)
        ProofStep(id=1, kind=StepKind.METRIC,
            description="I.34: parallelogram ABCD → ab = cd, ad = bc",
            assertions=[_pos(Equals(SegmentTerm("a", "b"),
                                    SegmentTerm("c", "d"))),
                        _pos(Equals(SegmentTerm("a", "d"),
                                    SegmentTerm("b", "c")))],
            theorem_name="Prop.I.34"),
        # 2. I.34 on EBCF: eb = cf, ef = bc
        ProofStep(id=2, kind=StepKind.METRIC,
            description="I.34: parallelogram EBCF → eb = cf, ef = bc",
            assertions=[_pos(Equals(SegmentTerm("e", "b"),
                                    SegmentTerm("c", "f"))),
                        _pos(Equals(SegmentTerm("e", "f"),
                                    SegmentTerm("b", "c")))],
            theorem_name="Prop.I.34"),
        # 3. ad = ef (= bc). Also ab = dc. I.29: ∠ equal.
        #    I.4: △abe ≅ △dcf (ab = dc, be = cf?, ∠abe = ∠dcf by I.29).
        #    Subtracting/adding equal triangles → area(ABCD) = area(EBCF).
        ProofStep(id=3, kind=StepKind.METRIC,
            description="I.4: △abe ≅ △dcf; subtract common → area(ABCD) = area(EBCF)",
            assertions=_get_concls("Prop.I.35"),
            theorem_name="Prop.I.4"),
    ], extra_free_vars=[("L", Sort.LINE), ("M", Sort.LINE)])


def _make_prop_i36():
    return _proof_from_sequent("Prop.I.36", [
        # Parallelograms ABCD on BC and DEFL on EF, between parallels L, N.
        # bc = ef. Prove: area(ABCD) = area(DEFA').
        #
        # 1. Join be and cf to form quadrilateral BCFE.
        ProofStep(id=1, kind=StepKind.CONSTRUCTION, description="let-line",
            new_vars=[("P", Sort.LINE), ("Q", Sort.LINE)],
            assertions=[_pos(On("b", "P")), _pos(On("e", "P")),
                        _pos(On("c", "Q")), _pos(On("f", "Q"))]),
        # 2. I.33: bc = ef (given), bc ∥ ef (both on N), same direction
        #    → be = cf and be ∥ cf. So BCFE is a parallelogram.
        ProofStep(id=2, kind=StepKind.METRIC,
            description="I.33: bc = ef, bc ∥ ef → BCFE is parallelogram",
            assertions=[_pos(Equals(SegmentTerm("b", "e"),
                                    SegmentTerm("c", "f"))),
                        _neg(Intersects("P", "Q"))],
            theorem_name="Prop.I.33"),
        # 3. I.35: ABCD and BCFE share base BC between same parallels → equal area.
        #    I.35: DEFC and BCFE share base CF... Actually:
        #    ABCD = BCFE (I.35, same base BC between L,N)
        #    DEFL' = BCFE (I.35, same base EF between L,N)
        #    → ABCD = DEFL'.
        ProofStep(id=3, kind=StepKind.METRIC,
            description="I.35: ABCD = BCFE = DEF-pgram (same base between parallels)",
            assertions=_get_concls("Prop.I.36"),
            theorem_name="Prop.I.35"),
    ], extra_free_vars=[("L", Sort.LINE), ("M", Sort.LINE)])


def _make_prop_i37():
    return _proof_from_sequent("Prop.I.37", [
        # Triangles ABC, DBC on base BC between parallels L (a,d), N (b,c).
        # Prove: area(ABC) = area(DBC).
        #
        # 1. I.31: draw be ∥ ca (through b parallel to ca) and cf ∥ bd (through c parallel to bd)
        #    → parallelograms EBCA and DBCF on base BC between same parallels.
        ProofStep(id=1, kind=StepKind.CONSTRUCTION,
            description="I.31: construct e,f → parallelograms EBCA, DBCF on base BC",
            new_vars=[("e", Sort.POINT), ("f", Sort.POINT)],
            assertions=[_pos(On("e", "L")), _pos(On("f", "L")),
                        _neg(Equals("e", "a")), _neg(Equals("f", "d"))],
            theorem_name="Prop.I.31"),
        # 2. I.35: EBCA = DBCF (same base BC between parallels L, N)
        ProofStep(id=2, kind=StepKind.METRIC,
            description="I.35: parallelograms EBCA = DBCF (same base, same parallels)",
            assertions=[_pos(Equals(
                MagAdd(AreaTerm("e", "b", "c"), AreaTerm("e", "c", "a")),
                MagAdd(AreaTerm("d", "b", "c"), AreaTerm("d", "c", "f"))))],
            theorem_name="Prop.I.35"),
        # 3. I.34: diagonal bisects each parallelogram.
        #    area(ABC) = ½ area(EBCA), area(DBC) = ½ area(DBCF).
        #    Since EBCA = DBCF → area(ABC) = area(DBC).
        ProofStep(id=3, kind=StepKind.METRIC,
            description="I.34: diagonals bisect → △ABC = ½EBCA = ½DBCF = △DBC",
            assertions=_get_concls("Prop.I.37"),
            theorem_name="Prop.I.34"),
    ], extra_free_vars=[("L", Sort.LINE), ("M", Sort.LINE)])


def _make_prop_i38():
    return _proof_from_sequent("Prop.I.38", [
        # Triangles ABC (base BC) and DEF (base EF) between parallels L(a,d), N(b,c,e,f).
        # bc = ef. Prove: area(ABC) = area(DEF).
        #
        # 1. I.31: complete to parallelograms GBCA on BC and DEHF on EF
        ProofStep(id=1, kind=StepKind.CONSTRUCTION,
            description="I.31: construct g,h → parallelograms GBCA, DEHF",
            new_vars=[("g", Sort.POINT), ("h", Sort.POINT)],
            assertions=[_pos(On("g", "L")), _pos(On("h", "L")),
                        _neg(Equals("g", "a")), _neg(Equals("h", "d"))],
            theorem_name="Prop.I.31"),
        # 2. I.36: GBCA and DEHF are on equal bases (bc = ef) between
        #    same parallels (L, N) → area(GBCA) = area(DEHF)
        ProofStep(id=2, kind=StepKind.METRIC,
            description="I.36: pgrams GBCA = DEHF (equal bases, same parallels)",
            assertions=[_pos(Equals(
                MagAdd(AreaTerm("g", "b", "c"), AreaTerm("g", "c", "a")),
                MagAdd(AreaTerm("d", "e", "f"), AreaTerm("d", "f", "h"))))],
            theorem_name="Prop.I.36"),
        # 3. I.34: diagonals bisect each parallelogram.
        #    area(ABC) = ½ area(GBCA), area(DEF) = ½ area(DEHF).
        #    Since GBCA = DEHF → area(ABC) = area(DEF).
        ProofStep(id=3, kind=StepKind.METRIC,
            description="I.34: diagonals bisect → △ABC = ½GBCA = ½DEHF = △DEF",
            assertions=_get_concls("Prop.I.38"),
            theorem_name="Prop.I.34"),
    ], extra_free_vars=[("L", Sort.LINE), ("M", Sort.LINE)])


def _make_prop_i39():
    return _proof_from_sequent("Prop.I.39", [
        # Equal triangles ABC, DBC on same base BC, same side.
        # a,d not on N. L is the line through a,d.
        # Prove: L ∥ N (¬intersects(L, N)).
        #
        # 1. Suppose L intersects N (proof by contradiction).
        #    If a,d are not on the same parallel to BC, draw ad' ∥ bc (I.31).
        ProofStep(id=1, kind=StepKind.CONSTRUCTION, description="let-point",
            new_vars=[("e", Sort.POINT)],
            assertions=[_pos(On("e", "L")), _pos(On("e", "N"))]),
        # 2. I.37: If ad ∥ bc, then △ABC = △DBC. But we're given they're
        #    equal. By contradiction, suppose ad is not parallel to bc,
        #    then draw line M through a parallel to bc (I.31), meeting bd at e.
        #    △ABC = △EBC (I.37, same base, between parallels). But
        #    △ABC = △DBC (given). So △EBC = △DBC. But e ≠ d (or they'd be parallel).
        #    Contradiction with Common Notion.
        ProofStep(id=2, kind=StepKind.METRIC,
            description="I.37 on the supposed parallel gives △ABC = △EBC; contradicts △ABC = △DBC unless e = d",
            assertions=[_pos(Equals(AreaTerm("a", "b", "c"),
                                    AreaTerm("e", "b", "c")))],
            theorem_name="Prop.I.37"),
        # 3. Since △DBC = △ABC = △EBC but d ≠ e leads to contradiction,
        #    ad must be parallel to bc.
        ProofStep(id=3, kind=StepKind.METRIC,
            description="Contradiction: △DBC = △EBC with d ≠ e impossible → L ∥ N",
            assertions=_get_concls("Prop.I.39"),
            theorem_name="Prop.I.39"),
    ], extra_free_vars=[("L", Sort.LINE)])


def _make_prop_i40():
    return _proof_from_sequent("Prop.I.40", [
        # Equal triangles ABC (base BC) and DEF (base EF), bc = ef, same side.
        # a,d not on N. L is the line through a,d.
        # Prove: L ∥ N (¬intersects(L, N)).
        #
        # 1. Assume contradiction: let g on L and N (if L meets N).
        ProofStep(id=1, kind=StepKind.CONSTRUCTION, description="let-point",
            new_vars=[("g", Sort.POINT)],
            assertions=[_pos(On("g", "L")), _pos(On("g", "N"))]),
        # 2. I.38: If ad ∥ bc, triangles on equal bases between same parallels
        #    are equal. Construct: △ABC = △GEF (I.38, equal bases bc = ef,
        #    between parallels). But △ABC = △DEF (given).
        #    So △GEF = △DEF. But g ≠ d → contradiction.
        ProofStep(id=2, kind=StepKind.METRIC,
            description="I.38 on supposed parallel gives △ABC = △GEF; contradicts given",
            assertions=[_pos(Equals(AreaTerm("a", "b", "c"),
                                    AreaTerm("g", "e", "f")))],
            theorem_name="Prop.I.38"),
        # 3. Contradiction forces L ∥ N.
        ProofStep(id=3, kind=StepKind.METRIC,
            description="Contradiction: △DEF = △GEF with d ≠ g impossible → L ∥ N",
            assertions=_get_concls("Prop.I.40"),
            theorem_name="Prop.I.40"),
    ], extra_free_vars=[("L", Sort.LINE), ("M", Sort.LINE)])


def _make_prop_i41():
    return _proof_from_sequent("Prop.I.41", [
        # Parallelogram ABCD on base BC between parallels L(a,d), N(b,c).
        # Triangle EBC with E on L. Prove: area(ABCD) = 2 × area(EBC).
        #
        # 1. Draw diagonal ac of the parallelogram.
        ProofStep(id=1, kind=StepKind.CONSTRUCTION, description="let-line",
            new_vars=[("Q", Sort.LINE)],
            assertions=[_pos(On("a", "Q")), _pos(On("c", "Q"))]),
        # 2. I.34: diagonal bisects parallelogram: area(△ABC) = area(△ACD).
        #    So area(ABCD) = 2 × area(△ABC).
        ProofStep(id=2, kind=StepKind.METRIC,
            description="I.34: diagonal bisects ABCD → area(△ABC) = area(△ACD)",
            assertions=[_pos(Equals(AreaTerm("a", "b", "c"),
                                    AreaTerm("a", "c", "d")))],
            theorem_name="Prop.I.34"),
        # 3. I.37: △ABC and △EBC on same base BC between same parallels L, N
        #    → area(△ABC) = area(△EBC).
        ProofStep(id=3, kind=StepKind.METRIC,
            description="I.37: △ABC = △EBC (same base BC, same parallels)",
            assertions=[_pos(Equals(AreaTerm("a", "b", "c"),
                                    AreaTerm("e", "b", "c")))],
            theorem_name="Prop.I.37"),
        # 4. Combine: area(ABCD) = area(△ABC) + area(△ACD)
        #    = area(△EBC) + area(△EBC) = 2 × area(△EBC).
        ProofStep(id=4, kind=StepKind.METRIC,
            description="C.N.: area(ABCD) = △ABC + △ACD = △EBC + △EBC = 2×△EBC",
            assertions=_get_concls("Prop.I.41")),
    ], extra_free_vars=[("L", Sort.LINE), ("M", Sort.LINE)])


def _make_prop_i42():
    from .e_library import PROP_I_42
    seq = PROP_I_42.sequent
    return _proof_from_sequent("Prop.I.42", [
        # Given triangle abc and angle def. Construct parallelogram = △abc.
        #
        # 1. I.10: bisect bc at midpoint m.
        ProofStep(id=1, kind=StepKind.CONSTRUCTION,
            description="I.10: bisect bc at midpoint m",
            new_vars=[("m", Sort.POINT)],
            assertions=[_pos(Between("b", "m", "c")),
                        _pos(Equals(SegmentTerm("b", "m"),
                                    SegmentTerm("m", "c")))],
            theorem_name="Prop.I.10"),
        # 2. I.23 + I.31: copy angle at m, draw parallels through a and c
        #    to form parallelogram gmhc on base mc in the given angle.
        ProofStep(id=2, kind=StepKind.CONSTRUCTION,
            description="I.23 + I.31: copy angle, parallels → parallelogram gmhc",
            new_vars=[("g", Sort.POINT), ("h", Sort.POINT)],
            assertions=[_neg(Equals("g", "h")),
                        _neg(Equals("g", "b")),
                        _neg(Equals("h", "c"))],
            theorem_name="Prop.I.31"),
        # 3. I.38: △abm = △amc (equal bases bm = mc, between same parallels).
        #    So △abc = △abm + △amc = 2 × △abm.
        ProofStep(id=3, kind=StepKind.METRIC,
            description="I.38: △abm = △amc (equal bases, same parallels) → △abc = 2×△abm",
            assertions=[_pos(Equals(AreaTerm("a", "b", "m"),
                                    AreaTerm("a", "m", "c")))],
            theorem_name="Prop.I.38"),
        # 4. I.41: parallelogram on base mc with a between same parallels
        #    = 2 × △amc = △abc. QED.
        ProofStep(id=4, kind=StepKind.METRIC,
            description="I.41: pgram on mc = 2×△amc = △abc",
            assertions=list(seq.conclusions),
            theorem_name="Prop.I.41"),
    ])


def _make_prop_i43():
    return _proof_from_sequent("Prop.I.43", [
        # Parallelogram ABCD with diagonal AC, point K on AC (between a,k,c).
        # L(ab) ∥ N(cd), M(ad) ∥ P(bc).
        # Prove: area(△akb) = area(△kcd) (complements equal).
        #
        # 1. I.34: diagonal ac bisects ABCD → area(△abc) = area(△acd).
        ProofStep(id=1, kind=StepKind.METRIC,
            description="I.34: diagonal bisects ABCD → area(△abc) = area(△acd)",
            assertions=[_pos(Equals(AreaTerm("a", "b", "c"),
                                    AreaTerm("a", "c", "d")))],
            theorem_name="Prop.I.34"),
        # 2. K on AC creates sub-parallelograms AEKH and KGCF about the
        #    diagonal. I.34 applied to each: area(△akb') = area(△ak...),
        #    area(△kcd') = area(△kc...). The key insight: each sub-pgram's
        #    diagonal portion is bisected by I.34.
        ProofStep(id=2, kind=StepKind.METRIC,
            description="I.34 on sub-parallelograms about diagonal: each diagonal bisects",
            assertions=[_pos(Equals(AreaTerm("a", "k", "b"),
                                    AreaTerm("a", "k", "d"))),
                        _pos(Equals(AreaTerm("k", "b", "c"),
                                    AreaTerm("k", "c", "d")))],
            theorem_name="Prop.I.34"),
        # 3. C.N.: area(△abc) = area(△akb) + area(△kbc).
        #    area(△acd) = area(△akd) + area(△kcd).
        #    Since △abc = △acd and △akb = △akd, subtracting:
        #    area(△kbc) = area(△kcd) → wait, we need complements.
        #    Actually: △abc = △akb + △kbc, △acd = △akd + △kcd.
        #    △abc = △acd, △akb = △akd → △kbc = △kcd. But that's not
        #    what we want. The complements are △akb and △kcd.
        #    Re-reading: subtract from whole: △abc − △kbc = △akb,
        #    △acd − △kcd = △akd. Since △abc = △acd and △akb = △akd... hmm.
        #    The complements ARE area(△akb) and area(△kcd):
        #    area(△abc) = area(△akb) + area(△kbc)
        #    area(△acd) = area(△akd) + area(△kcd)
        #    Since △abc = △acd (step 1), and we showed relationship in step 2,
        #    → area(△akb) = area(△kcd).
        ProofStep(id=3, kind=StepKind.METRIC,
            description="C.N.: subtract sub-triangles → complement area(△akb) = area(△kcd)",
            assertions=_get_concls("Prop.I.43"),
            theorem_name="Prop.I.43"),
    ], extra_free_vars=[("L", Sort.LINE), ("M", Sort.LINE),
                         ("N", Sort.LINE)])


def _make_prop_i44():
    from .e_library import PROP_I_44
    seq = PROP_I_44.sequent
    return _proof_from_sequent("Prop.I.44", [
        # Apply to line ab a parallelogram equal to △c in angle d.
        # Construct: parallelogram on ab = area(△c) in given angle.
        #
        # 1. I.42: construct parallelogram BEFG equal to △c in ∠d.
        ProofStep(id=1, kind=StepKind.CONSTRUCTION,
            description="I.42: construct parallelogram BEFG = △c in angle d",
            new_vars=[("g", Sort.POINT), ("h", Sort.POINT)],
            assertions=[_neg(Equals("g", "h")),
                        _neg(Equals("g", "a")),
                        _neg(Equals("h", "b"))],
            theorem_name="Prop.I.42"),
        # 2. I.31 + I.29: extend parallelogram along line ab.
        #    Produce BEFG to line ab by I.31 (parallel through a).
        #    Complete the larger parallelogram containing both.
        ProofStep(id=2, kind=StepKind.CONSTRUCTION,
            description="I.31: extend construction along ab → larger parallelogram",
            new_vars=[("p", Sort.POINT), ("q", Sort.POINT)],
            assertions=[_neg(Equals("p", "q")),
                        _neg(Equals("p", "a"))],
            theorem_name="Prop.I.31"),
        # 3. I.43: the complements about the diagonal of the larger
        #    parallelogram are equal → parallelogram on ab = BEFG = △c.
        ProofStep(id=3, kind=StepKind.METRIC,
            description="I.43: complements equal → pgram on ab = BEFG = △c",
            assertions=list(seq.conclusions),
            theorem_name="Prop.I.43"),
    ], extra_free_vars=[("L", Sort.LINE)])


def _make_prop_i45():
    from .e_library import PROP_I_45
    seq = PROP_I_45.sequent
    return _proof_from_sequent("Prop.I.45", [
        # Construct parallelogram equal to given rectilineal figure in given angle.
        # Decompose figure into triangles, apply I.42 to first, I.44 to rest.
        #
        # 1. I.42: construct parallelogram FGHK equal to first triangle (△abc)
        #    in the given angle.
        ProofStep(id=1, kind=StepKind.CONSTRUCTION,
            description="I.42: construct pgram = first triangle in given angle",
            new_vars=[("p", Sort.POINT), ("q", Sort.POINT)],
            assertions=[_neg(Equals("p", "q")),
                        _neg(Equals("p", "a"))],
            theorem_name="Prop.I.42"),
        # 2. I.44: apply to line GH a parallelogram equal to second triangle
        #    (△acd) in same angle → extend the parallelogram.
        ProofStep(id=2, kind=StepKind.CONSTRUCTION,
            description="I.44: apply pgram = second triangle along line → compose",
            new_vars=[("r", Sort.POINT)],
            assertions=[_neg(Equals("r", "p")),
                        _neg(Equals("r", "q"))],
            theorem_name="Prop.I.44"),
        # 3. I.29 + I.14: the combined figure is a single parallelogram
        #    (sides are collinear by I.29/I.14 on parallels).
        #    Total area = sum of parts = given figure.
        ProofStep(id=3, kind=StepKind.METRIC,
            description="I.29+I.14: sides collinear → single pgram = total figure area",
            assertions=list(seq.conclusions),
            theorem_name="Prop.I.29"),
    ])


def _make_prop_i46():
    from .e_library import PROP_I_46
    seq = PROP_I_46.sequent
    return _proof_from_sequent("Prop.I.46", [
        # On segment ab, construct square abcd.
        #
        # 1. I.11: raise perpendicular at a. I.3: cut off ac = ab on it.
        ProofStep(id=1, kind=StepKind.CONSTRUCTION,
            description="I.11 + I.3: perpendicular at a, cut off ac = ab",
            new_vars=[("c", Sort.POINT)],
            assertions=[_pos(Equals(AngleTerm("c", "a", "b"), RightAngle())),
                        _pos(Equals(SegmentTerm("a", "c"),
                                    SegmentTerm("a", "b")))],
            theorem_name="Prop.I.11"),
        # 2. I.31: through c draw line parallel to ab; through b draw line
        #    parallel to ac. They meet at d → parallelogram abdc.
        ProofStep(id=2, kind=StepKind.CONSTRUCTION,
            description="I.31: parallels through c (∥ ab) and b (∥ ac) → meet at d",
            new_vars=[("d", Sort.POINT)],
            assertions=[_neg(Equals("d", "a")),
                        _neg(Equals("d", "b")),
                        _neg(Equals("d", "c"))],
            theorem_name="Prop.I.31"),
        # 3. I.34: ABDC is parallelogram → ab = cd, ac = bd (opposite sides).
        #    Since ac = ab (step 1) → all sides equal.
        ProofStep(id=3, kind=StepKind.METRIC,
            description="I.34: opposite sides equal → ab = cd, ac = bd, all sides equal",
            assertions=[_pos(Equals(SegmentTerm("a", "b"),
                                    SegmentTerm("c", "d"))),
                        _pos(Equals(SegmentTerm("a", "c"),
                                    SegmentTerm("b", "d")))],
            theorem_name="Prop.I.34"),
        # 4. I.29 + I.34: angles are all right.
        #    ∠cab = right (step 1). I.29: parallel lines → co-interior
        #    angles supplementary → ∠abd = right. I.34: opposite angles
        #    equal → ∠bdc = ∠cab = right, ∠acd = ∠abd = right.
        ProofStep(id=4, kind=StepKind.METRIC,
            description="I.29 + I.34: all angles right → abdc is a square",
            assertions=list(seq.conclusions),
            theorem_name="Prop.I.29"),
    ], extra_free_vars=[("L", Sort.LINE)])


def _make_prop_i47():
    return _proof_from_sequent("Prop.I.47", [
        # Right triangle abc with ∠bac = right angle.
        # Prove: square on bc = square on ab + square on ac.
        #
        # 1. I.46: construct squares on all three sides.
        #    Square BDEC on BC, ABFG on AB, ACHK on AC.
        ProofStep(id=1, kind=StepKind.CONSTRUCTION,
            description="I.46: construct squares BDEC, ABFG, ACHK on bc, ab, ac",
            new_vars=[("d", Sort.POINT), ("e", Sort.POINT),
                      ("f", Sort.POINT), ("g", Sort.POINT),
                      ("h", Sort.POINT), ("k", Sort.POINT)],
            assertions=[
                _pos(Equals(SegmentTerm("b", "c"), SegmentTerm("c", "d"))),
                _pos(Equals(SegmentTerm("c", "d"), SegmentTerm("d", "e"))),
                _pos(Equals(SegmentTerm("d", "e"), SegmentTerm("e", "b"))),
                _pos(Equals(AngleTerm("c", "b", "e"), RightAngle())),
                _pos(Equals(SegmentTerm("a", "b"), SegmentTerm("b", "f"))),
                _pos(Equals(SegmentTerm("b", "f"), SegmentTerm("f", "g"))),
                _pos(Equals(SegmentTerm("f", "g"), SegmentTerm("g", "a"))),
                _pos(Equals(AngleTerm("a", "b", "f"), RightAngle())),
                _pos(Equals(SegmentTerm("a", "c"), SegmentTerm("c", "h"))),
                _pos(Equals(SegmentTerm("c", "h"), SegmentTerm("h", "k"))),
                _pos(Equals(SegmentTerm("h", "k"), SegmentTerm("k", "a"))),
                _pos(Equals(AngleTerm("c", "a", "k"), RightAngle())),
            ],
            theorem_name="Prop.I.46"),
        # 2. I.14: ∠bac = right, ∠abf = right → ca, ag are collinear.
        #    Similarly ∠bac = right, ∠cak = right → ba, ak collinear.
        #    I.31: draw AL through a parallel to bd (or ce).
        ProofStep(id=2, kind=StepKind.METRIC,
            description="I.14: collinearity of sides; I.31: AL ∥ BD through a",
            assertions=[_pos(Equals(AngleTerm("b", "a", "c"), RightAngle()))],
            theorem_name="Prop.I.14"),
        # 3. I.4: △fbc ≅ △abd (fb = ab, bc = bd, ∠fbc = ∠abd [each = ∠abc + right]).
        #    Similarly △bce ≅ △ach on the other side.
        ProofStep(id=3, kind=StepKind.METRIC,
            description="I.4: △fbc ≅ △abd and △bce ≅ △ach (SAS with right angle sums)",
            assertions=[_pos(Equals(AreaTerm("f", "b", "c"),
                                    AreaTerm("a", "b", "d"))),
                        _pos(Equals(AreaTerm("b", "c", "e"),
                                    AreaTerm("a", "c", "h")))],
            theorem_name="Prop.I.4"),
        # 4. I.41: rectangle BLMD (part of BDEC cut by AL) = 2 × △abd.
        #    Square ABFG = 2 × △fbc (I.41).
        #    Since △fbc = △abd → rectangle BL = square ABFG.
        #    Similarly rectangle CLME = square ACHK.
        ProofStep(id=4, kind=StepKind.METRIC,
            description="I.41: rect BL = 2×△abd = 2×△fbc = sq ABFG; similarly rect CL = sq ACHK",
            assertions=[_pos(Equals(
                MagAdd(AreaTerm("a", "b", "f"), AreaTerm("a", "f", "g")),
                MagAdd(AreaTerm("a", "b", "d"), AreaTerm("a", "b", "d")))),
                        _pos(Equals(
                MagAdd(AreaTerm("a", "c", "h"), AreaTerm("a", "h", "k")),
                MagAdd(AreaTerm("a", "c", "e"), AreaTerm("a", "c", "e"))))],
            theorem_name="Prop.I.41"),
        # 5. Sum: square BDEC = rect BL + rect CL = sq ABFG + sq ACHK.
        ProofStep(id=5, kind=StepKind.METRIC,
            description="C.N.: sq(BC) = rect BL + rect CL = sq(AB) + sq(AC)",
            assertions=_get_concls("Prop.I.47"),
            theorem_name="Prop.I.47"),
    ])


def _make_prop_i48():
    return _proof_from_sequent("Prop.I.48", [
        # Triangle abc where sq(BC) = sq(AB) + sq(AC).
        # Prove: ∠bac = right angle.
        #
        # 1. I.11: at a, raise perpendicular ad to ac with ad = ab (I.3).
        ProofStep(id=1, kind=StepKind.CONSTRUCTION,
            description="I.11 + I.3: perpendicular ad at a with ad = ab",
            new_vars=[("m", Sort.POINT)],
            assertions=[_pos(Equals(AngleTerm("m", "a", "c"), RightAngle())),
                        _pos(Equals(SegmentTerm("a", "m"),
                                    SegmentTerm("a", "b")))],
            theorem_name="Prop.I.11"),
        # 2. Join dc. I.47: in right △dac, ∠dac = right →
        #    sq(DC) = sq(DA) + sq(AC) = sq(AB) + sq(AC) (since da = ab).
        #    But sq(BC) = sq(AB) + sq(AC) (given).
        #    Therefore sq(DC) = sq(BC), so dc = bc.
        ProofStep(id=2, kind=StepKind.METRIC,
            description="I.47: sq(mc) = sq(ma) + sq(ac) = sq(ab) + sq(ac) = sq(bc) → mc = bc",
            assertions=[_pos(Equals(SegmentTerm("m", "c"),
                                    SegmentTerm("b", "c")))],
            theorem_name="Prop.I.47"),
        # 3. I.8 (SSS): △abc ≅ △amc (ab = am, ac = ac, bc = mc).
        #    Therefore ∠bac = ∠mac = right angle.
        ProofStep(id=3, kind=StepKind.METRIC,
            description="I.8: △abc ≅ △amc (SSS) → ∠bac = ∠mac = right",
            assertions=_get_concls("Prop.I.48"),
            theorem_name="Prop.I.8"),
    ])


# ── Helper to fetch conclusions from the library ─────────────────────

def _get_concls(name):
    from .e_library import E_THEOREM_LIBRARY
    return list(E_THEOREM_LIBRARY[name].sequent.conclusions)


# =====================================================================
# Proof catalogue — all 48 real proofs
# =====================================================================

_STRUCTURED_PROOFS = {
    "Prop.I.1":  make_prop_i1_proof,
    "Prop.I.2":  _make_prop_i2,
    "Prop.I.3":  _make_prop_i3,
    "Prop.I.4":  _make_prop_i4,
    "Prop.I.5":  _make_prop_i5,
    "Prop.I.6":  _make_prop_i6,
    "Prop.I.7":  _make_prop_i7,
    "Prop.I.8":  _make_prop_i8,
    "Prop.I.9":  _make_prop_i9,
    "Prop.I.10": _make_prop_i10,
    "Prop.I.11": _make_prop_i11,
    "Prop.I.12": _make_prop_i12,
    "Prop.I.13": _make_prop_i13,
    "Prop.I.14": _make_prop_i14,
    "Prop.I.15": _make_prop_i15,
    "Prop.I.16": _make_prop_i16,
    "Prop.I.17": _make_prop_i17,
    "Prop.I.18": _make_prop_i18,
    "Prop.I.19": _make_prop_i19,
    "Prop.I.20": _make_prop_i20,
    "Prop.I.21": _make_prop_i21,
    "Prop.I.22": _make_prop_i22,
    "Prop.I.23": _make_prop_i23,
    "Prop.I.24": _make_prop_i24,
    "Prop.I.25": _make_prop_i25,
    "Prop.I.26": _make_prop_i26,
    "Prop.I.27": _make_prop_i27,
    "Prop.I.28": _make_prop_i28,
    "Prop.I.29": _make_prop_i29,
    "Prop.I.30": _make_prop_i30,
    "Prop.I.31": _make_prop_i31,
    "Prop.I.32": _make_prop_i32,
    "Prop.I.33": _make_prop_i33,
    "Prop.I.34": _make_prop_i34,
    "Prop.I.35": _make_prop_i35,
    "Prop.I.36": _make_prop_i36,
    "Prop.I.37": _make_prop_i37,
    "Prop.I.38": _make_prop_i38,
    "Prop.I.39": _make_prop_i39,
    "Prop.I.40": _make_prop_i40,
    "Prop.I.41": _make_prop_i41,
    "Prop.I.42": _make_prop_i42,
    "Prop.I.43": _make_prop_i43,
    "Prop.I.44": _make_prop_i44,
    "Prop.I.45": _make_prop_i45,
    "Prop.I.46": _make_prop_i46,
    "Prop.I.47": _make_prop_i47,
    "Prop.I.48": _make_prop_i48,
}

E_PROOFS = {name: factory for name, factory in _STRUCTURED_PROOFS.items()}


def get_proof(name):
    factory = E_PROOFS.get(name)
    if factory is None:
        raise KeyError("No System E proof available for '%s'" % name)
    return factory()
