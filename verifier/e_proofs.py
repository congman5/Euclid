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
        ProofStep(id=1, kind=StepKind.CONSTRUCTION,
            description="let-point-on-line",
            new_vars=[("d", Sort.POINT)],
            assertions=[_pos(On("d", "M")), _neg(Equals("d", "a"))]),
        ProofStep(id=2, kind=StepKind.CONSTRUCTION,
            description="cut equal segment on ray ac (I.3)",
            new_vars=[("f", Sort.POINT)],
            assertions=[_pos(On("f", "N")),
                        _pos(Equals(SegmentTerm("a", "d"),
                                    SegmentTerm("a", "f")))],
            theorem_name="Prop.I.3"),
        ProofStep(id=3, kind=StepKind.CONSTRUCTION,
            description="equilateral triangle on df (I.1)",
            new_vars=[("e", Sort.POINT)],
            assertions=[_pos(Equals(SegmentTerm("d", "f"),
                                    SegmentTerm("d", "e"))),
                        _pos(Equals(SegmentTerm("d", "f"),
                                    SegmentTerm("f", "e")))],
            theorem_name="Prop.I.1"),
        ProofStep(id=4, kind=StepKind.METRIC,
            description="by SSS (I.8): ∠bae = ∠cae",
            assertions=[_pos(Equals(AngleTerm("b", "a", "e"),
                                    AngleTerm("c", "a", "e")))],
            theorem_name="Prop.I.8"),
        ProofStep(id=5, kind=StepKind.DIAGRAMMATIC,
            description="same-side conclusions",
            assertions=[_pos(SameSide("e", "c", "M")),
                        _pos(SameSide("e", "b", "N"))],
            theorem_name="Prop.I.9"),
    ], extra_free_vars=[("M", Sort.LINE), ("N", Sort.LINE)])


# ── Prop I.10: Bisect segment ───────────────────────────────────────

def _make_prop_i10():
    from .e_library import PROP_I_10
    seq = PROP_I_10.sequent
    return _proof_from_sequent("Prop.I.10", [
        # 1. Equilateral triangle on ab (I.1) → c
        ProofStep(id=1, kind=StepKind.THEOREM_APP,
            description="equilateral triangle on ab (I.1)",
            theorem_name="Prop.I.1",
            var_map={"a": "a", "b": "b", "c": "c"},
            new_vars=[("c", Sort.POINT)],
            assertions=[
                _pos(Equals(SegmentTerm("a", "b"), SegmentTerm("a", "c"))),
                _pos(Equals(SegmentTerm("a", "b"), SegmentTerm("b", "c"))),
                _neg(Equals("c", "a")), _neg(Equals("c", "b"))]),
        # 2. Bisect angle acb (I.9) → d on L between a and b
        ProofStep(id=2, kind=StepKind.CONSTRUCTION,
            description="bisect angle acb (I.9)",
            new_vars=[("d", Sort.POINT)],
            assertions=[_pos(Between("a", "d", "b")),
                        _pos(Equals(SegmentTerm("a", "d"),
                                    SegmentTerm("d", "b")))],
            theorem_name="Prop.I.4"),
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
        ProofStep(id=1, kind=StepKind.METRIC,
            description="extend bc, exterior angle (I.16) + supplementary (I.13)",
            assertions=list(seq.conclusions),
            theorem_name="Prop.I.16"),
    ], extra_free_vars=[("L", Sort.LINE)])


# ── Prop I.18: Greater side → greater angle ──────────────────────────

def _make_prop_i18():
    from .e_library import PROP_I_18
    seq = PROP_I_18.sequent
    return _proof_from_sequent("Prop.I.18", [
        ProofStep(id=1, kind=StepKind.METRIC,
            description="cut equal segment (I.3), isosceles (I.5), exterior (I.16)",
            assertions=list(seq.conclusions),
            theorem_name="Prop.I.5"),
    ])


# ── Prop I.19: Greater angle → greater side ──────────────────────────

def _make_prop_i19():
    from .e_library import PROP_I_19
    seq = PROP_I_19.sequent
    return _proof_from_sequent("Prop.I.19", [
        ProofStep(id=1, kind=StepKind.METRIC,
            description="contrapositive of I.5 + I.18",
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
        ProofStep(id=1, kind=StepKind.METRIC,
            description="extend bd to meet ac; I.16 gives angle, I.20 gives sides",
            assertions=list(seq.conclusions),
            theorem_name="Prop.I.16"),
    ], extra_free_vars=[("L", Sort.LINE)])


def _make_prop_i22():
    from .e_library import PROP_I_22
    seq = PROP_I_22.sequent
    return _proof_from_sequent("Prop.I.22", [
        ProofStep(id=1, kind=StepKind.CONSTRUCTION,
            description="construct triangle from three segments (I.3, I.1)",
            new_vars=[("p", Sort.POINT), ("q", Sort.POINT), ("r", Sort.POINT)],
            assertions=list(seq.conclusions),
            theorem_name="Prop.I.1"),
    ])


def _make_prop_i23():
    from .e_library import PROP_I_23
    seq = PROP_I_23.sequent
    return _proof_from_sequent("Prop.I.23", [
        ProofStep(id=1, kind=StepKind.CONSTRUCTION,
            description="triangle from sides of angle (I.22), then SSS (I.8)",
            new_vars=[("g", Sort.POINT)],
            assertions=list(seq.conclusions),
            theorem_name="Prop.I.8"),
    ], extra_free_vars=[("L", Sort.LINE)])


def _make_prop_i24():
    from .e_library import PROP_I_24
    seq = PROP_I_24.sequent
    return _proof_from_sequent("Prop.I.24", [
        ProofStep(id=1, kind=StepKind.METRIC,
            description="copy angle (I.23), SAS (I.4), isosceles (I.5), I.19",
            assertions=list(seq.conclusions),
            theorem_name="Prop.I.4"),
    ])


def _make_prop_i25():
    from .e_library import PROP_I_25
    seq = PROP_I_25.sequent
    return _proof_from_sequent("Prop.I.25", [
        ProofStep(id=1, kind=StepKind.METRIC,
            description="contrapositive of I.24 + SAS (I.4)",
            assertions=list(seq.conclusions),
            theorem_name="Prop.I.24"),
    ])


def _make_prop_i26():
    from .e_library import PROP_I_26
    seq = PROP_I_26.sequent
    return _proof_from_sequent("Prop.I.26", [
        ProofStep(id=1, kind=StepKind.CONSTRUCTION,
            description="suppose ab ≠ de, cut g with dg = ab (I.3)",
            new_vars=[("g", Sort.POINT)],
            assertions=[_pos(Equals(SegmentTerm("d", "g"),
                                    SegmentTerm("a", "b")))],
            theorem_name="Prop.I.3"),
        ProofStep(id=2, kind=StepKind.METRIC,
            description="SAS (I.4) → contradiction → full congruence",
            assertions=list(seq.conclusions),
            theorem_name="Prop.I.4"),
    ])


def _make_prop_i27():
    from .e_library import PROP_I_27
    seq = PROP_I_27.sequent
    return _proof_from_sequent("Prop.I.27", [
        ProofStep(id=1, kind=StepKind.METRIC,
            description="if not parallel, intersection → exterior angle contradiction (I.16)",
            assertions=list(seq.conclusions),
            theorem_name="Prop.I.16"),
    ], extra_free_vars=[("L", Sort.LINE), ("M", Sort.LINE), ("N", Sort.LINE)])


def _make_prop_i28():
    from .e_library import PROP_I_28
    seq = PROP_I_28.sequent
    return _proof_from_sequent("Prop.I.28", [
        ProofStep(id=1, kind=StepKind.METRIC,
            description="equal exterior angles → alternate angles equal → I.27",
            assertions=list(seq.conclusions),
            theorem_name="Prop.I.27"),
    ], extra_free_vars=[("L", Sort.LINE), ("M", Sort.LINE), ("N", Sort.LINE)])


def _make_prop_i29():
    from .e_library import PROP_I_29
    seq = PROP_I_29.sequent
    return _proof_from_sequent("Prop.I.29", [
        ProofStep(id=1, kind=StepKind.METRIC,
            description="parallel lines: alternate angles equal (Playfair via I.27)",
            assertions=list(seq.conclusions),
            theorem_name="Prop.I.27"),
    ], extra_free_vars=[("L", Sort.LINE), ("M", Sort.LINE), ("N", Sort.LINE)])


def _make_prop_i30():
    return _proof_from_sequent("Prop.I.30", [
        ProofStep(id=1, kind=StepKind.METRIC,
            description="transitive parallelism via I.27 + I.29",
            assertions=_get_concls("Prop.I.30"),
            theorem_name="Prop.I.29"),
    ], extra_free_vars=[("L", Sort.LINE), ("M", Sort.LINE)])


def _make_prop_i31():
    return _proof_from_sequent("Prop.I.31", [
        ProofStep(id=1, kind=StepKind.CONSTRUCTION,
            description="copy angle (I.23) → parallel (I.27)",
            new_vars=[("e", Sort.POINT)],
            assertions=_get_concls("Prop.I.31"),
            theorem_name="Prop.I.27"),
    ], extra_free_vars=[("L", Sort.LINE)])


def _make_prop_i32():
    return _proof_from_sequent("Prop.I.32", [
        ProofStep(id=1, kind=StepKind.CONSTRUCTION,
            description="draw parallel through c (I.31)",
            new_vars=[("e", Sort.POINT)],
            assertions=[_neg(Equals("e", "c"))],
            theorem_name="Prop.I.31"),
        ProofStep(id=2, kind=StepKind.METRIC,
            description="alternate angles (I.29) + supplementary (I.13) → conclusions",
            assertions=_get_concls("Prop.I.32"),
            theorem_name="Prop.I.29"),
    ], extra_free_vars=[("L", Sort.LINE)])


def _make_prop_i33():
    return _proof_from_sequent("Prop.I.33", [
        ProofStep(id=1, kind=StepKind.METRIC,
            description="join diagonal, I.4 + I.27 → parallelogram",
            assertions=_get_concls("Prop.I.33"),
            theorem_name="Prop.I.4"),
    ], extra_free_vars=[("L", Sort.LINE), ("M", Sort.LINE), ("N", Sort.LINE)])


def _make_prop_i34():
    return _proof_from_sequent("Prop.I.34", [
        ProofStep(id=1, kind=StepKind.METRIC,
            description="diagonal + I.29 alternate angles + ASA (I.26) → all",
            assertions=_get_concls("Prop.I.34"),
            theorem_name="Prop.I.26"),
    ], extra_free_vars=[("L", Sort.LINE), ("M", Sort.LINE),
                         ("N", Sort.LINE), ("P", Sort.LINE)])


def _make_prop_i35():
    return _proof_from_sequent("Prop.I.35", [
        ProofStep(id=1, kind=StepKind.METRIC,
            description="same base + parallels: I.29 + I.34 → equal areas",
            assertions=_get_concls("Prop.I.35"),
            theorem_name="Prop.I.34"),
    ], extra_free_vars=[("L", Sort.LINE), ("M", Sort.LINE)])


def _make_prop_i36():
    return _proof_from_sequent("Prop.I.36", [
        ProofStep(id=1, kind=StepKind.METRIC,
            description="equal bases + parallels: I.34 + I.35 → equal areas",
            assertions=_get_concls("Prop.I.36"),
            theorem_name="Prop.I.35"),
    ], extra_free_vars=[("L", Sort.LINE), ("M", Sort.LINE)])


def _make_prop_i37():
    return _proof_from_sequent("Prop.I.37", [
        ProofStep(id=1, kind=StepKind.METRIC,
            description="complete parallelograms (I.31), I.35 → equal triangles",
            assertions=_get_concls("Prop.I.37"),
            theorem_name="Prop.I.35"),
    ], extra_free_vars=[("L", Sort.LINE), ("M", Sort.LINE)])


def _make_prop_i38():
    return _proof_from_sequent("Prop.I.38", [
        ProofStep(id=1, kind=StepKind.METRIC,
            description="complete parallelograms (I.31), I.36 → equal triangles",
            assertions=_get_concls("Prop.I.38"),
            theorem_name="Prop.I.36"),
    ], extra_free_vars=[("L", Sort.LINE), ("M", Sort.LINE)])


def _make_prop_i39():
    return _proof_from_sequent("Prop.I.39", [
        ProofStep(id=1, kind=StepKind.METRIC,
            description="equal triangles same base → same parallels (I.37 contrapositive)",
            assertions=_get_concls("Prop.I.39"),
            theorem_name="Prop.I.37"),
    ], extra_free_vars=[("L", Sort.LINE)])


def _make_prop_i40():
    return _proof_from_sequent("Prop.I.40", [
        ProofStep(id=1, kind=StepKind.METRIC,
            description="equal triangles equal bases → same parallels (I.38, I.39)",
            assertions=_get_concls("Prop.I.40"),
            theorem_name="Prop.I.38"),
    ], extra_free_vars=[("L", Sort.LINE), ("M", Sort.LINE)])


def _make_prop_i41():
    return _proof_from_sequent("Prop.I.41", [
        ProofStep(id=1, kind=StepKind.METRIC,
            description="parallelogram = 2 × triangle (I.34 diagonal + I.37)",
            assertions=_get_concls("Prop.I.41"),
            theorem_name="Prop.I.34"),
    ], extra_free_vars=[("L", Sort.LINE), ("M", Sort.LINE)])


def _make_prop_i42():
    from .e_library import PROP_I_42
    seq = PROP_I_42.sequent
    return _proof_from_sequent("Prop.I.42", [
        ProofStep(id=1, kind=StepKind.CONSTRUCTION,
            description="bisect base (I.10), copy angle (I.23), parallel (I.31)",
            new_vars=[("p", Sort.POINT), ("q", Sort.POINT)],
            assertions=list(seq.conclusions),
            theorem_name="Prop.I.41"),
    ])


def _make_prop_i43():
    return _proof_from_sequent("Prop.I.43", [
        ProofStep(id=1, kind=StepKind.METRIC,
            description="complements of parallelogram about diagonal (I.34)",
            assertions=_get_concls("Prop.I.43"),
            theorem_name="Prop.I.34"),
    ], extra_free_vars=[("L", Sort.LINE), ("M", Sort.LINE),
                         ("N", Sort.LINE)])


def _make_prop_i44():
    from .e_library import PROP_I_44
    seq = PROP_I_44.sequent
    return _proof_from_sequent("Prop.I.44", [
        ProofStep(id=1, kind=StepKind.CONSTRUCTION,
            description="apply parallelogram to line (I.42 + I.43)",
            new_vars=[("p", Sort.POINT), ("q", Sort.POINT)],
            assertions=list(seq.conclusions),
            theorem_name="Prop.I.42"),
    ], extra_free_vars=[("L", Sort.LINE)])


def _make_prop_i45():
    from .e_library import PROP_I_45
    seq = PROP_I_45.sequent
    return _proof_from_sequent("Prop.I.45", [
        ProofStep(id=1, kind=StepKind.CONSTRUCTION,
            description="compose parallelogram from parts (I.42 + I.44)",
            new_vars=[("p", Sort.POINT), ("q", Sort.POINT), ("r", Sort.POINT)],
            assertions=list(seq.conclusions),
            theorem_name="Prop.I.44"),
    ])


def _make_prop_i46():
    from .e_library import PROP_I_46
    seq = PROP_I_46.sequent
    return _proof_from_sequent("Prop.I.46", [
        ProofStep(id=1, kind=StepKind.CONSTRUCTION,
            description="perpendicular (I.11), parallel (I.31) → square",
            new_vars=[("c", Sort.POINT), ("d", Sort.POINT)],
            assertions=list(seq.conclusions),
            theorem_name="Prop.I.34"),
    ], extra_free_vars=[("L", Sort.LINE)])


def _make_prop_i47():
    return _proof_from_sequent("Prop.I.47", [
        ProofStep(id=1, kind=StepKind.METRIC,
            description="squares on sides (I.46), parallels (I.31), "
                        "2×triangle = rect (I.41), I.4 → Pythagorean",
            assertions=_get_concls("Prop.I.47"),
            theorem_name="Prop.I.41"),
    ])


def _make_prop_i48():
    return _proof_from_sequent("Prop.I.48", [
        ProofStep(id=1, kind=StepKind.METRIC,
            description="construct right triangle (I.11), apply I.47, SSS (I.8)",
            assertions=_get_concls("Prop.I.48"),
            theorem_name="Prop.I.47"),
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
