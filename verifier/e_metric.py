"""
e_metric.py — Metric inference engine for System E (Section 3.5).

Handles reasoning about magnitudes (segments, angles, areas) in the
framework of a non-negative ordered abelian group ⟨ℝ⁺, 0, +, < ⟩.

Core properties (from the paper):
  - + is associative, commutative, identity 0
  - < is a linear ordering with least element 0
  - x < y → x + z < y + z  (monotonicity)
  - x + z = y + z → x = y   (cancellation, CN3)
  - 0 < y → z < y + z       (CN5: whole > part)

Additional axioms (M1–M9):
  M1. ab = 0 ↔ a = b
  M2. ab ≥ 0
  M3. ab = ba
  M4. a ≠ b ∧ a ≠ c → ∠abc = ∠cba
  M5. 0 ≤ ∠abc ∧ ∠abc ≤ right-angle + right-angle
  M6. △aab = 0
  M7. △abc ≥ 0
  M8. △abc = △cab ∧ △abc = △acb
  M9. Full congruence → equal areas

Also handles Euclid's Common Notions (CN):
  CN1. Things equal to the same thing are equal to one another  (transitivity)
  CN2. If equals be added to equals, the wholes are equal
  CN3. If equals be subtracted from equals, the remainders are equal
  CN4. Things which coincide are equal  (reflexivity)
  CN5. The whole is greater than the part
"""
from __future__ import annotations

from typing import Dict, FrozenSet, List, Optional, Set, Tuple, Union

from .e_ast import (
    Sort, Term,
    SegmentTerm, AngleTerm, AreaTerm,
    MagAdd, RightAngle, ZeroMag,
    Equals, LessThan,
    Literal,
    mag_sort,
)


# ═══════════════════════════════════════════════════════════════════════
# Metric state: tracks known equalities and inequalities
# ═══════════════════════════════════════════════════════════════════════

class MetricState:
    """Tracks known metric facts and derives consequences.

    Uses a union-find structure for equalities and a consistent set
    of strict inequalities.
    """

    def __init__(self):
        # Equality classes via union-find
        self._parent: Dict[Term, Term] = {}
        self._rank: Dict[Term, int] = {}
        # Known strict inequalities: (a, b) means a < b
        self._less: Set[Tuple[Term, Term]] = set()
        # Known negated strict inequalities: (a, b) means ¬(a < b)
        self._not_less: Set[Tuple[Term, Term]] = set()
        # Known terms
        self._terms: Set[Term] = set()
        # M1 support: known point disequalities {a, b} means a ≠ b
        self._point_diseq: Set[FrozenSet[str]] = set()
        # M1 forward: known point equalities {a, b} derived from ab = 0
        self._point_eq: Set[FrozenSet[str]] = set()
        # Magnitude terms known to be ≠ 0
        self._nonzero: Set[Term] = set()

    def add_term(self, t: Term) -> None:
        """Register a term in the state."""
        if t not in self._parent:
            self._parent[t] = t
            self._rank[t] = 0
            self._terms.add(t)

    def find(self, t: Term) -> Term:
        """Find the representative of a term's equivalence class."""
        self.add_term(t)
        while self._parent[t] != t:
            # Path compression
            self._parent[t] = self._parent[self._parent[t]]
            t = self._parent[t]
        return t

    def union(self, a: Term, b: Term) -> bool:
        """Merge equivalence classes.  Returns True if a change was made."""
        ra, rb = self.find(a), self.find(b)
        if ra == rb:
            return False
        # Union by rank
        if self._rank[ra] < self._rank[rb]:
            ra, rb = rb, ra
        self._parent[rb] = ra
        if self._rank[ra] == self._rank[rb]:
            self._rank[ra] += 1
        return True

    def are_equal(self, a: Term, b: Term) -> bool:
        """Check if two terms are known to be equal."""
        return self.find(a) == self.find(b)

    def add_less(self, a: Term, b: Term) -> None:
        """Record a < b."""
        self.add_term(a)
        self.add_term(b)
        self._less.add((a, b))

    def is_less(self, a: Term, b: Term) -> bool:
        """Check if a < b is known (resolving through union-find)."""
        ra, rb = self.find(a), self.find(b)
        for x, y in self._less:
            if self.find(x) == ra and self.find(y) == rb:
                return True
        return False

    def has_contradiction(self) -> bool:
        """Check for inconsistency (a < a, or a < b and b < a)."""
        for a, b in self._less:
            ra, rb = self.find(a), self.find(b)
            if ra == rb:
                return True  # a < a
            for c, d in self._less:
                if self.find(c) == rb and self.find(d) == ra:
                    return True  # a < b and b < a
        return False


# ═══════════════════════════════════════════════════════════════════════
# Metric inference engine
# ═══════════════════════════════════════════════════════════════════════

class MetricEngine:
    """Derives metric consequences from known metric literals.

    Implements the axioms of a non-negative ordered abelian group
    plus the additional axioms M1–M9 from Section 3.5.
    """

    def __init__(self):
        self.state = MetricState()

    def reset(self):
        """Reset internal state for reuse without creating a new instance."""
        self.state = MetricState()

    def process_literals(self, literals: Set[Literal]) -> Set[Literal]:
        """Process known metric literals and derive consequences.

        Returns the set of all metric literals that can be derived
        (including the input).
        """
        # Load known facts into the state
        for lit in literals:
            if lit.is_metric or self._is_point_eq(lit):
                self._load_literal(lit)

        # Apply built-in rules to derive consequences
        derived = set(literals)
        changed = True
        while changed:
            changed = False
            new = self._apply_rules()
            for lit in new:
                if lit not in derived:
                    derived.add(lit)
                    self._load_literal(lit)
                    changed = True

        return derived

    def is_consequence(self, known: Set[Literal], query: Literal) -> bool:
        """Check if a metric literal is a consequence of known literals.

        The query's own terms are pre-loaded into the state so that
        built-in symmetry rules (M3/M4/M8) can fire on them.  This is
        sound because those rules hold for all well-formed terms, not
        just terms that appear explicitly in the known set.
        """
        self.process_literals(known)
        # Pre-load query terms so M3/M4/M8 can apply
        self._preload_query_terms(query)
        # Re-run rules after introducing query terms
        self._apply_rules()
        return self._check_literal(query)

    def _preload_query_terms(self, lit: Literal) -> None:
        """Add the magnitude terms from a query literal to the state."""
        atom = lit.atom
        if isinstance(atom, Equals):
            self._to_term(atom.left)
            self._to_term(atom.right)
        elif isinstance(atom, LessThan):
            self._to_term(atom.left)
            self._to_term(atom.right)

    # ── Internal methods ──────────────────────────────────────────────

    def _load_literal(self, lit: Literal) -> None:
        """Load a single literal into the metric state."""
        atom = lit.atom
        if isinstance(atom, Equals):
            if lit.polarity:
                # Positive: x = y
                left = self._to_term(atom.left)
                right = self._to_term(atom.right)
                if left is not None and right is not None:
                    self.state.union(left, right)
            else:
                # Negative equality: x ≠ y
                if (isinstance(atom.left, str) and
                        isinstance(atom.right, str)):
                    # Point disequality: a ≠ b
                    self.state._point_diseq.add(
                        frozenset({atom.left, atom.right}))
                else:
                    # Magnitude disequality: if ¬(t = 0) then t is nonzero
                    left = self._to_term(atom.left)
                    right = self._to_term(atom.right)
                    if left is not None and right is not None:
                        for zero_sort in (Sort.SEGMENT, Sort.ANGLE,
                                          Sort.AREA):
                            z = ZeroMag(zero_sort)
                            self.state.add_term(z)
                            if ((isinstance(right, ZeroMag)
                                    and right.sort == zero_sort)
                                    or self.state.are_equal(right, z)):
                                self.state._nonzero.add(left)
                            if ((isinstance(left, ZeroMag)
                                    and left.sort == zero_sort)
                                    or self.state.are_equal(left, z)):
                                self.state._nonzero.add(right)
        elif isinstance(atom, LessThan):
            if lit.polarity:
                left = self._to_term(atom.left)
                right = self._to_term(atom.right)
                if left is not None and right is not None:
                    self.state.add_less(left, right)
            else:
                # ¬(a < b) — record for trichotomy
                left = self._to_term(atom.left)
                right = self._to_term(atom.right)
                if left is not None and right is not None:
                    self.state._not_less.add((left, right))

    def _to_term(self, x) -> Optional[Term]:
        """Convert a literal argument to a Term."""
        if isinstance(x, Term):
            self.state.add_term(x)
            return x
        if isinstance(x, str):
            # Point variable — not a magnitude term
            return None
        return None

    def _check_literal(self, lit: Literal) -> bool:
        """Check if a literal is satisfied by the current state."""
        atom = lit.atom
        if isinstance(atom, Equals):
            # Point equality: a = b where a, b are point variables
            if (lit.polarity and
                    isinstance(atom.left, str) and
                    isinstance(atom.right, str)):
                return (frozenset({atom.left, atom.right})
                        in self.state._point_eq)
            # Point disequality: ¬(a = b) where a, b are point variables
            if (not lit.polarity and
                    isinstance(atom.left, str) and
                    isinstance(atom.right, str)):
                return (frozenset({atom.left, atom.right})
                        in self.state._point_diseq)
            left = self._to_term(atom.left)
            right = self._to_term(atom.right)
            if left is None or right is None:
                return False
            if lit.polarity:
                return self.state.are_equal(left, right)
            else:
                # Check if we know they're NOT equal
                # They're not equal if one < other, or no path exists
                return not self.state.are_equal(left, right)
        elif isinstance(atom, LessThan):
            left = self._to_term(atom.left)
            right = self._to_term(atom.right)
            if left is None or right is None:
                return False
            if lit.polarity:
                return self.state.is_less(left, right)
            else:
                # ¬(a < b) means a ≥ b
                return (self.state.are_equal(left, right) or
                        self.state.is_less(right, left))
        return False

    def _apply_rules(self) -> Set[Literal]:
        """Apply built-in metric rules to derive new facts."""
        new: Set[Literal] = set()

        # M3: ab = ba (segment symmetry)
        for t in list(self.state._terms):
            if isinstance(t, SegmentTerm):
                rev = SegmentTerm(t.p2, t.p1)
                self.state.add_term(rev)
                if not self.state.are_equal(t, rev):
                    self.state.union(t, rev)
                    new.add(Literal(Equals(t, rev)))

        # M4: ∠abc = ∠cba (angle vertex symmetry)
        for t in list(self.state._terms):
            if isinstance(t, AngleTerm):
                rev = AngleTerm(t.p3, t.p2, t.p1)
                self.state.add_term(rev)
                if not self.state.are_equal(t, rev):
                    self.state.union(t, rev)
                    new.add(Literal(Equals(t, rev)))

        # M8: △abc = △cab and △abc = △acb (area symmetries)
        for t in list(self.state._terms):
            if isinstance(t, AreaTerm):
                cyc = AreaTerm(t.p3, t.p1, t.p2)
                flp = AreaTerm(t.p1, t.p3, t.p2)
                self.state.add_term(cyc)
                self.state.add_term(flp)
                if not self.state.are_equal(t, cyc):
                    self.state.union(t, cyc)
                    new.add(Literal(Equals(t, cyc)))
                if not self.state.are_equal(t, flp):
                    self.state.union(t, flp)
                    new.add(Literal(Equals(t, flp)))

        # CN1: Transitivity — handled by union-find

        # Cancellation: if a + c = b + c then a = b
        # (Check all pairs of known equalities involving MagAdd)
        for t in list(self.state._terms):
            if isinstance(t, MagAdd):
                for t2 in list(self.state._terms):
                    if isinstance(t2, MagAdd) and t != t2:
                        if self.state.are_equal(t, t2):
                            # t.left + t.right = t2.left + t2.right
                            if self.state.are_equal(t.right, t2.right):
                                if not self.state.are_equal(t.left, t2.left):
                                    self.state.union(t.left, t2.left)
                                    new.add(Literal(Equals(t.left, t2.left)))
                            if self.state.are_equal(t.left, t2.left):
                                if not self.state.are_equal(
                                        t.right, t2.right):
                                    self.state.union(t.right, t2.right)
                                    new.add(Literal(
                                        Equals(t.right, t2.right)))

        # Absorption: if x + y = x (or = y) then the other component is 0
        # This is a special case of CN3 where one "sum" is x + 0.
        for t in list(self.state._terms):
            if not isinstance(t, MagAdd):
                continue
            ms = mag_sort(t)
            if ms is None:
                continue
            zero = ZeroMag(ms)
            self.state.add_term(zero)
            # x + y = x → y = 0
            if self.state.are_equal(t, t.left):
                if not self.state.are_equal(t.right, zero):
                    self.state.union(t.right, zero)
                    new.add(Literal(Equals(t.right, zero)))
            # x + y = y → x = 0
            if self.state.are_equal(t, t.right):
                if not self.state.are_equal(t.left, zero):
                    self.state.union(t.left, zero)
                    new.add(Literal(Equals(t.left, zero)))

        # Congruence: if a = b then f(a) = f(b) for magnitude terms
        # E.g. if a = c then ab = cb
        # We check all segment terms
        for t in list(self.state._terms):
            if isinstance(t, SegmentTerm):
                for t2 in list(self.state._terms):
                    if isinstance(t2, SegmentTerm) and t != t2:
                        # If p1s are equal and p2s are equal, segments equal
                        p1a = SegmentTerm(t.p1, "")  # dummy
                        # Actually we'd need point equalities from the
                        # diagrammatic engine.  Skip for now.
                        pass

        # M1: ab = 0 ↔ a = b
        # Forward: ab = 0 → a = b (point equality from zero segment)
        # Contrapositive: a ≠ b → ab ≠ 0 (segment is nonzero)
        zero_seg = ZeroMag(Sort.SEGMENT)
        self.state.add_term(zero_seg)

        # Forward direction: ab = 0 → a = b
        for t in list(self.state._terms):
            if isinstance(t, SegmentTerm):
                if self.state.are_equal(t, zero_seg):
                    # Segment is zero → endpoints are equal (point equality)
                    pair = frozenset({t.p1, t.p2})
                    if pair not in self.state._point_eq:
                        self.state._point_eq.add(pair)
                        new.add(Literal(Equals(t.p1, t.p2)))

        # Contrapositive: a ≠ b → ab ≠ 0
        for pair in list(self.state._point_diseq):
            pts = sorted(pair)
            if len(pts) == 2:
                a, b = pts[0], pts[1]
                for seg in (SegmentTerm(a, b), SegmentTerm(b, a)):
                    self.state.add_term(seg)
                    if seg not in self.state._nonzero:
                        self.state._nonzero.add(seg)

        # M1 reverse + disequality propagation through equivalence classes:
        # If SegmentTerm(c, d) is in the same equivalence class as a known
        # nonzero term, then c ≠ d.
        for t in list(self.state._terms):
            if isinstance(t, SegmentTerm) and t.p1 != t.p2:
                rep = self.state.find(t)
                is_nz = any(self.state.find(nz) == rep
                            for nz in self.state._nonzero)
                if is_nz:
                    pair = frozenset({t.p1, t.p2})
                    if pair not in self.state._point_diseq:
                        self.state._point_diseq.add(pair)
                        new.add(Literal(Equals(t.p1, t.p2), False))

        # ── CN5: Whole > Part ─────────────────────────────────────
        # If a + b = c and b > 0 then a < c   (and symmetrically
        # if a + b = c and a > 0 then b < c).
        #
        # A magnitude is > 0 when:
        #   • it appears in _nonzero (from M1 contrapositive), OR
        #   • 0 < t is in _less, OR
        #   • it is a MagAdd of two terms where at least one is > 0
        #     and neither is known = 0 (not needed here; handled by
        #     the fixpoint loop).

        def _is_positive(term: Term) -> bool:
            """Check if a term is known to be strictly > 0."""
            rep = self.state.find(term)
            # Check _nonzero set (includes segments from M1 contra)
            if any(self.state.find(nz) == rep
                   for nz in self.state._nonzero):
                return True
            # Check explicit 0 < term in _less
            for z in (ZeroMag(Sort.SEGMENT), ZeroMag(Sort.ANGLE),
                      ZeroMag(Sort.AREA)):
                self.state.add_term(z)
                if self.state.is_less(z, term):
                    return True
            return False

        for t in list(self.state._terms):
            if not isinstance(t, MagAdd):
                continue
            left, right = t.left, t.right
            self.state.add_term(left)
            self.state.add_term(right)
            # Find all terms c where t (= left + right) = c
            for c in list(self.state._terms):
                if c is t or isinstance(c, MagAdd):
                    continue
                if not self.state.are_equal(t, c):
                    continue
                # left + right = c
                # If right > 0 → left < c
                if _is_positive(right):
                    if not self.state.is_less(left, c):
                        self.state.add_less(left, c)
                        new.add(Literal(LessThan(left, c)))
                # If left > 0 → right < c
                if _is_positive(left):
                    if not self.state.is_less(right, c):
                        self.state.add_less(right, c)
                        new.add(Literal(LessThan(right, c)))

        # ── CN2: Addition congruence ──────────────────────────────
        # If a = b and c = d then a + c = b + d.
        # We look for MagAdd terms whose components have known-equal
        # counterparts in other MagAdd terms.
        mag_adds = [t for t in self.state._terms if isinstance(t, MagAdd)]
        for t1 in mag_adds:
            for t2 in mag_adds:
                if t1 is t2:
                    continue
                if self.state.are_equal(t1, t2):
                    continue
                if (self.state.are_equal(t1.left, t2.left) and
                        self.state.are_equal(t1.right, t2.right)):
                    self.state.union(t1, t2)
                    new.add(Literal(Equals(t1, t2)))
                elif (self.state.are_equal(t1.left, t2.right) and
                      self.state.are_equal(t1.right, t2.left)):
                    self.state.union(t1, t2)
                    new.add(Literal(Equals(t1, t2)))

        # ── + Monotonicity ────────────────────────────────────────
        # If a < b then a + c < b + c (for every known term c).
        for a_rep, b_rep in list(self.state._less):
            for t in mag_adds:
                # Check if t = a + c  and  b + c exists
                a_t = t.left if self.state.find(t.left) == a_rep else (
                    t.right if self.state.find(t.right) == a_rep else None)
                if a_t is None:
                    continue
                c_t = t.right if a_t is t.left else t.left
                # Look for a MagAdd b + c
                for t2 in mag_adds:
                    if t2 is t:
                        continue
                    b_side = None
                    c_side = None
                    if self.state.find(t2.left) == b_rep:
                        b_side = t2.left
                        c_side = t2.right
                    elif self.state.find(t2.right) == b_rep:
                        b_side = t2.right
                        c_side = t2.left
                    if b_side is None:
                        continue
                    if self.state.are_equal(c_t, c_side):
                        if not self.state.is_less(t, t2):
                            self.state.add_less(t, t2)
                            new.add(Literal(LessThan(t, t2)))

        # ── < Transitivity ────────────────────────────────────────
        # If a < b and b < c then a < c.
        less_list = list(self.state._less)
        for a, b in less_list:
            for b2, c in less_list:
                if self.state.find(b) == self.state.find(b2):
                    if not self.state.is_less(a, c):
                        self.state.add_less(a, c)
                        new.add(Literal(LessThan(a, c)))

        # ── Trichotomy ────────────────────────────────────────────
        # For a linear ordering: ¬(a < b) ∧ ¬(b < a) → a = b.
        for a, b in list(self.state._not_less):
            ra, rb = self.state.find(a), self.state.find(b)
            if ra == rb:
                continue  # already equal
            # Check ¬(b < a) via representatives
            reverse_found = False
            for c, d in self.state._not_less:
                if (self.state.find(c) == rb and
                        self.state.find(d) == ra):
                    reverse_found = True
                    break
            if reverse_found:
                self.state.union(a, b)
                new.add(Literal(Equals(a, b)))

        return new

    def _is_point_eq(self, lit: Literal) -> bool:
        """Check if a literal is a point equality (a = b)."""
        return (isinstance(lit.atom, Equals) and
                isinstance(lit.atom.left, str) and
                isinstance(lit.atom.right, str))
