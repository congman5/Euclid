"""
e_discovery.py — Transfer oracle / discovery tool for System E.

Given a set of known facts and variable sorts, runs the full pipeline
(diagrammatic closure → transfer → metric) and reports ALL derivable
facts, grouped by type.  Designed to eliminate the "guess the exact
structural form" problem that blocks proof writing.

Usage (standalone)::

    from verifier.e_discovery import discover_all
    facts = discover_all(known_literals, variables)
    facts.print_report()

Usage (from PB proof builder)::

    pb.discover()   # prints what's derivable at the current proof state
"""
from __future__ import annotations

from dataclasses import dataclass, field
from typing import Dict, List, Optional, Set

from .e_ast import (
    Sort, Literal,
    Equals, LessThan,
    SegmentTerm, AngleTerm, AreaTerm, MagAdd, RightAngle, ZeroMag,
    On, SameSide, Between, Center, Inside, Intersects,
)
from .e_axioms import ALL_DIAGRAMMATIC_AXIOMS, ALL_TRANSFER_AXIOMS
from .e_consequence import ConsequenceEngine
from .e_transfer import TransferEngine
from .e_metric import MetricEngine


@dataclass
class DiscoveryReport:
    """Grouped derivable facts from the full engine pipeline."""

    # Diagrammatic facts
    on_facts: List[Literal] = field(default_factory=list)
    same_side: List[Literal] = field(default_factory=list)
    between: List[Literal] = field(default_factory=list)
    circle_facts: List[Literal] = field(default_factory=list)
    diag_equalities: List[Literal] = field(default_factory=list)
    diag_negations: List[Literal] = field(default_factory=list)

    # Transfer-derived (metric from diagram or diagram from metric)
    angle_sums: List[Literal] = field(default_factory=list)
    segment_sums: List[Literal] = field(default_factory=list)
    area_decomps: List[Literal] = field(default_factory=list)
    nonzero: List[Literal] = field(default_factory=list)
    angle_equalities: List[Literal] = field(default_factory=list)
    segment_equalities: List[Literal] = field(default_factory=list)
    area_equalities: List[Literal] = field(default_factory=list)
    inequalities: List[Literal] = field(default_factory=list)

    # Metric-derived
    metric_derived: List[Literal] = field(default_factory=list)

    # All facts (union)
    all_facts: Set[Literal] = field(default_factory=set)

    def print_report(self, *, show_negations: bool = False) -> None:
        """Pretty-print the discovery report to stdout."""
        import sys
        out = sys.stdout

        def _section(title: str, items: list) -> None:
            if not items:
                return
            out.write(f"\n  {title} ({len(items)}):\n")
            for lit in sorted(items, key=str):
                out.write(f"    {lit}\n")

        out.write("═══ Discovery Report ═══\n")

        # Diagrammatic
        _section("on()", self.on_facts)
        _section("same-side()", self.same_side)
        _section("between()", self.between)
        _section("Circle facts", self.circle_facts)
        _section("Diagrammatic equalities", self.diag_equalities)
        if show_negations:
            _section("Diagrammatic negations", self.diag_negations)
        else:
            neg_count = len(self.diag_negations)
            if neg_count:
                out.write(
                    f"\n  Diagrammatic negations: {neg_count} "
                    f"(use show_negations=True to list)\n")

        # Transfer-derived
        _section("Angle sums (DA2)", self.angle_sums)
        _section("Segment sums (betweenness)", self.segment_sums)
        _section("Area decompositions (DAr2)", self.area_decomps)
        _section("Nonzero (DAr1c etc.)", self.nonzero)
        _section("Angle equalities", self.angle_equalities)
        _section("Segment equalities", self.segment_equalities)
        _section("Area equalities", self.area_equalities)
        _section("Inequalities (<)", self.inequalities)

        # Metric
        _section("Metric derived", self.metric_derived)

        out.write(f"\n  Total facts: {len(self.all_facts)}\n")
        out.write("════════════════════════\n")


def _classify_literal(
    lit: Literal,
    report: DiscoveryReport,
    *,
    is_transfer: bool = False,
    is_metric_only: bool = False,
) -> None:
    """Classify a literal into the appropriate report bucket."""
    atom = lit.atom

    # --- Diagrammatic atoms ---
    if isinstance(atom, On):
        if lit.polarity:
            report.on_facts.append(lit)
        else:
            report.diag_negations.append(lit)
    elif isinstance(atom, SameSide):
        if lit.polarity:
            report.same_side.append(lit)
        else:
            report.diag_negations.append(lit)
    elif isinstance(atom, Between):
        if lit.polarity:
            report.between.append(lit)
        else:
            report.diag_negations.append(lit)
    elif isinstance(atom, (Center, Inside, Intersects)):
        if lit.polarity:
            report.circle_facts.append(lit)
        else:
            report.diag_negations.append(lit)
    elif isinstance(atom, Equals):
        left, right = atom.left, atom.right
        # Diagrammatic point/line equality
        if isinstance(left, str) and isinstance(right, str):
            if lit.polarity:
                report.diag_equalities.append(lit)
            else:
                report.diag_negations.append(lit)
        # Metric equalities
        elif not lit.polarity:
            # Negated metric equality → nonzero
            if isinstance(right, ZeroMag) or isinstance(left, ZeroMag):
                report.nonzero.append(lit)
            else:
                report.diag_negations.append(lit)
        else:
            # Positive metric equality
            _has_add = isinstance(left, MagAdd) or isinstance(right, MagAdd)
            if _has_add:
                # Sum equation
                if _any_term_is(left, AngleTerm) or _any_term_is(
                        right, AngleTerm):
                    report.angle_sums.append(lit)
                elif _any_term_is(left, AreaTerm) or _any_term_is(
                        right, AreaTerm):
                    report.area_decomps.append(lit)
                elif _any_term_is(left, SegmentTerm) or _any_term_is(
                        right, SegmentTerm):
                    report.segment_sums.append(lit)
                else:
                    report.metric_derived.append(lit)
            elif _any_term_is(left, AngleTerm) or _any_term_is(
                    right, AngleTerm):
                report.angle_equalities.append(lit)
            elif _any_term_is(left, AreaTerm) or _any_term_is(
                    right, AreaTerm):
                report.area_equalities.append(lit)
            elif _any_term_is(left, SegmentTerm) or _any_term_is(
                    right, SegmentTerm):
                report.segment_equalities.append(lit)
            else:
                report.metric_derived.append(lit)
    elif isinstance(atom, LessThan):
        report.inequalities.append(lit)
    else:
        if is_metric_only:
            report.metric_derived.append(lit)
        elif lit.is_diagrammatic:
            if lit.polarity:
                report.diag_equalities.append(lit)
            else:
                report.diag_negations.append(lit)
        else:
            report.metric_derived.append(lit)


def _any_term_is(term, cls) -> bool:
    """Check if a term or any sub-term is an instance of cls."""
    if isinstance(term, cls):
        return True
    if isinstance(term, MagAdd):
        return _any_term_is(term.left, cls) or _any_term_is(term.right, cls)
    return False


def discover_all(
    known: Set[Literal],
    variables: Dict[str, Sort],
    *,
    include_input: bool = False,
) -> DiscoveryReport:
    """Run the full engine pipeline and return all derivable facts.

    Args:
        known: Initial set of known literals (premises + derived so far).
        variables: Mapping from variable names to sorts.
        include_input: If True, also classify input literals in the report.

    Returns:
        A DiscoveryReport with grouped facts.
    """
    report = DiscoveryReport()
    input_set = set(known) if not include_input else set()

    # 1. Diagrammatic closure
    ce = ConsequenceEngine(ALL_DIAGRAMMATIC_AXIOMS)
    closure = ce.direct_consequences(known, variables)

    # 2. Transfer derivation
    diagram_known = {lit for lit in closure if lit.is_diagrammatic}
    metric_known = {lit for lit in closure if lit.is_metric}
    te = TransferEngine(ALL_TRANSFER_AXIOMS)
    transfer_derived = te.apply_transfers(diagram_known, metric_known,
                                          variables)

    # 3. Metric engine on combined facts
    me = MetricEngine()
    all_metric = metric_known | {lit for lit in transfer_derived
                                 if lit.is_metric}
    metric_derived = me.process_literals(all_metric)

    # Combine everything
    all_facts = closure | transfer_derived | metric_derived
    report.all_facts = all_facts

    # Classify each fact
    for lit in all_facts:
        if not include_input and lit in input_set:
            continue
        _classify_literal(lit, report)

    return report
