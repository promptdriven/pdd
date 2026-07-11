"""Per-iteration analysis of the snapshot series (design.md §6.1, H2).

Turns the ordered ``SnapshotRecord`` sequence (plus optional per-request
attribution) into the pre-registered *iteration trajectory* family:

- per-request ``input_tokens`` and ``context_growth`` series,
- per-request ``distractor_context_share`` series,
- early / middle / late phase medians (thirds by request ordinal),
- ``growth_shape`` classification: ``gradual`` / ``step`` / ``plateau`` /
  ``sawtooth`` (thresholds fixed here, mirrored in design §6.1; precedence
  when curves qualify for more than one class: sawtooth → step → plateau →
  gradual),
- ``largest_single_jump_share``,
- first-edit boundary (`iterations_before_first_edit`).

The shape thresholds are part of the pre-registration: changing them after
runs is a new experiment.
"""

from __future__ import annotations

from dataclasses import dataclass, field
from statistics import median
from typing import Sequence

from .attribution import Attribution
from .schema import SnapshotRecord

# Pre-registered classification thresholds (design §6.1).
STEP_JUMP_SHARE = 0.30  # one request contributing > 30% of final context ⇒ step
PLATEAU_TAIL_SHARE = 0.05  # < 5% of final context added in the last third ⇒ plateau
SAWTOOTH_DROP_TOLERANCE = 0.02  # relative shrink > 2% of final context ⇒ sawtooth


@dataclass
class IterationPoint:
    ordinal: int
    input_tokens: int | None
    context_growth: int | None  # None for the first point / missing usage
    distractor_share: float | None
    distractor_tokens: float | None
    edit_tool_call: bool


@dataclass
class PhaseStats:
    name: str  # early / middle / late
    ordinals: list[int]
    median_input_tokens: float | None
    median_growth: float | None
    median_distractor_share: float | None


@dataclass
class RunTrajectory:
    run_id: str
    iterations_total: int
    iterations_before_first_edit: int | None  # None ⇒ no edit ever happened
    first_edit_ordinal: int | None
    growth_shape: str
    largest_single_jump_share: float | None
    points: list[IterationPoint] = field(default_factory=list)
    phases: list[PhaseStats] = field(default_factory=list)

    @property
    def distractor_share_early(self) -> float | None:
        return self._phase_share("early")

    @property
    def distractor_share_late(self) -> float | None:
        return self._phase_share("late")

    def _phase_share(self, name: str) -> float | None:
        for phase in self.phases:
            if phase.name == name:
                return phase.median_distractor_share
        return None

    @property
    def share_delta_late_minus_early(self) -> float | None:
        early, late = self.distractor_share_early, self.distractor_share_late
        if early is None or late is None:
            return None
        return late - early


def _thirds(n: int) -> list[tuple[str, range]]:
    """Split ordinals 1..n into early/middle/late thirds (early gets remainder)."""
    if n <= 0:
        return []
    third = max(1, n // 3)
    early_end = n - 2 * third  # early takes the remainder for small n
    return [
        ("early", range(1, early_end + 1)),
        ("middle", range(early_end + 1, early_end + third + 1)),
        ("late", range(early_end + third + 1, n + 1)),
    ]


def _median_or_none(values: Sequence[float]) -> float | None:
    values = [v for v in values if v is not None]
    return median(values) if values else None


def classify_growth_shape(
    growths: Sequence[int], final_tokens: int | None
) -> tuple[str, float | None]:
    """Classify the cumulative-context curve; returns (shape, largest_jump_share)."""
    growths = [g for g in growths if g is not None]
    if not growths or not final_tokens or final_tokens <= 0:
        return "unknown", None
    largest_jump = max(growths)
    largest_share = largest_jump / final_tokens
    total_growth = sum(growths)
    if any(g < -SAWTOOTH_DROP_TOLERANCE * final_tokens for g in growths):
        return "sawtooth", largest_share
    if largest_share > STEP_JUMP_SHARE:
        return "step", largest_share
    tail_count = max(1, len(growths) // 3)
    tail_growth = sum(growths[-tail_count:])
    if total_growth > 0 and tail_growth < PLATEAU_TAIL_SHARE * final_tokens:
        return "plateau", largest_share
    return "gradual", largest_share


def analyze_run(
    records: Sequence[SnapshotRecord],
    attributions: Sequence[Attribution] | None = None,
) -> RunTrajectory:
    """Build the iteration-trajectory family for one run.

    ``records`` must be the full ordered snapshot series of a single run;
    ``attributions`` (optional) must be parallel to ``records``.
    """
    records = sorted(records, key=lambda r: r.ordinal)
    if attributions is not None and len(attributions) != len(records):
        raise ValueError("attributions must be parallel to records")

    run_id = records[0].run_id if records else ""
    points: list[IterationPoint] = []
    previous_tokens: int | None = None
    first_edit_ordinal: int | None = None

    for i, record in enumerate(records):
        growth: int | None = None
        if record.input_tokens is not None and previous_tokens is not None:
            growth = record.input_tokens - previous_tokens
        if record.input_tokens is not None:
            previous_tokens = record.input_tokens
        share = tokens = None
        if attributions is not None:
            attribution = attributions[i]
            share = attribution.distractor_share
            tokens = attribution.distractor_tokens
        if record.edit_tool_call and first_edit_ordinal is None:
            first_edit_ordinal = record.ordinal
        points.append(
            IterationPoint(
                ordinal=record.ordinal,
                input_tokens=record.input_tokens,
                context_growth=growth,
                distractor_share=share,
                distractor_tokens=tokens,
                edit_tool_call=record.edit_tool_call,
            )
        )

    final_tokens = next(
        (p.input_tokens for p in reversed(points) if p.input_tokens is not None), None
    )
    shape, largest_share = classify_growth_shape(
        [p.context_growth for p in points], final_tokens
    )

    phases: list[PhaseStats] = []
    by_ordinal = {p.ordinal: p for p in points}
    for name, ordinal_range in _thirds(len(points)):
        phase_points = [by_ordinal[o] for o in ordinal_range if o in by_ordinal]
        phases.append(
            PhaseStats(
                name=name,
                ordinals=[p.ordinal for p in phase_points],
                median_input_tokens=_median_or_none(
                    [p.input_tokens for p in phase_points]
                ),
                median_growth=_median_or_none(
                    [p.context_growth for p in phase_points]
                ),
                median_distractor_share=_median_or_none(
                    [p.distractor_share for p in phase_points]
                ),
            )
        )

    return RunTrajectory(
        run_id=run_id,
        iterations_total=len(points),
        iterations_before_first_edit=(
            first_edit_ordinal - 1 if first_edit_ordinal is not None else None
        ),
        first_edit_ordinal=first_edit_ordinal,
        growth_shape=shape,
        largest_single_jump_share=largest_share,
        points=points,
        phases=phases,
    )
