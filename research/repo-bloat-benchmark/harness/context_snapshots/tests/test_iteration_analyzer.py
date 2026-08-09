"""Tests for the iteration-trajectory analysis (H2 machinery)."""

from harness.context_snapshots.attribution import Attribution
from harness.context_snapshots.iteration_analyzer import (
    analyze_run,
    classify_growth_shape,
)
from harness.context_snapshots.schema import SnapshotRecord


def _record(ordinal, input_tokens, edit=False):
    return SnapshotRecord(
        run_id="run",
        ordinal=ordinal,
        timestamp=1000.0 + ordinal,
        endpoint="/v1/chat/completions",
        request_sha256="0" * 64,
        payload_path=f"payloads/{ordinal:05d}.request.json",
        input_tokens=input_tokens,
        edit_tool_call=edit,
    )


def test_gradual_growth_classified():
    # Linear accretion: every request adds ~1000 tokens.
    records = [_record(i, 1000 * i) for i in range(1, 10)]
    trajectory = analyze_run(records)
    assert trajectory.growth_shape == "gradual"
    assert trajectory.iterations_total == 9
    assert trajectory.largest_single_jump_share < 0.30


def test_step_growth_classified():
    # One giant read dominates the final context.
    tokens = [1000, 1100, 9000, 9100, 9200, 9300]
    records = [_record(i + 1, t) for i, t in enumerate(tokens)]
    trajectory = analyze_run(records)
    assert trajectory.growth_shape == "step"
    assert trajectory.largest_single_jump_share > 0.30


def test_plateau_classified():
    # Steady growth that stalls (truncation ceiling) with no dominating jump:
    # step takes precedence over plateau, so no single growth may exceed 30%.
    tokens = [3000, 5500, 8000, 10500, 11000, 11050, 11080, 11100, 11110]
    records = [_record(i + 1, t) for i, t in enumerate(tokens)]
    trajectory = analyze_run(records)
    assert trajectory.growth_shape == "plateau"


def test_sawtooth_classified():
    # Context shrinks mid-run: compaction dropped content.
    tokens = [3000, 6000, 9000, 4000, 7000, 10000]
    records = [_record(i + 1, t) for i, t in enumerate(tokens)]
    trajectory = analyze_run(records)
    assert trajectory.growth_shape == "sawtooth"


def test_first_edit_boundary():
    records = [
        _record(1, 1000),
        _record(2, 2000),
        _record(3, 3000, edit=True),
        _record(4, 4000),
    ]
    trajectory = analyze_run(records)
    assert trajectory.first_edit_ordinal == 3
    assert trajectory.iterations_before_first_edit == 2


def test_no_edit_ever():
    records = [_record(1, 1000), _record(2, 2000)]
    trajectory = analyze_run(records)
    assert trajectory.first_edit_ordinal is None
    assert trajectory.iterations_before_first_edit is None


def test_phase_medians_and_share_delta():
    records = []
    attributions = []
    for i in range(1, 10):
        records.append(_record(i, 1000 * i))
        # Distractor share climbs from 0.1 to 0.9 across the run.
        share = i / 10.0
        attributions.append(
            Attribution(distractor_tokens=share * 100, core_tokens=(1 - share) * 100)
        )
    trajectory = analyze_run(records, attributions)
    early = trajectory.distractor_share_early
    late = trajectory.distractor_share_late
    assert early is not None and late is not None
    assert late > early
    assert trajectory.share_delta_late_minus_early is not None
    assert trajectory.share_delta_late_minus_early > 0.3
    assert [p.name for p in trajectory.phases] == ["early", "middle", "late"]


def test_missing_usage_tolerated():
    records = [
        _record(1, None),
        _record(2, 2000),
        _record(3, None),
        _record(4, 4000),
    ]
    trajectory = analyze_run(records)
    assert trajectory.iterations_total == 4  # no crash; growth where computable


def test_classify_growth_shape_empty():
    shape, share = classify_growth_shape([], None)
    assert shape == "unknown"
    assert share is None
