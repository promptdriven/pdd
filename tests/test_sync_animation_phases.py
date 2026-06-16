"""Tests for the pipeline-stage animation model (issue #1560, workstream 6).

The sync animation was redesigned so its motion mirrors the real system flow:
high-level boxes for the framing stages (entry / inspect / plan / output) and an
expanded, detailed view for the command-execution loop. These tests pin the
mapping from orchestrator function names to pipeline stages, the step-strip
progression, and that every frame stays a fixed-height, crash-free render.
"""

from rich.console import Console

from pdd.sync_animation import (
    AnimationState,
    ANIMATION_BOX_HEIGHT,
    COMMAND_SEQUENCE,
    PIPELINE_STAGES,
    STAGE_ENTRY,
    STAGE_INSPECT,
    STAGE_PLAN,
    STAGE_EXECUTE,
    STAGE_OUTPUT,
    _render_animation_frame,
    _render_phase_rail,
    _render_step_strip,
    stage_for_function,
)

PATHS = ("p.prompt", "c.py", "e.py", "t.py")


def _render_lines(state: AnimationState, width: int = 80):
    console = Console(width=width)
    with console.capture() as cap:
        console.print(_render_animation_frame(state, width), end="")
    return [ln for ln in cap.get().split("\n") if ln != ""]


class TestStageMapping:
    """stage_for_function classifies every orchestrator signal correctly."""

    def test_initializing_is_inspect(self):
        # Entry (arg parse) is done by the time the main frame renders.
        assert stage_for_function("initializing") == STAGE_INSPECT

    def test_checking_is_plan(self):
        assert stage_for_function("checking") == STAGE_PLAN

    def test_operations_are_execute(self):
        for op in ["auto-deps", "generate", "example", "verify", "crash",
                   "test", "test_extend", "fix", "update"]:
            assert stage_for_function(op) == STAGE_EXECUTE, op

    def test_terminal_states_are_output(self):
        for fn in ["synced", "nothing", "all_synced", "conflict", "error",
                   "fail_and_request_manual_merge"]:
            assert stage_for_function(fn) == STAGE_OUTPUT, fn

    def test_unknown_defaults_to_execute(self):
        # A future/unknown operation name is still command execution, never a
        # fake stage.
        assert stage_for_function("some_new_op") == STAGE_EXECUTE

    def test_blank_and_none_are_entry_inspect(self):
        assert stage_for_function("") == STAGE_INSPECT
        assert stage_for_function(None) == STAGE_INSPECT

    def test_pipeline_has_all_five_stages_in_order(self):
        ids = [s[0] for s in PIPELINE_STAGES]
        assert ids == [STAGE_ENTRY, STAGE_INSPECT, STAGE_PLAN,
                       STAGE_EXECUTE, STAGE_OUTPUT]


class TestExecutedStepProgression:
    """The step strip records completed execute-loop steps as ops change."""

    def test_steps_accumulate_in_order(self):
        state = AnimationState(basename="m", budget=5.0)
        for fn in ["initializing", "auto-deps", "generate", "example",
                   "verify", "test", "fix", "update"]:
            state.update_dynamic_state(fn, 0.0, *PATHS)
        # Every prior execute op (canonicalized) is marked done; the current
        # op (update) is not yet in the completed set.
        assert state.executed_steps == [
            "auto-deps", "generate", "example", "verify", "test", "fix"
        ]

    def test_aliases_collapse_onto_canonical_slot(self):
        state = AnimationState(basename="m", budget=5.0)
        # crash is the failure face of verify; test_extend continues test.
        for fn in ["generate", "crash", "verify", "test", "test_extend", "fix"]:
            state.update_dynamic_state(fn, 0.0, *PATHS)
        assert "verify" in state.executed_steps
        assert "test" in state.executed_steps
        assert "crash" not in state.executed_steps
        assert "test_extend" not in state.executed_steps

    def test_non_execute_states_do_not_pollute_steps(self):
        state = AnimationState(basename="m", budget=5.0)
        for fn in ["initializing", "checking", "synced"]:
            state.update_dynamic_state(fn, 0.0, *PATHS)
        assert state.executed_steps == []


class TestFrameRendering:
    """Every frame is a fixed-height, non-crashing render at any width."""

    def test_height_is_stable_across_stages_and_widths(self):
        for fn in ["initializing", "checking", "generate", "verify", "crash",
                   "test", "update", "synced", "conflict", "error"]:
            for width in [20, 30, 44, 80, 120, 160]:
                state = AnimationState(basename="calculator", budget=None)
                state.update_dynamic_state(fn, 0.42, *PATHS)
                state.frame_count = 3
                lines = _render_lines(state, width)
                assert len(lines) == ANIMATION_BOX_HEIGHT, (
                    f"{fn} @ {width}: {len(lines)} lines"
                )

    def test_rail_shows_current_stage_label(self):
        state = AnimationState(basename="m", budget=5.0)
        state.update_dynamic_state("generate", 0.0, *PATHS)
        rail = _render_phase_rail(state, blink_on=True).plain
        # All five stage labels are present; Execute is the current one.
        for _id, label, _sub in PIPELINE_STAGES:
            assert label in rail

    def test_step_strip_marks_current_and_done(self):
        state = AnimationState(basename="m", budget=5.0)
        for fn in ["auto-deps", "generate", "example", "verify"]:
            state.update_dynamic_state(fn, 0.0, *PATHS)
        strip = _render_step_strip(state, blink_on=True).plain
        assert "deps" in strip and "verify" in strip
        # Done steps get a check, the active probe step gets a probe glyph.
        assert "✓" in strip
        assert "◈" in strip

    def test_execute_frame_shows_artifact_boxes(self):
        state = AnimationState(basename="m", budget=5.0)
        state.update_dynamic_state("generate", 0.0, *PATHS)
        text = "\n".join(_render_lines(state, 80))
        for box in ["Prompt", "Code", "Example", "Tests"]:
            assert box in text

    def test_output_frame_shows_completion(self):
        state = AnimationState(basename="m", budget=5.0)
        state.update_dynamic_state("synced", 0.0, *PATHS)
        text = "\n".join(_render_lines(state, 80))
        assert "Outputs" in text
        assert "complete" in text.lower()

    def test_command_sequence_matches_step_labels(self):
        # Guard against the strip and sequence drifting apart.
        assert COMMAND_SEQUENCE == [
            "auto-deps", "generate", "example", "verify", "test", "fix", "update"
        ]
