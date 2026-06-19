"""End-to-end test for the sync-animation step strip (issue #1560).

This drives the *real* CLI data path rather than calling the renderer in
isolation. In production the chain is:

    sync_orchestration  →  mutable refs (function_name_ref, cost_ref, …)
                        →  SyncApp.update_animation reads the refs each tick
                        →  AnimationState.update_dynamic_state(…)
                        →  _render_animation_frame(state, width)
                        →  _render_step_strip(…)

`_drive_lifecycle` reproduces that loop exactly (see SyncApp.update_animation in
sync_tui.py: read refs → set_box_colors → update_dynamic_state → render at the
app width), walks a realistic sync lifecycle, and captures the actual rendered
frames. We assert the execute sub-commands are spelt out in full and that the
strip adapts to width without ever breaking the fixed-height frame:

* wide terminal  → full names, roomy separators;
* 80-col floor   → resized (tighter separators) — the tier the Textual app hits
  at its _min_ui_width floor;
* narrow         → rotating marquee, never overflowing one line.
"""

from rich.console import Console

from pdd.sync_animation import (
    AnimationState,
    ANIMATION_BOX_HEIGHT,
    COMMAND_SEQUENCE,
    STAGE_EXECUTE,
    _render_animation_frame,
    stage_for_function,
    DEFAULT_PROMPT_COLOR,
    DEFAULT_CODE_COLOR,
    DEFAULT_EXAMPLE_COLOR,
    DEFAULT_TESTS_COLOR,
)

# The function-name sequence the orchestrator emits over a realistic run:
# entry → state inspection → planning → the full command-execution loop
# (including a crash/fix detour) → terminal "synced".
LIFECYCLE = [
    "initializing", "checking",
    "auto-deps", "generate", "example", "verify", "crash", "fix",
    "test", "fix", "update",
    "synced",
]

PATHS = (
    "prompts/calculator_python.prompt",
    "src/calculator.py",
    "examples/calculator_example.py",
    "tests/test_calculator.py",
)


def _render_frame_lines(state: AnimationState, width: int):
    console = Console(width=width)
    with console.capture() as cap:
        console.print(_render_animation_frame(state, width), end="")
    return [ln for ln in cap.get().split("\n") if ln != ""]


def _drive_lifecycle(width: int):
    """Run the orchestrator→SyncApp render loop for one terminal width.

    Returns (state, frames) where frames is a list of (function_name, lines).
    """
    # The mutable refs are exactly what sync_orchestration constructs and the
    # worker thread mutates; the UI thread only ever reads index [0].
    function_name_ref = ["initializing"]
    cost_ref = [0.0]
    prompt_path_ref, code_path_ref = [PATHS[0]], [PATHS[1]]
    example_path_ref, tests_path_ref = [PATHS[2]], [PATHS[3]]
    color_refs = (
        [DEFAULT_PROMPT_COLOR], [DEFAULT_CODE_COLOR],
        [DEFAULT_EXAMPLE_COLOR], [DEFAULT_TESTS_COLOR],
    )

    state = AnimationState(basename="calculator", budget=5.00)
    frames = []
    cost = 0.0
    for fn in LIFECYCLE:
        function_name_ref[0] = fn
        cost += 0.12
        cost_ref[0] = cost
        # Several ticks per stage, as the 0.05s app timer would fire.
        for _ in range(6):
            # --- mirror SyncApp.update_animation ---
            state.set_box_colors(*(ref[0] for ref in color_refs))
            state.update_dynamic_state(
                function_name_ref[0], cost_ref[0],
                prompt_path_ref[0], code_path_ref[0],
                example_path_ref[0], tests_path_ref[0],
            )
            lines = _render_frame_lines(state, width)
            frames.append((fn, lines))
    return state, frames


class TestSyncAnimationEndToEnd:
    def test_every_frame_keeps_fixed_height_across_widths(self):
        # The frame must stay ANIMATION_BOX_HEIGHT lines tall the whole run, at
        # every width — proving the (possibly resized/rotating) strip never
        # wraps to a second line.
        for width in (120, 80, 50):
            _state, frames = _drive_lifecycle(width)
            for fn, lines in frames:
                assert len(lines) == ANIMATION_BOX_HEIGHT, (
                    f"width={width} fn={fn}: {len(lines)} lines"
                )

    def test_execute_subcommands_spelt_out_in_full(self):
        # Over the run, every execute sub-command appears spelt out in full in
        # the rendered frame (not abbreviated to deps/gen/ex/upd).
        _state, frames = _drive_lifecycle(120)
        execute_text = "\n".join(
            "\n".join(lines) for fn, lines in frames
            if stage_for_function(fn) == STAGE_EXECUTE
        )
        for full in COMMAND_SEQUENCE:  # auto-deps, generate, example, verify, …
            assert full in execute_text, full
        # The old short forms are gone as standalone strip labels.
        assert "▸ gen " not in execute_text
        assert " upd " not in execute_text

    def test_floor_width_resizes_rather_than_rotating(self):
        # At the Textual app's 80-col floor the strip tightens its separators
        # but keeps full names, and never needs to rotate.
        state, frames = _drive_lifecycle(80)
        execute_text = "\n".join(
            "\n".join(lines) for fn, lines in frames
            if stage_for_function(fn) == STAGE_EXECUTE
        )
        assert "auto-deps" in execute_text and "update" in execute_text
        # Resize uses the compact separator, so the roomy one never appears in
        # the strip, and the marquee is never engaged at this width.
        assert state.step_scroll_offset == 0

    def test_narrow_width_engages_rotating_marquee(self):
        # Below the floor (e.g. a forced-narrow demo run) the strip rotates: the
        # marquee offset advances while still rendering full command names.
        state, frames = _drive_lifecycle(50)
        execute_text = "\n".join(
            "\n".join(lines) for fn, lines in frames
            if stage_for_function(fn) == STAGE_EXECUTE
        )
        assert "auto-deps" in execute_text  # full names still scroll past
        assert state.step_scroll_offset > 0  # the marquee actually rotated

    def test_full_run_never_crashes(self):
        # The whole lifecycle renders cleanly end to end at every width.
        for width in (120, 100, 80, 64, 50, 40):
            state, frames = _drive_lifecycle(width)
            assert frames  # produced output
            assert stage_for_function(frames[-1][0]) != STAGE_EXECUTE  # ended at Output
