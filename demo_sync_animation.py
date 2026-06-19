#!/usr/bin/env python3
"""Demo harness for the redesigned `pdd sync` animation (issue #1560, w6).

Modes:

    python demo_sync_animation.py                # live: play the animation in-terminal
    python demo_sync_animation.py --width 50     # ...forced to a narrow width
    python demo_sync_animation.py --storyboard   # print one frame per lifecycle stage
    python demo_sync_animation.py --strip        # compare the step strip across widths

The live mode drives AnimationState through a realistic sync lifecycle
(initialize -> inspect -> plan -> auto-deps -> generate -> example -> verify ->
crash -> test -> fix -> update -> synced), advancing several frames per stage so
arrows, blinks and probe pulses are visible. No LLM calls, no cost — it only
feeds the renderer canned state, exactly the way the orchestrator would.

The `--strip` mode is the quickest way to verify the execute sub-commands are
spelt out in full and that the strip resizes (tighter separators) and finally
rotates (marquee) as the terminal narrows — it prints the strip at a ladder of
widths, and animates the marquee at a narrow width so the rotation is visible.
"""
from __future__ import annotations

import sys
import time

from rich.console import Console

from pdd import sync_animation as sa

PATHS = (
    "prompts/calculator_python.prompt",
    "src/calculator.py",
    "examples/calculator_example.py",
    "tests/test_calculator.py",
)

# (function_name, frames_to_dwell, cost_at_stage)
LIFECYCLE = [
    ("initializing", 12, 0.00),
    ("checking",     10, 0.00),
    ("auto-deps",    20, 0.04),
    ("generate",     24, 0.31),
    ("example",      20, 0.46),
    ("verify",       24, 0.58),
    ("crash",        16, 0.58),
    ("fix",          20, 0.79),
    ("test",         20, 1.02),
    ("fix",          18, 1.21),
    ("update",       18, 1.40),
    ("synced",       14, 1.40),
]


def _new_state() -> sa.AnimationState:
    state = sa.AnimationState(basename="calculator", budget=5.00)
    state.set_box_colors(sa.LUMEN_PURPLE, sa.ELECTRIC_CYAN, sa.BUILD_GREEN, sa.PROMPT_MAGENTA)
    return state


def run_live(width: int | None = None) -> None:
    from rich.live import Live

    console = Console()
    forced = width is not None
    state = _new_state()
    with Live(console=console, refresh_per_second=12, screen=False) as live:
        for fn, dwell, cost in LIFECYCLE:
            for _ in range(dwell):
                state.update_dynamic_state(fn, cost, *PATHS)
                # Re-read the terminal width each frame (unless --width forces
                # one), mirroring the real orchestrator — resize the window
                # mid-run and the step strip resizes/rotates live.
                frame_width = width if forced else min(96, console.width or 80)
                live.update(sa._render_animation_frame(state, frame_width))
                time.sleep(1 / 12)
    console.print("[bold #18C07A]✓ demo complete[/]  (this was canned state — no sync ran)")


def run_storyboard() -> None:
    console = Console(width=82)
    # Use one state so the step strip accumulates "done" marks like a real run.
    state = _new_state()
    # Pick a mid-animation frame so arrows are visible, not at rest.
    for fn, _dwell, cost in LIFECYCLE:
        for f in range(6):  # advance a few frames so the arrow leaves the box
            state.update_dynamic_state(fn, cost, *PATHS)
            state.frame_count = f + 3
        with console.capture() as cap:
            console.print(sa._render_animation_frame(state, 82), end="")
        title = f" stage: {sa.stage_for_function(fn):8}  function_name = {fn!r} "
        console.rule(title)
        print("\n".join(l.rstrip() for l in cap.get().split("\n") if l != ""))
        print()


def _strip_tier(state: sa.AnimationState, content_width: int) -> str:
    """Name which adaptive tier the strip lands in at a given width."""
    for i, sep in enumerate(sa._STRIP_SEPARATORS):
        if len(sa._step_strip_cells(state, True, sep)) <= content_width:
            return "full" if i == 0 else "resized"
    return "rotating"


def run_strip() -> None:
    """Show the command step strip across a ladder of terminal widths.

    Builds a mid-run state (a few steps done, a probe step active) so the strip
    carries checks and a probe glyph, then renders it at each width and labels
    which tier engaged: full names, resized (tighter separators), or rotating.
    """
    console = Console()
    state = _new_state()
    for fn in ["auto-deps", "generate", "example", "verify"]:
        state.update_dynamic_state(fn, 0.58, *PATHS)

    # Ladder of simulated widths, capped to the real terminal so no row wraps;
    # always includes the current terminal width plus narrower steps so the
    # full -> resized -> rotating progression is visible.
    term = console.width or 80
    widths = []
    for w in (term, 100, 80, 64, 50, 40, 30, 24):
        if 24 <= w <= term and w not in widths:
            widths.append(w)

    console.rule("[bold]step strip vs. terminal width[/]")
    for width in widths:
        content_width = max(10, width - 4)
        strip = sa._render_step_strip(state, True, content_width)
        tier = _strip_tier(state, content_width)
        # Render the strip inside a console clamped to its own width so it reads
        # the same regardless of the real terminal; print it on its own line so
        # the label never pushes it past the edge.
        sub = Console(width=content_width)
        with sub.capture() as cap:
            sub.print(strip, end="")
        line = cap.get().split("\n")[0]
        console.print(f"[dim]── simulated width {width:>3}  ({tier})[/]")
        console.print("  " + line)

    # Animate the marquee at a narrow width so the rotation is visible.
    console.rule("[bold]marquee rotation @ width 34 (12 frames)[/]")
    marquee_state = _new_state()
    for fn in ["auto-deps", "generate"]:
        marquee_state.update_dynamic_state(fn, 0.31, *PATHS)
    for _ in range(12):
        console.print("  ", sa._render_step_strip(marquee_state, True, 30))
        time.sleep(0.18)
    console.print("\n[bold #18C07A]✓ strip demo complete[/]  (canned state — no sync ran)")


if __name__ == "__main__":
    if "--storyboard" in sys.argv:
        run_storyboard()
    elif "--strip" in sys.argv:
        run_strip()
    else:
        width = None
        if "--width" in sys.argv:
            width = int(sys.argv[sys.argv.index("--width") + 1])
        run_live(width)
