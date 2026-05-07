"""Example usage of pdd.progress_events.

Demonstrates how long-running PDD commands and the sync watchdog use the
opt-in JSON Lines progress-event channel:

  * `is_enabled()` — gate on `PDD_PROGRESS_EVENTS_PATH` env var.
  * `get_sink_path()` — resolved Path to the JSONL sink (or None).
  * `new_run_id()` — opaque short id reused for every event in one run.
  * `emit(...)` — append one bounded, redacted event line. Never raises.
  * `is_real_progress_kind(kind)` — classify event kinds: True for
    real-progress kinds (the watchdog resets its stall timer), False for
    liveness-only kinds (heartbeat, repeat_message).

Disabled mode (env var unset/empty) is a strict no-op: no file is created,
no warning is printed, and CLI behavior is byte-identical to a build
without progress events.
"""
from __future__ import annotations

import os
import sys
import time
from pathlib import Path

# Add the project root to sys.path
project_root = Path(__file__).resolve().parent.parent
sys.path.append(str(project_root))

from pdd.progress_events import (
    emit,
    get_sink_path,
    is_enabled,
    is_real_progress_kind,
    new_run_id,
)


def example_run_with_progress_events() -> None:
    """Show the canonical emit pattern for a long-running command."""
    # Quick-exit no-op when the sink env var is not set.
    if not is_enabled():
        return

    sink: Path | None = get_sink_path()
    print(f"Progress events sink: {sink}")

    # One run id per CLI invocation; reuse for every event so a downstream
    # consumer (sync watchdog, PDD Cloud) can correlate them.
    run_id = new_run_id()

    # Real-progress event: meaningful work happened. Watchdog resets stall.
    emit(
        "run_started",
        run_id=run_id,
        phase="generate",
        activity="generate code for crm_models",
        markers={"basenames": ["crm_models"], "max_workers": 4},
    )

    # Per-step real-progress event.
    emit(
        "phase_started",
        run_id=run_id,
        phase="generate",
        step="example_generate",
    )

    # Liveness-only event: no semantic progress; watchdog does NOT reset.
    emit(
        "heartbeat",
        run_id=run_id,
        phase="generate",
        markers={"elapsed_s": 60},
    )

    # Real-progress event: cost increased.
    emit(
        "cost_progress",
        run_id=run_id,
        phase="generate",
        markers={"cost_delta": 0.0123, "stream": "stdout"},
    )

    # Terminal event with bounded summary on completion.
    emit(
        "module_completed",
        run_id=run_id,
        phase="generate",
        summary={
            "status": "success",
            "duration_s": 42.5,
            "cost": 0.05,
            "completed_phases": ["example", "verify", "test"],
        },
    )


def example_classify_event_kinds() -> None:
    """Show how the watchdog distinguishes real progress from liveness noise."""
    real_kinds = (
        "run_started",
        "phase_started",
        "phase_completed",
        "step_completed",
        "output_progress",
        "cost_progress",
        "file_progress",
        "module_started",
        "module_completed",
        "run_completed",
    )
    for kind in real_kinds:
        assert is_real_progress_kind(kind) is True, kind

    liveness_kinds = ("heartbeat", "repeat_message", "liveness")
    for kind in liveness_kinds:
        assert is_real_progress_kind(kind) is False, kind

    # Unknown kinds default to liveness-only so unrecognized events never
    # accidentally reset the watchdog stall timer.
    assert is_real_progress_kind("totally_unknown_kind") is False


def example_watchdog_stall_loop() -> None:
    """Sketch of how a soft progress-aware watchdog uses these helpers."""
    if not is_enabled():
        return

    stall_seconds = int(os.environ.get("PDD_PROGRESS_STALL_SECONDS", "600"))
    last_real_progress_at = time.monotonic()

    def on_event(kind: str) -> None:
        nonlocal last_real_progress_at
        if is_real_progress_kind(kind):
            last_real_progress_at = time.monotonic()
        # else: liveness-only, do not touch the stall timer.

    # The runner would call on_event(kind) for every emitted event and
    # check `time.monotonic() - last_real_progress_at > stall_seconds` to
    # decide whether to terminate the child process group with a clear
    # stall reason while the hard `PDD_MODULE_TIMEOUT_SECONDS` backstop
    # still fires independently.
    _ = (stall_seconds, on_event)


if __name__ == "__main__":
    example_run_with_progress_events()
    example_classify_event_kinds()
