"""Contract test: the phase the CLI shows is the operation it actually runs.

The sync animation never runs an independent script — it displays
``current_function_name_ref[0]``, which the orchestrator sets to the planner's
chosen ``operation`` one line before it dispatches that same ``operation`` (see
sync_orchestration.py: ``current_function_name_ref[0] = operation`` →
``print("PDD_PHASE: ...")`` → ``if operation == ...``). The ``PDD_PHASE:``
marker printed at that point is therefore a faithful, machine-readable proxy for
what the strip shows.

This test locks the "what's shown == what ran" contract so a future refactor
can't silently desync the displayed phase from the dispatched command: it
scripts the planner, makes each executor *record that it ran*, then asserts the
emitted ``PDD_PHASE`` markers match the operations that actually executed, in
order — with the terminal ``synced`` marker closing the run.

No LLM calls: the planner and every operation executor are mocked.
"""

import os
import re
from pathlib import Path
from unittest.mock import patch

import pytest

from pdd.sync_orchestration import sync_orchestration
from pdd.sync_determine_operation import SyncDecision

BASENAME = "contract_math"
# Scripted run: a few build steps then a terminal "all_synced". Each non-terminal
# entry is an operation the loop must both *show* (PDD_PHASE) and *dispatch*.
SCRIPT = ["auto-deps", "generate", "example", "test", "all_synced"]
EXECUTED_OPS = ["auto-deps", "generate", "example", "test"]  # SCRIPT minus terminal


def _phase_markers(captured_stdout: str):
    """Ordered list of operations announced via 'PDD_PHASE:' markers."""
    return [
        m.group(1).strip()
        for line in captured_stdout.splitlines()
        if (m := re.match(r"\s*PDD_PHASE:\s*(.+)$", line))
    ]


@pytest.fixture
def workspace(tmp_path, monkeypatch):
    for sub in ("prompts", "pdd", "examples", "tests", "context"):
        (tmp_path / sub).mkdir()
    (tmp_path / ".pdd" / "meta").mkdir(parents=True)
    (tmp_path / "prompts" / f"{BASENAME}_python.prompt").write_text(
        "Create a Python module with an `add(a, b)` function that returns a + b.\n"
        f"Import it as `from {BASENAME} import add`.\n"
    )
    monkeypatch.chdir(tmp_path)
    # PDD_FORCE is set by headless mode anyway; set it up front for determinism.
    monkeypatch.setenv("PDD_FORCE", "1")
    return tmp_path


def test_phase_markers_match_dispatched_operations(workspace, capsys):
    executed = []  # operations whose executor actually ran

    def planner(*_args, **_kwargs):
        op = SCRIPT[min(len(executed_decisions), len(SCRIPT) - 1)]
        executed_decisions.append(op)
        return SyncDecision(operation=op, reason=f"scripted:{op}",
                             confidence=0.9, estimated_cost=0.01)

    executed_decisions = []

    def make_code(*_a, **_k):
        executed.append("generate")
        (workspace / "pdd" / f"{BASENAME}.py").write_text(
            "def add(a, b):\n    return a + b\n"
        )
        return ("code", 0.05, "mock-model")

    def make_example(*_a, **_k):
        executed.append("example")
        (workspace / "examples" / f"{BASENAME}_example.py").write_text(
            f"from {BASENAME} import add\nprint(add(2, 3))\n"
        )
        return ("example", 0.03, "mock-model")

    def make_test(ctx, prompt_file, code_file, output, language, *_a, **_k):
        executed.append("test")
        out = Path(output)
        out.parent.mkdir(parents=True, exist_ok=True)
        out.write_text(
            f"from {BASENAME} import add\n\n"
            "def test_add():\n    assert add(2, 3) == 5\n"
        )
        return ("test", 0.04, "mock-model")

    def make_deps(*_a, **_k):
        executed.append("auto-deps")
        return {"success": True, "cost": 0.01, "model": "mock-model"}

    with patch.dict(
        sync_orchestration.__globals__,
        {
            "sync_determine_operation": planner,
            "auto_deps_main": make_deps,
            "code_generator_main": make_code,
            "context_generator_main": make_example,
            "cmd_test_main": make_test,
            "fix_verification_main": lambda *_a, **_k: {
                "success": True,
                "cost": 0.0,
                "model": "mock-model",
            },
            "crash_main": lambda *_a, **_k: {
                "success": True,
                "cost": 0.0,
                "model": "mock-model",
            },
            "fix_main": lambda *_a, **_k: {
                "success": True,
                "cost": 0.0,
                "model": "mock-model",
            },
        },
    ):
        result = sync_orchestration(
            basename=BASENAME, language="python",
            budget=10.0, max_attempts=5, quiet=True,  # quiet => headless, no TUI
        )

    markers = _phase_markers(capsys.readouterr().out)
    non_terminal = [m for m in markers if m not in ("synced", "conflict")
                    and not m.startswith("skip:")]

    # 1. Every announced (non-terminal) phase is an operation that actually ran,
    #    in the same order — the strip cannot show a step the loop did not run.
    assert non_terminal == executed, (
        f"shown={non_terminal!r} ran={executed!r}"
    )
    # 2. ...and that order is exactly the planner's scripted decisions.
    assert non_terminal == EXECUTED_OPS
    # 3. The run is announced complete via the terminal marker.
    assert markers[-1] == "synced"
    assert result["success"] is True


def test_no_phase_marker_without_a_dispatch(workspace, capsys):
    """A marker is only emitted alongside a real dispatch (or terminal state).

    Guards the inverse of the main contract: the loop must not announce a phase
    it never executes. Here the planner goes straight to a terminal state, so
    the only marker is the terminal one and no executor runs.
    """
    def planner(*_args, **_kwargs):
        return SyncDecision(operation="nothing", reason="already in sync",
                            confidence=0.99, estimated_cost=0.0)

    ran = []
    with patch.dict(
        sync_orchestration.__globals__,
        {
            "sync_determine_operation": planner,
            "code_generator_main": lambda *_a, **_k: ran.append("generate"),
            "cmd_test_main": lambda *_a, **_k: ran.append("test"),
        },
    ):
        sync_orchestration(basename=BASENAME, language="python",
                           budget=10.0, max_attempts=5, quiet=True)

    markers = _phase_markers(capsys.readouterr().out)
    non_terminal = [m for m in markers if m not in ("synced", "conflict")
                    and not m.startswith("skip:")]
    assert ran == []            # nothing executed
    assert non_terminal == []   # so nothing non-terminal was announced
    assert markers and markers[-1] == "synced"
