"""Runnable example for ``pdd.agentic_multishot.run_multishot_candidates``.

This script demonstrates the sequential multi-shot repeat-run controller without
making any real agent/CLI calls. ``run_agentic_task`` and the ``pdd --version``
subprocess probe are mocked so the example runs standalone and deterministically.

What the controller does
------------------------
``run_multishot_candidates`` repeatedly invokes an agentic task (up to ``n_shots``
times), runs a hidden binary ``verifier_fn`` on each result, and stops early on the
first passing shot (when ``stop_on_first_pass=True``). It enforces a per-shot and a
total cost budget plus a total wall-clock timeout, and can append per-shot telemetry
to a JSONL file.

Key inputs (units)
------------------
- instruction (str): natural-language task for the agent.
- cwd (Path): working directory; its file listing is fingerprinted into multishot_run_id.
- n_shots (int): max number of sequential attempts.
- per_shot_budget / total_budget (float, USD): cost limits.
- per_shot_timeout_s / total_timeout_s (float, seconds): time limits.
- verifier_fn (Callable[[AgenticTaskResult], bool]): pass/fail decision per shot.
- jsonl_path (str | Path | None): when set, each shot record is appended as one JSON line.

Output
------
A ``MultishotResult`` with:
- winner (Optional[MultishotCandidateRecord]): first passing shot, or None.
- candidates (List[MultishotCandidateRecord]): every shot record in order.
- total_cost_usd (float, USD): sum of per-shot costs actually consumed.
- total_latency_ms (float, ms): wall-clock latency of the whole run.
"""

from __future__ import annotations

import os
import sys
import tempfile
from pathlib import Path
from unittest.mock import patch

# Make the local ``pdd`` package importable regardless of working directory.
sys.path.insert(0, os.path.join(os.path.dirname(__file__), ".."))

from pdd.agentic_common import AgenticTaskResult
from pdd.agentic_multishot import (
    MultishotCandidateRecord,
    MultishotResult,
    run_multishot_candidates,
)


def _make_result(success: bool, output_text: str, cost_usd: float) -> AgenticTaskResult:
    """Build a fake AgenticTaskResult (success, output_text, cost_usd, provider, usage)."""
    return AgenticTaskResult(success, output_text, cost_usd, "anthropic", None)


def _passing_verifier(result: AgenticTaskResult) -> bool:
    """Hidden verifier: a shot passes only when the underlying task succeeded."""
    return bool(result.success)


def _print_result(label: str, result: MultishotResult) -> None:
    print(f"=== {label} ===")
    print(f"winner shot_id : {result.winner.shot_id if result.winner else None}")
    print(f"num candidates : {len(result.candidates)}")
    print(f"total_cost_usd : {result.total_cost_usd:.4f}")
    for rec in result.candidates:
        print(
            f"  shot {rec.shot_id}: verdict={rec.verdict} "
            f"failure_class={rec.failure_class} stop_reason={rec.stop_reason} "
            f"cost=${rec.cost_usd:.2f}"
        )
    print()


def demo_single_shot_pass() -> None:
    """n_shots=1 (default): one successful shot becomes the winner."""
    with patch("pdd.agentic_multishot.run_agentic_task") as mock_task, patch(
        "pdd.agentic_multishot.subprocess.run"
    ) as mock_subproc:
        mock_subproc.return_value.returncode = 0
        mock_subproc.return_value.stdout = "pdd 1.2.3"
        mock_task.return_value = _make_result(True, "all tests passed", 0.10)

        result = run_multishot_candidates(
            "Implement feature X",
            Path("."),
            per_shot_budget=1.0,
            total_budget=5.0,
            per_shot_timeout_s=30.0,
            total_timeout_s=120.0,
            verifier_fn=_passing_verifier,
            config_id="cfg-A",
            task_id="task-001",
        )
    _print_result("Single shot, immediate pass", result)
    assert result.winner is not None
    assert result.winner.verdict == "pass"
    assert result.winner.stop_reason == "verifier_pass"
    assert result.winner.cli_version == "pdd 1.2.3"


def demo_stop_on_first_pass() -> None:
    """First shot fails, second passes; controller stops at the second shot."""
    outcomes = [
        _make_result(False, "AssertionError: expected 4 got 5", 0.20),
        _make_result(True, "all tests passed", 0.30),
    ]
    with patch("pdd.agentic_multishot.run_agentic_task", side_effect=outcomes), patch(
        "pdd.agentic_multishot.subprocess.run"
    ) as mock_subproc:
        mock_subproc.return_value.returncode = 0
        mock_subproc.return_value.stdout = "pdd 1.2.3"

        result = run_multishot_candidates(
            "Fix the failing test",
            Path("."),
            n_shots=3,
            per_shot_budget=1.0,
            total_budget=5.0,
            per_shot_timeout_s=30.0,
            total_timeout_s=120.0,
            verifier_fn=_passing_verifier,
            config_id="cfg-A",
            task_id="task-002",
        )
    _print_result("Multi-shot, pass on shot 2", result)
    assert len(result.candidates) == 2
    assert result.candidates[0].verdict == "fail"
    # First (failed) shot was classified from its output text.
    assert result.candidates[0].failure_class == "assertion_logic"
    assert result.winner is not None and result.winner.shot_id == 2
    # Accumulated cost = 0.20 + 0.30.
    assert abs(result.total_cost_usd - 0.50) < 1e-9


def demo_budget_exhausted() -> None:
    """per_shot_budget exceeds remaining total_budget -> stop without invoking the task."""
    with patch("pdd.agentic_multishot.run_agentic_task") as mock_task, patch(
        "pdd.agentic_multishot.subprocess.run"
    ) as mock_subproc:
        mock_subproc.return_value.returncode = 0
        mock_subproc.return_value.stdout = "pdd 1.2.3"

        result = run_multishot_candidates(
            "Expensive task",
            Path("."),
            n_shots=2,
            per_shot_budget=2.0,
            total_budget=1.0,  # less than per_shot_budget -> immediate stop
            per_shot_timeout_s=30.0,
            total_timeout_s=120.0,
            verifier_fn=_passing_verifier,
            config_id="cfg-A",
            task_id="task-003",
        )
        # The task must never be invoked when the budget pre-check trips.
        assert mock_task.call_count == 0
    _print_result("Budget exhausted before shot 1", result)
    assert result.winner is None
    assert result.candidates[0].failure_class == "budget_truncated"
    assert result.candidates[0].stop_reason == "budget_exhausted"


def demo_jsonl_persistence() -> None:
    """When jsonl_path is set, each shot record is appended as one JSON line."""
    with tempfile.TemporaryDirectory() as tmp:
        jsonl_path = os.path.join(tmp, "telemetry.jsonl")
        with patch(
            "pdd.agentic_multishot.run_agentic_task"
        ) as mock_task, patch("pdd.agentic_multishot.subprocess.run") as mock_subproc:
            mock_subproc.return_value.returncode = 0
            mock_subproc.return_value.stdout = "pdd 1.2.3"
            mock_task.return_value = _make_result(True, "all tests passed", 0.10)

            run_multishot_candidates(
                "Persisted task",
                Path("."),
                per_shot_budget=1.0,
                total_budget=5.0,
                per_shot_timeout_s=30.0,
                total_timeout_s=120.0,
                verifier_fn=_passing_verifier,
                config_id="cfg-A",
                task_id="task-004",
                jsonl_path=jsonl_path,
            )
        lines = Path(jsonl_path).read_text(encoding="utf-8").splitlines()
        print("=== JSONL persistence ===")
        print(f"records written: {len(lines)}")
        print(f"first line     : {lines[0]}")
        print()
        assert len(lines) == 1


def main() -> None:
    print("run_multishot_candidates — sequential multi-shot controller demo")
    print()
    demo_single_shot_pass()
    demo_stop_on_first_pass()
    demo_budget_exhausted()
    demo_jsonl_persistence()
    print("All demos completed successfully.")


if __name__ == "__main__":
    main()
