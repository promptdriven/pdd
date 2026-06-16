"""Tests for pdd.agentic_multishot.run_multishot_candidates.

Test plan (one+ test per spec requirement / branch):

R1  MultishotCandidateRecord — 12 fields exist with correct names.
R2  MultishotResult — 4 fields exist; winner None when all fail.
R3  Signature / defaults:
    - n_shots defaults to 1 (single-shot backward compat).
    - **kwargs forwarded to run_agentic_task unchanged.
    - config_id frozen/identical across all shot records.
R4  Candidate isolation contract — multishot_run_id is a sha256 hex digest,
    identical across all shot records of one run, sensitive to cwd contents.
R5  Pre-shot budget pre-check — remaining < per_shot_budget stops WITHOUT
    invoking run_agentic_task; record verdict=fail, failure_class=budget_truncated,
    stop_reason=budget_exhausted, zero cost/latency.
R6  Total timeout enforcement — elapsed >= total_timeout_s stops with
    stop_reason=timeout before invoking the task.
R7  Per-shot invocation — run_agentic_task called with timeout=per_shot_timeout_s
    and forwarded kwargs; exception => failure_class/stop_reason=infrastructure_error,
    cost 0.0, loop stops.
R8  Hidden verifier — verifier_fn called with the task result; failed shots get
    failure_class from classify_failure; verifier exception => failure_class
    infrastructure_error (verdict fail).
R9  JSONL persistence — one JSON line appended per shot; absent when jsonl_path is None.
R10 Stop-early logic — stop_on_first_pass True stops after first pass
    (stop_reason=verifier_pass); False runs all n_shots, intermediate passes have
    stop_reason None; last shot without early stop => max_shots_reached.
R11 Winner selection — first passing record by ascending shot_id; None if all fail.
R12 CLI version capture — subprocess pdd --version stdout stored in all records;
    empty string on nonzero exit / exception.
"""

from __future__ import annotations

import json
from pathlib import Path

import pytest

from pdd.agentic_common import AgenticTaskResult
from pdd.agentic_multishot import (
    MultishotCandidateRecord,
    MultishotResult,
    run_multishot_candidates,
)

MODULE = "pdd.agentic_multishot"


def make_result(success: bool, output_text: str = "", cost_usd: float = 0.1) -> AgenticTaskResult:
    return AgenticTaskResult(success, output_text, cost_usd, "anthropic", None)


def always_pass(_result: AgenticTaskResult) -> bool:
    return True


def always_fail(_result: AgenticTaskResult) -> bool:
    return False


def verify_by_success(result: AgenticTaskResult) -> bool:
    """Verifier that mirrors the task's own success flag."""
    return bool(result.success)


@pytest.fixture
def patched(monkeypatch):
    """Patch run_agentic_task and subprocess.run with controllable doubles.

    Returns a helper object exposing ``task`` (MagicMock) and a setter for the
    pdd --version subprocess stdout/returncode.
    """
    import unittest.mock as mock

    task_mock = mock.MagicMock(name="run_agentic_task")
    subproc_mock = mock.MagicMock(name="subprocess_run")
    subproc_mock.return_value.returncode = 0
    subproc_mock.return_value.stdout = "pdd 9.9.9"

    monkeypatch.setattr(f"{MODULE}.run_agentic_task", task_mock)
    monkeypatch.setattr(f"{MODULE}.subprocess.run", subproc_mock)

    class Harness:
        task = task_mock
        subproc = subproc_mock

    return Harness()


def base_kwargs(**overrides):
    kw = dict(
        per_shot_budget=1.0,
        total_budget=10.0,
        per_shot_timeout_s=30.0,
        total_timeout_s=120.0,
        verifier_fn=always_pass,
        config_id="cfg",
        task_id="task",
    )
    kw.update(overrides)
    return kw


# ---------------------------------------------------------------------------
# R1 / R2 — dataclass shapes
# ---------------------------------------------------------------------------
class TestDataclasses:
    def test_candidate_record_fields(self):
        fields = MultishotCandidateRecord.__dataclass_fields__.keys()
        assert set(fields) == {
            "shot_id", "task_id", "multishot_run_id", "cli_version", "config_id",
            "verdict", "failure_class", "cost_usd", "latency_ms", "started_at",
            "finished_at", "stop_reason",
        }

    def test_result_fields(self):
        fields = MultishotResult.__dataclass_fields__.keys()
        assert set(fields) == {"winner", "candidates", "total_cost_usd", "total_latency_ms"}


# ---------------------------------------------------------------------------
# R3 — defaults, kwargs forwarding, config_id immutability
# ---------------------------------------------------------------------------
class TestSignatureAndForwarding:
    def test_n_shots_default_is_single_shot(self, patched):
        patched.task.return_value = make_result(True, "ok", 0.1)
        result = run_multishot_candidates("do", Path("."), **base_kwargs())
        assert len(result.candidates) == 1
        assert patched.task.call_count == 1

    def test_kwargs_forwarded_to_run_agentic_task(self, patched):
        patched.task.return_value = make_result(True, "ok", 0.1)
        run_multishot_candidates(
            "do", Path("/work"),
            **base_kwargs(), verbose=True, quiet=False, label="L",
        )
        args, kwargs = patched.task.call_args
        assert args[0] == "do"
        assert args[1] == Path("/work")
        assert kwargs["timeout"] == 30.0
        assert kwargs["verbose"] is True
        assert kwargs["quiet"] is False
        assert kwargs["label"] == "L"

    def test_per_shot_timeout_passed(self, patched):
        patched.task.return_value = make_result(True, "ok", 0.1)
        run_multishot_candidates("do", Path("."), **base_kwargs(per_shot_timeout_s=7.5))
        _, kwargs = patched.task.call_args
        assert kwargs["timeout"] == 7.5

    def test_config_id_frozen_across_shots(self, patched):
        patched.task.return_value = make_result(False, "boom", 0.1)
        result = run_multishot_candidates(
            "do", Path("."), **base_kwargs(n_shots=3, verifier_fn=always_fail, config_id="frozen")
        )
        assert len(result.candidates) == 3
        assert all(c.config_id == "frozen" for c in result.candidates)


# ---------------------------------------------------------------------------
# R4 — candidate isolation / multishot_run_id
# ---------------------------------------------------------------------------
class TestIsolationContract:
    def test_run_id_is_sha256_and_identical_across_shots(self, patched):
        patched.task.return_value = make_result(False, "boom", 0.1)
        result = run_multishot_candidates(
            "do", Path("."), **base_kwargs(n_shots=2, verifier_fn=always_fail)
        )
        ids = {c.multishot_run_id for c in result.candidates}
        assert len(ids) == 1
        only = ids.pop()
        assert len(only) == 64
        int(only, 16)  # hex digest

    def test_run_id_changes_with_cwd_contents(self, patched, tmp_path):
        patched.task.return_value = make_result(True, "ok", 0.1)
        r1 = run_multishot_candidates("do", tmp_path, **base_kwargs())
        (tmp_path / "newfile.txt").write_text("data")
        r2 = run_multishot_candidates("do", tmp_path, **base_kwargs())
        assert r1.candidates[0].multishot_run_id != r2.candidates[0].multishot_run_id


# ---------------------------------------------------------------------------
# R5 — budget pre-check
# ---------------------------------------------------------------------------
class TestBudgetPrecheck:
    def test_budget_exhausted_before_first_shot(self, patched):
        result = run_multishot_candidates(
            "do", Path("."), **base_kwargs(per_shot_budget=2.0, total_budget=1.0)
        )
        assert patched.task.call_count == 0
        rec = result.candidates[0]
        assert rec.verdict == "fail"
        assert rec.failure_class == "budget_truncated"
        assert rec.stop_reason == "budget_exhausted"
        assert rec.cost_usd == 0.0
        assert rec.latency_ms == 0.0
        assert result.winner is None

    def test_budget_exhausted_after_accumulation(self, patched):
        # First shot costs 0.6, leaving 0.4 < per_shot_budget 0.5 -> stop on shot 2.
        patched.task.return_value = make_result(False, "boom", 0.6)
        result = run_multishot_candidates(
            "do", Path("."),
            **base_kwargs(n_shots=3, per_shot_budget=0.5, total_budget=1.0, verifier_fn=always_fail),
        )
        assert patched.task.call_count == 1
        assert result.candidates[-1].stop_reason == "budget_exhausted"
        assert result.candidates[-1].failure_class == "budget_truncated"


# ---------------------------------------------------------------------------
# R6 — total timeout enforcement
# ---------------------------------------------------------------------------
class TestTotalTimeout:
    def test_timeout_stops_before_invoking_task(self, patched):
        result = run_multishot_candidates(
            "do", Path("."), **base_kwargs(total_timeout_s=-1.0)
        )
        assert patched.task.call_count == 0
        rec = result.candidates[0]
        assert rec.stop_reason == "timeout"
        assert rec.verdict == "fail"
        assert rec.cost_usd == 0.0


# ---------------------------------------------------------------------------
# R7 — per-shot invocation & infrastructure error
# ---------------------------------------------------------------------------
class TestInfrastructureError:
    def test_exception_from_task_sets_infrastructure_error(self, patched):
        patched.task.side_effect = RuntimeError("provider exploded")
        result = run_multishot_candidates(
            "do", Path("."), **base_kwargs(n_shots=3)
        )
        # Stops immediately after the exception.
        assert len(result.candidates) == 1
        rec = result.candidates[0]
        assert rec.verdict == "fail"
        assert rec.failure_class == "infrastructure_error"
        assert rec.stop_reason == "infrastructure_error"
        assert rec.cost_usd == 0.0
        assert result.winner is None


# ---------------------------------------------------------------------------
# R8 — hidden verifier
# ---------------------------------------------------------------------------
class TestVerifier:
    def test_verifier_receives_task_result(self, patched):
        sentinel = make_result(True, "ok", 0.1)
        patched.task.return_value = sentinel
        seen = {}

        def verifier(result):
            seen["result"] = result
            return True

        run_multishot_candidates("do", Path("."), **base_kwargs(verifier_fn=verifier))
        assert seen["result"] is sentinel

    def test_failed_shot_classified_via_classify_failure(self, patched):
        patched.task.return_value = make_result(False, "SyntaxError: bad token", 0.1)
        result = run_multishot_candidates(
            "do", Path("."), **base_kwargs(verifier_fn=always_fail)
        )
        # classify_failure maps SyntaxError -> syntax_import.
        assert result.candidates[0].failure_class == "syntax_import"
        assert result.candidates[0].verdict == "fail"

    def test_verifier_exception_marks_infrastructure_error(self, patched):
        patched.task.return_value = make_result(True, "ok", 0.1)

        def boom(_):
            raise ValueError("verifier crashed")

        result = run_multishot_candidates(
            "do", Path("."), **base_kwargs(verifier_fn=boom)
        )
        rec = result.candidates[0]
        assert rec.verdict == "fail"
        assert rec.failure_class == "infrastructure_error"

    def test_passing_shot_has_no_failure_class(self, patched):
        patched.task.return_value = make_result(True, "ok", 0.1)
        result = run_multishot_candidates("do", Path("."), **base_kwargs())
        assert result.candidates[0].failure_class is None
        assert result.candidates[0].verdict == "pass"


# ---------------------------------------------------------------------------
# R9 — JSONL persistence
# ---------------------------------------------------------------------------
class TestJsonlPersistence:
    def test_none_path_writes_nothing(self, patched, tmp_path):
        patched.task.return_value = make_result(True, "ok", 0.1)
        run_multishot_candidates("do", Path("."), **base_kwargs(jsonl_path=None))
        assert list(tmp_path.iterdir()) == []

    def test_one_line_per_shot(self, patched, tmp_path):
        patched.task.return_value = make_result(False, "boom", 0.1)
        out = tmp_path / "telemetry.jsonl"
        run_multishot_candidates(
            "do", Path("."),
            **base_kwargs(n_shots=3, verifier_fn=always_fail, jsonl_path=out),
        )
        lines = out.read_text(encoding="utf-8").splitlines()
        assert len(lines) == 3
        first = json.loads(lines[0])
        assert first["shot_id"] == 1
        assert first["verdict"] == "fail"
        assert first["task_id"] == "task"

    def test_record_serializes_failure_class_as_string(self, patched, tmp_path):
        patched.task.return_value = make_result(False, "SyntaxError: x", 0.1)
        out = tmp_path / "t.jsonl"
        run_multishot_candidates(
            "do", Path("."), **base_kwargs(verifier_fn=always_fail, jsonl_path=out)
        )
        rec = json.loads(out.read_text(encoding="utf-8").splitlines()[0])
        assert rec["failure_class"] == "syntax_import"


# ---------------------------------------------------------------------------
# R10 — stop-early logic
# ---------------------------------------------------------------------------
class TestStopEarly:
    def test_stop_on_first_pass_true_stops(self, patched):
        results = [make_result(False, "boom", 0.1), make_result(True, "ok", 0.1)]
        patched.task.side_effect = results
        result = run_multishot_candidates(
            "do", Path("."),
            **base_kwargs(n_shots=5, stop_on_first_pass=True, verifier_fn=verify_by_success),
        )
        assert len(result.candidates) == 2
        assert result.candidates[1].stop_reason == "verifier_pass"
        assert patched.task.call_count == 2

    def test_stop_on_first_pass_false_runs_all(self, patched):
        patched.task.return_value = make_result(True, "ok", 0.1)
        result = run_multishot_candidates(
            "do", Path("."), **base_kwargs(n_shots=3, stop_on_first_pass=False)
        )
        assert len(result.candidates) == 3
        # Intermediate passing records carry stop_reason None.
        assert result.candidates[0].stop_reason is None
        assert result.candidates[1].stop_reason is None
        # Final shot completing the loop.
        assert result.candidates[2].stop_reason == "max_shots_reached"

    def test_max_shots_reached_when_all_fail(self, patched):
        patched.task.return_value = make_result(False, "boom", 0.1)
        result = run_multishot_candidates(
            "do", Path("."), **base_kwargs(n_shots=2, verifier_fn=always_fail)
        )
        assert result.candidates[-1].stop_reason == "max_shots_reached"
        assert result.winner is None


# ---------------------------------------------------------------------------
# R11 — winner selection
# ---------------------------------------------------------------------------
class TestWinnerSelection:
    def test_winner_is_first_pass_by_shot_id(self, patched):
        results = [
            make_result(False, "boom", 0.1),
            make_result(True, "ok", 0.1),
            make_result(True, "ok", 0.1),
        ]
        patched.task.side_effect = results
        result = run_multishot_candidates(
            "do", Path("."),
            **base_kwargs(n_shots=3, stop_on_first_pass=False, verifier_fn=verify_by_success),
        )
        assert result.winner is not None
        assert result.winner.shot_id == 2

    def test_winner_none_when_all_fail(self, patched):
        patched.task.return_value = make_result(False, "boom", 0.1)
        result = run_multishot_candidates(
            "do", Path("."), **base_kwargs(n_shots=2, verifier_fn=always_fail)
        )
        assert result.winner is None

    def test_total_cost_accumulates(self, patched):
        patched.task.side_effect = [
            make_result(False, "boom", 0.2),
            make_result(False, "boom", 0.3),
        ]
        result = run_multishot_candidates(
            "do", Path("."), **base_kwargs(n_shots=2, verifier_fn=always_fail)
        )
        assert abs(result.total_cost_usd - 0.5) < 1e-9


# ---------------------------------------------------------------------------
# R12 — CLI version capture
# ---------------------------------------------------------------------------
class TestCliVersion:
    def test_version_stored_in_records(self, patched):
        patched.subproc.return_value.returncode = 0
        patched.subproc.return_value.stdout = "pdd 1.2.3\n"
        patched.task.return_value = make_result(True, "ok", 0.1)
        result = run_multishot_candidates("do", Path("."), **base_kwargs())
        assert result.candidates[0].cli_version == "pdd 1.2.3"

    def test_version_empty_on_nonzero_exit(self, patched):
        patched.subproc.return_value.returncode = 1
        patched.subproc.return_value.stdout = "pdd 1.2.3"
        patched.task.return_value = make_result(True, "ok", 0.1)
        result = run_multishot_candidates("do", Path("."), **base_kwargs())
        assert result.candidates[0].cli_version == ""

    def test_version_empty_on_subprocess_exception(self, patched):
        patched.subproc.side_effect = FileNotFoundError("pdd not found")
        patched.task.return_value = make_result(True, "ok", 0.1)
        result = run_multishot_candidates("do", Path("."), **base_kwargs())
        assert result.candidates[0].cli_version == ""
