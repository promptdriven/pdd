"""Smoke tests for benchmarks/formalization (issue #1273)."""
from __future__ import annotations

import json
import subprocess
import sys
from pathlib import Path

import jsonschema
import pytest

BENCH_ROOT = Path(__file__).resolve().parents[1] / "benchmarks" / "formalization"
RUNNER = BENCH_ROOT / "run_benchmark.py"
RESULTS_SCHEMA = BENCH_ROOT / "schemas" / "results.schema.json"


@pytest.fixture(name="results_schema")
def fixture_results_schema() -> dict:
    return json.loads(RESULTS_SCHEMA.read_text(encoding="utf-8"))


def test_discover_tasks() -> None:
    sys.path.insert(0, str(BENCH_ROOT))
    from _runner import discover_tasks  # pylint: disable=import-outside-toplevel

    tasks = discover_tasks(BENCH_ROOT / "tasks")
    ids = {task.task_id for task in tasks}
    assert "email_validator" in ids
    assert "refund_payment" in ids
    assert "payment_api_lint" in ids


def test_run_benchmark_smoke(tmp_path: Path, results_schema: dict) -> None:
    out = tmp_path / "results"
    completed = subprocess.run(
        [
            sys.executable,
            str(RUNNER),
            "--tasks",
            "email_validator",
            "--report",
            "--results-dir",
            str(out),
        ],
        cwd=BENCH_ROOT.parent.parent,
        capture_output=True,
        text=True,
        check=False,
    )
    assert completed.returncode == 0, completed.stdout + completed.stderr

    aggregate_path = out / "aggregate.json"
    assert aggregate_path.is_file()
    aggregate = json.loads(aggregate_path.read_text(encoding="utf-8"))
    assert len(aggregate["runs"]) == 3
    assert (out / "summary.json").is_file()
    assert (out / "REPORT.md").is_file()

    for arm in ("A0", "A1", "A2"):
        run_path = out / "email_validator" / f"{arm}.json"
        assert run_path.is_file()
        payload = json.loads(run_path.read_text(encoding="utf-8"))
        jsonschema.validate(instance=payload, schema=results_schema)
        assert payload["task_id"] == "email_validator"
        assert payload["arm"] == arm


def test_a1_has_more_structure_than_a0(tmp_path: Path) -> None:
    """Formalized arm should expose contract rules the ad-hoc arm lacks."""
    sys.path.insert(0, str(BENCH_ROOT))
    from _runner import discover_tasks, run_arm  # pylint: disable=import-outside-toplevel

    task = discover_tasks(BENCH_ROOT / "tasks", task_ids=["email_validator"])[0]
    a0 = run_arm(task, "A0")
    a1 = run_arm(task, "A1")

    assert (a0["metrics"]["total_rules"] or 0) == 0
    assert (a1["metrics"]["total_rules"] or 0) >= 6
    assert (a1["metrics"]["formal_candidate_rules"] or 0) >= 4
    assert (a1["metrics"]["z3_test_count"] or 0) >= 3
    assert a1["metrics"]["test_pass_rate"] == 1.0
    assert (a1["metrics"]["test_total"] or 0) >= 6


def test_email_validator_z3_tests_run() -> None:
    """Z3 tests are collected and pass when z3-solver is installed."""
    test_file = (
        BENCH_ROOT
        / "tasks/email_validator/baseline/tests/test_email_validator_z3.py"
    )
    completed = subprocess.run(
        [
            sys.executable,
            "-m",
            "pytest",
            "-q",
            str(test_file),
        ],
        cwd=BENCH_ROOT.parent.parent,
        env={
            **dict(__import__("os").environ),
            "PYTHONPATH": str(
                BENCH_ROOT / "tasks/email_validator/baseline/src"
            ),
        },
        capture_output=True,
        text=True,
        check=False,
    )
    if "z3-solver not installed" in (completed.stdout + completed.stderr):
        pytest.skip("z3-solver not installed")
    assert completed.returncode == 0, completed.stdout + completed.stderr


def test_payment_api_lint_a1_fewer_warnings_than_a0() -> None:
    sys.path.insert(0, str(BENCH_ROOT))
    from _runner import discover_tasks, run_arm  # pylint: disable=import-outside-toplevel

    task = discover_tasks(BENCH_ROOT / "tasks", task_ids=["payment_api_lint"])[0]
    a0 = run_arm(task, "A0")
    a1 = run_arm(task, "A1")
    assert (a0["metrics"]["prompt_lint_warnings"] or 0) > (
        a1["metrics"]["prompt_lint_warnings"] or 0
    )


def test_build_summary_report(tmp_path: Path) -> None:
    sys.path.insert(0, str(BENCH_ROOT))
    from _report import build_summary  # pylint: disable=import-outside-toplevel

    aggregate = {
        "benchmark_version": "0.2.0",
        "collected_at": "2026-01-01T00:00:00+00:00",
        "task_ids": ["email_validator"],
        "runs": [
            {
                "task_id": "email_validator",
                "arm": "A0",
                "metrics": {"total_rules": 0, "prompt_lint_warnings": 0},
            },
            {
                "task_id": "email_validator",
                "arm": "A1",
                "metrics": {
                    "total_rules": 6,
                    "checked_rules": 0,
                    "test_only_rules": 6,
                    "prompt_lint_warnings": 0,
                    "formal_candidate_rules": 4,
                    "test_pass_rate": 1.0,
                },
            },
        ],
    }
    summary = build_summary(aggregate)
    assert summary["comparisons"][0]["primary_delta_A0_to_A1"]["total_rules"] == 6
    assert "headline" in summary


def test_refund_epic833_evidence_passes() -> None:
    sys.path.insert(0, str(BENCH_ROOT))
    from _runner import discover_tasks, run_arm  # pylint: disable=import-outside-toplevel

    task = discover_tasks(BENCH_ROOT / "tasks", task_ids=["refund_payment"])[0]
    a1 = run_arm(task, "A1")
    epic = a1.get("epic833") or {}
    assert epic.get("checks_failed", 1) == 0
    names = {c["name"] for c in epic.get("checks", []) if c.get("status") == "pass"}
    assert "evidence_manifest" in names
    assert a1["metrics"]["evidence_manifest_present"] is True


def test_refund_payment_a1_coverage(tmp_path: Path) -> None:
    sys.path.insert(0, str(BENCH_ROOT))
    from _runner import discover_tasks, run_arm  # pylint: disable=import-outside-toplevel

    task = discover_tasks(BENCH_ROOT / "tasks", task_ids=["refund_payment"])[0]
    a1 = run_arm(task, "A1")
    assert a1["command_success"] is True
    assert a1["metrics"]["total_rules"] == 6
    assert (a1["metrics"]["checked_rules"] or 0) >= 1
