"""Issue #1979: single-module `pdd sync <basename>` must exit non-zero when the
aggregated result reports `overall_success == False`.

Before this fix, the sync command printed `Overall status: Failed` in the final
summary panel but returned the `(str(result), total_cost, model_name)` cost-tracking
tuple unconditionally, so CI, shell `&&` chains, and the agentic child runners
(which key off the exit code) read a failed sync as success.

Convention: the #1677 AmbiguousModuleError handler and the agentic/global dispatch
helpers in the same command raise `click.exceptions.Exit(1)` on failure.
"""

import csv
import sys

import pytest
from click.testing import CliRunner

import pdd.cli  # noqa: F401 - registers commands (incl. sync) on the core CLI
from pdd.core.cli import cli as real_cli


def _fake_sync_main(*, overall_success: bool):
    """Build a sync_main stand-in returning an aggregated result dict shaped like
    the real `pdd/sync_main.py` return value (see sync_main.py ~line 1391)."""

    def fake(ctx, basename, **kwargs):  # noqa: ARG001 - mirrors sync_main call shape
        aggregated = {
            "overall_success": overall_success,
            "results_by_language": {
                "python": {
                    "success": overall_success,
                    "error": None if overall_success else "generate step failed",
                    "total_cost": 0.0123,
                    "model_name": "test-model",
                }
            },
            "total_cost": 0.0123,
            "primary_model": "test-model",
        }
        return aggregated, 0.0123, "test-model"

    return fake


@pytest.mark.parametrize("extra", [[], ["--quiet"]], ids=["default", "quiet"])
def test_cli_sync_failed_overall_status_exits_nonzero(tmp_path, monkeypatch, extra):
    """A single-module sync whose aggregated result has overall_success == False
    must exit non-zero (issue #1979), including under --quiet."""
    monkeypatch.chdir(tmp_path)
    monkeypatch.setattr(
        "pdd.commands.maintenance.sync_main", _fake_sync_main(overall_success=False)
    )

    result = CliRunner().invoke(
        real_cli, ["--no-core-dump", *extra, "sync", "my_module"]
    )
    assert result.exit_code != 0, (
        f"failed sync must exit non-zero (args={extra}); output:\n{result.output}"
    )


def test_cli_sync_successful_result_exits_zero(tmp_path, monkeypatch):
    """A successful single-module sync must keep exiting 0."""
    monkeypatch.chdir(tmp_path)
    monkeypatch.setattr(
        "pdd.commands.maintenance.sync_main", _fake_sync_main(overall_success=True)
    )

    result = CliRunner().invoke(real_cli, ["--no-core-dump", "sync", "my_module"])
    assert result.exit_code == 0, result.output


def test_cli_sync_dry_run_success_exits_zero(tmp_path, monkeypatch):
    """A successful --dry-run reporting-only run must keep exiting 0."""
    monkeypatch.chdir(tmp_path)
    monkeypatch.setattr(
        "pdd.commands.maintenance.sync_main", _fake_sync_main(overall_success=True)
    )

    result = CliRunner().invoke(
        real_cli, ["--no-core-dump", "sync", "my_module", "--dry-run"]
    )
    assert result.exit_code == 0, result.output


def test_cli_sync_dry_run_failure_exits_nonzero(tmp_path, monkeypatch):
    """A --dry-run whose aggregated result reports failure must also exit non-zero."""
    monkeypatch.chdir(tmp_path)
    monkeypatch.setattr(
        "pdd.commands.maintenance.sync_main", _fake_sync_main(overall_success=False)
    )

    result = CliRunner().invoke(
        real_cli, ["--no-core-dump", "sync", "my_module", "--dry-run"]
    )
    assert result.exit_code != 0, result.output


def test_cli_sync_failure_still_writes_evidence_manifest(tmp_path, monkeypatch):
    """The failure exit must be raised AFTER the evidence manifest write so
    `--evidence` runs still record failure evidence (cost/manifest path)."""
    monkeypatch.chdir(tmp_path)
    monkeypatch.setattr(
        "pdd.commands.maintenance.sync_main", _fake_sync_main(overall_success=False)
    )
    calls = []
    monkeypatch.setattr(
        "pdd.commands.maintenance._write_sync_evidence_manifest",
        lambda **kwargs: calls.append(kwargs),
    )

    result = CliRunner().invoke(
        real_cli, ["--no-core-dump", "sync", "my_module", "--evidence"]
    )
    assert result.exit_code != 0, result.output
    assert len(calls) == 1, "evidence manifest must still be written on failure"
    assert calls[0]["result"]["overall_success"] is False


def _enable_cost_csv(tmp_path, monkeypatch):
    """Route the track_cost CSV row to a temp file and neutralise the runtime
    behaviors that key off PYTEST_CURRENT_TEST (track_cost skips row-writing
    under pytest; the duplicate-run guard, auto-update, and onboarding shell
    detection — which shells out to `ps` and breaks in sandboxes — activate
    without it). Codex round-2 review: PDD_SUPPRESS_SETUP_REMINDER must be set
    here, not inherited from the outer environment, so these tests stay
    hermetic."""
    csv_path = tmp_path / "cost.csv"
    monkeypatch.delenv("PYTEST_CURRENT_TEST", raising=False)
    monkeypatch.setenv("PDD_OUTPUT_COST_PATH", str(csv_path))
    monkeypatch.setenv("PDD_DISABLE_DUPLICATE_GUARD", "1")
    monkeypatch.setenv("PDD_AUTO_UPDATE", "false")
    monkeypatch.setenv("PDD_SUPPRESS_SETUP_REMINDER", "1")
    return csv_path


def _read_cost_rows(csv_path):
    with csv_path.open(newline="", encoding="utf-8") as handle:
        return list(csv.DictReader(handle))


def test_cli_sync_failure_still_writes_cost_csv_row(tmp_path, monkeypatch):
    """Codex review of PR #1982: the failure exit must NOT skip the track_cost
    CSV row. The agentic runner sets PDD_OUTPUT_COST_PATH for child syncs
    (pdd/agentic_sync_runner.py ~2398) and parses the row to accumulate cost and
    enforce --budget, so failed attempts must still record their cost."""
    monkeypatch.chdir(tmp_path)
    monkeypatch.setattr(
        "pdd.commands.maintenance.sync_main", _fake_sync_main(overall_success=False)
    )
    csv_path = _enable_cost_csv(tmp_path, monkeypatch)

    result = CliRunner().invoke(real_cli, ["--no-core-dump", "sync", "my_module"])

    assert result.exit_code != 0, result.output
    assert csv_path.is_file(), "failed sync must still write the cost CSV row"
    rows = _read_cost_rows(csv_path)
    assert len(rows) == 1, rows
    assert rows[0]["command"] == "sync"
    assert rows[0]["model"] == "test-model"
    assert float(rows[0]["cost"]) == pytest.approx(0.0123)


def test_cli_sync_success_writes_exactly_one_cost_csv_row(tmp_path, monkeypatch):
    """Successful syncs must keep writing exactly ONE cost row (no double-write
    from the failure-path plumbing)."""
    monkeypatch.chdir(tmp_path)
    monkeypatch.setattr(
        "pdd.commands.maintenance.sync_main", _fake_sync_main(overall_success=True)
    )
    csv_path = _enable_cost_csv(tmp_path, monkeypatch)

    result = CliRunner().invoke(real_cli, ["--no-core-dump", "sync", "my_module"])

    assert result.exit_code == 0, result.output
    rows = _read_cost_rows(csv_path)
    assert len(rows) == 1, rows
    assert rows[0]["command"] == "sync"
    assert float(rows[0]["cost"]) == pytest.approx(0.0123)


def test_failed_sync_restores_captured_streams_in_process(tmp_path, monkeypatch):
    """Codex round-2 review of PR #1982: the non-zero `click.exceptions.Exit`
    branch in PDDCLI.invoke must restore the core-dump `OutputCapture` streams
    before re-raising. The server executor invokes commands in-process
    (pdd/server/executor.py, ctx.invoke), so a failed sync with --core-dump
    would otherwise leak OutputCapture onto sys.stdout/sys.stderr for the rest
    of the process. Driven via cli.main(standalone_mode=False), the embedded
    top-level invocation shape (click returns the exit code for Exit there)."""
    from pdd.core.cli import OutputCapture  # noqa: PLC0415 - test-local import

    monkeypatch.chdir(tmp_path)
    monkeypatch.setattr(
        "pdd.commands.maintenance.sync_main", _fake_sync_main(overall_success=False)
    )
    monkeypatch.setenv("PDD_AUTO_UPDATE", "false")
    monkeypatch.setenv("PDD_SUPPRESS_SETUP_REMINDER", "1")

    original_stdout, original_stderr = sys.stdout, sys.stderr
    try:
        exit_code = real_cli.main(
            ["--core-dump", "sync", "my_module"], standalone_mode=False
        )
        leaked_stdout, leaked_stderr = sys.stdout, sys.stderr
    finally:
        # Never let a red run poison sys.stdout/sys.stderr for later tests.
        sys.stdout, sys.stderr = original_stdout, original_stderr

    assert exit_code == 1
    assert not isinstance(leaked_stdout, OutputCapture), (
        "failed sync leaked the core-dump OutputCapture onto sys.stdout"
    )
    assert leaked_stdout is original_stdout
    assert leaked_stderr is original_stderr
