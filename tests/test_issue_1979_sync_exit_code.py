"""Issue #1979: single-module `pdd sync <basename>` must exit non-zero when the
aggregated result reports `overall_success == False`.

Before this fix, the sync command printed `Overall status: Failed` in the final
summary panel but returned the `(str(result), total_cost, model_name)` cost-tracking
tuple unconditionally, so CI, shell `&&` chains, and the agentic child runners
(which key off the exit code) read a failed sync as success.

Convention: the #1677 AmbiguousModuleError handler and the agentic/global dispatch
helpers in the same command raise `click.exceptions.Exit(1)` on failure.
"""

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
