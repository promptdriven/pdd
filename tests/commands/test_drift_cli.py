"""CLI smoke tests for ``pdd checkup drift`` (PR #1261 manual test plan)."""
from __future__ import annotations

import hashlib
import json
from pathlib import Path
from unittest.mock import patch

import pytest
from click.testing import CliRunner

from pdd.cli import cli
from pdd.commands.checkup import checkup


def _write_smoke_project(project: Path) -> None:
    prompt = project / "prompts" / "refund_payment_python.prompt"
    prompt.parent.mkdir(parents=True)
    prompt.write_text("<prompt>\nRefund module.\n</prompt>\n", encoding="utf-8")
    code = project / "src" / "refund_payment.py"
    code.parent.mkdir(parents=True)
    code.write_text(
        "def refund_payment(amount: int) -> int:\n    return amount\n",
        encoding="utf-8",
    )
    manifest = project / ".pdd" / "evidence" / "devunits" / "refund_payment.latest.json"
    manifest.parent.mkdir(parents=True)
    manifest.write_text(
        json.dumps(
            {
                "schema_version": 1,
                "prompt": {"path": str(prompt.relative_to(project))},
                "outputs": [
                    {
                        "path": str(code.relative_to(project)),
                        "sha256": hashlib.sha256(code.read_bytes()).hexdigest(),
                    }
                ],
                "validation": {
                    "detect_stories": "not_available",
                    "verify": "not_available",
                    "unit_tests": "not_available",
                },
            },
            indent=2,
        )
        + "\n",
        encoding="utf-8",
    )


@pytest.fixture
def runner() -> CliRunner:
    return CliRunner()


def test_checkup_drift_help(runner: CliRunner) -> None:
    result = runner.invoke(checkup, ["drift", "--help"])
    assert result.exit_code == 0
    assert "regeneration stability" in result.output.lower()
    assert "--dry-run" in result.output
    assert "--json" in result.output


def test_checkup_drift_dry_run_json(runner: CliRunner, tmp_path: Path, monkeypatch) -> None:
    _write_smoke_project(tmp_path)
    monkeypatch.chdir(tmp_path)
    result = runner.invoke(
        checkup,
        ["drift", "refund_payment", "--dry-run", "--json"],
        catch_exceptions=False,
    )
    assert result.exit_code == 0, result.output
    payload = json.loads(result.output)
    assert payload["status"] == "stable"
    assert payload["dry_run"] is True


def test_checkup_drift_from_evidence_json(runner: CliRunner, tmp_path: Path, monkeypatch) -> None:
    _write_smoke_project(tmp_path)
    monkeypatch.chdir(tmp_path)
    manifest = tmp_path / ".pdd" / "evidence" / "devunits" / "refund_payment.latest.json"
    result = runner.invoke(
        checkup,
        [
            "drift",
            "refund_payment",
            "--from-evidence",
            str(manifest),
            "--dry-run",
            "--json",
        ],
        catch_exceptions=False,
    )
    assert result.exit_code == 0, result.output
    payload = json.loads(result.output)
    assert payload["policy_check_skipped"] is True
    assert payload["policy_check_unavailable"] is False


def test_checkup_drift_runs_two_leaves_worktree_unchanged(
    runner: CliRunner,
    tmp_path: Path,
    monkeypatch,
) -> None:
    _write_smoke_project(tmp_path)
    monkeypatch.chdir(tmp_path)
    code = tmp_path / "src" / "refund_payment.py"
    before = code.read_bytes()
    stable_source = code.read_text(encoding="utf-8")

    def _fake_regenerate(_prompt_path: Path, output_path: Path, **kwargs) -> float:
        output_path.parent.mkdir(parents=True, exist_ok=True)
        output_path.write_text(stable_source, encoding="utf-8")
        return 0.0

    with patch("pdd.drift_main._regenerate_code", side_effect=_fake_regenerate):
        result = runner.invoke(
            checkup,
            ["drift", "refund_payment", "--runs", "2", "--json"],
            catch_exceptions=False,
        )
    assert result.exit_code == 0, result.output
    payload = json.loads(result.output)
    assert payload["runs"] == 2
    assert len(payload["snapshots"]) == 2
    assert code.read_bytes() == before


def test_no_top_level_pdd_drift_command(runner: CliRunner) -> None:
    result = runner.invoke(cli, ["--help"])
    assert result.exit_code == 0
    lines = [line.strip() for line in result.output.splitlines()]
    assert "drift" not in lines
    assert any(line.startswith("checkup") for line in lines)


def test_preview_does_not_inject_dry_run_into_drift(
    runner: CliRunner, tmp_path: Path, monkeypatch
) -> None:
    """--preview must never inject --dry-run into drift args (#1519 finding #3).

    pdd checkup drift <unit> --preview → drift must NOT receive --dry-run;
    drift --dry-run suppresses regeneration, which is unrelated to interactive apply preview.
    """
    _write_smoke_project(tmp_path)
    monkeypatch.chdir(tmp_path)

    captured = {}

    def _fake_drift_main(args, **kwargs):
        captured["args"] = list(args)
        return 0

    with patch("pdd.commands.checkup.drift_cmd.main", side_effect=_fake_drift_main):
        result = runner.invoke(
            checkup,
            ["drift", "refund_payment", "--preview"],
            catch_exceptions=False,
        )

    assert "--dry-run" not in captured.get("args", []), (
        "--preview must not forward --dry-run to drift"
    )


def test_explicit_dry_run_still_forwarded_to_drift(
    runner: CliRunner, tmp_path: Path, monkeypatch
) -> None:
    """User passing --dry-run directly as a drift arg must still reach drift unchanged."""
    _write_smoke_project(tmp_path)
    monkeypatch.chdir(tmp_path)

    result = runner.invoke(
        checkup,
        ["drift", "refund_payment", "--dry-run", "--json"],
        catch_exceptions=False,
    )
    assert result.exit_code == 0, result.output
    payload = json.loads(result.output)
    assert payload["dry_run"] is True
