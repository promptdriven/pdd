"""Tests for checkup advisory layer and --review option."""
from __future__ import annotations

from pathlib import Path
from unittest.mock import patch

import pytest
from click.testing import CliRunner

from pdd.checkup_advisory import (
    CheckupReport,
    SKIPPED_REPORT,
    advisory_for_review,
    failed_report,
    final_exit_code,
    report_as_dict,
)
from pdd.commands.checkup_snapshot import checkup_snapshot
from pdd.commands.gate import gate_cmd


def test_final_exit_code_unchanged_by_advisory() -> None:
    assert final_exit_code(1, failed_report("boom")) == 1
    assert final_exit_code(0, CheckupReport(status="warned", findings=[])) == 0


def test_advisory_skipped_when_review_off() -> None:
    report = advisory_for_review("off", {"passed": False}, command="test")
    assert report.status == "skipped"
    assert SKIPPED_REPORT.status == "skipped"


def test_snapshot_rejects_review_explain() -> None:
    runner = CliRunner()
    prompt = (
        Path(__file__).resolve().parents[1]
        / "tests/fixtures/prompt_lint/clean.prompt"
    )
    result = runner.invoke(
        checkup_snapshot,
        ["--review", "explain", str(prompt)],
    )
    assert result.exit_code != 0
    assert "not supported" in result.output


def test_gate_json_includes_advisory_key_when_review_explain() -> None:
    runner = CliRunner()
    with patch("pdd.commands.gate.run_gate_policy") as gate, patch(
        "pdd.checkup_advisory.run_advisory_explain"
    ) as explain:
        from pdd.gate_main import GateResult

        gate.return_value = GateResult(passed=True, manifests_checked=0)
        explain.return_value = CheckupReport(status="ok", findings=[])
        result = runner.invoke(
            gate_cmd,
            ["--json", "--review", "explain", "--skip-waivers", "--skip-evidence"],
            obj={"quiet": True, "local": True},
        )
    assert result.exit_code == 0, result.output
    payload = __import__("json").loads(result.output)
    assert "advisory" in payload
    assert payload["advisory"]["status"] == "ok"


def test_gate_json_omits_advisory_when_review_off() -> None:
    runner = CliRunner()
    with patch("pdd.commands.gate.run_gate_policy") as gate:
        from pdd.gate_main import GateResult

        gate.return_value = GateResult(passed=True, manifests_checked=0)
        result = runner.invoke(
            gate_cmd,
            ["--json", "--skip-waivers", "--skip-evidence"],
            obj={"quiet": True, "local": True},
        )
    assert result.exit_code == 0, result.output
    payload = __import__("json").loads(result.output)
    assert "advisory" not in payload
