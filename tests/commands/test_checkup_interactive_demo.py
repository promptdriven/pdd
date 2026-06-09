"""Focused routing tests for the demos/checkup_interactive demo fixtures.

Verifies that `pdd checkup <prompt> --explain --json` reaches the same call
abstraction layer as the direct subcommands (lint, contract, coverage, gate,
snapshot) for each demo prompt fixture.
"""
from __future__ import annotations

import json
from pathlib import Path

import pytest
from click.testing import CliRunner

from pdd.commands.checkup import checkup

DEMO = Path(__file__).parent.parent.parent / "demos" / "checkup_interactive"
PROMPTS = DEMO / "prompts"

FIXTURE_FILES = [
    "01_clean_task.prompt",
    "02_vague_requirements.prompt",
    "03_contract_coverage.prompt",
    "04_formatting_edge_case.prompt",
    "05_snapshot_candidate.prompt",
]


@pytest.fixture(scope="module")
def runner() -> CliRunner:
    return CliRunner()


def _run_explain_json(runner: CliRunner, prompt: Path) -> dict:
    result = runner.invoke(
        checkup,
        [str(prompt), "--explain", "--json"],
        catch_exceptions=False,
    )
    assert result.exit_code in (0, 1, 2), f"Unexpected exit: {result.exit_code}\n{result.output}"
    try:
        return json.loads(result.output)
    except json.JSONDecodeError as exc:
        pytest.fail(f"Non-JSON output for {prompt.name}: {exc}\n{result.output[:500]}")


def _check_status(data: dict, check_name: str) -> str:
    reports = data.get("reports", [])
    if not reports:
        return "?"
    for check in reports[0].get("checks", []):
        if check.get("name") == check_name:
            return check.get("status", "?")
    return "?"


def _findings_for(data: dict, source_check: str) -> list[dict]:
    reports = data.get("reports", [])
    if not reports:
        return []
    return [f for f in reports[0].get("findings", []) if f.get("source_check") == source_check]


# ---------------------------------------------------------------------------
# Fixture files exist and are readable
# ---------------------------------------------------------------------------

@pytest.mark.parametrize("filename", FIXTURE_FILES)
def test_demo_prompt_fixture_exists(filename: str) -> None:
    path = PROMPTS / filename
    assert path.is_file(), f"Demo fixture missing: {path}"
    assert path.read_text(encoding="utf-8").strip(), f"Demo fixture is empty: {path}"


def test_demo_readme_exists() -> None:
    assert (DEMO / "README.md").is_file()


def test_demo_run_script_exists() -> None:
    assert (DEMO / "run_demo.sh").is_file()


# ---------------------------------------------------------------------------
# Unified command reports all expected check names
# ---------------------------------------------------------------------------

EXPECTED_CHECK_NAMES = {"lint", "contract", "coverage", "gate", "snapshot"}


def test_unified_command_reports_all_check_names(runner: CliRunner) -> None:
    data = _run_explain_json(runner, PROMPTS / "01_clean_task.prompt")
    reports = data.get("reports", [])
    assert reports, "No reports in unified output"
    names = {c["name"] for c in reports[0].get("checks", [])}
    missing = EXPECTED_CHECK_NAMES - names
    assert not missing, f"Checks missing from unified output: {missing}"


# ---------------------------------------------------------------------------
# Per-prompt check status assertions
# ---------------------------------------------------------------------------

def test_clean_prompt_all_pass_or_skip(runner: CliRunner) -> None:
    data = _run_explain_json(runner, PROMPTS / "01_clean_task.prompt")
    for check_name in ("lint", "contract", "coverage", "gate", "snapshot"):
        status = _check_status(data, check_name)
        assert status in ("pass", "skip"), f"{check_name}: expected pass/skip, got {status!r}"


def test_vague_prompt_lint_warns(runner: CliRunner) -> None:
    data = _run_explain_json(runner, PROMPTS / "02_vague_requirements.prompt")
    assert _check_status(data, "lint") == "warn", "Expected lint: warn on vague prompt"
    lint_findings = _findings_for(data, "lint")
    assert len(lint_findings) > 0, "Expected lint findings on vague prompt"


def test_vague_prompt_findings_all_require_clarification(runner: CliRunner) -> None:
    data = _run_explain_json(runner, PROMPTS / "02_vague_requirements.prompt")
    lint_findings = _findings_for(data, "lint")
    assert lint_findings, "Expected lint findings"
    missing_field = [f for f in lint_findings if "requires_clarification" not in f]
    assert not missing_field, f"{len(missing_field)} findings missing requires_clarification field"
    not_flagged = [f for f in lint_findings if not f.get("requires_clarification")]
    assert not not_flagged, (
        f"{len(not_flagged)} vague-term findings have requires_clarification=False; "
        "they must be routed to the interactive path (#1438)"
    )


def test_contract_prompt_coverage_finds_unchecked_rules(runner: CliRunner) -> None:
    data = _run_explain_json(runner, PROMPTS / "03_contract_coverage.prompt")
    status = _check_status(data, "coverage")
    assert status in ("warn", "fail"), f"Expected coverage warn/fail, got {status!r}"
    cov_findings = _findings_for(data, "coverage")
    assert cov_findings, "Expected coverage findings (unchecked rules)"
    unchecked = [f for f in cov_findings if f.get("code") == "unchecked"]
    assert len(unchecked) == 3, f"Expected 3 unchecked rules (R901-R903), got {len(unchecked)}"


def test_formatting_edge_case_does_not_crash(runner: CliRunner) -> None:
    data = _run_explain_json(runner, PROMPTS / "04_formatting_edge_case.prompt")
    assert _check_status(data, "lint") in ("pass", "warn", "skip")


def test_snapshot_prompt_fails_snapshot_check(runner: CliRunner) -> None:
    data = _run_explain_json(runner, PROMPTS / "05_snapshot_candidate.prompt")
    assert _check_status(data, "snapshot") == "fail", "Expected snapshot: fail on nondeterministic prompt"
    snap_findings = _findings_for(data, "snapshot")
    assert any(f.get("code") == "snapshot_policy" for f in snap_findings), (
        "Expected snapshot_policy finding"
    )


# ---------------------------------------------------------------------------
# requires_clarification exclusion from auto-repair (issue #1438)
# ---------------------------------------------------------------------------

def test_requires_clarification_findings_excluded_from_auto_repair(runner: CliRunner) -> None:
    """Vague-term findings must not be processed by the automated repair loop."""
    from pdd.prompt_repair import _actionable_findings  # pylint: disable=import-outside-toplevel

    data = _run_explain_json(runner, PROMPTS / "02_vague_requirements.prompt")
    findings = data.get("reports", [{}])[0].get("findings", [])
    lint_findings = [f for f in findings if f.get("source_check") == "lint"]

    actionable = _actionable_findings(lint_findings)
    clarification_findings = [f for f in lint_findings if f.get("requires_clarification")]

    assert clarification_findings, "Expected clarification-flagged findings"
    for f in clarification_findings:
        assert f not in actionable, (
            f"Finding {f.get('id')} has requires_clarification=True but is in actionable list"
        )


# ---------------------------------------------------------------------------
# CLI flag validation
# ---------------------------------------------------------------------------

def test_apply_without_interactive_exits_2(runner: CliRunner) -> None:
    result = runner.invoke(
        checkup,
        [str(PROMPTS / "01_clean_task.prompt"), "--apply"],
    )
    assert result.exit_code == 2
    assert "requires --interactive" in result.output


def test_interactive_json_incompatible(runner: CliRunner) -> None:
    result = runner.invoke(
        checkup,
        [str(PROMPTS / "01_clean_task.prompt"), "--interactive", "--json"],
    )
    assert result.exit_code == 2
    assert "--json" in result.output or "interactive" in result.output
