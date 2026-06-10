"""Demo verification tests for demos/checkup_interactive (issue #1423).

Two concerns are covered:

1. The demo assets are present, runnable, and documented with the current CLI
   surface (``--interactive``, ``--planner``, ``--auto``, and all six direct
   subcommands).
2. The unified ``pdd checkup <prompt>`` path reaches the same six check engines
   as the direct subcommands, and the agentic ``CheckupAgent`` drives them.

No test makes a live LLM or network call.
"""
from __future__ import annotations

import json
import re
from pathlib import Path

import pytest
from click.testing import CliRunner

from pdd.commands.checkup import checkup

DEMO = Path(__file__).parent.parent.parent / "demos" / "checkup_interactive"
PROMPTS = DEMO / "prompts"
RUN_SCRIPT = DEMO / "run_demo.sh"
README = DEMO / "README.md"

FIXTURE_FILES = [
    "01_clean_task.prompt",
    "02_vague_clarification.prompt",
    "03_formatting_edge_case.prompt",
    "04_contract_sensitive.prompt",
    "05_coverage_sensitive.prompt",
    "06_snapshot_candidate.prompt",
    "07_drift_candidate.prompt",
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
# Demo assets present
# ---------------------------------------------------------------------------

@pytest.mark.parametrize("filename", FIXTURE_FILES)
def test_demo_prompt_fixture_exists(filename: str) -> None:
    path = PROMPTS / filename
    assert path.is_file(), f"Demo fixture missing: {path}"
    assert path.read_text(encoding="utf-8").strip(), f"Demo fixture is empty: {path}"


def test_demo_readme_exists() -> None:
    assert README.is_file()


def test_demo_run_script_exists_and_executable() -> None:
    assert RUN_SCRIPT.is_file()
    import os

    assert os.access(RUN_SCRIPT, os.X_OK), "run_demo.sh must be executable"


def test_drift_workspace_fixture_exists() -> None:
    """The direct drift command needs a resolvable dev unit (prompt + baseline)."""
    ws = DEMO / "drift_workspace"
    assert (ws / "prompts" / "drift_candidate_python.prompt").is_file()
    assert (ws / "src" / "drift_candidate.py").is_file()


# ---------------------------------------------------------------------------
# run_demo.sh content contract
# ---------------------------------------------------------------------------

def _script_text() -> str:
    return RUN_SCRIPT.read_text(encoding="utf-8")


def test_run_script_uses_python_m_pdd_not_stale_binary() -> None:
    text = _script_text()
    assert "python -m pdd" in text, "Demo must invoke `python -m pdd`"
    # No bare `pdd ` CLI invocations that would hit a stale .venv/bin/pdd.
    bare = re.findall(r"(?m)^\s*pdd\s+checkup", text)
    assert not bare, f"Found bare `pdd checkup` invocations (use python -m pdd): {bare}"


def test_run_script_exercises_agentic_flags() -> None:
    text = _script_text()
    for flag in ("--interactive", "--planner deterministic", "--planner llm", "--auto"):
        assert flag in text, f"run_demo.sh should exercise `{flag}`"


def test_run_script_covers_all_six_direct_subcommands() -> None:
    text = _script_text()
    for sub in (
        "checkup lint",
        "checkup contract check",
        "checkup coverage",
        "checkup gate",
        "checkup snapshot",
        "checkup drift",
    ):
        assert sub in text, f"run_demo.sh should call `python -m pdd {sub}`"


def test_run_script_documents_replay_flags() -> None:
    text = _script_text()
    for flag in ("--all", "--deterministic", "--auto", "--llm-fallback", "--direct", "--cleanup"):
        assert flag in text, f"run_demo.sh should support `{flag}`"


def test_run_script_help_runs() -> None:
    import subprocess

    proc = subprocess.run(
        ["bash", str(RUN_SCRIPT), "--help"],
        capture_output=True,
        text=True,
        timeout=30,
    )
    assert proc.returncode == 0
    assert "Usage" in proc.stdout or "usage" in proc.stdout.lower()


# ---------------------------------------------------------------------------
# README documents the agentic surface
# ---------------------------------------------------------------------------

def test_readme_documents_agentic_architecture() -> None:
    text = README.read_text(encoding="utf-8")
    for token in (
        "CheckupAgent",
        "CheckupTool",
        "DeterministicPlanner",
        "LLMPlanner",
        "--planner",
        "--auto",
        "pip install -e .",
        "python -m pdd",
    ):
        assert token in text, f"README should document `{token}`"


# ---------------------------------------------------------------------------
# Unified command reaches all six engines
# ---------------------------------------------------------------------------

EXPECTED_CHECK_NAMES = {"lint", "contract", "coverage", "gate", "snapshot", "drift"}


def test_unified_command_reports_all_check_names(runner: CliRunner) -> None:
    data = _run_explain_json(runner, PROMPTS / "01_clean_task.prompt")
    reports = data.get("reports", [])
    assert reports, "No reports in unified output"
    names = {c["name"] for c in reports[0].get("checks", [])}
    missing = EXPECTED_CHECK_NAMES - names
    # drift may be absent for a bare prompt with no dev unit; the other five
    # must always be present in the unified report.
    assert not (missing - {"drift"}), f"Checks missing from unified output: {missing}"


# ---------------------------------------------------------------------------
# Per-prompt check status assertions
# ---------------------------------------------------------------------------

def test_clean_prompt_all_pass_or_skip(runner: CliRunner) -> None:
    data = _run_explain_json(runner, PROMPTS / "01_clean_task.prompt")
    for check_name in ("lint", "contract", "coverage", "gate", "snapshot"):
        status = _check_status(data, check_name)
        assert status in ("pass", "skip"), f"{check_name}: expected pass/skip, got {status!r}"


def test_vague_prompt_lint_warns(runner: CliRunner) -> None:
    data = _run_explain_json(runner, PROMPTS / "02_vague_clarification.prompt")
    assert _check_status(data, "lint") == "warn", "Expected lint: warn on vague prompt"
    assert _findings_for(data, "lint"), "Expected lint findings on vague prompt"


def test_vague_prompt_findings_all_require_clarification(runner: CliRunner) -> None:
    data = _run_explain_json(runner, PROMPTS / "02_vague_clarification.prompt")
    lint_findings = _findings_for(data, "lint")
    assert lint_findings, "Expected lint findings"
    not_flagged = [f for f in lint_findings if not f.get("requires_clarification")]
    assert not not_flagged, (
        f"{len(not_flagged)} vague-term findings have requires_clarification=False; "
        "they must be routed to the interactive path (#1438)"
    )


def test_contract_prompt_coverage_finds_unchecked_rules(runner: CliRunner) -> None:
    data = _run_explain_json(runner, PROMPTS / "04_contract_sensitive.prompt")
    status = _check_status(data, "coverage")
    assert status in ("warn", "fail"), f"Expected coverage warn/fail, got {status!r}"
    unchecked = [f for f in _findings_for(data, "coverage") if f.get("code") == "unchecked"]
    assert len(unchecked) == 3, f"Expected 3 unchecked rules (R901-R903), got {len(unchecked)}"


def test_coverage_sensitive_prompt_finds_unchecked_rules(runner: CliRunner) -> None:
    data = _run_explain_json(runner, PROMPTS / "05_coverage_sensitive.prompt")
    status = _check_status(data, "coverage")
    assert status in ("warn", "fail"), f"Expected coverage warn/fail, got {status!r}"
    unchecked = [f for f in _findings_for(data, "coverage") if f.get("code") == "unchecked"]
    assert len(unchecked) == 4, f"Expected 4 unchecked rules (R301-R304), got {len(unchecked)}"


def test_formatting_edge_case_does_not_crash(runner: CliRunner) -> None:
    data = _run_explain_json(runner, PROMPTS / "03_formatting_edge_case.prompt")
    assert _check_status(data, "lint") in ("pass", "warn", "skip")


def test_snapshot_prompt_fails_snapshot_check(runner: CliRunner) -> None:
    data = _run_explain_json(runner, PROMPTS / "06_snapshot_candidate.prompt")
    assert _check_status(data, "snapshot") == "fail", "Expected snapshot: fail on nondeterministic prompt"
    snap_findings = _findings_for(data, "snapshot")
    assert any(f.get("code") == "snapshot_policy" for f in snap_findings), (
        "Expected snapshot_policy finding"
    )


# ---------------------------------------------------------------------------
# Agentic workflow reaches all six tools (offline, no TTY, no LLM)
# ---------------------------------------------------------------------------

def test_agentic_agent_reaches_all_six_tools_in_auto_mode(tmp_path) -> None:
    """Drive CheckupAgent in auto mode over a demo prompt; assert six tool_start events."""
    from pdd.checkup_agent import CheckupAgent, RecordingCheckupSession
    from pdd.checkup_planner import DeterministicPlanner

    session = RecordingCheckupSession()
    agent = CheckupAgent(DeterministicPlanner(), session)
    agent.run(
        str(PROMPTS / "05_coverage_sensitive.prompt"),
        project_root=DEMO.parent.parent,
        quiet=True,
        auto=True,
    )
    reached = {e.data["tool"] for e in session.events_of_kind("tool_start")}
    assert reached == EXPECTED_CHECK_NAMES, f"Agent did not reach all six tools: {reached}"


# ---------------------------------------------------------------------------
# CLI flag validation
# ---------------------------------------------------------------------------

def test_planner_flag_exposed_in_help(runner: CliRunner) -> None:
    result = runner.invoke(checkup, ["--help"], catch_exceptions=False)
    assert "--planner" in result.output
    assert "--auto" in result.output


def test_apply_without_interactive_exits_2(runner: CliRunner) -> None:
    result = runner.invoke(checkup, [str(PROMPTS / "01_clean_task.prompt"), "--apply"])
    assert result.exit_code == 2
    assert "requires --interactive" in result.output


def test_interactive_json_incompatible(runner: CliRunner) -> None:
    result = runner.invoke(
        checkup,
        [str(PROMPTS / "01_clean_task.prompt"), "--interactive", "--json"],
    )
    assert result.exit_code == 2


# ---------------------------------------------------------------------------
# Review-mode UX (the simple default command) — CLI level
# ---------------------------------------------------------------------------


def test_review_mode_groups_vague_terms_and_is_concise(runner: CliRunner, tmp_path) -> None:
    """`pdd checkup <vague> --planner deterministic` collapses 10 prompts into one."""
    result = runner.invoke(
        checkup,
        [
            str(PROMPTS / "02_vague_clarification.prompt"),
            "--planner",
            "deterministic",
            "--project-root",
            str(tmp_path),
        ],
        catch_exceptions=False,
    )
    out = result.output
    # grouped, not ten separate menus
    assert "undefined vague terms" in out
    assert "Apply recommended safe fix" not in out  # review mode never prompts
    # final summary distinguishes categories
    assert "Total:" in out and "Remaining:" in out
    assert "Saved for review:" in out


def test_review_mode_shows_skip_reasons(runner: CliRunner, tmp_path) -> None:
    result = runner.invoke(
        checkup,
        [
            str(PROMPTS / "02_vague_clarification.prompt"),
            "--planner",
            "deterministic",
            "--project-root",
            str(tmp_path),
        ],
        catch_exceptions=False,
    )
    assert "no <contract_rules> to cover" in result.output  # coverage skip reason
    assert "no baseline evidence" in result.output  # drift skip reason


def test_review_mode_writes_artifacts_under_project_root(runner: CliRunner, tmp_path) -> None:
    runner.invoke(
        checkup,
        [
            str(PROMPTS / "02_vague_clarification.prompt"),
            "--planner",
            "deterministic",
            "--project-root",
            str(tmp_path),
        ],
        catch_exceptions=False,
    )
    out_dir = tmp_path / ".pdd" / "checkup"
    assert (out_dir / "02_vague_clarification.report.md").is_file()
    assert (out_dir / "02_vague_clarification.patch").is_file()


def test_clean_prompt_writes_no_artifacts(runner: CliRunner, tmp_path) -> None:
    runner.invoke(
        checkup,
        [
            str(PROMPTS / "01_clean_task.prompt"),
            "--planner",
            "deterministic",
            "--project-root",
            str(tmp_path),
        ],
        catch_exceptions=False,
    )
    assert not (tmp_path / ".pdd" / "checkup").exists()
