"""End-to-end tests for the `pdd checkup` lifecycle and demo (issue #1423).

Exercises the real CLI path (via Click's CliRunner) over every demo prompt and
the run_demo.sh script (via subprocess). No real LLM calls — the deterministic
planner is used throughout, and CI has no credential so any LLM path falls back.
"""

from __future__ import annotations

import subprocess
import sys
from pathlib import Path

import pytest
from click.testing import CliRunner

from pdd.commands.checkup import checkup

REPO_ROOT = Path(__file__).resolve().parents[2]
DEMO = REPO_ROOT / "demos" / "checkup_interactive"
PROMPTS = DEMO / "prompts"
RUN_SCRIPT = DEMO / "run_demo.sh"

ALL_PROMPTS = sorted(PROMPTS.glob("*.prompt"))


@pytest.fixture
def runner() -> CliRunner:
    return CliRunner()


def _run(runner: CliRunner, args, tmp_path) -> "object":
    """Invoke checkup in review mode with artifacts isolated to tmp_path."""
    return runner.invoke(
        checkup,
        [*args, "--planner", "deterministic", "--project-root", str(tmp_path)],
        catch_exceptions=False,
    )


# ---------------------------------------------------------------------------
# Every prompt is runnable
# ---------------------------------------------------------------------------


def test_demo_has_prompts() -> None:
    assert ALL_PROMPTS, "no demo prompts found"


@pytest.mark.parametrize("prompt", ALL_PROMPTS, ids=lambda p: p.name)
def test_every_prompt_runs_and_decides(runner: CliRunner, prompt: Path, tmp_path) -> None:
    """Each prompt runs without crashing and prints a lifecycle Decision.

    exit 0 = continue, exit 2 = block; both are valid checkup outcomes.
    """
    result = _run(runner, [str(prompt)], tmp_path)
    assert result.exit_code in (0, 2), (
        f"{prompt.name} crashed (exit {result.exit_code})\n{result.output[:800]}"
    )
    assert "Decision:" in result.output, f"{prompt.name} printed no Decision"
    assert "→ continue" in result.output or "→ block" in result.output


# ---------------------------------------------------------------------------
# pass / warn / strict-block decisions
# ---------------------------------------------------------------------------


def test_clean_prompt_passes_and_continues(runner: CliRunner, tmp_path) -> None:
    result = _run(runner, [str(PROMPTS / "01_clean_task.prompt")], tmp_path)
    assert result.exit_code == 0
    assert "pass → continue" in result.output


def test_vague_prompt_warns_and_continues(runner: CliRunner, tmp_path) -> None:
    result = _run(runner, [str(PROMPTS / "02_vague_clarification.prompt")], tmp_path)
    assert result.exit_code == 0
    assert "warn → continue" in result.output
    assert "undefined vague terms" in result.output  # grouped


def test_strict_mode_blocks(runner: CliRunner, tmp_path) -> None:
    result = runner.invoke(
        checkup,
        [
            str(PROMPTS / "02_vague_clarification.prompt"),
            "--planner", "deterministic",
            "--strict",
            "--project-root", str(tmp_path),
        ],
        catch_exceptions=False,
    )
    assert result.exit_code == 2
    assert "strict failure → block" in result.output


def test_snapshot_prompt_blocks_on_hard_error(runner: CliRunner, tmp_path) -> None:
    """A snapshot-policy error is a hard block even without --strict."""
    result = _run(runner, [str(PROMPTS / "06_snapshot_candidate.prompt")], tmp_path)
    assert result.exit_code == 2
    assert "→ block" in result.output


# ---------------------------------------------------------------------------
# Skip reasons and accounting in real output
# ---------------------------------------------------------------------------


def test_skip_reasons_present(runner: CliRunner, tmp_path) -> None:
    result = _run(runner, [str(PROMPTS / "02_vague_clarification.prompt")], tmp_path)
    assert "no <contract_rules> to cover" in result.output
    assert "no baseline evidence" in result.output


def test_accounting_blocks_present(runner: CliRunner, tmp_path) -> None:
    result = _run(runner, [str(PROMPTS / "02_vague_clarification.prompt")], tmp_path)
    for token in ("Findings:", "Total:", "Remaining:", "Patches:", "Decision:"):
        assert token in result.output


def test_artifacts_written_for_findings(runner: CliRunner, tmp_path) -> None:
    _run(runner, [str(PROMPTS / "02_vague_clarification.prompt")], tmp_path)
    out = tmp_path / ".pdd" / "checkup"
    assert (out / "02_vague_clarification.report.md").is_file()
    assert (out / "02_vague_clarification.patch").is_file()


def test_no_artifacts_for_clean_pass(runner: CliRunner, tmp_path) -> None:
    _run(runner, [str(PROMPTS / "01_clean_task.prompt")], tmp_path)
    assert not (tmp_path / ".pdd" / "checkup").exists()


def test_non_interactive_does_not_hang(runner: CliRunner, tmp_path) -> None:
    """Review mode must never block on input (no stdin provided here)."""
    result = _run(runner, [str(PROMPTS / "04_contract_sensitive.prompt")], tmp_path)
    assert result.exit_code in (0, 2)
    assert "Apply recommended safe fix" not in result.output  # no prompt


# ---------------------------------------------------------------------------
# Full workflow & strict-gate demo scripts (real subprocess)
# ---------------------------------------------------------------------------


def _bash(flag: str):
    return subprocess.run(
        ["bash", str(RUN_SCRIPT), flag],
        capture_output=True,
        text=True,
        timeout=300,
        cwd=str(REPO_ROOT),
    )


@pytest.mark.slow
def test_run_demo_strict_gate_passes() -> None:
    proc = _bash("--strict-gate")
    assert proc.returncode == 0, proc.stdout[-2000:]
    assert "pass → continue" in proc.stdout
    assert "strict failure → block" in proc.stdout
    assert "FAIL: 0" in proc.stdout


@pytest.mark.slow
def test_run_demo_full_workflow_runs_auto_over_every_prompt() -> None:
    """--workflow runs `checkup <prompt> --planner deterministic --auto` per prompt."""
    proc = _bash("--workflow")
    assert proc.returncode == 0, proc.stdout[-2000:]
    assert "--planner deterministic --auto" in proc.stdout
    # every demo prompt appears as an auto checkup line
    for prompt in ALL_PROMPTS:
        assert f"checkup {prompt.name} --auto" in proc.stdout
    # a per-prompt lifecycle decision is shown, and the tally is printed
    assert "→ continue" in proc.stdout
    assert "→ block" in proc.stdout  # 06_snapshot is a hard block
    assert "Prompts checked:" in proc.stdout
    assert "FAIL: 0" in proc.stdout


def test_full_workflow_doc_exists_and_describes_lifecycle() -> None:
    doc = DEMO / "FULL_WORKFLOW.md"
    assert doc.is_file()
    text = doc.read_text()
    for token in (
        "PRD / issue / user request",
        "automatic prompt checkup",
        "interactive repair",
        "strict failure → block",
        "generate or modify code",
        "pdd checkup",
        "pdd generate",
    ):
        assert token in text, f"FULL_WORKFLOW.md missing: {token}"


def test_run_demo_help_lists_workflow_flags() -> None:
    proc = _bash("--help")
    assert proc.returncode == 0
    for flag in ("--workflow", "--strict-gate", "--all", "--cleanup"):
        assert flag in proc.stdout
