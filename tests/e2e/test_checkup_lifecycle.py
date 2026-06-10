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
# Directory targets
# ---------------------------------------------------------------------------


def test_directory_checkup_summarizes_and_gates(runner: CliRunner, tmp_path) -> None:
    """`pdd checkup <dir>/` checks every prompt and gives one pass/warn/block summary."""
    result = runner.invoke(
        checkup,
        [str(PROMPTS), "--project-root", str(tmp_path)],
        catch_exceptions=False,
    )
    out = result.output
    assert "01_clean_task.prompt: pass" in out
    assert "02_vague_clarification.prompt: warn" in out
    assert "06_snapshot_candidate.prompt: fail" in out
    assert "Summary:" in out and "block over" in out
    # one prompt (06) is a hard block → the directory gate exits 2
    assert result.exit_code == 2


def test_empty_directory_fails_clearly(runner: CliRunner, tmp_path) -> None:
    empty = tmp_path / "prompts"
    empty.mkdir()
    result = runner.invoke(
        checkup, [str(empty), "--project-root", str(tmp_path)]
    )
    assert result.exit_code != 0
    assert "No .prompt files found" in result.output


def test_directory_with_interactive_is_rejected_clearly(runner: CliRunner, tmp_path) -> None:
    from unittest.mock import patch

    # Assume a TTY so we reach the directory guard (not the TTY guard).
    with patch("pdd.commands.checkup._interactive_tty_available", return_value=True):
        result = runner.invoke(
            checkup,
            [str(PROMPTS), "--interactive", "--project-root", str(tmp_path)],
        )
    assert result.exit_code != 0
    assert "single .prompt file" in result.output


# ---------------------------------------------------------------------------
# apply gating
# ---------------------------------------------------------------------------


def test_interactive_quit_is_clean(runner: CliRunner, tmp_path) -> None:
    """Typing q on a group quits the session cleanly, touching nothing."""
    from unittest.mock import patch

    with patch("pdd.commands.checkup._interactive_tty_available", return_value=True):
        result = runner.invoke(
            checkup,
            [str(PROMPTS / "02_vague_clarification.prompt"), "--interactive",
             "--project-root", str(tmp_path)],
            input="Y\nq\n",   # confirm plan, then quit on the first group
            catch_exceptions=False,
        )
    assert "Quit" in result.output
    assert "Checkup complete" in result.output  # still summarised, not crashed


def test_apply_alone_rejected(runner: CliRunner, tmp_path) -> None:
    result = runner.invoke(
        checkup,
        [str(PROMPTS / "02_vague_clarification.prompt"), "--apply",
         "--project-root", str(tmp_path)],
    )
    assert result.exit_code != 0
    assert "--apply requires --interactive or --auto" in result.output


def test_auto_apply_preview_allowed(runner: CliRunner, tmp_path) -> None:
    """--auto --apply --preview is allowed and writes nothing (medium-risk saved)."""
    result = runner.invoke(
        checkup,
        [str(PROMPTS / "02_vague_clarification.prompt"), "--auto", "--apply", "--preview",
         "--project-root", str(tmp_path)],
        catch_exceptions=False,
    )
    assert result.exit_code == 0
    assert "Checkup complete" in result.output


# ---------------------------------------------------------------------------
# Report / patch are reviewer-friendly (actionable-first, no raw internals)
# ---------------------------------------------------------------------------


def test_report_is_actionable_first(runner: CliRunner, tmp_path) -> None:
    _run(runner, [str(PROMPTS / "02_vague_clarification.prompt")], tmp_path)
    text = (tmp_path / ".pdd" / "checkup" / "02_vague_clarification.report.md").read_text()
    # "What to do" comes before the raw finding-ID traceability section
    assert "## What to do" in text
    assert text.index("## What to do") < text.index("## Traceability")
    assert "<details>" in text  # IDs collapsed


def test_patch_uses_relative_paths_and_line_context(runner: CliRunner, tmp_path) -> None:
    _run(runner, [str(PROMPTS / "02_vague_clarification.prompt")], tmp_path)
    text = (tmp_path / ".pdd" / "checkup" / "02_vague_clarification.patch").read_text()
    assert "<vocabulary>" in text                     # actionable stub first
    assert str(tmp_path) not in text                  # no absolute paths
    assert "# at:" in text                            # line context, not a python dict
    assert "anchor: {" not in text


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


def test_bare_command_is_agentic_by_default(runner: CliRunner, tmp_path) -> None:
    """`pdd checkup <prompt>` with NO flags is the agentic review (grouped + decision)."""
    result = runner.invoke(
        checkup,
        [str(PROMPTS / "02_vague_clarification.prompt"), "--project-root", str(tmp_path)],
        catch_exceptions=False,
    )
    assert result.exit_code == 0
    assert "Plan:" in result.output
    assert "undefined vague terms" in result.output       # grouped
    assert "Decision:" in result.output                   # gate
    assert (tmp_path / ".pdd" / "checkup").exists()        # artifacts


def test_prompt_directory_default_uses_aggregate_multi_target_path(
    runner: CliRunner,
    tmp_path,
) -> None:
    """`pdd checkup prompts/` must not be intercepted by the single-file agent."""
    result = runner.invoke(
        checkup,
        [str(PROMPTS), "--project-root", str(tmp_path)],
        catch_exceptions=False,
    )

    assert result.exit_code in (0, 1, 2)
    assert "requires a single .prompt file target" not in result.output
    assert "Expected a single .prompt file" not in result.output
    assert "Checkup:" in result.output
    assert "Summary:" in result.output
    assert "Decision:" in result.output


def test_prompt_directory_auto_uses_aggregate_multi_target_path(
    runner: CliRunner,
    tmp_path,
) -> None:
    """`--auto` on a directory should not turn a documented target into UsageError."""
    result = runner.invoke(
        checkup,
        [str(PROMPTS), "--auto", "--project-root", str(tmp_path)],
        catch_exceptions=False,
    )

    assert result.exit_code in (0, 1, 2)
    assert "requires a single .prompt file target" not in result.output
    assert "Expected a single .prompt file" not in result.output
    assert "Checkup:" in result.output
    assert "Summary:" in result.output
    assert "Decision:" in result.output


def test_devunit_default_uses_structured_path(
    runner: CliRunner,
    tmp_path,
) -> None:
    """A devunit target advertised by help should remain a valid default target."""
    prompts_dir = tmp_path / "prompts"
    prompts_dir.mkdir()
    (prompts_dir / "refund_payment_python.prompt").write_text(
        (PROMPTS / "01_clean_task.prompt").read_text(encoding="utf-8"),
        encoding="utf-8",
    )

    result = runner.invoke(
        checkup,
        ["refund_payment", "--project-root", str(tmp_path)],
        catch_exceptions=False,
    )

    assert result.exit_code in (0, 1)
    assert "requires a single .prompt file target" not in result.output
    assert "Expected a single .prompt file" not in result.output
    assert "Prompt:" in result.output
    assert "Status:" in result.output


def test_missing_prompt_file_error_is_specific(runner: CliRunner, tmp_path) -> None:
    result = runner.invoke(
        checkup,
        [str(tmp_path / "typo.prompt")],
        catch_exceptions=False,
    )

    assert result.exit_code == 2
    assert "Prompt file not found" in result.output
    assert "requires a single .prompt file target" not in result.output


def test_empty_prompt_directory_error_is_specific(runner: CliRunner, tmp_path) -> None:
    prompts_dir = tmp_path / "prompts"
    prompts_dir.mkdir()

    result = runner.invoke(
        checkup,
        ["prompts", "--project-root", str(tmp_path)],
        catch_exceptions=False,
    )

    assert result.exit_code == 2
    assert "No .prompt files found under" in result.output
    assert "TARGET must be a GitHub issue URL" not in result.output


def test_bare_json_stays_structured(runner: CliRunner, tmp_path) -> None:
    """--json on the bare command keeps the structured (non-agent) output."""
    result = runner.invoke(
        checkup,
        [str(PROMPTS / "02_vague_clarification.prompt"), "--json",
         "--project-root", str(tmp_path)],
        catch_exceptions=False,
    )
    import json as _json

    data = _json.loads(result.output)
    assert data["status"] == "warn"
    assert "Decision:" not in result.output  # not the agent path


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
def test_run_demo_full_workflow_uses_directory_command() -> None:
    """--workflow runs the one directory command and shows an aggregate summary."""
    proc = _bash("--workflow")
    assert proc.returncode == 0, proc.stdout[-2000:]
    # per-prompt decision lines from the directory summary
    assert "01_clean_task.prompt: pass" in proc.stdout
    assert "06_snapshot_candidate.prompt: fail" in proc.stdout
    assert "→ continue" in proc.stdout
    assert "→ block" in proc.stdout  # 06_snapshot is a hard block
    assert "Summary:" in proc.stdout and "block over" in proc.stdout
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
