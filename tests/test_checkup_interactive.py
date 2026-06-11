"""Tests for interactive checkup flags and interaction policy.

Covers:
- non-TTY + --interactive → UsageError
- --apply without --interactive → UsageError
- --dry-run: no file writes (including no backup)
- --interactive without --apply: no file writes
- skip flow: choice 4 skips all findings
"""
from __future__ import annotations

from pathlib import Path
from unittest.mock import MagicMock, patch

import pytest
from click.testing import CliRunner

from pdd.commands.checkup import checkup
from pdd.checkup_interactive_main import InteractiveRepairSession, run_interactive_checkup
from pdd.checkup_prompt_main import PromptSourceSetReport, SourceSetFinding


# ---------------------------------------------------------------------------
# Helpers
# ---------------------------------------------------------------------------

def _make_finding(finding_id: str = "F001") -> SourceSetFinding:
    return SourceSetFinding(
        finding_id=finding_id,
        source_check="lint",
        severity="warn",
        file=Path("prompts/test.prompt"),
        message="Test finding",
        evidence="some evidence",
        recommended_action="Fix the issue",
    )


def _make_report(tmp_path: Path, findings: list[SourceSetFinding] | None = None) -> PromptSourceSetReport:
    prompt_path = tmp_path / "test.prompt"
    return PromptSourceSetReport(
        prompt_path=prompt_path,
        project_root=tmp_path,
        target=str(prompt_path),
        findings=findings or [],
    )


# ---------------------------------------------------------------------------
# Guard: non-TTY + --interactive → UsageError
# ---------------------------------------------------------------------------

def test_interactive_requires_tty(tmp_path: Path) -> None:
    """--interactive in a non-TTY context (CliRunner) must raise UsageError."""
    prompt_file = tmp_path / "test.prompt"
    prompt_file.write_text("test prompt content")

    runner = CliRunner()
    result = runner.invoke(checkup, [str(prompt_file), "--interactive"])

    assert result.exit_code != 0
    assert "TTY" in result.output or "tty" in result.output.lower()


# ---------------------------------------------------------------------------
# Guard: --apply without --interactive → UsageError
# ---------------------------------------------------------------------------

def test_apply_requires_interactive(tmp_path: Path) -> None:
    """--apply without --interactive must raise UsageError regardless of TTY."""
    prompt_file = tmp_path / "test.prompt"
    prompt_file.write_text("test prompt content")

    runner = CliRunner()
    result = runner.invoke(checkup, [str(prompt_file), "--apply"])

    assert result.exit_code != 0
    assert "--apply requires --interactive" in result.output


# ---------------------------------------------------------------------------
# --dry-run: no writes including no backup
# ---------------------------------------------------------------------------

def test_dry_run_no_writes(tmp_path: Path) -> None:
    """--dry-run must not modify any files or create backups."""
    prompt_file = tmp_path / "test.prompt"
    original_content = "original prompt content"
    prompt_file.write_text(original_content)

    finding = _make_finding("DRY-001")
    report = _make_report(tmp_path, [finding])

    with patch("pdd.checkup_interactive_main.build_prompt_source_set_report", return_value=report):
        with patch("click.prompt", return_value=1):  # choose "apply" option
            run_interactive_checkup(
                str(prompt_file),
                apply=True,
                dry_run=True,
                project_root=tmp_path,
                quiet=True,
            )

    # File must be unchanged
    assert prompt_file.read_text() == original_content
    # No backup file created
    backup_files = list(tmp_path.glob("*.bak")) + list(tmp_path.glob("*.prompt.bak"))
    assert backup_files == [], f"Unexpected backup files: {backup_files}"


# ---------------------------------------------------------------------------
# --interactive without --apply: no writes
# ---------------------------------------------------------------------------

def test_interactive_no_writes(tmp_path: Path) -> None:
    """--interactive without --apply must not modify any files."""
    prompt_file = tmp_path / "test.prompt"
    original_content = "original prompt content"
    prompt_file.write_text(original_content)

    finding = _make_finding("NW-001")
    report = _make_report(tmp_path, [finding])

    with patch("pdd.checkup_interactive_main.build_prompt_source_set_report", return_value=report):
        with patch("click.prompt", return_value=1):  # choose "apply" option, but apply=False
            run_interactive_checkup(
                str(prompt_file),
                apply=False,
                dry_run=False,
                project_root=tmp_path,
                quiet=True,
            )

    assert prompt_file.read_text() == original_content
    backup_files = list(tmp_path.glob("*.bak")) + list(tmp_path.glob("*.prompt.bak"))
    assert backup_files == [], f"Unexpected backup files: {backup_files}"


# ---------------------------------------------------------------------------
# Skip flow: choice 4 skips finding
# ---------------------------------------------------------------------------

def test_skip_flow(tmp_path: Path) -> None:
    """Choice 4 (Skip) must not apply any changes and count as skipped."""
    prompt_file = tmp_path / "test.prompt"
    prompt_file.write_text("prompt content")

    findings = [_make_finding("SK-001"), _make_finding("SK-002")]
    report = _make_report(tmp_path, findings)

    with patch("pdd.checkup_interactive_main.build_prompt_source_set_report", return_value=report):
        with patch("click.prompt", return_value=4):  # always skip
            result = run_interactive_checkup(
                str(prompt_file),
                apply=True,
                dry_run=False,
                project_root=tmp_path,
                quiet=True,
            )

    assert result is not None
    message, cost, model = result
    assert "skipped" in message
    assert "2 skipped" in message


# ---------------------------------------------------------------------------
# InteractiveRepairSession stub interface
# ---------------------------------------------------------------------------

def test_interactive_repair_session_stub() -> None:
    """InteractiveRepairSession stub exposes ask() and is iterable."""
    finding = _make_finding("SES-001")
    session = InteractiveRepairSession([finding])

    # iterable
    findings_list = list(session)
    assert len(findings_list) == 1
    assert findings_list[0].finding_id == "SES-001"

    # ask returns a string
    answer = session.ask("clarify this")
    assert isinstance(answer, str)


# ---------------------------------------------------------------------------
# CLI param registration
# ---------------------------------------------------------------------------

def test_checkup_registers_interactive_flags() -> None:
    """checkup command must have interactive, apply, and dry_run params."""
    param_names = {p.name for p in checkup.params}
    missing = {"interactive", "apply", "dry_run"} - param_names
    assert not missing, f"Missing params: {missing}"
