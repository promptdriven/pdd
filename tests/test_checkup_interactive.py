"""Tests for interactive checkup flags and interaction policy (#1436)."""

from __future__ import annotations

from pathlib import Path
from unittest.mock import patch

import pytest
from click.testing import CliRunner

from pdd.checkup_interactive_main import (
    ClickInteractiveSession,
    filter_interactive_findings,
    run_interactive_checkup,
)
from pdd.checkup_interactive_session import FakeInteractiveSession, RepairOption
from pdd.checkup_prompt_main import PromptSourceSetReport, SourceSetFinding
from pdd.commands.checkup import checkup


def _make_finding(
    finding_id: str = "F001",
    *,
    requires_clarification: bool = False,
    code: str = "",
) -> SourceSetFinding:
    return SourceSetFinding(
        finding_id=finding_id,
        source_check="lint",
        severity="warn",
        file=Path("prompts/test.prompt"),
        message="Test finding",
        evidence="some evidence",
        recommended_action="Fix the issue",
        code=code,
        requires_clarification=requires_clarification,
    )


def _make_report(
    tmp_path: Path,
    findings: list[SourceSetFinding] | None = None,
) -> PromptSourceSetReport:
    prompt_path = tmp_path / "test.prompt"
    return PromptSourceSetReport(
        prompt_path=prompt_path,
        project_root=tmp_path,
        target=str(prompt_path),
        findings=findings or [],
    )


def test_interactive_requires_tty(tmp_path: Path) -> None:
    prompt_file = tmp_path / "test.prompt"
    prompt_file.write_text("test prompt content")

    runner = CliRunner()
    result = runner.invoke(checkup, [str(prompt_file), "--interactive"])

    assert result.exit_code != 0
    assert "TTY" in result.output or "tty" in result.output.lower()


def test_apply_requires_interactive(tmp_path: Path) -> None:
    prompt_file = tmp_path / "test.prompt"
    prompt_file.write_text("test prompt content")

    runner = CliRunner()
    result = runner.invoke(checkup, [str(prompt_file), "--apply"])

    assert result.exit_code != 0
    assert "--apply requires --interactive" in result.output


def test_interactive_rejects_non_prompt_target() -> None:
    runner = CliRunner()
    with patch("pdd.commands.checkup._interactive_tty_available", return_value=True):
        result = runner.invoke(
            checkup,
            ["https://github.com/promptdriven/pdd/issues/1", "--interactive"],
        )

    assert result.exit_code != 0
    assert "prompt-shaped" in result.output


def test_filter_interactive_findings_explicit_includes_all() -> None:
    findings = [
        _make_finding("A", requires_clarification=False),
        _make_finding("B", requires_clarification=True),
    ]
    report = _make_report(Path("/tmp"), findings)

    filtered = filter_interactive_findings(report, explicit_interactive=True)

    assert len(filtered) == 2


def test_filter_interactive_findings_auto_only_clarification() -> None:
    findings = [
        _make_finding("A", requires_clarification=False),
        _make_finding("B", requires_clarification=True, code="VAGUE_TERM"),
    ]
    report = _make_report(Path("/tmp"), findings)

    filtered = filter_interactive_findings(report, explicit_interactive=False)

    assert [finding.finding_id for finding in filtered] == ["B"]


def test_dry_run_no_writes(tmp_path: Path) -> None:
    prompt_file = tmp_path / "test.prompt"
    original_content = "original prompt content"
    prompt_file.write_text(original_content)

    finding = _make_finding("DRY-001")
    report = _make_report(tmp_path, [finding])

    with patch(
        "pdd.checkup_interactive_main.build_prompt_source_set_report",
        return_value=report,
    ):
        with patch("pdd.checkup_interactive_main._prompt_menu_choice", return_value=1):
            run_interactive_checkup(
                str(prompt_file),
                apply=True,
                dry_run=True,
                project_root=tmp_path,
                quiet=True,
            )

    assert prompt_file.read_text() == original_content
    backup_files = list(tmp_path.glob("*.bak")) + list(tmp_path.glob("*.prompt.bak"))
    assert backup_files == []


def test_interactive_no_writes(tmp_path: Path) -> None:
    prompt_file = tmp_path / "test.prompt"
    original_content = "original prompt content"
    prompt_file.write_text(original_content)

    finding = _make_finding("NW-001")
    report = _make_report(tmp_path, [finding])

    with patch(
        "pdd.checkup_interactive_main.build_prompt_source_set_report",
        return_value=report,
    ):
        with patch("pdd.checkup_interactive_main._prompt_menu_choice", return_value=1):
            run_interactive_checkup(
                str(prompt_file),
                apply=False,
                dry_run=False,
                project_root=tmp_path,
                quiet=True,
            )

    assert prompt_file.read_text() == original_content
    backup_files = list(tmp_path.glob("*.bak")) + list(tmp_path.glob("*.prompt.bak"))
    assert backup_files == []


def test_skip_flow(tmp_path: Path) -> None:
    prompt_file = tmp_path / "test.prompt"
    prompt_file.write_text("prompt content")

    findings = [_make_finding("SK-001"), _make_finding("SK-002")]
    report = _make_report(tmp_path, findings)

    with patch(
        "pdd.checkup_interactive_main.build_prompt_source_set_report",
        return_value=report,
    ):
        with patch("pdd.checkup_interactive_main._prompt_menu_choice", return_value=4):
            result = run_interactive_checkup(
                str(prompt_file),
                apply=True,
                dry_run=False,
                project_root=tmp_path,
                quiet=True,
            )

    assert result is not None
    message, _cost, _model = result
    assert "skipped" in message
    assert "2 skipped" in message


def test_click_interactive_session_records_candidate_choice() -> None:
    finding = _make_finding("SES-001")
    report = _make_report(Path("/tmp"), [finding])
    session = ClickInteractiveSession()
    session.seed(report)

    options = session.present_finding("SES-001")
    assert len(options) == 2
    session.record_choice("SES-001", options[0])

    patches = session.approved_patches()
    assert len(patches) == 1
    assert patches[0].finding_id == "SES-001"


def test_checkup_registers_interactive_flags() -> None:
    param_names = {param.name for param in checkup.params}
    missing = {"interactive", "apply", "dry_run"} - param_names
    assert not missing, f"Missing params: {missing}"


def test_cli_interactive_routes_with_tty(tmp_path: Path) -> None:
    prompt_file = tmp_path / "test.prompt"
    prompt_file.write_text("prompt content")
    finding = _make_finding("CLI-001")
    report = _make_report(tmp_path, [finding])

    with patch("pdd.commands.checkup._interactive_tty_available", return_value=True):
        with patch(
            "pdd.checkup_interactive_main.build_prompt_source_set_report",
            return_value=report,
        ):
            with patch("pdd.checkup_interactive_main._prompt_menu_choice", return_value=4):
                runner = CliRunner()
                result = runner.invoke(checkup, [str(prompt_file), "--interactive"])

    assert result.exit_code == 0
    assert "Interactive checkup complete" in result.output


def test_fake_session_still_usable_via_factory(tmp_path: Path) -> None:
    from pdd.checkup_interactive_session import ApprovedPatch

    prompt_file = tmp_path / "test.prompt"
    prompt_file.write_text("prompt content")
    finding = _make_finding("FAKE-001")
    report = _make_report(tmp_path, [finding])
    repair_option = RepairOption(
        label="Fix",
        preview="preview",
        patch=ApprovedPatch(
            kind="repair_candidate",
            target=prompt_file,
            anchor={"finding_id": "FAKE-001"},
            replacement="fix",
            finding_id="FAKE-001",
        ),
    )
    fake = FakeInteractiveSession({"FAKE-001": [repair_option, repair_option]})

    with patch(
        "pdd.checkup_interactive_main.build_prompt_source_set_report",
        return_value=report,
    ):
        with patch("pdd.checkup_interactive_main._prompt_menu_choice", return_value=1):
            run_interactive_checkup(
                str(prompt_file),
                apply=False,
                project_root=tmp_path,
                quiet=True,
                session_factory=lambda: fake,
            )

    assert fake.recorded_choices == [("FAKE-001", repair_option)]
