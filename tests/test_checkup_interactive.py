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
    """--interactive (with a TTY) routes to the agentic session and completes."""
    prompt_file = tmp_path / "test.prompt"
    prompt_file.write_text("prompt content")
    finding = _make_finding("CLI-001")
    report = _make_report(tmp_path, [finding])

    with patch("pdd.commands.checkup._interactive_tty_available", return_value=True):
        with patch(
            "pdd.checkup_agent.build_prompt_source_set_report",
            return_value=report,
        ):
            runner = CliRunner()
            # Accept the plan (Y), then skip the single finding group (n).
            result = runner.invoke(
                checkup,
                [str(prompt_file), "--interactive", "--project-root", str(tmp_path)],
                input="Y\nn\n",
            )

    assert result.exit_code == 0
    assert "Checkup complete" in result.output
    assert "Option A" in result.output
    assert "Option B" in result.output
    assert "Keep current / skip" in result.output
    assert "Custom fix" in result.output
    assert "View rationale/details" in result.output


def test_bare_prompt_target_stays_on_structured_path(tmp_path: Path) -> None:
    """`pdd checkup <prompt>` with no flags keeps the structured non-interactive path."""
    prompt_file = tmp_path / "test.prompt"
    prompt_file.write_text("% t\n")
    with patch("pdd.commands.checkup.run_checkup_prompt") as mock_struct, patch(
        "pdd.checkup_agent.CheckupAgent.run"
    ) as mock_agent:
        mock_struct.return_value = (True, "ok", 0.0, "", 0)
        result = CliRunner().invoke(checkup, [str(prompt_file)], catch_exceptions=False)
    mock_agent.assert_not_called()
    mock_struct.assert_called_once()
    assert result.exit_code == 0


def test_cli_accepts_dry_run_alias_for_apply(tmp_path: Path) -> None:
    prompt_file = tmp_path / "test.prompt"
    prompt_file.write_text("% t\n")
    with patch("pdd.checkup_agent.CheckupAgent.run") as mock_run:
        mock_run.return_value = ("done", 0.0, "")
        result = CliRunner().invoke(
            checkup,
            ["--auto", "--apply", "--dry-run", str(prompt_file)],
            catch_exceptions=False,
        )
    assert result.exit_code == 0
    assert mock_run.call_args.kwargs["dry_run"] is True


def test_cli_keeps_preview_alias_for_apply(tmp_path: Path) -> None:
    prompt_file = tmp_path / "test.prompt"
    prompt_file.write_text("% t\n")
    with patch("pdd.checkup_agent.CheckupAgent.run") as mock_run:
        mock_run.return_value = ("done", 0.0, "")
        result = CliRunner().invoke(
            checkup,
            ["--auto", "--apply", "--preview", str(prompt_file)],
            catch_exceptions=False,
        )
    assert result.exit_code == 0
    assert mock_run.call_args.kwargs["dry_run"] is True


def test_json_target_stays_on_structured_path(tmp_path: Path) -> None:
    """--json keeps machine output on the structured (non-agent) path."""
    prompt_file = tmp_path / "test.prompt"
    prompt_file.write_text("% t\n")
    with patch("pdd.commands.checkup.run_checkup_prompt") as mock_struct, patch(
        "pdd.checkup_agent.CheckupAgent.run"
    ) as mock_agent:
        mock_struct.return_value = (True, "ok", 0.0, "", 0)
        CliRunner().invoke(checkup, [str(prompt_file), "--json"], catch_exceptions=False)
    mock_agent.assert_not_called()
    mock_struct.assert_called_once()


def test_explain_target_stays_on_structured_path(tmp_path: Path) -> None:
    prompt_file = tmp_path / "test.prompt"
    prompt_file.write_text("% t\n")
    with patch("pdd.commands.checkup.run_checkup_prompt") as mock_struct, patch(
        "pdd.checkup_agent.CheckupAgent.run"
    ) as mock_agent:
        mock_struct.return_value = (True, "ok", 0.0, "", 0)
        CliRunner().invoke(checkup, [str(prompt_file), "--explain"], catch_exceptions=False)
    mock_agent.assert_not_called()
    mock_struct.assert_called_once()


def test_active_prompt_repair_stays_on_structured_path(tmp_path: Path) -> None:
    """When the LLM prompt-repair loop is requested, keep the structured path."""
    prompt_file = tmp_path / "test.prompt"
    prompt_file.write_text("% t\n")
    with patch("pdd.commands.checkup.run_checkup_prompt") as mock_struct, patch(
        "pdd.checkup_agent.CheckupAgent.run"
    ) as mock_agent:
        mock_struct.return_value = (True, "ok", 0.0, "", 0)
        CliRunner().invoke(
            checkup, [str(prompt_file), "--prompt-repair", "best-effort"],
            catch_exceptions=False,
        )
    mock_agent.assert_not_called()
    mock_struct.assert_called_once()


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
            kind="vocab_definition",
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


def test_relative_target_resolved_against_project_root(tmp_path: Path) -> None:
    """Path existence check must resolve relative targets against project_root (#1519 finding #4).

    pdd checkup prompts/foo.prompt --project-root=/other --interactive must find the
    file at project_root/prompts/foo.prompt, not relative to cwd.
    """
    project_root = tmp_path / "project"
    project_root.mkdir()
    prompt_file = project_root / "prompts" / "test.prompt"
    prompt_file.parent.mkdir()
    prompt_file.write_text("prompt content")

    finding = _make_finding("REL-001")
    report = _make_report(project_root, [finding])

    # Use a relative path (the file does NOT exist relative to tmp_path itself)
    relative_target = "prompts/test.prompt"

    with patch(
        "pdd.checkup_interactive_main.build_prompt_source_set_report",
        return_value=report,
    ):
        with patch("pdd.checkup_interactive_main._prompt_menu_choice", return_value=4):
            # Must NOT raise UsageError even though cwd != project_root
            result = run_interactive_checkup(
                relative_target,
                project_root=project_root,
                quiet=True,
            )

    assert result is not None
    message, _, _ = result
    assert "Interactive checkup complete" in message


def test_relative_target_missing_gives_clear_error(tmp_path: Path) -> None:
    """Missing relative target must raise UsageError with the original path in the message."""
    import click

    with pytest.raises(click.UsageError, match="nonexistent.prompt"):
        run_interactive_checkup(
            "nonexistent.prompt",
            project_root=tmp_path,
            quiet=True,
        )


def test_fake_session_skip_choice_is_recorded(tmp_path: Path) -> None:
    """Choice 4 (skip) must be recorded for FakeInteractiveSession, not silently dropped (#1519 finding #5)."""
    from pdd.checkup_interactive_session import ApprovedPatch

    prompt_file = tmp_path / "test.prompt"
    prompt_file.write_text("prompt content")
    finding = _make_finding("SKIP-FAKE-001")
    report = _make_report(tmp_path, [finding])

    fake = FakeInteractiveSession({"SKIP-FAKE-001": []})

    with patch(
        "pdd.checkup_interactive_main.build_prompt_source_set_report",
        return_value=report,
    ):
        with patch("pdd.checkup_interactive_main._prompt_menu_choice", return_value=4):
            run_interactive_checkup(
                str(prompt_file),
                apply=False,
                project_root=tmp_path,
                quiet=True,
                session_factory=lambda: fake,
            )

    assert len(fake.recorded_choices) == 1
    fid, opt = fake.recorded_choices[0]
    assert fid == "SKIP-FAKE-001"
    assert opt.patch.kind == "skip"


def test_fake_session_custom_choice_is_recorded(tmp_path: Path) -> None:
    """Choice 3 (custom definition) must be recorded for FakeInteractiveSession (#1519 finding #5)."""
    prompt_file = tmp_path / "test.prompt"
    prompt_file.write_text("prompt content")
    finding = _make_finding("CUSTOM-FAKE-001")
    report = _make_report(tmp_path, [finding])

    # FakeInteractiveSession.ask() pops from its answer queue
    fake = FakeInteractiveSession(
        options_by_finding={"CUSTOM-FAKE-001": []},
        answers=["my definition"],
    )

    with patch(
        "pdd.checkup_interactive_main.build_prompt_source_set_report",
        return_value=report,
    ):
        with patch("pdd.checkup_interactive_main._prompt_menu_choice", return_value=3):
            run_interactive_checkup(
                str(prompt_file),
                apply=False,
                project_root=tmp_path,
                quiet=True,
                session_factory=lambda: fake,
            )

    assert len(fake.recorded_choices) == 1
    fid, opt = fake.recorded_choices[0]
    assert fid == "CUSTOM-FAKE-001"
    assert opt.patch.kind == "custom_no_patch"
    assert opt.patch.replacement == "my definition"


def test_out_of_bounds_option_choice_emits_warning_and_skips(
    tmp_path: Path, capsys
) -> None:
    """Out-of-bounds option index must emit a warning and skip the finding, not silently discard (#1519 finding #6)."""
    prompt_file = tmp_path / "test.prompt"
    prompt_file.write_text("prompt content")
    finding = _make_finding("OOB-001")
    report = _make_report(tmp_path, [finding])

    # FakeInteractiveSession with ZERO options for the finding
    fake = FakeInteractiveSession({"OOB-001": []})

    with patch(
        "pdd.checkup_interactive_main.build_prompt_source_set_report",
        return_value=report,
    ):
        # Choice 1 with 0 options → out-of-bounds
        with patch("pdd.checkup_interactive_main._prompt_menu_choice", return_value=1):
            result = run_interactive_checkup(
                str(prompt_file),
                apply=False,
                project_root=tmp_path,
                quiet=True,
                session_factory=lambda: fake,
            )

    # No choice must be recorded (finding was skipped with warning)
    assert fake.recorded_choices == []
    assert result is not None
    message, _, _ = result
    assert "skipped" in message


def test_repair_patch_replacement_is_annotation_not_raw_prose(tmp_path: Path) -> None:
    """Applied patch content must be a clearly-delimited checkup annotation, not the
    raw recommended_action prose that would corrupt the prompt (#1519 prose-injection)."""
    from pdd.checkup_interactive_main import build_repair_options_for_finding

    finding = SourceSetFinding(
        finding_id="lint:test:2:STYLE_1",
        source_check="lint",
        severity="warn",
        file=Path("prompts/test.prompt"),
        line="2",
        message="Style issue",
        recommended_action="Tidy wording",
        code="STYLE_1",
    )
    options = build_repair_options_for_finding(finding, project_root=tmp_path)

    primary_replacement = options[0].patch.replacement
    # The human guidance is preserved as the menu label / preview...
    assert options[0].label == "Tidy wording"
    # ...but the *applied* content is an inert, labelled annotation, never bare prose.
    assert primary_replacement != "Tidy wording"
    assert primary_replacement.startswith("<!--")
    assert primary_replacement.endswith("-->")
    assert "STYLE_1" in primary_replacement


def test_generate_forwards_apply_to_prompt_gate() -> None:
    """`pdd generate --apply` must reach the workflow gate (choices were silently
    discarded before because apply was never forwarded) (#1519 apply-not-forwarded)."""
    from pdd.commands.generate import generate, _maybe_run_prompt_gate
    import inspect

    assert "apply" in {p.name for p in generate.params}
    # The shared gate helper must accept and forward apply.
    assert "apply" in inspect.signature(_maybe_run_prompt_gate).parameters


def test_change_forwards_apply_to_prompt_gate() -> None:
    """`pdd change --apply` must expose the flag for the workflow gate."""
    from pdd.commands.modify import change

    assert "apply" in {p.name for p in change.params}
