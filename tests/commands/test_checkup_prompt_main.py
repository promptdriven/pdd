"""Tests for ``pdd checkup prompt`` orchestration and CLI."""
from __future__ import annotations

import sys
from pathlib import Path
from unittest.mock import patch

import pytest
from click.testing import CliRunner

from pdd.checkup_prompt_main import (
    PatchProposal,
    build_prompt_source_set_report,
    resolve_prompt_target,
    run_checkup_prompt,
    _interactive_apply_patches,
    _is_eligible_write_path,
    _run_explain_advisory,
)
from pdd.commands.checkup import checkup
from pdd.commands.checkup_prompt import checkup_prompt_cmd

FIXTURES = Path(__file__).parent.parent / "fixtures"
PAYMENT_PROMPT = FIXTURES / "prompt_lint" / "payment_api_python.prompt"
CLEAN_PROMPT = FIXTURES / "prompt_lint" / "clean.prompt"
REPO_ROOT = Path(__file__).parents[2]


class TestResolvePromptTarget:
    def test_resolve_by_path(self) -> None:
        path = resolve_prompt_target(str(PAYMENT_PROMPT), REPO_ROOT)
        assert path == PAYMENT_PROMPT.resolve()

    def test_resolve_missing_raises(self) -> None:
        with pytest.raises(Exception) as exc:
            resolve_prompt_target("no_such_module_xyz", REPO_ROOT)
        assert "Could not resolve" in str(exc.value)


class TestDeterministicReport:
    def test_build_report_finds_lint_issues(self) -> None:
        report = build_prompt_source_set_report(PAYMENT_PROMPT, project_root=REPO_ROOT)
        assert report.lint is not None
        assert report.findings
        lint_ids = [f for f in report.findings if f.engine == "lint"]
        assert lint_ids

    def test_build_report_includes_contract_engine(self) -> None:
        report = build_prompt_source_set_report(PAYMENT_PROMPT, project_root=REPO_ROOT)
        contract_findings = [f for f in report.findings if f.engine == "contract"]
        assert contract_findings

    def test_clean_prompt_passes_lint_errors(self) -> None:
        report = build_prompt_source_set_report(CLEAN_PROMPT, project_root=REPO_ROOT)
        lint_errors = [
            f for f in report.findings if f.engine == "lint" and f.level == "error"
        ]
        assert not lint_errors


class TestRunCheckupPrompt:
    def test_check_only_returns_stage1_pass(self) -> None:
        success, message, cost, model = run_checkup_prompt(
            str(PAYMENT_PROMPT),
            explain=False,
            interactive=False,
            apply=False,
            quiet=True,
            project_root=REPO_ROOT,
        )
        assert isinstance(success, bool)
        assert "Prompt source-set check" in message
        assert cost == 0.0
        assert model == ""

    def test_explain_non_fatal_on_llm_failure(self) -> None:
        report = build_prompt_source_set_report(PAYMENT_PROMPT, project_root=REPO_ROOT)
        stage1_pass = report.passed
        with patch(
            "pdd.llm_invoke.llm_invoke",
            side_effect=RuntimeError("no api"),
        ):
            text, cost, model = _run_explain_advisory(
                report, quiet=True, use_cloud=False
            )
            assert text == ""
            assert cost == 0.0
            assert model == ""
            with patch(
                "pdd.checkup_prompt_main._run_explain_advisory",
                return_value=("", 0.0, ""),
            ):
                success, _, _, _ = run_checkup_prompt(
                    str(PAYMENT_PROMPT),
                    explain=True,
                    interactive=False,
                    apply=False,
                    quiet=True,
                    project_root=REPO_ROOT,
                )
        assert success == stage1_pass

    def test_explain_does_not_change_exit_outcome(self) -> None:
        with patch("pdd.checkup_prompt_main._run_explain_advisory") as explain:
            explain.return_value = ("advisory", 0.01, "test-model")
            fail_success, _, _, _ = run_checkup_prompt(
                str(PAYMENT_PROMPT),
                explain=True,
                quiet=True,
                project_root=REPO_ROOT,
            )
        without_explain, _, _, _ = run_checkup_prompt(
            str(PAYMENT_PROMPT),
            explain=False,
            quiet=True,
            project_root=REPO_ROOT,
        )
        assert fail_success == without_explain


class TestAuthorityModel:
    def test_apply_requires_interactive(self) -> None:
        runner = CliRunner()
        result = runner.invoke(
            checkup_prompt_cmd,
            [str(PAYMENT_PROMPT), "--apply"],
            obj={"quiet": True},
        )
        assert result.exit_code == 2
        assert "--apply requires --interactive" in result.output

    def test_interactive_requires_tty(self, monkeypatch: pytest.MonkeyPatch) -> None:
        monkeypatch.setattr(sys.stdin, "isatty", lambda: False)
        runner = CliRunner()
        result = runner.invoke(
            checkup_prompt_cmd,
            [str(PAYMENT_PROMPT), "--interactive"],
            obj={"quiet": True},
        )
        assert result.exit_code == 2
        assert "--interactive requires a TTY" in result.output


class TestCheckupDispatch:
    def test_checkup_parent_help_lists_prompt_utility(self) -> None:
        runner = CliRunner()
        result = runner.invoke(checkup, ["--help"], obj={"quiet": True})
        assert result.exit_code == 0
        assert "pdd checkup prompt" in result.output

    def test_checkup_prompt_help(self) -> None:
        runner = CliRunner()
        result = runner.invoke(
            checkup,
            ["prompt", "--help"],
            obj={"quiet": True},
        )
        assert result.exit_code == 0
        assert "--explain" in result.output
        assert "coach" not in result.output.lower()

    def test_checkup_prompt_runs(self) -> None:
        runner = CliRunner()
        result = runner.invoke(
            checkup,
            ["prompt", str(PAYMENT_PROMPT)],
            obj={"quiet": False, "verbose": False},
        )
        assert result.exit_code in {0, 1}
        assert "Status:" in result.output
        assert "Prompt source-set check" in result.output


class TestApplyGuards:
    def test_eligible_paths(self, tmp_path: Path) -> None:
        prompt = tmp_path / "prompts" / "foo_python.prompt"
        prompt.parent.mkdir(parents=True)
        prompt.write_text("x", encoding="utf-8")
        story = tmp_path / "user_stories" / "story__foo.md"
        story.parent.mkdir(parents=True)
        story.write_text("y", encoding="utf-8")
        assert _is_eligible_write_path(prompt, tmp_path)
        assert _is_eligible_write_path(story, tmp_path)
        assert not _is_eligible_write_path(tmp_path / "src" / "main.py", tmp_path)

    def test_postflight_reruns_after_apply(self) -> None:
        proposal = PatchProposal(
            path=PAYMENT_PROMPT,
            new_content=PAYMENT_PROMPT.read_text(encoding="utf-8"),
            reason="noop",
        )
        with patch(
            "pdd.checkup_prompt_main._suggest_apply_patches",
            return_value=([proposal], 0.0, ""),
        ), patch(
            "pdd.checkup_prompt_main._interactive_apply_patches",
            return_value=1,
        ), patch(
            "pdd.checkup_prompt_main.build_prompt_source_set_report"
        ) as build_report:
            first = build_prompt_source_set_report(PAYMENT_PROMPT, project_root=REPO_ROOT)
            second = build_prompt_source_set_report(PAYMENT_PROMPT, project_root=REPO_ROOT)
            build_report.side_effect = [first, second]
            run_checkup_prompt(
                str(PAYMENT_PROMPT),
                interactive=True,
                apply=True,
                quiet=True,
                project_root=REPO_ROOT,
            )
        assert build_report.call_count == 2

    def test_interactive_apply_writes_on_yes(self, tmp_path: Path) -> None:
        target = tmp_path / "user_stories" / "story__demo.md"
        target.parent.mkdir(parents=True)
        target.write_text("before\n", encoding="utf-8")
        proposals = [
            PatchProposal(path=target, new_content="after\n", reason="demo"),
        ]
        with patch("pdd.checkup_prompt_main.click.prompt", return_value="y"):
            applied = _interactive_apply_patches(proposals, quiet=True)
        assert applied == 1
        assert target.read_text(encoding="utf-8") == "after\n"
