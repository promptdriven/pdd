from __future__ import annotations

import pytest
from click.testing import CliRunner

from pdd.commands.checkup import checkup


def test_checkup_help_exit_code_zero() -> None:
    runner = CliRunner()
    result = runner.invoke(checkup, ["-h"])
    assert result.exit_code == 0


def test_checkup_help_prompt_section_before_agentic() -> None:
    runner = CliRunner()
    result = runner.invoke(checkup, ["-h"])
    output = result.output
    assert "Prompt source-set check" in output
    assert "checkup prompt" in output
    assert "Agentic issue / PR checkup" in output
    assert output.index("Prompt source-set check") < output.index("Agentic issue / PR checkup")


def test_checkup_help_focused_checks_before_agentic() -> None:
    runner = CliRunner()
    result = runner.invoke(checkup, ["-h"])
    output = result.output
    assert "Focused local checks" in output
    assert output.index("Focused local checks") < output.index("Agentic issue / PR checkup")


def test_checkup_help_mentions_focused_subcommands() -> None:
    runner = CliRunner()
    result = runner.invoke(checkup, ["-h"])
    output = result.output
    for subcommand in ("lint", "contract", "coverage", "gate", "snapshot", "drift"):
        assert subcommand in output, f"Expected '{subcommand}' in checkup help output"


def test_checkup_help_does_not_advertise_coach() -> None:
    runner = CliRunner()
    result = runner.invoke(checkup, ["-h"])
    assert "coach" not in result.output.lower()


def test_checkup_prompt_stub_exits_zero() -> None:
    runner = CliRunner()
    result = runner.invoke(checkup, ["prompt", "prompts/foo_python.prompt"])
    assert result.exit_code == 0
    assert "not yet implemented" in result.output
    assert "#1379" in result.output


def test_checkup_lint_unchanged_backward_compat(tmp_path) -> None:
    """Focused lint dispatch must remain first-class (not nested under prompt)."""
    prompt = tmp_path / "clean_python.prompt"
    prompt.write_text(
        "<pdd-reason>ok</pdd-reason>\n"
        "<pdd-interface>{\"type\": \"function\"}</pdd-interface>\n",
        encoding="utf-8",
    )
    runner = CliRunner()
    result = runner.invoke(
        checkup,
        ["lint", "--json", str(prompt)],
        obj={"quiet": True},
    )
    assert result.exit_code == 0, result.output
