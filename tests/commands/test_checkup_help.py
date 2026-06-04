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
    assert "Unified prompt-space health" in output or "checkup prompt" in output
    assert "Agentic" in output or "GitHub" in output


def test_checkup_help_focused_checks_before_agentic() -> None:
    runner = CliRunner()
    result = runner.invoke(checkup, ["-h"])
    output = result.output
    assert "checkup lint" in output
    assert "GitHub" in output or "agentic" in output.lower()


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


def test_checkup_prompt_help_renders() -> None:
    runner = CliRunner()
    result = runner.invoke(checkup, ["prompt", "--help"])
    assert result.exit_code == 0
    assert "--json" in result.output
    assert "--strict" in result.output
    assert "--explain" in result.output


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
