from __future__ import annotations

import pytest
from click.testing import CliRunner

from pdd.commands.checkup import checkup


def test_checkup_help_exit_code_zero() -> None:
    runner = CliRunner()
    result = runner.invoke(checkup, ["-h"])
    assert result.exit_code == 0


def test_checkup_help_local_section_before_agentic() -> None:
    runner = CliRunner()
    result = runner.invoke(checkup, ["-h"])
    output = result.output
    assert "Local evidence & contracts" in output, "Expected 'Local evidence & contracts' in help output"
    assert "Agentic" in output, "Expected 'Agentic' in help output"
    assert output.index("Local evidence & contracts") < output.index("Agentic"), (
        "Expected 'Local evidence & contracts' to appear before 'Agentic' in help output"
    )


def test_checkup_help_mentions_all_verifier_subcommands() -> None:
    runner = CliRunner()
    result = runner.invoke(checkup, ["-h"])
    output = result.output
    for subcommand in ("lint", "contract", "coverage", "gate", "snapshot", "drift", "coach"):
        assert subcommand in output, f"Expected '{subcommand}' to appear in checkup help output"
