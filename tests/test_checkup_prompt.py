"""Tests for unified ``pdd checkup prompt`` CLI entrypoint."""
from __future__ import annotations

import json
from pathlib import Path
from unittest.mock import patch

from click.testing import CliRunner

from pdd.checkup_advisory import SKIPPED_REPORT
from pdd.commands.checkup import checkup

FIXTURES = Path(__file__).parent / "fixtures" / "prompt_lint"


def test_checkup_prompt_help_lists_json_strict_explain() -> None:
    runner = CliRunner()
    result = runner.invoke(checkup, ["prompt", "--help"])
    assert result.exit_code == 0
    assert "--json" in result.output
    assert "--strict" in result.output
    assert "--explain" in result.output


def test_checkup_prompt_not_stub() -> None:
    runner = CliRunner()
    result = runner.invoke(checkup, ["prompt", str(FIXTURES / "clean.prompt")])
    assert "not yet implemented" not in result.output
    assert "Prompt:" in result.output


def test_checkup_prompt_json_is_valid() -> None:
    runner = CliRunner()
    result = runner.invoke(
        checkup,
        ["prompt", "--json", str(FIXTURES / "clean.prompt")],
        obj={"quiet": True},
    )
    payload = json.loads(result.output)
    assert "reports" in payload
    assert "exit_code" in payload


def test_checkup_lint_accepts_review_explain() -> None:
    runner = CliRunner()
    with patch(
        "pdd.commands.prompt.advisory_for_review",
        return_value=SKIPPED_REPORT,
    ) as advisory:
        result = runner.invoke(
            checkup,
            ["lint", "--review", "explain", str(FIXTURES / "clean.prompt")],
            obj={"quiet": True, "local": True},
        )
    assert result.exit_code == 0, result.output
    advisory.assert_called_once()


def test_checkup_lint_llm_deprecation_warning() -> None:
    runner = CliRunner()
    with patch("pdd.commands.prompt.advisory_for_review", return_value=SKIPPED_REPORT):
        result = runner.invoke(
            checkup,
            ["lint", "--llm", str(FIXTURES / "clean.prompt")],
            obj={"quiet": True, "local": True},
        )
    assert "DeprecationWarning" in result.output
