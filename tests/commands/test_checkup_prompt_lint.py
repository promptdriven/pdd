"""CLI tests for deterministic ``pdd checkup lint``."""
from __future__ import annotations

import json
from pathlib import Path

from click.testing import CliRunner

from pdd.commands.checkup import checkup

FIXTURES = Path(__file__).parents[1] / "fixtures" / "prompt_lint"


def test_checkup_lint_clean_prompt_json() -> None:
    result = CliRunner().invoke(
        checkup,
        ["lint", "--json", str(FIXTURES / "clean.prompt")],
        obj={"quiet": True},
    )

    assert result.exit_code == 0
    payload = json.loads(result.output)
    assert payload[0]["issues"] == []


def test_checkup_lint_reports_warning() -> None:
    result = CliRunner().invoke(
        checkup,
        ["lint", "--json", str(FIXTURES / "vague_undefined.prompt")],
        obj={"quiet": True},
    )

    assert result.exit_code == 1
    assert json.loads(result.output)[0]["warn_count"] > 0


def test_checkup_lint_strict_promotes_warning_to_error() -> None:
    result = CliRunner().invoke(
        checkup,
        ["lint", "--strict", "--json", str(FIXTURES / "vague_undefined.prompt")],
        obj={"quiet": True},
    )

    assert result.exit_code == 2
    assert json.loads(result.output)[0]["error_count"] > 0
