"""CLI tests for deterministic ``pdd checkup contract check``."""
from __future__ import annotations

import json
from pathlib import Path

from click.testing import CliRunner

from pdd.commands.checkup import checkup

FIXTURES = Path(__file__).parents[1] / "fixtures" / "contract_check"


def test_checkup_contract_check_valid_prompt_json() -> None:
    result = CliRunner().invoke(
        checkup,
        ["contract", "check", "--json", str(FIXTURES / "valid_contract_python.prompt")],
        obj={"quiet": True},
    )

    assert result.exit_code == 0
    assert json.loads(result.output)[0]["issues"] == []


def test_checkup_contract_check_reports_defect() -> None:
    result = CliRunner().invoke(
        checkup,
        ["contract", "check", "--json", str(FIXTURES / "missing_modal_python.prompt")],
        obj={"quiet": True},
    )

    assert result.exit_code != 0
    codes = {issue["code"] for issue in json.loads(result.output)[0]["issues"]}
    assert "MISSING_MODAL" in codes


def test_checkup_contract_check_strict_is_forwarded() -> None:
    result = CliRunner().invoke(
        checkup,
        [
            "contract",
            "check",
            "--strict",
            "--json",
            str(FIXTURES / "non_sequential_ids_python.prompt"),
        ],
        obj={"quiet": True},
    )

    assert result.exit_code == 2
