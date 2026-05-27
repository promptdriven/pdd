"""CLI tests for deterministic ``pdd checkup contract check``."""
from __future__ import annotations

import json
import os
import subprocess
import sys
from pathlib import Path

import pytest
from click.testing import CliRunner

from pdd.commands.checkup import checkup
from pdd.commands.contracts import contracts_cli

FIXTURES = Path(__file__).parents[1] / "fixtures" / "contract_check"
REPO_ROOT = Path(__file__).parents[2]


def test_checkup_help_without_target() -> None:
    """``pdd checkup --help`` must work (contract dispatch must not break it)."""
    result = CliRunner().invoke(checkup, ["--help"], obj={"quiet": True})
    assert result.exit_code == 0
    assert "checkup" in result.output.lower()
    assert "contract" in result.output.lower()


def test_contracts_check_top_level_alias_json() -> None:
    """``pdd contracts check`` mirrors ``pdd checkup contract check``."""
    result = CliRunner().invoke(
        contracts_cli,
        ["check", "--json", str(FIXTURES / "valid_contract_python.prompt")],
        obj={"quiet": True},
    )

    assert result.exit_code == 0
    assert json.loads(result.output)[0]["issues"] == []


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


@pytest.mark.parametrize(
    ("fixture_name", "expected_exit_code"),
    [("valid_contract_python.prompt", 0), ("missing_modal_python.prompt", 1)],
)
def test_checkup_contract_check_real_cli_json_stdout_is_parseable_only(
    fixture_name: str, expected_exit_code: int
) -> None:
    env = os.environ.copy()
    env.update(
        {
            "PDD_PATH": str(REPO_ROOT / "pdd"),
            "PYTHONPATH": str(REPO_ROOT),
            "PDD_AUTO_UPDATE": "false",
        }
    )
    result = subprocess.run(
        [
            sys.executable,
            "-m",
            "pdd",
            "contracts",
            "check",
            "--json",
            str(FIXTURES / fixture_name),
        ],
        cwd=REPO_ROOT,
        env=env,
        capture_output=True,
        text=True,
        check=False,
    )

    assert result.returncode == expected_exit_code
    payload = json.loads(result.stdout)
    assert isinstance(payload, list)
