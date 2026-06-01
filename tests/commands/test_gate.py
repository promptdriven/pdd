"""Tests for ``pdd checkup gate`` waiver policy enforcement."""
from __future__ import annotations

import textwrap
from pathlib import Path

import pytest
from click.testing import CliRunner

from pdd.commands.checkup import checkup
from pdd.commands.gate import gate_cmd

FIXTURES = Path(__file__).parents[1] / "fixtures" / "contract_check"


def _invoke_checkup_gate(*args: str):
    return CliRunner().invoke(
        checkup,
        ["gate", *args],
        obj={"quiet": True},
    )


def _write_prompt(tmp_path: Path, name: str, content: str) -> Path:
    path = tmp_path / name
    path.write_text(textwrap.dedent(content), encoding="utf-8")
    return path


def test_top_level_pdd_gate_is_not_registered() -> None:
    from pdd.core.cli import cli  # pylint: disable=import-outside-toplevel

    assert "gate" not in cli.commands
    result = CliRunner().invoke(cli, ["gate"], obj={"quiet": True})
    assert result.exit_code != 0
    assert "No such command" in result.output


def test_checkup_gate_help() -> None:
    result = CliRunner().invoke(checkup, ["gate", "--help"], obj={"quiet": True})
    assert result.exit_code == 0
    assert "Validate waiver policy" in result.output


def test_checkup_gate_allow_waivers_passes_for_valid_fixture() -> None:
    result = _invoke_checkup_gate(
        str(FIXTURES / "waiver_valid_python.prompt"),
        "--allow-waivers",
    )
    assert result.exit_code == 0, result.output


def test_checkup_gate_forbid_waivers_fails_when_any_waiver_exists() -> None:
    result = _invoke_checkup_gate(
        str(FIXTURES / "waiver_valid_python.prompt"),
        "--forbid-waivers",
    )
    assert result.exit_code == 1, result.output
    assert "waivers-forbidden" in result.output


def test_checkup_gate_no_allow_waivers_fails_when_any_waiver_exists() -> None:
    result = _invoke_checkup_gate(
        str(FIXTURES / "waiver_valid_python.prompt"),
        "--no-allow-waivers",
    )
    assert result.exit_code == 1, result.output
    assert "waivers-forbidden" in result.output


def test_checkup_gate_require_expiration_fails_missing_expiration() -> None:
    result = _invoke_checkup_gate(
        str(FIXTURES / "waiver_missing_fields_python.prompt"),
        "--require-expiration",
    )
    assert result.exit_code == 1, result.output
    assert "missing-expiration" in result.output


def test_checkup_gate_enforce_expiration_fails_expired_waiver() -> None:
    result = _invoke_checkup_gate(
        str(FIXTURES / "waiver_expired_python.prompt"),
        "--enforce-expiration",
    )
    assert result.exit_code == 1, result.output
    assert "expired" in result.output


def test_checkup_gate_fails_unknown_rule_waiver(tmp_path: Path) -> None:
    prompt = _write_prompt(
        tmp_path,
        "unknown_rule_python.prompt",
        """
        <contract_rules>
        R1: The system MUST validate input.
        </contract_rules>
        <coverage>
        - R1: WAIVED W1
        </coverage>
        <waivers>
        W1:
          Rule: R99
          Reason: Temporary gap.
          Approved by: security-review
          Expires: 2099-06-01
        </waivers>
        """,
    )
    result = _invoke_checkup_gate(str(prompt))
    assert result.exit_code == 1, result.output
    assert "unknown-rule" in result.output


def test_checkup_gate_fails_malformed_waiver(tmp_path: Path) -> None:
    prompt = _write_prompt(
        tmp_path,
        "malformed_waiver_python.prompt",
        """
        <contract_rules>
        R1: The system MUST validate input.
        </contract_rules>
        <coverage>
        - R1: WAIVED W1
        </coverage>
        <waivers>
        W1:
          Rule: R1
          Reason: Missing approver and expiry.
        </waivers>
        """,
    )
    result = _invoke_checkup_gate(str(prompt))
    assert result.exit_code == 1, result.output
    assert "malformed" in result.output


def test_explicit_policy_file_missing_fails_closed(tmp_path: Path) -> None:
    missing = tmp_path / "missing-policy.yaml"
    result = CliRunner().invoke(
        gate_cmd,
        [
            str(FIXTURES / "waiver_valid_python.prompt"),
            "--policy-file",
            str(missing),
        ],
        obj={"quiet": True},
    )
    assert result.exit_code != 0
    assert "Policy file not found" in result.output


def test_explicit_policy_file_without_gate_section_fails_closed(tmp_path: Path) -> None:
    policy = tmp_path / "policy.yaml"
    policy.write_text("version: '1.0'\n", encoding="utf-8")
    result = CliRunner().invoke(
        gate_cmd,
        [
            str(FIXTURES / "waiver_valid_python.prompt"),
            "--policy-file",
            str(policy),
        ],
        obj={"quiet": True},
    )
    assert result.exit_code != 0
    assert "no top-level `gate:` mapping" in result.output
