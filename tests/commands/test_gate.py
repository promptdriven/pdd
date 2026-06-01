"""Tests for `pdd gate` waiver policy enforcement."""
from __future__ import annotations

from pathlib import Path

from click.testing import CliRunner

from pdd.commands.gate import gate_cmd


FIXTURES = Path(__file__).parents[1] / "fixtures" / "contract_check"


def test_gate_allow_waivers_passes_for_valid_fixture() -> None:
    result = CliRunner().invoke(
        gate_cmd,
        [str(FIXTURES / "waiver_valid_python.prompt"), "--allow-waivers"],
    )
    assert result.exit_code == 0, result.output


def test_gate_forbid_waivers_fails_when_any_waiver_exists() -> None:
    result = CliRunner().invoke(
        gate_cmd,
        [str(FIXTURES / "waiver_valid_python.prompt"), "--forbid-waivers"],
    )
    assert result.exit_code == 1, result.output
    assert "waivers-forbidden" in result.output


def test_gate_require_expiration_fails_missing_expiration() -> None:
    result = CliRunner().invoke(
        gate_cmd,
        [str(FIXTURES / "waiver_missing_fields_python.prompt"), "--require-expiration"],
    )
    assert result.exit_code == 1, result.output
    assert "missing-expiration" in result.output


def test_gate_enforce_expiration_fails_expired_waiver() -> None:
    result = CliRunner().invoke(
        gate_cmd,
        [str(FIXTURES / "waiver_expired_python.prompt"), "--enforce-expiration"],
    )
    assert result.exit_code == 1, result.output
    assert "expired" in result.output
