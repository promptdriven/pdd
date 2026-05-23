"""CLI tests for `pdd contracts compile`."""
from __future__ import annotations

import json
from pathlib import Path

import pytest
from click.testing import CliRunner

from pdd import cli

FIXTURES = Path(__file__).parents[1] / "fixtures" / "contract_compile"


@pytest.fixture
def runner():
    return CliRunner()


def _invoke(runner: CliRunner, *args):
    return runner.invoke(
        cli.cli,
        ["--quiet", "contracts", "compile", *args],
        catch_exceptions=False,
    )


def _json_invoke(runner: CliRunner, *args):
    return runner.invoke(
        cli.cli,
        ["--quiet", "contracts", "compile", "--json", *args],
        catch_exceptions=False,
    )


def test_compile_clean_prompt_exits_zero(runner):
    result = _invoke(runner, str(FIXTURES / "refund_payment_python.prompt"))

    assert result.exit_code == 0
    assert "compiled" in result.output
    assert "R1" in result.output


def test_compile_uncompilable_prompt_exits_two(runner):
    result = _invoke(runner, str(FIXTURES / "uncompilable_python.prompt"))

    assert result.exit_code == 2
    assert "NO_OBSERVABLE_OBLIGATION" in result.output


def test_compile_json_is_parseable_and_has_ir_version(runner):
    result = _json_invoke(runner, str(FIXTURES / "refund_payment_python.prompt"))
    data = json.loads(result.output)

    assert result.exit_code == 0
    assert data[0]["version"] == "pdd.contract_ir.v1"
    assert data[0]["rule_count"] == 3


def test_compile_json_contains_obligations(runner):
    result = _json_invoke(runner, str(FIXTURES / "refund_payment_python.prompt"))
    data = json.loads(result.output)
    rules = {rule["id"]: rule for rule in data[0]["rules"]}

    assert any(
        obligation["type"] == "return"
        and obligation["value"]["http_status"] == 400
        for obligation in rules["R1"]["obligations"]
    )


def test_compile_json_reports_errors(runner):
    result = _json_invoke(runner, str(FIXTURES / "uncompilable_python.prompt"))
    data = json.loads(result.output)
    codes = {error["code"] for error in data[0]["compile_errors"]}

    assert result.exit_code == 2
    assert "MISSING_CONDITION" in codes


def test_compile_legacy_prompt_exits_zero(runner):
    result = _json_invoke(runner, str(FIXTURES / "legacy_no_contracts_python.prompt"))
    data = json.loads(result.output)

    assert result.exit_code == 0
    assert data[0]["has_contract_rules"] is False
    assert data[0]["rules"] == []


def test_compile_directory_outputs_all_prompts(runner):
    result = _json_invoke(runner, str(FIXTURES))
    data = json.loads(result.output)
    names = {Path(entry["path"]).name for entry in data}

    assert "refund_payment_python.prompt" in names
    assert "uncompilable_python.prompt" in names


def test_compile_directory_exit_two_when_any_prompt_has_compile_error(runner):
    result = _invoke(runner, str(FIXTURES))

    assert result.exit_code == 2
    assert "NO_OBSERVABLE_OBLIGATION" in result.output


def test_compile_help_documents_obligation_examples(runner):
    result = runner.invoke(
        cli.cli,
        ["--quiet", "contracts", "compile", "--help"],
        catch_exceptions=False,
    )

    assert result.exit_code == 0
    assert "MUST return HTTP 409" in result.output
    assert "MUST NOT call provider_client" in result.output


def test_compile_missing_target_is_usage_error(runner):
    result = runner.invoke(
        cli.cli,
        ["--quiet", "contracts", "compile", "/tmp/pdd_missing_contract.prompt"],
    )

    assert result.exit_code != 0
    assert "does not exist" in result.output


def test_checkup_contract_compile_alias(runner):
    result = runner.invoke(
        cli.cli,
        [
            "--quiet",
            "checkup",
            "contract",
            "compile",
            str(FIXTURES / "refund_payment_python.prompt"),
        ],
        catch_exceptions=False,
    )

    assert result.exit_code == 0
    assert "compiled" in result.output


def test_checkup_contracts_compile_alias(runner):
    result = runner.invoke(
        cli.cli,
        [
            "--quiet",
            "checkup",
            "contracts",
            "compile",
            str(FIXTURES / "refund_payment_python.prompt"),
        ],
        catch_exceptions=False,
    )

    assert result.exit_code == 0
    assert "compiled" in result.output
