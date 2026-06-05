from __future__ import annotations

import json
from pathlib import Path
from unittest.mock import patch

import pytest
from click.testing import CliRunner

from pdd.checkup_prompt_main import build_prompt_source_set_report, run_checkup_prompt
from pdd.commands.checkup import checkup


FIXTURES = Path(__file__).resolve().parent / "fixtures" / "prompt_lint"


def test_build_prompt_source_set_report_clean_fixture() -> None:
    prompt = FIXTURES / "clean.prompt"
    report = build_prompt_source_set_report(
        prompt,
        target=str(prompt),
        project_root=FIXTURES,
    )
    assert report.lint is not None
    assert report.lint.error_count == 0
    assert report.deterministic_exit_code() in {0, 1}


def test_run_checkup_prompt_json_schema() -> None:
    prompt = FIXTURES / "clean.prompt"
    runner = CliRunner()
    result = runner.invoke(
        checkup,
        [str(prompt), "--json"],
        obj={"quiet": True},
    )
    assert result.exit_code in {0, 1}
    payload = json.loads(result.output)
    assert payload["schema"] == "pdd.prompt_source_set_report.v1"
    assert payload["deterministic_exit_code"] in {0, 1}
    assert payload["reports"][0]["schema"] == "pdd.prompt_source_set_report.v1"


def test_run_checkup_prompt_strict_exit_on_warnings() -> None:
    prompt = FIXTURES / "vague_undefined.prompt"
    passed, _message, _cost, _model, exit_code = run_checkup_prompt(
        str(prompt),
        strict=True,
        quiet=True,
        project_root=FIXTURES,
    )
    assert not passed
    assert exit_code == 2


def test_build_prompt_source_set_report_records_contract_under_strict() -> None:
    prompt = FIXTURES / "vague_undefined.prompt"
    report = build_prompt_source_set_report(
        prompt,
        target=str(prompt),
        project_root=FIXTURES,
        strict=True,
    )
    contract_checks = [item for item in report.checks if item["name"] == "contract"]
    assert contract_checks == [{"name": "contract", "status": "fail"}]


def test_run_checkup_prompt_json_includes_contract_check_under_strict() -> None:
    prompt = FIXTURES / "vague_undefined.prompt"
    runner = CliRunner()
    result = runner.invoke(
        checkup,
        [str(prompt), "--strict", "--json"],
        obj={"quiet": True},
    )
    assert result.exit_code == 2
    payload = json.loads(result.output)
    contract_checks = [
        item
        for item in payload["reports"][0]["checks"]
        if item["name"] == "contract"
    ]
    assert contract_checks == [{"name": "contract", "status": "fail"}]


def test_checkup_issue_url_still_uses_agentic_path() -> None:
    runner = CliRunner()
    with patch("pdd.commands.checkup.run_agentic_checkup") as run_checkup:
        run_checkup.return_value = (True, "ok", 0.0, "codex")
        result = runner.invoke(
            checkup,
            ["https://github.com/org/repo/issues/123"],
            obj={"quiet": True},
        )
    assert result.exit_code == 0
    run_checkup.assert_called_once()
