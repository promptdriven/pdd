"""CLI tests for deterministic ``pdd checkup lint``."""
from __future__ import annotations

import json
from pathlib import Path
from unittest.mock import patch

from click.testing import CliRunner

from pdd.commands.checkup import checkup
from pdd.prompt_lint import LintIssue, run_llm_ambiguity_pass

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


@patch("pdd.commands.prompt.run_llm_ambiguity_pass")
def test_checkup_lint_ambiguity_uses_cloud_by_default(mock_llm) -> None:
    mock_llm.return_value = [
        LintIssue(
            level="warn",
            code="LLM_AMBIGUITY",
            term="reliable",
            section="contract_rules",
            line="",
            message='LLM flagged "reliable" as potentially ambiguous.',
        )
    ]
    result = CliRunner().invoke(
        checkup,
        ["lint", "--ambiguity", "--json", str(FIXTURES / "clean.prompt")],
        obj={"quiet": True},
    )

    assert result.exit_code == 0
    assert json.loads(result.output)[0]["issues"][0]["code"] == "LLM_AMBIGUITY"
    assert mock_llm.call_args.kwargs["use_cloud"] is True


@patch("pdd.commands.prompt.run_llm_ambiguity_pass")
def test_checkup_lint_ambiguity_honors_local_execution(mock_llm) -> None:
    mock_llm.return_value = []
    result = CliRunner().invoke(
        checkup,
        ["lint", "--ambiguity", "--json", str(FIXTURES / "clean.prompt")],
        obj={"quiet": True, "local": True},
    )

    assert result.exit_code == 0
    assert mock_llm.call_args.kwargs["use_cloud"] is False


@patch("pdd.llm_invoke.llm_invoke")
def test_cloud_linter_parses_llm_response(mock_invoke, tmp_path: Path) -> None:
    prompt = tmp_path / "sample.prompt"
    prompt.write_text("<contract_rules>Return a reliable response.</contract_rules>\n")
    mock_invoke.return_value = {
        "result": json.dumps(
            [
                {
                    "term": "reliable",
                    "section": "contract_rules",
                    "interpretations": ["HTTP 200", "valid schema"],
                    "suggestion": "reliable: HTTP 200 with a valid response schema",
                }
            ]
        )
    }

    issues = run_llm_ambiguity_pass(prompt, use_cloud=True)

    assert issues[0].code == "LLM_AMBIGUITY"
    assert issues[0].term == "reliable"
    assert mock_invoke.call_args.kwargs["use_cloud"] is True
