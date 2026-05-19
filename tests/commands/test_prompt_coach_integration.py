"""Integration-style tests for lint --ambiguity with LLM mocked."""
from __future__ import annotations

import json
from pathlib import Path
from unittest.mock import patch

import pytest
from click.testing import CliRunner

from pdd import cli

FIXTURES = Path(__file__).parents[1] / "fixtures" / "prompt_lint"


@pytest.fixture
def runner():
    return CliRunner()


@patch("pdd.llm_invoke.llm_invoke")
def test_lint_ambiguity_json_runs_detection_then_template_and_engine(mock_llm, runner):
    mock_llm.side_effect = [
        {
            "result": json.dumps([
                {
                    "term": "duplicate upload",
                    "section": "contract_rules",
                    "interpretations": [
                        "Same filename",
                        "Same tenant plus normalized file hash",
                    ],
                    "suggestion": (
                        "duplicate upload: an upload with the same tenant ID "
                        "and normalized file hash"
                    ),
                }
            ])
        },
        {
            "result": json.dumps({
                "summary": "Prompt can be made more formalizable.",
                "vocabulary_suggestions": [
                    {
                        "term": "valid upload",
                        "suggestion": "valid upload: PNG or JPEG at most 10 MB",
                        "why": "Gives tests a deterministic oracle.",
                    }
                ],
                "rule_rewrites": [
                    {
                        "rule_id": "R1",
                        "finding": "Valid is undefined.",
                        "rewrite": "R1 - Valid upload\nWhen ...",
                        "why": "Adds a compile-friendly condition.",
                    }
                ],
                "acceptance_criteria_improvements": [],
                "formalization_notes": [],
            })
        },
    ]

    result = runner.invoke(
        cli.cli,
        [
            "--quiet",
            "prompt",
            "lint",
            "--ambiguity",
            "--json",
            str(FIXTURES / "upload_handler_python.prompt"),
        ],
        catch_exceptions=False,
    )
    data = json.loads(result.output)
    guidance = data["guidance"][0]

    assert result.exit_code == 0
    assert guidance["summary"] == "Prompt can be made more formalizable."
    assert guidance["ambiguities"][0]["term"] == "duplicate upload"
    assert guidance["vocabulary_suggestions"][0]["term"] == "valid upload"
    assert mock_llm.call_count == 2
    detection_message = mock_llm.call_args_list[0].kwargs["messages"][0]["content"]
    guidance_message = mock_llm.call_args_list[1].kwargs["messages"][0]["content"]
    assert "Prompt to analyse" in detection_message
    assert "Prompt to coach" in guidance_message


@patch("pdd.llm_invoke.llm_invoke")
def test_lint_ambiguity_skips_guidance_when_detection_fails(mock_llm, runner):
    mock_llm.side_effect = RuntimeError("provider unavailable")

    result = runner.invoke(
        cli.cli,
        [
            "--quiet",
            "prompt",
            "lint",
            "--ambiguity",
            str(FIXTURES / "upload_handler_python.prompt"),
        ],
        catch_exceptions=False,
    )

    assert result.exit_code == 0
    assert "No LLM-detected ambiguities to clarify" in result.output
    assert mock_llm.call_count == 1


def test_removed_prompt_coach_command(runner):
    result = runner.invoke(
        cli.cli,
        ["--quiet", "prompt", "coach", str(FIXTURES / "clean.prompt")],
    )
    assert result.exit_code != 0


def test_removed_prompt_clarify_command(runner):
    result = runner.invoke(
        cli.cli,
        ["--quiet", "prompt", "clarify", str(FIXTURES / "clean.prompt")],
    )
    assert result.exit_code != 0
