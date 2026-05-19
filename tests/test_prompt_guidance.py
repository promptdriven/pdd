"""Unit tests for the LLM-backed prompt coaching adapter."""
from __future__ import annotations

import json
from pathlib import Path
from unittest.mock import patch

from pdd.prompt_lint import run_llm_guidance_pass

FIXTURES = Path(__file__).parent / "fixtures" / "prompt_lint"


@patch("pdd.llm_invoke.llm_invoke")
def test_run_llm_guidance_pass_parses_json_object(mock_llm):
    mock_llm.return_value = {
        "result": json.dumps({
            "summary": "Define duplicate upload.",
            "vocabulary_suggestions": [
                {
                    "term": "duplicate upload",
                    "suggestion": "duplicate upload: same tenant and SHA-256 hash",
                    "why": "Defines equality for generated code.",
                }
            ],
            "rule_rewrites": [],
            "acceptance_criteria_improvements": [],
            "formalization_notes": [],
        })
    }

    result = run_llm_guidance_pass(FIXTURES / "upload_handler_python.prompt")

    assert result["error"] == ""
    assert result["summary"] == "Define duplicate upload."
    assert result["vocabulary_suggestions"][0]["term"] == "duplicate upload"


@patch("pdd.llm_invoke.llm_invoke")
def test_run_llm_guidance_pass_parses_fenced_json(mock_llm):
    mock_llm.return_value = {
        "result": (
            "```json\n"
            "{\n"
            '  "summary": "Rewrite rules.",\n'
            '  "vocabulary_suggestions": [],\n'
            '  "rule_rewrites": [{"rule_id": "R1", "rewrite": "R1 - Upload\\nWhen ...", "why": "Compiles."}],\n'
            '  "acceptance_criteria_improvements": [],\n'
            '  "formalization_notes": []\n'
            "}\n"
            "```"
        )
    }

    result = run_llm_guidance_pass(FIXTURES / "upload_handler_python.prompt")

    assert result["error"] == ""
    assert result["summary"] == "Rewrite rules."
    assert result["rule_rewrites"][0]["rule_id"] == "R1"


@patch("pdd.llm_invoke.llm_invoke")
def test_run_llm_guidance_pass_normalizes_non_list_sections(mock_llm):
    mock_llm.return_value = {
        "result": json.dumps({
            "summary": "Normalize me.",
            "vocabulary_suggestions": {"term": "valid"},
            "rule_rewrites": "not a list",
            "acceptance_criteria_improvements": None,
            "formalization_notes": [],
        })
    }

    result = run_llm_guidance_pass(FIXTURES / "upload_handler_python.prompt")

    assert result["error"] == ""
    assert result["vocabulary_suggestions"] == []
    assert result["rule_rewrites"] == []
    assert result["acceptance_criteria_improvements"] == []


@patch("pdd.llm_invoke.llm_invoke")
def test_run_llm_guidance_pass_returns_error_payload_on_invalid_json(mock_llm):
    mock_llm.return_value = {"result": "not-json"}

    result = run_llm_guidance_pass(FIXTURES / "upload_handler_python.prompt")

    assert result["path"].endswith("upload_handler_python.prompt")
    assert result["summary"] == ""
    assert result["vocabulary_suggestions"] == []
    assert result["error"]


@patch("pdd.llm_invoke.llm_invoke")
def test_run_llm_guidance_pass_sends_prompt_content_and_baseline_terms(mock_llm):
    mock_llm.return_value = {
        "result": json.dumps({
            "summary": "",
            "vocabulary_suggestions": [],
            "rule_rewrites": [],
            "acceptance_criteria_improvements": [],
            "formalization_notes": [],
        })
    }

    run_llm_guidance_pass(FIXTURES / "upload_handler_python.prompt")

    message = mock_llm.call_args.kwargs["messages"][0]["content"]
    assert "duplicate" in message
    assert "formal verification" in message
    assert "Prompt to coach" in message
