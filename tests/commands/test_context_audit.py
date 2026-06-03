"""Tests for the ``pdd context-audit`` command (pdd.commands.context_audit).

Covers issue #789 acceptance criteria:
- per-source token attribution (prompt body, each include, grounding)
- largest consumer first (sorted descending)
- JSON output for CI/dashboards
- no LLM call (token counting is mocked/deterministic; preprocessing is local)
- threshold exit code 2 for budget gating
- deferred warnings for nondeterministic tags (<shell>, <web>)
"""
import json

import pytest
from click.testing import CliRunner

import importlib

from pdd.commands.context_audit import context_audit

# ``pdd.commands.__init__`` binds the name ``context_audit`` to the command
# function, shadowing the submodule attribute. Fetch the real module object so
# monkeypatching ``count_tokens``/``get_context_limit`` targets module globals.
ca_module = importlib.import_module("pdd.commands.context_audit")


@pytest.fixture
def runner():
    return CliRunner()


def _word_count_tokens(text, model="gpt-4o"):
    """Deterministic stand-in for the litellm tokenizer (no network/LLM)."""
    return len(text.split())


@pytest.fixture
def patched_tokens(monkeypatch):
    """Replace token counting + context-limit lookup with deterministic stubs."""
    monkeypatch.setattr(ca_module, "count_tokens", _word_count_tokens)
    monkeypatch.setattr(ca_module, "get_context_limit", lambda model: 1000)


@pytest.fixture
def prompt_with_include(tmp_path, monkeypatch):
    """A prompt with one resolvable include, written into an isolated cwd."""
    monkeypatch.chdir(tmp_path)
    (tmp_path / "context").mkdir()
    include = tmp_path / "context" / "preamble.prompt"
    include.write_text("alpha beta gamma delta epsilon", encoding="utf-8")
    prompt = tmp_path / "module_python.prompt"
    prompt.write_text(
        "Write the module.\n<include>context/preamble.prompt</include>\nDone here.",
        encoding="utf-8",
    )
    return prompt


def test_table_attributes_per_source(runner, prompt_with_include, patched_tokens):
    result = runner.invoke(context_audit, [str(prompt_with_include)], obj={})
    assert result.exit_code == 0, result.output
    assert "Model: gpt-4o" in result.output
    assert "Context limit: 1,000 tokens" in result.output
    # Per-source rows present.
    assert "context/preamble.prompt" in result.output
    assert "prompt_body" in result.output
    # Grounding reported as unavailable, no network call.
    assert "grounding" in result.output
    assert "requires cloud" in result.output


def test_rows_sorted_descending(runner, prompt_with_include, patched_tokens):
    result = runner.invoke(
        context_audit, [str(prompt_with_include), "--json"], obj={}
    )
    assert result.exit_code == 0, result.output
    payload = json.loads(result.output)
    token_values = [row["tokens"] for row in payload["rows"]]
    assert token_values == sorted(token_values, reverse=True)


def test_json_shape_and_keys(runner, prompt_with_include, patched_tokens):
    result = runner.invoke(
        context_audit, [str(prompt_with_include), "--json"], obj={}
    )
    assert result.exit_code == 0, result.output
    payload = json.loads(result.output)
    assert set(payload.keys()) == {
        "total_tokens",
        "context_limit",
        "percent_used",
        "model",
        "rows",
        "warnings",
        "threshold_exceeded",
    }
    assert payload["context_limit"] == 1000
    assert payload["model"] == "gpt-4o"
    assert payload["threshold_exceeded"] is False
    # The include's words are attributed to its own row.
    include_row = next(
        r for r in payload["rows"] if r["source"] == "context/preamble.prompt"
    )
    assert include_row["tokens"] == 5
    for row in payload["rows"]:
        assert set(row.keys()) == {"source", "tokens", "percent"}


def test_model_option_overrides_default(runner, prompt_with_include, patched_tokens):
    result = runner.invoke(
        context_audit,
        [str(prompt_with_include), "--model", "claude-sonnet-4-6", "--json"],
        obj={},
    )
    assert result.exit_code == 0, result.output
    assert json.loads(result.output)["model"] == "claude-sonnet-4-6"


def test_threshold_exceeded_exits_2(runner, prompt_with_include, monkeypatch):
    monkeypatch.setattr(ca_module, "count_tokens", _word_count_tokens)
    # Tiny limit forces total tokens well above the default 80% threshold.
    monkeypatch.setattr(ca_module, "get_context_limit", lambda model: 10)
    result = runner.invoke(context_audit, [str(prompt_with_include)], obj={})
    assert result.exit_code == 2, result.output
    assert "context budget exceeded" in result.output


def test_threshold_exceeded_exits_2_json(runner, prompt_with_include, monkeypatch):
    monkeypatch.setattr(ca_module, "count_tokens", _word_count_tokens)
    monkeypatch.setattr(ca_module, "get_context_limit", lambda model: 10)
    result = runner.invoke(
        context_audit, [str(prompt_with_include), "--json"], obj={}
    )
    assert result.exit_code == 2
    assert json.loads(result.output)["threshold_exceeded"] is True


def test_threshold_zero_disables_check(runner, prompt_with_include, monkeypatch):
    monkeypatch.setattr(ca_module, "count_tokens", _word_count_tokens)
    monkeypatch.setattr(ca_module, "get_context_limit", lambda model: 10)
    result = runner.invoke(
        context_audit, [str(prompt_with_include), "--threshold", "0"], obj={}
    )
    assert result.exit_code == 0, result.output


def test_dynamic_tag_warning(runner, tmp_path, monkeypatch, patched_tokens):
    monkeypatch.chdir(tmp_path)
    prompt = tmp_path / "dyn_python.prompt"
    prompt.write_text(
        "Build it.\n<shell>echo hello</shell>\n<web>https://example.com</web>",
        encoding="utf-8",
    )
    result = runner.invoke(context_audit, [str(prompt), "--json"], obj={})
    assert result.exit_code == 0, result.output
    warnings = json.loads(result.output)["warnings"]
    joined = " ".join(warnings)
    assert "shell" in joined
    assert "web" in joined
    assert all("deferred" in w for w in warnings)


def test_unknown_model_limit_reported_gracefully(runner, prompt_with_include, monkeypatch):
    monkeypatch.setattr(ca_module, "count_tokens", _word_count_tokens)
    monkeypatch.setattr(ca_module, "get_context_limit", lambda model: None)
    result = runner.invoke(context_audit, [str(prompt_with_include)], obj={})
    assert result.exit_code == 0, result.output
    assert "unknown" in result.output


def test_missing_prompt_path_errors(runner):
    result = runner.invoke(context_audit, ["does_not_exist.prompt"], obj={})
    assert result.exit_code != 0
