"""Tests for the ``pdd context`` command (pdd.commands.context).

These tests are derived from the user story
``user_stories/story__context.md`` (issue-derived; issue #789 plus the PR #1387
intentional change). Each test names the story Acceptance Criterion (AC) or
Change requirement (CH) it encodes. Because the story is authored from the issue
and is independent of ``commands/context_python.prompt``, these tests fail if the
prompt regresses away from the issue's intent — for example dropping per-source
attribution, removing the default ``/context``-style usage box, or introducing an
LLM call.

Story coverage:
- AC1: total tokens + percent of context window, shown in the usage box.
- AC2: per-source breakdown (prompt body + each include).
- AC3: largest token consumer first.
- AC4: JSON output; threshold exit-code gating.
- AC5: no LLM call for the deterministic audit.
- AC6: deferred warnings for nondeterministic tags.
- CH1: default output is the ``/context``-style box; ``--table`` is the raw table.
"""
import importlib
import json

import pytest
from click.testing import CliRunner

from pdd.commands.context import context

# ``pdd.commands.__init__`` binds the name ``context`` to the command function,
# shadowing the submodule attribute. Fetch the real module object so
# monkeypatching ``count_tokens``/``get_context_limit`` targets module globals.
cx_module = importlib.import_module("pdd.commands.context")


@pytest.fixture
def runner():
    return CliRunner()


def _word_count_tokens(text, model="gpt-4o"):
    """Deterministic stand-in for the litellm tokenizer (no network/LLM)."""
    return len(text.split())


@pytest.fixture
def patched_tokens(monkeypatch):
    """Replace token counting + context-limit lookup with deterministic stubs."""
    monkeypatch.setattr(cx_module, "count_tokens", _word_count_tokens)
    monkeypatch.setattr(cx_module, "get_context_limit", lambda model: 1000)


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


def test_default_output_is_context_usage_box(runner, prompt_with_include, patched_tokens):
    """AC1 + CH1: the default (no-flag) output is a Claude-Code /context-style
    usage box naming the model and total/limit/percent, not the raw table."""
    result = runner.invoke(context, [str(prompt_with_include)], obj={})
    assert result.exit_code == 0, result.output
    assert "Context Usage" in result.output
    assert "gpt-4o" in result.output
    assert "Estimated usage by category" in result.output
    # total/limit (percent%) summary line is present.
    assert "/1,000 tokens (" in result.output
    assert "Free space" in result.output
    # It is the box, NOT the attribution table.
    assert "% of total" not in result.output


def test_box_breaks_down_per_source(runner, prompt_with_include, patched_tokens):
    """AC2: usage box lists each source (prompt body + each include), not just
    an aggregate total."""
    result = runner.invoke(context, [str(prompt_with_include)], obj={})
    assert result.exit_code == 0, result.output
    assert "context/preamble.prompt" in result.output
    assert "prompt_body" in result.output
    # Grounding reported as unavailable, no network call (AC5).
    assert "grounding" in result.output
    assert "requires cloud" in result.output


def test_table_flag_shows_sorted_attribution_table(runner, prompt_with_include, patched_tokens):
    """AC2 + AC3 + CH1: --table renders the per-source attribution table with
    rows ordered largest-token-consumer first."""
    result = runner.invoke(context, [str(prompt_with_include), "--table"], obj={})
    assert result.exit_code == 0, result.output
    assert "Model: gpt-4o" in result.output
    assert "Context limit: 1,000 tokens" in result.output
    assert "% of total" in result.output
    assert "context/preamble.prompt" in result.output
    # Rows are sorted descending: the include row (5 tokens) must appear before
    # the grounding row (0 tokens) in the table body.
    body = result.output
    assert body.index("context/preamble.prompt") < body.index("grounding")
    # The box header must NOT appear in table mode.
    assert "Estimated usage by category" not in result.output


def test_json_rows_sorted_descending(runner, prompt_with_include, patched_tokens):
    """AC3: JSON rows are sorted by tokens descending."""
    result = runner.invoke(context, [str(prompt_with_include), "--json"], obj={})
    assert result.exit_code == 0, result.output
    payload = json.loads(result.output)
    token_values = [row["tokens"] for row in payload["rows"]]
    assert token_values == sorted(token_values, reverse=True)


def test_json_shape_and_keys(runner, prompt_with_include, patched_tokens):
    """AC4: JSON output exposes exactly the documented keys for CI/dashboards."""
    result = runner.invoke(context, [str(prompt_with_include), "--json"], obj={})
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
    # The include's words are attributed to its own row (per-source, AC2).
    include_row = next(
        r for r in payload["rows"] if r["source"] == "context/preamble.prompt"
    )
    assert include_row["tokens"] == 5
    for row in payload["rows"]:
        assert set(row.keys()) == {"source", "tokens", "percent"}


def test_model_option_overrides_default(runner, prompt_with_include, patched_tokens):
    """AC1: --model selects the model whose context window is reported."""
    result = runner.invoke(
        context,
        [str(prompt_with_include), "--model", "claude-sonnet-4-6", "--json"],
        obj={},
    )
    assert result.exit_code == 0, result.output
    assert json.loads(result.output)["model"] == "claude-sonnet-4-6"


def test_threshold_exceeded_exits_2_box(runner, prompt_with_include, monkeypatch):
    """AC4: exceeding the budget threshold exits with code 2 (box mode)."""
    monkeypatch.setattr(cx_module, "count_tokens", _word_count_tokens)
    # Tiny limit forces total tokens well above the default 80% threshold.
    monkeypatch.setattr(cx_module, "get_context_limit", lambda model: 10)
    result = runner.invoke(context, [str(prompt_with_include)], obj={})
    assert result.exit_code == 2, result.output
    assert "context budget exceeded" in result.output


def test_threshold_exceeded_exits_2_json(runner, prompt_with_include, monkeypatch):
    """AC4: exceeding the budget threshold sets threshold_exceeded and exits 2."""
    monkeypatch.setattr(cx_module, "count_tokens", _word_count_tokens)
    monkeypatch.setattr(cx_module, "get_context_limit", lambda model: 10)
    result = runner.invoke(context, [str(prompt_with_include), "--json"], obj={})
    assert result.exit_code == 2
    assert json.loads(result.output)["threshold_exceeded"] is True


def test_threshold_zero_disables_check(runner, prompt_with_include, monkeypatch):
    """AC4: --threshold 0 disables the budget check."""
    monkeypatch.setattr(cx_module, "count_tokens", _word_count_tokens)
    monkeypatch.setattr(cx_module, "get_context_limit", lambda model: 10)
    result = runner.invoke(
        context, [str(prompt_with_include), "--threshold", "0"], obj={}
    )
    assert result.exit_code == 0, result.output


def test_dynamic_tag_warning_without_llm_call(runner, tmp_path, monkeypatch, patched_tokens):
    """AC5 + AC6: unexpanded <shell>/<web> tags produce deferred warnings and the
    audit makes no LLM call. We assert the latter by making any llm_invoke raise;
    the deterministic audit must still succeed."""
    monkeypatch.chdir(tmp_path)

    import pdd.llm_invoke as llm_module

    def _boom(*_args, **_kwargs):
        raise AssertionError("context audit must not make an LLM call")

    monkeypatch.setattr(llm_module, "llm_invoke", _boom)

    prompt = tmp_path / "dyn_python.prompt"
    prompt.write_text(
        "Build it.\n<shell>echo hello</shell>\n<web>https://example.com</web>",
        encoding="utf-8",
    )
    result = runner.invoke(context, [str(prompt), "--json"], obj={})
    assert result.exit_code == 0, result.output
    warnings = json.loads(result.output)["warnings"]
    joined = " ".join(warnings)
    assert "shell" in joined
    assert "web" in joined
    assert all("deferred" in w for w in warnings)


def test_unknown_model_limit_reported_gracefully(runner, prompt_with_include, monkeypatch):
    """AC1: when the model context limit is unknown, the box still renders and
    says so instead of crashing."""
    monkeypatch.setattr(cx_module, "count_tokens", _word_count_tokens)
    monkeypatch.setattr(cx_module, "get_context_limit", lambda model: None)
    result = runner.invoke(context, [str(prompt_with_include)], obj={})
    assert result.exit_code == 0, result.output
    assert "context limit unknown" in result.output


def test_missing_prompt_path_errors(runner):
    """A non-existent prompt path is a usage error (no audit performed)."""
    result = runner.invoke(context, ["does_not_exist.prompt"], obj={})
    assert result.exit_code != 0
