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

from pdd.cli import cli
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
    """Replace token counting + context-limit lookup with deterministic stubs.

    Also clears ``PDD_MODEL_DEFAULT`` so tests that assert the built-in default
    model (``gpt-4o``) are not sensitive to the developer's ambient environment
    (the repo's ``pdd`` env sets it). Tests that exercise the env default set it
    explicitly instead.
    """
    monkeypatch.delenv("PDD_MODEL_DEFAULT", raising=False)
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


def test_cli_json_output_is_machine_readable_without_summary(
    runner, prompt_with_include, patched_tokens
):
    """AC4: through the real CLI, --json stdout is only the JSON payload so
    dashboards can parse it; the global execution summary is suppressed."""
    result = runner.invoke(cli, ["context", str(prompt_with_include), "--json"])
    assert result.exit_code == 0, result.output
    payload = json.loads(result.output)
    assert payload["model"] == "gpt-4o"
    assert "--- Command Execution Summary ---" not in result.output
    assert "Debug snapshot saved" not in result.output


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


# --------------------------------------------------------------------------- #
# Attribution must match the *hydrated* payload, not whole-file recounts.      #
# (issue #789 review #1 — lines=, select=, include-many, nested includes.)     #
# --------------------------------------------------------------------------- #


def _rows(runner, prompt):
    return json.loads(runner.invoke(context, [str(prompt), "--json"], obj={}).output)["rows"]


def test_lines_selector_attributes_only_selected_slice(runner, tmp_path, monkeypatch, patched_tokens):
    """review #1: an include with lines= must attribute only the selected lines,
    not the entire file (the old code reported the whole file, yielding >100%)."""
    monkeypatch.chdir(tmp_path)
    (tmp_path / "context").mkdir()
    # 5 lines, 11 words total; lines 1-2 are 5 words.
    (tmp_path / "context" / "big.txt").write_text(
        "l1 a b\nl2 c\nl3 d\nl4 e\nl5 f", encoding="utf-8"
    )
    prompt = tmp_path / "p_python.prompt"
    prompt.write_text(
        'Body text\n<include lines="1-2">context/big.txt</include>', encoding="utf-8"
    )
    include_row = next(r for r in _rows(runner, prompt) if "big.txt" in r["source"])
    assert include_row["tokens"] == 5  # the selected slice, not the whole 11-word file
    assert include_row["percent"] <= 100.0


def test_select_selector_attributes_only_selected_symbol(runner, tmp_path, monkeypatch, patched_tokens):
    """review #1: an include with select=def:NAME attributes only that symbol."""
    monkeypatch.chdir(tmp_path)
    (tmp_path / "context").mkdir()
    (tmp_path / "context" / "mod.py").write_text(
        "def foo():\n    return 1\n\ndef bar():\n    return 2\n", encoding="utf-8"
    )
    prompt = tmp_path / "p_python.prompt"
    prompt.write_text(
        'Body\n<include select="def:foo">context/mod.py</include>', encoding="utf-8"
    )
    include_row = next(r for r in _rows(runner, prompt) if "mod.py" in r["source"])
    # Only `def foo(): return 1` (4 words), not both functions (8 words).
    assert include_row["tokens"] == 4


def test_include_many_attributes_each_listed_file(runner, tmp_path, monkeypatch, patched_tokens):
    """review #1: a literal <include-many> attributes each file's real content."""
    monkeypatch.chdir(tmp_path)
    (tmp_path / "context").mkdir()
    (tmp_path / "context" / "a.txt").write_text("aa bb", encoding="utf-8")
    (tmp_path / "context" / "b.txt").write_text("cc dd ee", encoding="utf-8")
    prompt = tmp_path / "p_python.prompt"
    prompt.write_text(
        "Body here\n<include-many>context/a.txt, context/b.txt</include-many>",
        encoding="utf-8",
    )
    rows = _rows(runner, prompt)
    by_source = {r["source"]: r["tokens"] for r in rows}
    assert by_source.get("context/a.txt") == 2
    assert by_source.get("context/b.txt") == 3


def test_nested_include_rolls_up_into_top_level_parent(runner, tmp_path, monkeypatch, patched_tokens):
    """review #1: a nested include is counted once, rolled into the top-level
    include the user wrote (not double-counted as its own row)."""
    monkeypatch.chdir(tmp_path)
    (tmp_path / "context").mkdir()
    (tmp_path / "context" / "leaf.txt").write_text("leaf one two", encoding="utf-8")
    (tmp_path / "context" / "mid.prompt").write_text(
        "mid head\n<include>context/leaf.txt</include>\nmid tail", encoding="utf-8"
    )
    prompt = tmp_path / "p_python.prompt"
    prompt.write_text("Body\n<include>context/mid.prompt</include>", encoding="utf-8")
    rows = _rows(runner, prompt)
    sources = [r["source"] for r in rows]
    assert any(s.endswith("mid.prompt") for s in sources)
    assert not any(s.endswith("leaf.txt") for s in sources)  # rolled into the parent
    mid_row = next(r for r in rows if r["source"].endswith("mid.prompt"))
    assert mid_row["tokens"] == 7  # full expanded mid content, including the leaf


def test_overlapping_top_level_includes_are_both_attributed(
    runner, tmp_path, monkeypatch, patched_tokens
):
    """review #5: independent top-level includes must not be treated as nested
    just because one file's realized content is a substring of another file."""
    monkeypatch.chdir(tmp_path)
    (tmp_path / "context").mkdir()
    (tmp_path / "context" / "a.txt").write_text("alpha beta", encoding="utf-8")
    (tmp_path / "context" / "b.txt").write_text(
        "prefix alpha beta suffix", encoding="utf-8"
    )
    prompt = tmp_path / "p_python.prompt"
    prompt.write_text(
        "Body\n<include>context/a.txt</include>\n<include>context/b.txt</include>",
        encoding="utf-8",
    )
    rows = _rows(runner, prompt)
    by_source = {r["source"]: r["tokens"] for r in rows}
    assert by_source.get("context/a.txt") == 2
    assert by_source.get("context/b.txt") == 4


def test_missing_include_is_surfaced_not_hidden(runner, tmp_path, monkeypatch, patched_tokens):
    """review #2: an unresolved include must appear as a warning and a row, not
    be silently folded into the body."""
    monkeypatch.chdir(tmp_path)
    (tmp_path / "context").mkdir()
    prompt = tmp_path / "p_python.prompt"
    prompt.write_text(
        "Body\n<include>context/missing.prompt</include>", encoding="utf-8"
    )
    result = runner.invoke(context, [str(prompt), "--json"], obj={})
    assert result.exit_code == 0, result.output
    payload = json.loads(result.output)
    assert any("missing.prompt" in w and "unresolved" in w for w in payload["warnings"])
    assert any(r["source"] == "context/missing.prompt" for r in payload["rows"])


def test_code_fenced_include_syntax_is_not_reported_unresolved(
    runner, tmp_path, monkeypatch, patched_tokens
):
    """review #5: documentation/example blocks that show include syntax are not
    real preprocess directives and must not produce unresolved rows."""
    monkeypatch.chdir(tmp_path)
    prompt = tmp_path / "p_python.prompt"
    prompt.write_text(
        "Body\n```\n<include>context/missing.prompt</include>\n```\n",
        encoding="utf-8",
    )
    payload = json.loads(runner.invoke(context, [str(prompt), "--json"], obj={}).output)
    assert not any("missing.prompt" in w for w in payload["warnings"])
    assert not any("missing.prompt" in r["source"] for r in payload["rows"])


def test_code_fenced_include_many_is_not_expanded_or_reported(
    runner, tmp_path, monkeypatch, patched_tokens
):
    """review #5: <include-many> inside a code fence is documentation, not a
    directive to expand or warn on."""
    monkeypatch.chdir(tmp_path)
    (tmp_path / "context").mkdir()
    (tmp_path / "context" / "a.txt").write_text("aa bb", encoding="utf-8")
    prompt = tmp_path / "p_python.prompt"
    prompt.write_text(
        "Body\n```\n<include-many>context/a.txt, context/missing.txt</include-many>\n```",
        encoding="utf-8",
    )
    payload = json.loads(runner.invoke(context, [str(prompt), "--json"], obj={}).output)
    assert not any(r["source"] == "context/a.txt" for r in payload["rows"])
    assert not any("missing.txt" in w for w in payload["warnings"])


def test_optional_missing_include_is_silent(
    runner, tmp_path, monkeypatch, patched_tokens
):
    """review #5: optional missing includes mirror preprocess semantics: skipped
    without an unresolved row or warning."""
    monkeypatch.chdir(tmp_path)
    prompt = tmp_path / "p_python.prompt"
    prompt.write_text(
        "Body\n<include optional>context/missing.prompt</include>\n"
        '<include-many optional="true">context/missing_many.prompt</include-many>',
        encoding="utf-8",
    )
    payload = json.loads(runner.invoke(context, [str(prompt), "--json"], obj={}).output)
    assert not any("missing.prompt" in w for w in payload["warnings"])
    assert not any("missing_many.prompt" in w for w in payload["warnings"])
    assert not any("missing" in r["source"] for r in payload["rows"])


def test_dynamic_tag_inside_included_file_is_warned(runner, tmp_path, monkeypatch, patched_tokens):
    """review #3: a <shell>/<web> tag inside an *included* file is detected, not
    just tags in the top-level prompt."""
    monkeypatch.chdir(tmp_path)
    (tmp_path / "context").mkdir()
    (tmp_path / "context" / "dyn.prompt").write_text(
        "alpha beta\n<shell>echo hi</shell>\ngamma", encoding="utf-8"
    )
    prompt = tmp_path / "p_python.prompt"
    prompt.write_text("Body\n<include>context/dyn.prompt</include>", encoding="utf-8")
    result = runner.invoke(context, [str(prompt), "--json"], obj={})
    assert result.exit_code == 0, result.output
    warnings = json.loads(result.output)["warnings"]
    assert any("shell" in w and "deferred" in w for w in warnings)


def test_dynamic_markup_excluded_from_deterministic_total(runner, tmp_path, monkeypatch, patched_tokens):
    """review #3: deferred dynamic-tag markup is not billed as hydrated payload."""
    monkeypatch.chdir(tmp_path)
    prompt = tmp_path / "p_python.prompt"
    prompt.write_text(
        "Build it.\n<shell>echo hello world here now</shell>", encoding="utf-8"
    )
    payload = json.loads(runner.invoke(context, [str(prompt), "--json"], obj={}).output)
    # Only "Build it." (2 words) counts; the 5-word shell body is excluded.
    assert payload["total_tokens"] == 2


# --------------------------------------------------------------------------- #
# Model default resolution is explicit about the environment (review #4).      #
# --------------------------------------------------------------------------- #


def test_default_model_falls_back_to_gpt4o_when_env_unset(runner, prompt_with_include, monkeypatch):
    """review #4: with PDD_MODEL_DEFAULT unset, the default model is gpt-4o."""
    monkeypatch.delenv("PDD_MODEL_DEFAULT", raising=False)
    monkeypatch.setattr(cx_module, "count_tokens", _word_count_tokens)
    monkeypatch.setattr(cx_module, "get_context_limit", lambda model: 1000)
    result = runner.invoke(context, [str(prompt_with_include), "--json"], obj={})
    assert json.loads(result.output)["model"] == "gpt-4o"


def test_default_model_honors_pdd_model_default_env(runner, prompt_with_include, monkeypatch):
    """review #4: when PDD_MODEL_DEFAULT is set, the default honors it (so the
    suite is not silently env-sensitive — the behavior is asserted explicitly)."""
    monkeypatch.setenv("PDD_MODEL_DEFAULT", "claude-sonnet-4-6")
    monkeypatch.setattr(cx_module, "count_tokens", _word_count_tokens)
    monkeypatch.setattr(cx_module, "get_context_limit", lambda model: 1000)
    result = runner.invoke(context, [str(prompt_with_include), "--json"], obj={})
    assert json.loads(result.output)["model"] == "claude-sonnet-4-6"
