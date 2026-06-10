"""Cross-surface parity for the shared context-audit core (PR #1387 review #5).

`pdd context --json` (CLI), `pdd.context_audit.audit_prompt_file` (the shared
core), and the `pdd connect` `POST /api/v1/prompts/context-audit` endpoint must
return the **same audit facts** for the same prompt — that is the whole point of
extracting the core: the two public surfaces can never drift. These tests assert
that across three scenarios: a normal include, a missing include, and a deferred
dynamic tag. Token counting is stubbed to a deterministic word count on the core
module so all three paths agree numerically without an LLM/tokenizer call.
"""
import asyncio
import importlib
import json

import pytest
from click.testing import CliRunner
from unittest.mock import MagicMock

from pdd.commands.context import context
from pdd.server.routes.prompts import context_audit as context_audit_endpoint, ContextAuditRequest

ca_module = importlib.import_module("pdd.context_audit")


def _word_count_tokens(text, model="gpt-4o"):
    return len(text.split())


@pytest.fixture
def patched_core(monkeypatch):
    """Deterministic, no-LLM token counting on the shared core (all surfaces)."""
    monkeypatch.delenv("PDD_MODEL_DEFAULT", raising=False)
    monkeypatch.setattr(ca_module, "count_tokens", _word_count_tokens)
    monkeypatch.setattr(ca_module, "get_context_limit", lambda model: 1000)


def _norm(total_tokens, context_limit, percent_used, model, rows, warnings):
    """Normalize an audit into a comparable, order-independent fact set."""
    return {
        "total_tokens": total_tokens,
        "context_limit": context_limit,
        "percent_used": percent_used,
        "model": model,
        "warnings": sorted(warnings),
        "rows": sorted((r["source"], r["tokens"], r["status"], r["note"]) for r in rows),
    }


def _facts_cli(prompt):
    payload = json.loads(
        CliRunner().invoke(context, [str(prompt), "--json", "--model", "gpt-4o"], obj={}).output
    )
    return _norm(
        payload["total_tokens"], payload["context_limit"], payload["percent_used"],
        payload["model"], payload["rows"], payload["warnings"],
    )


def _facts_core(prompt):
    audit = ca_module.audit_prompt_file(str(prompt), model="gpt-4o")
    rows = [{"source": r.source, "tokens": r.tokens, "status": r.status, "note": r.note}
            for r in audit.rows]
    return _norm(
        audit.total_tokens, audit.context_limit, audit.percent_used,
        audit.model, rows, audit.warnings,
    )


def _facts_endpoint(prompt, project_root):
    validator = MagicMock()
    validator.project_root = project_root
    validator.validate.return_value = prompt
    response = asyncio.run(
        context_audit_endpoint(
            ContextAuditRequest(path=str(prompt), model="gpt-4o", threshold=80),
            validator=validator,
        )
    )
    rows = [{"source": r.source, "tokens": r.tokens, "status": r.status, "note": r.note}
            for r in response.rows]
    return _norm(
        response.total_tokens, response.context_limit, response.percent_used,
        response.model, rows, response.warnings,
    )


def _facts_endpoint_content(prompt, project_root, content):
    """Audit facts from the endpoint's override-content path (unsaved edits)."""
    validator = MagicMock()
    validator.project_root = project_root
    validator.validate.return_value = prompt
    response = asyncio.run(
        context_audit_endpoint(
            ContextAuditRequest(
                path=str(prompt), model="gpt-4o", threshold=80, content=content,
            ),
            validator=validator,
        )
    )
    rows = [{"source": r.source, "tokens": r.tokens, "status": r.status, "note": r.note}
            for r in response.rows]
    return _norm(
        response.total_tokens, response.context_limit, response.percent_used,
        response.model, rows, response.warnings,
    )


def _assert_all_agree(prompt, project_root):
    cli = _facts_cli(prompt)
    core = _facts_core(prompt)
    endpoint = _facts_endpoint(prompt, project_root)
    assert cli == core, f"CLI vs core mismatch:\n{cli}\n{core}"
    assert cli == endpoint, f"CLI vs endpoint mismatch:\n{cli}\n{endpoint}"
    return cli


def test_parity_normal_include(tmp_path, monkeypatch, patched_core):
    monkeypatch.chdir(tmp_path)
    (tmp_path / "context").mkdir()
    (tmp_path / "context" / "a.txt").write_text("alpha beta gamma", encoding="utf-8")
    prompt = tmp_path / "p_python.prompt"
    prompt.write_text("Write it now\n<include>context/a.txt</include>", encoding="utf-8")

    facts = _assert_all_agree(prompt, tmp_path)
    sources = {src: (toks, status) for src, toks, status, _ in facts["rows"]}
    assert sources["context/a.txt"] == (3, "resolved")
    assert sources["prompt_body"][1] == "body"


def test_parity_missing_include(tmp_path, monkeypatch, patched_core):
    monkeypatch.chdir(tmp_path)
    (tmp_path / "context").mkdir()
    prompt = tmp_path / "p_python.prompt"
    prompt.write_text("Body\n<include>context/missing.prompt</include>", encoding="utf-8")

    facts = _assert_all_agree(prompt, tmp_path)
    statuses = {src: status for src, _, status, _ in facts["rows"]}
    assert statuses.get("context/missing.prompt") == "unresolved"
    assert any("missing.prompt" in w and "unresolved" in w for w in facts["warnings"])


def test_parity_deferred_dynamic_tag(tmp_path, monkeypatch, patched_core):
    monkeypatch.chdir(tmp_path)
    (tmp_path / "context").mkdir()
    (tmp_path / "context" / "data.py").write_text("def f():\n    return 1\n", encoding="utf-8")
    prompt = tmp_path / "p_python.prompt"
    prompt.write_text(
        'Body\n<include query="summarize">context/data.py</include>', encoding="utf-8"
    )

    facts = _assert_all_agree(prompt, tmp_path)
    statuses = [status for _, _, status, _ in facts["rows"]]
    assert "deferred" in statuses
    assert any("query_include" in w and "deferred" in w for w in facts["warnings"])


def test_endpoint_override_content_audits_buffer_not_disk(tmp_path, monkeypatch, patched_core):
    """The endpoint's `content` override (unsaved editor edits) audits the
    provided buffer — not the file on disk — and resolves includes from the
    project root, so connect agrees with the visible editor (PR #1387 review #2).
    """
    monkeypatch.chdir(tmp_path)
    (tmp_path / "context").mkdir()
    (tmp_path / "context" / "a.txt").write_text("alpha beta gamma", encoding="utf-8")

    # The on-disk file and the unsaved editor buffer deliberately differ.
    prompt = tmp_path / "p_python.prompt"
    prompt.write_text("Stale on-disk body, no includes", encoding="utf-8")
    buffer = "Just-typed body\n<include>context/a.txt</include>"

    # Endpoint(content=buffer) must equal the core run on the buffer itself,
    # and must NOT equal the audit of the stale file on disk.
    from_buffer = _facts_endpoint_content(prompt, tmp_path, buffer)
    core_buffer = _norm(
        *(lambda a: (
            a.total_tokens, a.context_limit, a.percent_used, a.model,
            [{"source": r.source, "tokens": r.tokens, "status": r.status, "note": r.note}
             for r in a.rows],
            a.warnings,
        ))(ca_module.audit_prompt_text(buffer, model="gpt-4o", base_dir=str(tmp_path)))
    )
    assert from_buffer == core_buffer
    assert from_buffer != _facts_endpoint(prompt, tmp_path)  # not the disk file

    # The include in the buffer resolved against the project root.
    sources = {src: status for src, _, status, _ in from_buffer["rows"]}
    assert sources.get("context/a.txt") == "resolved"


# ---------------------------------------------------------------------------
# Pure helper tests
# ---------------------------------------------------------------------------


import sys
from pathlib import Path

# Add project root to sys.path to ensure local code is prioritized
# This allows testing local changes without installing the package
project_root = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(project_root))

def test_percent_basic():
    assert ca_module.percent(50, 200) == 25.0
    assert ca_module.percent(1, 3) == 33.3


def test_percent_none_when_whole_is_falsy():
    assert ca_module.percent(10, 0) is None
    assert ca_module.percent(10, None) is None


def test_row_percent_zero_when_total_zero():
    row = ca_module.AuditRow(source="x", tokens=5, status="resolved")
    assert ca_module.row_percent(row, 0) == 0.0
    assert ca_module.row_percent(row, 10) == 50.0


def test_threshold_exceeded_rules():
    assert ca_module.threshold_exceeded(90.0, 80) is True
    assert ca_module.threshold_exceeded(50.0, 80) is False
    # threshold=0 disables
    assert ca_module.threshold_exceeded(99.0, 0) is False
    # None percent_used never trips
    assert ca_module.threshold_exceeded(None, 50) is False
    # Equal does not exceed
    assert ca_module.threshold_exceeded(80.0, 80) is False


# ---------------------------------------------------------------------------
# Dataclass shape
# ---------------------------------------------------------------------------

def test_audit_row_is_frozen():
    row = ca_module.AuditRow(source="s", tokens=1, status="body")
    with pytest.raises(Exception):
        row.tokens = 2  # type: ignore[misc]


def test_context_audit_defaults():
    audit = ca_module.ContextAudit(
        model="m", total_tokens=0, context_limit=None, percent_used=None
    )
    assert audit.rows == []
    assert audit.warnings == []


# ---------------------------------------------------------------------------
# audit_prompt_text / file behaviors
# ---------------------------------------------------------------------------

def test_audit_prompt_file_reads_utf8(tmp_path, monkeypatch, patched_core):
    monkeypatch.chdir(tmp_path)
    prompt = tmp_path / "p_python.prompt"
    prompt.write_text("h llo w rld", encoding="utf-8")
    audit = ca_module.audit_prompt_file(str(prompt), model="gpt-4o")
    assert audit.model == "gpt-4o"
    assert audit.total_tokens == 2
    assert audit.context_limit == 1000
    assert audit.percent_used == ca_module.percent(2, 1000)


def test_audit_prompt_text_grounding_row_always_present(patched_core):
    audit = ca_module.audit_prompt_text("just a body", model="gpt-4o")
    grounding = [r for r in audit.rows if r.source == "grounding"]
    assert len(grounding) == 1
    assert grounding[0].status == "unavailable"
    assert grounding[0].tokens == 0
    assert "cloud" in (grounding[0].note or "").lower()


def test_audit_prompt_text_body_row_present(patched_core):
    audit = ca_module.audit_prompt_text("one two three four", model="gpt-4o")
    body = [r for r in audit.rows if r.status == "body"]
    assert len(body) == 1
    assert body[0].source == "prompt_body"
    assert body[0].tokens == 4


def test_audit_context_limit_none_yields_none_percent(monkeypatch, patched_core):
    monkeypatch.setattr(ca_module, "get_context_limit", lambda model: None)
    audit = ca_module.audit_prompt_text("hello world", model="unknown-model")
    assert audit.context_limit is None
    assert audit.percent_used is None


def test_rows_sorted_by_tokens_desc(tmp_path, monkeypatch, patched_core):
    monkeypatch.chdir(tmp_path)
    (tmp_path / "ctx").mkdir()
    (tmp_path / "ctx" / "big.txt").write_text("a " * 20, encoding="utf-8")
    (tmp_path / "ctx" / "small.txt").write_text("x", encoding="utf-8")
    prompt = tmp_path / "p_python.prompt"
    prompt.write_text(
        "body words here\n"
        "<include>ctx/big.txt</include>\n"
        "<include>ctx/small.txt</include>",
        encoding="utf-8",
    )
    audit = ca_module.audit_prompt_text(prompt.read_text(), model="gpt-4o")
    token_counts = [r.tokens for r in audit.rows]
    assert token_counts == sorted(token_counts, reverse=True)


def test_dynamic_tag_in_code_fence_not_warned(tmp_path, monkeypatch, patched_core):
    """<shell> inside a fenced code block is documentation, not a directive."""
    monkeypatch.chdir(tmp_path)
    text = "Example:\n```\n<shell>ls</shell>\n```\nend"
    audit = ca_module.audit_prompt_text(text, model="gpt-4o")
    assert not any(r.status == "deferred" for r in audit.rows)
    assert not any("shell" in w for w in audit.warnings)


def test_dynamic_shell_tag_outside_code_is_deferred(patched_core):
    text = "before <shell>ls -la</shell> after"
    audit = ca_module.audit_prompt_text(text, model="gpt-4o")
    deferred = [r for r in audit.rows if r.status == "deferred"]
    assert any(r.source == "<shell>" for r in deferred)
    assert any("shell" in w for w in audit.warnings)


def test_env_vars_restored_after_audit(monkeypatch, patched_core):
    monkeypatch.delenv("PDD_QUIET", raising=False)
    monkeypatch.delenv("PDD_CONTEXT_AUDIT_NO_QUERY_FALLBACK", raising=False)
    ca_module.audit_prompt_text("hello", model="gpt-4o")
    assert "PDD_QUIET" not in os.environ
    assert "PDD_CONTEXT_AUDIT_NO_QUERY_FALLBACK" not in os.environ


def test_preexisting_env_vars_restored(monkeypatch, patched_core):
    monkeypatch.setenv("PDD_QUIET", "original")
    monkeypatch.setenv("PDD_CONTEXT_AUDIT_NO_QUERY_FALLBACK", "prior")
    ca_module.audit_prompt_text("hello", model="gpt-4o")
    assert os.environ["PDD_QUIET"] == "original"
    assert os.environ["PDD_CONTEXT_AUDIT_NO_QUERY_FALLBACK"] == "prior"


def test_base_dir_restores_cwd(tmp_path, monkeypatch, patched_core):
    monkeypatch.chdir(tmp_path)
    other = tmp_path / "other"
    other.mkdir()
    origin = os.getcwd()
    ca_module.audit_prompt_text("hi", model="gpt-4o", base_dir=str(other))
    assert os.getcwd() == origin


def test_base_dir_resolves_relative_includes(tmp_path, monkeypatch, patched_core):
    monkeypatch.chdir(tmp_path)  # CWD is NOT the project root
    project = tmp_path / "proj"
    (project / "ctx").mkdir(parents=True)
    (project / "ctx" / "a.txt").write_text("alpha beta", encoding="utf-8")
    text = "body\n<include>ctx/a.txt</include>"
    audit = ca_module.audit_prompt_text(text, model="gpt-4o", base_dir=str(project))
    sources = {r.source: r.status for r in audit.rows}
    assert any("a.txt" in s and st == "resolved" for s, st in sources.items())


def test_stdout_not_corrupted_by_audit(capsys, patched_core):
    audit = ca_module.audit_prompt_text("hello world", model="gpt-4o")
    captured = capsys.readouterr()
    assert captured.out == ""
    assert audit.total_tokens == 2