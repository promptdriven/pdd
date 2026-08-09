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
import os
import threading

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


# --- PR #1387 review #3: the audit's process-global cwd/env mutation is
# serialized so concurrent connect audits stay deterministic, and the server can
# pass a project root via base_dir instead of changing cwd in its route. --------


def test_audit_file_base_dir_resolves_without_leaking_cwd(
    tmp_path, monkeypatch, patched_core
):
    """`audit_prompt_file(base_dir=...)` resolves includes from base_dir and
    restores the caller's cwd, so the route never has to chdir itself."""
    project = tmp_path / "proj"
    (project / "context").mkdir(parents=True)
    (project / "context" / "a.txt").write_text("alpha beta gamma", encoding="utf-8")
    prompt = project / "p_python.prompt"
    prompt.write_text("Body\n<include>context/a.txt</include>", encoding="utf-8")

    # Run from an unrelated cwd to prove resolution uses base_dir, not cwd.
    outside = tmp_path / "outside"
    outside.mkdir()
    monkeypatch.chdir(outside)
    before = os.getcwd()

    audit = ca_module.audit_prompt_file(
        str(prompt), model="gpt-4o", base_dir=str(project)
    )

    assert os.getcwd() == before  # cwd restored — no leak into the caller
    sources = {r.source: r.status for r in audit.rows}
    assert sources.get("context/a.txt") == "resolved"


def test_cwd_env_lock_is_reentrant():
    """The shared cwd/env lock is reentrant, so a route holding it (e.g. /analyze)
    can run an audit — which re-acquires it — without deadlocking."""
    with ca_module.cwd_env_lock():
        with ca_module.cwd_env_lock():
            assert True


def test_concurrent_audits_with_distinct_base_dirs_stay_correct(
    tmp_path, monkeypatch, patched_core
):
    """Concurrent audits resolving includes from different project roots must not
    cross-contaminate, and every run must restore cwd — the determinism the
    serialized cwd/env lock provides (PR #1387 review #3)."""
    monkeypatch.chdir(tmp_path)
    origin = os.getcwd()

    roots = []
    for i in range(6):
        proj = tmp_path / f"proj{i}"
        (proj / "context").mkdir(parents=True)
        # Each root's include has a distinct token count (i+1 words) so a
        # cross-contaminated resolution would attribute the wrong number.
        (proj / "context" / "a.txt").write_text(
            " ".join(["w"] * (i + 1)), encoding="utf-8"
        )
        prompt = proj / "p_python.prompt"
        prompt.write_text("Body\n<include>context/a.txt</include>", encoding="utf-8")
        roots.append((proj, prompt, i + 1))

    errors = []

    def run(proj, prompt, expected):
        try:
            for _ in range(8):
                audit = ca_module.audit_prompt_file(
                    str(prompt), model="gpt-4o", base_dir=str(proj)
                )
                by_source = {r.source: r.tokens for r in audit.rows}
                assert by_source.get("context/a.txt") == expected
        except AssertionError as e:  # pragma: no cover - failure path
            errors.append(str(e))

    threads = [
        threading.Thread(target=run, args=(proj, prompt, exp))
        for proj, prompt, exp in roots
    ]
    for t in threads:
        t.start()
    for t in threads:
        t.join()

    assert not errors, f"cross-contaminated audits: {errors}"
    assert os.getcwd() == origin  # no thread leaked a cwd change
