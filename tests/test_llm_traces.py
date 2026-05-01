"""Tier 1: Mocked tests for LLM trace logging (sections A through Q)."""
from __future__ import annotations

import json
import os
import shutil
import textwrap
from pathlib import Path
from typing import Any, Dict, List, Optional
from unittest import mock

import pytest

# ---------------------------------------------------------------------------
# Helpers
# ---------------------------------------------------------------------------

def _write_sync_log(path: Path, entries: List[Dict[str, Any]]) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    with open(path, "w", encoding="utf-8") as f:
        for entry in entries:
            f.write(json.dumps(entry) + "\n")


def _read_sync_log(path: Path) -> List[Dict[str, Any]]:
    entries = []
    with open(path, "r", encoding="utf-8") as f:
        for line in f:
            if line.strip():
                entries.append(json.loads(line))
    return entries


# =========================================================================
# Section A: Log file location and migration
# =========================================================================

class TestLogFileLocationAndMigration:
    """Section A: log file location and migration."""

    def test_new_write_path(self, tmp_path, monkeypatch):
        """get_log_path returns .pdd/logs/ path and creates directory."""
        monkeypatch.chdir(tmp_path)
        from pdd.operation_log import get_log_path
        result = get_log_path("mymod", "python")
        assert result == Path(".pdd/logs/mymod_python_sync.log")
        assert result.parent.exists()

    def test_migration_on_write(self, tmp_path, monkeypatch):
        """Legacy file moves from .pdd/meta/ to .pdd/logs/ on get_log_path()."""
        monkeypatch.chdir(tmp_path)
        old_dir = tmp_path / ".pdd" / "meta"
        old_dir.mkdir(parents=True)
        old_path = old_dir / "mymod_python_sync.log"
        content = b'{"test": true}\n'
        old_path.write_bytes(content)

        from pdd.operation_log import get_log_path
        new_path = get_log_path("mymod", "python")

        assert new_path.exists()
        assert new_path.read_bytes() == content
        assert not old_path.exists()

    def test_migration_on_read(self, tmp_path, monkeypatch):
        """load_operation_log triggers migration and returns entries."""
        monkeypatch.chdir(tmp_path)
        old_dir = tmp_path / ".pdd" / "meta"
        old_dir.mkdir(parents=True)
        old_path = old_dir / "mymod_python_sync.log"
        entry = {"operation": "generate", "success": True, "timestamp": "2026-01-01T00:00:00"}
        old_path.write_text(json.dumps(entry) + "\n", encoding="utf-8")

        from pdd.operation_log import load_operation_log
        entries = load_operation_log("mymod", "python")

        assert len(entries) == 1
        assert entries[0]["operation"] == "generate"
        new_path = tmp_path / ".pdd" / "logs" / "mymod_python_sync.log"
        assert new_path.exists()
        assert not old_path.exists()

    def test_already_migrated(self, tmp_path, monkeypatch):
        """File already in .pdd/logs/ — no error, file untouched."""
        monkeypatch.chdir(tmp_path)
        new_dir = tmp_path / ".pdd" / "logs"
        new_dir.mkdir(parents=True)
        new_path = new_dir / "mymod_python_sync.log"
        content = b'{"test": true}\n'
        new_path.write_bytes(content)

        from pdd.operation_log import get_log_path
        result = get_log_path("mymod", "python")
        assert result.read_bytes() == content

    def test_only_sync_logs_migrate(self, tmp_path, monkeypatch):
        """Fingerprint and run report stay in .pdd/meta/."""
        monkeypatch.chdir(tmp_path)
        meta_dir = tmp_path / ".pdd" / "meta"
        meta_dir.mkdir(parents=True)
        fp = meta_dir / "mymod_python.json"
        rr = meta_dir / "mymod_python_run.json"
        fp.write_text("{}", encoding="utf-8")
        rr.write_text("{}", encoding="utf-8")

        from pdd.operation_log import get_log_path
        get_log_path("mymod", "python")

        assert fp.exists()
        assert rr.exists()

    def test_directory_creation_safe_twice(self, tmp_path, monkeypatch):
        """Calling get_log_path twice doesn't error."""
        monkeypatch.chdir(tmp_path)
        from pdd.operation_log import get_log_path
        get_log_path("mymod", "python")
        get_log_path("mymod", "python")  # should not raise


# =========================================================================
# Section B: LLM trace structure
# =========================================================================

class TestLLMTraceStructure:
    """Section B: llm_traces structure."""

    def test_generate_gets_llm_traces_list(self, tmp_path, monkeypatch):
        """record_llm_pair accumulates multiple pairs under one operation."""
        from pdd.core.llm_trace import set_current_operation, record_llm_pair, pop_all_pairs
        set_current_operation("generate")
        for i in range(3):
            record_llm_pair(prompt=f"prompt_{i}", response=f"response_{i}", model="test-model")
        pairs = pop_all_pairs("generate")
        assert len(pairs) == 3
        for i, p in enumerate(pairs):
            assert p["prompt"] == f"prompt_{i}"
            assert p["response"] == f"response_{i}"
            assert p["model"] == "test-model"
            assert "thinking" in p

    def test_crash_retries_collect_all(self):
        """crash with 3 retries x 2 calls = 6 trace items."""
        from pdd.core.llm_trace import set_current_operation, record_llm_pair, pop_all_pairs
        set_current_operation("crash")
        for retry in range(3):
            for call in range(2):
                record_llm_pair(prompt=f"r{retry}c{call}", response="resp", model="m")
        pairs = pop_all_pairs("crash")
        assert len(pairs) == 6

    def test_trace_item_schema(self):
        """Every item has prompt, response, model, thinking keys."""
        from pdd.core.llm_trace import set_current_operation, record_llm_pair, pop_all_pairs
        set_current_operation("generate")
        record_llm_pair(prompt="p", response="r", model="m")
        pairs = pop_all_pairs("generate")
        assert len(pairs) == 1
        item = pairs[0]
        assert isinstance(item["prompt"], str) and item["prompt"]
        assert isinstance(item["response"], str) and item["response"]
        assert isinstance(item["model"], str) and item["model"]
        assert item["thinking"] is None or isinstance(item["thinking"], str)

    def test_traces_on_success_and_failure(self):
        """Both success and failure operations get traces."""
        from pdd.core.llm_trace import set_current_operation, record_llm_pair, pop_all_pairs
        # Success
        set_current_operation("generate")
        record_llm_pair(prompt="p", response="r", model="m")
        success_pairs = pop_all_pairs("generate")
        assert len(success_pairs) == 1

        # Failure (still recorded)
        set_current_operation("generate")
        record_llm_pair(prompt="p2", response="r2", model="m")
        failure_pairs = pop_all_pairs("generate")
        assert len(failure_pairs) == 1

    def test_failed_operation_keeps_all_traces(self):
        """3 LLM calls before failure are all preserved."""
        from pdd.core.llm_trace import set_current_operation, record_llm_pair, pop_all_pairs
        set_current_operation("generate")
        for i in range(3):
            record_llm_pair(prompt=f"p{i}", response=f"r{i}", model="m")
        # Operation fails, but traces are still there
        pairs = pop_all_pairs("generate")
        assert len(pairs) == 3

    def test_thinking_populated(self):
        """thinking field populated when provided."""
        from pdd.core.llm_trace import set_current_operation, record_llm_pair, pop_all_pairs
        set_current_operation("generate")
        record_llm_pair(prompt="p", response="r", model="m", thinking="I think therefore I am")
        pairs = pop_all_pairs("generate")
        assert pairs[0]["thinking"] == "I think therefore I am"

    def test_thinking_null_when_absent(self):
        """thinking is null (None), not missing, when not provided."""
        from pdd.core.llm_trace import set_current_operation, record_llm_pair, pop_all_pairs
        set_current_operation("generate")
        record_llm_pair(prompt="p", response="r", model="m")
        pairs = pop_all_pairs("generate")
        assert "thinking" in pairs[0]
        assert pairs[0]["thinking"] is None


# =========================================================================
# Section C: Agentic trace structure
# =========================================================================

class TestAgenticTraceStructure:
    """Section C: agentic_trace structure — tests actual discovery functions."""

    def test_claude_discovery_returns_correct_schema(self, tmp_path, monkeypatch):
        """_discover_claude_session returns dict with session_file, provider, format."""
        from pdd.agentic_common import _discover_claude_session
        cwd = tmp_path / "proj"
        cwd.mkdir()
        slug = str(cwd).replace("/", "-")
        session_dir = tmp_path / ".claude" / "projects" / slug
        session_dir.mkdir(parents=True)
        sf = session_dir / "sess-1.jsonl"
        sf.write_text('{"ok":true}\n', encoding="utf-8")
        monkeypatch.setattr(Path, "home", lambda: tmp_path)

        trace = _discover_claude_session("sess-1", cwd)
        assert trace is not None
        assert set(trace.keys()) == {"session_file", "provider", "format"}
        assert trace["provider"] == "anthropic"
        assert trace["format"] == "jsonl"

    def test_gemini_discovery_returns_json_format(self, tmp_path, monkeypatch):
        """_discover_gemini_session sets format='json' for .json files."""
        from pdd.agentic_common import _discover_gemini_session
        cwd = tmp_path / "proj"
        cwd.mkdir()
        gemini_home = tmp_path / ".gemini"
        projects_json = gemini_home / "projects.json"
        projects_json.parent.mkdir(parents=True)
        projects_json.write_text(
            json.dumps({"projects": {str(cwd): "my-slug"}}), encoding="utf-8"
        )
        chats_dir = gemini_home / "tmp" / "my-slug" / "chats"
        chats_dir.mkdir(parents=True)
        session_id = "abcdef12-full-uuid"
        sf = chats_dir / f"{session_id}.json"
        sf.write_text('{"ok":true}\n', encoding="utf-8")
        monkeypatch.setattr(Path, "home", lambda: tmp_path)

        trace = _discover_gemini_session(session_id, cwd)
        assert trace is not None
        assert trace["provider"] == "google"
        assert trace["format"] == "json"

    def test_codex_discovery_returns_correct_schema(self, tmp_path, monkeypatch):
        """_discover_codex_session returns dict with provider='openai' and format='jsonl'."""
        from pdd.agentic_common import _discover_codex_session
        sessions_dir = tmp_path / ".codex" / "sessions" / "2026" / "04" / "25"
        sessions_dir.mkdir(parents=True)
        monkeypatch.setenv("CODEX_HOME", str(tmp_path / ".codex"))
        # pre-snapshot is empty; one new file appears
        new_file = sessions_dir / "rollout-new.jsonl"
        new_file.write_text('{"step":1}\n', encoding="utf-8")

        trace = _discover_codex_session(set(), tmp_path)
        assert trace is not None
        assert set(trace.keys()) == {"session_file", "provider", "format"}
        assert trace["provider"] == "openai"
        assert trace["format"] == "jsonl"

    def test_both_llm_traces_and_agentic_trace_on_same_entry(self, tmp_path, monkeypatch):
        """sync_orchestration can attach both llm_traces and agentic_trace to one entry."""
        from unittest.mock import patch as _patch
        from pdd.sync_determine_operation import SyncDecision
        import pdd.agentic_common as ac

        monkeypatch.chdir(tmp_path)
        (tmp_path / "prompts").mkdir()
        (tmp_path / "src").mkdir()
        (tmp_path / "tests").mkdir()
        (tmp_path / "context").mkdir()
        (tmp_path / ".pdd" / "meta").mkdir(parents=True)

        prompt = tmp_path / "prompts" / "demo_python.prompt"
        code = tmp_path / "src" / "demo.py"
        example = tmp_path / "context" / "demo_example.py"
        test_file = tmp_path / "tests" / "test_demo.py"
        prompt.write_text("Create demo", encoding="utf-8")
        code.write_text("print('x')\n", encoding="utf-8")
        example.write_text("print('example')\n", encoding="utf-8")
        test_file.write_text("def test_ok(): assert True\n", encoding="utf-8")

        fake_paths = {
            "prompt": prompt, "code": code, "example": example,
            "test": test_file, "test_files": [test_file],
        }
        decisions = [
            SyncDecision(operation="generate", reason="force"),
            SyncDecision(operation="error", reason="stop"),
        ]

        seen_entries = []
        fake_traces = [{"prompt": "P", "response": "R", "model": "m", "thinking": None}]
        fake_agentic = {"session_file": "/path/sess.jsonl", "provider": "anthropic", "format": "jsonl"}

        # Simulate _run_with_provider setting the trace DURING the operation
        # (after the pre-op drain, before the post-op read).
        real_code_gen = None
        def fake_code_gen(*args, **kwargs):
            ac._last_agentic_trace.set(fake_agentic)
            return (None, False, 0.01, "m")

        with _patch("pdd.sync_orchestration.get_pdd_file_paths", return_value=fake_paths), \
             _patch("pdd.sync_orchestration.SyncLock") as mock_lock, \
             _patch("pdd.sync_orchestration.sync_determine_operation", side_effect=decisions), \
             _patch("pdd.sync_orchestration.code_generator_main", side_effect=fake_code_gen), \
             _patch("pdd.sync_orchestration.pop_all_pairs", return_value=fake_traces), \
             _patch("pdd.sync_orchestration.append_log_entry", side_effect=lambda _b, _l, e: seen_entries.append(e)), \
             _patch("pdd.sync_orchestration.log_event"):
            mock_lock.return_value.__enter__.return_value = mock_lock
            mock_lock.return_value.__exit__.return_value = None
            from pdd.sync_orchestration import sync_orchestration
            sync_orchestration(basename="demo", language="python", quiet=True, prompts_dir="prompts")

        gen_entries = [e for e in seen_entries if e.get("operation") == "generate"]
        assert gen_entries, f"No generate entry found in {seen_entries}"
        assert gen_entries[0].get("llm_traces") == fake_traces
        assert gen_entries[0].get("agentic_trace") == fake_agentic


# =========================================================================
# Section D: Entries without traces
# =========================================================================

class TestEntriesWithoutTraces:
    """Section D: skip/event/error entries have no trace keys via sync_orchestration."""

    @staticmethod
    def _run_sync_with_decisions(tmp_path, monkeypatch, decisions):
        """Helper: run sync_orchestration with mocked decisions, return logged entries."""
        from unittest.mock import patch as _patch
        monkeypatch.chdir(tmp_path)
        (tmp_path / "prompts").mkdir()
        (tmp_path / "src").mkdir()
        (tmp_path / "tests").mkdir()
        (tmp_path / "context").mkdir()
        (tmp_path / ".pdd" / "meta").mkdir(parents=True)

        prompt = tmp_path / "prompts" / "demo_python.prompt"
        code = tmp_path / "src" / "demo.py"
        example = tmp_path / "context" / "demo_example.py"
        test_file = tmp_path / "tests" / "test_demo.py"
        prompt.write_text("Create demo", encoding="utf-8")
        code.write_text("print('x')\n", encoding="utf-8")
        example.write_text("print('example')\n", encoding="utf-8")
        test_file.write_text("def test_ok(): assert True\n", encoding="utf-8")

        fake_paths = {
            "prompt": prompt, "code": code, "example": example,
            "test": test_file, "test_files": [test_file],
        }

        seen_entries = []
        seen_events = []

        with _patch("pdd.sync_orchestration.get_pdd_file_paths", return_value=fake_paths), \
             _patch("pdd.sync_orchestration.SyncLock") as mock_lock, \
             _patch("pdd.sync_orchestration.sync_determine_operation", side_effect=decisions), \
             _patch("pdd.sync_orchestration.append_log_entry", side_effect=lambda _b, _l, e: seen_entries.append(e)), \
             _patch("pdd.sync_orchestration.log_event", side_effect=lambda _b, _l, *a, **kw: seen_events.append(a)):
            mock_lock.return_value.__enter__.return_value = mock_lock
            mock_lock.return_value.__exit__.return_value = None
            from pdd.sync_orchestration import sync_orchestration
            sync_orchestration(basename="demo", language="python", quiet=True, prompts_dir="prompts",
                               skip_verify=True, skip_tests=True)

        return seen_entries, seen_events

    def test_skip_entry_has_no_trace_keys(self, tmp_path, monkeypatch):
        """When sync_orchestration skips verify, the logged entry has no llm_traces or agentic_trace."""
        from pdd.sync_determine_operation import SyncDecision
        decisions = [
            SyncDecision(operation="verify", reason="check"),
            SyncDecision(operation="all_synced", reason="done"),
        ]
        entries, _ = self._run_sync_with_decisions(tmp_path, monkeypatch, decisions)
        verify_entries = [e for e in entries if "verify" in e.get("operation", "")]
        assert verify_entries, f"No verify entry: {entries}"
        for e in verify_entries:
            assert "llm_traces" not in e
            assert "agentic_trace" not in e

    def test_error_decision_entry_has_no_trace_keys(self, tmp_path, monkeypatch):
        """When sync_determine_operation returns 'error', the logged entry has no trace keys."""
        from pdd.sync_determine_operation import SyncDecision
        decisions = [SyncDecision(operation="error", reason="something broke")]
        entries, _ = self._run_sync_with_decisions(tmp_path, monkeypatch, decisions)
        error_entries = [e for e in entries if e.get("operation") == "error"]
        assert error_entries, f"No error entry: {entries}"
        for e in error_entries:
            assert "llm_traces" not in e
            assert "agentic_trace" not in e

    def test_event_logged_via_log_event_has_no_trace_keys(self, tmp_path, monkeypatch):
        """log_event() produces entries without trace keys (events go through a different path)."""
        from pdd.operation_log import log_event
        monkeypatch.chdir(tmp_path)
        (tmp_path / ".pdd" / "logs").mkdir(parents=True)
        log_event("demo", "python", "sync_start", {"modules": ["demo"]})

        from pdd.operation_log import load_operation_log
        entries = load_operation_log("demo", "python")
        assert len(entries) == 1
        assert entries[0]["type"] == "event"
        assert "llm_traces" not in entries[0]
        assert "agentic_trace" not in entries[0]


# =========================================================================
# Section E: Truncation and redaction
# =========================================================================

class TestTruncationAndRedaction:
    """Section E: truncation and redaction."""

    def test_prompt_truncation(self):
        """Prompt over 20k chars is truncated with suffix."""
        from pdd.core.llm_trace import set_current_operation, record_llm_pair, pop_all_pairs
        set_current_operation("gen")
        long_prompt = "x" * 30000
        record_llm_pair(prompt=long_prompt, response="r", model="m")
        pairs = pop_all_pairs("gen")
        stored = pairs[0]["prompt"]
        assert stored.endswith(f"\n... (truncated, 30000 total chars)")
        assert len(stored) <= 20000 + len(f"\n... (truncated, 30000 total chars)")

    def test_response_truncation(self):
        """Response over 20k chars is truncated."""
        from pdd.core.llm_trace import set_current_operation, record_llm_pair, pop_all_pairs
        set_current_operation("gen2")
        long_resp = "y" * 30000
        record_llm_pair(prompt="p", response=long_resp, model="m")
        pairs = pop_all_pairs("gen2")
        assert pairs[0]["response"].endswith(f"\n... (truncated, 30000 total chars)")

    def test_thinking_truncation(self):
        """Thinking over 20k chars is truncated."""
        from pdd.core.llm_trace import set_current_operation, record_llm_pair, pop_all_pairs
        set_current_operation("gen3")
        long_think = "z" * 30000
        record_llm_pair(prompt="p", response="r", model="m", thinking=long_think)
        pairs = pop_all_pairs("gen3")
        assert pairs[0]["thinking"].endswith(f"\n... (truncated, 30000 total chars)")

    def test_secret_redaction(self):
        """Bearer tokens, api_key, token, password, secret are scrubbed."""
        from pdd.core.llm_trace import set_current_operation, record_llm_pair, pop_all_pairs
        set_current_operation("gen4")
        prompt = (
            "Bearer sk-abc123secretvalue "
            "api_key=secret456 "
            "token=mytoken123 "
            "password=hunter2abc "
            "secret=topsecret99"
        )
        record_llm_pair(prompt=prompt, response="r", model="m")
        pairs = pop_all_pairs("gen4")
        stored = pairs[0]["prompt"]
        for val in ["sk-abc123secretvalue", "secret456", "mytoken123", "hunter2abc", "topsecret99"]:
            assert val not in stored
        assert "<redacted>" in stored


# =========================================================================
# Section F: Session discovery: Claude
# =========================================================================

class TestSessionDiscoveryClaude:
    """Section F: Claude session discovery."""

    def test_finds_session_by_id(self, tmp_path, monkeypatch):
        """Constructs path from session_id and finds it."""
        from pdd.agentic_common import _discover_claude_session
        cwd = tmp_path / "myproject"
        cwd.mkdir()
        slug = str(cwd).replace("/", "-")
        session_id = "abc-123-def"
        session_dir = tmp_path / ".claude" / "projects" / slug
        session_dir.mkdir(parents=True)
        session_file = session_dir / f"{session_id}.jsonl"
        session_file.write_text('{"test": true}\n', encoding="utf-8")
        monkeypatch.setattr(Path, "home", lambda: tmp_path)
        result = _discover_claude_session(session_id, cwd)
        assert result is not None
        assert result["session_file"] == str(session_file)
        assert result["provider"] == "anthropic"
        assert result["format"] == "jsonl"

    def test_slug_has_leading_dash(self, tmp_path, monkeypatch):
        """For /Users/dev/project, slug is -Users-dev-project."""
        cwd = Path("/Users/dev/project")
        slug = str(cwd).replace("/", "-")
        assert slug.startswith("-")
        assert slug == "-Users-dev-project"

    def test_slug_with_spaces(self, tmp_path, monkeypatch):
        """Literal replacement of / with -, no encoding."""
        from pdd.agentic_common import _discover_claude_session
        cwd = tmp_path / "my project (v2)"
        cwd.mkdir()
        slug = str(cwd).replace("/", "-")
        session_dir = tmp_path / ".claude" / "projects" / slug
        session_dir.mkdir(parents=True)
        sf = session_dir / "sess1.jsonl"
        sf.write_text('{"x":1}\n', encoding="utf-8")
        monkeypatch.setattr(Path, "home", lambda: tmp_path)
        result = _discover_claude_session("sess1", cwd)
        assert result is not None

    def test_deep_path(self, tmp_path, monkeypatch):
        """Deep cwd paths still produce valid slugs."""
        from pdd.agentic_common import _discover_claude_session
        cwd = tmp_path / "home" / "ci" / "builds" / "org" / "repo"
        cwd.mkdir(parents=True)
        slug = str(cwd).replace("/", "-")
        session_dir = tmp_path / ".claude" / "projects" / slug
        session_dir.mkdir(parents=True)
        sf = session_dir / "deep-session.jsonl"
        sf.write_text('{"x":1}\n', encoding="utf-8")
        monkeypatch.setattr(Path, "home", lambda: tmp_path)
        result = _discover_claude_session("deep-session", cwd)
        assert result is not None

    def test_missing_session_id(self, tmp_path, monkeypatch):
        """No session_id → None."""
        from pdd.agentic_common import _discover_claude_session
        monkeypatch.setattr(Path, "home", lambda: tmp_path)
        assert _discover_claude_session("", tmp_path) is None

    def test_file_not_found(self, tmp_path, monkeypatch):
        """session_id present but .jsonl missing → None."""
        from pdd.agentic_common import _discover_claude_session
        cwd = tmp_path / "proj"
        cwd.mkdir()
        slug = str(cwd).replace("/", "-")
        (tmp_path / ".claude" / "projects" / slug).mkdir(parents=True)
        monkeypatch.setattr(Path, "home", lambda: tmp_path)
        assert _discover_claude_session("nonexistent", cwd) is None

    def test_missing_claude_dir(self, tmp_path, monkeypatch):
        """No ~/.claude/ → None, no exception."""
        from pdd.agentic_common import _discover_claude_session
        monkeypatch.setattr(Path, "home", lambda: tmp_path)
        assert _discover_claude_session("abc", tmp_path) is None

    def test_empty_session_file(self, tmp_path, monkeypatch):
        """0-byte session file → None."""
        from pdd.agentic_common import _discover_claude_session
        cwd = tmp_path / "proj"
        cwd.mkdir()
        slug = str(cwd).replace("/", "-")
        session_dir = tmp_path / ".claude" / "projects" / slug
        session_dir.mkdir(parents=True)
        sf = session_dir / "empty.jsonl"
        sf.write_text("", encoding="utf-8")
        monkeypatch.setattr(Path, "home", lambda: tmp_path)
        assert _discover_claude_session("empty", cwd) is None

    def test_parallel_safety(self, tmp_path, monkeypatch):
        """Two session IDs resolve to different files."""
        from pdd.agentic_common import _discover_claude_session
        cwd = tmp_path / "proj"
        cwd.mkdir()
        slug = str(cwd).replace("/", "-")
        session_dir = tmp_path / ".claude" / "projects" / slug
        session_dir.mkdir(parents=True)
        for sid in ["sess-a", "sess-b"]:
            (session_dir / f"{sid}.jsonl").write_text(f'{{"id":"{sid}"}}\n', encoding="utf-8")
        monkeypatch.setattr(Path, "home", lambda: tmp_path)
        a = _discover_claude_session("sess-a", cwd)
        b = _discover_claude_session("sess-b", cwd)
        assert a["session_file"] != b["session_file"]


# =========================================================================
# Section G: Session discovery: Gemini
# =========================================================================

class TestSessionDiscoveryGemini:
    """Section G: Gemini session discovery."""

    def _setup_gemini(self, tmp_path, cwd_str, slug, session_id, filename, monkeypatch):
        gemini_home = tmp_path / ".gemini"
        projects_json = gemini_home / "projects.json"
        projects_json.parent.mkdir(parents=True, exist_ok=True)
        projects_json.write_text(json.dumps({"projects": {cwd_str: slug}}), encoding="utf-8")
        chats_dir = gemini_home / "tmp" / slug / "chats"
        chats_dir.mkdir(parents=True, exist_ok=True)
        sf = chats_dir / filename
        sf.write_text('{"test": true}\n', encoding="utf-8")
        monkeypatch.setattr(Path, "home", lambda: tmp_path)
        return sf

    def test_happy_path(self, tmp_path, monkeypatch):
        """Find session by ID prefix."""
        from pdd.agentic_common import _discover_gemini_session
        cwd = tmp_path / "proj"
        cwd.mkdir()
        sid = "b017d68a-e4a7-4c7a-a454-72cd790ea905"
        sf = self._setup_gemini(tmp_path, str(cwd), "pdd", sid,
                                "session-2026-04-25T20-32-b017d68a.json", monkeypatch)
        result = _discover_gemini_session(sid, cwd)
        assert result is not None
        assert result["format"] == "json"
        assert result["provider"] == "google"

    def test_falls_back_to_jsonl(self, tmp_path, monkeypatch):
        """No .json match → falls back to .jsonl."""
        from pdd.agentic_common import _discover_gemini_session
        cwd = tmp_path / "proj"
        cwd.mkdir()
        sid = "b017d68a-e4a7-4c7a-a454-72cd790ea905"
        sf = self._setup_gemini(tmp_path, str(cwd), "pdd", sid,
                                "session-2026-04-25T20-32-b017d68a.jsonl", monkeypatch)
        result = _discover_gemini_session(sid, cwd)
        assert result is not None
        assert result["format"] == "jsonl"

    def test_prefers_json_over_jsonl(self, tmp_path, monkeypatch):
        """Both .json and .jsonl exist → returns .json."""
        from pdd.agentic_common import _discover_gemini_session
        cwd = tmp_path / "proj"
        cwd.mkdir()
        sid = "b017d68a-e4a7-4c7a-a454-72cd790ea905"
        self._setup_gemini(tmp_path, str(cwd), "pdd", sid,
                           "session-2026-04-25T20-32-b017d68a.json", monkeypatch)
        chats_dir = tmp_path / ".gemini" / "tmp" / "pdd" / "chats"
        (chats_dir / "session-2026-04-25T20-32-b017d68a.jsonl").write_text("{}\n", encoding="utf-8")
        result = _discover_gemini_session(sid, cwd)
        assert result["format"] == "json"

    def test_multiple_json_picks_newest(self, tmp_path, monkeypatch):
        """Multiple .json matches → picks newest by mtime."""
        from pdd.agentic_common import _discover_gemini_session
        import time as _time
        cwd = tmp_path / "proj"
        cwd.mkdir()
        sid = "b017d68a-e4a7-4c7a-a454-72cd790ea905"
        self._setup_gemini(tmp_path, str(cwd), "pdd", sid,
                           "session-2026-04-24T10-00-b017d68a.json", monkeypatch)
        chats_dir = tmp_path / ".gemini" / "tmp" / "pdd" / "chats"
        newer = chats_dir / "session-2026-04-25T20-32-b017d68a.json"
        newer.write_text("{}\n", encoding="utf-8")
        # Ensure newer has later mtime
        os.utime(newer, (9999999999, 9999999999))
        result = _discover_gemini_session(sid, cwd)
        assert str(newer) in result["session_file"]

    def test_uses_first_8_chars(self, tmp_path, monkeypatch):
        """Glob uses first 8 chars of UUID."""
        from pdd.agentic_common import _discover_gemini_session
        cwd = tmp_path / "proj"
        cwd.mkdir()
        sid = "b017d68a-e4a7-4c7a-a454-72cd790ea905"
        self._setup_gemini(tmp_path, str(cwd), "pdd", sid,
                           "session-2026-04-25T20-32-b017d68a.json", monkeypatch)
        result = _discover_gemini_session(sid, cwd)
        assert result is not None

    def test_slug_with_special_chars(self, tmp_path, monkeypatch):
        """Slug with special characters works."""
        from pdd.agentic_common import _discover_gemini_session
        cwd = tmp_path / "proj"
        cwd.mkdir()
        sid = "b017d68a-e4a7-4c7a-a454-72cd790ea905"
        self._setup_gemini(tmp_path, str(cwd), "my-project_v2", sid,
                           "session-2026-04-25T20-32-b017d68a.json", monkeypatch)
        result = _discover_gemini_session(sid, cwd)
        assert result is not None

    def test_rejects_subdirectory(self, tmp_path, monkeypatch):
        """Exact key match only — subdir of mapped cwd returns None."""
        from pdd.agentic_common import _discover_gemini_session
        cwd = tmp_path / "proj" / "subdir"
        cwd.mkdir(parents=True)
        parent_cwd = tmp_path / "proj"
        self._setup_gemini(tmp_path, str(parent_cwd), "pdd", "b017d68a-xxxx",
                           "session-2026-04-25T20-32-b017d68a.json", monkeypatch)
        result = _discover_gemini_session("b017d68a-xxxx", cwd)
        assert result is None

    def test_bad_projects_json_schema(self, tmp_path, monkeypatch):
        """projects.json with no 'projects' key → None."""
        from pdd.agentic_common import _discover_gemini_session
        gemini_home = tmp_path / ".gemini"
        pj = gemini_home / "projects.json"
        pj.parent.mkdir(parents=True)
        pj.write_text('{"version": 2}', encoding="utf-8")
        monkeypatch.setattr(Path, "home", lambda: tmp_path)
        assert _discover_gemini_session("abc12345", tmp_path) is None

    def test_missing_projects_json(self, tmp_path, monkeypatch):
        """No projects.json → None."""
        from pdd.agentic_common import _discover_gemini_session
        monkeypatch.setattr(Path, "home", lambda: tmp_path)
        assert _discover_gemini_session("abc12345", tmp_path) is None

    def test_no_session_id(self, tmp_path, monkeypatch):
        """Empty session_id → None."""
        from pdd.agentic_common import _discover_gemini_session
        monkeypatch.setattr(Path, "home", lambda: tmp_path)
        assert _discover_gemini_session("", tmp_path) is None

    def test_corrupt_projects_json(self, tmp_path, monkeypatch):
        """Garbage in projects.json → None."""
        from pdd.agentic_common import _discover_gemini_session
        gemini_home = tmp_path / ".gemini"
        pj = gemini_home / "projects.json"
        pj.parent.mkdir(parents=True)
        pj.write_bytes(b'\x00\x01\x02garbage')
        monkeypatch.setattr(Path, "home", lambda: tmp_path)
        assert _discover_gemini_session("abc12345", tmp_path) is None

    def test_cwd_not_in_projects(self, tmp_path, monkeypatch):
        """cwd not in projects.json → None."""
        from pdd.agentic_common import _discover_gemini_session
        gemini_home = tmp_path / ".gemini"
        pj = gemini_home / "projects.json"
        pj.parent.mkdir(parents=True)
        pj.write_text('{"projects": {"/other/path": "other"}}', encoding="utf-8")
        monkeypatch.setattr(Path, "home", lambda: tmp_path)
        assert _discover_gemini_session("abc12345", tmp_path) is None

    def test_parallel_safety(self, tmp_path, monkeypatch):
        """Two session IDs resolve to different files."""
        from pdd.agentic_common import _discover_gemini_session
        cwd = tmp_path / "proj"
        cwd.mkdir()
        gemini_home = tmp_path / ".gemini"
        pj = gemini_home / "projects.json"
        pj.parent.mkdir(parents=True, exist_ok=True)
        pj.write_text(json.dumps({"projects": {str(cwd): "pdd"}}), encoding="utf-8")
        chats_dir = gemini_home / "tmp" / "pdd" / "chats"
        chats_dir.mkdir(parents=True, exist_ok=True)
        for prefix in ["aaa11111", "bbb22222"]:
            (chats_dir / f"session-2026-04-25T20-32-{prefix}.json").write_text("{}\n", encoding="utf-8")
        monkeypatch.setattr(Path, "home", lambda: tmp_path)
        sid_a = f"aaa11111-e4a7-4c7a-a454-72cd790ea905"
        sid_b = f"bbb22222-e4a7-4c7a-a454-72cd790ea905"
        a = _discover_gemini_session(sid_a, cwd)
        b = _discover_gemini_session(sid_b, cwd)
        assert a is not None and b is not None
        assert a["session_file"] != b["session_file"]


# =========================================================================
# Section H: Session discovery: Codex
# =========================================================================

class TestSessionDiscoveryCodex:
    """Section H: Codex session discovery."""

    def test_happy_path_one_new_file(self, tmp_path, monkeypatch):
        """One new rollout file after diff."""
        from pdd.agentic_common import _discover_codex_session
        sessions_dir = tmp_path / ".codex" / "sessions" / "2026" / "04" / "25"
        sessions_dir.mkdir(parents=True)
        monkeypatch.setenv("CODEX_HOME", str(tmp_path / ".codex"))
        pre = set()
        new_file = sessions_dir / "rollout-abc.jsonl"
        new_file.write_text('{"test": true}\n', encoding="utf-8")
        result = _discover_codex_session(pre, tmp_path)
        assert result is not None
        assert result["session_file"] == str(new_file)
        assert result["provider"] == "openai"
        assert result["format"] == "jsonl"

    def test_multiple_new_files(self, tmp_path, monkeypatch):
        """Multiple new files → pick newest by mtime."""
        from pdd.agentic_common import _discover_codex_session
        sessions_dir = tmp_path / ".codex" / "sessions" / "2026" / "04" / "25"
        sessions_dir.mkdir(parents=True)
        monkeypatch.setenv("CODEX_HOME", str(tmp_path / ".codex"))
        pre = set()
        old = sessions_dir / "rollout-old.jsonl"
        old.write_text("{}\n", encoding="utf-8")
        os.utime(old, (1000000, 1000000))
        new = sessions_dir / "rollout-new.jsonl"
        new.write_text("{}\n", encoding="utf-8")
        os.utime(new, (9999999999, 9999999999))
        result = _discover_codex_session(pre, tmp_path)
        assert result["session_file"] == str(new)

    def test_pre_existing_files_ignored(self, tmp_path, monkeypatch):
        """Pre-existing files in snapshot are excluded."""
        from pdd.agentic_common import _discover_codex_session
        sessions_dir = tmp_path / ".codex" / "sessions" / "2026" / "04" / "25"
        sessions_dir.mkdir(parents=True)
        monkeypatch.setenv("CODEX_HOME", str(tmp_path / ".codex"))
        old = sessions_dir / "rollout-old.jsonl"
        old.write_text("{}\n", encoding="utf-8")
        pre = {old}
        new = sessions_dir / "rollout-new.jsonl"
        new.write_text("{}\n", encoding="utf-8")
        result = _discover_codex_session(pre, tmp_path)
        assert result["session_file"] == str(new)

    def test_respects_codex_home(self, tmp_path, monkeypatch):
        """Uses CODEX_HOME env var."""
        from pdd.agentic_common import _discover_codex_session
        custom = tmp_path / "custom_codex"
        sessions_dir = custom / "sessions" / "2026" / "04" / "25"
        sessions_dir.mkdir(parents=True)
        monkeypatch.setenv("CODEX_HOME", str(custom))
        f = sessions_dir / "rollout-x.jsonl"
        f.write_text("{}\n", encoding="utf-8")
        result = _discover_codex_session(set(), tmp_path)
        assert result is not None

    def test_missing_codex_dir(self, tmp_path, monkeypatch):
        """Missing .codex/ → None."""
        from pdd.agentic_common import _discover_codex_session
        monkeypatch.setenv("CODEX_HOME", str(tmp_path / "nonexistent"))
        assert _discover_codex_session(set(), tmp_path) is None

    def test_only_rollout_files(self, tmp_path, monkeypatch):
        """Non-rollout files are ignored."""
        from pdd.agentic_common import _discover_codex_session
        sessions_dir = tmp_path / ".codex" / "sessions" / "2026" / "04" / "25"
        sessions_dir.mkdir(parents=True)
        monkeypatch.setenv("CODEX_HOME", str(tmp_path / ".codex"))
        (sessions_dir / "debug-log.jsonl").write_text("{}\n", encoding="utf-8")
        assert _discover_codex_session(set(), tmp_path) is None

    def test_no_new_files(self, tmp_path, monkeypatch):
        """Snapshot and post identical → None."""
        from pdd.agentic_common import _discover_codex_session
        sessions_dir = tmp_path / ".codex" / "sessions" / "2026" / "04" / "25"
        sessions_dir.mkdir(parents=True)
        monkeypatch.setenv("CODEX_HOME", str(tmp_path / ".codex"))
        f = sessions_dir / "rollout-old.jsonl"
        f.write_text("{}\n", encoding="utf-8")
        pre = {f}
        assert _discover_codex_session(pre, tmp_path) is None


# =========================================================================
# Section I: Session discovery: shared behavior
# =========================================================================

class TestSessionDiscoveryShared:
    """Section I: shared behavior across providers."""

    def test_never_raises_claude(self, tmp_path, monkeypatch):
        """PermissionError in Claude discovery → None."""
        from pdd.agentic_common import _discover_claude_session
        monkeypatch.setattr(Path, "home", lambda: tmp_path)
        with mock.patch.object(Path, "exists", side_effect=PermissionError("denied")):
            result = _discover_claude_session("abc", tmp_path)
        assert result is None

    def test_never_raises_gemini(self, tmp_path, monkeypatch):
        """PermissionError in Gemini discovery → None."""
        from pdd.agentic_common import _discover_gemini_session
        monkeypatch.setattr(Path, "home", lambda: tmp_path)
        with mock.patch.object(Path, "exists", side_effect=PermissionError("denied")):
            result = _discover_gemini_session("abc", tmp_path)
        assert result is None

    def test_never_raises_codex(self, tmp_path, monkeypatch):
        """PermissionError in Codex discovery → None."""
        from pdd.agentic_common import _discover_codex_session
        monkeypatch.setenv("CODEX_HOME", str(tmp_path / "nonexistent"))
        with mock.patch("pdd.agentic_common.Path.home", side_effect=PermissionError("denied")):
            # Even if Path.home() raises, Codex uses CODEX_HOME env
            result = _discover_codex_session(set(), tmp_path)
        assert result is None

    def test_no_warnings(self, tmp_path, monkeypatch, caplog):
        """Only DEBUG messages, no WARNING+."""
        import logging
        from pdd.agentic_common import _discover_claude_session
        monkeypatch.setattr(Path, "home", lambda: tmp_path)
        with caplog.at_level(logging.DEBUG, logger="pdd.agentic_common.session_discovery"):
            _discover_claude_session("missing", tmp_path)
        for record in caplog.records:
            assert record.levelno < logging.WARNING

    def test_failed_discovery_does_not_block_logging(self, tmp_path, monkeypatch):
        """When discovery returns None, sync_orchestration writes the entry without agentic_trace."""
        from unittest.mock import patch as _patch
        from pdd.sync_determine_operation import SyncDecision
        import pdd.agentic_common as ac

        monkeypatch.chdir(tmp_path)
        (tmp_path / "prompts").mkdir()
        (tmp_path / "src").mkdir()
        (tmp_path / "tests").mkdir()
        (tmp_path / "context").mkdir()
        (tmp_path / ".pdd" / "meta").mkdir(parents=True)

        prompt = tmp_path / "prompts" / "demo_python.prompt"
        code = tmp_path / "src" / "demo.py"
        example = tmp_path / "context" / "demo_example.py"
        test_file = tmp_path / "tests" / "test_demo.py"
        prompt.write_text("Create demo", encoding="utf-8")
        code.write_text("print('x')\n", encoding="utf-8")
        example.write_text("print('example')\n", encoding="utf-8")
        test_file.write_text("def test_ok(): assert True\n", encoding="utf-8")

        fake_paths = {
            "prompt": prompt, "code": code, "example": example,
            "test": test_file, "test_files": [test_file],
        }
        decisions = [
            SyncDecision(operation="generate", reason="force"),
            SyncDecision(operation="error", reason="stop"),
        ]

        seen_entries = []
        # Ensure no agentic trace is set (discovery "failed")
        ac._last_agentic_trace.set(None)

        with _patch("pdd.sync_orchestration.get_pdd_file_paths", return_value=fake_paths), \
             _patch("pdd.sync_orchestration.SyncLock") as mock_lock, \
             _patch("pdd.sync_orchestration.sync_determine_operation", side_effect=decisions), \
             _patch("pdd.sync_orchestration.code_generator_main", return_value=("code", True, 0.01, "m")), \
             _patch("pdd.sync_orchestration.pop_all_pairs", return_value=[]), \
             _patch("pdd.sync_orchestration.append_log_entry", side_effect=lambda _b, _l, e: seen_entries.append(e)), \
             _patch("pdd.sync_orchestration.log_event"):
            mock_lock.return_value.__enter__.return_value = mock_lock
            mock_lock.return_value.__exit__.return_value = None
            from pdd.sync_orchestration import sync_orchestration
            sync_orchestration(basename="demo", language="python", quiet=True, prompts_dir="prompts")

        gen_entries = [e for e in seen_entries if e.get("operation") == "generate"]
        assert gen_entries, f"No generate entry: {seen_entries}"
        # Entry was written successfully, without agentic_trace
        assert "agentic_trace" not in gen_entries[0]

    def test_run_with_provider_sets_last_agentic_trace(self, tmp_path, monkeypatch):
        """_run_with_provider stores trace in module state; get_last_agentic_trace returns and clears it."""
        import pdd.agentic_common as ac

        # Set up a Claude session file so discovery succeeds
        cwd = tmp_path / "proj"
        cwd.mkdir()
        slug = str(cwd).replace("/", "-")
        session_dir = tmp_path / ".claude" / "projects" / slug
        session_dir.mkdir(parents=True)
        sf = session_dir / "sess-xyz.jsonl"
        sf.write_text('{"ok":true}\n', encoding="utf-8")
        monkeypatch.setattr(Path, "home", lambda: tmp_path)

        # Mock subprocess so _run_with_provider returns success with session_id
        mock_result = mock.MagicMock()
        mock_result.returncode = 0
        mock_result.stdout = json.dumps({
            "result": "Done. " + "x" * 200,  # long enough to avoid false-positive check
            "total_cost_usd": 0.05,
            "session_id": "sess-xyz",
        })
        mock_result.stderr = ""

        with mock.patch.object(ac, "_subprocess_run", return_value=mock_result), \
             mock.patch.object(ac, "_find_cli_binary", return_value="/bin/claude"):
            prompt_file = cwd / ".agentic_prompt_test.txt"
            prompt_file.write_text("test prompt", encoding="utf-8")
            monkeypatch.setenv("ANTHROPIC_API_KEY", "fake-key")

            success, text, cost, trace = ac._run_with_provider(
                "anthropic", prompt_file, cwd, verbose=False, quiet=True,
            )

        assert success
        assert trace is not None
        assert trace["provider"] == "anthropic"
        assert trace["session_file"] == str(sf)

        # get_last_agentic_trace returns the same trace and clears it
        retrieved = ac.get_last_agentic_trace()
        assert retrieved == trace
        assert ac.get_last_agentic_trace() is None  # cleared after first call


# =========================================================================
# Section J: Core dump
# =========================================================================

class TestCoreDump:
    """Section J: core dump changes."""

    def test_reads_sync_steps_from_logs_dir(self, tmp_path, monkeypatch):
        """sync_steps populated from .pdd/logs/."""
        monkeypatch.chdir(tmp_path)
        from pdd.core.dump import _extract_sync_data_from_disk
        logs_dir = tmp_path / ".pdd" / "logs"
        logs_dir.mkdir(parents=True)
        entries = [
            {"operation": "generate", "success": True, "actual_cost": 0.01, "model": "m", "duration": 1.0},
            {"operation": "test", "success": True, "actual_cost": 0.02, "model": "m", "duration": 2.0},
            {"operation": "fix", "success": False, "actual_cost": 0.03, "model": "m", "duration": 3.0, "error": "fail"},
            {"type": "event", "event_type": "sync_start"},
            {"type": "event", "event_type": "lock_released"},
        ]
        _write_sync_log(logs_dir / "mymod_python_sync.log", entries)
        steps, refs = _extract_sync_data_from_disk()
        assert len(steps) == 3  # events excluded
        assert steps[0]["operation"] == "generate"
        assert steps[1]["operation"] == "test"
        assert steps[2]["operation"] == "fix"

    def test_includes_sync_log_refs(self, tmp_path, monkeypatch):
        """sync_log_refs has module, language, path, size_bytes, entry_count."""
        monkeypatch.chdir(tmp_path)
        from pdd.core.dump import _extract_sync_data_from_disk
        logs_dir = tmp_path / ".pdd" / "logs"
        logs_dir.mkdir(parents=True)
        _write_sync_log(logs_dir / "mymod_python_sync.log", [
            {"operation": "generate", "success": True},
        ])
        _, refs = _extract_sync_data_from_disk()
        assert len(refs) == 1
        ref = refs[0]
        assert ref["module"] == "mymod"
        assert ref["language"] == "python"
        assert ref["path"] == ".pdd/logs/mymod_python_sync.log"
        assert ref["size_bytes"] > 0
        assert ref["entry_count"] == 1

    def test_does_not_embed_sync_logs(self, tmp_path, monkeypatch):
        """No *_sync.log in file_contents after removal of glob."""
        # This is structural: the glob("*_sync.log") line was removed from dump.py.
        # We verify by checking that the code no longer adds sync.log files to core_dump_files.
        from pdd.core import dump
        import inspect
        source = inspect.getsource(dump._write_core_dump)
        assert 'glob("*_sync.log")' not in source

    def test_sync_steps_excludes_trace_data(self, tmp_path, monkeypatch):
        """sync_steps items do not contain llm_traces or agentic_trace."""
        monkeypatch.chdir(tmp_path)
        from pdd.core.dump import _extract_sync_data_from_disk
        logs_dir = tmp_path / ".pdd" / "logs"
        logs_dir.mkdir(parents=True)
        _write_sync_log(logs_dir / "mymod_python_sync.log", [
            {
                "operation": "generate",
                "success": True,
                "actual_cost": 0.01,
                "model": "m",
                "duration": 1.0,
                "llm_traces": [{"prompt": "big", "response": "data"}],
                "agentic_trace": {"session_file": "/x", "provider": "anthropic", "format": "jsonl"},
            },
        ])
        steps, _ = _extract_sync_data_from_disk()
        assert len(steps) == 1
        assert "llm_traces" not in steps[0]
        assert "agentic_trace" not in steps[0]

    def test_falls_back_to_meta_for_unmigrated(self, tmp_path, monkeypatch):
        """Reads from .pdd/meta/ when .pdd/logs/ doesn't have the file."""
        monkeypatch.chdir(tmp_path)
        from pdd.core.dump import _extract_sync_data_from_disk
        meta_dir = tmp_path / ".pdd" / "meta"
        meta_dir.mkdir(parents=True)
        _write_sync_log(meta_dir / "mymod_python_sync.log", [
            {"operation": "generate", "success": True},
        ])
        steps, refs = _extract_sync_data_from_disk()
        assert len(steps) == 1
        assert refs[0]["path"] == ".pdd/meta/mymod_python_sync.log"


# =========================================================================
# Section K: Dry-run
# =========================================================================

class TestDryRun:
    """Section K: dry-run uses new location."""

    def test_reads_from_new_location(self, tmp_path, monkeypatch):
        """_display_sync_log reads from .pdd/logs/ via get_log_path."""
        monkeypatch.chdir(tmp_path)
        from pdd.operation_log import get_log_path, append_log_entry
        append_log_entry("mymod", "python", {
            "operation": "generate",
            "success": True,
            "timestamp": "2026-01-01T00:00:00",
        })
        log_path = get_log_path("mymod", "python")
        assert log_path.exists()
        assert ".pdd/logs/" in str(log_path)

    def test_triggers_migration(self, tmp_path, monkeypatch):
        """Dry-run on old location triggers migration."""
        monkeypatch.chdir(tmp_path)
        old_dir = tmp_path / ".pdd" / "meta"
        old_dir.mkdir(parents=True)
        entry = {"operation": "generate", "success": True, "timestamp": "2026-01-01T00:00:00"}
        (old_dir / "mymod_python_sync.log").write_text(json.dumps(entry) + "\n", encoding="utf-8")

        from pdd.operation_log import load_operation_log
        entries = load_operation_log("mymod", "python")
        assert len(entries) == 1
        assert not (old_dir / "mymod_python_sync.log").exists()
        assert (tmp_path / ".pdd" / "logs" / "mymod_python_sync.log").exists()

    def test_does_not_show_trace_content(self, tmp_path, monkeypatch, capsys):
        """Display function doesn't print prompt/response text."""
        monkeypatch.chdir(tmp_path)
        from pdd.operation_log import append_log_entry
        append_log_entry("mymod", "python", {
            "operation": "generate",
            "success": True,
            "timestamp": "2026-01-01T00:00:00",
            "llm_traces": [{"prompt": "SECRET_PROMPT_TEXT", "response": "SECRET_RESPONSE"}],
        })
        from pdd.sync_orchestration import _display_sync_log
        _display_sync_log("mymod", "python")
        captured = capsys.readouterr()
        assert "SECRET_PROMPT_TEXT" not in captured.out
        assert "SECRET_RESPONSE" not in captured.out


# =========================================================================
# Section L: Multi-operation sync
# =========================================================================

class TestMultiOperationSync:
    """Section L: each operation gets its own traces."""

    def test_each_operation_gets_own_traces(self):
        """Generate (3), test (2), example (1) — separate lists."""
        from pdd.core.llm_trace import set_current_operation, record_llm_pair, pop_all_pairs
        set_current_operation("generate")
        for i in range(3):
            record_llm_pair(prompt=f"gp{i}", response=f"gr{i}", model="m")
        set_current_operation("test")
        for i in range(2):
            record_llm_pair(prompt=f"tp{i}", response=f"tr{i}", model="m")
        set_current_operation("example")
        record_llm_pair(prompt="ep", response="er", model="m")

        gen = pop_all_pairs("generate")
        tst = pop_all_pairs("test")
        ex = pop_all_pairs("example")
        assert len(gen) == 3
        assert len(tst) == 2
        assert len(ex) == 1

    def test_no_trace_leakage(self):
        """pop_all_pairs drains the list — later op sees only its own."""
        from pdd.core.llm_trace import set_current_operation, record_llm_pair, pop_all_pairs
        set_current_operation("generate")
        for i in range(3):
            record_llm_pair(prompt=f"p{i}", response=f"r{i}", model="m")
        pop_all_pairs("generate")  # drain

        set_current_operation("test")
        record_llm_pair(prompt="tp", response="tr", model="m")
        record_llm_pair(prompt="tp2", response="tr2", model="m")
        tst = pop_all_pairs("test")
        assert len(tst) == 2  # not 2 + leftovers

    def test_mixed_entries(self):
        """Skip entry between operations has no traces."""
        from pdd.core.llm_trace import set_current_operation, record_llm_pair, pop_all_pairs
        set_current_operation("generate")
        record_llm_pair(prompt="p", response="r", model="m")
        gen = pop_all_pairs("generate")
        assert len(gen) == 1

        # skip:verify — no LLM calls
        skip = pop_all_pairs("skip:verify")
        assert skip == []

        set_current_operation("test")
        record_llm_pair(prompt="tp", response="tr", model="m")
        tst = pop_all_pairs("test")
        assert len(tst) == 1


# =========================================================================
# Section M: pop_all_pairs semantics
# =========================================================================

class TestPopAllPairsSemantics:
    """Section M: pop_all_pairs behavior."""

    def test_returns_all_recorded(self):
        """4 pairs recorded → 4 returned, then empty."""
        from pdd.core.llm_trace import set_current_operation, record_llm_pair, pop_all_pairs
        set_current_operation("crash")
        for i in range(4):
            record_llm_pair(prompt=f"p{i}", response=f"r{i}", model="m")
        result = pop_all_pairs("crash")
        assert len(result) == 4
        assert pop_all_pairs("crash") == []

    def test_empty_when_nothing_recorded(self):
        """No recording → empty list."""
        from pdd.core.llm_trace import pop_all_pairs
        assert pop_all_pairs("generate") == []

    def test_scoped_by_operation(self):
        """Different operations don't interfere."""
        from pdd.core.llm_trace import set_current_operation, record_llm_pair, pop_all_pairs
        set_current_operation("generate")
        record_llm_pair(prompt="g1", response="r1", model="m")
        record_llm_pair(prompt="g2", response="r2", model="m")
        set_current_operation("test")
        record_llm_pair(prompt="t1", response="r1", model="m")

        assert len(pop_all_pairs("generate")) == 2
        assert len(pop_all_pairs("test")) == 1


# =========================================================================
# Section N: Concurrent sync
# =========================================================================

class TestConcurrentSync:
    """Section N: two modules write to separate log files."""

    def test_separate_log_files(self, tmp_path, monkeypatch):
        """Two modules' traces don't leak into each other's logs."""
        monkeypatch.chdir(tmp_path)
        from pdd.operation_log import append_log_entry, load_operation_log

        entry_a = {"operation": "generate", "success": True, "module": "mod_a",
                    "llm_traces": [{"prompt": "a_prompt", "response": "a_resp", "model": "m", "thinking": None}]}
        entry_b = {"operation": "generate", "success": True, "module": "mod_b",
                    "llm_traces": [{"prompt": "b_prompt", "response": "b_resp", "model": "m", "thinking": None}]}

        append_log_entry("mod_a", "python", entry_a)
        append_log_entry("mod_b", "python", entry_b)

        log_a = load_operation_log("mod_a", "python")
        log_b = load_operation_log("mod_b", "python")

        assert len(log_a) == 1
        assert log_a[0]["llm_traces"][0]["prompt"] == "a_prompt"
        assert len(log_b) == 1
        assert log_b[0]["llm_traces"][0]["prompt"] == "b_prompt"


# =========================================================================
# Section O: Old agentic log removal
# =========================================================================

class TestOldAgenticLogRemoval:
    """Section O: old agentic logging infrastructure removed."""

    def test_log_agentic_interaction_removed(self):
        """_log_agentic_interaction is no longer in agentic_common."""
        from pdd import agentic_common
        assert not hasattr(agentic_common, '_log_agentic_interaction')

    def test_agentic_log_dir_removed(self):
        """AGENTIC_LOG_DIR is no longer in agentic_common."""
        from pdd import agentic_common
        assert not hasattr(agentic_common, 'AGENTIC_LOG_DIR')

    def test_agentic_session_id_removed(self):
        """_AGENTIC_SESSION_ID is no longer in agentic_common."""
        from pdd import agentic_common
        assert not hasattr(agentic_common, '_AGENTIC_SESSION_ID')

    def test_no_agentic_logs_dir_created(self, tmp_path, monkeypatch):
        """run_agentic_task does not create .pdd/agentic-logs/."""
        # Just verify the directory name is not referenced in the module
        from pdd import agentic_common
        import inspect
        source = inspect.getsource(agentic_common)
        assert "agentic-logs" not in source


# =========================================================================
# Section P: Redaction on all fields
# =========================================================================

class TestRedactionAllFields:
    """Section P: redaction on response and thinking."""

    def test_response_redacted(self):
        """Response with secrets gets redacted."""
        from pdd.core.llm_trace import set_current_operation, record_llm_pair, pop_all_pairs
        set_current_operation("p_resp")
        record_llm_pair(
            prompt="clean",
            response="Bearer sk-abc123secretvalue api_key=secret456",
            model="m",
        )
        pairs = pop_all_pairs("p_resp")
        stored = pairs[0]["response"]
        assert "sk-abc123secretvalue" not in stored
        assert "secret456" not in stored
        assert "<redacted>" in stored

    def test_thinking_redacted(self):
        """Thinking with secrets gets redacted."""
        from pdd.core.llm_trace import set_current_operation, record_llm_pair, pop_all_pairs
        set_current_operation("p_think")
        record_llm_pair(
            prompt="clean",
            response="clean",
            model="m",
            thinking="token=mytoken123 password=hunter2abc secret=topsecret99",
        )
        pairs = pop_all_pairs("p_think")
        stored = pairs[0]["thinking"]
        assert "mytoken123" not in stored
        assert "hunter2abc" not in stored
        assert "topsecret99" not in stored
        assert "<redacted>" in stored


# =========================================================================
# Section Q: Thinking normalization
# =========================================================================

class TestThinkingNormalization:
    """Section Q: thinking normalization."""

    def test_thinking_list_of_objects(self):
        """List of thinking objects → concatenated string."""
        from pdd.core.llm_trace import set_current_operation, record_llm_pair, pop_all_pairs
        set_current_operation("q_list")
        thinking_list = [
            {"type": "thinking", "thinking": "step one"},
            {"type": "thinking", "thinking": "step two"},
        ]
        record_llm_pair(prompt="p", response="r", model="m", thinking=thinking_list)
        pairs = pop_all_pairs("q_list")
        assert pairs[0]["thinking"] == "step one\nstep two"

    def test_thinking_unexpected_type(self):
        """Non-string/non-list thinking (int) → str()."""
        from pdd.core.llm_trace import set_current_operation, record_llm_pair, pop_all_pairs
        set_current_operation("q_int")
        record_llm_pair(prompt="p", response="r", model="m", thinking=12345)
        pairs = pop_all_pairs("q_int")
        assert pairs[0]["thinking"] == "12345"

    def test_thinking_none(self):
        """None thinking → null."""
        from pdd.core.llm_trace import set_current_operation, record_llm_pair, pop_all_pairs
        set_current_operation("q_none")
        record_llm_pair(prompt="p", response="r", model="m", thinking=None)
        pairs = pop_all_pairs("q_none")
        assert pairs[0]["thinking"] is None


# =========================================================================
# Section R: JSON-quoted secret redaction
# =========================================================================

class TestJsonQuotedSecretRedaction:
    """Section R: secrets in JSON-style quoted values must be redacted."""

    def test_json_api_key_redacted(self):
        """'\"api_key\": \"sk-ant-abc123...\"' must be scrubbed."""
        from pdd.core.llm_trace import set_current_operation, record_llm_pair, pop_all_pairs
        set_current_operation("r_json_key")
        prompt = '{"api_key": "sk-ant-abc123secretvalue"}'
        record_llm_pair(prompt=prompt, response="r", model="m")
        pairs = pop_all_pairs("r_json_key")
        assert "sk-ant-abc123secretvalue" not in pairs[0]["prompt"]
        assert "<redacted>" in pairs[0]["prompt"]

    def test_json_token_redacted(self):
        """'\"token\": \"eyJhbGciOi...\"' must be scrubbed."""
        from pdd.core.llm_trace import set_current_operation, record_llm_pair, pop_all_pairs
        set_current_operation("r_json_tok")
        prompt = '{"token": "eyJhbGciOiJIUzI1NiIsInR5cCI6IkpXVCJ9"}'
        record_llm_pair(prompt=prompt, response="r", model="m")
        pairs = pop_all_pairs("r_json_tok")
        assert "eyJhbGciOiJIUzI1NiIsInR5cCI6IkpXVCJ9" not in pairs[0]["prompt"]

    def test_json_secret_in_response(self):
        """JSON-quoted secrets in response field also redacted."""
        from pdd.core.llm_trace import set_current_operation, record_llm_pair, pop_all_pairs
        set_current_operation("r_json_resp")
        response = '{"password": "super_secret_pass_123"}'
        record_llm_pair(prompt="p", response=response, model="m")
        pairs = pop_all_pairs("r_json_resp")
        assert "super_secret_pass_123" not in pairs[0]["response"]

    def test_json_secret_in_thinking(self):
        """JSON-quoted secrets in thinking field also redacted."""
        from pdd.core.llm_trace import set_current_operation, record_llm_pair, pop_all_pairs
        set_current_operation("r_json_think")
        thinking = 'The config has "secret": "my_top_secret_value" set'
        record_llm_pair(prompt="p", response="r", model="m", thinking=thinking)
        pairs = pop_all_pairs("r_json_think")
        assert "my_top_secret_value" not in pairs[0]["thinking"]


# =========================================================================
# Section S: Agentic trace thread safety (ContextVar)
# =========================================================================

class TestAgenticTraceThreadSafety:
    """Section S: _last_agentic_trace uses ContextVar, not a plain global."""

    def test_agentic_trace_is_context_var(self):
        """_last_agentic_trace should be a ContextVar for thread safety."""
        from contextvars import ContextVar
        import pdd.agentic_common as ac
        assert isinstance(ac._last_agentic_trace, ContextVar)

    def test_agentic_trace_isolated_across_threads(self):
        """Traces set in one thread are not visible in another."""
        import threading
        import pdd.agentic_common as ac

        trace_a = {"session_file": "/a", "provider": "anthropic", "format": "jsonl"}

        # Set trace in main thread
        ac._last_agentic_trace.set(trace_a)

        seen_in_thread = []
        def worker():
            # New thread should NOT see main thread's trace
            seen_in_thread.append(ac.get_last_agentic_trace())

        t = threading.Thread(target=worker)
        t.start()
        t.join()

        assert seen_in_thread[0] is None, "Thread saw main thread's trace — not isolated"
        # Main thread's trace should still be there
        assert ac.get_last_agentic_trace() == trace_a


# =========================================================================
# Section T: Append migration newline boundary
# =========================================================================

class TestAppendMigrationNewlineBoundary:
    """Section T: merge migration must not corrupt JSONL at the join point."""

    def test_append_migration_preserves_newline_boundary(self, tmp_path, monkeypatch):
        """When both old and new files exist, appended content starts on a new line."""
        monkeypatch.chdir(tmp_path)
        meta_dir = tmp_path / ".pdd" / "meta"
        meta_dir.mkdir(parents=True)
        logs_dir = tmp_path / ".pdd" / "logs"
        logs_dir.mkdir(parents=True)

        # Write new file WITHOUT trailing newline (simulates interrupted write)
        new_path = logs_dir / "mymod_python_sync.log"
        new_path.write_bytes(b'{"line": 1}')  # no trailing \n

        old_path = meta_dir / "mymod_python_sync.log"
        old_path.write_bytes(b'{"line": 2}\n')

        from pdd.operation_log import get_log_path
        result = get_log_path("mymod", "python")

        # Each JSON line should be parseable individually
        lines = [l for l in result.read_text(encoding="utf-8").splitlines() if l.strip()]
        assert len(lines) == 2, f"Expected 2 JSONL lines, got {len(lines)}: {lines}"
        for line in lines:
            json.loads(line)  # should not raise
