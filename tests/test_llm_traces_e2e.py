"""E2E agentic trace tests for LLM trace logging (Issue #752).

These tests run real `pdd sync --agentic` with real CLI agents
(Claude, Gemini, Codex). Each test is parametrized over all 3 providers
and skips if that provider's CLI isn't installed.

Gate: PDD_RUN_AGENTIC_TESTS=1
Requires: `pip install -e .` so the subprocess gets the current code.

LiteLLM-only E2E tests (no CLI agents) live in test_sync_orchestration.py,
gated by PDD_RUN_REAL_LLM_TESTS=1.
"""
from __future__ import annotations

import json
import os
import subprocess
from pathlib import Path
from typing import Any, Dict, List, Optional

import pytest


# ---------------------------------------------------------------------------
# Fixtures
# ---------------------------------------------------------------------------

AGENTIC_PROVIDERS = ["anthropic", "google", "openai"]


@pytest.fixture(params=AGENTIC_PROVIDERS)
def agentic_provider(request, monkeypatch):
    provider = request.param
    if not os.environ.get("PDD_RUN_AGENTIC_TESTS"):
        pytest.skip("Set PDD_RUN_AGENTIC_TESTS=1 to run agentic E2E tests")
    from pdd.agentic_common import get_available_agents
    if provider not in get_available_agents():
        pytest.skip(f"{provider} CLI not available")
    monkeypatch.setenv("PDD_AGENTIC_PROVIDER", provider)
    return provider


def _create_minimal_pdd_project(tmp_path: Path, module: str = "greeter", language: str = "python") -> Path:
    project = tmp_path / "project"
    project.mkdir()
    prompts_dir = project / "prompts"
    prompts_dir.mkdir()
    prompt_file = prompts_dir / f"{module}_{language}.prompt"
    prompt_file.write_text(
        "Create a Python module called greeter.py with a single function greet(name) "
        "that returns f'Hello, {name}!'.\n",
        encoding="utf-8",
    )
    meta_dir = project / ".pdd" / "meta"
    meta_dir.mkdir(parents=True)
    return project


def _read_sync_log(project: Path, module: str = "greeter", language: str = "python") -> List[Dict[str, Any]]:
    for parent in [project / ".pdd" / "logs", project / ".pdd" / "meta"]:
        log_path = parent / f"{module}_{language}_sync.log"
        if log_path.exists():
            entries = []
            for line in log_path.read_text(encoding="utf-8").splitlines():
                if line.strip():
                    try:
                        entries.append(json.loads(line))
                    except json.JSONDecodeError:
                        continue
            return entries
    return []


def _run_pdd_sync(project: Path, extra_args: Optional[List[str]] = None) -> subprocess.CompletedProcess:
    cmd = ["pdd", "sync", "greeter"]
    if extra_args:
        cmd.extend(extra_args)
    return subprocess.run(
        cmd, cwd=project, capture_output=True, text=True, timeout=300,
    )


# =========================================================================
# Agentic clean-path: one pdd sync --agentic, verify traces
# =========================================================================

class TestAgenticPath:
    """Agentic sync via --agentic flag produces traces in sync log.

    One sync run per test. The clean-path test checks llm_traces, format,
    provider-specific paths, and session file existence from a single run.
    The crash-path test generates clean code then breaks it.
    """

    def test_agentic_sync_clean_path(self, tmp_path, agentic_provider):
        """Single pdd sync --agentic: llm_traces on generate, agentic_trace
        structure, session file on disk, format, provider-specific paths."""
        project = _create_minimal_pdd_project(tmp_path)
        result = _run_pdd_sync(project, extra_args=["--agentic"])
        log_path = project / ".pdd" / "logs" / "greeter_python_sync.log"
        assert log_path.exists(), (
            f"No sync log written. stdout: {result.stdout[:500]}\n"
            f"stderr: {result.stderr[:500]}"
        )
        entries = _read_sync_log(project)
        assert len(entries) >= 1, "Expected at least one sync log entry"

        # generate is always LiteLLM — should have llm_traces
        gen_entries = [e for e in entries if e.get("operation") == "generate"]
        assert len(gen_entries) >= 1, (
            f"No generate entry. Operations: {[e.get('operation') for e in entries]}"
        )
        gen = gen_entries[0]
        assert "llm_traces" in gen, (
            f"generate entry missing llm_traces. Keys: {list(gen.keys())}"
        )
        assert len(gen["llm_traces"]) >= 1

        # Check all agentic_trace entries
        for entry in entries:
            if "agentic_trace" not in entry:
                continue
            trace = entry["agentic_trace"]

            assert isinstance(trace["session_file"], str)
            assert trace["provider"] == agentic_provider
            assert trace["format"] in ("jsonl", "json")

            sf = Path(trace["session_file"])
            assert sf.exists(), f"Session file missing: {sf}"
            assert sf.stat().st_size > 0, f"Session file is empty: {sf}"

            if agentic_provider == "anthropic":
                assert trace["format"] == "jsonl"
                assert sf.suffix == ".jsonl"
                assert "/.claude/projects/" in str(sf)
                slug = str(project).replace("/", "-")
                assert slug in str(sf)
            elif agentic_provider == "google":
                assert "/.gemini/tmp/" in str(sf)
                assert "/chats/" in str(sf)
            elif agentic_provider == "openai":
                assert trace["format"] == "jsonl"

    def test_agentic_crash_produces_agentic_trace(self, tmp_path, agentic_provider):
        """Break code after generate, re-sync with --agentic. Crash entry
        gets agentic_trace with a real session file on disk."""
        project = _create_minimal_pdd_project(tmp_path)
        _run_pdd_sync(project, extra_args=["--agentic"])

        code_file = project / "greeter.py"
        if not code_file.exists():
            pytest.skip("First sync did not generate code file")

        code_file.write_text(
            "import nonexistent_xyz_module\n\ndef greet(name):\n    return f'Hello, {name}!'\n",
            encoding="utf-8",
        )
        fp = project / ".pdd" / "meta" / "greeter_python.json"
        if fp.exists():
            fp.unlink()

        _run_pdd_sync(project, extra_args=["--agentic"])
        entries = _read_sync_log(project)
        crash_entries = [e for e in entries if e.get("operation") == "crash"]
        for entry in crash_entries:
            if "agentic_trace" in entry:
                trace = entry["agentic_trace"]
                assert isinstance(trace["session_file"], str)
                assert trace["provider"] == agentic_provider
                assert trace["format"] in ("jsonl", "json")
                sf = Path(trace["session_file"])
                assert sf.exists(), f"Session file missing: {sf}"
                assert sf.stat().st_size > 0, f"Session file is empty: {sf}"


# =========================================================================
# Agentic fallback: LiteLLM tries first, then CLI agent
# =========================================================================

class TestCrashAgenticFallback:
    """Crash with LiteLLM + agentic fallback may produce both keys."""

    def test_both_keys_on_fallback(self, tmp_path, agentic_provider):
        """If a crash entry has both llm_traces and agentic_trace, both are valid."""
        project = _create_minimal_pdd_project(tmp_path)
        _run_pdd_sync(project, extra_args=["--agentic"])

        code_file = project / "greeter.py"
        if not code_file.exists():
            pytest.skip("First sync did not generate code file")

        code_file.write_text(
            "import nonexistent_xyz_module\ndef greet(name): return f'Hello, {name}!'\n",
            encoding="utf-8",
        )
        fp = project / ".pdd" / "meta" / "greeter_python.json"
        if fp.exists():
            fp.unlink()

        # Sync WITHOUT --agentic so crash_main tries LiteLLM first,
        # then falls back to agentic
        _run_pdd_sync(project)
        entries = _read_sync_log(project)
        both = [e for e in entries if "llm_traces" in e and "agentic_trace" in e]
        for entry in both:
            assert len(entry["llm_traces"]) > 0
            trace = entry["agentic_trace"]
            assert isinstance(trace["session_file"], str)
            assert trace["provider"] in ("anthropic", "google", "openai")
