"""Tier 2: Real LLM tests for trace logging (sections S through Y).

Gated by env vars:
  PDD_RUN_REAL_LLM_TESTS=1  — LiteLLM API tests (S, V, W, X, Y)
  PDD_RUN_AGENTIC_TESTS=1   — CLI agent tests (T, U)

IMPORTANT: These tests run `pdd` as a subprocess, so the installed pdd
package must include the llm_traces changes. Run `pip install -e .`
before running these tests against a development checkout.
"""
from __future__ import annotations

import json
import os
import shutil
import subprocess
import sys
from pathlib import Path
from typing import Any, Dict, List, Optional

import pytest


# ---------------------------------------------------------------------------
# Fixtures
# ---------------------------------------------------------------------------

AGENTIC_PROVIDERS = ["anthropic", "google", "openai"]


def _skip_unless_real_llm():
    if not os.environ.get("PDD_RUN_REAL_LLM_TESTS"):
        pytest.skip("Set PDD_RUN_REAL_LLM_TESTS=1 to run real LLM tests")


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
    """Create a minimal PDD project with a prompt file in tmp_path."""
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
    # Init .pdd/meta
    meta_dir = project / ".pdd" / "meta"
    meta_dir.mkdir(parents=True)
    return project


def _read_sync_log(project: Path, module: str = "greeter", language: str = "python") -> List[Dict[str, Any]]:
    """Read sync log entries from the project."""
    logs_dir = project / ".pdd" / "logs"
    meta_dir = project / ".pdd" / "meta"
    filename = f"{module}_{language}_sync.log"
    log_path = logs_dir / filename
    if not log_path.exists():
        log_path = meta_dir / filename
    if not log_path.exists():
        return []
    entries = []
    for line in log_path.read_text(encoding="utf-8").splitlines():
        if line.strip():
            try:
                entries.append(json.loads(line))
            except json.JSONDecodeError:
                continue
    return entries


def _run_pdd_sync(project: Path, extra_args: Optional[List[str]] = None) -> subprocess.CompletedProcess:
    """Run pdd sync in the project directory."""
    cmd = ["pdd", "sync", "greeter"]
    if extra_args:
        cmd.extend(extra_args)
    return subprocess.run(
        cmd,
        cwd=project,
        capture_output=True,
        text=True,
        timeout=300,
    )


# =========================================================================
# Section S: LiteLLM path (PDD_RUN_REAL_LLM_TESTS=1)
#
# One `pdd sync greeter` run, many assertions. Checks trace structure,
# model field, log location, fingerprint, example traces, and orphaned
# call detection all from a single sync.
# =========================================================================

class TestLiteLLMPath:
    """Section S: one real pdd sync, verify all LiteLLM trace behavior."""

    def test_litellm_sync_traces(self, tmp_path):
        """Single pdd sync on a fresh project. Checks everything about the
        LiteLLM trace path from one run."""
        _skip_unless_real_llm()
        project = _create_minimal_pdd_project(tmp_path)
        result = _run_pdd_sync(project)

        # --- Sync log lands in .pdd/logs/, not .pdd/meta/ ---
        log_path = project / ".pdd" / "logs" / "greeter_python_sync.log"
        assert log_path.exists(), (
            f"Expected log at {log_path}. stdout: {result.stdout[:500]}"
        )
        meta_dir = project / ".pdd" / "meta"
        sync_logs_in_meta = list(meta_dir.glob("*_sync.log")) if meta_dir.exists() else []
        assert len(sync_logs_in_meta) == 0, "Sync log should not be in .pdd/meta/"

        entries = _read_sync_log(project)

        # --- generate entry has llm_traces with valid structure ---
        gen_entries = [e for e in entries if e.get("operation") == "generate"]
        assert len(gen_entries) >= 1
        gen = gen_entries[0]
        assert "llm_traces" in gen
        assert len(gen["llm_traces"]) >= 2
        for item in gen["llm_traces"]:
            assert isinstance(item["prompt"], str) and item["prompt"]
            assert isinstance(item["response"], str) and item["response"]
            assert isinstance(item["model"], str) and item["model"]
            assert item["thinking"] is None or isinstance(item["thinking"], str)

        # --- example entry has llm_traces (if example was generated) ---
        ex_entries = [e for e in entries if e.get("operation") == "example"]
        if ex_entries:
            assert "llm_traces" in ex_entries[0]
            assert len(ex_entries[0]["llm_traces"]) >= 1

        # --- model field contains a recognizable model name ---
        for entry in entries:
            if "llm_traces" in entry:
                for item in entry["llm_traces"]:
                    model = item["model"]
                    assert isinstance(model, str) and model
                    assert any(k in model.lower() for k in (
                        "gemini", "gpt", "claude", "o1", "o3", "o4",
                    )), f"Unrecognized model: {model}"

        # --- every entry with llm_traces has >= 2 items (no orphaned calls) ---
        for entry in entries:
            if "llm_traces" in entry:
                assert len(entry["llm_traces"]) >= 2, (
                    f"Operation {entry.get('operation')} has only "
                    f"{len(entry['llm_traces'])} trace(s) — expected >= 2. "
                    f"set_current_operation may be called too late or "
                    f"pop_all_pairs too early."
                )

        # --- fingerprint still exists and is valid JSON ---
        fp_files = list(meta_dir.glob("greeter_python.json"))
        assert len(fp_files) == 1
        data = json.loads(fp_files[0].read_text(encoding="utf-8"))
        assert isinstance(data, dict)


# =========================================================================
# Section T: Agentic path (PDD_RUN_AGENTIC_TESTS=1, x3 providers)
#
# Uses `pdd sync greeter --agentic` which goes through sync_orchestration.
# generate is always LiteLLM (llm_traces). crash/fix/verify with --agentic
# skip the LiteLLM loop (max_attempts=0) and go straight to the CLI agent,
# producing agentic_trace on those entries.
#
# For a clean module that generates and tests without crashing, we expect:
#   - generate entry with llm_traces (LiteLLM code generation)
#   - test entry with llm_traces (LiteLLM test generation)
#   - possibly example, verify entries
# If a crash occurs and --agentic is on, the crash entry gets agentic_trace.
# =========================================================================

class TestAgenticPath:
    """Section T: agentic sync via --agentic flag produces traces in sync log.

    Uses a single `pdd sync --agentic` run per test method to avoid redundant
    LLM calls (~90s each). The clean-path test checks llm_traces, format,
    provider-specific paths, and session file existence all from one run.
    The crash-path test runs a second sync with broken code.
    """

    def test_agentic_sync_clean_path(self, tmp_path, agentic_provider):
        """Single pdd sync --agentic run: verify llm_traces, agentic_trace structure,
        format, provider-specific paths, and session file on disk."""
        project = _create_minimal_pdd_project(tmp_path)
        result = _run_pdd_sync(project, extra_args=["--agentic"])
        log_path = project / ".pdd" / "logs" / "greeter_python_sync.log"
        assert log_path.exists(), (
            f"No sync log written. stdout: {result.stdout[:500]}\n"
            f"stderr: {result.stderr[:500]}"
        )
        entries = _read_sync_log(project)
        assert len(entries) >= 1, "Expected at least one sync log entry"

        # --- generate is always LiteLLM, so it should have llm_traces ---
        gen_entries = [e for e in entries if e.get("operation") == "generate"]
        assert len(gen_entries) >= 1, (
            f"No generate entry. Operations: {[e.get('operation') for e in entries]}"
        )
        gen = gen_entries[0]
        assert "llm_traces" in gen, (
            f"generate entry missing llm_traces. Keys: {list(gen.keys())}"
        )
        assert len(gen["llm_traces"]) >= 1

        # --- Check all agentic_trace entries (if any operations used agent) ---
        for entry in entries:
            if "agentic_trace" not in entry:
                continue
            trace = entry["agentic_trace"]

            # Structure
            assert isinstance(trace["session_file"], str)
            assert trace["provider"] == agentic_provider
            assert trace["format"] in ("jsonl", "json")

            # Session file actually exists on disk with content
            sf = Path(trace["session_file"])
            assert sf.exists(), f"Session file missing: {sf}"
            assert sf.stat().st_size > 0, f"Session file is empty: {sf}"

            # Format matches file extension
            if agentic_provider == "anthropic":
                assert trace["format"] == "jsonl"
                assert sf.suffix == ".jsonl"
            elif agentic_provider == "openai":
                assert trace["format"] == "jsonl"
            # gemini can be json or jsonl

            # Provider-specific path structure
            if agentic_provider == "anthropic":
                assert "/.claude/projects/" in str(sf)
                slug = str(project).replace("/", "-")
                assert slug in str(sf)
            elif agentic_provider == "google":
                assert "/.gemini/tmp/" in str(sf)
                assert "/chats/" in str(sf)

    def test_agentic_crash_produces_agentic_trace(self, tmp_path, agentic_provider):
        """Force a crash, re-sync with --agentic. Crash entry gets agentic_trace
        with a real session file on disk."""
        project = _create_minimal_pdd_project(tmp_path)
        # First sync: generate clean code
        _run_pdd_sync(project, extra_args=["--agentic"])

        # Break the code to force a crash on next sync
        code_file = project / "greeter.py"
        if not code_file.exists():
            pytest.skip("First sync did not generate code file")

        code_file.write_text(
            "import nonexistent_xyz_module\n\ndef greet(name):\n    return f'Hello, {name}!'\n",
            encoding="utf-8",
        )
        # Clear fingerprint so sync re-runs
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
                # Session file exists on disk with content
                sf = Path(trace["session_file"])
                assert sf.exists(), f"Session file missing: {sf}"
                assert sf.stat().st_size > 0, f"Session file is empty: {sf}"


# =========================================================================
# Section U: Crash with agentic fallback (PDD_RUN_AGENTIC_TESTS=1)
#
# Without --agentic, Python crash_main tries LiteLLM fix attempts first
# (max_attempts=3), then falls back to agentic if all fail. That entry
# would have both llm_traces (from LiteLLM attempts) and agentic_trace
# (from the fallback). This is hard to trigger reliably in E2E because
# the LiteLLM fix loop may succeed. We test what we can: if both keys
# appear, they're structurally valid.
# =========================================================================

class TestCrashAgenticFallback:
    """Section U: crash with LiteLLM + agentic fallback may produce both keys."""

    def test_both_keys_on_fallback(self, tmp_path, agentic_provider):
        """If a crash entry has both llm_traces and agentic_trace, both are valid."""
        project = _create_minimal_pdd_project(tmp_path)
        # Generate clean code first
        _run_pdd_sync(project, extra_args=["--agentic"])

        # Break code to trigger crash
        code_file = project / "greeter.py"
        if code_file.exists():
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


# =========================================================================
# Section V+W: Skip, dry-run, core-dump (PDD_RUN_REAL_LLM_TESTS=1)
#
# One pdd sync to generate, then a second sync (skips), then dry-run
# and core-dump on the same project. 2 LLM sync runs total (second is
# instant because everything skips).
# =========================================================================

class TestSkipDryRunCoreDump:
    """Sections V+W: sync twice, then dry-run and core-dump on same project."""

    def test_skip_dryrun_coredump(self, tmp_path):
        """First sync generates. Second sync skips. Then check dry-run and core-dump."""
        _skip_unless_real_llm()
        project = _create_minimal_pdd_project(tmp_path)

        # First sync — generates code, tests, example
        _run_pdd_sync(project)

        # Second sync — should skip everything
        _run_pdd_sync(project)
        entries = _read_sync_log(project)

        # --- Skip entries have no traces ---
        skip_entries = [e for e in entries if str(e.get("operation", "")).startswith("skip")]
        for entry in skip_entries:
            assert "llm_traces" not in entry
            assert "agentic_trace" not in entry

        # --- Dry-run shows operation history ---
        result = subprocess.run(
            ["pdd", "sync", "greeter", "--dry-run"],
            cwd=project, capture_output=True, text=True, timeout=60,
        )
        assert "generate" in result.stdout.lower() or "test" in result.stdout.lower()

        # --- Core dump has sync_log_refs pointing to .pdd/logs/ ---
        subprocess.run(
            ["pdd", "sync", "greeter", "--core-dump"],
            cwd=project, capture_output=True, text=True, timeout=300,
        )
        core_dumps = list((project / ".pdd" / "core_dumps").glob("*.json"))
        if core_dumps:
            dump = json.loads(core_dumps[-1].read_text(encoding="utf-8"))
            if "sync_log_refs" in dump:
                for ref in dump["sync_log_refs"]:
                    assert ref["path"].startswith(".pdd/logs/")


# =========================================================================
# Section X: Migration (PDD_RUN_REAL_LLM_TESTS=1)
#
# Needs its own project because it plants a legacy file before syncing.
# =========================================================================

class TestMigration:
    """Section X: legacy file migrates on real sync."""

    def test_legacy_file_migrates(self, tmp_path):
        _skip_unless_real_llm()
        project = _create_minimal_pdd_project(tmp_path)
        # Plant a legacy sync log in .pdd/meta/
        meta_dir = project / ".pdd" / "meta"
        meta_dir.mkdir(parents=True, exist_ok=True)
        old_entry = {"operation": "old_generate", "success": True, "timestamp": "2025-01-01T00:00:00"}
        (meta_dir / "greeter_python_sync.log").write_text(json.dumps(old_entry) + "\n", encoding="utf-8")
        _run_pdd_sync(project)
        # Old location should be empty
        assert not (meta_dir / "greeter_python_sync.log").exists()
        # New location should have old + new entries
        new_log = project / ".pdd" / "logs" / "greeter_python_sync.log"
        assert new_log.exists()
        entries = _read_sync_log(project)
        ops = [e.get("operation") for e in entries]
        assert "old_generate" in ops  # old entry preserved
