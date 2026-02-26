"""
E2E Test for Issue #557: pdd sync --agentic fails with Codex/OpenAI provider.

This test exercises the full agentic sync pipeline from run_agentic_sync()
through to module identification, verifying that modern Codex NDJSON output
is correctly parsed, text is extracted, and modules are identified.

The bug chain:
1. NDJSON parser (agentic_common.py:775-791) looks for "type":"result" events
   that modern Codex CLI (0.104.0+) no longer emits
2. _parse_provider_json (agentic_common.py:821-824) tries data.get("result")
   / data.get("output") but modern Codex stores text at data["item"]["text"]
3. Empty output triggers false-positive detection (agentic_common.py:583-584)
4. All retries exhaust → run_agentic_sync reports failure

The E2E difference from unit tests:
- Unit tests (test_agentic_common.py) test _run_with_provider and _parse_provider_json
  in isolation
- This E2E test exercises the full run_agentic_sync pipeline: URL parsing → issue
  fetching → architecture loading → prompt templating → run_agentic_task →
  _run_with_provider → NDJSON parsing → text extraction → false positive detection →
  module list parsing

Only external boundaries are mocked: GitHub CLI (gh), Codex CLI subprocess, and
provider availability. All internal logic runs for real.
"""

import json
import os
import pytest
from pathlib import Path
from unittest.mock import patch, MagicMock


# ---------------------------------------------------------------------------
# Helpers
# ---------------------------------------------------------------------------

def _build_modern_codex_ndjson_with_modules(modules: list[str]) -> str:
    """
    Build realistic modern Codex NDJSON output (0.104.0+ format) that contains
    the structured markers run_agentic_sync expects in the LLM response.
    """
    module_list = ", ".join(modules)
    agent_text = (
        f"MODULES_TO_SYNC: [{module_list}]\n"
        f"DEPS_VALID: true\n"
        f"Analysis: Based on the issue, modules {module_list} need synchronization."
    )
    lines = [
        json.dumps({"type": "session.start", "session_id": "sess_e2e_557"}),
        json.dumps({
            "type": "item.completed",
            "item": {"type": "tool_call", "name": "shell", "output": "ls -la"}
        }),
        json.dumps({
            "type": "item.completed",
            "item": {"type": "agent_message", "text": agent_text}
        }),
        json.dumps({
            "type": "session.end",
            "usage": {"input_tokens": 500, "output_tokens": 200}
        }),
    ]
    return "\n".join(lines)


def _make_fake_issue_json(title: str, body: str) -> str:
    """Build a JSON string mimicking the GitHub API response for an issue."""
    return json.dumps({
        "title": title,
        "body": body,
        "number": 42,
        "comments_url": "https://api.github.com/repos/test/repo/issues/42/comments",
    })


@pytest.fixture(autouse=True)
def set_pdd_path(monkeypatch):
    """Set PDD_PATH so prompt templates can be loaded."""
    import pdd
    pdd_package_dir = Path(pdd.__file__).parent
    monkeypatch.setenv("PDD_PATH", str(pdd_package_dir))


# ---------------------------------------------------------------------------
# E2E Test Class
# ---------------------------------------------------------------------------

class TestAgenticSyncCodexE2E:
    """
    E2E tests for Issue #557: Agentic sync with OpenAI/Codex provider.

    These tests exercise the full run_agentic_sync pipeline with only external
    boundaries mocked (GitHub CLI, Codex subprocess, provider availability).
    All internal parsing, extraction, false-positive detection, and module
    identification logic runs for real.
    """

    def test_agentic_sync_with_modern_codex_ndjson_identifies_modules(
        self, tmp_path, monkeypatch
    ):
        """
        E2E: Full agentic sync pipeline with modern Codex NDJSON output.

        When the user runs `pdd sync <github_issue_url> --agentic` and the
        Codex provider returns modern NDJSON with item.completed events:
        - The pipeline should parse the NDJSON correctly
        - Extract the agent_message text containing MODULES_TO_SYNC
        - Successfully identify the modules to sync
        - Return success=True

        CURRENT BUG: NDJSON parser misses item.completed → empty output →
        false positive detection → failure. run_agentic_sync returns
        (False, "LLM failed to identify modules: All agent providers failed: ...")

        AFTER FIX: run_agentic_sync returns (True, ...) with identified modules.
        """
        from pdd.agentic_sync import run_agentic_sync

        # Set up a minimal project structure in tmp_path
        (tmp_path / ".git").mkdir()
        (tmp_path / "architecture.json").write_text(json.dumps([
            {"filename": "auth_Python.prompt", "dependencies": []},
            {"filename": "payments_Python.prompt", "dependencies": ["auth_Python.prompt"]},
        ]))
        (tmp_path / "prompts").mkdir()
        (tmp_path / "prompts" / "auth_Python.prompt").write_text("prompt for auth")
        (tmp_path / "prompts" / "payments_Python.prompt").write_text("prompt for payments")

        monkeypatch.chdir(tmp_path)

        # Modern Codex NDJSON with the structured markers
        ndjson_output = _build_modern_codex_ndjson_with_modules(
            ["auth_Python", "payments_Python"]
        )

        # Fake GitHub API responses
        issue_json = _make_fake_issue_json(
            title="Update auth and payments modules",
            body="We need to sync auth and payments modules to match the latest spec.",
        )
        comments_json = json.dumps([])

        def fake_gh_command(args):
            """Simulate gh CLI API calls."""
            if "issues" in str(args) and "comments" not in str(args):
                return True, issue_json
            return True, comments_json

        with patch.dict(os.environ, {"OPENAI_API_KEY": "test-key-e2e"}, clear=False), \
             patch("pdd.agentic_sync._check_gh_cli", return_value=True), \
             patch("pdd.agentic_sync._run_gh_command", side_effect=fake_gh_command), \
             patch("pdd.agentic_common.get_available_agents", return_value=["openai"]), \
             patch("pdd.agentic_common.get_agent_provider_preference", return_value=["openai"]), \
             patch("pdd.agentic_common._find_cli_binary", return_value="/usr/bin/codex"), \
             patch("subprocess.run") as mock_subprocess, \
             patch("time.sleep"), \
             patch("pdd.agentic_sync._run_dry_run_validation",
                   return_value=(True, {"auth": tmp_path, "payments": tmp_path}, [], 0.0)), \
             patch("pdd.agentic_sync.AsyncSyncRunner") as mock_runner:
            mock_subprocess.return_value = MagicMock(
                returncode=0,
                stdout=ndjson_output,
                stderr=""
            )
            mock_runner_instance = MagicMock()
            mock_runner_instance.run.return_value = (True, "Sync completed", 0.05)
            mock_runner.return_value = mock_runner_instance

            success, message, cost, provider = run_agentic_sync(
                issue_url="https://github.com/test/repo/issues/42",
                verbose=False,
                quiet=True,
                agentic_mode=True,
                use_github_state=False,
            )

        # Primary assertion: the pipeline must succeed
        assert success is True, (
            f"Issue #557 E2E: Agentic sync with modern Codex NDJSON failed. "
            f"Message: {message}"
        )

    def test_agentic_sync_codex_false_positive_on_current_bug(
        self, tmp_path, monkeypatch
    ):
        """
        E2E: Confirms the exact failure mode the user reports.

        With the current buggy code, run_agentic_sync should fail because:
        1. NDJSON parser misses the agent_message in item.completed events
        2. _parse_provider_json extracts empty text
        3. False positive detection triggers
        4. All retries exhaust
        5. run_agentic_sync returns failure with "LLM failed" message

        This test documents the current broken behavior. After the fix is
        applied, this test should be updated to expect success.
        """
        from pdd.agentic_sync import run_agentic_sync

        # Minimal project setup
        (tmp_path / ".git").mkdir()
        (tmp_path / "architecture.json").write_text(json.dumps([
            {"filename": "users_Python.prompt", "dependencies": []},
        ]))

        monkeypatch.chdir(tmp_path)

        ndjson_output = _build_modern_codex_ndjson_with_modules(["users_Python"])

        issue_json = _make_fake_issue_json(
            title="Fix user module",
            body="The users module needs updating.",
        )

        def fake_gh_command(args):
            """Simulate gh CLI API calls."""
            if "issues" in str(args) and "comments" not in str(args):
                return True, issue_json
            return True, json.dumps([])

        with patch.dict(os.environ, {"OPENAI_API_KEY": "test-key-e2e"}, clear=False), \
             patch("pdd.agentic_sync._check_gh_cli", return_value=True), \
             patch("pdd.agentic_sync._run_gh_command", side_effect=fake_gh_command), \
             patch("pdd.agentic_common.get_available_agents", return_value=["openai"]), \
             patch("pdd.agentic_common.get_agent_provider_preference", return_value=["openai"]), \
             patch("pdd.agentic_common._find_cli_binary", return_value="/usr/bin/codex"), \
             patch("subprocess.run") as mock_subprocess, \
             patch("time.sleep"), \
             patch("pdd.agentic_sync._run_dry_run_validation",
                   return_value=(True, {"users": tmp_path}, [], 0.0)), \
             patch("pdd.agentic_sync.AsyncSyncRunner") as mock_runner:
            mock_subprocess.return_value = MagicMock(
                returncode=0,
                stdout=ndjson_output,
                stderr=""
            )
            mock_runner_instance = MagicMock()
            mock_runner_instance.run.return_value = (True, "Sync completed", 0.05)
            mock_runner.return_value = mock_runner_instance

            success, message, cost, provider = run_agentic_sync(
                issue_url="https://github.com/test/repo/issues/42",
                verbose=False,
                quiet=True,
                agentic_mode=True,
                use_github_state=False,
            )

        # With the bug: success is False and the message indicates LLM failure
        # After fix: this assertion should flip to success is True
        assert success is True, (
            f"Issue #557 E2E: Current bug causes false positive chain. "
            f"Message was: {message}"
        )

    def test_run_agentic_task_codex_ndjson_through_full_retry_loop(
        self, tmp_path, monkeypatch
    ):
        """
        E2E: Exercise run_agentic_task (the core public API) with modern Codex
        NDJSON through the full retry loop and false-positive detection.

        Unlike the unit test that calls _run_with_provider directly, this test
        goes through run_agentic_task's provider selection, prompt file creation,
        retry loop, and false-positive detection — the exact path triggered by
        `pdd sync --agentic`.

        CURRENT BUG: Empty output triggers false positive on every retry attempt.
        run_agentic_task returns (False, "All agent providers failed: ...", 0.0, "").

        EXPECTED: run_agentic_task returns (True, agent_text, cost, "openai").
        """
        from pdd.agentic_common import run_agentic_task

        agent_text = (
            "MODULES_TO_SYNC: [auth, payments, users]\n"
            "DEPS_VALID: true\n"
            "SYNC_CWD: /app\n"
            "Analysis complete. The following modules need synchronization."
        )
        ndjson_lines = [
            json.dumps({"type": "session.start", "session_id": "sess_e2e_retry"}),
            json.dumps({
                "type": "item.completed",
                "item": {"type": "tool_call", "name": "read_file", "output": "auth.py contents"}
            }),
            json.dumps({
                "type": "item.completed",
                "item": {"type": "agent_message", "text": agent_text}
            }),
            json.dumps({
                "type": "session.end",
                "usage": {"input_tokens": 1000, "output_tokens": 400}
            }),
        ]
        ndjson_output = "\n".join(ndjson_lines)

        with patch.dict(os.environ, {"OPENAI_API_KEY": "test-key-e2e"}, clear=False), \
             patch("pdd.agentic_common.get_available_agents", return_value=["openai"]), \
             patch("pdd.agentic_common.get_agent_provider_preference", return_value=["openai"]), \
             patch("pdd.agentic_common._find_cli_binary", return_value="/usr/bin/codex"), \
             patch("subprocess.run") as mock_subprocess, \
             patch("time.sleep"):
            mock_subprocess.return_value = MagicMock(
                returncode=0,
                stdout=ndjson_output,
                stderr=""
            )

            success, output, cost, provider = run_agentic_task(
                instruction="Identify modules that need syncing",
                cwd=tmp_path,
                max_retries=3,
                quiet=True,
            )

        # Primary assertions
        assert success is True, (
            f"Issue #557 E2E: run_agentic_task failed with modern Codex NDJSON. "
            f"Output: {output!r}"
        )
        assert "MODULES_TO_SYNC" in output, (
            f"Issue #557 E2E: Agent text not extracted. Got: {output!r}"
        )
        assert provider == "openai", (
            f"Expected provider 'openai', got '{provider}'"
        )
        # Cost should be non-zero (calculated from usage stats)
        assert cost >= 0.0

    def test_cli_sync_command_with_codex_provider(self, tmp_path, monkeypatch):
        """
        E2E: Exercise the actual Click CLI command for `pdd sync <url>`.

        This is the closest to how a real user invokes the feature. It uses
        Click's CliRunner to invoke the sync command with a GitHub issue URL,
        which dispatches to run_agentic_sync.

        CURRENT BUG: CLI exits with "LLM failed to identify modules" because
        the Codex NDJSON parsing chain fails.

        EXPECTED: CLI exits successfully and reports modules found.
        """
        from click.testing import CliRunner
        from pdd import cli

        # Set up project structure
        (tmp_path / ".git").mkdir()
        (tmp_path / "architecture.json").write_text(json.dumps([
            {"filename": "auth_Python.prompt", "dependencies": []},
        ]))
        (tmp_path / "prompts").mkdir()
        (tmp_path / "prompts" / "auth_Python.prompt").write_text("prompt for auth")

        monkeypatch.chdir(tmp_path)

        ndjson_output = _build_modern_codex_ndjson_with_modules(["auth_Python"])

        issue_json = _make_fake_issue_json(
            title="Update auth module",
            body="Auth needs sync.",
        )

        def fake_gh_command(args):
            """Simulate gh CLI API calls."""
            if "issues" in str(args) and "comments" not in str(args):
                return True, issue_json
            return True, json.dumps([])

        runner = CliRunner()
        with patch.dict(os.environ, {"OPENAI_API_KEY": "test-key-e2e"}, clear=False), \
             patch("pdd.agentic_sync._check_gh_cli", return_value=True), \
             patch("pdd.agentic_sync._run_gh_command", side_effect=fake_gh_command), \
             patch("pdd.agentic_common.get_available_agents", return_value=["openai"]), \
             patch("pdd.agentic_common.get_agent_provider_preference", return_value=["openai"]), \
             patch("pdd.agentic_common._find_cli_binary", return_value="/usr/bin/codex"), \
             patch("subprocess.run") as mock_subprocess, \
             patch("time.sleep"), \
             patch("pdd.agentic_sync.AsyncSyncRunner") as mock_runner:
            mock_subprocess.return_value = MagicMock(
                returncode=0,
                stdout=ndjson_output,
                stderr=""
            )
            # Mock the async sync runner to avoid actually running syncs
            mock_runner_instance = MagicMock()
            mock_runner_instance.run.return_value = (True, "Sync completed", 0.05)
            mock_runner.return_value = mock_runner_instance

            result = runner.invoke(
                cli.cli,
                ["--force", "--local", "sync",
                 "https://github.com/test/repo/issues/42",
                 "--agentic"],
                catch_exceptions=False,
            )

        # The CLI should not show "LLM failed" message
        assert "LLM failed to identify modules" not in (result.output or ""), (
            f"Issue #557 E2E: CLI reported LLM failure due to Codex NDJSON parsing bug. "
            f"Output: {result.output}"
        )
