"""
E2E CLI Test for Issue #419: Agentic fix pushes commits when exiting early

Tests the full orchestrator workflow with mocked LLM calls to verify commits are
pushed when the workflow exits early at Step 2.
"""

import pytest
import subprocess
import tempfile
import json
from pathlib import Path
from unittest.mock import patch, MagicMock
from click.testing import CliRunner


@pytest.fixture
def mock_git_repo_with_remote(tmp_path):
    """Create git repository with worktree and remote for testing."""
    main_repo = tmp_path / "main_repo"
    main_repo.mkdir()

    subprocess.run(["git", "init", "-b", "main"], cwd=main_repo, check=True, capture_output=True)
    subprocess.run(["git", "config", "user.email", "test@test.com"], cwd=main_repo, check=True)
    subprocess.run(["git", "config", "user.name", "Test User"], cwd=main_repo, check=True)

    pdd_dir = main_repo / "pdd"
    pdd_dir.mkdir()
    (pdd_dir / "__init__.py").write_text("__version__ = '0.0.1'\n")

    commands_dir = pdd_dir / "commands"
    commands_dir.mkdir()
    (commands_dir / "__init__.py").write_text("")

    generate_file = commands_dir / "generate.py"
    generate_file.write_text('''"""Generate command with a bug."""
import os

def generate():
    """Generate code from prompt."""
    os.environ.update({"TEMP_VAR": "value"})
    return "Generated code"
''')

    tests_dir = main_repo / "tests"
    tests_dir.mkdir()

    test_file = tests_dir / "test_generate.py"
    test_file.write_text('''"""Tests for generate command."""
import os
import pytest

def test_generate_does_not_pollute_env():
    """Test that generate() doesn't pollute environment variables."""
    initial_env = dict(os.environ)

    from pdd.commands.generate import generate
    result = generate()

    assert dict(os.environ) == initial_env, "generate() should not modify os.environ"
    assert result == "Generated code"
''')

    subprocess.run(["git", "add", "."], cwd=main_repo, check=True)
    subprocess.run(["git", "commit", "-m", "Initial commit"], cwd=main_repo, check=True)

    remote_repo = tmp_path / "remote.git"
    subprocess.run(["git", "init", "--bare", str(remote_repo)], check=True, capture_output=True)

    subprocess.run(["git", "remote", "add", "origin", str(remote_repo)], cwd=main_repo, check=True)
    subprocess.run(["git", "push", "-u", "origin", "main"], cwd=main_repo, check=True, capture_output=True)

    worktrees_dir = main_repo / ".pdd" / "worktrees"
    worktrees_dir.mkdir(parents=True)

    worktree_path = worktrees_dir / "fix-issue-419"
    subprocess.run(
        ["git", "worktree", "add", "-b", "fix/issue-419", str(worktree_path), "main"],
        cwd=main_repo,
        check=True,
        capture_output=True
    )

    subprocess.run(["git", "push", "-u", "origin", "fix/issue-419"], cwd=worktree_path, check=True, capture_output=True)

    return {
        "main_repo": main_repo,
        "worktree_path": worktree_path,
        "remote_repo": remote_repo,
    }


@pytest.mark.e2e
class TestIssue419CLIUnpushedCommitsE2E:
    """E2E tests for Issue #419: Full orchestrator workflow pushes commits on early exit."""

    def test_agentic_fix_pushes_commits_on_early_exit_at_step2(self, mock_git_repo_with_remote, monkeypatch):
        """Test that orchestrator pushes commits from Step 1 when exiting early at Step 2."""
        worktree_path = mock_git_repo_with_remote["worktree_path"]
        monkeypatch.chdir(worktree_path)
        monkeypatch.setenv("PDD_FORCE_LOCAL", "1")

        step_calls = []

        def mock_run_agentic_task(instruction, cwd, verbose, quiet, timeout, label, max_retries):
            """Mock LLM agent: Step 1 creates commit, Step 2 returns ALL_TESTS_PASS."""
            step_calls.append(label)

            if "step1" in label:
                generate_file = cwd / "pdd" / "commands" / "generate.py"
                fixed_content = '''"""Generate command - fixed."""
import os

def generate():
    """Generate code from prompt."""
    return "Generated code"
'''
                generate_file.write_text(fixed_content)
                subprocess.run(["git", "add", "pdd/commands/generate.py"], cwd=cwd, check=True)
                subprocess.run(
                    ["git", "commit", "-m", "Fix issue #419: Remove os.environ.update() causing environment pollution"],
                    cwd=cwd,
                    check=True,
                    capture_output=True
                )
                return (True, "Fixed pdd/commands/generate.py by removing os.environ.update()", 0.001, "mock-model")

            elif "step2" in label:
                return (True, "ALL_TESTS_PASS", 0.001, "mock-model")

            return (True, f"Mock success for {label}", 0.001, "mock-model")

        def mock_save_state(*args, **kwargs):
            pass

        def mock_load_state(*args, **kwargs):
            return None, None

        def mock_clear_state(*args, **kwargs):
            pass
        with patch('pdd.agentic_e2e_fix_orchestrator.run_agentic_task', side_effect=mock_run_agentic_task):
            with patch('pdd.agentic_e2e_fix_orchestrator.save_workflow_state', side_effect=mock_save_state):
                with patch('pdd.agentic_e2e_fix_orchestrator.load_workflow_state', side_effect=mock_load_state):
                    with patch('pdd.agentic_e2e_fix_orchestrator.clear_workflow_state', side_effect=mock_clear_state):
                        from pdd.agentic_e2e_fix_orchestrator import run_agentic_e2e_fix_orchestrator

                        success, message, cost, model, files = run_agentic_e2e_fix_orchestrator(
                            issue_url="https://github.com/test/repo/issues/419",
                            issue_content="Environment variable pollution bug",
                            repo_owner="test",
                            repo_name="repo",
                            issue_number=419,
                            issue_author="test-user",
                            issue_title="Bug: Agentic fix doesn't push commits when exiting early at Step 2",
                            cwd=worktree_path,
                            max_cycles=5,
                            resume=False,
                            verbose=False,
                            quiet=True,
                            use_github_state=False,
                            protect_tests=False
                        )

        assert success is True, f"Workflow should succeed, got: {message}"
        assert any("step1" in call for call in step_calls)
        assert any("step2" in call for call in step_calls)

        local_log = subprocess.run(
            ["git", "log", "--oneline", "-1"],
            cwd=worktree_path,
            capture_output=True,
            text=True,
            check=True
        )
        assert "Fix issue #419" in local_log.stdout

        remote_log = subprocess.run(
            ["git", "log", "origin/fix/issue-419", "--oneline", "-1"],
            cwd=worktree_path,
            capture_output=True,
            text=True,
            check=True
        )

        if "Fix issue #419" not in remote_log.stdout:
            status_result = subprocess.run(
                ["git", "status", "-sb"],
                cwd=worktree_path,
                capture_output=True,
                text=True,
                check=True
            )
            pytest.fail(
                f"BUG: Commit from Step 1 was not pushed to remote.\n"
                f"Local: {local_log.stdout}\n"
                f"Remote: {remote_log.stdout}\n"
                f"Status: {status_result.stdout}"
            )

        status_result = subprocess.run(
            ["git", "status", "-sb"],
            cwd=worktree_path,
            capture_output=True,
            text=True,
            check=True
        )
        assert "ahead" not in status_result.stdout

    def test_agentic_fix_output_indicates_push_success(self, mock_git_repo_with_remote, monkeypatch):
        """Test that output message indicates commits were pushed, not 'No changes to commit'."""
        worktree_path = mock_git_repo_with_remote["worktree_path"]
        monkeypatch.chdir(worktree_path)
        monkeypatch.setenv("PDD_FORCE_LOCAL", "1")

        def mock_run_agentic_task(instruction, cwd, verbose, quiet, timeout, label, max_retries):
            if "step1" in label:
                generate_file = cwd / "pdd" / "commands" / "generate.py"
                generate_file.write_text('"""Fixed."""\ndef generate():\n    return "Fixed"\n')
                subprocess.run(["git", "add", "pdd/commands/generate.py"], cwd=cwd, check=True)
                subprocess.run(["git", "commit", "-m", "Fix"], cwd=cwd, check=True, capture_output=True)
                return (True, "Fixed", 0.001, "mock-model")
            elif "step2" in label:
                return (True, "ALL_TESTS_PASS", 0.001, "mock-model")
            return (True, "Success", 0.001, "mock-model")

        with patch('pdd.agentic_e2e_fix_orchestrator.run_agentic_task', side_effect=mock_run_agentic_task):
            with patch('pdd.agentic_e2e_fix_orchestrator.save_workflow_state'):
                with patch('pdd.agentic_e2e_fix_orchestrator.load_workflow_state', return_value=(None, None)):
                    with patch('pdd.agentic_e2e_fix_orchestrator.clear_workflow_state'):
                        from pdd.agentic_e2e_fix_orchestrator import run_agentic_e2e_fix_orchestrator

                        success, message, cost, model, files = run_agentic_e2e_fix_orchestrator(
                            issue_url="https://github.com/test/repo/issues/419",
                            issue_content="Test issue",
                            repo_owner="test",
                            repo_name="repo",
                            issue_number=419,
                            issue_author="test-user",
                            issue_title="Test Issue",
                            cwd=worktree_path,
                            max_cycles=5,
                            resume=False,
                            verbose=False,
                            quiet=True,
                            use_github_state=False,
                            protect_tests=False
                        )

        if message == "No changes to commit":
            pytest.fail(
                f"BUG: Output message '{message}' is misleading. "
                f"Commits were created but message doesn't indicate they were pushed."
            )
