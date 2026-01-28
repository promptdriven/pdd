"""
E2E CLI Test for Issue #419: Agentic fix doesn't push commits when exiting early at Step 2

This test exercises the full CLI path for `pdd fix <GITHUB_ISSUE_URL>` to verify that
commits created by LLM agents during the workflow are pushed to the remote repository
even when the workflow exits early at Step 2 (ALL_TESTS_PASS).

The bug: When the agentic e2e fix workflow exits early at Step 2, commits created by
LLM agents in Step 1 are not pushed to the remote, despite the workflow reporting success.

This E2E test:
1. Creates a mock git repository with a remote (simulating a GitHub fork)
2. Creates test files that will pass immediately (to trigger early exit)
3. Mocks LLM calls to simulate the workflow:
   - Step 1: LLM agent creates a commit with a fix
   - Step 2: Tests pass immediately → ALL_TESTS_PASS → early exit
4. Verifies that the commit from Step 1 is pushed to the remote

Expected behavior (after fix):
- Workflow completes successfully
- Commit from Step 1 is pushed to remote
- Local and remote are in sync

Actual behavior (bug):
- Workflow completes successfully
- Commit from Step 1 exists locally
- Commit is NOT pushed to remote
- Local is ahead of remote by 1 commit
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
    """
    Create a mock git repository with a remote, simulating a GitHub fork.

    This fixture sets up:
    - A local git repository with a worktree structure like .pdd/worktrees/fix-issue-419/
    - A bare remote repository (simulating GitHub)
    - Initial commits and a branch tracking the remote
    """
    # Create main repo directory
    main_repo = tmp_path / "main_repo"
    main_repo.mkdir()

    # Initialize main repo
    subprocess.run(["git", "init", "-b", "main"], cwd=main_repo, check=True, capture_output=True)
    subprocess.run(["git", "config", "user.email", "test@test.com"], cwd=main_repo, check=True)
    subprocess.run(["git", "config", "user.name", "Test User"], cwd=main_repo, check=True)

    # Create initial file structure
    pdd_dir = main_repo / "pdd"
    pdd_dir.mkdir()

    init_file = pdd_dir / "__init__.py"
    init_file.write_text("__version__ = '0.0.1'\n")

    commands_dir = pdd_dir / "commands"
    commands_dir.mkdir()
    (commands_dir / "__init__.py").write_text("")

    # Create a file that will be "fixed" by the LLM agent
    generate_file = commands_dir / "generate.py"
    generate_file.write_text('''"""Generate command with a bug."""
import os

def generate():
    """Generate code from prompt."""
    # BUG: Environment variable pollution (related to issue #409)
    os.environ.update({"TEMP_VAR": "value"})
    return "Generated code"
''')

    # Create test directory
    tests_dir = main_repo / "tests"
    tests_dir.mkdir()

    # Create test file that will pass after the fix
    test_file = tests_dir / "test_generate.py"
    test_file.write_text('''"""Tests for generate command."""
import os
import pytest

def test_generate_does_not_pollute_env():
    """Test that generate() doesn't pollute environment variables."""
    initial_env = dict(os.environ)

    from pdd.commands.generate import generate
    result = generate()

    # After fix, this should pass
    assert dict(os.environ) == initial_env, "generate() should not modify os.environ"
    assert result == "Generated code"
''')

    # Commit initial state
    subprocess.run(["git", "add", "."], cwd=main_repo, check=True)
    subprocess.run(["git", "commit", "-m", "Initial commit"], cwd=main_repo, check=True)

    # Create bare remote repository (simulates GitHub)
    remote_repo = tmp_path / "remote.git"
    subprocess.run(["git", "init", "--bare", str(remote_repo)], check=True, capture_output=True)

    # Add remote and push
    subprocess.run(["git", "remote", "add", "origin", str(remote_repo)], cwd=main_repo, check=True)
    subprocess.run(["git", "push", "-u", "origin", "main"], cwd=main_repo, check=True, capture_output=True)

    # Create worktree for the fix (simulating `pdd bug` workflow)
    worktrees_dir = main_repo / ".pdd" / "worktrees"
    worktrees_dir.mkdir(parents=True)

    worktree_path = worktrees_dir / "fix-issue-419"
    subprocess.run(
        ["git", "worktree", "add", "-b", "fix/issue-419", str(worktree_path), "main"],
        cwd=main_repo,
        check=True,
        capture_output=True
    )

    # Push the branch to remote
    subprocess.run(["git", "push", "-u", "origin", "fix/issue-419"], cwd=worktree_path, check=True, capture_output=True)

    return {
        "main_repo": main_repo,
        "worktree_path": worktree_path,
        "remote_repo": remote_repo,
    }


@pytest.mark.e2e
class TestIssue419CLIUnpushedCommitsE2E:
    """
    E2E tests for Issue #419: Verify that commits are pushed even when workflow exits early.

    These tests exercise the full CLI path: pdd fix <GITHUB_ISSUE_URL>
    """

    def test_agentic_fix_pushes_commits_on_early_exit_at_step2(self, mock_git_repo_with_remote, monkeypatch):
        """
        E2E Test: Commits from Step 1 should be pushed when workflow exits early at Step 2.

        Scenario:
        1. User runs: pdd fix https://github.com/test/repo/issues/419
        2. Step 1: LLM agent fixes the code and creates a commit
        3. Step 2: Tests pass immediately → ALL_TESTS_PASS → early exit
        4. Workflow completes successfully

        Expected behavior (after fix):
        - Commit from Step 1 is pushed to remote
        - Local and remote are in sync
        - Output indicates commits were pushed

        Actual behavior (bug):
        - Commit from Step 1 exists locally
        - Commit is NOT pushed to remote
        - Output misleadingly says "No changes to commit"
        - Local is ahead of remote by 1 commit
        """
        worktree_path = mock_git_repo_with_remote["worktree_path"]

        # Set up environment
        monkeypatch.chdir(worktree_path)
        monkeypatch.setenv("PDD_FORCE_LOCAL", "1")

        # Track LLM calls to verify workflow steps
        step_calls = []

        def mock_run_agentic_task(instruction, cwd, verbose, quiet, timeout, label, max_retries):
            """
            Mock LLM agent that simulates the workflow steps.

            Step 1: Fix the code and create a commit (simulating LLM agent behavior)
            Step 2: Return ALL_TESTS_PASS to trigger early exit
            """
            step_calls.append(label)

            if "step1" in label:
                # SIMULATE LLM AGENT CREATING A FIX AND COMMITTING IT
                # This is what the LLM agent does in Step 1
                generate_file = cwd / "pdd" / "commands" / "generate.py"

                # Fix the bug (remove os.environ.update)
                fixed_content = '''"""Generate command - fixed."""
import os

def generate():
    """Generate code from prompt."""
    # FIXED: Removed environment variable pollution
    return "Generated code"
'''
                generate_file.write_text(fixed_content)

                # LLM agent commits the fix
                subprocess.run(["git", "add", "pdd/commands/generate.py"], cwd=cwd, check=True)
                subprocess.run(
                    ["git", "commit", "-m", "Fix issue #419: Remove os.environ.update() causing environment pollution"],
                    cwd=cwd,
                    check=True,
                    capture_output=True
                )

                return (True, "Fixed pdd/commands/generate.py by removing os.environ.update()", 0.001, "mock-model")

            elif "step2" in label:
                # Step 2: Tests pass immediately → early exit
                return (True, "ALL_TESTS_PASS", 0.001, "mock-model")

            # Shouldn't reach other steps due to early exit
            return (True, f"Mock success for {label}", 0.001, "mock-model")

        def mock_save_state(*args, **kwargs):
            """Mock state persistence."""
            pass

        def mock_load_state(*args, **kwargs):
            """Mock state loading - return no previous state."""
            return None, None

        def mock_clear_state(*args, **kwargs):
            """Mock state clearing."""
            pass

        # Patch the orchestrator's LLM task runner and state management
        with patch('pdd.agentic_e2e_fix_orchestrator.run_agentic_task', side_effect=mock_run_agentic_task):
            with patch('pdd.agentic_e2e_fix_orchestrator.save_workflow_state', side_effect=mock_save_state):
                with patch('pdd.agentic_e2e_fix_orchestrator.load_workflow_state', side_effect=mock_load_state):
                    with patch('pdd.agentic_e2e_fix_orchestrator.clear_workflow_state', side_effect=mock_clear_state):
                        from pdd.agentic_e2e_fix_orchestrator import run_agentic_e2e_fix_orchestrator

                        # Run the orchestrator (simulates `pdd fix <url>`)
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

        # Verify workflow completed successfully
        assert success is True, f"Workflow should succeed, got: {message}"

        # Verify Step 1 and Step 2 were executed
        assert any("step1" in call for call in step_calls), "Step 1 should have been executed"
        assert any("step2" in call for call in step_calls), "Step 2 should have been executed"

        # Verify the commit was created locally
        local_log = subprocess.run(
            ["git", "log", "--oneline", "-1"],
            cwd=worktree_path,
            capture_output=True,
            text=True,
            check=True
        )
        assert "Fix issue #419" in local_log.stdout, "Commit should exist locally"

        # THE BUG CHECK: Verify the commit was pushed to remote
        remote_log = subprocess.run(
            ["git", "log", "origin/fix/issue-419", "--oneline", "-1"],
            cwd=worktree_path,
            capture_output=True,
            text=True,
            check=True
        )

        if "Fix issue #419" not in remote_log.stdout:
            # Get git status to show the problem
            status_result = subprocess.run(
                ["git", "status", "-sb"],
                cwd=worktree_path,
                capture_output=True,
                text=True,
                check=True
            )

            pytest.fail(
                f"BUG DETECTED (Issue #419): Commit from Step 1 was NOT pushed to remote!\n\n"
                f"Local commit:\n{local_log.stdout}\n"
                f"Remote commit:\n{remote_log.stdout}\n"
                f"Git status:\n{status_result.stdout}\n\n"
                f"Root cause: _commit_and_push() in agentic_e2e_fix_orchestrator.py at lines 237-238\n"
                f"returns 'No changes to commit' without executing git push when the working tree\n"
                f"is clean (because LLM agents already committed the changes in Step 1).\n\n"
                f"Expected: Commit should be pushed to remote\n"
                f"Actual: Commit exists locally but is NOT on remote"
            )

        # Verify branch is in sync with remote (not ahead)
        status_result = subprocess.run(
            ["git", "status", "-sb"],
            cwd=worktree_path,
            capture_output=True,
            text=True,
            check=True
        )
        assert "ahead" not in status_result.stdout, \
            f"Branch should be in sync with remote (not ahead). Status: {status_result.stdout}"

    def test_agentic_fix_output_indicates_push_success(self, mock_git_repo_with_remote, monkeypatch):
        """
        E2E Test: Verify that the output message indicates commits were pushed.

        When commits are pushed successfully, the output should reflect this,
        not misleadingly say "No changes to commit".

        Expected output (after fix):
        - "Pushed existing commits" or similar
        - NOT "No changes to commit"
        """
        worktree_path = mock_git_repo_with_remote["worktree_path"]

        monkeypatch.chdir(worktree_path)
        monkeypatch.setenv("PDD_FORCE_LOCAL", "1")

        def mock_run_agentic_task(instruction, cwd, verbose, quiet, timeout, label, max_retries):
            """Simulate workflow with commit in Step 1."""
            if "step1" in label:
                # LLM agent creates and commits a fix
                generate_file = cwd / "pdd" / "commands" / "generate.py"
                generate_file.write_text('"""Fixed."""\ndef generate():\n    return "Fixed"\n')
                subprocess.run(["git", "add", "pdd/commands/generate.py"], cwd=cwd, check=True)
                subprocess.run(["git", "commit", "-m", "Fix"], cwd=cwd, check=True, capture_output=True)
                return (True, "Fixed", 0.001, "mock-model")
            elif "step2" in label:
                return (True, "ALL_TESTS_PASS", 0.001, "mock-model")
            return (True, "Success", 0.001, "mock-model")

        # Patch dependencies
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

        # After fix, message should NOT be "No changes to commit"
        # because commits were pushed
        if message == "No changes to commit":
            pytest.fail(
                f"BUG DETECTED (Issue #419): Output message is misleading!\n\n"
                f"Message: '{message}'\n\n"
                f"The workflow created and committed changes in Step 1, then exited early at Step 2.\n"
                f"The message 'No changes to commit' is misleading because commits exist but weren't pushed.\n\n"
                f"Expected message: 'Pushed existing commits' or similar\n"
                f"Actual message: '{message}'"
            )
