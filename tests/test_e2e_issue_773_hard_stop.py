"""
E2E Test for Issue #773: pdd change doesn't stop workflow when step asks user for clarification

Bug Context:
-----------
The orchestrator's _check_hard_stop() checks for status strings in step_output (the LLM's
conversational response text). The prompts instruct the LLM to post the status via
`gh issue comment`, which is a different channel. Whether it works depends on whether
the LLM echoes the exact string verbatim in its response.

The fix requires _check_hard_stop to look for a strict `STOP_CONDITION:` tag prefix
instead of loose string matching on conversational text.
"""

import pytest
import subprocess
import re
from pathlib import Path
from unittest.mock import patch, MagicMock


@pytest.fixture
def mock_git_repo(tmp_path):
    """Create a minimal git repository for testing the orchestrator."""
    repo_path = tmp_path / "test_repo"
    repo_path.mkdir()

    subprocess.run(["git", "init", "-b", "main"], cwd=repo_path, check=True, capture_output=True)
    subprocess.run(["git", "config", "user.email", "test@test.com"], cwd=repo_path, check=True)
    subprocess.run(["git", "config", "user.name", "Test User"], cwd=repo_path, check=True)

    pdd_dir = repo_path / ".pdd"
    pdd_dir.mkdir()

    (repo_path / "README.md").write_text("# Test Repository\n")
    subprocess.run(["git", "add", "."], cwd=repo_path, check=True)
    subprocess.run(["git", "commit", "-m", "Initial commit"], cwd=repo_path, check=True, capture_output=True)

    return repo_path


@pytest.mark.e2e
class TestIssue773HardStopE2E:
    """
    E2E tests for Issue #773: change workflow doesn't stop when clarification needed.
    """

    def test_casual_mention_does_not_stop(self, mock_git_repo, monkeypatch):
        """
        E2E Test: A casual mention of 'Clarification Needed' without the STOP_CONDITION tag
        should NOT stop the workflow.
        Before the fix, this would incorrectly stop the workflow.
        """
        monkeypatch.setenv("PDD_FORCE_LOCAL", "1")

        steps_attempted = []

        def mock_run_agentic_task(instruction, cwd, verbose, quiet, timeout, label, max_retries, **kwargs):
            """Track which steps are attempted."""
            match = re.search(r"step(\d+)", label)
            if match:
                step_num = int(match.group(1))
                steps_attempted.append(step_num)

            if "step4" in label:
                # Bug trigger: casual mention without STOP_CONDITION tag
                return (True, "I think some Clarification Needed here.", 0.001, "mock-model")

            # End workflow at step 6 to avoid infinite loops
            if "step6" in label:
                return (True, "STOP_CONDITION: No Dev Units Found", 0.001, "mock-model")

            return (True, f"Mock success for {label}", 0.001, "mock-model")

        def mock_save_state(*args, **kwargs):
            """No-op save."""
            pass

        def mock_load_state(*args, **kwargs):
            """Return no saved state."""
            return None, None

        def mock_clear_state(*args, **kwargs):
            """No-op clear."""
            pass

        from pdd.agentic_change_orchestrator import run_agentic_change_orchestrator

        with patch('pdd.agentic_change_orchestrator.run_agentic_task', side_effect=mock_run_agentic_task):
            with patch('pdd.agentic_change_orchestrator.save_workflow_state', side_effect=mock_save_state):
                with patch('pdd.agentic_change_orchestrator.load_workflow_state', side_effect=mock_load_state):
                    with patch('pdd.agentic_change_orchestrator.clear_workflow_state', side_effect=mock_clear_state):
                        success, message, cost, model, files = run_agentic_change_orchestrator(
                            issue_url="https://github.com/test/repo/issues/773",
                            issue_content="Test issue for bug #773",
                            repo_owner="test",
                            repo_name="repo",
                            issue_number=773,
                            issue_author="test-user",
                            issue_title="Test Issue 773",
                            cwd=mock_git_repo,
                            verbose=False,
                            quiet=True,
                            use_github_state=False
                        )

        # The buggy code would stop at Step 4 due to loose string match.
        # The fixed code should continue past Step 4 because there is no STOP_CONDITION tag.
        if 5 not in steps_attempted:
            pytest.fail(
                "BUG DETECTED (Issue #773): Orchestrator improperly stopped at Step 4 "
                "due to a casual mention of 'Clarification Needed' without a STOP_CONDITION tag.\n"
                f"Steps attempted: {steps_attempted}"
            )

    def test_strict_tag_does_stop(self, mock_git_repo, monkeypatch):
        """
        E2E Test: The exact tag 'STOP_CONDITION: Clarification Needed'
        SHOULD stop the workflow correctly.
        """
        monkeypatch.setenv("PDD_FORCE_LOCAL", "1")

        steps_attempted = []

        def mock_run_agentic_task(instruction, cwd, verbose, quiet, timeout, label, max_retries, **kwargs):
            """Track which steps are attempted."""
            match = re.search(r"step(\d+)", label)
            if match:
                step_num = int(match.group(1))
                steps_attempted.append(step_num)

            if "step4" in label:
                return (True, "I posted the comment. STOP_CONDITION: Clarification Needed", 0.001, "mock-model")

            return (True, f"Mock success for {label}", 0.001, "mock-model")

        def mock_save_state(*args, **kwargs):
            """No-op save."""
            pass

        def mock_load_state(*args, **kwargs):
            """Return no saved state."""
            return None, None

        def mock_clear_state(*args, **kwargs):
            """No-op clear."""
            pass

        from pdd.agentic_change_orchestrator import run_agentic_change_orchestrator

        with patch('pdd.agentic_change_orchestrator.run_agentic_task', side_effect=mock_run_agentic_task):
            with patch('pdd.agentic_change_orchestrator.save_workflow_state', side_effect=mock_save_state):
                with patch('pdd.agentic_change_orchestrator.load_workflow_state', side_effect=mock_load_state):
                    with patch('pdd.agentic_change_orchestrator.clear_workflow_state', side_effect=mock_clear_state):
                        with patch('pdd.agentic_change_orchestrator.post_step_comment'):
                            success, message, cost, model, files = run_agentic_change_orchestrator(
                                issue_url="https://github.com/test/repo/issues/773",
                                issue_content="Test issue for bug #773",
                                repo_owner="test",
                                repo_name="repo",
                                issue_number=773,
                                issue_author="test-user",
                                issue_title="Test Issue 773",
                                cwd=mock_git_repo,
                                verbose=False,
                                quiet=True,
                                use_github_state=False
                            )

        # The workflow SHOULD stop at step 4. Step 5 should not be attempted.
        assert 4 in steps_attempted

        if 5 in steps_attempted:
            pytest.fail(
                "BUG DETECTED (Issue #773): Orchestrator failed to stop at Step 4 "
                "when 'STOP_CONDITION: Clarification Needed' was provided.\n"
                f"Steps attempted: {steps_attempted}"
            )

        assert success is False
        assert "Clarification" in message or "Stopped" in message or "step 4" in message.lower()
