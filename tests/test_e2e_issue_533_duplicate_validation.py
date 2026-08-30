"""
E2E tests for Issue #533: Orchestrator should validate LLM duplicate detection output.

These E2E tests differ from the unit tests in test_issue_533_duplicate_validation.py:
- Unit tests mock load_prompt_template and test orchestrator logic in isolation
- E2E tests use REAL prompt loading via load_prompt_template (not mocked)
- E2E tests exercise the full pipeline: prompt file → preprocess → format → orchestrator

Bug: The orchestrator at line 441 of agentic_bug_orchestrator.py blindly trusts
the LLM's duplicate detection output without validating that the original issue
is actually resolved. When the LLM fails to follow prompt instructions and outputs
"Duplicate of #520" even though #520 is OPEN, the orchestrator incorrectly triggers
a hard stop and closes the issue.

Real-world scenario (issue #530/#520):
- User files issue #530 about a bug
- LLM outputs "Duplicate of #520" without verifying #520's status
- Issue #520 is still OPEN (unresolved)
- Orchestrator blindly trusts LLM and stops workflow, closing #530
- User had to manually reopen #530

Root cause:
The hard stop at line 441 checks for "Duplicate of #" but doesn't validate:
    if step_num == 1 and "Duplicate of #" in output:
        msg = f"Stopped at Step 1: Issue is a duplicate. {output.strip()}"
        return False, msg, total_cost, last_model_used, changed_files

Fix:
The orchestrator should validate the original issue's state using `gh issue view`
before triggering the hard stop. If the original issue is still OPEN (unresolved),
the orchestrator should log a warning and continue the workflow.

This is a regression of issue #469, which fixed the prompts but didn't add
orchestrator-level validation as defense-in-depth against LLM instruction-following failures.

Test Strategy:
- Test 1: LLM outputs duplicate of UNRESOLVED issue → orchestrator validates & continues
- Test 2: LLM outputs duplicate of RESOLVED issue → hard stop works correctly (regression)
- Test 3: Exact scenario from issue #533 using real issue numbers #530/#520
"""

import os
import re
import subprocess
from pathlib import Path
from unittest.mock import patch

import pytest

from pdd.agentic_bug_orchestrator import run_agentic_bug_orchestrator

# Project root: the worktree (or repo root) containing prompts/
_PROJECT_ROOT = Path(__file__).resolve().parent.parent


@pytest.fixture(autouse=True)
def set_pdd_path_to_project_root():
    """Ensure PDD_PATH points to the project root so load_prompt_template
    picks up the prompts/ directory from this worktree, not an external install."""
    old = os.environ.get("PDD_PATH")
    os.environ["PDD_PATH"] = str(_PROJECT_ROOT)
    yield
    if old is not None:
        os.environ["PDD_PATH"] = old
    elif "PDD_PATH" in os.environ:
        del os.environ["PDD_PATH"]


@pytest.fixture
def mock_git_repo(tmp_path):
    """Create a minimal git repository for testing the orchestrator."""
    repo_path = tmp_path / "test_repo"
    repo_path.mkdir()

    subprocess.run(
        ["git", "init", "-b", "main"], cwd=repo_path,
        check=True, capture_output=True
    )
    subprocess.run(
        ["git", "config", "user.email", "test@test.com"],
        cwd=repo_path, check=True
    )
    subprocess.run(
        ["git", "config", "user.name", "Test User"],
        cwd=repo_path, check=True
    )

    (repo_path / "README.md").write_text("# Test Repository\n")
    subprocess.run(["git", "add", "."], cwd=repo_path, check=True)
    subprocess.run(
        ["git", "commit", "-m", "Initial commit"],
        cwd=repo_path, check=True, capture_output=True
    )

    return repo_path


class TestIssue533DuplicateValidationE2E:
    """
    E2E tests for Issue #533: Orchestrator should validate duplicate detection.

    These tests exercise the real prompt loading, preprocessing, and formatting
    pipeline — only the LLM execution layer (run_agentic_task) and git
    operations (_setup_worktree) are mocked.
    """

    def test_llm_outputs_duplicate_of_unresolved_issue_workflow_continues(self, mock_git_repo):
        """
        E2E Test: When the LLM fails to follow prompt instructions and outputs
        "Duplicate of #520" even though #520 is OPEN (unresolved), the orchestrator
        should validate the original issue's state and continue the workflow.

        This is the PRIMARY BUG SCENARIO from issue #533.

        This exercises the full code path:
        1. Real load_prompt_template (loads actual prompt file from disk)
        2. Real preprocess() and format() (expands includes, substitutes vars)
        3. Real orchestrator loop logic (step iteration, hard-stop checks)
        4. Mocked LLM (returns output where it failed to follow prompt instructions)
        5. Mocked worktree setup (avoids real git operations)

        The mock LLM simulates what happened in the real bug: the LLM output
        "Duplicate of #520" WITHOUT properly checking that #520 was resolved.
        The orchestrator should catch this error and validate the issue state.

        EXPECTED BEHAVIOR (after fix):
        - Orchestrator detects "Duplicate of #" in LLM output
        - Orchestrator calls `gh issue view 520` to validate
        - Orchestrator sees #520 is OPEN (unresolved)
        - Orchestrator logs warning about LLM failing to follow instructions
        - Orchestrator continues workflow to Step 2

        BUGGY BEHAVIOR (before fix):
        - Orchestrator detects "Duplicate of #" in LLM output
        - Orchestrator immediately triggers hard stop
        - Workflow stops at Step 1, issue closed as duplicate
        - User has to manually reopen the issue
        """
        mock_worktree = mock_git_repo / ".pdd" / "worktrees" / "fix-issue-533"
        mock_worktree.mkdir(parents=True, exist_ok=True)

        steps_executed = []

        def mock_run_agentic_task(instruction, cwd, verbose, quiet, timeout, label, max_retries):
            """Mock LLM that fails to follow prompt instructions."""
            match = re.search(r"step(\d+(?:_\d+)?)", label)
            if match:
                steps_executed.append(label)

            if "step1" in label:
                # LLM FAILS to follow the prompt: it outputs "Duplicate of #520"
                # without properly checking that #520 is OPEN (unresolved).
                # This simulates the real-world bug from issue #533.
                return (
                    True,
                    "## Step 1: Duplicate Check\n\n"
                    "**Status:** Duplicate of #520\n\n"
                    "### Search Performed\n"
                    "- Searched for: pdd bug agents closes duplicated issues\n"
                    "- Issues reviewed: 5\n\n"
                    "### Findings\n"
                    "Found issue #520 which reports the exact same problem. "
                    "This is a duplicate.\n\n"
                    "---",
                    0.01,
                    "mock-model",
                )

            if "step7" in label:
                return (True, "Generated unit test\nFILES_CREATED: test_fix.py", 0.01, "mock-model")

            return (True, f"Mock output for {label}", 0.01, "mock-model")

        with patch("pdd.agentic_bug_orchestrator.run_agentic_task", side_effect=mock_run_agentic_task), \
             patch("pdd.agentic_bug_orchestrator.console"), \
             patch("pdd.agentic_bug_orchestrator._setup_worktree", return_value=(mock_worktree, None)), \
             patch("subprocess.run") as mock_subprocess:

            # Mock gh issue view to return that #520 is OPEN (unresolved)
            def subprocess_side_effect(*args, **kwargs):
                cmd = args[0] if args else kwargs.get('args', [])
                if isinstance(cmd, list) and 'gh' in cmd and 'issue' in cmd and 'view' in cmd:
                    # Return mock JSON showing issue #520 is OPEN
                    mock_result = subprocess.CompletedProcess(
                        args=cmd,
                        returncode=0,
                        stdout='{"number": 520, "state": "OPEN", "title": "Bug with pdd"}\n',
                        stderr=''
                    )
                    return mock_result
                # For git commands, return success
                return subprocess.CompletedProcess(
                    args=cmd, returncode=0, stdout='', stderr=''
                )

            mock_subprocess.side_effect = subprocess_side_effect

            success, message, cost, model, files = run_agentic_bug_orchestrator(
                issue_url="https://github.com/promptdriven/pdd/issues/530",
                issue_content="PDD bug agents still closes duplicated issues that are not resolved",
                repo_owner="promptdriven",
                repo_name="pdd",
                issue_number=530,
                issue_author="jiaminc-cmu",
                issue_title="pdd bug agents still closes duplicated issues that are not resolved",
                cwd=mock_git_repo,
                verbose=False,
                quiet=True,
                use_github_state=False,
            )

        # The workflow should continue past Step 1 despite LLM outputting "Duplicate of #"
        # because the orchestrator validates that #520 is OPEN (unresolved)
        assert success is True, (
            f"BUG DETECTED (Issue #533): Workflow should continue when LLM outputs "
            f"duplicate of UNRESOLVED issue. The orchestrator should validate that "
            f"#520 is OPEN and not trigger hard stop. Instead got: success={success}, "
            f"msg={message}"
        )
        assert "step1" in steps_executed, "Step 1 should have executed"
        assert len(steps_executed) == 11, (
            f"All 11 steps should execute when the original duplicate is unresolved. "
            f"The orchestrator should validate issue state before stopping. "
            f"Got {len(steps_executed)} steps: {steps_executed}"
        )

    def test_llm_outputs_duplicate_of_resolved_issue_workflow_stops(self, mock_git_repo):
        """
        E2E Regression Test: When the LLM correctly identifies a CLOSED (resolved)
        duplicate and outputs "Duplicate of #520", the workflow should hard-stop
        at Step 1.

        This ensures the fix for #533 doesn't break the valid duplicate detection path.

        EXPECTED BEHAVIOR:
        - LLM outputs "Duplicate of #520"
        - Orchestrator validates with `gh issue view 520`
        - Issue #520 is CLOSED (resolved)
        - Orchestrator triggers hard stop
        - Workflow stops at Step 1 (correct behavior)
        """
        mock_worktree = mock_git_repo / ".pdd" / "worktrees" / "fix-issue-533"
        mock_worktree.mkdir(parents=True, exist_ok=True)

        steps_executed = []

        def mock_run_agentic_task(instruction, cwd, verbose, quiet, timeout, label, max_retries):
            """Mock LLM that correctly identifies a resolved duplicate."""
            match = re.search(r"step(\d+(?:_\d+)?)", label)
            if match:
                steps_executed.append(label)

            if "step1" in label:
                # LLM correctly identifies a resolved duplicate
                return (
                    True,
                    "## Step 1: Duplicate Check\n\n"
                    "**Status:** Duplicate of #520\n\n"
                    "### Search Performed\n"
                    "- Searched for: pdd bug agents closes duplicated issues\n"
                    "- Issues reviewed: 5\n\n"
                    "### Findings\n"
                    "Issue #520 was resolved in PR #525. This is a duplicate.\n\n"
                    "---",
                    0.01,
                    "mock-model",
                )

            return (True, f"Mock output for {label}", 0.01, "mock-model")

        with patch("pdd.agentic_bug_orchestrator.run_agentic_task", side_effect=mock_run_agentic_task), \
             patch("pdd.agentic_bug_orchestrator.console"), \
             patch("pdd.agentic_bug_orchestrator._setup_worktree", return_value=(mock_worktree, None)), \
             patch("subprocess.run") as mock_subprocess:

            # Mock gh issue view to return that #520 is CLOSED (resolved)
            def subprocess_side_effect(*args, **kwargs):
                cmd = args[0] if args else kwargs.get('args', [])
                if isinstance(cmd, list) and 'gh' in cmd and 'issue' in cmd and 'view' in cmd:
                    # Return mock JSON showing issue #520 is CLOSED
                    mock_result = subprocess.CompletedProcess(
                        args=cmd,
                        returncode=0,
                        stdout='{"number": 520, "state": "CLOSED", "title": "Bug with pdd"}\n',
                        stderr=''
                    )
                    return mock_result
                # For git commands, return success
                return subprocess.CompletedProcess(
                    args=cmd, returncode=0, stdout='', stderr=''
                )

            mock_subprocess.side_effect = subprocess_side_effect

            success, message, cost, model, files = run_agentic_bug_orchestrator(
                issue_url="https://github.com/promptdriven/pdd/issues/530",
                issue_content="PDD bug agents still closes duplicated issues that are not resolved",
                repo_owner="promptdriven",
                repo_name="pdd",
                issue_number=530,
                issue_author="jiaminc-cmu",
                issue_title="pdd bug agents still closes duplicated issues that are not resolved",
                cwd=mock_git_repo,
                verbose=False,
                quiet=True,
                use_github_state=False,
            )

        # Workflow should stop at Step 1 — this is CORRECT behavior for resolved duplicates
        assert success is False, (
            "Workflow should stop for resolved duplicates. This is the correct behavior."
        )
        assert "Stopped at Step 1" in message, (
            f"Message should indicate Step 1 hard stop. Got: {message}"
        )
        assert "duplicate" in message.lower(), (
            f"Message should mention duplicate. Got: {message}"
        )
        assert len(steps_executed) == 1, (
            f"Only Step 1 should execute for a resolved duplicate. "
            f"Got: {steps_executed}"
        )

    def test_exact_scenario_issue_533_with_real_issue_numbers(self, mock_git_repo):
        """
        E2E Test: Exact scenario from issue #533 using real issue numbers.

        Real-world events:
        - User filed issue #530 about a bug
        - LLM Step 1 output: "Duplicate of #520"
        - Issue #520 was OPEN (unresolved)
        - Orchestrator stopped workflow and closed #530
        - User had to manually reopen #530

        This test verifies the orchestrator should validate that #520 is OPEN
        and continue the workflow instead of blindly trusting the LLM.
        """
        mock_worktree = mock_git_repo / ".pdd" / "worktrees" / "fix-issue-530"
        mock_worktree.mkdir(parents=True, exist_ok=True)

        steps_executed = []

        def mock_run_agentic_task(instruction, cwd, verbose, quiet, timeout, label, max_retries):
            """Mock LLM that reproduces the exact output from issue #533."""
            match = re.search(r"step(\d+(?:_\d+)?)", label)
            if match:
                steps_executed.append(label)

            if "step1" in label:
                # Reproduce the exact LLM output that caused issue #533
                return (
                    True,
                    "## Step 1: Duplicate Check\n\n"
                    "**Status:** Duplicate of #520\n\n"
                    "This issue appears to be a duplicate of #520.\n",
                    0.01,
                    "mock-model",
                )

            if "step7" in label:
                return (True, "Generated unit test\nFILES_CREATED: test_fix.py", 0.01, "mock-model")

            return (True, f"Mock output for {label}", 0.01, "mock-model")

        with patch("pdd.agentic_bug_orchestrator.run_agentic_task", side_effect=mock_run_agentic_task), \
             patch("pdd.agentic_bug_orchestrator.console"), \
             patch("pdd.agentic_bug_orchestrator._setup_worktree", return_value=(mock_worktree, None)), \
             patch("subprocess.run") as mock_subprocess:

            # Mock gh issue view to return that #520 is OPEN (matching real scenario)
            def subprocess_side_effect(*args, **kwargs):
                cmd = args[0] if args else kwargs.get('args', [])
                if isinstance(cmd, list) and 'gh' in cmd and 'issue' in cmd and 'view' in cmd and '520' in str(cmd):
                    # Return mock JSON showing issue #520 is OPEN (unresolved)
                    mock_result = subprocess.CompletedProcess(
                        args=cmd,
                        returncode=0,
                        stdout='{"number": 520, "state": "OPEN", "title": "pdd fails to use the latest version of claude 3.7 sonnet"}\n',
                        stderr=''
                    )
                    return mock_result
                # For git commands, return success
                return subprocess.CompletedProcess(
                    args=cmd, returncode=0, stdout='', stderr=''
                )

            mock_subprocess.side_effect = subprocess_side_effect

            success, message, cost, model, files = run_agentic_bug_orchestrator(
                issue_url="https://github.com/promptdriven/pdd/issues/530",
                issue_content="For example, this one:https://github.com/promptdriven/pdd/issues/520; I had to manually reopen it",
                repo_owner="promptdriven",
                repo_name="pdd",
                issue_number=530,
                issue_author="jiaminc-cmu",
                issue_title="pdd bug agents still closes duplicated issues that are not resolved",
                cwd=mock_git_repo,
                verbose=False,
                quiet=True,
                use_github_state=False,
            )

        # This is the exact scenario from issue #533 - workflow should continue
        assert success is True, (
            f"BUG DETECTED (Issue #533 - Exact Scenario): This reproduces the exact "
            f"bug reported in issue #533 where issue #530 was incorrectly closed as "
            f"a duplicate of the still-OPEN issue #520. The orchestrator should "
            f"validate that #520 is OPEN and continue the workflow. "
            f"Instead got: success={success}, msg={message}"
        )
        assert len(steps_executed) == 11, (
            f"All 11 steps should execute. Issue #530 should NOT be closed as a "
            f"duplicate when #520 is still OPEN. Got {len(steps_executed)} steps: {steps_executed}"
        )
