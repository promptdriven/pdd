"""
Tests for Issue #533: Orchestrator should validate LLM duplicate detection output.

Bug: The orchestrator at line 441 of agentic_bug_orchestrator.py blindly trusts
the LLM's duplicate detection output without validating that the original issue
is actually resolved. When the LLM fails to follow prompt instructions and outputs
"Duplicate of #520" even though #520 is OPEN, the orchestrator incorrectly triggers
a hard stop and closes the issue.

Root cause:
The hard stop at line 441 checks for the string "Duplicate of #" but doesn't
validate the original issue's state:
    if step_num == 1 and "Duplicate of #" in output:
        msg = f"Stopped at Step 1: Issue is a duplicate. {output.strip()}"
        return False, msg, total_cost, last_model_used, changed_files

Fix:
The orchestrator should validate the original issue's state using `gh issue view`
before triggering the hard stop. If the original issue is still OPEN (unresolved),
the orchestrator should log a warning and continue the workflow instead of stopping.

These tests verify:
1. When LLM outputs duplicate of UNRESOLVED issue → orchestrator validates & continues
2. When LLM outputs duplicate of RESOLVED issue → hard stop works correctly
3. Edge cases: invalid issue numbers, network errors, various output formats
4. Fail-safe behavior: errors default to letting workflow continue

This is a regression of issue #469, which fixed the prompts but didn't add
orchestrator-level validation as defense-in-depth.
"""

import pytest
from pathlib import Path
from unittest.mock import patch, MagicMock
import subprocess

from pdd.agentic_bug_orchestrator import run_agentic_bug_orchestrator


# ---------------------------------------------------------------------------
# Fixtures
# ---------------------------------------------------------------------------

@pytest.fixture
def bug_mock_dependencies(tmp_path):
    """Mocks for the bug orchestrator."""
    mock_worktree_path = tmp_path / ".pdd" / "worktrees" / "fix-issue-533"
    mock_worktree_path.mkdir(parents=True, exist_ok=True)

    with patch("pdd.agentic_bug_orchestrator.run_agentic_task") as mock_run, \
         patch("pdd.agentic_bug_orchestrator.load_prompt_template") as mock_load, \
         patch("pdd.agentic_bug_orchestrator.console") as mock_console, \
         patch("pdd.agentic_bug_orchestrator._setup_worktree") as mock_worktree:

        mock_run.return_value = (True, "Step output", 0.1, "gpt-4")
        mock_load.return_value = "Prompt for {issue_number}"
        mock_worktree.return_value = (mock_worktree_path, None)

        yield mock_run, mock_load, mock_console, mock_worktree


@pytest.fixture
def bug_default_args(tmp_path):
    """Default arguments for the bug orchestrator."""
    return {
        "issue_url": "http://github.com/owner/repo/issues/533",
        "issue_content": "Bug description",
        "repo_owner": "owner",
        "repo_name": "repo",
        "issue_number": 533,
        "issue_author": "user",
        "issue_title": "Bug Title",
        "cwd": tmp_path,
        "verbose": False,
        "quiet": True,
        "use_github_state": False,
    }


# ---------------------------------------------------------------------------
# Test 1: LLM outputs duplicate of UNRESOLVED issue → workflow should continue
# ---------------------------------------------------------------------------

def test_bug_orchestrator_llm_outputs_duplicate_of_unresolved_issue(
    bug_mock_dependencies, bug_default_args
):
    """
    PRIMARY BUG SCENARIO: When the LLM fails to follow prompt instructions and
    outputs "Duplicate of #520" even though #520 is OPEN (unresolved), the
    orchestrator should validate the original issue's state and continue the
    workflow instead of incorrectly stopping.

    This test simulates the exact scenario from issue #533/#530/#520:
    - Issue #530 reports a bug
    - LLM outputs "Duplicate of #520" (failing to check resolution status)
    - Issue #520 is still OPEN (unresolved)
    - Expected: Orchestrator validates, logs warning, continues to Step 2
    - Buggy behavior: Hard stop at Step 1, issue closed as duplicate

    This test will FAIL on the current buggy code (before fix) because line 441
    doesn't validate the original issue's state.
    """
    mock_run, _, _, _ = bug_mock_dependencies

    # Simulate LLM failing to follow instructions: outputs duplicate without
    # checking that the original issue is still OPEN
    llm_output_duplicate_unresolved = (
        "## Step 1: Duplicate Check\n\n"
        "**Status:** Duplicate of #520\n\n"
        "### Findings\n"
        "This issue has the same symptoms as #520."
    )

    def side_effect(*args, **kwargs):
        label = kwargs.get("label", "")
        if label == "step1":
            return (True, llm_output_duplicate_unresolved, 0.1, "gpt-4")
        if label == "step7":
            return (True, "Generated test\nFILES_CREATED: test_fix.py", 0.1, "gpt-4")
        return (True, f"Output for {label}", 0.1, "gpt-4")

    mock_run.side_effect = side_effect

    # Mock gh issue view to return OPEN state for issue #520
    with patch("subprocess.run") as mock_subprocess:
        # gh issue view #520 should return OPEN state
        mock_result = MagicMock()
        mock_result.returncode = 0
        mock_result.stdout = "state: OPEN\ntitle: Original Issue\n"
        mock_subprocess.return_value = mock_result

        success, msg, cost, model, files = run_agentic_bug_orchestrator(
            **bug_default_args
        )

    # CRITICAL ASSERTION: Workflow should continue (not stop at Step 1)
    # The buggy code will FAIL this assertion because it triggers hard stop
    # without validating the original issue's state
    assert success is True, (
        f"Workflow should continue when LLM outputs duplicate of UNRESOLVED issue. "
        f"The orchestrator should validate that #520 is OPEN and not trigger hard stop. "
        f"Instead got: success={success}, msg={msg}"
    )

    # Verify workflow completed all steps (not stopped at Step 1)
    assert mock_run.call_count == 11, (
        f"All 11 steps should execute when original issue is unresolved. "
        f"Got {mock_run.call_count} steps instead."
    )

    assert "Investigation complete" in msg, (
        f"Expected completion message, got: {msg}"
    )


# ---------------------------------------------------------------------------
# Test 2: LLM outputs duplicate of RESOLVED issue → hard stop (regression test)
# ---------------------------------------------------------------------------

def test_bug_orchestrator_llm_outputs_duplicate_of_resolved_issue(
    bug_mock_dependencies, bug_default_args
):
    """
    REGRESSION TEST: When the LLM outputs "Duplicate of #520" and #520 is
    actually CLOSED (resolved), the orchestrator should trigger the hard stop.
    This is the correct behavior and should not be broken by the fix.

    This ensures we don't break valid duplicate detection when fixing the bug.
    """
    mock_run, _, _, _ = bug_mock_dependencies

    # LLM correctly outputs duplicate of a resolved issue
    llm_output_duplicate_resolved = (
        "## Step 1: Duplicate Check\n\n"
        "**Status:** Duplicate of #520\n\n"
        "### Findings\n"
        "Issue #520 was resolved in PR #525. This is a duplicate."
    )
    mock_run.return_value = (True, llm_output_duplicate_resolved, 0.05, "claude")

    # Mock gh issue view to return CLOSED state for issue #520
    with patch("subprocess.run") as mock_subprocess:
        mock_result = MagicMock()
        mock_result.returncode = 0
        mock_result.stdout = "state: CLOSED\ntitle: Original Issue\n"
        mock_subprocess.return_value = mock_result

        success, msg, cost, _, _ = run_agentic_bug_orchestrator(**bug_default_args)

    # Hard stop should be triggered (correct duplicate detection)
    assert success is False, (
        f"Workflow should stop when original issue is CLOSED. Got success={success}"
    )
    assert "Stopped at Step 1" in msg
    assert "duplicate" in msg.lower()
    assert mock_run.call_count == 1
    assert cost == 0.05


# ---------------------------------------------------------------------------
# Test 3: Various duplicate output formats
# ---------------------------------------------------------------------------

class TestDuplicateOutputFormats:
    """
    Test that the orchestrator correctly extracts issue numbers from various
    LLM output formats and validates them.
    """

    @pytest.mark.parametrize(
        "llm_output,expected_issue_num",
        [
            # Standard format
            ("Duplicate of #520", "520"),
            # With context
            ("Duplicate of #520 (resolved in PR #525)", "520"),
            # Multiple issue mentions (should extract first after "Duplicate of")
            ("Related to #100, but Duplicate of #520", "520"),
            # With markdown
            ("**Status:** Duplicate of #520\n\nClosing.", "520"),
        ],
        ids=[
            "standard_format",
            "with_pr_reference",
            "multiple_issues",
            "with_markdown",
        ],
    )
    def test_duplicate_extraction_formats(
        self, bug_mock_dependencies, bug_default_args, llm_output, expected_issue_num
    ):
        """
        Verify the orchestrator correctly extracts issue numbers from various
        output formats and validates them with gh issue view.
        """
        mock_run, _, _, _ = bug_mock_dependencies
        mock_run.return_value = (True, llm_output, 0.05, "claude")

        # Mock gh issue view to return OPEN state
        with patch("subprocess.run") as mock_subprocess:
            mock_result = MagicMock()
            mock_result.returncode = 0
            mock_result.stdout = "state: OPEN\ntitle: Issue\n"
            mock_subprocess.return_value = mock_result

            success, msg, _, _, _ = run_agentic_bug_orchestrator(**bug_default_args)

            # Verify gh issue view was called with correct issue number
            assert mock_subprocess.called, (
                "orchestrator should call gh issue view to validate"
            )
            # Find the call that checks the issue state
            gh_calls = [
                call for call in mock_subprocess.call_args_list
                if call[0][0][0:2] == ["gh", "issue"]
            ]
            assert len(gh_calls) > 0, "Should have called gh issue view"
            # Extract issue number from the call
            assert expected_issue_num in str(gh_calls[0]), (
                f"Should check issue #{expected_issue_num}, calls: {gh_calls}"
            )

        # Since original is OPEN, workflow should continue
        assert success is True, f"Should continue when original is OPEN, got: {msg}"


# ---------------------------------------------------------------------------
# Test 4: Invalid issue number handling
# ---------------------------------------------------------------------------

def test_bug_orchestrator_invalid_issue_number_failsafe(
    bug_mock_dependencies, bug_default_args
):
    """
    FAIL-SAFE TEST: When the LLM outputs a duplicate of a non-existent issue
    (e.g., #99999), gh issue view will fail. The orchestrator should treat
    this as "unresolved" (fail-safe) and let the workflow continue rather
    than crashing or incorrectly stopping.
    """
    mock_run, _, _, _ = bug_mock_dependencies

    llm_output_invalid = "Duplicate of #99999"

    def side_effect(*args, **kwargs):
        label = kwargs.get("label", "")
        if label == "step1":
            return (True, llm_output_invalid, 0.1, "gpt-4")
        if label == "step7":
            return (True, "Generated test\nFILES_CREATED: test_fix.py", 0.1, "gpt-4")
        return (True, f"Output for {label}", 0.1, "gpt-4")

    mock_run.side_effect = side_effect

    # Mock gh issue view to return error (issue not found)
    with patch("subprocess.run") as mock_subprocess:
        mock_result = MagicMock()
        mock_result.returncode = 1  # Error
        mock_result.stderr = "issue not found"
        mock_subprocess.return_value = mock_result

        success, msg, _, _, _ = run_agentic_bug_orchestrator(**bug_default_args)

    # Fail-safe: should continue workflow (treat as unresolved)
    assert success is True, (
        f"When gh issue view fails, orchestrator should fail-safe and continue. "
        f"Got: success={success}, msg={msg}"
    )


# ---------------------------------------------------------------------------
# Test 5: Network/CLI error handling
# ---------------------------------------------------------------------------

def test_bug_orchestrator_gh_cli_error_failsafe(
    bug_mock_dependencies, bug_default_args
):
    """
    FAIL-SAFE TEST: When gh CLI fails (network error, timeout, rate limit),
    the orchestrator should log the error and treat the issue as unresolved
    (fail-safe), allowing the workflow to continue.
    """
    mock_run, _, _, _ = bug_mock_dependencies

    llm_output = "Duplicate of #520"

    def side_effect(*args, **kwargs):
        label = kwargs.get("label", "")
        if label == "step1":
            return (True, llm_output, 0.1, "gpt-4")
        if label == "step7":
            return (True, "Generated test\nFILES_CREATED: test_fix.py", 0.1, "gpt-4")
        return (True, f"Output for {label}", 0.1, "gpt-4")

    mock_run.side_effect = side_effect

    # Mock subprocess.run to handle both git commands and gh commands
    with patch("subprocess.run") as mock_subprocess:
        def subprocess_side_effect(cmd, *args, **kwargs):
            # Let git commands work normally (needed for _get_git_root)
            if cmd[0] == "git":
                mock_result = MagicMock()
                mock_result.returncode = 0
                mock_result.stdout = str(bug_default_args["cwd"])
                return mock_result
            # Make gh commands raise timeout
            elif cmd[0] == "gh":
                raise subprocess.TimeoutExpired("gh", 5)
            # Default
            mock_result = MagicMock()
            mock_result.returncode = 0
            return mock_result

        mock_subprocess.side_effect = subprocess_side_effect

        success, msg, _, _, _ = run_agentic_bug_orchestrator(**bug_default_args)

    # Fail-safe: should continue workflow
    assert success is True, (
        f"When gh CLI fails/times out, orchestrator should fail-safe and continue. "
        f"Got: success={success}, msg={msg}"
    )


# ---------------------------------------------------------------------------
# Test 6: Regression test - exact scenario from issue #533
# ---------------------------------------------------------------------------

def test_bug_orchestrator_issue_533_exact_scenario(
    bug_mock_dependencies, bug_default_args
):
    """
    REGRESSION TEST FOR ISSUE #533: Simulate the exact scenario that triggered
    the bug report:
    - User filed issue #530
    - LLM output "Duplicate of #520" without checking resolution
    - Issue #520 was still OPEN (created 2026-02-14, never resolved)
    - Bug: Orchestrator closed #530 as duplicate
    - Fix: Orchestrator should validate #520 is OPEN and continue workflow

    This test uses the actual issue numbers from the incident.
    """
    mock_run, _, _, _ = bug_mock_dependencies

    # Update args to simulate issue #530
    bug_default_args["issue_number"] = 530
    bug_default_args["issue_url"] = "http://github.com/owner/repo/issues/530"

    # LLM output that triggered the bug (claims #520 is duplicate)
    llm_output_530 = (
        "## Step 1: Duplicate Check\n\n"
        "Duplicate of #520\n\n"
        "This issue appears to be the same as #520."
    )

    def side_effect(*args, **kwargs):
        label = kwargs.get("label", "")
        if label == "step1":
            return (True, llm_output_530, 0.1, "gpt-4")
        if label == "step7":
            return (True, "Generated test\nFILES_CREATED: test_fix.py", 0.1, "gpt-4")
        return (True, f"Output for {label}", 0.1, "gpt-4")

    mock_run.side_effect = side_effect

    # Mock gh issue view for #520 - it's still OPEN (unresolved)
    with patch("subprocess.run") as mock_subprocess:
        mock_result = MagicMock()
        mock_result.returncode = 0
        mock_result.stdout = "state: OPEN\ntitle: Original bug\ncreatedAt: 2026-02-14\n"
        mock_subprocess.return_value = mock_result

        success, msg, _, _, _ = run_agentic_bug_orchestrator(**bug_default_args)

    # The fix should prevent the buggy hard stop
    assert success is True, (
        f"Issue #530 should NOT have been closed as duplicate of unresolved #520. "
        f"This is the exact bug from issue #533. Got: success={success}, msg={msg}"
    )
    assert "Investigation complete" in msg


# ---------------------------------------------------------------------------
# Test 7: No false positives - conversational mentions shouldn't validate
# ---------------------------------------------------------------------------

def test_bug_orchestrator_no_validation_without_duplicate_marker(
    bug_mock_dependencies, bug_default_args
):
    """
    Verify that the orchestrator only validates when the LLM output contains
    the exact "Duplicate of #" marker. Conversational mentions of related
    issues should not trigger validation.

    This ensures the fix doesn't add unnecessary overhead for outputs that
    mention related issues without claiming they are duplicates.
    """
    mock_run, _, _, _ = bug_mock_dependencies

    # Output mentions related issue but doesn't claim duplicate
    llm_output_no_duplicate = (
        "## Step 1: Duplicate Check\n\n"
        "**Status:** No duplicates found\n\n"
        "### Findings\n"
        "Found related issue #520, but it has different symptoms. "
        "Proceeding with investigation."
    )

    def side_effect(*args, **kwargs):
        label = kwargs.get("label", "")
        if label == "step1":
            return (True, llm_output_no_duplicate, 0.1, "gpt-4")
        if label == "step7":
            return (True, "Generated test\nFILES_CREATED: test_fix.py", 0.1, "gpt-4")
        return (True, f"Output for {label}", 0.1, "gpt-4")

    mock_run.side_effect = side_effect

    # Mock subprocess to track if gh issue view is called
    with patch("subprocess.run") as mock_subprocess:
        mock_result = MagicMock()
        mock_result.returncode = 0
        mock_result.stdout = "state: OPEN\n"
        mock_subprocess.return_value = mock_result

        success, msg, _, _, _ = run_agentic_bug_orchestrator(**bug_default_args)

    # Workflow should continue
    assert success is True, f"Workflow should continue, got: {msg}"

    # gh issue view should NOT have been called (no duplicate marker)
    # Note: This checks that we don't add unnecessary validation overhead
    # when the LLM correctly follows instructions and doesn't claim a duplicate
    gh_calls = [
        call for call in mock_subprocess.call_args_list
        if call[0][0][0:2] == ["gh", "issue"]
    ]
    assert len(gh_calls) == 0, (
        "Should not call gh issue view when no 'Duplicate of #' marker present"
    )
