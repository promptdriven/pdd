"""
Tests for Issue #469: Duplicate detection should not close issues when the
original issue was unresolved.

Bug: When Step 1 finds a "duplicate" but the previous issue's workflow had
completely failed (all steps FAILED), the system still closed the new issue
and blocked the user from making progress.

Root cause:
1. Prompt defect: The step1_duplicate_LLM.prompt files unconditionally
   instructed the LLM to close duplicates without checking resolution status.
2. Orchestrator defect: The hard-stop logic checks for "Duplicate of #" in
   output with no validation of the original issue's resolution state.

Fix: The prompts now instruct the LLM to verify the original issue's
resolution status before declaring a duplicate. If unresolved, the LLM
should NOT output "Duplicate of #" and the workflow should proceed.

These tests verify:
- Prompt regression: All three prompts contain resolution-status checking
- Bug orchestrator: Unresolved duplicate does not trigger hard stop
- Change orchestrator: _check_hard_stop returns None for unresolved output
- Test orchestrator: _check_hard_stop returns None for unresolved output
- Various output patterns that mention related issues conversationally
"""

import pytest
from pathlib import Path
from unittest.mock import patch

from pdd.agentic_bug_orchestrator import run_agentic_bug_orchestrator
from pdd.agentic_change_orchestrator import (
    _check_hard_stop as change_check_hard_stop,
)
from pdd.agentic_test_orchestrator import (
    _check_hard_stop as _testorch_check_hard_stop,
)


# ---------------------------------------------------------------------------
# Helpers
# ---------------------------------------------------------------------------

def _get_prompts_dir() -> Path:
    """Return the prompts directory relative to the project root."""
    # Navigate up from tests/ to project root
    return Path(__file__).resolve().parent.parent / "prompts"


# ---------------------------------------------------------------------------
# Fixtures
# ---------------------------------------------------------------------------

@pytest.fixture
def bug_mock_dependencies(tmp_path):
    """Mocks for the bug orchestrator."""
    mock_worktree_path = tmp_path / ".pdd" / "worktrees" / "fix-issue-1"
    mock_worktree_path.mkdir(parents=True, exist_ok=True)

    with patch("pdd.agentic_bug_orchestrator.run_agentic_task") as mock_run, \
         patch("pdd.agentic_bug_orchestrator.load_prompt_template") as mock_load, \
         patch("pdd.agentic_bug_orchestrator.console") as mock_console, \
         patch("pdd.agentic_bug_orchestrator._setup_worktree") as mock_worktree:

        mock_run.return_value = (True, "Step output", 0.1, "gpt-4")
        mock_load.return_value = "Prompt for {issue_number}"
        mock_worktree.return_value = (mock_worktree_path, None)

        yield mock_run, mock_load, mock_console


@pytest.fixture
def bug_default_args(tmp_path):
    """Default arguments for the bug orchestrator."""
    return {
        "issue_url": "http://github.com/owner/repo/issues/469",
        "issue_content": "Bug description",
        "repo_owner": "owner",
        "repo_name": "repo",
        "issue_number": 469,
        "issue_author": "user",
        "issue_title": "Bug Title",
        "cwd": tmp_path,
        "verbose": False,
        "quiet": True,
        "use_github_state": False,
    }


@pytest.fixture
def test_default_args():
    """Default arguments for the test orchestrator."""
    return {
        "issue_url": "http://github.com/o/r/issues/469",
        "issue_content": "Test request",
        "repo_owner": "owner",
        "repo_name": "repo",
        "issue_number": 469,
        "issue_author": "user",
        "issue_title": "Test Generation",
        "cwd": Path("/cwd"),
        "quiet": True,
    }


# ---------------------------------------------------------------------------
# Test 1: Bug orchestrator — unresolved original → workflow continues
# ---------------------------------------------------------------------------

def test_bug_orchestrator_unresolved_duplicate_continues(
    bug_mock_dependencies, bug_default_args
):
    """
    When Step 1 reports that a related issue exists but was UNRESOLVED,
    the output should NOT contain 'Duplicate of #' and the workflow
    should continue past Step 1 to subsequent steps.

    This is the core scenario from issue #469: the user filed a new issue
    because the original (#468) had completely failed, but the old prompt
    unconditionally told the LLM to close it as a duplicate.
    """
    mock_run, _, _ = bug_mock_dependencies

    # Simulate the LLM following the FIXED prompt: it found a related issue
    # but the original was unresolved, so it does NOT say "Duplicate of #".
    # Instead it says the issue should proceed.
    unresolved_output = (
        "## Step 1: Duplicate Check\n\n"
        "**Status:** No duplicates found\n\n"
        "### Findings\n"
        "Found related issue #468, but its workflow completely failed "
        "(all steps returned FAILED). The original issue was never resolved. "
        "This issue should proceed with investigation."
    )

    def side_effect(*args, **kwargs):
        label = kwargs.get("label", "")
        if label == "step1":
            return (True, unresolved_output, 0.1, "gpt-4")
        if label == "step7":
            return (True, "Generated test\nFILES_CREATED: test_fix.py", 0.1, "gpt-4")
        return (True, f"Output for {label}", 0.1, "gpt-4")

    mock_run.side_effect = side_effect

    success, msg, cost, model, files = run_agentic_bug_orchestrator(
        **bug_default_args
    )

    # Workflow should continue past Step 1 and complete all 11 steps
    assert success is True, (
        f"Workflow should have continued when original was unresolved, "
        f"but got: {msg}"
    )
    assert mock_run.call_count == 11  # All 11 steps executed
    assert "Investigation complete" in msg


# ---------------------------------------------------------------------------
# Test 2: Bug orchestrator — resolved original → workflow stops (regression)
# ---------------------------------------------------------------------------

def test_bug_orchestrator_resolved_duplicate_stops(
    bug_mock_dependencies, bug_default_args
):
    """
    When Step 1 reports that the issue IS a duplicate of a resolved issue,
    the output contains 'Duplicate of #' and the workflow should stop.
    This is a regression test to ensure we don't break the valid duplicate
    detection path.
    """
    mock_run, _, _ = bug_mock_dependencies

    # The LLM found a true duplicate whose original was resolved
    resolved_output = (
        "## Step 1: Duplicate Check\n\n"
        "**Status:** Duplicate of #468\n\n"
        "### Findings\n"
        "Issue #468 was resolved with a merged fix in PR #470. "
        "This issue is a duplicate. Closing."
    )
    mock_run.return_value = (True, resolved_output, 0.05, "claude")

    success, msg, cost, _, _ = run_agentic_bug_orchestrator(**bug_default_args)

    assert success is False
    assert "Stopped at Step 1" in msg
    assert "duplicate" in msg.lower()
    assert mock_run.call_count == 1
    assert cost == 0.05


# ---------------------------------------------------------------------------
# Test 3: Change orchestrator — _check_hard_stop returns None for unresolved
# ---------------------------------------------------------------------------

def test_change_hard_stop_unresolved_duplicate_returns_none():
    """
    When Step 1 output mentions a related issue that was unresolved,
    _check_hard_stop should return None (no hard stop), allowing the
    workflow to continue.
    """
    unresolved_output = (
        "## Step 1: Duplicate Check\n\n"
        "**Status:** No duplicates found\n\n"
        "### Findings\n"
        "Found related issue #468, but the original was never resolved. "
        "This issue should proceed."
    )

    result = change_check_hard_stop(step_num=1, output=unresolved_output)
    assert result is None, (
        f"_check_hard_stop should return None for unresolved duplicate, "
        f"but got: {result}"
    )


# ---------------------------------------------------------------------------
# Test 4: Test orchestrator — _check_hard_stop returns None for unresolved
# ---------------------------------------------------------------------------

def test_test_hard_stop_unresolved_duplicate_returns_none():
    """
    When Step 1 output mentions a related issue that was unresolved,
    _check_hard_stop should return None (no hard stop), allowing the
    workflow to continue.
    """
    unresolved_output = (
        "## Step 1: Duplicate Check\n\n"
        "**Status:** No duplicates found\n\n"
        "### Findings\n"
        "Found related issue #468, but its workflow completely failed. "
        "The original issue was never resolved. Proceeding with this issue."
    )

    result = _testorch_check_hard_stop(step_num=1, output=unresolved_output)
    assert result is None, (
        f"_check_hard_stop should return None for unresolved duplicate, "
        f"but got: {result}"
    )


# ---------------------------------------------------------------------------
# Test 5: _check_hard_stop — conversational mentions of issues
# ---------------------------------------------------------------------------

class TestCheckHardStopConversationalMentions:
    """
    Verify that _check_hard_stop does NOT trigger on outputs that mention
    related issues conversationally without the exact 'Duplicate of #' trigger.
    These outputs are what the fixed prompt produces when it finds a related
    but unresolved issue.
    """

    @pytest.mark.parametrize(
        "output",
        [
            # Mentions related issue but says to proceed
            "Found related issue #468 but it was never resolved. Proceeding.",
            # Mentions issue number in analysis without duplicate marker
            "Issue #468 had similar symptoms but all workflow steps failed. "
            "This appears to be a fresh investigation.",
            # Contains the word 'duplicate' but not 'Duplicate of #'
            "This may be a duplicate attempt at fixing issue #468, which was "
            "not successfully resolved. Treating as new issue.",
            # Status explicitly says no duplicates
            "**Status:** No duplicates found\n\n"
            "Related to #468 which failed to resolve.",
        ],
        ids=[
            "related_but_unresolved",
            "similar_symptoms_failed_workflow",
            "word_duplicate_without_trigger",
            "status_no_duplicates",
        ],
    )
    def test_change_no_hard_stop_on_conversational_mention(self, output):
        """Change orchestrator should not hard-stop on conversational mentions."""
        result = change_check_hard_stop(step_num=1, output=output)
        assert result is None, (
            f"Should not hard-stop on conversational mention, got: {result}"
        )

    @pytest.mark.parametrize(
        "output",
        [
            "Found related issue #468 but it was never resolved. Proceeding.",
            "Issue #468 had similar symptoms but all workflow steps failed.",
            "This may be a duplicate attempt at fixing issue #468.",
            "**Status:** No duplicates found\n\nRelated to #468.",
        ],
        ids=[
            "related_but_unresolved",
            "similar_symptoms_failed_workflow",
            "word_duplicate_without_trigger",
            "status_no_duplicates",
        ],
    )
    def test_test_no_hard_stop_on_conversational_mention(self, output):
        """Test orchestrator should not hard-stop on conversational mentions."""
        result = _testorch_check_hard_stop(step_num=1, output=output)
        assert result is None, (
            f"Should not hard-stop on conversational mention, got: {result}"
        )


# ---------------------------------------------------------------------------
# Test 6: Prompt regression — resolution status checking instructions
# ---------------------------------------------------------------------------

class TestPromptResolutionStatusCheck:
    """
    Regression tests to ensure all three step1_duplicate_LLM.prompt files
    contain instructions for verifying the original issue's resolution status
    before declaring a duplicate.

    These tests fail on the original buggy prompts which unconditionally
    instructed the LLM to close duplicates without any resolution check.
    """

    PROMPT_FILES = [
        "agentic_bug_step1_duplicate_LLM.prompt",
        "agentic_change_step1_duplicate_LLM.prompt",
        "agentic_test_step1_duplicate_LLM.prompt",
    ]

    def _read_prompt(self, filename: str) -> str:
        """Read a prompt file and return its content."""
        prompt_path = _get_prompts_dir() / filename
        assert prompt_path.exists(), f"Prompt file not found: {prompt_path}"
        return prompt_path.read_text()

    @pytest.mark.parametrize("prompt_file", PROMPT_FILES)
    def test_prompt_contains_resolution_status_verification(self, prompt_file):
        """
        Each prompt must instruct the LLM to verify the original issue's
        resolution status before declaring a duplicate.

        The original buggy prompts (pre-fix) did NOT contain these
        instructions, causing the LLM to unconditionally close duplicates
        even when the original was never resolved.
        """
        content = self._read_prompt(prompt_file)

        # Must contain instructions about checking resolution status
        assert "resolution" in content.lower() or "resolved" in content.lower(), (
            f"{prompt_file} must contain instructions about checking "
            f"resolution status of the original issue"
        )

    @pytest.mark.parametrize("prompt_file", PROMPT_FILES)
    def test_prompt_contains_unresolved_handling(self, prompt_file):
        """
        Each prompt must contain instructions for handling the case where
        the original issue is unresolved (do NOT close the new issue).

        The original buggy prompts had no concept of 'unresolved' — they
        just said to close any duplicate found.
        """
        content = self._read_prompt(prompt_file)

        # Must mention 'unresolved' handling
        assert "unresolved" in content.lower(), (
            f"{prompt_file} must contain handling for unresolved originals. "
            f"Without this, duplicates of failed issues get incorrectly closed."
        )

    @pytest.mark.parametrize("prompt_file", PROMPT_FILES)
    def test_prompt_does_not_unconditionally_close(self, prompt_file):
        """
        The prompt must NOT unconditionally instruct closing duplicates.
        It should have conditional logic: only close if the original was resolved.

        The original buggy prompt at line 35 said:
        'Close this issue with a comment linking to the original'
        without any condition on resolution status.
        """
        content = self._read_prompt(prompt_file)

        # The prompt should have CONDITIONAL closing logic
        # It must mention both resolved AND unresolved paths
        has_resolved_path = "resolved" in content.lower()
        has_unresolved_path = "unresolved" in content.lower()

        assert has_resolved_path and has_unresolved_path, (
            f"{prompt_file} must have both resolved and unresolved handling paths. "
            f"has_resolved={has_resolved_path}, has_unresolved={has_unresolved_path}. "
            f"The original buggy prompt only had unconditional closing."
        )

    @pytest.mark.parametrize("prompt_file", PROMPT_FILES)
    def test_prompt_contains_gh_issue_view_instruction(self, prompt_file):
        """
        Each prompt must instruct the LLM to use 'gh issue view' to check
        the original issue's state before declaring a duplicate.

        This ensures the LLM actually verifies resolution status rather
        than making assumptions.
        """
        content = self._read_prompt(prompt_file)

        assert "gh issue view" in content, (
            f"{prompt_file} must instruct the LLM to use 'gh issue view' "
            f"to check the original issue's resolution status."
        )
