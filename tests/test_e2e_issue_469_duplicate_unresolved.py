"""
E2E tests for Issue #469: Duplicate detection should not close issues when the
original issue was unresolved.

These E2E tests differ from the unit tests in test_issue_469_duplicate_unresolved.py:
- Unit tests mock load_prompt_template and test orchestrator logic in isolation
- E2E tests use REAL prompt loading via load_prompt_template (not mocked)
- E2E tests exercise the full pipeline: prompt file → preprocess → format → orchestrator

Bug: When Step 1 found a "duplicate" but the original issue's workflow had completely
failed, the system still closed the new issue because:
1. The original prompt had no instructions to check resolution status
2. The orchestrator hard-stops on "Duplicate of #" with no validation

Fix: The prompts now instruct the LLM to verify the original issue's resolution
status before declaring a duplicate.

Test Strategy:
- Test 1: Verify the REAL prompt pipeline produces instructions that include
  resolution-status checking (fails on original buggy prompt, passes on fixed)
- Test 2: Full orchestrator E2E where unresolved duplicate → workflow continues
- Test 3: Full orchestrator E2E where resolved duplicate → workflow stops (regression)
- Test 4: Verify all three prompt files through the real preprocessing pipeline
"""

import os
import re
import subprocess
from pathlib import Path
from unittest.mock import patch

import pytest

from pdd.agentic_bug_orchestrator import run_agentic_bug_orchestrator
from pdd.preprocess import preprocess

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


@pytest.mark.e2e
class TestIssue469DuplicateUnresolvedE2E:
    """
    E2E tests for Issue #469: Duplicate detection should check resolution status.

    These tests exercise the real prompt loading, preprocessing, and formatting
    pipeline — only the LLM execution layer (run_agentic_task) and git
    operations (_setup_worktree) are mocked.
    """

    def test_prompt_pipeline_includes_resolution_check(self):
        """
        E2E Test: The real prompt file, loaded and preprocessed through the
        same pipeline as the orchestrator, must contain resolution-status
        checking instructions.

        This test exercises:
        1. Real file I/O to read the prompt
        2. Real preprocess() to expand includes and escape braces
        3. Real format() with context variables

        On the ORIGINAL buggy prompt:
        - The prompt says "If duplicates are found:" with no resolution check
        - This test FAILS because "unresolved" is absent from the formatted prompt

        On the FIXED prompt:
        - The prompt says "Verify original issue resolution status" (step 3)
        - The prompt has conditional handling for resolved vs unresolved
        - This test PASSES
        """
        from pdd.load_prompt_template import load_prompt_template

        # Load through the real pipeline (same as orchestrator does)
        template = load_prompt_template("agentic_bug_step1_duplicate_LLM")
        assert template is not None, "Prompt template should load successfully"

        # Preprocess (same as orchestrator does at line 408)
        context = {
            "issue_url": "https://github.com/test/repo/issues/469",
            "issue_content": "Bug: duplicate closes unresolved issues",
            "repo_owner": "test",
            "repo_name": "repo",
            "issue_number": 469,
        }
        exclude_keys = list(context.keys())
        processed = preprocess(
            template,
            recursive=True,
            double_curly_brackets=True,
            exclude_keys=exclude_keys,
        )

        # Format (same as orchestrator does at line 412)
        formatted = processed.format(**context)

        # The formatted prompt MUST contain resolution-status checking
        assert "unresolved" in formatted.lower(), (
            "BUG DETECTED (Issue #469): The Step 1 duplicate prompt does not "
            "contain instructions for handling unresolved originals.\n\n"
            "The original buggy prompt unconditionally instructed the LLM to "
            "close duplicates without checking whether the original issue was "
            "actually resolved. This caused issue #469 to be closed even though "
            "the original #468 had completely failed.\n\n"
            "Expected: Prompt should instruct LLM to check resolution status "
            "and only close if the original was resolved."
        )

        assert "resolved" in formatted.lower(), (
            "BUG DETECTED (Issue #469): The Step 1 duplicate prompt does not "
            "mention 'resolved' — it lacks conditional duplicate handling."
        )

        assert "gh issue view" in formatted, (
            "BUG DETECTED (Issue #469): The Step 1 duplicate prompt does not "
            "instruct the LLM to use 'gh issue view' to verify the original "
            "issue's resolution status."
        )

    def test_unresolved_duplicate_workflow_continues(self, mock_git_repo):
        """
        E2E Test: When the LLM (following the fixed prompt) reports that the
        original issue was unresolved, the output does NOT contain
        "Duplicate of #" and the workflow continues past Step 1.

        This exercises the full code path:
        1. Real load_prompt_template (loads actual prompt file from disk)
        2. Real preprocess() and format() (expands includes, substitutes vars)
        3. Real orchestrator loop logic (step iteration, hard-stop checks)
        4. Mocked LLM (returns output consistent with the fixed prompt)
        5. Mocked worktree setup (avoids real git operations)

        The mock LLM simulates what a real LLM would do when following the
        FIXED prompt: finding a related issue that was unresolved, and NOT
        outputting "Duplicate of #".
        """
        mock_worktree = mock_git_repo / ".pdd" / "worktrees" / "fix-issue-469"
        mock_worktree.mkdir(parents=True, exist_ok=True)

        steps_executed = []

        def mock_run_agentic_task(instruction, cwd, verbose, quiet, timeout, label, max_retries):
            """Mock LLM that follows the fixed prompt for unresolved duplicates."""
            match = re.search(r"step(\d+(?:_\d+)?)", label)
            if match:
                steps_executed.append(label)

            if "step1" in label:
                # LLM follows FIXED prompt: found related issue but it was
                # unresolved, so does NOT say "Duplicate of #"
                return (
                    True,
                    "## Step 1: Duplicate Check\n\n"
                    "**Status:** No duplicates found\n\n"
                    "### Search Performed\n"
                    "- Searched for: duplicate detection, issue closing\n"
                    "- Issues reviewed: 3\n\n"
                    "### Findings\n"
                    "Found related issue #468 with similar symptoms. However, "
                    "after checking with `gh issue view 468`, the original issue "
                    "was never resolved — all workflow steps failed with "
                    "'FAILED: All agent providers failed'. The original issue "
                    "is unresolved, so this issue should proceed with "
                    "investigation as a new issue.\n\n"
                    "---\n"
                    "*Proceeding to Step 2: Documentation Check*",
                    0.01,
                    "mock-model",
                )

            if "step7" in label:
                return (True, "Generated unit test\nFILES_CREATED: test_fix.py", 0.01, "mock-model")

            return (True, f"Mock output for {label}", 0.01, "mock-model")

        with patch("pdd.agentic_bug_orchestrator.run_agentic_task", side_effect=mock_run_agentic_task), \
             patch("pdd.agentic_bug_orchestrator.console"), \
             patch("pdd.agentic_bug_orchestrator._setup_worktree", return_value=(mock_worktree, None)):

            success, message, cost, model, files = run_agentic_bug_orchestrator(
                issue_url="https://github.com/test/repo/issues/469",
                issue_content="PDD bug closes issue because duplicate was found, "
                              "but the previous issue was not resolved",
                repo_owner="test",
                repo_name="repo",
                issue_number=469,
                issue_author="jiaminc-cmu",
                issue_title="Duplicate closes unresolved issue",
                cwd=mock_git_repo,
                verbose=False,
                quiet=True,
                use_github_state=False,
            )

        # The workflow should have continued past Step 1 through all 11 steps
        assert success is True, (
            f"BUG DETECTED (Issue #469): Workflow should continue when the "
            f"original duplicate was unresolved, but it stopped: {message}"
        )
        assert "step1" in steps_executed, "Step 1 should have executed"
        assert len(steps_executed) == 11, (
            f"All 11 steps should execute when duplicate is unresolved. "
            f"Got {len(steps_executed)} steps: {steps_executed}"
        )

    def test_resolved_duplicate_workflow_stops(self, mock_git_repo):
        """
        E2E Regression Test: When the LLM correctly identifies a resolved
        duplicate and outputs "Duplicate of #468", the workflow should
        hard-stop at Step 1.

        This ensures the fix for #469 doesn't break the valid duplicate
        detection path.
        """
        mock_worktree = mock_git_repo / ".pdd" / "worktrees" / "fix-issue-469"
        mock_worktree.mkdir(parents=True, exist_ok=True)

        steps_executed = []

        def mock_run_agentic_task(instruction, cwd, verbose, quiet, timeout, label, max_retries):
            """Mock LLM that finds a resolved duplicate."""
            match = re.search(r"step(\d+(?:_\d+)?)", label)
            if match:
                steps_executed.append(label)

            if "step1" in label:
                # LLM found a resolved duplicate → outputs "Duplicate of #468"
                return (
                    True,
                    "## Step 1: Duplicate Check\n\n"
                    "**Status:** Duplicate of #468\n\n"
                    "### Search Performed\n"
                    "- Searched for: duplicate detection, issue closing\n"
                    "- Issues reviewed: 3\n\n"
                    "### Findings\n"
                    "Issue #468 was resolved with a merged fix in PR #470. "
                    "This issue is a confirmed duplicate. Closing.\n\n"
                    "---",
                    0.01,
                    "mock-model",
                )

            return (True, f"Mock output for {label}", 0.01, "mock-model")

        with patch("pdd.agentic_bug_orchestrator.run_agentic_task", side_effect=mock_run_agentic_task), \
             patch("pdd.agentic_bug_orchestrator.console"), \
             patch("pdd.agentic_bug_orchestrator._setup_worktree", return_value=(mock_worktree, None)):

            success, message, cost, model, files = run_agentic_bug_orchestrator(
                issue_url="https://github.com/test/repo/issues/469",
                issue_content="PDD bug closes issue because duplicate was found",
                repo_owner="test",
                repo_name="repo",
                issue_number=469,
                issue_author="jiaminc-cmu",
                issue_title="Duplicate closes unresolved issue",
                cwd=mock_git_repo,
                verbose=False,
                quiet=True,
                use_github_state=False,
            )

        # Workflow should stop at Step 1 — this is correct behavior for resolved dups
        assert success is False, "Workflow should stop for resolved duplicates"
        assert "Stopped at Step 1" in message
        assert "duplicate" in message.lower()
        assert len(steps_executed) == 1, (
            f"Only Step 1 should execute for a resolved duplicate. "
            f"Got: {steps_executed}"
        )


@pytest.mark.e2e
class TestIssue469AllPromptPipelinesE2E:
    """
    E2E tests verifying all three workflow prompt files (bug, change, test)
    through the real load/preprocess/format pipeline.

    These tests catch the bug because the ORIGINAL prompts lacked any mention
    of "unresolved" or resolution-status checking, causing the LLM to
    unconditionally close duplicates.
    """

    PROMPT_CONFIGS = [
        {
            "template_name": "agentic_bug_step1_duplicate_LLM",
            "context": {
                "issue_url": "https://github.com/test/repo/issues/469",
                "issue_content": "Bug description",
                "repo_owner": "test",
                "repo_name": "repo",
                "issue_number": 469,
            },
        },
        {
            "template_name": "agentic_change_step1_duplicate_LLM",
            "context": {
                "issue_url": "https://github.com/test/repo/issues/469",
                "issue_content": "Change request",
                "repo_owner": "test",
                "repo_name": "repo",
                "issue_number": 469,
            },
        },
        {
            "template_name": "agentic_test_step1_duplicate_LLM",
            "context": {
                "issue_url": "https://github.com/test/repo/issues/469",
                "issue_content": "Test generation request",
                "repo_owner": "test",
                "repo_name": "repo",
                "issue_number": 469,
            },
        },
    ]

    @pytest.mark.parametrize(
        "config",
        PROMPT_CONFIGS,
        ids=["bug_prompt", "change_prompt", "test_prompt"],
    )
    def test_prompt_pipeline_contains_resolution_check(self, config):
        """
        E2E: Each prompt, loaded through the real pipeline, must contain
        resolution-status checking instructions.

        Fails on original buggy prompts (no "unresolved" or "resolved" handling).
        Passes on fixed prompts (conditional resolution-based duplicate handling).
        """
        from pdd.load_prompt_template import load_prompt_template

        template = load_prompt_template(config["template_name"])
        assert template is not None, (
            f"Failed to load prompt: {config['template_name']}"
        )

        exclude_keys = list(config["context"].keys())
        processed = preprocess(
            template,
            recursive=True,
            double_curly_brackets=True,
            exclude_keys=exclude_keys,
        )
        formatted = processed.format(**config["context"])

        # Must contain resolution-status checking
        assert "unresolved" in formatted.lower(), (
            f"BUG DETECTED (Issue #469): {config['template_name']} does not "
            f"contain handling for unresolved originals. The original buggy "
            f"prompt unconditionally closed duplicates without checking "
            f"resolution status."
        )

        assert "gh issue view" in formatted, (
            f"BUG DETECTED (Issue #469): {config['template_name']} does not "
            f"instruct the LLM to use 'gh issue view' to verify the original "
            f"issue's state before declaring a duplicate."
        )

    @pytest.mark.parametrize(
        "config",
        PROMPT_CONFIGS,
        ids=["bug_prompt", "change_prompt", "test_prompt"],
    )
    def test_prompt_pipeline_has_conditional_duplicate_handling(self, config):
        """
        E2E: Each prompt must have BOTH resolved and unresolved paths — not
        unconditional closing.

        The original buggy prompt just said:
          "If duplicates are found: Close this issue..."
        The fixed prompt says:
          "If resolved: Close..."
          "If unresolved: Do NOT close..."
        """
        from pdd.load_prompt_template import load_prompt_template

        template = load_prompt_template(config["template_name"])
        assert template is not None

        exclude_keys = list(config["context"].keys())
        processed = preprocess(
            template,
            recursive=True,
            double_curly_brackets=True,
            exclude_keys=exclude_keys,
        )
        formatted = processed.format(**config["context"])

        has_resolved = "resolved" in formatted.lower()
        has_unresolved = "unresolved" in formatted.lower()

        assert has_resolved and has_unresolved, (
            f"BUG DETECTED (Issue #469): {config['template_name']} lacks "
            f"conditional duplicate handling. "
            f"has_resolved={has_resolved}, has_unresolved={has_unresolved}. "
            f"The prompt must have BOTH paths to prevent closing unresolved "
            f"duplicates."
        )
