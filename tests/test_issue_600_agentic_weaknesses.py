"""
Tests for three weaknesses found during pdd_cloud issue #600 assessment:

1. Duplicate check should instruct LLM to reuse prior PR artifacts (#610 partial)
2. Step 9 test generation prompt should block vacuous waitFor negative assertions
3. Step 11 E2E tests should be independently verified by the bug orchestrator

TDD: These tests are written FIRST and should FAIL on the current code.
"""

import pytest
from pathlib import Path
from unittest.mock import patch

from pdd.agentic_bug_orchestrator import run_agentic_bug_orchestrator


# ---------------------------------------------------------------------------
# Helpers
# ---------------------------------------------------------------------------

def _get_prompts_dir() -> Path:
    """Return the prompts directory relative to the project root."""
    return Path(__file__).resolve().parent.parent / "pdd" / "prompts"


def _read_prompt(filename: str) -> str:
    """Read a prompt file and return its content."""
    prompt_path = _get_prompts_dir() / filename
    assert prompt_path.exists(), f"Prompt file not found: {prompt_path}"
    return prompt_path.read_text()


# ===========================================================================
# Issue 1: Duplicate check prompt should instruct reuse of prior PR artifacts
# ===========================================================================

class TestDuplicateCheckPRReuse:
    """
    When Step 1 finds a duplicate that is unresolved, the prompt should
    instruct the LLM to check for and reuse existing PR artifacts (branches,
    test files, draft PRs) from prior attempts rather than redoing all work
    from scratch.
    """

    def test_step1_prompt_instructs_pr_artifact_discovery(self):
        """
        The Step 1 duplicate prompt must instruct the LLM to check for
        existing PRs from unresolved duplicates so work can be reused.
        """
        content = _read_prompt("agentic_bug_step1_duplicate_LLM.prompt")

        has_pr_artifact_check = (
            "gh pr list" in content.lower()
            or "gh pr view" in content.lower()
            or ("pull request" in content.lower() and "artifact" in content.lower())
            or ("existing pr" in content.lower())
            or ("draft pr" in content.lower())
        )
        assert has_pr_artifact_check, (
            "Step 1 duplicate prompt must instruct the LLM to check for "
            "existing PRs from unresolved duplicates so work can be reused "
            "instead of redone from scratch."
        )

    def test_step1_prompt_instructs_branch_discovery(self):
        """
        The prompt must instruct the LLM to look for existing fix branches
        from prior attempts at the unresolved duplicate.
        """
        content = _read_prompt("agentic_bug_step1_duplicate_LLM.prompt")

        has_branch_check = (
            "branch" in content.lower()
            or "git branch" in content.lower()
        )
        assert has_branch_check, (
            "Step 1 duplicate prompt must instruct the LLM to look for "
            "existing branches from prior unresolved attempts."
        )

    def test_step1_prompt_instructs_artifact_reporting(self):
        """
        When proceeding past an unresolved duplicate, the prompt must instruct
        the LLM to report found artifacts so downstream steps can reuse them.
        """
        content = _read_prompt("agentic_bug_step1_duplicate_LLM.prompt")

        has_artifact_reporting = (
            "reuse" in content.lower()
            or "existing artifacts" in content.lower()
            or "prior work" in content.lower()
            or "existing work" in content.lower()
        )
        assert has_artifact_reporting, (
            "Step 1 duplicate prompt must instruct the LLM to report "
            "existing artifacts from unresolved duplicates for reuse."
        )


# ===========================================================================
# Issue 2: Step 9 prompt should block vacuous waitFor negative assertions
# ===========================================================================

class TestStep9VacuousWaitForBlock:
    """
    The Step 9 test generation prompt already blocks structural/shape tests.
    It must also block a subtler anti-pattern: negative assertions inside
    async waitFor/waitForEffect utilities.
    """

    def test_step9_prompt_blocks_negative_waitfor_assertions(self):
        """
        The Step 9 prompt must explicitly warn against using negative
        assertions (.not) inside waitFor, as they are vacuous.
        """
        content = _read_prompt("agentic_bug_step9_generate_LLM.prompt")

        has_waitfor_warning = (
            "waitfor" in content.lower()
            and "not" in content.lower()
            and ("vacuous" in content.lower()
                 or "no-op" in content.lower()
                 or "passes immediately" in content.lower()
                 or "never throws" in content.lower())
        )
        assert has_waitfor_warning, (
            "Step 9 prompt must warn against negative assertions (.not) "
            "inside waitFor — they pass immediately and test nothing."
        )

    def test_step9_prompt_provides_waitfor_alternative(self):
        """
        After warning about the anti-pattern, the prompt should suggest
        the correct alternative.
        """
        content = _read_prompt("agentic_bug_step9_generate_LLM.prompt")

        has_alternative = (
            ("positive assertion" in content.lower()
             or "waitfor.*positive" in content.lower())
            or ("advancetimer" in content.lower()
                or "expect(" in content and "not" in content
                and "instead" in content.lower())
        )
        assert has_alternative, (
            "Step 9 prompt must provide the correct alternative to "
            "vacuous waitFor negative assertions."
        )


# ===========================================================================
# Issue 3: Bug orchestrator Step 11 should verify E2E tests independently
# ===========================================================================

class TestStep11E2EVerification:
    """
    The bug orchestrator's Step 11 handler should run E2E tests
    independently (like Step 10 does for unit tests) to verify they
    actually work, not just check for E2E_FILES_CREATED markers.
    """

    @pytest.fixture
    def bug_mock_deps(self, tmp_path):
        """Mocks for the bug orchestrator focused on Step 11 behavior."""
        mock_worktree_path = tmp_path / ".pdd" / "worktrees" / "fix-issue-1"
        mock_worktree_path.mkdir(parents=True, exist_ok=True)

        with patch("pdd.agentic_bug_orchestrator.run_agentic_task") as mock_run, \
             patch("pdd.agentic_bug_orchestrator.load_prompt_template") as mock_load, \
             patch("pdd.agentic_bug_orchestrator.console") as mock_console, \
             patch("pdd.agentic_bug_orchestrator._setup_worktree") as mock_worktree, \
             patch("pdd.agentic_bug_orchestrator._verify_e2e_tests") as mock_verify_e2e:

            mock_run.return_value = (True, "Step output", 0.1, "gpt-4")
            mock_load.return_value = "Prompt for {issue_number}"
            mock_worktree.return_value = (mock_worktree_path, None)
            # E2E verification returns (passed=False, output) — tests fail on buggy code
            mock_verify_e2e.return_value = (False, "e2e_test.spec.ts: FAILED (bug detected)")

            yield {
                "mock_run": mock_run,
                "mock_load": mock_load,
                "mock_console": mock_console,
                "mock_verify_e2e": mock_verify_e2e,
                "worktree_path": mock_worktree_path,
            }

    @pytest.fixture
    def default_args(self, tmp_path):
        """Default arguments for the bug orchestrator."""
        return {
            "issue_url": "http://github.com/owner/repo/issues/600",
            "issue_content": "WaitlistPending doesn't auto-refresh",
            "repo_owner": "owner",
            "repo_name": "repo",
            "issue_number": 600,
            "issue_author": "user",
            "issue_title": "Waitlist Bug",
            "cwd": tmp_path,
            "verbose": False,
            "quiet": True,
            "use_github_state": False,
        }

    def test_step11_calls_verify_e2e_tests(self, bug_mock_deps, default_args):
        """
        When Step 11 produces E2E_FILES_CREATED, the orchestrator should
        call _verify_e2e_tests to independently run the E2E tests.
        """
        mock_run = bug_mock_deps["mock_run"]
        mock_verify_e2e = bug_mock_deps["mock_verify_e2e"]

        def side_effect(*args, **kwargs):
            label = kwargs.get("label", "")
            if label == "step9":
                return (True, "Generated test\nFILES_CREATED: tests/test_fix.py", 0.1, "gpt-4")
            if label == "step11":
                return (True, "E2E test\nE2E_FILES_CREATED: e2e/test_waitlist.spec.ts", 0.1, "gpt-4")
            return (True, f"Output for {label}", 0.1, "gpt-4")

        mock_run.side_effect = side_effect

        run_agentic_bug_orchestrator(**default_args)

        mock_verify_e2e.assert_called_once()
        call_args = mock_verify_e2e.call_args
        assert "e2e/test_waitlist.spec.ts" in str(call_args)

    def test_step11_e2e_verification_failure_is_logged(
        self, bug_mock_deps, default_args
    ):
        """
        If E2E verification fails, the orchestrator should call
        _verify_e2e_tests (even if it returns failure).
        """
        mock_run = bug_mock_deps["mock_run"]
        mock_verify_e2e = bug_mock_deps["mock_verify_e2e"]

        mock_verify_e2e.return_value = (
            False,
            "e2e_test.spec.ts: FAILED (Cannot find module '@/context/AuthContext')"
        )

        def side_effect(*args, **kwargs):
            label = kwargs.get("label", "")
            if label == "step9":
                return (True, "Generated test\nFILES_CREATED: tests/test_fix.py", 0.1, "gpt-4")
            if label == "step11":
                return (True, "E2E test created\nE2E_FILES_CREATED: e2e/test.spec.ts", 0.1, "gpt-4")
            return (True, f"Output for {label}", 0.1, "gpt-4")

        mock_run.side_effect = side_effect

        run_agentic_bug_orchestrator(**default_args)

        mock_verify_e2e.assert_called_once()

    def test_step11_skips_verification_when_e2e_skip(
        self, bug_mock_deps, default_args
    ):
        """
        When the LLM outputs E2E_SKIP (browsers not installed, etc.),
        the orchestrator should NOT attempt to run E2E verification.
        """
        mock_run = bug_mock_deps["mock_run"]
        mock_verify_e2e = bug_mock_deps["mock_verify_e2e"]

        def side_effect(*args, **kwargs):
            label = kwargs.get("label", "")
            if label == "step9":
                return (True, "Generated test\nFILES_CREATED: tests/test_fix.py", 0.1, "gpt-4")
            if label == "step11":
                return (
                    True,
                    "E2E test\nE2E_FILES_CREATED: e2e/test.spec.ts\n"
                    "E2E_SKIP: Playwright browsers not installed",
                    0.1,
                    "gpt-4",
                )
            return (True, f"Output for {label}", 0.1, "gpt-4")

        mock_run.side_effect = side_effect

        run_agentic_bug_orchestrator(**default_args)

        mock_verify_e2e.assert_not_called()
