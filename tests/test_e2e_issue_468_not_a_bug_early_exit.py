"""
E2E Test for Issue #468: PDD fix didn't pause even though the agent reported no bug to fix.

Bug: When Step 3 returns NOT_A_BUG, the orchestrator should stop the workflow
immediately. Instead, it continues executing Steps 4-9 because there is no
early exit check after Step 3.

The root cause has two parts:
1. The Step 3 prompt now includes NOT_A_BUG as a category (fixed in step 5.5),
   so the agent CAN classify issues as not-a-bug.
2. The orchestrator (agentic_e2e_fix_orchestrator.py:504-522) does NOT check
   for NOT_A_BUG after Step 3, so it continues through all 9 steps.

This E2E test exercises the REAL orchestrator code path:
- Real prompt template loading (load_prompt_template is NOT mocked)
- Real prompt formatting with context variables
- Real orchestrator loop logic with early exit checks
- Only LLM execution (run_agentic_task) and state/git ops are mocked

This differs from the unit tests in test_agentic_e2e_fix_orchestrator.py which
mock load_prompt_template and test the orchestrator in isolation.

The test should FAIL on the current buggy code (orchestrator runs all 9 steps)
and PASS once the NOT_A_BUG early exit check is added.
"""

import re
import pytest
from pathlib import Path
from unittest.mock import patch


@pytest.fixture
def mock_cwd(tmp_path):
    """Create a mock working directory with .git to simulate a git repo."""
    (tmp_path / ".git").mkdir()
    (tmp_path / ".pdd").mkdir()
    return tmp_path


class TestIssue468NotABugEarlyExitE2E:
    """
    E2E tests for Issue #468: NOT_A_BUG should cause early exit after Step 3.

    These tests exercise the full orchestrator code path with real prompt
    loading and formatting, only mocking the LLM execution layer.
    """

    def test_not_a_bug_stops_after_step3(self, mock_cwd):
        """
        E2E Test: When Step 3 returns NOT_A_BUG, the orchestrator should stop.

        This test:
        1. Calls run_agentic_e2e_fix_orchestrator with real prompt loading
        2. Mock LLM returns NOT_A_BUG for Step 3
        3. Verifies the orchestrator stops after Step 3 (3 calls total)

        Bug behavior: The orchestrator runs all 9 steps (or 45 with 5 cycles)
        because it has no check for NOT_A_BUG after Step 3.

        Fixed behavior: The orchestrator detects NOT_A_BUG in Step 3 output
        and exits immediately, like the bug orchestrator does for
        "Feature Request (Not a Bug)" at Step 2.
        """
        from pdd.agentic_e2e_fix_orchestrator import run_agentic_e2e_fix_orchestrator

        steps_executed = []

        def mock_run_agentic_task(instruction, cwd, verbose, quiet, timeout, label, max_retries):
            """Mock LLM execution that returns NOT_A_BUG for Step 3."""
            match = re.search(r"step(\d+)", label)
            if match:
                step_num = int(match.group(1))
                steps_executed.append(step_num)

            if "step3" in label:
                return (
                    True,
                    "## Root Cause Analysis\n\n"
                    "**Status:** NOT_A_BUG\n\n"
                    "After thorough investigation, the reported behavior is "
                    "expected and documented. This is not a bug.\n\n"
                    "### Recommendation\n"
                    "Close the issue as not-a-bug.",
                    0.001,
                    "mock-model",
                )
            if "step9" in label:
                return (True, "CONTINUE_CYCLE", 0.001, "mock-model")
            return (True, f"Mock output for {label}", 0.001, "mock-model")

        with patch("pdd.agentic_e2e_fix_orchestrator.run_agentic_task", side_effect=mock_run_agentic_task), \
             patch("pdd.agentic_e2e_fix_orchestrator.save_workflow_state", return_value=None), \
             patch("pdd.agentic_e2e_fix_orchestrator.load_workflow_state", return_value=(None, None)), \
             patch("pdd.agentic_e2e_fix_orchestrator.clear_workflow_state"), \
             patch("pdd.agentic_e2e_fix_orchestrator._get_file_hashes", return_value={}), \
             patch("pdd.agentic_e2e_fix_orchestrator._commit_and_push", return_value=(True, "No changes")):

            success, message, cost, model, files = run_agentic_e2e_fix_orchestrator(
                issue_url="https://github.com/test/repo/issues/468",
                issue_content="Test issue: behavior is expected, not a bug",
                repo_owner="test",
                repo_name="repo",
                issue_number=468,
                issue_author="test-user",
                issue_title="Not a bug issue",
                cwd=mock_cwd,
                max_cycles=1,
                resume=False,
                verbose=False,
                quiet=True,
                use_github_state=False,
                protect_tests=False,
            )

        # The orchestrator should stop after Step 3, executing only Steps 1-3
        assert steps_executed == [1, 2, 3], (
            f"BUG DETECTED (Issue #468): Expected orchestrator to stop after Step 3 "
            f"when NOT_A_BUG is returned, but it executed steps: {steps_executed}.\n\n"
            f"The orchestrator should check for NOT_A_BUG in Step 3 output and "
            f"exit immediately, similar to how the bug orchestrator checks for "
            f"'Feature Request (Not a Bug)' at Step 2.\n\n"
            f"Missing code: An early exit check after Step 3 in "
            f"agentic_e2e_fix_orchestrator.py:504-522."
        )

    def test_not_a_bug_embedded_in_verbose_output(self, mock_cwd):
        """
        E2E Test: NOT_A_BUG detection works even with verbose surrounding text.

        The LLM may embed the NOT_A_BUG token in a verbose response with
        markdown, explanations, and recommendations. The orchestrator should
        still detect the token via substring match (like ALL_TESTS_PASS).
        """
        from pdd.agentic_e2e_fix_orchestrator import run_agentic_e2e_fix_orchestrator

        steps_executed = []

        def mock_run_agentic_task(instruction, cwd, verbose, quiet, timeout, label, max_retries):
            """Mock LLM with verbose NOT_A_BUG response for Step 3."""
            match = re.search(r"step(\d+)", label)
            if match:
                steps_executed.append(int(match.group(1)))

            if "step3" in label:
                return (
                    True,
                    "## Step 3: Root Cause Analysis (Cycle 1)\n\n"
                    "### Failure Analysis\n\n"
                    "#### Test: `test_expected_behavior`\n"
                    "- **Expected behavior (per docs):** The API returns 404 for deleted resources\n"
                    "- **Test expects:** A 404 response\n"
                    "- **Code does:** Returns 404 correctly\n\n"
                    "### Root Cause\n"
                    "The test is actually passing. The user misread the error output.\n\n"
                    "**Status:** NOT_A_BUG\n\n"
                    "### Recommendation\n"
                    "Close the issue. The behavior is correct and documented in the API spec.\n\n"
                    "---\n"
                    "*Step 3 complete.*",
                    0.001,
                    "mock-model",
                )
            if "step9" in label:
                return (True, "CONTINUE_CYCLE", 0.001, "mock-model")
            return (True, f"Mock output for {label}", 0.001, "mock-model")

        with patch("pdd.agentic_e2e_fix_orchestrator.run_agentic_task", side_effect=mock_run_agentic_task), \
             patch("pdd.agentic_e2e_fix_orchestrator.save_workflow_state", return_value=None), \
             patch("pdd.agentic_e2e_fix_orchestrator.load_workflow_state", return_value=(None, None)), \
             patch("pdd.agentic_e2e_fix_orchestrator.clear_workflow_state"), \
             patch("pdd.agentic_e2e_fix_orchestrator._get_file_hashes", return_value={}), \
             patch("pdd.agentic_e2e_fix_orchestrator._commit_and_push", return_value=(True, "No changes")):

            success, message, cost, model, files = run_agentic_e2e_fix_orchestrator(
                issue_url="https://github.com/test/repo/issues/468",
                issue_content="User error: misread error output",
                repo_owner="test",
                repo_name="repo",
                issue_number=468,
                issue_author="test-user",
                issue_title="Verbose not-a-bug issue",
                cwd=mock_cwd,
                max_cycles=1,
                resume=False,
                verbose=False,
                quiet=True,
                use_github_state=False,
                protect_tests=False,
            )

        assert steps_executed == [1, 2, 3], (
            f"BUG DETECTED (Issue #468): NOT_A_BUG token not detected in verbose output. "
            f"Expected steps [1, 2, 3] but got {steps_executed}.\n\n"
            f"The orchestrator should detect NOT_A_BUG via substring match "
            f"even when embedded in verbose markdown output."
        )

    def test_normal_code_bug_continues_past_step3(self, mock_cwd):
        """
        Regression Test: CODE_BUG in Step 3 should NOT trigger early exit.

        This ensures the NOT_A_BUG fix doesn't accidentally stop the workflow
        for legitimate bug classifications like CODE_BUG, TEST_BUG, BOTH.
        """
        from pdd.agentic_e2e_fix_orchestrator import run_agentic_e2e_fix_orchestrator

        steps_executed = []

        def mock_run_agentic_task(instruction, cwd, verbose, quiet, timeout, label, max_retries):
            """Mock LLM with CODE_BUG response for Step 3."""
            match = re.search(r"step(\d+)", label)
            if match:
                steps_executed.append(int(match.group(1)))

            if "step3" in label:
                return (
                    True,
                    "**Status:** CODE_BUG\n\n"
                    "The code has a bug in the validation logic.",
                    0.001,
                    "mock-model",
                )
            if "step9" in label:
                return (True, "ALL_TESTS_PASS", 0.001, "mock-model")
            return (True, f"Mock output for {label}", 0.001, "mock-model")

        with patch("pdd.agentic_e2e_fix_orchestrator.run_agentic_task", side_effect=mock_run_agentic_task), \
             patch("pdd.agentic_e2e_fix_orchestrator.save_workflow_state", return_value=None), \
             patch("pdd.agentic_e2e_fix_orchestrator.load_workflow_state", return_value=(None, None)), \
             patch("pdd.agentic_e2e_fix_orchestrator.clear_workflow_state"), \
             patch("pdd.agentic_e2e_fix_orchestrator._get_file_hashes", return_value={}), \
             patch("pdd.agentic_e2e_fix_orchestrator._commit_and_push", return_value=(True, "No changes")):

            success, message, cost, model, files = run_agentic_e2e_fix_orchestrator(
                issue_url="https://github.com/test/repo/issues/468",
                issue_content="Real bug in validation logic",
                repo_owner="test",
                repo_name="repo",
                issue_number=468,
                issue_author="test-user",
                issue_title="Real bug issue",
                cwd=mock_cwd,
                max_cycles=1,
                resume=False,
                verbose=False,
                quiet=True,
                use_github_state=False,
                protect_tests=False,
            )

        # CODE_BUG should continue past Step 3 through all 9 steps
        assert steps_executed == [1, 2, 3, 4, 5, 6, 7, 8, 9], (
            f"Regression: CODE_BUG should continue through all steps. "
            f"Got {steps_executed}. The NOT_A_BUG fix may be too aggressive."
        )
        assert success is True, f"Should succeed when ALL_TESTS_PASS at Step 9: {message}"

    def test_step3_prompt_template_includes_not_a_bug_and_formats(self, mock_cwd):
        """
        E2E Test: Step 3 prompt template loads, contains NOT_A_BUG, and formats correctly.

        This verifies the full prompt loading + formatting pipeline works
        with the NOT_A_BUG category present. Unlike the unit test which
        checks raw template content, this exercises the real preprocess
        and format pipeline.
        """
        from pdd.preprocess import preprocess

        prompt_path = Path(__file__).parent.parent / "prompts" / "agentic_e2e_fix_step3_root_cause_LLM.prompt"
        template = prompt_path.read_text()

        # Verify NOT_A_BUG exists in the raw template
        assert "NOT_A_BUG" in template, (
            "Step 3 prompt must include NOT_A_BUG as a root cause category. "
            "Without it, the agent cannot classify issues as not-a-bug."
        )

        # Format the template with real context (same as orchestrator does)
        context = {
            "issue_url": "https://github.com/test/repo/issues/468",
            "repo_owner": "test",
            "repo_name": "repo",
            "issue_number": 468,
            "cycle_number": 1,
            "max_cycles": 5,
            "issue_content": "Test issue content",
            "protect_tests": "false",
            "protect_tests_flag": "",
            "step1_output": "Step 1 output",
            "step2_output": "Step 2 output",
        }

        exclude_keys = list(context.keys())
        processed = preprocess(template, recursive=True, double_curly_brackets=True, exclude_keys=exclude_keys)

        try:
            formatted = processed.format(**context)
        except KeyError as e:
            pytest.fail(
                f"Step 3 template formatting failed with KeyError: {e}. "
                f"This may indicate improper escaping in the template."
            )

        # NOT_A_BUG should appear in the formatted output as a category option
        assert "NOT_A_BUG" in formatted, (
            "NOT_A_BUG should be present in the formatted Step 3 prompt. "
            "The agent needs to see this as an available classification option."
        )
