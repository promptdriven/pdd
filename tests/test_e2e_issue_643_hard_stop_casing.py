"""
E2E Test for Issue #643: pdd change doesn't wait for response after posting
clarification/architecture questions.

Bug: The orchestrator's _check_hard_stop checks for "Clarification Needed" and
"Architectural Decision Needed" (title case), but the prompts instruct the LLM
to output "STOP_CONDITION: Clarification needed" / "STOP_CONDITION: Architectural
decision needed" (lowercase). The casing mismatch means the workflow continues
past steps 4 and 7 instead of halting.

These E2E tests exercise the REAL orchestrator loop (run_agentic_change_orchestrator)
with real prompt loading, real _check_hard_stop, and real step sequencing. Only the
LLM execution layer (run_agentic_task) and state persistence are mocked — the bug
detection logic runs unmodified.

This differs from the unit tests in test_issue_643_hard_stop_casing.py which test
_check_hard_stop in isolation.
"""

import re
import pytest
from pathlib import Path
from unittest.mock import patch, MagicMock


@pytest.fixture
def mock_cwd(tmp_path):
    """Create a minimal working directory that looks like a git repo."""
    (tmp_path / ".git").mkdir()
    (tmp_path / ".pdd").mkdir()
    return tmp_path


@pytest.mark.e2e
class TestIssue643Step4HardStopE2E:
    """E2E: Orchestrator must halt at Step 4 when LLM outputs prompt-format stop."""

    def test_step4_halts_on_prompt_instructed_stop_condition(self, mock_cwd):
        """
        E2E Test: When the LLM outputs "STOP_CONDITION: Clarification needed"
        (the format the step 4 prompt instructs), the orchestrator should stop
        after step 4 and NOT continue to step 5+.

        Bug behavior: _check_hard_stop returns None because it checks for
        "Clarification Needed" (title case N) but the prompt instructs
        "Clarification needed" (lowercase n). The workflow continues.

        Fixed behavior: _check_hard_stop detects the stop condition regardless
        of casing and halts the workflow.
        """
        from pdd.agentic_change_orchestrator import run_agentic_change_orchestrator

        steps_executed = []

        def mock_run_agentic_task(instruction, cwd, verbose, quiet, timeout, label, max_retries):
            match = re.search(r"step(\d+)", label)
            if match:
                steps_executed.append(int(match.group(1)))

            if "step4" in label:
                # Exact output format the prompt instructs the LLM to produce
                return (
                    True,
                    "## Clarification Questions\n\n"
                    "I've posted the following questions to the GitHub issue:\n"
                    "1. What is the expected behavior when X happens?\n"
                    "2. Should Y be supported?\n\n"
                    "STOP_CONDITION: Clarification needed",
                    0.001,
                    "mock-model",
                )
            if "step9" in label:
                return (True, "FILES_MODIFIED: file.py", 0.001, "mock-model")
            return (True, f"Mock output for {label}", 0.001, "mock-model")

        with patch("pdd.agentic_change_orchestrator.run_agentic_task", side_effect=mock_run_agentic_task), \
             patch("pdd.agentic_change_orchestrator.save_workflow_state", return_value=None), \
             patch("pdd.agentic_change_orchestrator.load_workflow_state", return_value=(None, None)), \
             patch("pdd.agentic_change_orchestrator.clear_workflow_state"), \
             patch("pdd.agentic_change_orchestrator.post_step_comment"):

            success, message, cost, model, files = run_agentic_change_orchestrator(
                issue_url="https://github.com/test/repo/issues/643",
                issue_content="Test issue requiring clarification",
                repo_owner="test",
                repo_name="repo",
                issue_number=643,
                issue_author="test-user",
                issue_title="Test Issue 643",
                cwd=mock_cwd,
                verbose=False,
                quiet=True,
                use_github_state=False,
            )

        # The orchestrator should stop at or before step 4
        max_step = max(steps_executed) if steps_executed else 0
        assert max_step <= 4, (
            f"BUG #643 (E2E): Orchestrator continued past Step 4 to step {max_step}. "
            f"Steps executed: {steps_executed}. "
            f"_check_hard_stop failed to detect 'STOP_CONDITION: Clarification needed' "
            f"because it only checks for 'Clarification Needed' (title case)."
        )

        # Verify the workflow reported stopping (not success)
        assert not success or "stop" in message.lower() or "clarification" in message.lower(), (
            f"Orchestrator should report stopping for clarification. Got: {message}"
        )

    def test_step4_halts_on_lowercase_clarification_needed(self, mock_cwd):
        """
        E2E Test: When LLM outputs just "Clarification needed" (lowercase n,
        no STOP_CONDITION prefix), the orchestrator should still halt.
        """
        from pdd.agentic_change_orchestrator import run_agentic_change_orchestrator

        steps_executed = []

        def mock_run_agentic_task(instruction, cwd, verbose, quiet, timeout, label, max_retries):
            match = re.search(r"step(\d+)", label)
            if match:
                steps_executed.append(int(match.group(1)))

            if "step4" in label:
                return (
                    True,
                    "Clarification needed — posted questions to the issue.",
                    0.001,
                    "mock-model",
                )
            if "step9" in label:
                return (True, "FILES_MODIFIED: file.py", 0.001, "mock-model")
            return (True, f"Mock output for {label}", 0.001, "mock-model")

        with patch("pdd.agentic_change_orchestrator.run_agentic_task", side_effect=mock_run_agentic_task), \
             patch("pdd.agentic_change_orchestrator.save_workflow_state", return_value=None), \
             patch("pdd.agentic_change_orchestrator.load_workflow_state", return_value=(None, None)), \
             patch("pdd.agentic_change_orchestrator.clear_workflow_state"), \
             patch("pdd.agentic_change_orchestrator.post_step_comment"):

            success, message, cost, model, files = run_agentic_change_orchestrator(
                issue_url="https://github.com/test/repo/issues/643",
                issue_content="Test issue requiring clarification",
                repo_owner="test",
                repo_name="repo",
                issue_number=643,
                issue_author="test-user",
                issue_title="Test Issue 643",
                cwd=mock_cwd,
                verbose=False,
                quiet=True,
                use_github_state=False,
            )

        max_step = max(steps_executed) if steps_executed else 0
        assert max_step <= 4, (
            f"BUG #643 (E2E): Orchestrator continued past Step 4 to step {max_step}. "
            f"Steps executed: {steps_executed}. "
            f"_check_hard_stop failed to detect 'Clarification needed' (lowercase 'n')."
        )


@pytest.mark.e2e
class TestIssue643Step7HardStopE2E:
    """E2E: Orchestrator must halt at Step 7 when LLM outputs prompt-format stop."""

    def test_step7_halts_on_prompt_instructed_stop_condition(self, mock_cwd):
        """
        E2E Test: When the LLM outputs "STOP_CONDITION: Architectural decision needed"
        (the format the step 7 prompt instructs), the orchestrator should stop
        after step 7 and NOT continue to step 8+.

        Bug behavior: _check_hard_stop returns None because it checks for
        "Architectural Decision Needed" (title case D/N) but the prompt instructs
        "Architectural decision needed" (lowercase d/n). The workflow continues.
        """
        from pdd.agentic_change_orchestrator import run_agentic_change_orchestrator

        steps_executed = []

        def mock_run_agentic_task(instruction, cwd, verbose, quiet, timeout, label, max_retries):
            match = re.search(r"step(\d+)", label)
            if match:
                steps_executed.append(int(match.group(1)))

            if "step7" in label:
                return (
                    True,
                    "## Architectural Questions\n\n"
                    "Posted the following to the GitHub issue:\n"
                    "- Should we use pattern A or pattern B?\n"
                    "- Is the database schema change acceptable?\n\n"
                    "Workflow paused - awaiting architectural decisions\n\n"
                    "STOP_CONDITION: Architectural decision needed",
                    0.001,
                    "mock-model",
                )
            if "step9" in label:
                return (True, "FILES_MODIFIED: file.py", 0.001, "mock-model")
            return (True, f"Mock output for {label}", 0.001, "mock-model")

        with patch("pdd.agentic_change_orchestrator.run_agentic_task", side_effect=mock_run_agentic_task), \
             patch("pdd.agentic_change_orchestrator.save_workflow_state", return_value=None), \
             patch("pdd.agentic_change_orchestrator.load_workflow_state", return_value=(None, None)), \
             patch("pdd.agentic_change_orchestrator.clear_workflow_state"), \
             patch("pdd.agentic_change_orchestrator.post_step_comment"):

            success, message, cost, model, files = run_agentic_change_orchestrator(
                issue_url="https://github.com/test/repo/issues/643",
                issue_content="Test issue requiring architectural review",
                repo_owner="test",
                repo_name="repo",
                issue_number=643,
                issue_author="test-user",
                issue_title="Test Issue 643",
                cwd=mock_cwd,
                verbose=False,
                quiet=True,
                use_github_state=False,
            )

        max_step = max(steps_executed) if steps_executed else 0
        assert max_step <= 7, (
            f"BUG #643 (E2E): Orchestrator continued past Step 7 to step {max_step}. "
            f"Steps executed: {steps_executed}. "
            f"_check_hard_stop failed to detect 'STOP_CONDITION: Architectural decision needed' "
            f"because it only checks for 'Architectural Decision Needed' (title case)."
        )

        assert not success or "stop" in message.lower() or "architectural" in message.lower(), (
            f"Orchestrator should report stopping for architectural decision. Got: {message}"
        )

    def test_step7_halts_on_lowercase_architectural_decision_needed(self, mock_cwd):
        """
        E2E Test: When LLM outputs just "Architectural decision needed" (lowercase),
        the orchestrator should still halt.
        """
        from pdd.agentic_change_orchestrator import run_agentic_change_orchestrator

        steps_executed = []

        def mock_run_agentic_task(instruction, cwd, verbose, quiet, timeout, label, max_retries):
            match = re.search(r"step(\d+)", label)
            if match:
                steps_executed.append(int(match.group(1)))

            if "step7" in label:
                return (
                    True,
                    "Architectural decision needed — awaiting input on database schema.",
                    0.001,
                    "mock-model",
                )
            if "step9" in label:
                return (True, "FILES_MODIFIED: file.py", 0.001, "mock-model")
            return (True, f"Mock output for {label}", 0.001, "mock-model")

        with patch("pdd.agentic_change_orchestrator.run_agentic_task", side_effect=mock_run_agentic_task), \
             patch("pdd.agentic_change_orchestrator.save_workflow_state", return_value=None), \
             patch("pdd.agentic_change_orchestrator.load_workflow_state", return_value=(None, None)), \
             patch("pdd.agentic_change_orchestrator.clear_workflow_state"), \
             patch("pdd.agentic_change_orchestrator.post_step_comment"):

            success, message, cost, model, files = run_agentic_change_orchestrator(
                issue_url="https://github.com/test/repo/issues/643",
                issue_content="Test issue requiring architectural review",
                repo_owner="test",
                repo_name="repo",
                issue_number=643,
                issue_author="test-user",
                issue_title="Test Issue 643",
                cwd=mock_cwd,
                verbose=False,
                quiet=True,
                use_github_state=False,
            )

        max_step = max(steps_executed) if steps_executed else 0
        assert max_step <= 7, (
            f"BUG #643 (E2E): Orchestrator continued past Step 7 to step {max_step}. "
            f"Steps executed: {steps_executed}. "
            f"_check_hard_stop failed to detect 'Architectural decision needed' (lowercase)."
        )


@pytest.mark.e2e
class TestIssue643RegressionE2E:
    """E2E regression tests: title-case stop conditions must still work."""

    def test_step4_still_halts_on_title_case(self, mock_cwd):
        """Regression: "Clarification Needed" (original title case) must still halt."""
        from pdd.agentic_change_orchestrator import run_agentic_change_orchestrator

        steps_executed = []

        def mock_run_agentic_task(instruction, cwd, verbose, quiet, timeout, label, max_retries):
            match = re.search(r"step(\d+)", label)
            if match:
                steps_executed.append(int(match.group(1)))

            if "step4" in label:
                return (True, "Clarification Needed — ambiguous requirements.", 0.001, "mock-model")
            if "step9" in label:
                return (True, "FILES_MODIFIED: file.py", 0.001, "mock-model")
            return (True, f"Mock output for {label}", 0.001, "mock-model")

        with patch("pdd.agentic_change_orchestrator.run_agentic_task", side_effect=mock_run_agentic_task), \
             patch("pdd.agentic_change_orchestrator.save_workflow_state", return_value=None), \
             patch("pdd.agentic_change_orchestrator.load_workflow_state", return_value=(None, None)), \
             patch("pdd.agentic_change_orchestrator.clear_workflow_state"), \
             patch("pdd.agentic_change_orchestrator.post_step_comment"):

            success, message, cost, model, files = run_agentic_change_orchestrator(
                issue_url="https://github.com/test/repo/issues/643",
                issue_content="Test issue",
                repo_owner="test",
                repo_name="repo",
                issue_number=643,
                issue_author="test-user",
                issue_title="Test Issue 643",
                cwd=mock_cwd,
                verbose=False,
                quiet=True,
                use_github_state=False,
            )

        max_step = max(steps_executed) if steps_executed else 0
        assert max_step <= 4, (
            f"Regression: Orchestrator should still halt on title-case 'Clarification Needed'. "
            f"Steps executed: {steps_executed}"
        )

    def test_step7_still_halts_on_title_case(self, mock_cwd):
        """Regression: "Architectural Decision Needed" (original title case) must still halt."""
        from pdd.agentic_change_orchestrator import run_agentic_change_orchestrator

        steps_executed = []

        def mock_run_agentic_task(instruction, cwd, verbose, quiet, timeout, label, max_retries):
            match = re.search(r"step(\d+)", label)
            if match:
                steps_executed.append(int(match.group(1)))

            if "step7" in label:
                return (True, "Architectural Decision Needed — awaiting input.", 0.001, "mock-model")
            if "step9" in label:
                return (True, "FILES_MODIFIED: file.py", 0.001, "mock-model")
            return (True, f"Mock output for {label}", 0.001, "mock-model")

        with patch("pdd.agentic_change_orchestrator.run_agentic_task", side_effect=mock_run_agentic_task), \
             patch("pdd.agentic_change_orchestrator.save_workflow_state", return_value=None), \
             patch("pdd.agentic_change_orchestrator.load_workflow_state", return_value=(None, None)), \
             patch("pdd.agentic_change_orchestrator.clear_workflow_state"), \
             patch("pdd.agentic_change_orchestrator.post_step_comment"):

            success, message, cost, model, files = run_agentic_change_orchestrator(
                issue_url="https://github.com/test/repo/issues/643",
                issue_content="Test issue",
                repo_owner="test",
                repo_name="repo",
                issue_number=643,
                issue_author="test-user",
                issue_title="Test Issue 643",
                cwd=mock_cwd,
                verbose=False,
                quiet=True,
                use_github_state=False,
            )

        max_step = max(steps_executed) if steps_executed else 0
        assert max_step <= 7, (
            f"Regression: Orchestrator should still halt on title-case 'Architectural Decision Needed'. "
            f"Steps executed: {steps_executed}"
        )
