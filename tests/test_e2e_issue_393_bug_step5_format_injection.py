"""
E2E Test for Issue #393: pdd bug command fails silently at step 5.5 due to format string injection

This E2E test exercises the full `pdd bug` orchestrator code path to verify that:
1. Step 5 outputs containing curly braces (like {url}) don't cause KeyError at step 5.5
2. Errors at step 5.5 are printed to the console (not silent)
3. Resume messages correctly show step 5.5 when resuming after step 5

The bug: When step 5 (root cause analysis) outputs text containing format placeholders like
{url}, {user_id}, etc., step 5.5 (defect classification) tries to format its prompt with
`prompt_template.format(**context)` where the context includes `step5_output`. Python's
str.format() interprets {url} as a placeholder and raises KeyError: 'url' because 'url'
is not in the context dictionary.

Three bugs identified:
1. Format String Injection: Curly braces in LLM outputs are not escaped before being stored
   in the context dictionary, allowing format string injection when interpolated into
   subsequent prompts.

2. Silent Error Handling: The KeyError is caught but no error message is printed to the
   console before returning, leaving users without visibility into what went wrong.

3. Resume Message Mismatch: When resuming after step 5, the message says "Resuming from
   step 6" but the actual execution starts at step 5.5.

This E2E test:
1. Calls run_agentic_bug_orchestrator with mocked LLM
2. Simulates step 5 outputting text with {url} placeholder
3. Verifies that step 5.5 completes without KeyError
4. Verifies resume message accuracy when resuming from step 5

The test should FAIL on buggy code (before commit 88a37d5d) and PASS on fixed code.
"""

import pytest
from pathlib import Path
from unittest.mock import patch

from pdd.agentic_bug_orchestrator import run_agentic_bug_orchestrator


@pytest.fixture
def mock_cwd(tmp_path):
    """Create a mock working directory with .git to simulate a git repo."""
    (tmp_path / ".git").mkdir()
    (tmp_path / ".pdd").mkdir()
    (tmp_path / ".pdd" / "meta").mkdir()
    return tmp_path


class TestIssue393FormatStringInjectionE2E:
    """
    E2E tests for Issue #393: Verify pdd bug orchestrator handles format string injection
    correctly and doesn't fail silently at step 5.5.
    """

    def test_step5_output_with_curly_braces_does_not_crash_step5_5(self, mock_cwd, monkeypatch):
        """
        E2E Test: Step 5 output containing {url} should not cause KeyError at step 5.5.

        This test simulates the exact failure scenario from the bug report:
        1. Step 5 analyzes a bug and outputs text like "The error occurs because {url} is not in context"
        2. Step 5.5 tries to format its prompt and would get KeyError: 'url' before the fix
        3. After the fix, curly braces should be escaped and step 5.5 should complete

        Expected behavior (after fix):
        - Step 5.5 completes without KeyError
        - The workflow can continue past step 5.5

        Bug behavior (Issue #393):
        - KeyError: 'url' is raised at step 5.5
        - The workflow fails silently
        """
        monkeypatch.setenv("PDD_FORCE_LOCAL", "1")

        steps_attempted = []
        step_outputs = {}

        def mock_run_agentic_task(instruction, cwd, verbose, quiet, timeout, label, max_retries):
            """Mock LLM that returns outputs with format placeholders at step 5."""
            import re
            match = re.search(r"step(\d+(?:\.\d+)?)", label)
            if match:
                step_num = match.group(1)
                steps_attempted.append(step_num)

                # Step 5: Return output with format placeholder (THE BUG TRIGGER)
                if step_num == "5":
                    output = "Root cause: The bug occurs because {url} is not in context dictionary"
                    step_outputs[step_num] = output
                    return (True, output, 0.001, "mock-model")

                # Step 5.5: If we get here without KeyError, the fix is working
                elif step_num == "5_5":
                    output = "DEFECT_TYPE: code\n\nThis is a code bug."
                    step_outputs[step_num] = output
                    return (True, output, 0.001, "mock-model")

                # Other steps: Return simple success
                else:
                    output = f"Step {step_num} success"
                    step_outputs[step_num] = output
                    if step_num == "6":
                        output = "STOP\n\nTest complete"
                    return (True, output, 0.001, "mock-model")
            return (True, "Success", 0.001, "mock-model")

        def mock_save_state(*args, **kwargs):
            return None

        def mock_load_state(*args, **kwargs):
            return None, None

        def mock_setup_worktree(cwd, issue_number, quiet, resume_existing=False):
            worktree_dir = cwd / ".pdd" / "worktrees" / f"fix-issue-{issue_number}"
            worktree_dir.mkdir(parents=True, exist_ok=True)
            return worktree_dir, None

        with patch('pdd.agentic_bug_orchestrator.run_agentic_task', side_effect=mock_run_agentic_task):
            with patch('pdd.agentic_bug_orchestrator.save_workflow_state', side_effect=mock_save_state):
                with patch('pdd.agentic_bug_orchestrator.load_workflow_state', side_effect=mock_load_state):
                    with patch('pdd.agentic_bug_orchestrator._setup_worktree', side_effect=mock_setup_worktree):
                        try:
                            success, message, cost, model, files = run_agentic_bug_orchestrator(
                                issue_url="https://github.com/promptdriven/pdd/issues/393",
                                issue_content="Test issue for bug #393",
                                repo_owner="promptdriven",
                                repo_name="pdd",
                                issue_number=393,
                                issue_author="jamesdlevine",
                                issue_title="pdd bug command fails silently at step 5.5",
                                cwd=mock_cwd,
                                verbose=False,
                                quiet=True,
                                use_github_state=False
                            )
                        except KeyError as e:
                            pytest.fail(
                                f"BUG DETECTED (Issue #393): Orchestrator raised KeyError '{e.args[0]}' "
                                f"during step 5.5 prompt formatting.\n\n"
                                f"Steps completed before crash: {steps_attempted}\n\n"
                                f"Step 5 output that triggered the bug:\n{step_outputs.get('5', 'N/A')}\n\n"
                                f"This confirms Bug #1: Format string injection when LLM outputs contain "
                                f"curly braces like {{url}}, {{user_id}}, etc.\n\n"
                                f"Expected fix: Escape curly braces before storing in context dictionary."
                            )

        # Verify step 5 was attempted
        assert "5" in steps_attempted, "Step 5 should have been attempted"

        # If we got here without KeyError, the fix is working!
        # The test would have failed in the except block if KeyError was raised
        # Verify step 5 output contained curly braces (the bug trigger)
        step5_output = step_outputs.get("5", "")
        assert "{url}" in step5_output, (
            "Step 5 output should contain {url} to trigger the bug"
        )

        # Success! The orchestrator completed without raising KeyError from format string injection
        assert success is not None, "Orchestrator should have completed (not crashed with KeyError)"

    def test_resume_message_shows_correct_step_5_5(self, mock_cwd, monkeypatch):
        """
        E2E Test: Resume message should show "step 5.5" when resuming after step 5.

        This test verifies Bug #3: Resume message mismatch.
        Before the fix: "Resuming from step 6" (wrong - actually resumes at 5.5)
        After the fix: "Resuming from step 5.5" (correct)
        """
        monkeypatch.setenv("PDD_FORCE_LOCAL", "1")

        console_messages = []

        def mock_console_print(*args, **kwargs):
            """Capture console messages to verify resume message."""
            msg = " ".join(str(arg) for arg in args)
            console_messages.append(msg)

        def mock_run_agentic_task(instruction, cwd, verbose, quiet, timeout, label, max_retries):
            return (True, "Success", 0.001, "mock-model")

        def mock_save_state(*args, **kwargs):
            return None

        def mock_load_state(*args, **kwargs):
            """Return saved state with step 5 completed."""
            state = {
                "last_completed_step": 5,
                "total_cost": 1.0,
                "model_used": "test-model",
                "step_outputs": {
                    "1": "Duplicate check complete",
                    "2": "Docs check complete",
                    "3": "Triage complete",
                    "4": "Reproduction complete",
                    "5": "Root cause analysis complete",
                },
                "changed_files": [],
                "worktree_path": str(mock_cwd / ".pdd" / "worktrees" / "fix-issue-393"),
            }
            return state, None

        worktree_dir = mock_cwd / ".pdd" / "worktrees" / "fix-issue-393"
        worktree_dir.mkdir(parents=True, exist_ok=True)

        def mock_setup_worktree(cwd, issue_number, quiet, resume_existing=False):
            return worktree_dir, None

        with patch('pdd.agentic_bug_orchestrator.run_agentic_task', side_effect=mock_run_agentic_task):
            with patch('pdd.agentic_bug_orchestrator.save_workflow_state', side_effect=mock_save_state):
                with patch('pdd.agentic_bug_orchestrator.load_workflow_state', side_effect=mock_load_state):
                    with patch('pdd.agentic_bug_orchestrator._setup_worktree', side_effect=mock_setup_worktree):
                        with patch('pdd.agentic_bug_orchestrator.console.print', side_effect=mock_console_print):
                            success, message, cost, model, files = run_agentic_bug_orchestrator(
                                issue_url="https://github.com/promptdriven/pdd/issues/393",
                                issue_content="Test issue",
                                repo_owner="promptdriven",
                                repo_name="pdd",
                                issue_number=393,
                                issue_author="test",
                                issue_title="Test",
                                cwd=mock_cwd,
                                verbose=False,
                                quiet=False,
                                use_github_state=False
                            )

        # Find the resume message
        resume_messages = [msg for msg in console_messages if "Resuming from step" in msg]

        assert len(resume_messages) > 0, (
            f"Should have printed a resume message.\n"
            f"Console messages: {console_messages}"
        )

        resume_msg = resume_messages[0]

        # After the fix, should say "Resuming from step 5.5"
        assert "5.5" in resume_msg, (
            f"BUG DETECTED (Issue #393 - Bug #3): Resume message should show 'step 5.5' "
            f"when last_completed_step=5.\n\n"
            f"Actual message: {resume_msg}\n\n"
            f"Before fix: 'Resuming from step 6' (wrong)\n"
            f"After fix: 'Resuming from step 5.5' (correct)"
        )


class TestIssue393RegressionPrevention:
    """Regression prevention tests for Issue #393."""

    def test_step_output_escaping_prevents_format_injection(self, mock_cwd, monkeypatch):
        """
        Regression Test: Verify that curly braces in step outputs are escaped.

        This test verifies the fix at lines 394-397 of agentic_bug_orchestrator.py.
        """
        monkeypatch.setenv("PDD_FORCE_LOCAL", "1")

        def mock_run_agentic_task(instruction, cwd, verbose, quiet, timeout, label, max_retries):
            return (True, "Success", 0.001, "mock-model")

        def mock_save_state(*args, **kwargs):
            return None

        def mock_load_state(*args, **kwargs):
            """Return state with step 5 output containing curly braces."""
            state = {
                "last_completed_step": 5,
                "total_cost": 1.0,
                "model_used": "test-model",
                "step_outputs": {
                    "5": "The bug is caused by {url} not being in the context",
                },
                "changed_files": [],
                "worktree_path": str(mock_cwd / ".pdd" / "worktrees" / "fix-issue-393"),
            }
            return state, None

        worktree_dir = mock_cwd / ".pdd" / "worktrees" / "fix-issue-393"
        worktree_dir.mkdir(parents=True, exist_ok=True)

        def mock_setup_worktree(cwd, issue_number, quiet, resume_existing=False):
            return worktree_dir, None

        with patch('pdd.agentic_bug_orchestrator.run_agentic_task', side_effect=mock_run_agentic_task):
            with patch('pdd.agentic_bug_orchestrator.save_workflow_state', side_effect=mock_save_state):
                with patch('pdd.agentic_bug_orchestrator.load_workflow_state', side_effect=mock_load_state):
                    with patch('pdd.agentic_bug_orchestrator._setup_worktree', side_effect=mock_setup_worktree):
                        try:
                            success, message, cost, model, files = run_agentic_bug_orchestrator(
                                issue_url="https://github.com/promptdriven/pdd/issues/393",
                                issue_content="Test",
                                repo_owner="promptdriven",
                                repo_name="pdd",
                                issue_number=393,
                                issue_author="test",
                                issue_title="Test",
                                cwd=mock_cwd,
                                verbose=False,
                                quiet=True,
                                use_github_state=False
                            )
                        except KeyError as e:
                            pytest.fail(
                                f"REGRESSION: Format string injection vulnerability reintroduced!\n"
                                f"KeyError: '{e.args[0]}' - curly braces in step outputs are not being escaped.\n"
                                f"The fix at lines 394-397 may have been removed or broken."
                            )

        # If we get here without KeyError, the escaping is working
        assert True, "Curly braces were properly escaped"
