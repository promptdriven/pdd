"""
E2E Test for Issue #737: Step completion markers in orchestrators.

Unlike the unit tests in test_issue_737_step_completion_markers.py which mock
console.print() and inspect call_args, these E2E tests capture REAL Rich Console
output (rendered text) and verify the executor regex matches — simulating exactly
what the GitHub App executor does when scanning orchestrator output.

The executor's credential waterfall uses this regex to detect successful steps:
    (?:→|->)\s*Step\s+(\S+)\s+complete

If no markers match, the executor treats $0 cost + no markers as an auth failure.
"""
from __future__ import annotations

import io
import re

import pytest
from pathlib import Path
from unittest.mock import patch, MagicMock

from rich.console import Console

# The exact regex the executor uses to detect step completion
EXECUTOR_REGEX = re.compile(r"(?:→|->)\s*Step\s+(\S+)\s+complete")


def _make_capturing_console() -> tuple[Console, io.StringIO]:
    """Create a real Rich Console that writes to a capturable StringIO."""
    buf = io.StringIO()
    return Console(file=buf, force_terminal=False, no_color=True, width=200), buf


def _extract_completed_steps(output: str) -> list[str]:
    """Extract step numbers from captured console output using the executor regex."""
    return EXECUTOR_REGEX.findall(output)


# ---------------------------------------------------------------------------
# Change Orchestrator E2E
# ---------------------------------------------------------------------------

@pytest.mark.e2e
class TestChangeOrchestratorE2E:
    """E2E: Verify change orchestrator output contains step markers the executor can parse."""

    def test_executor_can_detect_step_markers_in_real_output(self, tmp_path):
        """
        Run change orchestrator with real Rich Console output and verify
        the executor regex finds step completion markers in the rendered text.
        """
        from pdd.agentic_change_orchestrator import run_agentic_change_orchestrator

        console, buf = _make_capturing_console()

        with patch("pdd.agentic_change_orchestrator.run_agentic_task") as mock_run, \
             patch("pdd.agentic_change_orchestrator.load_prompt_template") as mock_tpl, \
             patch("pdd.agentic_change_orchestrator.load_workflow_state") as mock_load, \
             patch("pdd.agentic_change_orchestrator.save_workflow_state"), \
             patch("pdd.agentic_change_orchestrator.clear_workflow_state"), \
             patch("pdd.agentic_change_orchestrator.subprocess.run") as mock_sub, \
             patch("pdd.agentic_change_orchestrator.post_step_comment") as mock_post, \
             patch("pdd.agentic_change_orchestrator.console", console), \
             patch("pdd.agentic_change_orchestrator.preprocess", side_effect=lambda p, **kw: p):

            mock_tpl.return_value = "Mocked Prompt"
            mock_load.return_value = (None, None)
            mock_sub.return_value = MagicMock(stdout=str(tmp_path), returncode=0)
            mock_post.return_value = True

            def side_effect(**kwargs):
                label = kwargs.get("label", "")
                if label == "step9":
                    return (True, "FILES_MODIFIED: a.py", 0.1, "gpt-4")
                if label == "step10":
                    return (True, "FILES_MODIFIED: b.py", 0.1, "gpt-4")
                if label.startswith("step11"):
                    return (True, "No Issues Found", 0.1, "gpt-4")
                if label == "step13":
                    return (True, "PR Created: https://github.com/o/r/pull/1", 0.1, "gpt-4")
                return (True, f"Output for {label}", 0.1, "gpt-4")

            mock_run.side_effect = side_effect

            run_agentic_change_orchestrator(
                issue_url="http://url",
                issue_content="Fix bug",
                repo_owner="owner",
                repo_name="repo",
                issue_number=1,
                issue_author="me",
                issue_title="Bug fix",
                cwd=tmp_path,
                verbose=True,
                quiet=False,
                use_github_state=False,
            )

        output = buf.getvalue()
        steps_found = _extract_completed_steps(output)

        # The executor must find at least steps 1-8 in the rendered output
        for step in ["1", "2", "3", "4", "5", "6", "7", "8"]:
            assert step in steps_found, (
                f"Executor regex cannot find 'Step {step} complete.' in real console output.\n"
                f"Steps found: {steps_found}\n"
                f"Full output:\n{output}"
            )


# ---------------------------------------------------------------------------
# Architecture Orchestrator E2E
# ---------------------------------------------------------------------------

@pytest.mark.e2e
class TestArchitectureOrchestratorE2E:
    """E2E: Verify architecture orchestrator output contains step markers."""

    def test_executor_can_detect_step_markers_in_real_output(self, tmp_path):
        """
        Run architecture orchestrator with real Rich Console and verify
        step completion markers appear in the rendered text.
        """
        from pdd.agentic_architecture_orchestrator import run_agentic_architecture_orchestrator

        console, buf = _make_capturing_console()

        with patch("pdd.agentic_architecture_orchestrator.run_agentic_task") as mock_run, \
             patch("pdd.agentic_architecture_orchestrator.load_workflow_state") as mock_load, \
             patch("pdd.agentic_architecture_orchestrator.save_workflow_state"), \
             patch("pdd.agentic_architecture_orchestrator.clear_workflow_state"), \
             patch("pdd.agentic_architecture_orchestrator.load_prompt_template") as mock_tpl, \
             patch("pdd.agentic_architecture_orchestrator.generate_mermaid_code") as mock_merm, \
             patch("pdd.agentic_architecture_orchestrator.generate_html") as mock_html, \
             patch("pdd.agentic_architecture_orchestrator.HAS_MERMAID", True), \
             patch("pdd.agentic_architecture_orchestrator.console", console):

            mock_load.return_value = (None, None)
            mock_tpl.return_value = "Prompt for {issue_title}"
            mock_run.return_value = (True, "Step Output\nVALIDATION_RESULT: VALID", 0.1, "gpt-4")
            mock_merm.return_value = "graph TD; A-->B;"
            mock_html.return_value = "<html>...</html>"

            run_agentic_architecture_orchestrator(
                issue_url="http://url",
                issue_content="Build an app",
                repo_owner="owner",
                repo_name="repo",
                issue_number=1,
                issue_author="me",
                issue_title="Feature",
                cwd=tmp_path,
                verbose=False,
                quiet=False,
                use_github_state=False,
                force_single=True,
            )

        output = buf.getvalue()
        steps_found = _extract_completed_steps(output)

        # The executor must find at least steps 1-5 in the rendered output
        for step in ["1", "2", "3", "4", "5"]:
            assert step in steps_found, (
                f"Executor regex cannot find 'Step {step} complete.' in real console output.\n"
                f"Steps found: {steps_found}\n"
                f"Full output:\n{output}"
            )


# ---------------------------------------------------------------------------
# Test Orchestrator E2E
# ---------------------------------------------------------------------------

@pytest.mark.e2e
class TestTestOrchestratorE2E:
    """E2E: Verify test orchestrator output contains step markers."""

    def test_executor_can_detect_step_markers_in_real_output(self, tmp_path):
        """
        Run test orchestrator with real Rich Console and verify
        step completion markers appear in the rendered text.
        """
        from pdd.agentic_test_orchestrator import run_agentic_test_orchestrator

        console, buf = _make_capturing_console()

        with patch("pdd.agentic_test_orchestrator.run_agentic_task") as mock_run, \
             patch("pdd.agentic_test_orchestrator.load_workflow_state") as mock_load, \
             patch("pdd.agentic_test_orchestrator.save_workflow_state"), \
             patch("pdd.agentic_test_orchestrator.clear_workflow_state"), \
             patch("pdd.agentic_test_orchestrator.load_prompt_template") as mock_tpl, \
             patch("pdd.agentic_test_orchestrator._setup_worktree") as mock_wt, \
             patch("pdd.agentic_test_orchestrator.shutil") as mock_shutil, \
             patch("pdd.agentic_test_orchestrator._get_console", return_value=console), \
             patch("subprocess.run") as mock_sub:

            mock_load.return_value = (None, None)
            mock_tpl.return_value = "Mock prompt: {issue_content}"
            mock_wt.return_value = (Path("/tmp/worktree"), None)
            mock_shutil.which.return_value = None
            mock_sub.return_value = MagicMock(stdout="main\n", returncode=0)

            def side_effect(instruction, cwd, *, verbose=False, quiet=False, label="",
                            timeout=None, max_retries=1, retry_delay=5.0, deadline=None,
                            use_playwright=False):
                if label == "step4":
                    return (True, "TEST_TYPE: api\nTEST_FRAMEWORK: pytest", 0.1, "anthropic")
                if label == "step12":
                    return (True, "FILES_CREATED: tests/test_api.py\nGenerated.", 0.1, "anthropic")
                if label == "step17":
                    return (True, "PR Created: https://github.com/o/r/pull/10", 0.1, "anthropic")
                return (True, f"Output for {label}", 0.1, "anthropic")

            mock_run.side_effect = side_effect

            run_agentic_test_orchestrator(
                issue_url="http://url",
                issue_content="Add tests",
                repo_owner="owner",
                repo_name="repo",
                issue_number=1,
                issue_author="me",
                issue_title="Add tests",
                cwd=tmp_path,
                quiet=False,
                use_github_state=False,
            )

        output = buf.getvalue()
        steps_found = _extract_completed_steps(output)

        # The executor must find at least steps 1-5 in the rendered output
        for step in ["1", "2", "3", "4", "5"]:
            assert step in steps_found, (
                f"Executor regex cannot find 'Step {step} complete.' in real console output.\n"
                f"Steps found: {steps_found}\n"
                f"Full output:\n{output}"
            )


# ---------------------------------------------------------------------------
# Bug Orchestrator E2E (regression — should pass on current code)
# ---------------------------------------------------------------------------

@pytest.mark.e2e
class TestBugOrchestratorE2E:
    """E2E regression: bug orchestrator already emits markers — verify with real console."""

    def test_executor_can_detect_step_markers_in_real_output(self, tmp_path):
        """
        Run bug orchestrator with real Rich Console and verify the executor
        regex matches step markers in the rendered text.
        """
        from pdd.agentic_bug_orchestrator import run_agentic_bug_orchestrator

        console, buf = _make_capturing_console()
        mock_worktree_path = tmp_path / ".pdd" / "worktrees" / "fix-issue-1"
        mock_worktree_path.mkdir(parents=True, exist_ok=True)

        with patch("pdd.agentic_bug_orchestrator.run_agentic_task") as mock_run, \
             patch("pdd.agentic_bug_orchestrator.load_prompt_template") as mock_tpl, \
             patch("pdd.agentic_bug_orchestrator.console", console), \
             patch("pdd.agentic_bug_orchestrator._setup_worktree") as mock_wt:

            mock_tpl.return_value = "Prompt for {issue_number}"
            mock_wt.return_value = (mock_worktree_path, None)

            def side_effect(*args, **kwargs):
                label = kwargs.get("label", "")
                if label == "step7":
                    return (True, "Generated test\nFILES_CREATED: test_file.py", 0.1, "gpt-4")
                return (True, f"Output for {label}", 0.1, "gpt-4")

            mock_run.side_effect = side_effect

            run_agentic_bug_orchestrator(
                issue_url="http://url",
                issue_content="Bug description",
                repo_owner="owner",
                repo_name="repo",
                issue_number=1,
                issue_author="user",
                issue_title="Bug",
                cwd=tmp_path,
                verbose=False,
                quiet=False,
            )

        output = buf.getvalue()
        steps_found = _extract_completed_steps(output)

        # Bug orchestrator should have markers for at least steps 1-4
        for step in ["1", "2", "3", "4"]:
            assert step in steps_found, (
                f"Regression: bug orchestrator missing 'Step {step} complete.' in output.\n"
                f"Steps found: {steps_found}\n"
                f"Full output:\n{output}"
            )


# ---------------------------------------------------------------------------
# Cross-orchestrator: executor simulation
# ---------------------------------------------------------------------------

@pytest.mark.e2e
class TestExecutorCredentialWaterfallE2E:
    """
    E2E: Simulate the executor's credential waterfall logic.

    The executor checks: if total_cost == 0 AND no step markers found,
    it treats the run as an auth failure. This test verifies that all
    orchestrators produce output that the executor can distinguish
    from auth failures.
    """

    def test_change_orchestrator_not_misidentified_as_auth_failure(self, tmp_path):
        """
        Simulate executor logic: run change orchestrator, then apply the
        same regex the executor uses. If no markers found, the executor
        would incorrectly flag this as an auth failure.
        """
        from pdd.agentic_change_orchestrator import run_agentic_change_orchestrator

        console, buf = _make_capturing_console()

        with patch("pdd.agentic_change_orchestrator.run_agentic_task") as mock_run, \
             patch("pdd.agentic_change_orchestrator.load_prompt_template") as mock_tpl, \
             patch("pdd.agentic_change_orchestrator.load_workflow_state") as mock_load, \
             patch("pdd.agentic_change_orchestrator.save_workflow_state"), \
             patch("pdd.agentic_change_orchestrator.clear_workflow_state"), \
             patch("pdd.agentic_change_orchestrator.subprocess.run") as mock_sub, \
             patch("pdd.agentic_change_orchestrator.post_step_comment") as mock_post, \
             patch("pdd.agentic_change_orchestrator.console", console), \
             patch("pdd.agentic_change_orchestrator.preprocess", side_effect=lambda p, **kw: p):

            mock_tpl.return_value = "Mocked Prompt"
            mock_load.return_value = (None, None)
            mock_sub.return_value = MagicMock(stdout=str(tmp_path), returncode=0)
            mock_post.return_value = True

            def side_effect(**kwargs):
                label = kwargs.get("label", "")
                if label == "step9":
                    return (True, "FILES_MODIFIED: a.py", 0.1, "gpt-4")
                if label == "step10":
                    return (True, "FILES_MODIFIED: b.py", 0.1, "gpt-4")
                if label.startswith("step11"):
                    return (True, "No Issues Found", 0.1, "gpt-4")
                if label == "step13":
                    return (True, "PR Created: https://github.com/o/r/pull/1", 0.1, "gpt-4")
                return (True, f"Output for {label}", 0.1, "gpt-4")

            mock_run.side_effect = side_effect

            run_agentic_change_orchestrator(
                issue_url="http://url",
                issue_content="Fix bug",
                repo_owner="owner",
                repo_name="repo",
                issue_number=1,
                issue_author="me",
                issue_title="Bug fix",
                cwd=tmp_path,
                verbose=True,
                quiet=False,
                use_github_state=False,
            )

        output = buf.getvalue()
        steps_found = _extract_completed_steps(output)

        # Executor logic: if no step markers found AND cost ~0, assume auth failure
        assert len(steps_found) > 0, (
            "EXECUTOR WOULD MISIDENTIFY AS AUTH FAILURE!\n"
            "The change orchestrator produced zero step completion markers.\n"
            "The executor regex `(?:→|->)\\s*Step\\s+(\\S+)\\s+complete` found no matches.\n"
            "This is the exact bug described in issue #737 / pdd_cloud#568.\n"
            f"Full output:\n{output}"
        )
