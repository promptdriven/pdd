r"""Tests for issue #737: Step completion markers in orchestrators.

Verifies that all orchestrators emit '→ Step {step_num} complete.' markers
after each successful step when quiet=False. The executor's credential
waterfall regex `(?:→|->)\s*Step\s+(\S+)\s+complete` depends on these markers
to distinguish successful runs from auth failures.

Currently, bug/checkup/e2e_fix orchestrators emit these markers, but
change/architecture/test orchestrators do not — causing false auth-failure
detection.
"""
from __future__ import annotations

import re
import pytest
from unittest.mock import patch, MagicMock
from pathlib import Path

from pdd.agentic_change_orchestrator import run_agentic_change_orchestrator
from pdd.agentic_architecture_orchestrator import run_agentic_architecture_orchestrator
from pdd.agentic_test_orchestrator import run_agentic_test_orchestrator
from pdd.agentic_bug_orchestrator import run_agentic_bug_orchestrator

# The executor regex that must match step completion markers
EXECUTOR_REGEX = re.compile(r"(?:→|->)\s*Step\s+(\S+)\s+complete")


# ---------------------------------------------------------------------------
# Helpers
# ---------------------------------------------------------------------------

def _get_console_print_texts(mock_console):
    """Extract all text strings passed to console.print()."""
    texts = []
    for call in mock_console.print.call_args_list:
        args, _ = call
        if args:
            texts.append(str(args[0]))
    return texts


def _assert_step_markers(texts, expected_steps):
    """Assert that step completion markers exist for all expected step numbers."""
    markers = []
    for text in texts:
        m = EXECUTOR_REGEX.search(text)
        if m:
            markers.append(m.group(1))
    for step in expected_steps:
        assert str(step) in markers, (
            f"Missing '→ Step {step} complete.' marker. "
            f"Found markers for steps: {markers}. "
            f"All console output: {texts}"
        )


# ---------------------------------------------------------------------------
# Fixtures
# ---------------------------------------------------------------------------

@pytest.fixture
def change_mocks(tmp_path):
    """Mocks for the change orchestrator with quiet=False."""
    with patch("pdd.agentic_change_orchestrator.run_agentic_task") as mock_run, \
         patch("pdd.agentic_change_orchestrator.load_prompt_template") as mock_tpl, \
         patch("pdd.agentic_change_orchestrator.load_workflow_state") as mock_load, \
         patch("pdd.agentic_change_orchestrator.save_workflow_state") as mock_save, \
         patch("pdd.agentic_change_orchestrator.clear_workflow_state") as mock_clear, \
         patch("pdd.agentic_change_orchestrator.subprocess.run") as mock_sub, \
         patch("pdd.agentic_change_orchestrator.post_step_comment") as mock_post, \
         patch("pdd.agentic_change_orchestrator.console") as mock_console, \
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
        yield mock_console, tmp_path


@pytest.fixture
def arch_mocks(tmp_path):
    """Mocks for the architecture orchestrator with quiet=False."""
    with patch("pdd.agentic_architecture_orchestrator.run_agentic_task") as mock_run, \
         patch("pdd.agentic_architecture_orchestrator.load_workflow_state") as mock_load, \
         patch("pdd.agentic_architecture_orchestrator.save_workflow_state") as mock_save, \
         patch("pdd.agentic_architecture_orchestrator.clear_workflow_state") as mock_clear, \
         patch("pdd.agentic_architecture_orchestrator.load_prompt_template") as mock_tpl, \
         patch("pdd.agentic_architecture_orchestrator.generate_mermaid_code") as mock_merm, \
         patch("pdd.agentic_architecture_orchestrator.generate_html") as mock_html, \
         patch("pdd.agentic_architecture_orchestrator.HAS_MERMAID", True), \
         patch("pdd.agentic_architecture_orchestrator.console") as mock_console:

        mock_load.return_value = (None, None)
        mock_tpl.return_value = "Prompt for {issue_title}"
        # Include VALIDATION_RESULT: VALID so step 5b passes
        mock_run.return_value = (True, "Step Output\nVALIDATION_RESULT: VALID", 0.1, "gpt-4")
        mock_merm.return_value = "graph TD; A-->B;"
        mock_html.return_value = "<html>...</html>"

        yield mock_console, tmp_path


@pytest.fixture
def test_mocks(tmp_path):
    """Mocks for the test orchestrator with quiet=False."""
    mock_console = MagicMock()
    with patch("pdd.agentic_test_orchestrator.run_agentic_task") as mock_run, \
         patch("pdd.agentic_test_orchestrator.load_workflow_state") as mock_load, \
         patch("pdd.agentic_test_orchestrator.save_workflow_state") as mock_save, \
         patch("pdd.agentic_test_orchestrator.clear_workflow_state") as mock_clear, \
         patch("pdd.agentic_test_orchestrator.load_prompt_template") as mock_tpl, \
         patch("pdd.agentic_test_orchestrator._setup_worktree") as mock_wt, \
         patch("pdd.agentic_test_orchestrator.shutil") as mock_shutil, \
         patch("pdd.agentic_test_orchestrator._get_console", return_value=mock_console), \
         patch("subprocess.run") as mock_sub:

        mock_load.return_value = (None, None)
        mock_save.return_value = None
        mock_tpl.return_value = "Mock prompt: {issue_content}"
        mock_wt.return_value = (Path("/tmp/worktree"), None)
        mock_shutil.which.return_value = None  # No playwright
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
        yield mock_console, tmp_path


@pytest.fixture
def bug_mocks(tmp_path):
    """Mocks for the bug orchestrator (reference — should already work)."""
    mock_worktree_path = tmp_path / ".pdd" / "worktrees" / "fix-issue-1"
    mock_worktree_path.mkdir(parents=True, exist_ok=True)

    with patch("pdd.agentic_bug_orchestrator.run_agentic_task") as mock_run, \
         patch("pdd.agentic_bug_orchestrator.load_prompt_template") as mock_tpl, \
         patch("pdd.agentic_bug_orchestrator.console") as mock_console, \
         patch("pdd.agentic_bug_orchestrator._setup_worktree") as mock_wt:

        mock_tpl.return_value = "Prompt for {issue_number}"
        mock_wt.return_value = (mock_worktree_path, None)

        def side_effect(*args, **kwargs):
            label = kwargs.get("label", "")
            if label == "step7":
                return (True, "Generated test\nFILES_CREATED: test_file.py", 0.1, "gpt-4")
            return (True, f"Output for {label}", 0.1, "gpt-4")

        mock_run.side_effect = side_effect
        yield mock_console, tmp_path


# ---------------------------------------------------------------------------
# Tests
# ---------------------------------------------------------------------------

class TestChangeOrchestratorStepMarkers:
    """Verify change orchestrator emits step completion markers."""

    def test_emits_step_markers_when_not_quiet(self, change_mocks):
        """Change orchestrator must print '→ Step N complete.' for each successful step."""
        mock_console, cwd = change_mocks

        run_agentic_change_orchestrator(
            issue_url="http://url",
            issue_content="Fix bug",
            repo_owner="owner",
            repo_name="repo",
            issue_number=1,
            issue_author="me",
            issue_title="Bug fix",
            cwd=cwd,
            verbose=True,
            quiet=False,
            use_github_state=False,
        )

        texts = _get_console_print_texts(mock_console)
        # Steps 1-10 are the main loop; verify at least steps 1-8 have markers
        _assert_step_markers(texts, [1, 2, 3, 4, 5, 6, 7, 8])


class TestArchitectureOrchestratorStepMarkers:
    """Verify architecture orchestrator emits step completion markers."""

    def test_emits_step_markers_when_not_quiet(self, arch_mocks):
        """Architecture orchestrator must print '→ Step N complete.' for each successful step."""
        mock_console, cwd = arch_mocks

        run_agentic_architecture_orchestrator(
            issue_url="http://url",
            issue_content="Build an app",
            repo_owner="owner",
            repo_name="repo",
            issue_number=1,
            issue_author="me",
            issue_title="Feature",
            cwd=cwd,
            verbose=False,
            quiet=False,
            use_github_state=False,
            force_single=True,  # Skip complexity sub-issues
        )

        texts = _get_console_print_texts(mock_console)
        # Verify at least steps 1-5 have markers (main loop steps)
        _assert_step_markers(texts, [1, 2, 3, 4, 5])


class TestTestOrchestratorStepMarkers:
    """Verify test orchestrator emits step completion markers."""

    def test_emits_step_markers_when_not_quiet(self, test_mocks):
        """Test orchestrator must print '→ Step N complete.' for each successful step."""
        mock_console, cwd = test_mocks

        run_agentic_test_orchestrator(
            issue_url="http://url",
            issue_content="Add tests",
            repo_owner="owner",
            repo_name="repo",
            issue_number=1,
            issue_author="me",
            issue_title="Add tests",
            cwd=cwd,
            quiet=False,
            use_github_state=False,
        )

        texts = _get_console_print_texts(mock_console)
        # Verify at least steps 1-5 have markers (pre-manual-testing steps)
        _assert_step_markers(texts, [1, 2, 3, 4, 5])


class TestBugOrchestratorStepMarkers:
    """Regression: verify bug orchestrator continues to emit markers."""

    def test_emits_step_markers_when_not_quiet(self, bug_mocks):
        """Bug orchestrator already prints '→ Step N complete.' — regression check."""
        mock_console, cwd = bug_mocks

        run_agentic_bug_orchestrator(
            issue_url="http://url",
            issue_content="Bug description",
            repo_owner="owner",
            repo_name="repo",
            issue_number=1,
            issue_author="user",
            issue_title="Bug",
            cwd=cwd,
            verbose=False,
            quiet=False,
        )

        texts = _get_console_print_texts(mock_console)
        # Bug orchestrator has 11 steps (incl 5.5); check a few key ones
        _assert_step_markers(texts, [1, 2, 3, 4])


class TestStepMarkersSuppressedWhenQuiet:
    """Markers should NOT be emitted when quiet=True."""

    def test_change_quiet_no_markers(self, change_mocks):
        """Change orchestrator should not print step markers when quiet=True."""
        mock_console, cwd = change_mocks

        run_agentic_change_orchestrator(
            issue_url="http://url",
            issue_content="Fix bug",
            repo_owner="owner",
            repo_name="repo",
            issue_number=1,
            issue_author="me",
            issue_title="Bug fix",
            cwd=cwd,
            quiet=True,
            use_github_state=False,
        )

        texts = _get_console_print_texts(mock_console)
        for text in texts:
            assert not EXECUTOR_REGEX.search(text), (
                f"Found step marker in quiet mode: {text}"
            )


class TestStepMarkerNotEmittedOnFailure:
    """Step markers should only appear for successful steps."""

    def test_change_no_marker_on_failed_step(self, tmp_path):
        """If a step fails, '→ Step N complete.' should NOT be printed for it."""
        with patch("pdd.agentic_change_orchestrator.run_agentic_task") as mock_run, \
             patch("pdd.agentic_change_orchestrator.load_prompt_template") as mock_tpl, \
             patch("pdd.agentic_change_orchestrator.load_workflow_state") as mock_load, \
             patch("pdd.agentic_change_orchestrator.save_workflow_state") as mock_save, \
             patch("pdd.agentic_change_orchestrator.clear_workflow_state"), \
             patch("pdd.agentic_change_orchestrator.subprocess.run") as mock_sub, \
             patch("pdd.agentic_change_orchestrator.post_step_comment") as mock_post, \
             patch("pdd.agentic_change_orchestrator.console") as mock_console, \
             patch("pdd.agentic_change_orchestrator.preprocess", side_effect=lambda p, **kw: p):

            mock_tpl.return_value = "Mocked Prompt"
            mock_load.return_value = (None, None)
            mock_sub.return_value = MagicMock(stdout=str(tmp_path), returncode=0)
            mock_post.return_value = True

            def side_effect(**kwargs):
                label = kwargs.get("label", "")
                if label == "step3":
                    # Step 3 fails
                    return (False, "Error in step 3", 0.1, "gpt-4")
                if label == "step9":
                    return (True, "FILES_MODIFIED: a.py", 0.1, "gpt-4")
                if label == "step10":
                    return (True, "FILES_MODIFIED: b.py", 0.1, "gpt-4")
                if label.startswith("step11"):
                    return (True, "No Issues Found", 0.1, "gpt-4")
                if label == "step13":
                    return (True, "PR: https://github.com/o/r/pull/1", 0.1, "gpt-4")
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
                quiet=False,
                use_github_state=False,
            )

            texts = _get_console_print_texts(mock_console)
            step3_markers = [
                t for t in texts
                if EXECUTOR_REGEX.search(t) and EXECUTOR_REGEX.search(t).group(1) == "3"
            ]
            assert len(step3_markers) == 0, (
                f"Found step completion marker for failed step 3: {step3_markers}"
            )


class TestMarkerFormatMatchesExecutorRegex:
    """Verify the exact marker string format matches the executor regex."""

    def test_marker_format(self):
        """The marker string '  → Step N complete.' must match the executor regex."""
        for step in [1, 2, 5, "5.5", 10, 13]:
            marker = f"  → Step {step} complete."
            assert EXECUTOR_REGEX.search(marker), (
                f"Marker '{marker}' does not match executor regex"
            )
