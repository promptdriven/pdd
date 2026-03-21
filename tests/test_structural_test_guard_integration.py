"""
Integration tests for structural test guard in the bug orchestrator.

Tests that:
1. After step 9 generates test files, the orchestrator scans them for structural patterns
2. If violations are found, step 9 is re-run with feedback (up to 1 retry)
3. If the retry also produces structural tests, the orchestrator proceeds with a warning
4. The Step 10 prompt includes the BLOCKED directive for structural tests
"""

import textwrap
from pathlib import Path
from unittest.mock import MagicMock, patch

import pytest

from pdd.agentic_bug_orchestrator import run_agentic_bug_orchestrator


# --- Fixtures ---


@pytest.fixture
def mock_dependencies(tmp_path):
    """Mocks external dependencies for orchestrator tests."""
    mock_worktree_path = tmp_path / ".pdd" / "worktrees" / "fix-issue-1"
    mock_worktree_path.mkdir(parents=True, exist_ok=True)

    with patch("pdd.agentic_bug_orchestrator.run_agentic_task") as mock_run, \
         patch("pdd.agentic_bug_orchestrator.load_prompt_template") as mock_load, \
         patch("pdd.agentic_bug_orchestrator.console") as mock_console, \
         patch("pdd.agentic_bug_orchestrator._setup_worktree") as mock_worktree, \
         patch("pdd.agentic_bug_orchestrator.preprocess", side_effect=lambda t, **kw: t) as mock_preprocess, \
         patch("pdd.agentic_bug_orchestrator.save_workflow_state", return_value=None) as mock_save, \
         patch("pdd.agentic_bug_orchestrator.load_workflow_state", return_value=(None, None)) as mock_load_state, \
         patch("pdd.agentic_bug_orchestrator._get_git_root", return_value=tmp_path) as mock_git_root, \
         patch("pdd.agentic_bug_orchestrator.set_agentic_progress") as mock_set_progress, \
         patch("pdd.agentic_bug_orchestrator.clear_agentic_progress") as mock_clear_progress:

        mock_run.return_value = (True, "Step output", 0.1, "gpt-4")
        mock_load.return_value = "Prompt for {issue_number}"
        mock_worktree.return_value = (mock_worktree_path, None)

        yield {
            "mock_run": mock_run,
            "mock_load": mock_load,
            "mock_console": mock_console,
            "worktree_path": mock_worktree_path,
        }


@pytest.fixture
def default_args(tmp_path):
    return {
        "issue_url": "http://github.com/owner/repo/issues/1",
        "issue_content": "Bug description",
        "repo_owner": "owner",
        "repo_name": "repo",
        "issue_number": 1,
        "issue_author": "user",
        "issue_title": "Bug Title",
        "cwd": tmp_path,
        "verbose": False,
        "quiet": True,
    }


# --- Option A: Orchestrator re-runs step 9 on structural test detection ---


class TestOrchestratorStructuralTestRetry:
    """After step 9, orchestrator should detect structural tests and retry."""

    def test_step9_structural_test_triggers_retry(
        self, mock_dependencies, default_args, tmp_path
    ):
        """When step 9 produces a structural test file, step 9 should be re-run."""
        deps = mock_dependencies
        mock_run = deps["mock_run"]
        worktree = deps["worktree_path"]

        # Write a structural test file that step 9 "creates"
        structural_test = worktree / "tests" / "test_structural.py"
        structural_test.parent.mkdir(parents=True, exist_ok=True)
        structural_test.write_text(textwrap.dedent("""\
            import inspect
            from src import module
            def test_has_feature():
                source = inspect.getsource(module)
                assert "feature" in source
        """))

        step9_call_count = 0

        def side_effect(*args, **kwargs):
            nonlocal step9_call_count
            label = kwargs.get("label", "")
            if label == "step9":
                step9_call_count += 1
                return (True, f"FILES_CREATED: tests/test_structural.py", 0.1, "gpt-4")
            return (True, "Step output", 0.1, "gpt-4")

        mock_run.side_effect = side_effect

        run_agentic_bug_orchestrator(**default_args)

        # Step 9 should have been called more than once (original + retry)
        assert step9_call_count >= 2, (
            f"Step 9 was only called {step9_call_count} time(s). "
            "Expected retry after structural test detection."
        )

    def test_step9_retry_prompt_includes_violation_feedback(
        self, mock_dependencies, default_args, tmp_path
    ):
        """The retry prompt should include what structural patterns were found."""
        deps = mock_dependencies
        mock_run = deps["mock_run"]
        worktree = deps["worktree_path"]

        structural_test = worktree / "tests" / "test_structural.py"
        structural_test.parent.mkdir(parents=True, exist_ok=True)
        structural_test.write_text(textwrap.dedent("""\
            import inspect
            from src import module
            def test_check():
                source = inspect.getsource(module)
                assert "keyword" in source
        """))

        retry_instructions = []

        def side_effect(*args, **kwargs):
            label = kwargs.get("label", "")
            if label == "step9":
                instruction = kwargs.get("instruction", "")
                retry_instructions.append(instruction)
                return (True, "FILES_CREATED: tests/test_structural.py", 0.1, "gpt-4")
            return (True, "Step output", 0.1, "gpt-4")

        mock_run.side_effect = side_effect

        run_agentic_bug_orchestrator(**default_args)

        # Step 9 should be retried when structural tests are detected
        assert len(retry_instructions) >= 2, (
            f"Step 9 should be retried when structural tests are detected. "
            f"Got {len(retry_instructions)} call(s)."
        )
        assert "structural" in retry_instructions[1].lower() or \
               "inspect.getsource" in retry_instructions[1], \
            "Retry prompt should include feedback about the structural pattern found"

    def test_step9_clean_test_no_retry(
        self, mock_dependencies, default_args, tmp_path
    ):
        """When step 9 produces a behavioral test, no retry should occur."""
        deps = mock_dependencies
        mock_run = deps["mock_run"]
        worktree = deps["worktree_path"]

        # Write a clean behavioral test
        behavioral_test = worktree / "tests" / "test_behavioral.py"
        behavioral_test.parent.mkdir(parents=True, exist_ok=True)
        behavioral_test.write_text(textwrap.dedent("""\
            from src.services.executor_job_service import _get_resource_overrides

            def test_opus_gets_32gi():
                result = _get_resource_overrides(label="bug", model_override="claude-oauth")
                assert result["memory"] == "32Gi"
        """))

        step9_count = 0

        def side_effect(*args, **kwargs):
            nonlocal step9_count
            label = kwargs.get("label", "")
            if label == "step9":
                step9_count += 1
                return (True, "FILES_CREATED: tests/test_behavioral.py", 0.1, "gpt-4")
            return (True, "Step output", 0.1, "gpt-4")

        mock_run.side_effect = side_effect

        run_agentic_bug_orchestrator(**default_args)

        assert step9_count == 1, (
            f"Step 9 was called {step9_count} times. "
            "Behavioral test should not trigger a retry."
        )


# --- Option B: Step 10 prompt includes BLOCKED directive ---


class TestStep10PromptBlockedDirective:
    """The Step 10 verification prompt should check for structural test patterns."""

    def test_step10_prompt_has_structural_test_blocked(self):
        """Step 10 prompt must contain BLOCKED directive for structural tests."""
        prompt_path = (
            Path(__file__).parent.parent
            / "pdd"
            / "prompts"
            / "agentic_bug_step10_verify_LLM.prompt"
        )
        assert prompt_path.exists(), f"Step 10 prompt not found: {prompt_path}"
        content = prompt_path.read_text()

        assert "BLOCKED" in content, (
            "Step 10 prompt must contain a BLOCKED directive for structural test patterns. "
            "Currently it only checks whether the test runs and fails, not whether it uses "
            "behavioral assertions."
        )

    def test_step10_prompt_mentions_inspect_getsource(self):
        """Step 10 prompt should specifically call out inspect.getsource as banned."""
        prompt_path = (
            Path(__file__).parent.parent
            / "pdd"
            / "prompts"
            / "agentic_bug_step10_verify_LLM.prompt"
        )
        content = prompt_path.read_text()

        assert "inspect.getsource" in content or "getsource" in content, (
            "Step 10 prompt should explicitly mention inspect.getsource as a banned pattern. "
            "This is the exact pattern that slipped through on issue #591."
        )

    def test_step10_prompt_mentions_source_string_matching(self):
        """Step 10 prompt should call out 'assert keyword in source' pattern."""
        prompt_path = (
            Path(__file__).parent.parent
            / "pdd"
            / "prompts"
            / "agentic_bug_step10_verify_LLM.prompt"
        )
        content = prompt_path.read_text()

        # Should mention source string matching or source scanning
        has_source_matching = (
            "source string matching" in content.lower()
            or "source scanning" in content.lower()
            or "source code scanning" in content.lower()
            or "string matching" in content.lower()
        )
        assert has_source_matching, (
            "Step 10 prompt should mention source string matching as a banned pattern."
        )
