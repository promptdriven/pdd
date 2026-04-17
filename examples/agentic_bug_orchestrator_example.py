"""Example showing how to use run_agentic_bug_orchestrator.

Demonstrates the 12-step agentic bug investigation workflow with mocked
dependencies so no real API calls or git operations are required.

Parameters:
    issue_url (str): Full GitHub issue URL
    issue_content (str): Body text of the issue
    repo_owner (str): GitHub repository owner
    repo_name (str): GitHub repository name
    issue_number (int): Issue number
    issue_author (str): GitHub username of the issue author
    issue_title (str): Title of the issue
    cwd (Path): Working directory (keyword-only)
    verbose (bool): Show full agentic task output (keyword-only, default False)
    quiet (bool): Suppress all output except errors (keyword-only, default False)

Returns:
    Tuple of (success: bool, final_message: str, total_cost: float,
              model_used: str, changed_files: List[str])
"""

import sys
import os

sys.path.insert(0, os.path.join(os.path.dirname(__file__), ".."))

from pathlib import Path
from tempfile import TemporaryDirectory
from unittest.mock import patch, MagicMock

from pdd.agentic_bug_orchestrator import run_agentic_bug_orchestrator, BUG_STEP_TIMEOUTS


def example_happy_path() -> None:
    """Run a full 12-step investigation with all steps succeeding."""
    print("=" * 60)
    print("Example 1: Happy path — full 12-step investigation")
    print("=" * 60)

    with TemporaryDirectory() as tmpdir:
        cwd = Path(tmpdir)

        def mock_run(*args, **kwargs):
            """Return step-specific outputs for realistic behavior."""
            label = kwargs.get("label", "")
            if label == "step9":
                return (True, "Generated unit test\nFILES_CREATED: tests/test_fix.py", 0.10, "anthropic")
            if label == "step11":
                return (True, "E2E test\nE2E_FILES_CREATED: tests/e2e/test_e2e.py", 0.15, "anthropic")
            if label == "step12":
                return (True, "PR created: https://github.com/owner/repo/pull/99", 0.05, "anthropic")
            return (True, f"Output for {label}", 0.10, "anthropic")

        mock_worktree = cwd / ".pdd" / "worktrees" / "fix-issue-42"
        mock_worktree.mkdir(parents=True, exist_ok=True)

        with patch("pdd.agentic_bug_orchestrator.run_agentic_task", side_effect=mock_run), \
             patch("pdd.agentic_bug_orchestrator.load_prompt_template", return_value="Prompt for {issue_number}"), \
             patch("pdd.agentic_bug_orchestrator.preprocess", side_effect=lambda t, **kw: t), \
             patch("pdd.agentic_bug_orchestrator.save_workflow_state", return_value=None), \
             patch("pdd.agentic_bug_orchestrator.load_workflow_state", return_value=(None, None)), \
             patch("pdd.agentic_bug_orchestrator._get_git_root", return_value=cwd), \
             patch("pdd.agentic_bug_orchestrator._setup_worktree", return_value=(mock_worktree, None)), \
             patch("pdd.agentic_bug_orchestrator._verify_e2e_tests", return_value=(True, "all passed")), \
             patch("pdd.agentic_bug_orchestrator.subprocess") as _mock_sub, \
             patch("pdd.agentic_bug_orchestrator.set_agentic_progress"), \
             patch("pdd.agentic_bug_orchestrator.clear_agentic_progress"):

            import subprocess as _real_subprocess
            _mock_sub.run.return_value = _real_subprocess.CompletedProcess(
                args=[], returncode=0, stdout="main", stderr=""
            )
            _mock_sub.CalledProcessError = _real_subprocess.CalledProcessError

            success, message, cost, model, changed_files = run_agentic_bug_orchestrator(
                issue_url="https://github.com/owner/repo/issues/42",
                issue_content="The function crashes when input is None",
                repo_owner="owner",
                repo_name="repo",
                issue_number=42,
                issue_author="reporter",
                issue_title="Crash on None input",
                cwd=cwd,
                verbose=False,
                quiet=False,
            )

        print("")
        print("--- Results ---")
        print(f"Success       : {success}")
        print(f"Message       : {message}")
        print(f"Total cost    : ${cost:.4f}")
        print(f"Model used    : {model}")
        print(f"Changed files : {changed_files}")
        print("")


def example_hard_stop_duplicate() -> None:
    """Show early exit when Step 1 detects a similar issue."""
    print("=" * 60)
    print("Example 2: Hard stop — similar issue detected at Step 1")
    print("=" * 60)

    with TemporaryDirectory() as tmpdir:
        cwd = Path(tmpdir)

        # Step 1 output triggers the hard stop condition
        mock_run = MagicMock(return_value=(
            True,
            "This looks like a Duplicate of #17",
            0.05,
            "anthropic",
        ))

        with patch("pdd.agentic_bug_orchestrator.run_agentic_task", mock_run), \
             patch("pdd.agentic_bug_orchestrator.load_prompt_template", return_value="Prompt"), \
             patch("pdd.agentic_bug_orchestrator.preprocess", side_effect=lambda t, **kw: t), \
             patch("pdd.agentic_bug_orchestrator.save_workflow_state", return_value=None), \
             patch("pdd.agentic_bug_orchestrator.load_workflow_state", return_value=(None, None)), \
             patch("pdd.agentic_bug_orchestrator._get_git_root", return_value=cwd), \
             patch("pdd.agentic_bug_orchestrator.set_agentic_progress"), \
             patch("pdd.agentic_bug_orchestrator.clear_agentic_progress"):

            success, message, cost, model, changed_files = run_agentic_bug_orchestrator(
                issue_url="https://github.com/owner/repo/issues/50",
                issue_content="Something is broken",
                repo_owner="owner",
                repo_name="repo",
                issue_number=50,
                issue_author="user2",
                issue_title="Bug report",
                cwd=cwd,
                quiet=True,
            )

        print(f"Success       : {success}")
        print(f"Message       : {message}")
        print(f"Cost          : ${cost:.4f}")
        print(f"Steps run     : 1 (stopped early)")
        print("")


def example_step_timeouts() -> None:
    """Display the per-step timeout configuration."""
    print("=" * 60)
    print("Example 3: Per-step timeout configuration")
    print("=" * 60)

    step_names = {
        1: "Duplicate Check",
        2: "Docs Check",
        3: "Triage",
        4: "API Research",
        5: "Reproduce",
        6: "Root Cause",
        7: "Prompt Classification",
        8: "Test Plan",
        9: "Generate Unit Test",
        10: "Verify Unit Test",
        11: "E2E Test",
        12: "Create PR",
    }
    for step_num, timeout in sorted(BUG_STEP_TIMEOUTS.items()):
        name = step_names.get(step_num, "Unknown")
        print(f"  Step {step_num:2d} ({name:24s}): {timeout:7.0f}s")
    print("")


def main() -> None:
    """Run all examples."""
    example_happy_path()
    example_hard_stop_duplicate()
    example_step_timeouts()


if __name__ == "__main__":
    main()
