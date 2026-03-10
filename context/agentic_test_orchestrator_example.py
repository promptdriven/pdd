"""Example usage of the pdd.agentic_test_orchestrator module.

Demonstrates:
  1. Running the 18-step agentic test orchestrator with mocked dependencies
  2. How the orchestrator accumulates context between steps
  3. Hard stop conditions (duplicate, needs more info, plan blocked, no files)
  4. Step sequencing with conditional manual/exploratory testing steps (6-11)
  5. File parsing from agent output (FILES_CREATED/FILES_MODIFIED)
  6. State persistence and resumption from cached state
  7. Worktree isolation for test generation

All external dependencies (run_agentic_task, load_prompt_template, git, etc.)
are mocked so this script runs standalone without any CLI tools or API keys.
"""
from __future__ import annotations

import json
import os
import sys
import tempfile
from pathlib import Path
from unittest.mock import patch, MagicMock

# Add project root to path
project_root = Path(__file__).resolve().parent.parent
sys.path.insert(0, str(project_root))

from pdd.agentic_test_orchestrator import (
    run_agentic_test_orchestrator,
    TEST_STEP_TIMEOUTS,
)


def _mock_run_agentic_task(**step_overrides):
    """Build a mock side_effect for run_agentic_task that returns step-specific outputs.

    Args:
        step_overrides: mapping of label -> (success, output, cost, provider) tuples.
            Any step not overridden returns a default success response.

    Returns:
        A callable suitable for use as a mock side_effect.
    """
    def side_effect(instruction, cwd, *, verbose=False, quiet=False, label="",
                    timeout=None, max_retries=1, retry_delay=5.0, deadline=None,
                    use_playwright=False):
        """Mock run_agentic_task returning per-step outputs."""
        if label in step_overrides:
            return step_overrides[label]
        # Default: success with generic output
        return (True, f"Output for {label}", 0.01, "anthropic")
    return side_effect


def example_happy_path() -> None:
    """Demonstrate a full successful 18-step orchestrator run.

    The orchestrator runs steps 1-5.5, then (since TEST_TYPE is not 'web') skips
    steps 6-11, creates a worktree, runs steps 12-17, and returns success.

    Return tuple: (success: bool, message: str, total_cost: float,
                    model_used: str, changed_files: List[str])
    """
    print("=== 1. Happy Path (18-step workflow, non-web) ===")

    step_outputs = {
        "step1": (True, "No duplicate test requests found.", 0.01, "anthropic"),
        "step2": (True, "Codebase reviewed. API routes found in /api/.", 0.02, "anthropic"),
        "step3": (True, "Requirements are clear. No clarification needed.", 0.01, "anthropic"),
        "step4": (True, "TEST_TYPE: api\nTEST_FRAMEWORK: pytest\nTARGET_URL: http://localhost:8000", 0.01, "anthropic"),
        "step5": (True, "Test plan: 5 test cases for API endpoints.", 0.03, "anthropic"),
        "step5.5": (True, "Enhanced plan with contract validation and schema tests.", 0.02, "anthropic"),
        "step12": (True, "FILES_CREATED: tests/test_api.py, tests/test_auth.py\nGenerated 10 tests.", 0.05, "anthropic"),
        "step13": (True, "TEST_RESULTS: 8 passed, 2 failed.", 0.02, "anthropic"),
        "step14": (True, "FILES_MODIFIED: tests/test_api.py\nAll 10 tests now passing.", 0.03, "anthropic"),
        "step15": (True, "Plan coverage: 100%. All test cases covered.", 0.02, "anthropic"),
        # Step 16 skipped because step15 has no FILES_CREATED
        "step17": (True, "PR Created: https://github.com/example/repo/pull/42\nTitle: Add API tests (#123)", 0.01, "anthropic"),
    }

    with tempfile.TemporaryDirectory() as tmpdir:
        cwd = Path(tmpdir)

        with patch("pdd.agentic_test_orchestrator.run_agentic_task",
                    side_effect=_mock_run_agentic_task(**step_outputs)), \
             patch("pdd.agentic_test_orchestrator.load_prompt_template",
                    return_value="Mock prompt: {issue_content}"), \
             patch("pdd.agentic_test_orchestrator.load_workflow_state",
                    return_value=(None, None)), \
             patch("pdd.agentic_test_orchestrator.save_workflow_state",
                    return_value=None), \
             patch("pdd.agentic_test_orchestrator.clear_workflow_state"), \
             patch("pdd.agentic_test_orchestrator._setup_worktree",
                    return_value=(Path(tmpdir) / "worktree", None)), \
             patch("pdd.agentic_test_orchestrator.shutil") as mock_shutil, \
             patch("subprocess.run") as mock_subprocess:

            mock_shutil.which.return_value = None  # No playwright-cli
            mock_subprocess.return_value = MagicMock(stdout="main\n", returncode=0)

            success, msg, cost, model, files = run_agentic_test_orchestrator(
                issue_url="https://github.com/example/repo/issues/123",
                issue_content="Add comprehensive API tests for the /users endpoint.",
                repo_owner="example",
                repo_name="repo",
                issue_number=123,
                issue_author="test_user",
                issue_title="Add API tests for /users",
                cwd=cwd,
                verbose=False,
                quiet=True,
                timeout_adder=0.0,
                use_github_state=False,
            )

    print(f"  Success:       {success}")
    print(f"  Message:       {msg}")
    print(f"  Total cost:    ${cost:.4f}")
    print(f"  Model:         {model}")
    print(f"  Changed files: {files}")
    assert success is True
    assert "tests/test_api.py" in files
    print()


def example_hard_stop_duplicate() -> None:
    """Demonstrate early exit when step 1 detects a duplicate issue.

    The orchestrator returns (False, "Stopped at step 1: Issue is a duplicate", ...).
    """
    print("=== 2. Hard Stop: Duplicate Issue ===")

    step_outputs = {
        "step1": (True, "Duplicate of #42. This issue is already covered.", 0.01, "anthropic"),
    }

    with tempfile.TemporaryDirectory() as tmpdir:
        cwd = Path(tmpdir)

        with patch("pdd.agentic_test_orchestrator.run_agentic_task",
                    side_effect=_mock_run_agentic_task(**step_outputs)), \
             patch("pdd.agentic_test_orchestrator.load_prompt_template",
                    return_value="Mock prompt"), \
             patch("pdd.agentic_test_orchestrator.load_workflow_state",
                    return_value=(None, None)), \
             patch("pdd.agentic_test_orchestrator.save_workflow_state",
                    return_value=None), \
             patch("pdd.agentic_test_orchestrator.clear_workflow_state"), \
             patch("pdd.agentic_test_orchestrator.shutil") as mock_shutil:

            mock_shutil.which.return_value = None

            success, msg, cost, model, files = run_agentic_test_orchestrator(
                issue_url="https://github.com/example/repo/issues/200",
                issue_content="Add tests for login.",
                repo_owner="example",
                repo_name="repo",
                issue_number=200,
                issue_author="user",
                issue_title="Add login tests",
                cwd=cwd,
                quiet=True,
                use_github_state=False,
            )

    print(f"  Success:  {success}")
    print(f"  Message:  {msg}")
    print(f"  Cost:     ${cost:.4f}")
    assert success is False
    assert "Stopped at step 1" in msg
    assert "duplicate" in msg.lower()
    print()


def example_hard_stop_needs_info() -> None:
    """Demonstrate early exit when step 3 determines more info is needed.

    The orchestrator returns (False, "Stopped at step 3: Needs more info from author", ...).
    """
    print("=== 3. Hard Stop: Needs More Info ===")

    step_outputs = {
        "step1": (True, "No duplicates found.", 0.01, "anthropic"),
        "step2": (True, "Codebase reviewed.", 0.01, "anthropic"),
        "step3": (True, "Needs More Info: Please specify the API version.", 0.01, "anthropic"),
    }

    with tempfile.TemporaryDirectory() as tmpdir:
        cwd = Path(tmpdir)

        with patch("pdd.agentic_test_orchestrator.run_agentic_task",
                    side_effect=_mock_run_agentic_task(**step_outputs)), \
             patch("pdd.agentic_test_orchestrator.load_prompt_template",
                    return_value="Mock prompt"), \
             patch("pdd.agentic_test_orchestrator.load_workflow_state",
                    return_value=(None, None)), \
             patch("pdd.agentic_test_orchestrator.save_workflow_state",
                    return_value=None), \
             patch("pdd.agentic_test_orchestrator.clear_workflow_state"), \
             patch("pdd.agentic_test_orchestrator.shutil") as mock_shutil:

            mock_shutil.which.return_value = None

            success, msg, cost, _, _ = run_agentic_test_orchestrator(
                issue_url="https://github.com/example/repo/issues/300",
                issue_content="Add tests.",
                repo_owner="example",
                repo_name="repo",
                issue_number=300,
                issue_author="user",
                issue_title="Add tests",
                cwd=cwd,
                quiet=True,
                use_github_state=False,
            )

    print(f"  Success: {success}")
    print(f"  Message: {msg}")
    assert success is False
    assert "Stopped at step 3" in msg
    print()


def example_step_timeouts() -> None:
    """Show the per-step timeout configuration.

    TEST_STEP_TIMEOUTS maps step numbers (int or float for step 5.5) to
    timeout values in seconds. The timeout_adder parameter extends all timeouts.
    """
    print("=== 4. Per-Step Timeouts (seconds) ===")
    for step_num, timeout in sorted(TEST_STEP_TIMEOUTS.items(), key=lambda x: float(x[0])):
        print(f"  Step {step_num:>5}: {timeout:>7.0f}s")
    print(f"  Total steps defined: {len(TEST_STEP_TIMEOUTS)}")
    assert len(TEST_STEP_TIMEOUTS) == 18  # 18 entries (steps 1-17 plus step 5.5)
    print()


def example_state_resumption() -> None:
    """Demonstrate resuming from cached state.

    When the orchestrator finds saved state (e.g., from a previous run that
    stopped at step 3 for 'Needs More Info'), it skips already-completed steps
    and resumes from the next step.
    """
    print("=== 5. State Resumption ===")

    cached_state = {
        "last_completed_step": 3,
        "step_outputs": {
            "1": "No duplicates found.",
            "2": "Codebase reviewed.",
            "3": "Enough info available.",
        },
        "total_cost": 0.03,
        "model_used": "anthropic",
    }

    executed_labels: list = []

    def tracking_run(instruction, cwd, *, verbose=False, quiet=False, label="",
                     timeout=None, max_retries=1, retry_delay=5.0, deadline=None,
                     use_playwright=False):
        """Track which steps get executed."""
        executed_labels.append(label)
        if label == "step12":
            return (True, "FILES_CREATED: tests/test_resume.py", 0.01, "anthropic")
        return (True, f"Output for {label}", 0.01, "anthropic")

    with tempfile.TemporaryDirectory() as tmpdir:
        cwd = Path(tmpdir)

        with patch("pdd.agentic_test_orchestrator.run_agentic_task",
                    side_effect=tracking_run), \
             patch("pdd.agentic_test_orchestrator.load_prompt_template",
                    return_value="Mock prompt"), \
             patch("pdd.agentic_test_orchestrator.load_workflow_state",
                    return_value=(cached_state, 12345)), \
             patch("pdd.agentic_test_orchestrator.save_workflow_state",
                    return_value=12345), \
             patch("pdd.agentic_test_orchestrator.clear_workflow_state"), \
             patch("pdd.agentic_test_orchestrator._setup_worktree",
                    return_value=(Path(tmpdir) / "worktree", None)), \
             patch("pdd.agentic_test_orchestrator.shutil") as mock_shutil, \
             patch("subprocess.run") as mock_subprocess:

            mock_shutil.which.return_value = None
            mock_subprocess.return_value = MagicMock(stdout="main\n", returncode=0)

            success, msg, cost, _, _ = run_agentic_test_orchestrator(
                issue_url="https://github.com/example/repo/issues/123",
                issue_content="Add tests.",
                repo_owner="example",
                repo_name="repo",
                issue_number=123,
                issue_author="user",
                issue_title="Resume test",
                cwd=cwd,
                quiet=True,
                use_github_state=False,
            )

    print(f"  Resumed from step 3 (cached)")
    print(f"  Executed steps: {executed_labels}")
    print(f"  Steps 1-3 skipped: {'step1' not in executed_labels and 'step2' not in executed_labels}")
    print(f"  Step 4 executed: {'step4' in executed_labels}")
    print(f"  Success: {success}")
    assert "step1" not in executed_labels, "Step 1 should be skipped (cached)"
    assert "step4" in executed_labels, "Step 4 should be executed (first after cache)"
    print()


def example_file_parsing() -> None:
    """Demonstrate file parsing from step 12 and step 14 outputs.

    The orchestrator parses FILES_CREATED and FILES_MODIFIED lines to build
    the changed_files list for the PR step (step 17).
    """
    print("=== 6. File Parsing from Agent Output ===")

    step_outputs = {
        "step12": (True, "FILES_CREATED: tests/test_api.py, tests/test_auth.py\nGenerated tests.", 0.05, "anthropic"),
        "step14": (True, "FILES_MODIFIED: tests/test_api.py\nFILES_CREATED: tests/test_utils.py\nFixed tests.", 0.03, "anthropic"),
        "step15": (True, "Plan coverage: 100%.", 0.02, "anthropic"),
        "step17": (True, "PR Created: https://github.com/example/repo/pull/99", 0.01, "anthropic"),
    }

    with tempfile.TemporaryDirectory() as tmpdir:
        cwd = Path(tmpdir)

        with patch("pdd.agentic_test_orchestrator.run_agentic_task",
                    side_effect=_mock_run_agentic_task(**step_outputs)), \
             patch("pdd.agentic_test_orchestrator.load_prompt_template",
                    return_value="Mock prompt"), \
             patch("pdd.agentic_test_orchestrator.load_workflow_state",
                    return_value=(None, None)), \
             patch("pdd.agentic_test_orchestrator.save_workflow_state",
                    return_value=None), \
             patch("pdd.agentic_test_orchestrator.clear_workflow_state"), \
             patch("pdd.agentic_test_orchestrator._setup_worktree",
                    return_value=(Path(tmpdir) / "worktree", None)), \
             patch("pdd.agentic_test_orchestrator.shutil") as mock_shutil, \
             patch("subprocess.run") as mock_subprocess:

            mock_shutil.which.return_value = None
            mock_subprocess.return_value = MagicMock(stdout="main\n", returncode=0)

            success, msg, cost, _, files = run_agentic_test_orchestrator(
                issue_url="https://github.com/example/repo/issues/123",
                issue_content="Add tests.",
                repo_owner="example",
                repo_name="repo",
                issue_number=123,
                issue_author="user",
                issue_title="File parsing demo",
                cwd=cwd,
                quiet=True,
                use_github_state=False,
            )

    print(f"  Changed files: {files}")
    print(f"  Deduplicated:  {len(files)} unique files")
    assert "tests/test_api.py" in files
    assert "tests/test_auth.py" in files
    assert "tests/test_utils.py" in files
    print()


def main() -> None:
    """Run all examples."""
    example_happy_path()
    example_hard_stop_duplicate()
    example_hard_stop_needs_info()
    example_step_timeouts()
    example_state_resumption()
    example_file_parsing()

    print("=== All examples completed successfully ===")


if __name__ == "__main__":
    main()
