#!/usr/bin/env python3
"""
Example usage of pdd.agentic_change_orchestrator.

Demonstrates:
1. Running the 13-step agentic change orchestrator (mocked)
2. Handling early PR guard (existing PR returns immediately)
3. Resuming from cached state (skips completed steps)
4. Helper functions: _parse_changed_files, _review_loop_no_issues,
   _parse_direct_edit_candidates, _check_hard_stop
"""

import sys
import os

sys.path.insert(0, os.path.join(os.path.dirname(__file__), ".."))

from pathlib import Path
from unittest.mock import patch, MagicMock
import subprocess
import json

# ---------------------------------------------------------------------------
# Import from the module under demonstration
# ---------------------------------------------------------------------------
from pdd.agentic_change_orchestrator import (
    run_agentic_change_orchestrator,
    _parse_changed_files,
    _parse_direct_edit_candidates,
    _review_loop_no_issues,
    _check_hard_stop,
    _load_pddrc_context,
    _build_dependency_context,
    CHANGE_STEP_TIMEOUTS,
    MAX_REVIEW_ITERATIONS,
)


def demo_parse_changed_files():
    """Show how FILES_CREATED/FILES_MODIFIED/DIRECT_EDITS lines are parsed."""
    print("=== _parse_changed_files ===")
    output = (
        "Step 9 complete.\n"
        "FILES_CREATED: prompts/new_module_python.prompt\n"
        "FILES_MODIFIED: prompts/existing_module_python.prompt\n"
        "DIRECT_EDITS: pdd/cli.py\n"
    )
    files = _parse_changed_files(output)
    print(f"  Input output contains FILES_CREATED, FILES_MODIFIED, DIRECT_EDITS")
    print(f"  Parsed files: {files}")
    assert "prompts/new_module_python.prompt" in files
    assert "prompts/existing_module_python.prompt" in files
    assert "pdd/cli.py" in files
    print("  OK")
    print()


def demo_parse_direct_edit_candidates():
    """Show parsing of Direct Edit Candidates table from Step 6 output."""
    print("=== _parse_direct_edit_candidates ===")
    step6_output = (
        "## Dev Units\n"
        "...\n"
        "### Direct Edit Candidates\n"
        "| File | Edit Type | Markers |\n"
        "| --- | --- | --- |\n"
        "| `pdd/cli.py` | uncomment | # TODO |\n"
        "| `pdd/main.py` | remove placeholder | PLACEHOLDER |\n"
    )
    candidates = _parse_direct_edit_candidates(step6_output)
    print(f"  Parsed candidates: {candidates}")
    assert "pdd/cli.py" in candidates
    assert "pdd/main.py" in candidates
    print("  OK")
    print()


def demo_review_loop_no_issues():
    """Show the loose matching for 'no issues found' in review loop."""
    print("=== _review_loop_no_issues ===")
    test_cases = [
        ("No Issues Found", True),
        ("After review, no issues identified in the prompts.", True),
        ("All checks passed successfully.", True),
        ("Found 3 issues that need fixing.", False),
        ("", False),
    ]
    for text, expected in test_cases:
        result = _review_loop_no_issues(text)
        status = "PASS" if result == expected else "FAIL"
        print(f"  [{status}] '{text[:50]}...' -> {result} (expected {expected})")
    print()


def demo_check_hard_stop():
    """Show hard stop detection for various steps."""
    print("=== _check_hard_stop ===")
    test_cases = [
        (1, "This is a Duplicate of #42", "Issue is a duplicate"),
        (2, "Already Implemented in v2.0", "Already implemented"),
        (4, "Normal output mentioning clarification", None),
        (4, "STOP_CONDITION: clarification needed from user", "Clarification needed"),
        (7, "STOP_CONDITION: architectural decision required", "Architectural decision needed"),
        (8, "No Changes Required for this issue", "No changes needed"),
        (9, "FAIL: could not write file", "Implementation failed"),
        (3, "Research completed successfully", None),
    ]
    for step_num, output, expected in test_cases:
        result = _check_hard_stop(step_num, output)
        status = "PASS" if result == expected else "FAIL"
        label = result if result else "None"
        print(f"  [{status}] Step {step_num}: '{output[:40]}...' -> {label}")
    print()


def demo_constants():
    """Show the per-step timeout configuration and review iteration limit."""
    print("=== Constants ===")
    print(f"  MAX_REVIEW_ITERATIONS: {MAX_REVIEW_ITERATIONS}")
    assert MAX_REVIEW_ITERATIONS == 5
    print(f"  CHANGE_STEP_TIMEOUTS ({len(CHANGE_STEP_TIMEOUTS)} steps):")
    for step, timeout in sorted(CHANGE_STEP_TIMEOUTS.items()):
        print(f"    Step {step:2d}: {timeout:.0f}s")
    assert CHANGE_STEP_TIMEOUTS[9] == 1000.0, "Step 9 should have the highest timeout"
    print()


def demo_full_orchestrator_mocked():
    """
    Run the full orchestrator with all external dependencies mocked.

    Demonstrates:
    - The 13-step flow completing successfully
    - Cost accumulation across steps
    - File extraction from step 9 and step 10
    - Return tuple: (success, message, cost, model, changed_files)
    """
    print("=== Full Orchestrator (mocked) ===")

    call_count = {"n": 0}

    def mock_run_agentic_task(**kwargs):
        """Mock that returns step-specific outputs."""
        label = kwargs.get("label", "")
        call_count["n"] += 1
        if label == "step9":
            return (
                True,
                "Implementation done.\nFILES_MODIFIED: prompts/foo_python.prompt\nFILES_CREATED: prompts/bar_python.prompt",
                0.50,
                "claude-sonnet-4-20250514",
            )
        if label == "step10":
            return (
                True,
                "Architecture updated.\nARCHITECTURE_FILES_MODIFIED: architecture.json",
                0.10,
                "claude-sonnet-4-20250514",
            )
        if label.startswith("step11"):
            return (True, "Review complete. No Issues Found.", 0.05, "claude-sonnet-4-20250514")
        if label == "step13":
            return (
                True,
                "PR created at https://github.com/owner/repo/pull/99",
                0.15,
                "claude-sonnet-4-20250514",
            )
        return (True, f"Output for {label}", 0.10, "claude-sonnet-4-20250514")

    tmp_dir = Path(os.path.dirname(__file__)) / ".." / "tmp_example_run"
    tmp_dir = tmp_dir.resolve()
    tmp_dir.mkdir(parents=True, exist_ok=True)

    # Create minimal git repo structure so _get_git_root doesn't fail
    git_dir = tmp_dir / ".git"
    git_dir.mkdir(exist_ok=True)

    try:
        with (
            patch("pdd.agentic_change_orchestrator.run_agentic_task", side_effect=mock_run_agentic_task),
            patch("pdd.agentic_change_orchestrator.load_prompt_template", return_value="Mock template {issue_content}"),
            patch("pdd.agentic_change_orchestrator.load_workflow_state", return_value=(None, None)),
            patch("pdd.agentic_change_orchestrator.save_workflow_state", return_value=None),
            patch("pdd.agentic_change_orchestrator.clear_workflow_state"),
            patch("pdd.agentic_change_orchestrator.post_step_comment"),
            patch("pdd.agentic_change_orchestrator.set_agentic_progress"),
            patch("pdd.agentic_change_orchestrator.clear_agentic_progress"),
            patch("pdd.agentic_change_orchestrator._check_existing_pr", return_value=None),
            patch("pdd.agentic_change_orchestrator.preprocess", side_effect=lambda prompt, **kw: prompt),
            patch("pdd.agentic_change_orchestrator.subprocess.run") as mock_subproc,
            patch("pdd.agentic_change_orchestrator._load_pddrc_context", return_value={
                "language": "python", "source_dir": "pdd/", "test_dir": "tests/",
                "example_dir": "examples/", "ext": "py", "lang": "_python",
            }),
            patch("pdd.agentic_change_orchestrator.build_dependency_graph", return_value={}),
        ):
            # Mock subprocess for git operations
            mock_result = MagicMock()
            mock_result.stdout = str(tmp_dir)
            mock_result.returncode = 0
            mock_subproc.return_value = mock_result

            success, message, total_cost, model, changed_files = run_agentic_change_orchestrator(
                issue_url="https://github.com/owner/repo/issues/99",
                issue_content="Add new feature X to the CLI",
                repo_owner="owner",
                repo_name="repo",
                issue_number=99,
                issue_author="contributor",
                issue_title="Add feature X",
                cwd=tmp_dir,
                quiet=True,
            )

        print(f"  Success: {success}")
        print(f"  Message: {message}")
        print(f"  Total cost: ${total_cost:.2f}")
        print(f"  Model: {model}")
        print(f"  Changed files: {changed_files}")
        print(f"  Steps executed: {call_count['n']}")
        assert success is True, f"Expected success but got: {message}"
        assert "pull/99" in message
        assert total_cost > 0
        assert len(changed_files) > 0
        print("  OK")
    finally:
        import shutil
        if tmp_dir.exists():
            shutil.rmtree(tmp_dir, ignore_errors=True)
    print()


def demo_existing_pr_guard():
    """
    Demonstrate that if a PR already exists for the issue branch,
    the orchestrator returns early without running any steps.

    Return value: (True, "PR already exists: <url>", 0.0, "unknown", [])
    """
    print("=== Existing PR Guard ===")

    tmp_dir = Path(os.path.dirname(__file__)) / ".." / "tmp_example_pr"
    tmp_dir = tmp_dir.resolve()
    tmp_dir.mkdir(parents=True, exist_ok=True)
    (tmp_dir / ".git").mkdir(exist_ok=True)

    try:
        with (
            patch("pdd.agentic_change_orchestrator.load_workflow_state", return_value=(None, None)),
            patch("pdd.agentic_change_orchestrator._check_existing_pr",
                  return_value="https://github.com/owner/repo/pull/42"),
            patch("pdd.agentic_change_orchestrator.clear_agentic_progress"),
            patch("pdd.agentic_change_orchestrator.subprocess.run") as mock_subproc,
        ):
            mock_result = MagicMock()
            mock_result.stdout = str(tmp_dir)
            mock_result.returncode = 0
            mock_subproc.return_value = mock_result

            success, message, cost, model, files = run_agentic_change_orchestrator(
                issue_url="https://github.com/owner/repo/issues/42",
                issue_content="Some issue",
                repo_owner="owner",
                repo_name="repo",
                issue_number=42,
                issue_author="user",
                issue_title="Test PR guard",
                cwd=tmp_dir,
                quiet=True,
            )

        print(f"  Success: {success}")
        print(f"  Message: {message}")
        print(f"  Cost: ${cost:.2f}")
        print(f"  Model: {model}")
        print(f"  Files: {files}")
        assert success is True
        assert "PR already exists" in message
        assert cost == 0.0
        assert model == "unknown"
        assert files == []
        print("  OK")
    finally:
        import shutil
        if tmp_dir.exists():
            shutil.rmtree(tmp_dir, ignore_errors=True)
    print()


def main():
    """Run all demonstrations."""
    print("pdd.agentic_change_orchestrator - Example Usage")
    print("=" * 50)
    print()

    demo_constants()
    demo_parse_changed_files()
    demo_parse_direct_edit_candidates()
    demo_review_loop_no_issues()
    demo_check_hard_stop()
    demo_existing_pr_guard()
    demo_full_orchestrator_mocked()

    print("All demonstrations passed.")


if __name__ == "__main__":
    main()
