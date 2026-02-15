"""
E2E Test for Issue #530: pdd-change should handle documentation-only changes

Bug Context:
-----------
When pdd change processes a documentation-only issue:
1. Steps 1-5 complete successfully (incurring LLM token costs)
2. Step 6 outputs "No Dev Units Found"
3. The orchestrator's _check_hard_stop() at line 286 treats this as a failure
4. Workflow exits, wasting tokens from Steps 1-5

Expected behavior:
------------------
1. Step 6 should output "Documentation Only" for doc-only changes (NOT "No Dev Units Found")
2. The orchestrator should recognize "Documentation Only" as a valid continuation signal
3. Steps 7-8 (architecture/code analysis) should be skipped for documentation-only changes
4. Step 9 (implementation) should proceed directly to handle documentation file operations

This E2E test exercises the full code path from the orchestrator perspective,
demonstrating the bug by mocking an LLM that returns "No Dev Units Found" at Step 6
and verifying that the orchestrator incorrectly stops the workflow.
"""

import pytest
import subprocess
from pathlib import Path
from unittest.mock import patch, MagicMock


@pytest.fixture
def mock_git_repo_with_docs(tmp_path):
    """Create a git repository with documentation files for testing."""
    repo_path = tmp_path / "test_repo"
    repo_path.mkdir()

    # Initialize git repo
    subprocess.run(["git", "init", "-b", "main"], cwd=repo_path, check=True, capture_output=True)
    subprocess.run(["git", "config", "user.email", "test@test.com"], cwd=repo_path, check=True)
    subprocess.run(["git", "config", "user.name", "Test User"], cwd=repo_path, check=True)

    # Create project structure with documentation
    pdd_dir = repo_path / ".pdd"
    pdd_dir.mkdir()

    docs_dir = repo_path / "docs"
    docs_dir.mkdir()

    # Create README and documentation files
    (repo_path / "README.md").write_text("# Test Repository\n\nDocumentation here.")
    (docs_dir / "guide.md").write_text("# User Guide\n\nHow to use this project.")

    # Create a minimal source file
    src_dir = repo_path / "src"
    src_dir.mkdir()
    (src_dir / "main.py").write_text("def main():\n    pass\n")

    # Commit everything
    subprocess.run(["git", "add", "."], cwd=repo_path, check=True)
    subprocess.run(["git", "commit", "-m", "Initial commit"], cwd=repo_path, check=True, capture_output=True)

    return repo_path


@pytest.mark.e2e
class TestIssue530DocumentationOnlyChanges:
    """
    E2E tests for Issue #530: pdd-change fails at Step 6 for documentation-only changes.

    These tests verify the complete orchestrator code path for documentation-only
    changes, demonstrating both the bug and the expected behavior after the fix.
    """

    def test_documentation_only_change_triggers_hard_stop(self, mock_git_repo_with_docs, monkeypatch):
        """
        PRIMARY BUG TEST: Documentation-only change incorrectly triggers hard stop at Step 6.

        This test demonstrates the EXACT bug scenario:
        1. Steps 1-5 complete successfully
        2. Step 6 outputs "No Dev Units Found" (current behavior)
        3. The orchestrator's _check_hard_stop() at line 286 detects this and exits
        4. Workflow stops, wasting tokens from Steps 1-5

        This test FAILS on the current buggy code (workflow stops at Step 6)
        and should PASS after the fix (workflow continues to Step 9).
        """
        monkeypatch.setenv("PDD_FORCE_LOCAL", "1")

        # Track which steps were executed
        steps_executed = []

        def mock_run_agentic_task(instruction, cwd, verbose, quiet, timeout, label, max_retries):
            """Mock LLM agent that simulates documentation-only change workflow."""
            import re
            match = re.search(r"step(\d+)", label)
            if match:
                step_num = int(match.group(1))
                steps_executed.append(step_num)

            # Simulate successful steps 1-5
            if "step1" in label:
                return (True, "No duplicate issues found. Proceed.", 0.001, "mock-model")
            elif "step2" in label:
                return (True, "Feature not documented yet. Proceed.", 0.001, "mock-model")
            elif "step3" in label:
                return (True, "Research complete. This is a documentation-only change.", 0.001, "mock-model")
            elif "step4" in label:
                return (True, "Requirements clear. Only documentation needs updating.", 0.001, "mock-model")
            elif "step5" in label:
                return (True, "Docs changes: Update README.md with new feature description.", 0.001, "mock-model")
            elif "step6" in label:
                # BUG: Current behavior returns "No Dev Units Found" for documentation-only changes
                # This triggers the hard-stop at line 286
                return (True, "No Dev Units Found", 0.001, "mock-model")
            elif "step7" in label:
                # Step 7 should NOT be reached with the bug (hard stop at Step 6)
                return (True, "Architecture review (should not reach this).", 0.001, "mock-model")
            elif "step9" in label:
                # Step 9 should NOT be reached with the bug (hard stop at Step 6)
                return (True, "Implementation complete.", 0.001, "mock-model")

            return (True, f"Mock success for {label}", 0.001, "mock-model")

        def mock_save_state(*args, **kwargs):
            pass

        def mock_load_state(*args, **kwargs):
            return None, None

        def mock_clear_state(*args, **kwargs):
            pass

        from pdd.agentic_change_orchestrator import run_agentic_change_orchestrator

        with patch('pdd.agentic_change_orchestrator.run_agentic_task', side_effect=mock_run_agentic_task):
            with patch('pdd.agentic_change_orchestrator.save_workflow_state', side_effect=mock_save_state):
                with patch('pdd.agentic_change_orchestrator.load_workflow_state', side_effect=mock_load_state):
                    with patch('pdd.agentic_change_orchestrator.clear_workflow_state', side_effect=mock_clear_state):
                        success, message, cost, model, files = run_agentic_change_orchestrator(
                            issue_url="https://github.com/test/repo/issues/530",
                            issue_content="Update documentation for new feature X",
                            repo_owner="test",
                            repo_name="repo",
                            issue_number=530,
                            issue_author="test-user",
                            issue_title="Update docs for feature X",
                            cwd=mock_git_repo_with_docs,
                            verbose=False,
                            quiet=True,
                            use_github_state=False
                        )

        # BUG DETECTION: With current code, workflow should stop at Step 6
        # Steps executed should be [1, 2, 3, 4, 5, 6] only
        assert 6 in steps_executed, f"Step 6 should have been executed. Steps: {steps_executed}"

        # Primary bug assertion: Steps 7-8 should NOT be executed (hard stop at Step 6)
        # After the fix, this test will fail because Step 7 should be skipped but Step 9 should run
        if 7 not in steps_executed and 9 not in steps_executed:
            # This is the BUGGY behavior - workflow stopped at Step 6
            pytest.fail(
                f"BUG DETECTED (Issue #530): Workflow stopped after Step 6 with 'No Dev Units Found'.\n\n"
                f"Steps executed: {steps_executed}\n"
                f"Final status: success={success}, message={message}\n\n"
                f"Expected behavior:\n"
                f"1. Step 6 should output 'Documentation Only' (not 'No Dev Units Found')\n"
                f"2. Steps 7-8 should be skipped (architecture/code analysis not needed)\n"
                f"3. Step 9 should execute (implementation handles documentation files)\n\n"
                f"Actual behavior:\n"
                f"1. Step 6 outputs 'No Dev Units Found'\n"
                f"2. _check_hard_stop() at line 286 treats this as a failure\n"
                f"3. Workflow exits, wasting tokens from Steps 1-5"
            )

        # After the fix, workflow should continue to Step 9
        assert 9 in steps_executed, (
            f"After fix: Step 9 should execute for documentation-only changes. "
            f"Steps executed: {steps_executed}"
        )

    def test_documentation_only_with_fixed_behavior(self, mock_git_repo_with_docs, monkeypatch):
        """
        EXPECTED BEHAVIOR TEST: Documentation-only change should skip Steps 7-8 and proceed to Step 9.

        This test demonstrates the CORRECT behavior after the fix:
        1. Steps 1-5 complete successfully
        2. Step 6 outputs "Documentation Only" (fixed behavior)
        3. Steps 7-8 are skipped (not needed for documentation-only changes)
        4. Step 9 executes (implementation handles documentation files)

        This test PASSES when the fix is implemented correctly.
        """
        monkeypatch.setenv("PDD_FORCE_LOCAL", "1")

        steps_executed = []

        def mock_run_agentic_task(instruction, cwd, verbose, quiet, timeout, label, max_retries):
            """Mock LLM agent that simulates FIXED documentation-only workflow."""
            import re
            match = re.search(r"step(\d+)", label)
            if match:
                step_num = int(match.group(1))
                steps_executed.append(step_num)

            # Simulate successful steps 1-5
            if "step1" in label:
                return (True, "No duplicate issues found. Proceed.", 0.001, "mock-model")
            elif "step2" in label:
                return (True, "Feature not documented yet. Proceed.", 0.001, "mock-model")
            elif "step3" in label:
                return (True, "Research complete. This is a documentation-only change.", 0.001, "mock-model")
            elif "step4" in label:
                return (True, "Requirements clear. Only documentation needs updating.", 0.001, "mock-model")
            elif "step5" in label:
                return (True, "Docs changes: Update README.md with new feature description.", 0.001, "mock-model")
            elif "step6" in label:
                # FIXED: Output "Documentation Only" instead of "No Dev Units Found"
                return (True, "Documentation Only\n\nNo code changes needed, only documentation.", 0.001, "mock-model")
            elif "step7" in label:
                # Should NOT be reached (skipped for documentation-only)
                pytest.fail("Step 7 should be skipped for documentation-only changes")
            elif "step8" in label:
                # Should NOT be reached (skipped for documentation-only)
                pytest.fail("Step 8 should be skipped for documentation-only changes")
            elif "step9" in label:
                # Should be reached (implementation handles documentation)
                return (True, "FILES_MODIFIED: README.md, docs/guide.md", 0.001, "mock-model")

            return (True, f"Mock success for {label}", 0.001, "mock-model")

        def mock_save_state(*args, **kwargs):
            pass

        def mock_load_state(*args, **kwargs):
            return None, None

        def mock_clear_state(*args, **kwargs):
            pass

        from pdd.agentic_change_orchestrator import run_agentic_change_orchestrator

        with patch('pdd.agentic_change_orchestrator.run_agentic_task', side_effect=mock_run_agentic_task):
            with patch('pdd.agentic_change_orchestrator.save_workflow_state', side_effect=mock_save_state):
                with patch('pdd.agentic_change_orchestrator.load_workflow_state', side_effect=mock_load_state):
                    with patch('pdd.agentic_change_orchestrator.clear_workflow_state', side_effect=mock_clear_state):
                        success, message, cost, model, files = run_agentic_change_orchestrator(
                            issue_url="https://github.com/test/repo/issues/530",
                            issue_content="Update documentation for new feature X",
                            repo_owner="test",
                            repo_name="repo",
                            issue_number=530,
                            issue_author="test-user",
                            issue_title="Update docs for feature X",
                            cwd=mock_git_repo_with_docs,
                            verbose=False,
                            quiet=True,
                            use_github_state=False
                        )

        # Verify the CORRECT flow:
        # Steps 1-6 should execute
        for step in [1, 2, 3, 4, 5, 6]:
            assert step in steps_executed, f"Step {step} should execute. Steps: {steps_executed}"

        # Steps 7-8 should be skipped
        assert 7 not in steps_executed, f"Step 7 should be skipped for documentation-only. Steps: {steps_executed}"
        assert 8 not in steps_executed, f"Step 8 should be skipped for documentation-only. Steps: {steps_executed}"

        # Step 9 should execute
        assert 9 in steps_executed, f"Step 9 should execute for documentation-only. Steps: {steps_executed}"

        # Workflow should succeed
        assert success is True, f"Workflow should succeed for documentation-only changes. Message: {message}"

    def test_normal_dev_units_path_continues_to_step7(self, mock_git_repo_with_docs, monkeypatch):
        """
        REGRESSION TEST: Normal dev units path should continue through Steps 7-8 as before.

        This test ensures the fix doesn't break the normal workflow when dev units
        ARE found and code changes are needed.
        """
        monkeypatch.setenv("PDD_FORCE_LOCAL", "1")

        steps_executed = []

        def mock_run_agentic_task(instruction, cwd, verbose, quiet, timeout, label, max_retries):
            """Mock LLM agent that simulates normal workflow with dev units."""
            import re
            match = re.search(r"step(\d+)", label)
            if match:
                step_num = int(match.group(1))
                steps_executed.append(step_num)

            # Simulate successful steps 1-6
            if "step1" in label:
                return (True, "No duplicate issues found. Proceed.", 0.001, "mock-model")
            elif "step2" in label:
                return (True, "Feature not implemented yet. Proceed.", 0.001, "mock-model")
            elif "step3" in label:
                return (True, "Research complete. Code changes needed.", 0.001, "mock-model")
            elif "step4" in label:
                return (True, "Requirements clear. Need to modify src/main.py.", 0.001, "mock-model")
            elif "step5" in label:
                return (True, "No docs changes needed.", 0.001, "mock-model")
            elif "step6" in label:
                # Normal case: Dev units found
                return (True, "Dev Units: src/main.py\n\nNeed to add new function.", 0.001, "mock-model")
            elif "step7" in label:
                # Should be reached (architecture review for code changes)
                return (True, "Architecture review complete.", 0.001, "mock-model")
            elif "step8" in label:
                # Should be reached (analyze prompt changes)
                return (True, "No prompt changes needed.", 0.001, "mock-model")
            elif "step9" in label:
                # Should be reached (implementation)
                return (True, "FILES_MODIFIED: src/main.py", 0.001, "mock-model")

            return (True, f"Mock success for {label}", 0.001, "mock-model")

        def mock_save_state(*args, **kwargs):
            pass

        def mock_load_state(*args, **kwargs):
            return None, None

        def mock_clear_state(*args, **kwargs):
            pass

        from pdd.agentic_change_orchestrator import run_agentic_change_orchestrator

        with patch('pdd.agentic_change_orchestrator.run_agentic_task', side_effect=mock_run_agentic_task):
            with patch('pdd.agentic_change_orchestrator.save_workflow_state', side_effect=mock_save_state):
                with patch('pdd.agentic_change_orchestrator.load_workflow_state', side_effect=mock_load_state):
                    with patch('pdd.agentic_change_orchestrator.clear_workflow_state', side_effect=mock_clear_state):
                        success, message, cost, model, files = run_agentic_change_orchestrator(
                            issue_url="https://github.com/test/repo/issues/530",
                            issue_content="Add new feature X",
                            repo_owner="test",
                            repo_name="repo",
                            issue_number=530,
                            issue_author="test-user",
                            issue_title="Add feature X",
                            cwd=mock_git_repo_with_docs,
                            verbose=False,
                            quiet=True,
                            use_github_state=False
                        )

        # Verify normal flow continues through Steps 7-8
        for step in [1, 2, 3, 4, 5, 6, 7, 8, 9]:
            assert step in steps_executed, f"Step {step} should execute in normal flow. Steps: {steps_executed}"

        # Workflow should succeed
        assert success is True, f"Workflow should succeed for normal dev units path. Message: {message}"

    def test_no_dev_units_found_without_docs_still_triggers_hard_stop(self, mock_git_repo_with_docs, monkeypatch):
        """
        REGRESSION TEST: True "No Dev Units Found" (without documentation context) should still stop.

        This test ensures the fix distinguishes between:
        - "Documentation Only" (valid continuation path) - should proceed to Step 9
        - "No Dev Units Found" (true failure) - should trigger hard stop

        When there are NO dev units AND NO documentation changes, the workflow
        should still stop as a failure (existing behavior preserved).
        """
        monkeypatch.setenv("PDD_FORCE_LOCAL", "1")

        steps_executed = []

        def mock_run_agentic_task(instruction, cwd, verbose, quiet, timeout, label, max_retries):
            """Mock LLM agent that finds neither dev units nor documentation changes."""
            import re
            match = re.search(r"step(\d+)", label)
            if match:
                step_num = int(match.group(1))
                steps_executed.append(step_num)

            if "step1" in label:
                return (True, "No duplicate issues found. Proceed.", 0.001, "mock-model")
            elif "step2" in label:
                return (True, "Already implemented. Proceed.", 0.001, "mock-model")
            elif "step3" in label:
                return (True, "Research complete. Issue is unclear.", 0.001, "mock-model")
            elif "step4" in label:
                return (True, "Requirements unclear.", 0.001, "mock-model")
            elif "step5" in label:
                return (True, "No docs changes needed.", 0.001, "mock-model")
            elif "step6" in label:
                # True failure case: No dev units AND no documentation changes
                return (True, "No Dev Units Found", 0.001, "mock-model")

            return (True, f"Mock success for {label}", 0.001, "mock-model")

        def mock_save_state(*args, **kwargs):
            pass

        def mock_load_state(*args, **kwargs):
            return None, None

        def mock_clear_state(*args, **kwargs):
            pass

        from pdd.agentic_change_orchestrator import run_agentic_change_orchestrator

        with patch('pdd.agentic_change_orchestrator.run_agentic_task', side_effect=mock_run_agentic_task):
            with patch('pdd.agentic_change_orchestrator.save_workflow_state', side_effect=mock_save_state):
                with patch('pdd.agentic_change_orchestrator.load_workflow_state', side_effect=mock_load_state):
                    with patch('pdd.agentic_change_orchestrator.clear_workflow_state', side_effect=mock_clear_state):
                        success, message, cost, model, files = run_agentic_change_orchestrator(
                            issue_url="https://github.com/test/repo/issues/530",
                            issue_content="Unclear issue with no clear action items",
                            repo_owner="test",
                            repo_name="repo",
                            issue_number=530,
                            issue_author="test-user",
                            issue_title="Unclear issue",
                            cwd=mock_git_repo_with_docs,
                            verbose=False,
                            quiet=True,
                            use_github_state=False
                        )

        # Verify workflow stopped at Step 6 (existing hard-stop behavior)
        assert 6 in steps_executed, f"Step 6 should execute. Steps: {steps_executed}"
        assert 7 not in steps_executed, f"Step 7 should NOT execute (hard stop). Steps: {steps_executed}"
        assert 9 not in steps_executed, f"Step 9 should NOT execute (hard stop). Steps: {steps_executed}"

        # Workflow should fail with "No dev units found" message
        assert success is False, f"Workflow should fail when no dev units AND no docs changes. Message: {message}"
        assert "no dev units" in message.lower(), f"Failure message should mention 'no dev units'. Message: {message}"
