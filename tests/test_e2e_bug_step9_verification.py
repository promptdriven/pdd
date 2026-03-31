"""E2E tests for issue #960: deterministic subprocess verification of Step 9 unit tests.

These tests exercise the full bug orchestrator workflow end-to-end, verifying
that Step 9's generated unit tests are executed via subprocess after generation.

Unlike the unit tests in test_agentic_bug_orchestrator.py which mock
_verify_e2e_tests and assert on mock call counts, these E2E tests let the
real _verify_e2e_tests function run and mock only at the lowest I/O boundary
(run_pytest_and_capture_output). This verifies the integration between the
Step 9 handler and the verification subsystem.

The bug: Step 9 generates tests and performs structural pattern scanning, but
never calls _verify_e2e_tests to execute them. The only subprocess execution
lives in Step 11, which gets skipped when Step 10 emits E2E_NEEDED: no.
"""

import sys
from pathlib import Path
from typing import List
from unittest.mock import patch, MagicMock, call

import pytest

# Add project root to sys.path
project_root = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(project_root))

from pdd.agentic_bug_orchestrator import run_agentic_bug_orchestrator


@pytest.fixture
def e2e_bug_mocks(tmp_path):
    """Mock external I/O for full orchestrator runs.

    Mocks only external I/O boundaries:
    - run_agentic_task (LLM calls)
    - load_prompt_template (prompt loading)
    - console (Rich output)
    - _setup_worktree (git worktree creation)
    - preprocess (template preprocessing)
    - save/load/clear workflow state (persistence)
    - _get_git_root (git root detection)
    - set/clear agentic progress (progress tracking)
    - run_pytest_and_capture_output (subprocess pytest execution)
    - detect_structural_test_patterns (structural scanning — returns no violations)

    Does NOT mock _verify_e2e_tests — it runs for real, exercising the
    integration between Step 9 handler and the verification subsystem.
    """
    mock_worktree_path = tmp_path / ".pdd" / "worktrees" / "fix-issue-42"
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
         patch("pdd.agentic_bug_orchestrator.clear_agentic_progress") as mock_clear_progress, \
         patch("pdd.agentic_bug_orchestrator.run_pytest_and_capture_output") as mock_pytest, \
         patch("pdd.agentic_bug_orchestrator.detect_structural_test_patterns", return_value=[]) as mock_structural:

        mock_run.return_value = (True, "Step output", 0.1, "gpt-4")
        mock_load.return_value = "Prompt for {issue_number}"
        mock_worktree.return_value = (mock_worktree_path, None)

        # Default pytest result: 1 failure (expected for TDD — bug detected)
        mock_pytest.return_value = {
            "test_results": [{
                "failures": 1,
                "errors": 0,
                "passed": 0,
                "standard_output": "FAILED test_bug_detection - AssertionError",
            }],
            "return_code": 1,
        }

        yield {
            "mock_run": mock_run,
            "mock_load": mock_load,
            "mock_console": mock_console,
            "mock_worktree": mock_worktree,
            "mock_pytest": mock_pytest,
            "mock_structural": mock_structural,
            "worktree_path": mock_worktree_path,
        }


@pytest.fixture
def bug_args(tmp_path):
    """Standard arguments for bug orchestrator invocation."""
    return {
        "issue_url": "https://github.com/owner/repo/issues/42",
        "issue_content": "Bug description\nTitle: Some bug\n",
        "repo_owner": "owner",
        "repo_name": "repo",
        "issue_number": 42,
        "issue_author": "testuser",
        "issue_title": "Some bug",
        "cwd": tmp_path,
        "verbose": False,
        "quiet": True,
    }


def _configure_step_outputs(mock_run, worktree_path, step9_files="tests/test_bug.py"):
    """Configure LLM responses for a full 12-step run.

    Step 9 returns FILES_CREATED with the specified test file(s).
    Step 10 returns E2E_NEEDED: no (the common case that triggers the bug).
    """
    def side_effect(*args, **kwargs):
        label = kwargs.get("label", "")
        if label == "step9":
            # Create the test file in the worktree so _verify_e2e_tests can find it
            test_path = worktree_path / step9_files
            test_path.parent.mkdir(parents=True, exist_ok=True)
            test_path.write_text("def test_bug(): assert False  # should fail on buggy code\n")
            return (True, f"Generated test\nFILES_CREATED: {step9_files}", 0.1, "gpt-4")
        if label == "step10":
            return (True, "Verification complete.\nE2E_NEEDED: no", 0.1, "gpt-4")
        if label == "step11":
            return (True, "E2E_SKIP: unit tests sufficient", 0.1, "gpt-4")
        return (True, "Step output", 0.1, "gpt-4")

    mock_run.side_effect = side_effect


class TestE2EStep9Verification:
    """E2E tests verifying that Step 9's generated unit tests are executed
    via subprocess before the orchestrator proceeds to Step 10.

    These tests exercise the real orchestrator loop and real _verify_e2e_tests
    function, mocking only at the subprocess boundary (run_pytest_and_capture_output).
    """

    def test_step9_tests_executed_via_subprocess(self, e2e_bug_mocks, bug_args):
        """Full workflow: Step 9 generates tests -> tests must be executed via subprocess.

        This is the primary E2E test. On buggy code, run_pytest_and_capture_output
        is never called for Step 9's test files because _verify_e2e_tests is only
        invoked in Step 11 (which gets skipped when E2E_NEEDED: no).
        """
        mocks = e2e_bug_mocks
        _configure_step_outputs(mocks["mock_run"], mocks["worktree_path"])

        run_agentic_bug_orchestrator(**bug_args)

        # The core assertion: run_pytest_and_capture_output should have been
        # called with the Step 9 test file path. On buggy code, it's never
        # called because _verify_e2e_tests is only in Step 11 (skipped).
        mock_pytest = mocks["mock_pytest"]
        assert mock_pytest.called, (
            "run_pytest_and_capture_output was never called — Step 9's generated "
            "test files were never executed via subprocess. The only subprocess "
            "execution lives in Step 11 (_verify_e2e_tests), which gets skipped "
            "when Step 10 emits E2E_NEEDED: no."
        )

        # Verify it was called with a path containing the Step 9 test file
        call_args_list = [str(c) for c in mock_pytest.call_args_list]
        assert any("test_bug.py" in str(c) for c in mock_pytest.call_args_list), (
            f"run_pytest_and_capture_output was called but not with the Step 9 "
            f"test file. Calls: {call_args_list}"
        )

    def test_verification_occurs_before_step10(self, e2e_bug_mocks, bug_args):
        """Verify that subprocess execution happens during Step 9 processing,
        not delayed until Step 11.

        Track the order of operations: run_pytest_and_capture_output must be
        called BEFORE the Step 10 LLM call.
        """
        mocks = e2e_bug_mocks
        call_order: List[str] = []

        original_side_effect = None

        def tracking_run(*args, **kwargs):
            label = kwargs.get("label", "")
            call_order.append(f"llm:{label}")
            if label == "step9":
                test_path = mocks["worktree_path"] / "tests" / "test_bug.py"
                test_path.parent.mkdir(parents=True, exist_ok=True)
                test_path.write_text("def test_bug(): assert False\n")
                return (True, "Generated test\nFILES_CREATED: tests/test_bug.py", 0.1, "gpt-4")
            if label == "step10":
                return (True, "E2E_NEEDED: no", 0.1, "gpt-4")
            if label == "step11":
                return (True, "E2E_SKIP: unit tests sufficient", 0.1, "gpt-4")
            return (True, "Step output", 0.1, "gpt-4")

        def tracking_pytest(*args, **kwargs):
            call_order.append("pytest_subprocess")
            return {
                "test_results": [{
                    "failures": 1, "errors": 0, "passed": 0,
                    "standard_output": "FAILED",
                }],
                "return_code": 1,
            }

        mocks["mock_run"].side_effect = tracking_run
        mocks["mock_pytest"].side_effect = tracking_pytest

        run_agentic_bug_orchestrator(**bug_args)

        # pytest_subprocess must appear in the call order
        assert "pytest_subprocess" in call_order, (
            f"run_pytest_and_capture_output was never called. "
            f"Call order: {call_order}"
        )

        # And it must appear AFTER step9 LLM call but BEFORE step10 LLM call
        pytest_idx = call_order.index("pytest_subprocess")
        step9_idx = call_order.index("llm:step9")
        step10_indices = [i for i, c in enumerate(call_order) if c == "llm:step10"]

        assert pytest_idx > step9_idx, (
            f"pytest_subprocess ({pytest_idx}) should come after step9 ({step9_idx}). "
            f"Order: {call_order}"
        )
        if step10_indices:
            assert pytest_idx < step10_indices[0], (
                f"pytest_subprocess ({pytest_idx}) should come before step10 "
                f"({step10_indices[0]}). Verification should happen during Step 9 "
                f"processing, not deferred to Step 11. Order: {call_order}"
            )

    def test_e2e_skipped_does_not_skip_step9_verification(self, e2e_bug_mocks, bug_args):
        """When Step 10 emits E2E_NEEDED: no and Step 11 is skipped entirely,
        Step 9's tests should still have been verified via subprocess.

        This is the exact production scenario described in #960: 30+ runs where
        Step 11 was skipped and no subprocess verification occurred.
        """
        mocks = e2e_bug_mocks
        _configure_step_outputs(mocks["mock_run"], mocks["worktree_path"])

        run_agentic_bug_orchestrator(**bug_args)

        # Even though Step 11 is skipped (E2E_NEEDED: no), Step 9's tests
        # should still have been executed via subprocess
        mock_pytest = mocks["mock_pytest"]
        assert mock_pytest.called, (
            "With E2E_NEEDED: no, Step 11 is skipped — but Step 9's tests "
            "should still be verified via subprocess. Currently, the only "
            "subprocess test execution is in Step 11, creating a verification gap."
        )

    def test_verification_result_propagates_to_context(self, e2e_bug_mocks, bug_args):
        """Verify that the subprocess verification result is stored in context
        and available to downstream steps (Step 10+).

        The verification output should be captured and injected into the
        orchestrator's context dict so Step 10's prompt can reference it.
        """
        mocks = e2e_bug_mocks
        step10_instructions: List[str] = []

        def tracking_run(*args, **kwargs):
            label = kwargs.get("label", "")
            if label == "step9":
                test_path = mocks["worktree_path"] / "tests" / "test_bug.py"
                test_path.parent.mkdir(parents=True, exist_ok=True)
                test_path.write_text("def test_bug(): assert False\n")
                return (True, "Generated test\nFILES_CREATED: tests/test_bug.py", 0.1, "gpt-4")
            if label == "step10":
                # Capture the instruction passed to Step 10
                instruction = kwargs.get("instruction", args[0] if args else "")
                step10_instructions.append(instruction)
                return (True, "E2E_NEEDED: no", 0.1, "gpt-4")
            if label == "step11":
                return (True, "E2E_SKIP: unit tests sufficient", 0.1, "gpt-4")
            return (True, "Step output", 0.1, "gpt-4")

        mocks["mock_run"].side_effect = tracking_run

        run_agentic_bug_orchestrator(**bug_args)

        # The Step 10 prompt should contain verification output from Step 9
        # On buggy code, step9_test_verification is never set, so the
        # template placeholder remains unreplaced or is absent
        assert len(step10_instructions) > 0, "Step 10 was never called"

        # Check that the verification result made it into step 10's context.
        # The prompt template uses {step9_test_verification} which should be
        # populated with the subprocess output.
        step10_prompt = step10_instructions[0]
        has_verification = (
            "failure" in step10_prompt.lower()
            or "bug detected" in step10_prompt.lower()
            or "step9_test_verification" in step10_prompt
        )
        assert has_verification, (
            "Step 10's prompt does not contain Step 9 verification results. "
            "The subprocess verification output should be stored in context "
            "as step9_test_verification and passed to downstream steps."
        )
