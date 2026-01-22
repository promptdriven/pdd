"""
E2E Test for Issue #365: Repeating fix operation when fix is already finished.

This test exercises the full e2e fix orchestrator path to verify the bug where
the fix loop repeats unnecessarily when tests already pass.

Bug Description:
- The e2e fix orchestrator runs multiple cycles even when tests already pass
- Step 8 (pdd fix) correctly detects "All tests already pass with no warnings!"
- But the outer loop continues to Step 9 and if Step 9 doesn't output exact
  "ALL_TESTS_PASS" token, the loop defaults to CONTINUE_CYCLE
- This causes unnecessary additional cycles with $0 cost

User Impact:
- Wasted compute time and resources
- Confusing output showing repeated "Success to fix errors" messages
- Potential for infinite loop until max_cycles is reached

This E2E test:
1. Sets up a mock environment where tests already pass on first attempt
2. Calls the orchestrator function with minimal mocking (only LLM calls)
3. Verifies that multiple unnecessary cycles occur (detecting the bug)
4. The test FAILS on buggy code and will PASS once the bug is fixed

Run with: pytest tests/test_e2e_issue_365_repeating_fix.py -v
"""

from __future__ import annotations

import pytest
from pathlib import Path
from typing import List, Dict, Any, Tuple
from unittest.mock import patch, MagicMock


# Mark this as an E2E test (exercises real orchestration logic, but mocks LLM)
pytestmark = pytest.mark.e2e


class TestIssue365RepeatingFixE2E:
    """
    E2E tests for Issue #365: Repeating fix operation when fix is already finished.

    These tests exercise the full orchestrator loop control logic to verify
    that when Step 8 indicates all tests pass, the loop terminates correctly
    without starting unnecessary additional cycles.
    """

    @pytest.fixture
    def project_dir(self, tmp_path: Path) -> Path:
        """Create a minimal project structure for testing."""
        # Create directories that the orchestrator expects
        (tmp_path / ".pdd" / "e2e-fix-state").mkdir(parents=True, exist_ok=True)
        (tmp_path / ".git").mkdir()  # Make it look like a git repo
        return tmp_path

    @pytest.fixture
    def mock_agentic_task(self):
        """Fixture that mocks run_agentic_task to control step outputs."""
        step_outputs: Dict[str, Tuple[bool, str, float, str]] = {}
        call_log: List[Dict[str, Any]] = []

        def _mock_run_agentic_task(
            prompt: str,
            label: str,
            *,
            timeout: float = 300.0,
            cwd: Path = None,
            verbose: bool = False,
            quiet: bool = False,
            max_retries: int = 3,
            **kwargs
        ) -> Tuple[bool, str, float, str]:
            """Mock implementation that logs calls and returns configured outputs."""
            call_log.append({
                "label": label,
                "timeout": timeout,
                "cwd": str(cwd) if cwd else None,
            })

            # Return configured output or default
            if label in step_outputs:
                return step_outputs[label]

            # Default: success with generic output
            return (True, f"Output for {label}", 0.1, "gpt-4")

        return {
            "mock_fn": _mock_run_agentic_task,
            "step_outputs": step_outputs,
            "call_log": call_log,
        }

    def test_e2e_orchestrator_repeats_unnecessarily_when_tests_pass(
        self, project_dir: Path, mock_agentic_task
    ):
        """
        E2E Test: Verify that the orchestrator unnecessarily repeats cycles
        when tests already pass (bug #365).

        This test demonstrates the actual buggy behavior:
        1. Cycle 1: Step 8 outputs "All tests already pass"
        2. Cycle 1: Step 9 runs but doesn't output exact "ALL_TESTS_PASS" token
        3. Bug: Cycle 2 starts unnecessarily
        4. Cycle 2: Same as cycle 1 (tests still pass)
        5. Bug: Cycle 3 starts...

        Expected behavior (after fix):
        - Cycle 1 should complete and loop should exit
        - Only 1 cycle should run when tests already pass

        Actual behavior (buggy):
        - Multiple cycles run even though tests pass from the start
        """
        step_outputs = mock_agentic_task["step_outputs"]
        call_log = mock_agentic_task["call_log"]

        # Configure step outputs to simulate tests already passing
        # We dynamically respond based on cycle number
        cycles_started = []
        current_cycle = [0]

        def dynamic_mock(
            instruction: str,
            cwd: Path,
            *,
            verbose: bool = False,
            quiet: bool = False,
            label: str = "",
            timeout: float = None,
            max_retries: int = 1,
            retry_delay: float = 1.0,
            **kwargs
        ) -> Tuple[bool, str, float, str]:
            """Dynamic mock that tracks cycles and simulates the bug scenario."""
            call_log.append({"label": label})

            # Track cycle starts (label format: "cycle1_step1", "cycle2_step1", etc.)
            if "_step1" in label:
                # Extract cycle number from label like "cycle1_step1"
                try:
                    # label is like "cycle1_step1" - extract "1" between "cycle" and "_"
                    cycle_part = label.split("_step")[0]  # "cycle1"
                    cycle_num = int(cycle_part.replace("cycle", ""))
                    current_cycle[0] = cycle_num
                    cycles_started.append(cycle_num)
                except (IndexError, ValueError):
                    pass

            # Step 8: pdd fix - Tests already pass (label like "cycle1_step8")
            if "_step8" in label:
                return (True, """
Starting fix error loop process.
All tests already pass with no warnings! No fixes needed on this iteration.

Summary Statistics:
Initial state: 0 fails, 0 errors, 0 warnings
Final state: 0 fails, 0 errors, 0 warnings
Best iteration: final
Success: True
Improvement: 0 fails, 0 errors, 0 warnings
Overall improvement: 100.00%
Success to fix errors
Total attempts: 0
Total cost: $0.000000
""", 0.0, "gpt-4")

            # Step 9: Final verification - Simulates LLM not outputting exact token
            # This is realistic - LLMs don't always output exact tokens
            # Label like "cycle1_step9"
            if "_step9" in label:
                if current_cycle[0] >= 3:
                    # Break out on cycle 3 to prevent infinite test loop
                    return (True, "ALL_TESTS_PASS - All tests verified successfully.", 0.1, "gpt-4")
                # Bug trigger: LLM doesn't output exact "ALL_TESTS_PASS" token
                return (True, "Verification complete. All tests are passing. The fix is successful.", 0.1, "gpt-4")

            # All other steps: generic success
            return (True, f"Output for {label}", 0.1, "gpt-4")

        # Patch all external dependencies
        with patch("pdd.agentic_e2e_fix_orchestrator.run_agentic_task", side_effect=dynamic_mock), \
             patch("pdd.agentic_e2e_fix_orchestrator.load_prompt_template") as mock_load_template, \
             patch("pdd.agentic_e2e_fix_orchestrator.save_workflow_state") as mock_save, \
             patch("pdd.agentic_e2e_fix_orchestrator.load_workflow_state") as mock_load_state, \
             patch("pdd.agentic_e2e_fix_orchestrator.clear_workflow_state") as mock_clear, \
             patch("pdd.agentic_e2e_fix_orchestrator._commit_and_push") as mock_commit, \
             patch("pdd.agentic_e2e_fix_orchestrator.console") as mock_console:

            mock_load_template.return_value = "Prompt template with {issue_number}"
            mock_load_state.return_value = (None, None)  # No previous state
            mock_commit.return_value = (True, "Changes committed")

            from pdd.agentic_e2e_fix_orchestrator import run_agentic_e2e_fix_orchestrator

            success, msg, cost, model, files = run_agentic_e2e_fix_orchestrator(
                issue_url="https://github.com/test/repo/issues/365",
                issue_content="Bug: repeating fix operation",
                repo_owner="test",
                repo_name="repo",
                issue_number=365,
                issue_author="testuser",
                issue_title="Repeating fix operation when fix is already finished",
                cwd=project_dir,
                verbose=False,
                quiet=True,
                max_cycles=3,  # Limit to 3 cycles for test
                resume=False,
                use_github_state=False,  # Don't use GitHub state for test
            )

        # THE BUG ASSERTION
        # When tests already pass (Step 8 says "All tests already pass"),
        # only 1 cycle should be needed.
        # The buggy code runs 3 cycles.
        assert len(cycles_started) == 1, (
            f"BUG #365 DETECTED: Expected only 1 cycle when tests already pass, "
            f"but {len(cycles_started)} cycles were started: {cycles_started}.\n\n"
            f"This E2E test demonstrates the bug where the orchestrator repeats "
            f"fix cycles unnecessarily when Step 8 indicates tests already pass.\n\n"
            f"Root cause: The loop control logic at agentic_e2e_fix_orchestrator.py:481-491 "
            f"only checks for exact 'ALL_TESTS_PASS' token in Step 9 output. When the LLM "
            f"doesn't output this exact token, it defaults to CONTINUE_CYCLE.\n\n"
            f"Fix: The orchestrator should also detect 'All tests already pass' pattern "
            f"in Step 8 output and exit the loop without relying on Step 9's LLM token."
        )

        # Also verify success was reported
        assert success is True, f"Expected success=True when tests pass, got {success}"

    def test_e2e_orchestrator_step8_tests_pass_pattern_detection(
        self, project_dir: Path, mock_agentic_task
    ):
        """
        E2E Test: Verify that detecting "All tests already pass" pattern
        in Step 8 output should terminate the loop.

        This test verifies the expected fix behavior:
        - When Step 8 outputs "All tests already pass with no warnings!"
        - The orchestrator should recognize this and set success=True
        - No additional cycles should run

        Current behavior (buggy): Loop continues to Step 9 and beyond
        Expected behavior (fixed): Loop exits after detecting tests pass in Step 8
        """
        call_log = mock_agentic_task["call_log"]
        step9_calls = []
        cycle2_step1_calls = []

        def mock_with_tracking(
            instruction: str,
            cwd: Path,
            *,
            verbose: bool = False,
            quiet: bool = False,
            label: str = "",
            timeout: float = None,
            max_retries: int = 1,
            **kwargs
        ) -> Tuple[bool, str, float, str]:
            call_log.append({"label": label})

                # Track Step 9 calls (label like "cycle1_step9")
            if "_step9" in label:
                step9_calls.append(label)
                # Return a non-exact token to trigger the bug
                if "cycle2_" in label or "cycle3_" in label:
                    return (True, "ALL_TESTS_PASS", 0.1, "gpt-4")
                return (True, "All tests verified and passing.", 0.1, "gpt-4")

            # Track cycle 2 step 1 calls (label like "cycle2_step1")
            if "cycle2_step1" in label:
                cycle2_step1_calls.append(label)

            # Step 8: Clear indication that tests pass
            if "_step8" in label:
                return (True, """
All tests already pass with no warnings! No fixes needed on this iteration.

Summary Statistics:
Initial state: 0 fails, 0 errors, 0 warnings
Final state: 0 fails, 0 errors, 0 warnings
Success: True
""", 0.0, "gpt-4")

            return (True, f"Output for {label}", 0.1, "gpt-4")

        with patch("pdd.agentic_e2e_fix_orchestrator.run_agentic_task", side_effect=mock_with_tracking), \
             patch("pdd.agentic_e2e_fix_orchestrator.load_prompt_template") as mock_load, \
             patch("pdd.agentic_e2e_fix_orchestrator.save_workflow_state"), \
             patch("pdd.agentic_e2e_fix_orchestrator.load_workflow_state", return_value=(None, None)), \
             patch("pdd.agentic_e2e_fix_orchestrator.clear_workflow_state"), \
             patch("pdd.agentic_e2e_fix_orchestrator._commit_and_push", return_value=(True, "Committed")), \
             patch("pdd.agentic_e2e_fix_orchestrator.console"):

            mock_load.return_value = "Template {issue_number}"

            from pdd.agentic_e2e_fix_orchestrator import run_agentic_e2e_fix_orchestrator

            success, msg, cost, model, files = run_agentic_e2e_fix_orchestrator(
                issue_url="https://github.com/test/repo/issues/365",
                issue_content="Test bug",
                repo_owner="test",
                repo_name="repo",
                issue_number=365,
                issue_author="testuser",
                issue_title="Test issue",
                cwd=project_dir,
                verbose=False,
                quiet=True,
                max_cycles=2,
                resume=False,
                use_github_state=False,
            )

        # THE BUG ASSERTION
        # When Step 8 says "All tests already pass", cycle 2 should not start
        assert len(cycle2_step1_calls) == 0, (
            f"BUG #365: Cycle 2 started when Step 8 indicated tests already pass.\n"
            f"Cycle 2 Step 1 calls: {cycle2_step1_calls}\n"
            f"Expected: 0 calls to cycle2_step1 (loop should exit after cycle 1)\n"
            f"The orchestrator should detect 'All tests already pass' in Step 8 "
            f"and terminate the loop."
        )

    def test_e2e_orchestrator_cost_tracking_shows_wasted_cycles(
        self, project_dir: Path, mock_agentic_task
    ):
        """
        E2E Test: Track costs per cycle to demonstrate wasted resources.

        This test quantifies the impact of bug #365:
        - Cycle 1: Does real work, incurs costs
        - Cycle 2+: No work done ("All tests already pass"), but cycle runs anyway

        The bug wastes compute resources on unnecessary cycles.
        """
        call_log = mock_agentic_task["call_log"]
        cycle_costs: Dict[int, float] = {}
        current_cycle = [1]

        def cost_tracking_mock(
            instruction: str,
            cwd: Path,
            *,
            verbose: bool = False,
            quiet: bool = False,
            label: str = "",
            timeout: float = None,
            max_retries: int = 1,
            **kwargs
        ) -> Tuple[bool, str, float, str]:
            call_log.append({"label": label})

            # Track cycle from label (format: "cycle1_step1", "cycle2_step1", etc.)
            if "_step1" in label:
                try:
                    cycle_part = label.split("_step")[0]  # "cycle1"
                    cycle_num = int(cycle_part.replace("cycle", ""))
                    current_cycle[0] = cycle_num
                    if cycle_num not in cycle_costs:
                        cycle_costs[cycle_num] = 0.0
                except (IndexError, ValueError):
                    pass

            cost = 0.0
            output = f"Output for {label}"

            if "_step8" in label:
                if current_cycle[0] == 1:
                    # First cycle: Real fix work
                    cost = 0.5
                    output = "Fixed 3 errors. Tests now pass."
                else:
                    # Later cycles: No work, $0
                    cost = 0.0
                    output = "All tests already pass with no warnings! No fixes needed."
            elif "_step9" in label:
                cost = 0.1
                if current_cycle[0] >= 3:
                    output = "ALL_TESTS_PASS"
                else:
                    output = "Tests verified."  # No exact token - triggers bug
            else:
                cost = 0.1

            # Track cost
            if current_cycle[0] in cycle_costs:
                cycle_costs[current_cycle[0]] += cost

            return (True, output, cost, "gpt-4")

        with patch("pdd.agentic_e2e_fix_orchestrator.run_agentic_task", side_effect=cost_tracking_mock), \
             patch("pdd.agentic_e2e_fix_orchestrator.load_prompt_template", return_value="Template"), \
             patch("pdd.agentic_e2e_fix_orchestrator.save_workflow_state"), \
             patch("pdd.agentic_e2e_fix_orchestrator.load_workflow_state", return_value=(None, None)), \
             patch("pdd.agentic_e2e_fix_orchestrator.clear_workflow_state"), \
             patch("pdd.agentic_e2e_fix_orchestrator._commit_and_push", return_value=(True, "Committed")), \
             patch("pdd.agentic_e2e_fix_orchestrator.console"):

            from pdd.agentic_e2e_fix_orchestrator import run_agentic_e2e_fix_orchestrator

            success, msg, total_cost, model, files = run_agentic_e2e_fix_orchestrator(
                issue_url="https://github.com/test/repo/issues/365",
                issue_content="Test bug",
                repo_owner="test",
                repo_name="repo",
                issue_number=365,
                issue_author="testuser",
                issue_title="Test issue",
                cwd=project_dir,
                verbose=False,
                quiet=True,
                max_cycles=3,
                resume=False,
                use_github_state=False,
            )

        # Count cycles that ran
        num_cycles = len(cycle_costs)

        # THE BUG ASSERTION
        # Only cycle 1 should run (it does the real work)
        # Cycles 2 and 3 are wasted resources
        assert num_cycles == 1, (
            f"BUG #365: Wasted resources on unnecessary cycles!\n"
            f"Cycles run: {num_cycles}\n"
            f"Cost per cycle: {cycle_costs}\n"
            f"Expected: 1 cycle (cost ${cycle_costs.get(1, 0):.2f})\n"
            f"Actual: {num_cycles} cycles ran, wasting resources on cycles 2+.\n"
            f"This demonstrates the user-facing impact of bug #365."
        )


class TestIssue365LoopControlTokens:
    """
    E2E tests specifically for the loop control token detection logic.

    These tests verify how the orchestrator handles different token scenarios
    in Step 9 output.
    """

    @pytest.fixture
    def project_dir(self, tmp_path: Path) -> Path:
        """Create minimal project structure."""
        (tmp_path / ".pdd" / "e2e-fix-state").mkdir(parents=True, exist_ok=True)
        (tmp_path / ".git").mkdir()
        return tmp_path

    def test_e2e_missing_token_causes_extra_cycle(self, project_dir: Path):
        """
        E2E Test: Verify that missing loop control token causes extra cycle.

        When Step 9 doesn't output ALL_TESTS_PASS, MAX_CYCLES_REACHED, or
        CONTINUE_CYCLE, the code defaults to CONTINUE_CYCLE.

        This is by design but becomes problematic when combined with
        "All tests already pass" in Step 8.
        """
        step9_call_count = [0]

        def token_test_mock(
            instruction: str,
            cwd: Path,
            *,
            verbose: bool = False,
            quiet: bool = False,
            label: str = "",
            timeout: float = None,
            max_retries: int = 1,
            **kwargs
        ) -> Tuple[bool, str, float, str]:

            if "_step9" in label:
                step9_call_count[0] += 1
                if step9_call_count[0] == 1:
                    # First call: No token (should trigger another cycle per current logic)
                    return (True, "Everything looks good. Tests passing.", 0.1, "gpt-4")
                else:
                    # Second call: Include token to exit
                    return (True, "ALL_TESTS_PASS", 0.1, "gpt-4")

            if "_step8" in label:
                return (True, "All tests already pass with no warnings!", 0.0, "gpt-4")

            return (True, f"Output for {label}", 0.1, "gpt-4")

        with patch("pdd.agentic_e2e_fix_orchestrator.run_agentic_task", side_effect=token_test_mock), \
             patch("pdd.agentic_e2e_fix_orchestrator.load_prompt_template", return_value="Template"), \
             patch("pdd.agentic_e2e_fix_orchestrator.save_workflow_state"), \
             patch("pdd.agentic_e2e_fix_orchestrator.load_workflow_state", return_value=(None, None)), \
             patch("pdd.agentic_e2e_fix_orchestrator.clear_workflow_state"), \
             patch("pdd.agentic_e2e_fix_orchestrator._commit_and_push", return_value=(True, "ok")), \
             patch("pdd.agentic_e2e_fix_orchestrator.console"):

            from pdd.agentic_e2e_fix_orchestrator import run_agentic_e2e_fix_orchestrator

            success, msg, cost, model, files = run_agentic_e2e_fix_orchestrator(
                issue_url="https://github.com/test/repo/issues/365",
                issue_content="Test",
                repo_owner="test",
                repo_name="repo",
                issue_number=365,
                issue_author="user",
                issue_title="Test",
                cwd=project_dir,
                verbose=False,
                quiet=True,
                max_cycles=3,
                resume=False,
                use_github_state=False,
            )

        # BUG: Step 9 was called twice because first call didn't have token
        # and the orchestrator started another cycle
        assert step9_call_count[0] == 1, (
            f"BUG #365: Step 9 was called {step9_call_count[0]} times.\n"
            f"Expected: 1 call (loop should exit when Step 8 says tests pass).\n"
            f"The missing token in Step 9 caused an unnecessary additional cycle.\n"
            f"This is the core mechanism of bug #365."
        )

    def test_e2e_exact_all_tests_pass_token_works(self, project_dir: Path):
        """
        E2E Test: Verify that exact ALL_TESTS_PASS token terminates correctly.

        This is the happy path - when Step 9 outputs the exact token,
        the loop terminates as expected.
        """
        cycles_started = []

        def happy_path_mock(
            instruction: str,
            cwd: Path,
            *,
            verbose: bool = False,
            quiet: bool = False,
            label: str = "",
            timeout: float = None,
            max_retries: int = 1,
            **kwargs
        ) -> Tuple[bool, str, float, str]:

            if "_step1" in label:
                try:
                    cycle_part = label.split("_step")[0]  # "cycle1"
                    cycle_num = int(cycle_part.replace("cycle", ""))
                    cycles_started.append(cycle_num)
                except (IndexError, ValueError):
                    pass

            if "_step9" in label:
                # Exact token - should exit loop
                return (True, "ALL_TESTS_PASS - All tests verified.", 0.1, "gpt-4")

            return (True, f"Output for {label}", 0.1, "gpt-4")

        with patch("pdd.agentic_e2e_fix_orchestrator.run_agentic_task", side_effect=happy_path_mock), \
             patch("pdd.agentic_e2e_fix_orchestrator.load_prompt_template", return_value="Template"), \
             patch("pdd.agentic_e2e_fix_orchestrator.save_workflow_state"), \
             patch("pdd.agentic_e2e_fix_orchestrator.load_workflow_state", return_value=(None, None)), \
             patch("pdd.agentic_e2e_fix_orchestrator.clear_workflow_state"), \
             patch("pdd.agentic_e2e_fix_orchestrator._commit_and_push", return_value=(True, "ok")), \
             patch("pdd.agentic_e2e_fix_orchestrator.console"):

            from pdd.agentic_e2e_fix_orchestrator import run_agentic_e2e_fix_orchestrator

            success, msg, cost, model, files = run_agentic_e2e_fix_orchestrator(
                issue_url="https://github.com/test/repo/issues/365",
                issue_content="Test",
                repo_owner="test",
                repo_name="repo",
                issue_number=365,
                issue_author="user",
                issue_title="Test",
                cwd=project_dir,
                verbose=False,
                quiet=True,
                max_cycles=3,
                resume=False,
                use_github_state=False,
            )

        # Happy path: Only 1 cycle should run when token is present
        assert len(cycles_started) == 1, (
            f"Expected 1 cycle with exact token, got {len(cycles_started)}: {cycles_started}"
        )
        assert success is True, f"Expected success=True, got {success}"
