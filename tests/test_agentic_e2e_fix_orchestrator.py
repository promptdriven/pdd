"""Tests for agentic_e2e_fix_orchestrator prompt formatting.

These tests verify that all e2e fix workflow prompts can be formatted
with the context variables provided by the orchestrator, without
raising KeyError on undefined placeholders.
"""
import pytest
from pdd.load_prompt_template import load_prompt_template


class TestPromptFormatting:
    """Test that all e2e fix prompts can be formatted with orchestrator context."""

    @pytest.fixture
    def base_context(self):
        """Minimal context provided by orchestrator for Step 1."""
        return {
            "issue_url": "https://github.com/test/repo/issues/1",
            "repo_owner": "test",
            "repo_name": "repo",
            "issue_number": 1,
            "cycle_number": 1,
            "max_cycles": 5,
            "issue_content": "Test issue content",
            "protect_tests": "false",
            "protect_tests_flag": "",
        }

    def test_step1_prompt_formats_without_error(self, base_context):
        """Step 1 template should format successfully with orchestrator context.

        Reproduces bug: Template has {test_files}, {dev_unit}, {N}, etc.
        that are not provided in the orchestrator context.
        """
        template = load_prompt_template("agentic_e2e_fix_step1_unit_tests_LLM")
        assert template is not None, "Template should load"

        # This should NOT raise KeyError
        formatted = template.format(**base_context)
        assert "pytest" in formatted
        assert "{issue_url}" not in formatted  # Should be substituted
        assert "{dev_unit}" in formatted  # Should remain as example literal

    def test_step2_prompt_formats_without_error(self, base_context):
        """Step 2 template should format successfully with orchestrator context.

        Reproduces bug: Template has {e2e_test_files}, {test_file}, {N}, etc.
        that are not provided in the orchestrator context.
        """
        base_context["step1_output"] = "Step 1 output"
        template = load_prompt_template("agentic_e2e_fix_step2_e2e_tests_LLM")
        assert template is not None, "Template should load"

        # This should NOT raise KeyError
        formatted = template.format(**base_context)
        assert "pytest" in formatted
        assert "{test_file}" in formatted  # Should remain as example literal

    def test_step3_prompt_formats_without_error(self, base_context):
        """Step 3 template should format successfully with orchestrator context.

        Regression test for issue #338: Template had {test_name}, {description},
        {detailed_explanation} that were not escaped with double braces.
        """
        base_context["step1_output"] = "Step 1 output"
        base_context["step2_output"] = "Step 2 output"
        template = load_prompt_template("agentic_e2e_fix_step3_root_cause_LLM")
        assert template is not None, "Template should load"

        # This should NOT raise KeyError (was the bug in issue #338)
        formatted = template.format(**base_context)
        assert "{test_name}" in formatted  # Should remain as example literal
        assert "{description}" in formatted  # Should remain as example literal
        assert "{detailed_explanation}" in formatted  # Should remain as example literal

    def test_step7_prompt_formats_without_error(self, base_context):
        """Step 7 template should format successfully with orchestrator context.

        Reproduces bug: Template has {test_files}, {name}, {N}, etc.
        that are not provided in the orchestrator context.
        """
        for i in range(1, 7):
            base_context[f"step{i}_output"] = f"Step {i} output"
        template = load_prompt_template("agentic_e2e_fix_step7_verify_tests_LLM")
        assert template is not None, "Template should load"

        # This should NOT raise KeyError
        formatted = template.format(**base_context)
        assert "pytest" in formatted
        assert "{name}" in formatted  # Should remain as example literal

    def test_step1_prompt_formats_with_protect_tests_flag(self, base_context):
        """Step 1 prompt should accept protect_tests_flag variable.

        When --protect-tests is enabled, the prompt should include the flag
        in pdd fix commands.
        """
        base_context["protect_tests"] = "true"
        base_context["protect_tests_flag"] = "--protect-tests"

        template = load_prompt_template("agentic_e2e_fix_step1_unit_tests_LLM")
        assert template is not None

        # This should NOT raise KeyError for missing protect_tests_flag
        formatted = template.format(**base_context)
        assert "--protect-tests" in formatted, \
            "Step 1 prompt should include --protect-tests flag when enabled"

    def test_step8_prompt_formats_with_protect_tests_flag(self, base_context):
        """Step 8 prompt should accept protect_tests_flag variable.

        When --protect-tests is enabled, the prompt should include the flag
        in pdd fix commands.
        """
        # Add required step outputs
        for i in range(1, 8):
            base_context[f"step{i}_output"] = f"Step {i} output"
        base_context["failing_dev_units"] = "test_module"
        base_context["protect_tests"] = "true"
        base_context["protect_tests_flag"] = "--protect-tests"

        template = load_prompt_template("agentic_e2e_fix_step8_run_pdd_fix_LLM")
        assert template is not None

        # This should NOT raise KeyError for missing protect_tests_flag
        formatted = template.format(**base_context)
        assert "--protect-tests" in formatted, \
            "Step 8 prompt should include --protect-tests flag when enabled"


def test_run_agentic_e2e_fix_orchestrator_has_protect_tests_parameter():
    """run_agentic_e2e_fix_orchestrator should accept protect_tests parameter.

    This ensures the orchestrator can receive and use the protect_tests flag.
    """
    import inspect
    from pdd.agentic_e2e_fix_orchestrator import run_agentic_e2e_fix_orchestrator

    sig = inspect.signature(run_agentic_e2e_fix_orchestrator)
    params = list(sig.parameters.keys())

    assert 'protect_tests' in params, \
        "run_agentic_e2e_fix_orchestrator must accept protect_tests parameter"


# --- Loop Control Tests for Issue #365 ---
# These tests verify the fix for issue #365: repeating fix operation when fix is already finished


class TestLoopControl:
    """Tests for loop control logic in the e2e fix orchestrator.

    Issue #365: The orchestrator repeats fix cycles unnecessarily when tests
    already pass. The bug is in the loop control logic at lines 481-491:
    - Step 8 (`pdd fix`) exits correctly when tests pass, outputting
      "All tests already pass with no warnings!"
    - But the outer loop doesn't detect this and waits for Step 9's LLM output
    - If Step 9 doesn't output exact token "ALL_TESTS_PASS", loop defaults to CONTINUE_CYCLE
    - This causes unnecessary additional cycles with $0 cost
    """

    @pytest.fixture
    def mock_e2e_dependencies(self, tmp_path):
        """Mocks external dependencies for e2e fix orchestrator tests."""
        from unittest.mock import patch, MagicMock

        with patch("pdd.agentic_e2e_fix_orchestrator.run_agentic_task") as mock_run, \
             patch("pdd.agentic_e2e_fix_orchestrator.load_prompt_template") as mock_load, \
             patch("pdd.agentic_e2e_fix_orchestrator.console") as mock_console, \
             patch("pdd.agentic_e2e_fix_orchestrator.save_workflow_state") as mock_save, \
             patch("pdd.agentic_e2e_fix_orchestrator.load_workflow_state") as mock_load_state, \
             patch("pdd.agentic_e2e_fix_orchestrator.clear_workflow_state") as mock_clear:

            # Default behavior: successful run
            mock_run.return_value = (True, "Step output", 0.1, "gpt-4")
            mock_load.return_value = "Prompt for {issue_number}"
            mock_load_state.return_value = (None, None)  # No previous state
            mock_save.return_value = None

            yield {
                "mock_run": mock_run,
                "mock_load": mock_load,
                "mock_console": mock_console,
                "mock_save": mock_save,
                "mock_load_state": mock_load_state,
                "mock_clear": mock_clear,
                "tmp_path": tmp_path,
            }

    @pytest.fixture
    def default_e2e_args(self, tmp_path):
        """Provides default arguments for the e2e orchestrator function."""
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
            "max_cycles": 5,
            "resume": False,
        }

    def test_all_tests_pass_token_terminates_loop(self, mock_e2e_dependencies, default_e2e_args):
        """Verify ALL_TESTS_PASS token in Step 9 terminates loop correctly.

        This is the expected happy path: Step 9 outputs ALL_TESTS_PASS and
        the loop exits without starting another cycle.
        """
        from pdd.agentic_e2e_fix_orchestrator import run_agentic_e2e_fix_orchestrator

        mock_run = mock_e2e_dependencies["mock_run"]

        cycle_count = [0]

        def side_effect(*args, **kwargs):
            label = kwargs.get('label', '')
            if 'cycle' in label and '_step1' in label:
                cycle_count[0] += 1
            if '_step9' in label:
                # Step 9 outputs the termination token
                return (True, "ALL_TESTS_PASS - All tests pass successfully", 0.1, "gpt-4")
            return (True, f"Output for {label}", 0.1, "gpt-4")

        mock_run.side_effect = side_effect

        success, msg, cost, model, files = run_agentic_e2e_fix_orchestrator(**default_e2e_args)

        # Should succeed and only use 1 cycle
        assert success is True, f"Expected success but got: {msg}"
        assert cycle_count[0] == 1, f"Expected 1 cycle but got {cycle_count[0]}"

    def test_tests_already_pass_in_step8_should_exit_loop(self, mock_e2e_dependencies, default_e2e_args):
        """Bug #365: When Step 8 outputs 'All tests already pass', loop should exit.

        This test reproduces the core bug scenario:
        1. Step 8 (pdd fix) detects tests already pass and outputs the pattern
        2. The orchestrator should detect this and exit the loop
        3. Instead, in the buggy code, it continues to Step 9 and potentially more cycles

        EXPECTED BEHAVIOR (after fix):
        - Loop should terminate after Step 8 detects tests already pass
        - OR Step 9 should reliably output ALL_TESTS_PASS
        - Loop should NOT start a second cycle when tests already pass

        ACTUAL BEHAVIOR (buggy):
        - Step 8 outputs "All tests already pass with no warnings!"
        - Step 9 runs but may not output exact ALL_TESTS_PASS token
        - Loop defaults to CONTINUE_CYCLE and starts another cycle
        """
        from pdd.agentic_e2e_fix_orchestrator import run_agentic_e2e_fix_orchestrator

        mock_run = mock_e2e_dependencies["mock_run"]

        cycles_started = []

        def side_effect(*args, **kwargs):
            label = kwargs.get('label', '')

            # Track cycle starts
            if '_step1' in label:
                cycle_num = int(label.split('cycle')[1].split('_')[0])
                cycles_started.append(cycle_num)

            if '_step8' in label:
                # Step 8 detects tests already pass (from inner fix_error_loop)
                return (True, """
Starting fix error loop process.
All tests already pass with no warnings! No fixes needed on this iteration.

Summary Statistics:
Initial state: 0 fails, 0 errors, 0 warnings
Final state: 0 fails, 0 errors, 0 warnings
Best iteration: final
Success: True
""", 0.0, "gpt-4")

            if '_step9' in label:
                # Bug: Step 9 LLM doesn't output exact token
                # This simulates the case where LLM response doesn't contain ALL_TESTS_PASS
                return (True, "Verification complete. Tests are passing.", 0.1, "gpt-4")

            return (True, f"Output for {label}", 0.1, "gpt-4")

        mock_run.side_effect = side_effect

        # Limit to 2 cycles so test doesn't run forever
        default_e2e_args["max_cycles"] = 2

        success, msg, cost, model, files = run_agentic_e2e_fix_orchestrator(**default_e2e_args)

        # The bug: When Step 8 says "All tests already pass", the orchestrator
        # should exit, but instead it continues and may start another cycle.
        #
        # EXPECTED: Only 1 cycle should be started (tests already pass, exit early)
        # ACTUAL (buggy): 2 cycles are started because Step 9 doesn't output exact token
        assert len(cycles_started) == 1, (
            f"BUG #365: Expected only 1 cycle when tests already pass, "
            f"but {len(cycles_started)} cycles were started. "
            f"The orchestrator should detect 'All tests already pass' in Step 8 output "
            f"and exit the loop, instead of relying solely on Step 9's LLM token."
        )

    def test_no_loop_control_token_defaults_to_continue(self, mock_e2e_dependencies, default_e2e_args):
        """Test that missing loop control token in Step 9 defaults to CONTINUE_CYCLE.

        This test documents the current (buggy) behavior where if Step 9's
        output doesn't contain ALL_TESTS_PASS, MAX_CYCLES_REACHED, or CONTINUE_CYCLE,
        the code defaults to CONTINUE_CYCLE and starts another cycle.

        This behavior causes issue #365 when combined with tests that already pass.
        """
        from pdd.agentic_e2e_fix_orchestrator import run_agentic_e2e_fix_orchestrator

        mock_run = mock_e2e_dependencies["mock_run"]

        cycles_completed = [0]

        def side_effect(*args, **kwargs):
            label = kwargs.get('label', '')

            if '_step9' in label:
                cycles_completed[0] += 1
                if cycles_completed[0] >= 2:
                    # Return ALL_TESTS_PASS on second cycle to avoid infinite loop
                    return (True, "ALL_TESTS_PASS", 0.1, "gpt-4")
                # First cycle: No loop control token (triggers the bug)
                return (True, "Tests verified. Everything looks good.", 0.1, "gpt-4")

            return (True, f"Output for {label}", 0.1, "gpt-4")

        mock_run.side_effect = side_effect

        default_e2e_args["max_cycles"] = 3

        success, msg, cost, model, files = run_agentic_e2e_fix_orchestrator(**default_e2e_args)

        # The buggy behavior: When no token is found, another cycle starts
        # Even though tests may be passing, this wastes compute and money
        assert cycles_completed[0] == 2, (
            f"Expected exactly 2 cycles (first has no token, second has ALL_TESTS_PASS), "
            f"but got {cycles_completed[0]}. "
            f"This demonstrates the bug where missing tokens cause unnecessary cycles."
        )

    def test_multiple_unnecessary_cycles_bug_reproduction(self, mock_e2e_dependencies, default_e2e_args):
        """Reproduce exact bug #365: Multiple unnecessary cycles with $0 cost.

        This test reproduces the exact scenario from the bug report:
        1. First cycle: Fixes are applied, tests pass
        2. Second cycle: "All tests already pass", $0 cost, but cycle runs anyway
        3. Third cycle: Same as second

        The bug is that cycles 2 and 3 should not happen at all.
        """
        from pdd.agentic_e2e_fix_orchestrator import run_agentic_e2e_fix_orchestrator

        mock_run = mock_e2e_dependencies["mock_run"]

        cycle_costs = []  # Track cost per cycle
        current_cycle = [0]

        def side_effect(*args, **kwargs):
            label = kwargs.get('label', '')

            if '_step1' in label:
                current_cycle[0] = int(label.split('cycle')[1].split('_')[0])
                if current_cycle[0] > len(cycle_costs):
                    cycle_costs.append(0.0)

            if '_step8' in label:
                if current_cycle[0] == 1:
                    # First cycle: Actual fix work done
                    cycle_costs[current_cycle[0] - 1] += 0.5
                    return (True, "Fixed 3 errors. Tests now pass.", 0.5, "gpt-4")
                else:
                    # Subsequent cycles: Tests already pass, $0 cost
                    return (True, """
All tests already pass with no warnings! No fixes needed on this iteration.
Total cost: $0.000000
""", 0.0, "gpt-4")

            if '_step9' in label:
                if current_cycle[0] >= 3:
                    # Exit on third cycle to prevent infinite loop in test
                    return (True, "ALL_TESTS_PASS", 0.1, "gpt-4")
                # Bug: LLM output doesn't contain exact token
                return (True, "Verified. Tests passing. No issues found.", 0.1, "gpt-4")

            # Other steps cost $0.1 each
            cycle_costs[current_cycle[0] - 1] += 0.1
            return (True, f"Output for {label}", 0.1, "gpt-4")

        mock_run.side_effect = side_effect

        default_e2e_args["max_cycles"] = 3

        success, msg, cost, model, files = run_agentic_e2e_fix_orchestrator(**default_e2e_args)

        # Bug assertion: We should only see 1 cycle (the one that does actual work)
        # but the buggy code runs 3 cycles
        assert len(cycle_costs) == 1, (
            f"BUG #365: Expected only 1 cycle, but {len(cycle_costs)} cycles ran. "
            f"Cycle costs: {cycle_costs}. "
            f"After tests pass in cycle 1, cycles 2+ are unnecessary and waste resources. "
            f"The orchestrator should detect 'All tests already pass' in Step 8 and exit."
        )

    def test_step8_tests_pass_detection_should_set_success_flag(self, mock_e2e_dependencies, default_e2e_args):
        """The orchestrator should detect 'tests already pass' pattern in Step 8.

        EXPECTED FIX: When Step 8 output contains patterns like:
        - "All tests already pass"
        - "No fixes needed"
        - "Success: True" with "0 fails, 0 errors"

        The orchestrator should set success=True and break out of the loop,
        rather than continuing to Step 9 and relying on LLM token output.
        """
        from pdd.agentic_e2e_fix_orchestrator import run_agentic_e2e_fix_orchestrator

        mock_run = mock_e2e_dependencies["mock_run"]

        steps_executed = []

        def side_effect(*args, **kwargs):
            label = kwargs.get('label', '')
            steps_executed.append(label)

            if '_step8' in label:
                # Step 8 clearly indicates all tests pass
                return (True, """
All tests already pass with no warnings! No fixes needed on this iteration.

Summary Statistics:
Initial state: 0 fails, 0 errors, 0 warnings
Final state: 0 fails, 0 errors, 0 warnings
Success: True
Overall improvement: 100.00%
""", 0.0, "gpt-4")

            if '_step9' in label:
                # Step 9 doesn't output exact token (simulating real-world LLM behavior)
                return (True, "Final verification complete.", 0.1, "gpt-4")

            return (True, f"Output for {label}", 0.1, "gpt-4")

        mock_run.side_effect = side_effect

        default_e2e_args["max_cycles"] = 2

        success, msg, cost, model, files = run_agentic_e2e_fix_orchestrator(**default_e2e_args)

        # Count how many cycle1 vs cycle2 steps were executed
        cycle1_steps = [s for s in steps_executed if 'cycle1_' in s]
        cycle2_steps = [s for s in steps_executed if 'cycle2_' in s]

        # EXPECTED: Only cycle 1 steps should execute
        # ACTUAL (buggy): Both cycle 1 and cycle 2 steps execute
        assert len(cycle2_steps) == 0, (
            f"BUG #365: Expected no cycle 2 steps when Step 8 says 'All tests already pass', "
            f"but {len(cycle2_steps)} cycle 2 steps were executed: {cycle2_steps}. "
            f"The orchestrator should detect the 'tests pass' pattern in Step 8 output "
            f"and terminate the loop without requiring Step 9's LLM token."
        )
        assert success is True, f"Expected success=True when all tests pass, got {success}"
