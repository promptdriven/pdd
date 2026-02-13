"""Tests for agentic_e2e_fix_orchestrator prompt formatting and runtime behavior.

These tests verify that all e2e fix workflow prompts can be formatted
with the context variables provided by the orchestrator, without
raising KeyError on undefined placeholders.

Additionally, tests verify the orchestrator's runtime behavior including
early exit conditions (issue #468).
"""
import pytest
from unittest.mock import patch, MagicMock
from pathlib import Path

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


    def test_step9_prompt_formats_without_error(self, base_context):
        """Step 9 template should format successfully with orchestrator context.

        Regression test for issue #357: The "max cycles reached" section of the
        template at lines 126-127 uses single braces {N}/{M} instead of double
        braces {{N}}/{{M}}, causing KeyError: 'N' when formatting.
        """
        # Add all required step outputs (steps 1-8)
        for i in range(1, 9):
            base_context[f"step{i}_output"] = f"Step {i} output"
        base_context["next_cycle"] = 2  # Required for "more cycles needed" section

        template = load_prompt_template("agentic_e2e_fix_step9_verify_all_LLM")
        assert template is not None, "Template should load"

        # This should NOT raise KeyError: 'N'
        # Bug: Lines 126-127 have {N}/{M} instead of {{N}}/{{M}}
        formatted = template.format(**base_context)

        # Verify escaped placeholders remain as literals in output
        assert "{N}" in formatted, "Escaped {{N}} should become {N} literal in output"
        assert "{M}" in formatted, "Escaped {{M}} should become {M} literal in output"
        assert "{K}" in formatted, "Escaped {{K}} should become {K} literal in output"


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


class TestLoopModeNoLogFile:
    """Tests for issue #360: Loop mode prompts should not include log file argument.

    When using --loop mode in pdd fix, all positional args after CODE are treated
    as test files. Including a log file argument causes pytest to fail with
    collection errors because it tries to load the .log file as a test file.

    These tests verify that step 1 and step 8 prompts do NOT include the
    problematic log file pattern when using --loop mode.
    """

    def test_step1_prompt_no_log_file_in_loop_mode(self):
        """Step 1 prompt should not pass log file argument when using --loop.

        Issue #360: The prompt incorrectly instructs LLM to run:
            touch /tmp/pdd_fix_errors_{{dev_unit}}.log
            pdd fix --manual ... /tmp/pdd_fix_errors_{{dev_unit}}.log --loop

        In loop mode, args after CODE are treated as test files, so the log file
        gets passed to pytest, causing collection errors (exit code 4).

        This test fails on buggy code (log file present) and passes when fixed.
        """
        template = load_prompt_template("agentic_e2e_fix_step1_unit_tests_LLM")
        assert template is not None, "Template should load"

        # Check raw template content for the problematic pattern
        # The bug is that log file is passed BEFORE --loop flag
        # Pattern: .log --loop or .log {protect_tests_flag}
        import re
        log_before_loop_pattern = r'\.log\s+--loop'
        log_with_protect_pattern = r'\.log\s+\{protect_tests_flag\}'

        match_before_loop = re.search(log_before_loop_pattern, template)
        match_with_protect = re.search(log_with_protect_pattern, template)

        assert match_before_loop is None and match_with_protect is None, (
            "Step 1 prompt should NOT include log file argument when using --loop mode. "
            "Loop mode treats all positional args after CODE as test files, "
            "causing pytest to fail when it tries to collect from .log files. "
            f"Found problematic pattern in template."
        )

    def test_step8_prompt_no_log_file_in_loop_mode(self):
        """Step 8 prompt should not pass log file argument when using --loop.

        Issue #360: The prompt incorrectly instructs LLM to run:
            touch /tmp/pdd_fix_errors_{{dev_unit}}.log
            pdd fix --manual ... /tmp/pdd_fix_errors_{{dev_unit}}.log --loop

        In loop mode, args after CODE are treated as test files, so the log file
        gets passed to pytest, causing collection errors (exit code 4).

        This test fails on buggy code (log file present) and passes when fixed.
        """
        template = load_prompt_template("agentic_e2e_fix_step8_run_pdd_fix_LLM")
        assert template is not None, "Template should load"

        # Check raw template content for the problematic pattern
        # The bug is that log file is passed BEFORE --loop flag
        import re
        log_before_loop_pattern = r'\.log\s+--loop'
        log_with_protect_pattern = r'\.log\s+\{protect_tests_flag\}'

        match_before_loop = re.search(log_before_loop_pattern, template)
        match_with_protect = re.search(log_with_protect_pattern, template)

        assert match_before_loop is None and match_with_protect is None, (
            "Step 8 prompt should NOT include log file argument when using --loop mode. "
            "Loop mode treats all positional args after CODE as test files, "
            "causing pytest to fail when it tries to collect from .log files. "
            f"Found problematic pattern in template."
        )

    def test_no_touch_log_file_command_for_loop_mode(self):
        """Neither step 1 nor step 8 should create temp log files for loop mode.

        Issue #360: The prompts include:
            touch /tmp/pdd_fix_errors_{{dev_unit}}.log

        This is unnecessary for --loop mode which handles errors internally.
        Creating the file and passing it as an argument causes pytest failures.

        This test verifies the `touch /tmp/pdd_fix_errors` pattern is absent.
        """
        step1_template = load_prompt_template("agentic_e2e_fix_step1_unit_tests_LLM")
        step8_template = load_prompt_template("agentic_e2e_fix_step8_run_pdd_fix_LLM")

        assert step1_template is not None, "Step 1 template should load"
        assert step8_template is not None, "Step 8 template should load"

        # Check for the touch command that creates the problematic log file
        touch_pattern = "touch /tmp/pdd_fix_errors"

        assert touch_pattern not in step1_template, (
            "Step 1 prompt should NOT create temp log file for loop mode. "
            "Loop mode handles errors internally and doesn't need ERROR_FILE."
        )
        assert touch_pattern not in step8_template, (
            "Step 8 prompt should NOT create temp log file for loop mode. "
            "Loop mode handles errors internally and doesn't need ERROR_FILE."
        )


class TestLoopModeLogFileE2E:
    """E2E tests for issue #360: Verify CLI behavior in loop mode.

    The unit tests in TestLoopModeNoLogFile verify that the prompt templates
    do NOT include the problematic log file argument.

    This E2E test class verifies the correct CLI behavior when pdd fix --loop
    is called without a log file argument (the expected usage pattern after
    the prompt fix).

    Note: The original test_loop_mode_with_log_file_causes_pytest_collection_error
    was removed because it explicitly passed a log file to the CLI, which will
    always cause the "bug" regardless of what the prompts say. The bug is in
    the prompt templates (now fixed), not in the CLI behavior. The CLI correctly
    treats all positional args after CODE as test files in loop mode (documented
    in CHANGELOG v0.0.119).
    """

    @pytest.fixture
    def loop_mode_test_files(self, tmp_path):
        """Create minimal files needed to run pdd fix --manual --loop.

        Returns a dict with paths to:
        - prompt_file: A minimal prompt file
        - code_file: A simple code file with a bug
        - test_file: A passing test file
        """
        # Create a minimal prompt file
        prompt_content = """% Language: Python
% Description: Simple calculator

def add(a, b):
    return a + b
"""
        prompt_file = tmp_path / "fix_calculator.prompt"
        prompt_file.write_text(prompt_content)

        # Create a simple code file
        code_content = """def add(a, b):
    return a + b
"""
        code_file = tmp_path / "calculator.py"
        code_file.write_text(code_content)

        # Create a passing test file
        test_content = """import pytest

def test_add():
    from calculator import add
    assert add(1, 2) == 3
"""
        test_file = tmp_path / "test_calculator.py"
        test_file.write_text(test_content)

        return {
            "prompt_file": str(prompt_file),
            "code_file": str(code_file),
            "test_file": str(test_file),
            "tmp_path": tmp_path,
        }

    def test_loop_mode_without_log_file_processes_single_test_file(
        self, loop_mode_test_files, monkeypatch
    ):
        """E2E Test: pdd fix --loop without log file only processes one test file.

        This test verifies the CORRECT behavior: when pdd fix --manual --loop
        is called with just PROMPT CODE TEST (no log file), it should only
        process one test file.

        This test serves as a baseline to ensure the correct usage pattern
        (no log file argument in loop mode) works as expected.
        """
        from click.testing import CliRunner
        from pdd import cli

        files = loop_mode_test_files
        monkeypatch.chdir(files["tmp_path"])
        monkeypatch.setenv("PDD_FORCE_LOCAL", "1")
        monkeypatch.setenv("OPENAI_API_KEY", "fake-key-for-testing")

        runner = CliRunner()

        # Correct command pattern (what the fixed prompts should use):
        # pdd fix --manual PROMPT CODE TEST --loop
        # Note: NO log file argument
        result = runner.invoke(
            cli.cli,
            [
                "--local",
                "--force",
                "fix",
                "--manual",
                "--loop",
                files["prompt_file"],
                files["code_file"],
                files["test_file"],
                # No log file - this is the CORRECT pattern
            ],
            catch_exceptions=False,
        )

        # The command should not show "Processing test file X/2" (only 1 test file)
        # And should not mention collection errors for .log files
        assert "pdd_fix_errors" not in result.output, (
            f"Log file should not appear in output when not passed as argument.\n"
            f"Output: {result.output}"
        )

        # Key check: If processing message appears, it should NOT mention "/2"
        # This verifies that only 1 test file is being processed
        assert "/2" not in result.output or "Processing test file" not in result.output, (
            f"Should only process 1 test file, not 2.\n"
            f"Output: {result.output}"
        )


# ============================================================================
# Issue #468: NOT_A_BUG Early Exit Tests
#
# Bug: When Step 3 returns NOT_A_BUG, the orchestrator should stop the
# workflow immediately. Instead, it continues executing Steps 4-9.
#
# Root cause: The orchestrator only checks for ALL_TESTS_PASS (Step 2)
# and loop control tokens (Step 9). There is no check after Step 3 for
# the NOT_A_BUG token, even though the prompt specification and Step 3
# prompt both define it.
#
# Pattern reference: agentic_bug_orchestrator.py:416-425 has the correct
# pattern (checking for "Feature Request" / "User Error" at Step 2).
# ============================================================================


from pdd.agentic_e2e_fix_orchestrator import run_agentic_e2e_fix_orchestrator


@pytest.fixture
def e2e_fix_mock_dependencies(tmp_path):
    """Mocks external dependencies for the e2e fix orchestrator.

    Mocks:
    - run_agentic_task: LLM task execution
    - load_prompt_template: Prompt loading
    - console: Suppress Rich output during tests
    - load_workflow_state: Returns no saved state (fresh run)
    - save_workflow_state: No-op
    - clear_workflow_state: No-op
    - _get_file_hashes: Returns empty dict (skip git operations)
    - _commit_and_push: No-op (skip git operations)
    """
    with patch("pdd.agentic_e2e_fix_orchestrator.run_agentic_task") as mock_run, \
         patch("pdd.agentic_e2e_fix_orchestrator.load_prompt_template") as mock_load, \
         patch("pdd.agentic_e2e_fix_orchestrator.console") as mock_console, \
         patch("pdd.agentic_e2e_fix_orchestrator.load_workflow_state") as mock_load_state, \
         patch("pdd.agentic_e2e_fix_orchestrator.save_workflow_state") as mock_save_state, \
         patch("pdd.agentic_e2e_fix_orchestrator.clear_workflow_state") as mock_clear_state, \
         patch("pdd.agentic_e2e_fix_orchestrator._get_file_hashes") as mock_hashes, \
         patch("pdd.agentic_e2e_fix_orchestrator._commit_and_push") as mock_commit:

        # Default: successful run, generic output
        mock_run.return_value = (True, "Step output", 0.1, "gpt-4")
        # Default: simple template
        mock_load.return_value = "Prompt for {issue_number}"
        # Default: no saved state (fresh run)
        mock_load_state.return_value = (None, None)
        # Default: save returns no GitHub comment ID
        mock_save_state.return_value = None
        # Default: no file hashes
        mock_hashes.return_value = {}
        # Default: commit succeeds
        mock_commit.return_value = (True, "No changes to commit")

        yield mock_run, mock_load, mock_console


@pytest.fixture
def e2e_fix_default_args(tmp_path):
    """Default arguments for run_agentic_e2e_fix_orchestrator."""
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
        "resume": False,
        "use_github_state": False,
    }


class TestNotABugEarlyExit:
    """Tests for issue #468: NOT_A_BUG should cause early exit after Step 3.

    The e2e fix orchestrator should stop the workflow when the agent
    determines the reported issue is not actually a bug.
    """

    def test_not_a_bug_early_exit_step3(self, e2e_fix_mock_dependencies, e2e_fix_default_args):
        """Primary bug test: NOT_A_BUG in Step 3 output should stop the workflow.

        Issue #468: When Step 3 returns NOT_A_BUG, the orchestrator should
        exit immediately after Step 3, executing only Steps 1-3 (3 calls).

        This test FAILS on the buggy code because the orchestrator has no
        check for NOT_A_BUG after Step 3 — it continues through all 9 steps.
        """
        mock_run, _, _ = e2e_fix_mock_dependencies

        # Step 3 returns NOT_A_BUG classification
        def side_effect(*args, **kwargs):
            label = kwargs.get('label', '')
            if 'step3' in label:
                return (True, "Root cause: NOT_A_BUG - This is expected behavior, not a bug.", 0.1, "gpt-4")
            return (True, f"Output for {label}", 0.1, "gpt-4")

        mock_run.side_effect = side_effect

        success, msg, cost, model, files = run_agentic_e2e_fix_orchestrator(
            **e2e_fix_default_args
        )

        # The orchestrator should have stopped after Step 3
        # Only 3 calls: Step 1, Step 2, Step 3
        assert mock_run.call_count == 3, (
            f"Expected 3 step calls (Steps 1-3) but got {mock_run.call_count}. "
            f"The orchestrator should stop after Step 3 returns NOT_A_BUG. "
            f"Called labels: {[c.kwargs.get('label', '') for c in mock_run.call_args_list]}"
        )

    def test_not_a_bug_with_surrounding_text(self, e2e_fix_mock_dependencies, e2e_fix_default_args):
        """Edge case: NOT_A_BUG token should be detected even in verbose output.

        The agent may embed the NOT_A_BUG token within verbose analysis text.
        The orchestrator should still detect it and stop.
        """
        mock_run, _, _ = e2e_fix_mock_dependencies

        def side_effect(*args, **kwargs):
            label = kwargs.get('label', '')
            if 'step3' in label:
                return (True, (
                    "## Root Cause Analysis\n"
                    "After thorough investigation, I've determined this is user error.\n"
                    "**Status:** NOT_A_BUG\n"
                    "The reported behavior is actually the expected behavior per the docs."
                ), 0.1, "gpt-4")
            return (True, f"Output for {label}", 0.1, "gpt-4")

        mock_run.side_effect = side_effect

        success, msg, cost, model, files = run_agentic_e2e_fix_orchestrator(
            **e2e_fix_default_args
        )

        # Should still detect NOT_A_BUG and stop after 3 steps
        assert mock_run.call_count == 3, (
            f"Expected 3 step calls but got {mock_run.call_count}. "
            f"NOT_A_BUG should be detected even in verbose output."
        )


class TestExistingEarlyExits:
    """Tests for existing early exit conditions that had zero coverage.

    These regression tests ensure the existing ALL_TESTS_PASS early exits
    continue to work correctly.
    """

    def test_all_tests_pass_early_exit_step2(self, e2e_fix_mock_dependencies, e2e_fix_default_args):
        """ALL_TESTS_PASS in Step 2 should exit the workflow successfully.

        This tests the existing early exit at Step 2 (lines 504-509 in
        agentic_e2e_fix_orchestrator.py).
        """
        mock_run, _, _ = e2e_fix_mock_dependencies

        def side_effect(*args, **kwargs):
            label = kwargs.get('label', '')
            if 'step2' in label:
                return (True, "All tests pass. ALL_TESTS_PASS", 0.1, "gpt-4")
            return (True, f"Output for {label}", 0.1, "gpt-4")

        mock_run.side_effect = side_effect

        success, msg, cost, model, files = run_agentic_e2e_fix_orchestrator(
            **e2e_fix_default_args
        )

        assert success is True, f"Should succeed when ALL_TESTS_PASS at Step 2: {msg}"
        assert mock_run.call_count == 2, (
            f"Expected 2 step calls (Steps 1-2) but got {mock_run.call_count}."
        )

    def test_all_tests_pass_step9_exits_loop(self, e2e_fix_mock_dependencies, e2e_fix_default_args):
        """ALL_TESTS_PASS in Step 9 should exit the loop successfully.

        This tests the existing early exit at Step 9 (lines 513-517 in
        agentic_e2e_fix_orchestrator.py).
        """
        mock_run, _, _ = e2e_fix_mock_dependencies

        def side_effect(*args, **kwargs):
            label = kwargs.get('label', '')
            if 'step9' in label:
                return (True, "Verification complete. ALL_TESTS_PASS", 0.1, "gpt-4")
            return (True, f"Output for {label}", 0.1, "gpt-4")

        mock_run.side_effect = side_effect

        success, msg, cost, model, files = run_agentic_e2e_fix_orchestrator(
            **e2e_fix_default_args
        )

        assert success is True, f"Should succeed when ALL_TESTS_PASS at Step 9: {msg}"
        assert mock_run.call_count == 9, (
            f"Expected 9 step calls (all steps in one cycle) but got {mock_run.call_count}."
        )

    def test_happy_path_all_9_steps_execute(self, e2e_fix_mock_dependencies, e2e_fix_default_args):
        """Regression test: Normal flow should execute all 9 steps per cycle.

        When no early exit tokens are present, the orchestrator should run
        all 9 steps. This ensures the NOT_A_BUG fix doesn't break the
        normal workflow.
        """
        mock_run, _, _ = e2e_fix_mock_dependencies
        e2e_fix_default_args["max_cycles"] = 1

        # No early exit tokens in any step output
        def side_effect(*args, **kwargs):
            label = kwargs.get('label', '')
            if 'step9' in label:
                return (True, "Some tests still failing. CONTINUE_CYCLE", 0.1, "gpt-4")
            return (True, f"Output for {label}", 0.1, "gpt-4")

        mock_run.side_effect = side_effect

        success, msg, cost, model, files = run_agentic_e2e_fix_orchestrator(
            **e2e_fix_default_args
        )

        # All 9 steps should execute
        assert mock_run.call_count == 9, (
            f"Expected 9 step calls but got {mock_run.call_count}. "
            f"Normal flow should execute all 9 steps."
        )


class TestPromptNotABugCategory:
    """Prompt verification tests: Ensure NOT_A_BUG exists in prompt templates.

    These tests prevent prompt regression — if someone removes the NOT_A_BUG
    category from the prompts, these tests will catch it.
    """

    def test_step3_prompt_has_not_a_bug_category(self):
        """Step 3 prompt must include NOT_A_BUG as a root cause category.

        Without NOT_A_BUG in the prompt, the agent has no structured way
        to signal that the issue isn't a bug.
        """
        template = load_prompt_template("agentic_e2e_fix_step3_root_cause_LLM")
        assert template is not None, "Step 3 template should load"
        assert "NOT_A_BUG" in template, (
            "Step 3 prompt must include NOT_A_BUG as a root cause category. "
            "Without it, the agent cannot signal that the issue is not a bug."
        )

    def test_orchestrator_prompt_has_not_a_bug_in_loop_control(self):
        """Orchestrator prompt must document NOT_A_BUG as a loop control token.

        The orchestrator prompt specification should document NOT_A_BUG
        alongside ALL_TESTS_PASS and CONTINUE_CYCLE.
        """
        template = load_prompt_template("agentic_e2e_fix_orchestrator_python")
        assert template is not None, "Orchestrator prompt should load"
        assert "NOT_A_BUG" in template, (
            "Orchestrator prompt must document NOT_A_BUG as a loop control token. "
            "This ensures the generated code includes the NOT_A_BUG check."
        )
