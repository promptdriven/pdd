"""Tests for agentic_e2e_fix_orchestrator prompt formatting and runtime behavior.

These tests verify that all e2e fix workflow prompts can be formatted
with the context variables provided by the orchestrator, without
raising KeyError on undefined placeholders.

Additionally, tests verify the orchestrator's runtime behavior including
early exit conditions (issue #468).
"""
import re
from typing import Dict, Optional

import pytest
from unittest.mock import patch, MagicMock
from pathlib import Path

from pdd.load_prompt_template import load_prompt_template
from pdd.agentic_e2e_fix_orchestrator import _extract_test_files, _verify_tests_independently


def _strip_pdd_metadata(template: str) -> str:
    """Strip <pdd-reason> and <pdd-interface> metadata blocks from a prompt template.

    These blocks contain JSON with bare curly braces that break str.format().
    The production orchestrator uses preprocess() + manual substitution which
    handles this, but the formatting tests call .format() directly.
    """
    template = re.sub(r'<pdd-reason>.*?</pdd-reason>', '', template, flags=re.DOTALL)
    template = re.sub(r'<pdd-interface>.*?</pdd-interface>', '', template, flags=re.DOTALL)
    return template


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
        formatted = _strip_pdd_metadata(template).format(**base_context)
        assert "test runner" in formatted or "pytest" in formatted
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
        formatted = _strip_pdd_metadata(template).format(**base_context)
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
        formatted = _strip_pdd_metadata(template).format(**base_context)
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
        formatted = _strip_pdd_metadata(template).format(**base_context)
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
        formatted = _strip_pdd_metadata(template).format(**base_context)
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
        formatted = _strip_pdd_metadata(template).format(**base_context)
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
        formatted = _strip_pdd_metadata(template).format(**base_context)

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
         patch("pdd.agentic_e2e_fix_orchestrator._commit_and_push") as mock_commit, \
         patch("pdd.agentic_e2e_fix_orchestrator._check_e2e_environment") as mock_check_e2e:

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
        # Default: E2E environment available
        mock_check_e2e.return_value = (True, "")

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

    @patch("pdd.agentic_e2e_fix_orchestrator._verify_tests_independently")
    @patch("pdd.agentic_e2e_fix_orchestrator._extract_test_files")
    def test_all_tests_pass_early_exit_step2(self, mock_extract, mock_verify, e2e_fix_mock_dependencies, e2e_fix_default_args):
        """ALL_TESTS_PASS in Step 2 should exit the workflow successfully.

        This tests the existing early exit at Step 2 (lines 504-509 in
        agentic_e2e_fix_orchestrator.py).
        """
        mock_run, _, _ = e2e_fix_mock_dependencies

        # Mock independent verification to confirm tests pass
        mock_extract.return_value = ["tests/test_foo.py"]
        mock_verify.return_value = (True, "1 passed")

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

    @patch("pdd.agentic_e2e_fix_orchestrator._verify_tests_independently")
    @patch("pdd.agentic_e2e_fix_orchestrator._extract_test_files")
    def test_all_tests_pass_step9_exits_loop(self, mock_extract, mock_verify, e2e_fix_mock_dependencies, e2e_fix_default_args):
        """ALL_TESTS_PASS in Step 9 should exit the loop successfully.

        This tests the existing early exit at Step 9 (lines 513-517 in
        agentic_e2e_fix_orchestrator.py).
        """
        mock_run, _, _ = e2e_fix_mock_dependencies

        # Mock independent verification to confirm tests pass
        mock_extract.return_value = ["tests/test_foo.py"]
        mock_verify.return_value = (True, "1 passed")

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
        prompt_path = Path(__file__).parent.parent / "prompts" / "agentic_e2e_fix_step3_root_cause_LLM.prompt"
        template = prompt_path.read_text()
        assert "NOT_A_BUG" in template, (
            "Step 3 prompt must include NOT_A_BUG as a root cause category. "
            "Without it, the agent cannot signal that the issue is not a bug."
        )

    def test_orchestrator_prompt_has_not_a_bug_in_loop_control(self):
        """Orchestrator prompt must document NOT_A_BUG as a loop control token.

        The orchestrator prompt specification should document NOT_A_BUG
        alongside ALL_TESTS_PASS and CONTINUE_CYCLE.
        """
        prompt_path = Path(__file__).parent.parent / "prompts" / "agentic_e2e_fix_orchestrator_python.prompt"
        if not prompt_path.exists():
            pytest.skip("Prompt file not available in public repo")
        template = prompt_path.read_text()
        assert "NOT_A_BUG" in template, (
            "Orchestrator prompt must document NOT_A_BUG as a loop control token. "
            "This ensures the generated code includes the NOT_A_BUG check."
        )


class TestDetectChangedFiles:
    """Tests for issue #355: Summary should report actual file changes.

    When pdd fix exits early (e.g. ALL_TESTS_PASS at Step 2), the summary
    reported empty "Files changed:" because it relied on LLM output parsing
    (FILES_MODIFIED/FILES_CREATED markers) rather than actual git state.

    The fix uses hash-based file change detection (_detect_changed_files)
    to accurately report files modified during the workflow.
    """

    def test_detect_changed_files_finds_modified_file(self, tmp_path):
        """_detect_changed_files should detect files modified after snapshot."""
        from pdd.agentic_e2e_fix_orchestrator import _detect_changed_files, _get_file_hashes
        import subprocess

        # Set up a git repo
        subprocess.run(["git", "init"], cwd=tmp_path, capture_output=True, check=True)
        subprocess.run(["git", "config", "user.email", "test@test.com"], cwd=tmp_path, capture_output=True, check=True)
        subprocess.run(["git", "config", "user.name", "Test"], cwd=tmp_path, capture_output=True, check=True)

        # Create and commit a file
        test_file = tmp_path / "module.py"
        test_file.write_text("x = 1\n")
        subprocess.run(["git", "add", "."], cwd=tmp_path, capture_output=True, check=True)
        subprocess.run(["git", "commit", "-m", "init"], cwd=tmp_path, capture_output=True, check=True)

        # Take snapshot (simulating workflow start)
        initial_hashes = _get_file_hashes(tmp_path)

        # Modify the file (simulating what pdd fix does)
        test_file.write_text("x = 2\n")

        # _detect_changed_files should find the modification
        changed = _detect_changed_files(tmp_path, initial_hashes)
        assert "module.py" in changed, (
            f"Should detect modified file. Got: {changed}"
        )

    def test_detect_changed_files_finds_new_file(self, tmp_path):
        """_detect_changed_files should detect files created after snapshot."""
        from pdd.agentic_e2e_fix_orchestrator import _detect_changed_files, _get_file_hashes
        import subprocess

        # Set up a git repo
        subprocess.run(["git", "init"], cwd=tmp_path, capture_output=True, check=True)
        subprocess.run(["git", "config", "user.email", "test@test.com"], cwd=tmp_path, capture_output=True, check=True)
        subprocess.run(["git", "config", "user.name", "Test"], cwd=tmp_path, capture_output=True, check=True)

        # Create and commit a file
        existing = tmp_path / "existing.py"
        existing.write_text("x = 1\n")
        subprocess.run(["git", "add", "."], cwd=tmp_path, capture_output=True, check=True)
        subprocess.run(["git", "commit", "-m", "init"], cwd=tmp_path, capture_output=True, check=True)

        # Take snapshot
        initial_hashes = _get_file_hashes(tmp_path)

        # Create a new file (simulating workflow creating a new file)
        new_file = tmp_path / "new_module.py"
        new_file.write_text("y = 2\n")

        # _detect_changed_files should find the new file
        changed = _detect_changed_files(tmp_path, initial_hashes)
        assert "new_module.py" in changed, (
            f"Should detect newly created file. Got: {changed}"
        )

    def test_detect_changed_files_ignores_unchanged(self, tmp_path):
        """_detect_changed_files should not report unchanged files."""
        from pdd.agentic_e2e_fix_orchestrator import _detect_changed_files, _get_file_hashes
        import subprocess

        # Set up a git repo with a modified-but-pre-existing file
        subprocess.run(["git", "init"], cwd=tmp_path, capture_output=True, check=True)
        subprocess.run(["git", "config", "user.email", "test@test.com"], cwd=tmp_path, capture_output=True, check=True)
        subprocess.run(["git", "config", "user.name", "Test"], cwd=tmp_path, capture_output=True, check=True)

        test_file = tmp_path / "module.py"
        test_file.write_text("x = 1\n")
        subprocess.run(["git", "add", "."], cwd=tmp_path, capture_output=True, check=True)
        subprocess.run(["git", "commit", "-m", "init"], cwd=tmp_path, capture_output=True, check=True)

        # Take snapshot AFTER file already exists and is committed
        initial_hashes = _get_file_hashes(tmp_path)

        # Don't modify anything
        changed = _detect_changed_files(tmp_path, initial_hashes)
        assert changed == [], (
            f"Should report no changes when nothing changed. Got: {changed}"
        )

    def test_parse_changed_files_returns_empty_without_markers(self):
        """_parse_changed_files returns empty list when LLM output has no markers.

        This demonstrates the root cause of issue #355: Steps 1 and 2 don't
        output FILES_MODIFIED/FILES_CREATED markers, so the parser finds nothing.
        """
        from pdd.agentic_e2e_fix_orchestrator import _parse_changed_files

        # Simulated Step 2 output with ALL_TESTS_PASS but no file markers
        step2_output = """Running e2e tests...
pytest tests/ -v
ALL_TESTS_PASS
All 42 tests passed."""

        result = _parse_changed_files(step2_output)
        assert result == [], (
            "LLM output without FILES_MODIFIED markers should return empty list"
        )


# ============================================================================
# Issue #467: Blind Resume — validate cached state on load
# ============================================================================


class TestIssue467BlindResume:
    """Tests for Issue #467 blind resume fix in the e2e fix orchestrator."""

    @pytest.fixture
    def mock_deps(self, tmp_path):
        """Mock dependencies for e2e fix orchestrator runtime tests."""
        with patch("pdd.agentic_e2e_fix_orchestrator.run_agentic_task") as mock_run, \
             patch("pdd.agentic_e2e_fix_orchestrator.load_workflow_state") as mock_load, \
             patch("pdd.agentic_e2e_fix_orchestrator.save_workflow_state") as mock_save, \
             patch("pdd.agentic_e2e_fix_orchestrator.clear_workflow_state") as mock_clear, \
             patch("pdd.agentic_e2e_fix_orchestrator.load_prompt_template") as mock_template, \
             patch("pdd.agentic_e2e_fix_orchestrator.console") as mock_console, \
             patch("pdd.agentic_e2e_fix_orchestrator._get_file_hashes") as mock_hashes, \
             patch("pdd.agentic_e2e_fix_orchestrator._commit_and_push") as mock_commit:
            mock_run.return_value = (True, "Step Output", 0.1, "gpt-4")
            mock_load.return_value = (None, None)
            mock_save.return_value = None
            mock_template.return_value = "Prompt for {issue_number}"
            mock_hashes.return_value = {}
            mock_commit.return_value = (True, "No changes")

            yield {
                "run": mock_run,
                "load": mock_load,
                "save": mock_save,
                "clear": mock_clear,
                "template": mock_template,
                "console": mock_console,
            }

    def test_resume_from_all_failed_state_reruns_from_step_1(self, mock_deps, tmp_path):
        """
        Issue #467: When resuming from a state where all steps failed,
        the workflow should re-run from step 1, not skip past them.
        """
        from pdd.agentic_e2e_fix_orchestrator import run_agentic_e2e_fix_orchestrator

        corrupted_state = {
            "workflow": "e2e_fix",
            "issue_number": 1,
            "current_cycle": 1,
            "last_completed_step": 5,
            "step_outputs": {
                "1": "FAILED: All agent providers failed",
                "2": "FAILED: All agent providers failed",
                "3": "FAILED: All agent providers failed",
                "4": "FAILED: All agent providers failed",
                "5": "FAILED: All agent providers failed",
            },
            "total_cost": 0.0,
            "model_used": "unknown",
            "changed_files": [],
            "dev_unit_states": {},
        }
        mock_deps["load"].return_value = (corrupted_state, None)

        executed_labels = []

        def track_run(*args, **kwargs):
            label = kwargs.get("label", "")
            executed_labels.append(label)
            if "step2" in label:
                return (True, "ALL_TESTS_PASS", 0.1, "gpt-4")
            return (True, "Step Output", 0.1, "gpt-4")

        mock_deps["run"].side_effect = track_run

        run_agentic_e2e_fix_orchestrator(
            issue_url="http://github.com/o/r/issues/1",
            issue_content="E2E test failure",
            repo_owner="owner",
            repo_name="repo",
            issue_number=1,
            issue_author="user",
            issue_title="E2E Fix",
            cwd=tmp_path,
            quiet=True,
            max_cycles=1,
            resume=True,
            use_github_state=False,
        )

        assert any("step1" in l for l in executed_labels), (
            f"Step 1 should be re-executed when its cached output is FAILED, "
            f"but executed steps were: {executed_labels}. "
            f"This is the 'blind resume' bug from issue #467."
        )

    def test_resume_from_partial_failure_reruns_failed_steps(self, mock_deps, tmp_path):
        """
        Issue #467: When steps 1-3 cached OK but 4-5 FAILED,
        resume should re-run from step 4.
        """
        from pdd.agentic_e2e_fix_orchestrator import run_agentic_e2e_fix_orchestrator

        corrupted_state = {
            "workflow": "e2e_fix",
            "issue_number": 1,
            "current_cycle": 1,
            "last_completed_step": 5,
            "step_outputs": {
                "1": "Tests ran successfully",
                "2": "Some tests failing",
                "3": "Root cause identified",
                "4": "FAILED: All agent providers failed",
                "5": "FAILED: All agent providers failed",
            },
            "total_cost": 0.3,
            "model_used": "gpt-4",
            "changed_files": [],
            "dev_unit_states": {},
        }
        mock_deps["load"].return_value = (corrupted_state, None)

        executed_labels = []

        def track_run(*args, **kwargs):
            label = kwargs.get("label", "")
            executed_labels.append(label)
            if "step9" in label:
                return (True, "ALL_TESTS_PASS", 0.1, "gpt-4")
            return (True, "Step Output", 0.1, "gpt-4")

        mock_deps["run"].side_effect = track_run

        run_agentic_e2e_fix_orchestrator(
            issue_url="http://github.com/o/r/issues/1",
            issue_content="E2E test failure",
            repo_owner="owner",
            repo_name="repo",
            issue_number=1,
            issue_author="user",
            issue_title="E2E Fix",
            cwd=tmp_path,
            quiet=True,
            max_cycles=1,
            resume=True,
            use_github_state=False,
        )

        # Steps 1-3 should be skipped
        assert not any("step1" in l for l in executed_labels), "Step 1 succeeded and should not be re-run"
        assert not any("step2" in l for l in executed_labels), "Step 2 succeeded and should not be re-run"
        assert not any("step3" in l for l in executed_labels), "Step 3 succeeded and should not be re-run"
        # Step 4 should be re-run
        assert any("step4" in l for l in executed_labels), (
            f"Step 4 should be re-executed because its cached output is FAILED, "
            f"but executed steps were: {executed_labels}."
        )


# ============================================================================
# Issue #545: _commit_and_push with tainted hash snapshot (resume scenario)
# ============================================================================


class TestIssue545CommitAndPushWithTaintedHashes:
    """Tests for issue #545: _commit_and_push falls back to git diff when
    hash snapshot is tainted (captured after pre-existing modifications).

    On a resumed run:
    - Prior run wrote code changes to disk but commit failed/timed out.
    - New run starts: initial_file_hashes = _get_file_hashes(cwd) is called
      AFTER the prior run's modifications already exist on disk.
    - Hash snapshot is "tainted" — it already reflects the modifications.
    - Hash delta is zero -> files_to_commit is empty.
    - Buggy code returns "No changes to commit" without checking git diff.
    - Fix: fall back to _get_modified_and_untracked() when hash delta is zero.
    """

    @staticmethod
    def _init_git_repo_with_remote(tmp_path):
        """Helper: creates a git repo cloned from a bare remote for push testing."""
        import subprocess

        bare = tmp_path / "bare.git"
        worktree = tmp_path / "worktree"

        subprocess.run(["git", "init", "--bare", str(bare)],
                       check=True, capture_output=True)
        subprocess.run(["git", "clone", str(bare), str(worktree)],
                       check=True, capture_output=True)
        subprocess.run(["git", "config", "user.email", "test@test.com"],
                       cwd=worktree, check=True, capture_output=True)
        subprocess.run(["git", "config", "user.name", "Test"],
                       cwd=worktree, check=True, capture_output=True)

        module = worktree / "module.py"
        module.write_text("x = 1\n")
        subprocess.run(["git", "add", "."],
                       cwd=worktree, check=True, capture_output=True)
        subprocess.run(["git", "commit", "-m", "init"],
                       cwd=worktree, check=True, capture_output=True)

        branch = subprocess.run(
            ["git", "rev-parse", "--abbrev-ref", "HEAD"],
            cwd=worktree, capture_output=True, text=True, check=True
        ).stdout.strip()
        subprocess.run(["git", "push", "-u", "origin", branch],
                       cwd=worktree, check=True, capture_output=True)

        return worktree, module

    def test_commit_and_push_falls_back_to_git_diff_when_hashes_match(self, tmp_path):
        """Primary bug test: fails on buggy code because hash delta is zero
        but git diff shows the file IS modified and uncommitted.

        Simulates a resume scenario where:
        1. Prior run modified module.py on disk but commit failed
        2. New run captures initial_file_hashes AFTER modification exists
        3. Hash delta is zero (tainted snapshot matches current state)
        4. _commit_and_push should fall back to _get_modified_and_untracked()
           to detect the orphaned unstaged change
        """
        from pdd.agentic_e2e_fix_orchestrator import _commit_and_push, _get_file_hashes
        import subprocess

        worktree, module = self._init_git_repo_with_remote(tmp_path)

        # Simulate prior run's modification (exists BEFORE hash snapshot)
        module.write_text("x = 2  # fixed by prior run\n")

        # Capture "initial" hashes AFTER modification — tainted snapshot
        tainted_hashes = _get_file_hashes(worktree)

        # Call _commit_and_push with tainted hashes
        success, message = _commit_and_push(
            cwd=worktree, issue_number=545,
            issue_title="Fix unstaged changes",
            repo_owner="owner", repo_name="repo",
            initial_file_hashes=tainted_hashes, quiet=True
        )

        # BUG: On buggy code, message is "No changes to commit"
        # FIX: Should detect unstaged change via _get_modified_and_untracked()
        assert "No changes to commit" not in message, (
            f"Issue #545: When initial_file_hashes was captured AFTER "
            f"pre-existing modifications (resume scenario where prior run wrote "
            f"files but commit failed), _commit_and_push must fall back to "
            f"_get_modified_and_untracked() to detect uncommitted changes "
            f"instead of returning 'No changes to commit'. Got: '{message}'"
        )

        # Verify the file was actually committed
        diff_result = subprocess.run(
            ["git", "diff", "--name-only", "HEAD"],
            cwd=worktree, capture_output=True, text=True
        )
        assert diff_result.stdout.strip() == "", (
            f"Issue #545: Pre-existing modification should have been committed. "
            f"Still uncommitted: {diff_result.stdout.strip()}"
        )

    def test_commit_and_push_no_changes_when_nothing_modified(self, tmp_path):
        """Regression guard: 'No changes to commit' preserved when nothing changed.

        Ensures the fix doesn't introduce false positives — when there are truly
        no changes (no hash delta AND no git diff), the function should still
        return "No changes to commit".
        """
        from pdd.agentic_e2e_fix_orchestrator import _commit_and_push, _get_file_hashes
        import subprocess

        worktree, module = self._init_git_repo_with_remote(tmp_path)

        # No modifications — clean worktree
        initial_hashes = _get_file_hashes(worktree)

        success, message = _commit_and_push(
            cwd=worktree, issue_number=545,
            issue_title="Fix unstaged changes",
            repo_owner="owner", repo_name="repo",
            initial_file_hashes=initial_hashes, quiet=True
        )

        assert success is True
        assert "No changes to commit" in message, (
            f"When nothing is modified, should return 'No changes to commit'. "
            f"Got: '{message}'"
        )

    def test_commit_and_push_with_hash_changes_still_commits(self, tmp_path):
        """Regression: normal hash-comparison path still works for fresh runs.

        On a fresh run, initial_file_hashes is a clean snapshot (empty, no
        unstaged files). When files are modified AFTER the snapshot, the hash
        comparison detects real deltas and commits normally.
        """
        from pdd.agentic_e2e_fix_orchestrator import _commit_and_push, _get_file_hashes
        import subprocess

        worktree, module = self._init_git_repo_with_remote(tmp_path)

        # Take snapshot BEFORE modification (clean baseline — fresh run)
        initial_hashes = _get_file_hashes(worktree)

        # Modify file AFTER snapshot (simulating workflow modification)
        module.write_text("x = 2  # fixed during workflow\n")

        success, message = _commit_and_push(
            cwd=worktree, issue_number=545,
            issue_title="Fix unstaged changes",
            repo_owner="owner", repo_name="repo",
            initial_file_hashes=initial_hashes, quiet=True
        )

        assert success is True
        assert "Committed and pushed" in message, (
            f"Normal hash-comparison path should detect and commit the change. "
            f"Got: '{message}'"
        )

        # Verify the file was committed (no remaining unstaged changes)
        diff_result = subprocess.run(
            ["git", "diff", "--name-only", "HEAD"],
            cwd=worktree, capture_output=True, text=True
        )
        assert diff_result.stdout.strip() == "", (
            f"File should be committed. Still uncommitted: {diff_result.stdout.strip()}"
        )

    def test_orchestrator_resume_with_pretainted_hashes_commits_changes(self, tmp_path):
        """Integration: resumed orchestrator detects and commits pre-existing
        unstaged modifications when ALL_TESTS_PASS at Step 2.

        This test does NOT mock _get_file_hashes or _commit_and_push — they
        run against a real git repo. Only the LLM (run_agentic_task) and
        state persistence are mocked.
        """
        from pdd.agentic_e2e_fix_orchestrator import run_agentic_e2e_fix_orchestrator
        import subprocess

        # Set up a real git repo with remote
        worktree, module = self._init_git_repo_with_remote(tmp_path)

        # Simulate prior run's orphaned modification
        module.write_text("x = 2  # fixed by prior interrupted run\n")

        def step_side_effect(*args, **kwargs):
            label = kwargs.get("label", "")
            if "step2" in label:
                return (True, "ALL_TESTS_PASS", 0.1, "gpt-4")
            return (True, f"Output for {label}", 0.1, "gpt-4")

        with patch("pdd.agentic_e2e_fix_orchestrator.run_agentic_task") as mock_run, \
             patch("pdd.agentic_e2e_fix_orchestrator.load_workflow_state") as mock_load, \
             patch("pdd.agentic_e2e_fix_orchestrator.save_workflow_state") as mock_save, \
             patch("pdd.agentic_e2e_fix_orchestrator.clear_workflow_state") as mock_clear, \
             patch("pdd.agentic_e2e_fix_orchestrator.load_prompt_template") as mock_template, \
             patch("pdd.agentic_e2e_fix_orchestrator._check_e2e_environment", return_value=(True, "")), \
             patch("pdd.agentic_e2e_fix_orchestrator.console"):

            mock_run.side_effect = step_side_effect
            mock_load.return_value = (None, None)
            mock_save.return_value = None
            mock_template.return_value = "Prompt for {issue_number}"

            success, message, cost, model, files = run_agentic_e2e_fix_orchestrator(
                issue_url="http://github.com/owner/repo/issues/545",
                issue_content="Bug: pdd fix exits 'no changes to commit'",
                repo_owner="owner", repo_name="repo",
                issue_number=545, issue_author="user",
                issue_title="Fix unstaged changes on resume",
                cwd=worktree, quiet=True, max_cycles=1,
                resume=False, use_github_state=False,
            )

        assert success is True

        # Assert on REAL git state — the orphaned file must be committed
        diff_after = subprocess.run(
            ["git", "diff", "--name-only", "HEAD"],
            cwd=worktree, capture_output=True, text=True
        )
        assert diff_after.stdout.strip() == "", (
            f"Issue #545: On resume with pre-existing unstaged modifications, "
            f"_commit_and_push must detect and commit those changes. "
            f"Still uncommitted: {diff_after.stdout.strip()}"
        )


# ============================================================================
# Issue #629: PDD_GH_TOKEN_FILE push retry on auth failure
# ============================================================================


class TestPushWithRetryTokenFile:
    """Tests for _push_with_retry and _commit_and_push token file retry behavior.

    When git push fails with an auth error and PDD_GH_TOKEN_FILE is set,
    the code should read the token, temporarily swap the remote URL to use
    x-access-token auth, retry the push, and restore the original URL.
    """

    def test_push_with_retry_succeeds_on_first_try(self, tmp_path):
        """When push succeeds on first try, no token retry is needed."""
        from pdd.agentic_e2e_fix_orchestrator import _push_with_retry

        with patch("pdd.agentic_e2e_fix_orchestrator.subprocess.run") as mock_run:
            mock_run.return_value = type("Result", (), {"returncode": 0, "stdout": "", "stderr": ""})()

            success, err = _push_with_retry(tmp_path, "owner", "repo")

        assert success is True
        assert err == ""
        assert mock_run.call_count == 1

    def test_push_with_retry_non_auth_failure_no_retry(self, tmp_path):
        """When push fails with non-auth error, no retry is attempted."""
        from pdd.agentic_e2e_fix_orchestrator import _push_with_retry

        with patch("pdd.agentic_e2e_fix_orchestrator.subprocess.run") as mock_run:
            mock_run.return_value = type("Result", (), {
                "returncode": 1, "stdout": "", "stderr": "fatal: remote hung up unexpectedly"
            })()

            success, err = _push_with_retry(tmp_path, "owner", "repo")

        assert success is False
        assert "remote hung up" in err
        assert mock_run.call_count == 1

    def test_push_with_retry_auth_failure_uses_token_file(self, tmp_path, monkeypatch):
        """When push fails with auth error and PDD_GH_TOKEN_FILE exists, retry with token."""
        from pdd.agentic_e2e_fix_orchestrator import _push_with_retry

        # Create token file
        token_file = tmp_path / "gh_token"
        token_file.write_text("ghp_test_token_123\n")
        monkeypatch.setenv("PDD_GH_TOKEN_FILE", str(token_file))

        call_count = 0

        def mock_run_side_effect(cmd, **kwargs):
            nonlocal call_count
            call_count += 1
            result = type("Result", (), {"returncode": 0, "stdout": "", "stderr": ""})()

            if cmd == ["git", "push", "-u", "origin", "HEAD"] and call_count == 1:
                # First push fails with auth error
                result.returncode = 1
                result.stderr = "fatal: Authentication failed for 'https://github.com/owner/repo.git'"
            elif cmd[0:3] == ["git", "remote", "get-url"]:
                result.stdout = "https://github.com/owner/repo.git"
            elif cmd[0:3] == ["git", "remote", "set-url"]:
                pass  # No-op
            elif cmd == ["git", "push", "-u", "origin", "HEAD"] and call_count > 1:
                pass  # Second push succeeds

            return result

        with patch("pdd.agentic_e2e_fix_orchestrator.subprocess.run", side_effect=mock_run_side_effect):
            success, err = _push_with_retry(tmp_path, "owner", "repo")

        assert success is True

    def test_push_with_retry_auth_failure_no_token_file(self, tmp_path, monkeypatch):
        """When push fails with auth error but no PDD_GH_TOKEN_FILE, return failure."""
        from pdd.agentic_e2e_fix_orchestrator import _push_with_retry

        monkeypatch.delenv("PDD_GH_TOKEN_FILE", raising=False)

        with patch("pdd.agentic_e2e_fix_orchestrator.subprocess.run") as mock_run:
            mock_run.return_value = type("Result", (), {
                "returncode": 1, "stdout": "", "stderr": "fatal: Authentication failed"
            })()

            success, err = _push_with_retry(tmp_path, "owner", "repo")

        assert success is False
        assert "Authentication failed" in err

    def test_push_with_retry_auth_failure_empty_token_file(self, tmp_path, monkeypatch):
        """When push fails with auth error and token file is empty, return failure."""
        from pdd.agentic_e2e_fix_orchestrator import _push_with_retry

        token_file = tmp_path / "gh_token"
        token_file.write_text("  \n")
        monkeypatch.setenv("PDD_GH_TOKEN_FILE", str(token_file))

        with patch("pdd.agentic_e2e_fix_orchestrator.subprocess.run") as mock_run:
            mock_run.return_value = type("Result", (), {
                "returncode": 1, "stdout": "", "stderr": "fatal: Authentication failed"
            })()

            success, err = _push_with_retry(tmp_path, "owner", "repo")

        assert success is False

    def test_push_with_retry_restores_original_url(self, tmp_path, monkeypatch):
        """After token retry (success or fail), original remote URL must be restored."""
        from pdd.agentic_e2e_fix_orchestrator import _push_with_retry

        token_file = tmp_path / "gh_token"
        token_file.write_text("ghp_test_token_123")
        monkeypatch.setenv("PDD_GH_TOKEN_FILE", str(token_file))

        set_url_calls = []

        def mock_run_side_effect(cmd, **kwargs):
            result = type("Result", (), {"returncode": 0, "stdout": "", "stderr": ""})()

            if cmd == ["git", "push", "-u", "origin", "HEAD"]:
                if not set_url_calls:
                    # First push fails
                    result.returncode = 1
                    result.stderr = "HTTP 401"
                # Retry push succeeds
            elif cmd[0:3] == ["git", "remote", "get-url"]:
                result.stdout = "https://github.com/owner/repo.git"
            elif cmd[0:3] == ["git", "remote", "set-url"]:
                set_url_calls.append(cmd[4])  # cmd is ["git", "remote", "set-url", "origin", URL]

            return result

        with patch("pdd.agentic_e2e_fix_orchestrator.subprocess.run", side_effect=mock_run_side_effect):
            _push_with_retry(tmp_path, "owner", "repo")

        # Should have 2 set-url calls: token URL, then restore original
        assert len(set_url_calls) == 2, f"Expected 2 set-url calls, got {len(set_url_calls)}: {set_url_calls}"
        assert "x-access-token" in set_url_calls[0], "First set-url should use token"
        assert set_url_calls[1] == "https://github.com/owner/repo.git", "Second set-url should restore original"

    def test_push_with_retry_detects_http_basic_access_denied(self, tmp_path, monkeypatch):
        """Auth error 'HTTP Basic: Access denied' should trigger token retry."""
        from pdd.agentic_e2e_fix_orchestrator import _push_with_retry

        token_file = tmp_path / "gh_token"
        token_file.write_text("ghp_test_token_123")
        monkeypatch.setenv("PDD_GH_TOKEN_FILE", str(token_file))

        call_count = 0

        def mock_run_side_effect(cmd, **kwargs):
            nonlocal call_count
            call_count += 1
            result = type("Result", (), {"returncode": 0, "stdout": "", "stderr": ""})()

            if cmd == ["git", "push", "-u", "origin", "HEAD"] and call_count == 1:
                result.returncode = 1
                result.stderr = "remote: HTTP Basic: Access denied"
            elif cmd[0:3] == ["git", "remote", "get-url"]:
                result.stdout = "https://github.com/owner/repo.git"

            return result

        with patch("pdd.agentic_e2e_fix_orchestrator.subprocess.run", side_effect=mock_run_side_effect):
            success, err = _push_with_retry(tmp_path, "owner", "repo")

        assert success is True

    def test_commit_and_push_passes_repo_params_to_push(self, tmp_path):
        """_commit_and_push should pass repo_owner/repo_name through to push logic."""
        from pdd.agentic_e2e_fix_orchestrator import _commit_and_push

        with patch("pdd.agentic_e2e_fix_orchestrator._get_file_hashes") as mock_hashes, \
             patch("pdd.agentic_e2e_fix_orchestrator._push_with_retry") as mock_push, \
             patch("pdd.agentic_e2e_fix_orchestrator.subprocess.run") as mock_run:

            # Simulate a file that changed
            mock_hashes.return_value = {"new_file.py": "abc123"}
            mock_push.return_value = (True, "")
            mock_run.return_value = type("Result", (), {"returncode": 0, "stdout": "", "stderr": ""})()

            success, message = _commit_and_push(
                cwd=tmp_path, issue_number=1,
                issue_title="Test",
                repo_owner="myowner", repo_name="myrepo",
                initial_file_hashes={}, quiet=True
            )

        # Verify _push_with_retry was called with correct repo params
        mock_push.assert_called_once_with(tmp_path, "myowner", "myrepo")


class TestProviderFailureAbort:
    """Tests for abort on consecutive provider failures."""

    def test_abort_after_3_consecutive_provider_failures(self, e2e_fix_mock_dependencies, e2e_fix_default_args):
        """3 consecutive 'All agent providers failed' steps should abort early."""
        mock_run, _, _ = e2e_fix_mock_dependencies
        mock_run.return_value = (False, "All agent providers failed: anthropic: Exit code 1", 0.0, "")

        success, msg, cost, model, files = run_agentic_e2e_fix_orchestrator(**e2e_fix_default_args)

        assert success is False
        assert "Aborting" in msg or "consecutive" in msg.lower()
        assert mock_run.call_count == 3  # Aborted after 3 steps

    @patch("pdd.agentic_e2e_fix_orchestrator._verify_tests_independently")
    @patch("pdd.agentic_e2e_fix_orchestrator._extract_test_files")
    def test_provider_failure_counter_resets_on_success(self, mock_extract, mock_verify, e2e_fix_mock_dependencies, e2e_fix_default_args):
        """Success between failures should reset the counter — no abort."""
        mock_run, _, _ = e2e_fix_mock_dependencies

        # Mock independent verification to confirm tests pass
        mock_extract.return_value = ["tests/test_foo.py"]
        mock_verify.return_value = (True, "1 passed")

        call_count = [0]
        def side_effect(**kwargs):
            call_count[0] += 1
            n = call_count[0]
            if n in (1, 2):  # Steps 1-2: provider failure
                return (False, "All agent providers failed: anthropic: Exit code 1", 0.0, "")
            if n == 3:  # Step 3: success resets counter
                return (True, "Step output", 0.1, "claude")
            if n in (4, 5):  # Steps 4-5: provider failure again
                return (False, "All agent providers failed: anthropic: Exit code 1", 0.0, "")
            if n == 9:  # Step 9: success with ALL_TESTS_PASS to end
                return (True, "ALL_TESTS_PASS", 0.1, "claude")
            return (True, "Step output", 0.1, "claude")

        mock_run.side_effect = side_effect
        success, msg, cost, model, files = run_agentic_e2e_fix_orchestrator(**e2e_fix_default_args)

        # Should NOT have aborted — counter reset at step 3
        assert mock_run.call_count > 3


class TestIsIntermediateFile:
    """Direct unit tests for _is_intermediate_file (Issue #383).

    Tests the pure function in isolation — faster and more targeted than
    going through _commit_and_push.
    """

    @pytest.fixture
    def is_intermediate(self):
        """Import helper."""
        from pdd.agentic_e2e_fix_orchestrator import _is_intermediate_file
        return _is_intermediate_file

    # --- Should be filtered (True) ---

    @pytest.mark.parametrize("path", [
        "module_fixed.py",
        "pdd/auth_test_commands_auth_fixed.py",
        "tests/test_auth_test_commands_auth_fixed.py",
    ])
    def test_underscore_fixed_suffix_filtered(self, is_intermediate, path):
        """Files with _fixed suffix in stem should be filtered."""
        assert is_intermediate(path) is True

    @pytest.mark.parametrize("path", [
        "module.fixed.py",
        "pdd/handler.fixed.py",
    ])
    def test_dot_fixed_suffix_filtered(self, is_intermediate, path):
        """Files with .fixed suffix in stem should be filtered."""
        assert is_intermediate(path) is True

    @pytest.mark.parametrize("path", [
        "module-fixed.py",
        "pdd/service-fixed.py",
    ])
    def test_hyphen_fixed_suffix_filtered(self, is_intermediate, path):
        """Files with -fixed suffix in stem should be filtered."""
        assert is_intermediate(path) is True

    @pytest.mark.parametrize("path", [
        "module.py.bak",
        "module.py.backup",
        "module.py.orig",
        "module.py.tmp",
        "pdd/deep/nested/file.py.bak",
    ])
    def test_backup_extensions_filtered(self, is_intermediate, path):
        """Files with backup extensions should be filtered."""
        assert is_intermediate(path) is True

    @pytest.mark.parametrize("path", [
        "error_output.txt",
        "error_output_models.txt",
        "pdd/error_output_auth.txt",
    ])
    def test_error_output_files_filtered(self, is_intermediate, path):
        """error_output debug files should be filtered (gap fix for #383)."""
        assert is_intermediate(path) is True

    # --- Should NOT be filtered (False) — false-positive guards ---

    @pytest.mark.parametrize("path", [
        "fix_error_loop.py",
        "pdd/fix_error_loop.py",
        "tests/test_agentic_fix.py",
        "fixed.py",
        "tests/test_fixed_point_math.py",
        "pdd/currency_fixed_rate.py",
        "pdd/prefix_fixer.py",
        "conftest.py",
        "pdd/__init__.py",
        "README.md",
        "extensions/github_pdd_app/src/models.py",
        "error_output.py",
    ])
    def test_legitimate_files_not_filtered(self, is_intermediate, path):
        """Legitimate files must NOT be caught by the filter."""
        assert is_intermediate(path) is False

    # --- Nested subdirectory paths ---

    @pytest.mark.parametrize("path,expected", [
        ("pdd/utils/deep/module_fixed.py", True),
        ("a/b/c/d/backup.py.orig", True),
        ("src/nested/handler-fixed.py", True),
        ("pdd/utils/deep/module.py", False),
        ("a/b/c/d/real_code.py", False),
    ])
    def test_nested_subdirectory_paths(self, is_intermediate, path, expected):
        """Filter should work correctly regardless of directory depth."""
        assert is_intermediate(path) is expected


class TestCommitAndPushIntermediateFileFiltering:
    """Tests for issue #383: _commit_and_push should filter out intermediate files.

    The `pdd fix agentic` command creates intermediate/debug files with suffixes
    like `_fixed.py` during the fix workflow. These files should NOT be committed.
    """

    @pytest.fixture
    def mock_git_repo(self, tmp_path, monkeypatch):
        """Create a mock git repository for testing _commit_and_push behavior."""
        import subprocess

        subprocess.run(["git", "init"], cwd=tmp_path, capture_output=True)
        subprocess.run(
            ["git", "config", "user.email", "test@example.com"],
            cwd=tmp_path, capture_output=True,
        )
        subprocess.run(
            ["git", "config", "user.name", "Test User"],
            cwd=tmp_path, capture_output=True,
        )

        (tmp_path / "initial.py").write_text("# initial")
        subprocess.run(["git", "add", "initial.py"], cwd=tmp_path, capture_output=True)
        subprocess.run(
            ["git", "commit", "-m", "initial commit"],
            cwd=tmp_path, capture_output=True,
        )

        monkeypatch.chdir(tmp_path)
        return tmp_path

    def test_commit_and_push_filters_fixed_suffix_files(self, mock_git_repo):
        """_commit_and_push should NOT stage files with _fixed suffix."""
        from unittest.mock import MagicMock
        from pdd.agentic_e2e_fix_orchestrator import _commit_and_push

        cwd = mock_git_repo
        (cwd / "auth.py").write_text("# fixed auth code")
        (cwd / "auth_fixed.py").write_text("# intermediate backup")
        (cwd / "test_auth_fixed.py").write_text("# intermediate test backup")

        initial_hashes = {}
        staged_files = []
        original_run = __import__("subprocess").run

        def mock_run(args, **kwargs):
            if args[0] == "git" and args[1] == "add":
                staged_files.append(args[2])
                result = MagicMock()
                result.returncode = 0
                result.stderr = ""
                return result
            if args[0] == "git" and args[1] == "commit":
                result = MagicMock()
                result.returncode = 0
                result.stderr = ""
                return result
            if args[0] == "git" and args[1] == "push":
                result = MagicMock()
                result.returncode = 1
                result.stderr = "No remote configured"
                return result
            return original_run(args, **kwargs)

        with patch("subprocess.run", side_effect=mock_run):
            _commit_and_push(
                cwd=cwd,
                issue_number=383,
                issue_title="Test issue",
                repo_owner="test",
                repo_name="repo",
                initial_file_hashes=initial_hashes,
                quiet=True,
            )

        assert "auth.py" in staged_files, "Legitimate file should be staged"
        assert "auth_fixed.py" not in staged_files, (
            "Files with _fixed suffix should NOT be staged (Issue #383)"
        )
        assert "test_auth_fixed.py" not in staged_files, (
            "Test files with _fixed suffix should NOT be staged (Issue #383)"
        )

    def test_commit_and_push_filters_backup_extension_files(self, mock_git_repo):
        """_commit_and_push should NOT stage files with backup extensions."""
        from unittest.mock import MagicMock
        from pdd.agentic_e2e_fix_orchestrator import _commit_and_push

        cwd = mock_git_repo
        (cwd / "module.py").write_text("# fixed module")
        (cwd / "module.py.bak").write_text("# backup")
        (cwd / "module.py.orig").write_text("# original")

        initial_hashes = {}
        staged_files = []
        original_run = __import__("subprocess").run

        def mock_run(args, **kwargs):
            if args[0] == "git" and args[1] == "add":
                staged_files.append(args[2])
                result = MagicMock()
                result.returncode = 0
                result.stderr = ""
                return result
            if args[0] == "git" and args[1] == "commit":
                result = MagicMock()
                result.returncode = 0
                result.stderr = ""
                return result
            if args[0] == "git" and args[1] == "push":
                result = MagicMock()
                result.returncode = 1
                result.stderr = "No remote"
                return result
            return original_run(args, **kwargs)

        with patch("subprocess.run", side_effect=mock_run):
            _commit_and_push(
                cwd=cwd,
                issue_number=383,
                issue_title="Test issue",
                repo_owner="test",
                repo_name="repo",
                initial_file_hashes=initial_hashes,
                quiet=True,
            )

        assert "module.py" in staged_files, "Legitimate file should be staged"
        assert "module.py.bak" not in staged_files, "Files with .bak should NOT be staged"
        assert "module.py.orig" not in staged_files, "Files with .orig should NOT be staged"

    def test_commit_and_push_filters_error_output_files(self, mock_git_repo):
        """_commit_and_push should NOT stage error_output debug files."""
        from unittest.mock import MagicMock
        from pdd.agentic_e2e_fix_orchestrator import _commit_and_push

        cwd = mock_git_repo
        (cwd / "module.py").write_text("# fixed module")
        (cwd / "error_output.txt").write_text("debug output")
        (cwd / "error_output_models.txt").write_text("debug output")

        initial_hashes = {}
        staged_files = []
        original_run = __import__("subprocess").run

        def mock_run(args, **kwargs):
            if args[0] == "git" and args[1] == "add":
                staged_files.append(args[2])
                result = MagicMock()
                result.returncode = 0
                result.stderr = ""
                return result
            if args[0] == "git" and args[1] == "commit":
                result = MagicMock()
                result.returncode = 0
                result.stderr = ""
                return result
            if args[0] == "git" and args[1] == "push":
                result = MagicMock()
                result.returncode = 1
                result.stderr = "No remote"
                return result
            return original_run(args, **kwargs)

        with patch("subprocess.run", side_effect=mock_run):
            _commit_and_push(
                cwd=cwd,
                issue_number=383,
                issue_title="Test issue",
                repo_owner="test",
                repo_name="repo",
                initial_file_hashes=initial_hashes,
                quiet=True,
            )

        assert "module.py" in staged_files, "Legitimate file should be staged"
        assert "error_output.txt" not in staged_files, (
            "error_output.txt should NOT be staged"
        )
        assert "error_output_models.txt" not in staged_files, (
            "error_output_models.txt should NOT be staged"
        )

class TestIndependentTestVerification:
    """Tests for issue #588: Independent pytest verification of LLM claims.

    The orchestrator must not trust the LLM's ALL_TESTS_PASS claim blindly.
    After the LLM claims tests pass, we run pytest independently via subprocess
    and only accept the claim if the real pytest run confirms it.
    """

    @patch("pdd.agentic_e2e_fix_orchestrator._verify_tests_independently")
    @patch("pdd.agentic_e2e_fix_orchestrator._extract_test_files")
    def test_step2_all_tests_pass_hallucinated(self, mock_extract, mock_verify, e2e_fix_mock_dependencies, e2e_fix_default_args):
        """LLM claims ALL_TESTS_PASS but independent pytest finds failures.

        Primary bug reproducer for issue #588: The LLM hallucinated passing
        test results. The orchestrator should NOT exit successfully; it should
        override the step output with the real failure and continue to Step 3+.
        """
        mock_run, _, _ = e2e_fix_mock_dependencies

        # Independent verification finds failures
        mock_extract.return_value = ["tests/test_e2e_webhook.py"]
        mock_verify.return_value = (False, "FAILED tests/test_e2e_webhook.py::test_repositories_added - AssertionError")

        def side_effect(*args, **kwargs):
            label = kwargs.get('label', '')
            if 'step2' in label:
                return (True, "All tests pass. ALL_TESTS_PASS", 0.1, "gpt-4")
            return (True, f"Output for {label}", 0.1, "gpt-4")

        mock_run.side_effect = side_effect
        e2e_fix_default_args["max_cycles"] = 1

        success, msg, cost, model, files = run_agentic_e2e_fix_orchestrator(
            **e2e_fix_default_args
        )

        # Should NOT have exited successfully at Step 2
        assert success is False, (
            "Orchestrator should NOT report success when independent verification fails"
        )
        # Should have continued past Step 2 (at least to Step 3)
        assert mock_run.call_count > 2, (
            f"Expected workflow to continue past Step 2 but only ran {mock_run.call_count} steps"
        )

    @patch("pdd.agentic_e2e_fix_orchestrator._verify_tests_independently")
    @patch("pdd.agentic_e2e_fix_orchestrator._extract_test_files")
    def test_step2_all_tests_pass_verified(self, mock_extract, mock_verify, e2e_fix_mock_dependencies, e2e_fix_default_args):
        """LLM claims ALL_TESTS_PASS and independent pytest confirms all pass.

        Happy path: verification succeeds, early exit after Step 2.
        """
        mock_run, _, _ = e2e_fix_mock_dependencies

        mock_extract.return_value = ["tests/test_e2e_webhook.py"]
        mock_verify.return_value = (True, "1 passed in 0.5s")

        def side_effect(*args, **kwargs):
            label = kwargs.get('label', '')
            if 'step2' in label:
                return (True, "All tests pass. ALL_TESTS_PASS", 0.1, "gpt-4")
            return (True, f"Output for {label}", 0.1, "gpt-4")

        mock_run.side_effect = side_effect

        success, msg, cost, model, files = run_agentic_e2e_fix_orchestrator(
            **e2e_fix_default_args
        )

        assert success is True, f"Should succeed when independently verified: {msg}"
        assert "verified" in msg.lower(), f"Message should mention verification: {msg}"
        assert mock_run.call_count == 2

    @patch("pdd.agentic_e2e_fix_orchestrator._verify_tests_independently")
    @patch("pdd.agentic_e2e_fix_orchestrator._extract_test_files")
    def test_step9_all_tests_pass_hallucinated(self, mock_extract, mock_verify, e2e_fix_mock_dependencies, e2e_fix_default_args):
        """LLM claims ALL_TESTS_PASS at Step 9 but independent pytest finds failures.

        Same hallucination check for Step 9's ALL_TESTS_PASS exit.
        """
        mock_run, _, _ = e2e_fix_mock_dependencies

        mock_extract.return_value = ["tests/test_e2e_webhook.py"]
        mock_verify.return_value = (False, "FAILED tests/test_e2e_webhook.py::test_foo")

        def side_effect(*args, **kwargs):
            label = kwargs.get('label', '')
            if 'step9' in label:
                return (True, "Verification complete. ALL_TESTS_PASS", 0.1, "gpt-4")
            return (True, f"Output for {label}", 0.1, "gpt-4")

        mock_run.side_effect = side_effect
        e2e_fix_default_args["max_cycles"] = 1

        success, msg, cost, model, files = run_agentic_e2e_fix_orchestrator(
            **e2e_fix_default_args
        )

        # Should NOT have exited successfully
        assert success is False, (
            "Orchestrator should NOT report success when Step 9 verification fails"
        )

    @patch("pdd.agentic_e2e_fix_orchestrator._verify_tests_independently")
    @patch("pdd.agentic_e2e_fix_orchestrator._extract_test_files")
    def test_step2_no_test_files_fallback(self, mock_extract, mock_verify, e2e_fix_mock_dependencies, e2e_fix_default_args):
        """No test files extractable from issue — trusts LLM (backwards compatible).

        When we can't find test files for independent verification, we fall back
        to trusting the LLM output (same as old behavior).
        """
        mock_run, _, _ = e2e_fix_mock_dependencies

        mock_extract.return_value = []  # No test files found

        def side_effect(*args, **kwargs):
            label = kwargs.get('label', '')
            if 'step2' in label:
                return (True, "All tests pass. ALL_TESTS_PASS", 0.1, "gpt-4")
            return (True, f"Output for {label}", 0.1, "gpt-4")

        mock_run.side_effect = side_effect

        success, msg, cost, model, files = run_agentic_e2e_fix_orchestrator(
            **e2e_fix_default_args
        )

        assert success is True, f"Should succeed with fallback when no test files: {msg}"
        assert mock_run.call_count == 2
        # verify_tests_independently should NOT have been called
        mock_verify.assert_not_called()

    def test_extract_test_files_from_issue_content(self, tmp_path):
        """Unit test for _extract_test_files helper.

        Should parse test paths from issue comments containing E2E_FILES_CREATED
        markers and step comments referencing test files.
        """
        # Create test files on disk so they pass the existence check
        (tmp_path / "tests").mkdir()
        (tmp_path / "tests" / "test_e2e_webhook_payload.py").touch()
        (tmp_path / "tests" / "test_e2e_repositories_added.py").touch()

        issue_content = (
            "## Step 11: E2E Test\n"
            "E2E_FILES_CREATED: tests/test_e2e_webhook_payload.py, tests/test_e2e_repositories_added.py\n"
            "Both tests verify the webhook payload handling.\n"
        )
        changed_files = ["tests/test_e2e_webhook_payload.py", "src/webhook.py"]

        result = _extract_test_files(issue_content, changed_files, tmp_path)

        assert "tests/test_e2e_webhook_payload.py" in result
        assert "tests/test_e2e_repositories_added.py" in result
        # Non-test files should NOT be included
        assert "src/webhook.py" not in result

    def test_extract_test_files_from_changed_files(self, tmp_path):
        """Test files from changed_files list should be included."""
        (tmp_path / "tests").mkdir()
        (tmp_path / "tests" / "test_foo.py").touch()

        result = _extract_test_files("No markers here", ["tests/test_foo.py", "src/foo.py"], tmp_path)

        assert "tests/test_foo.py" in result
        assert "src/foo.py" not in result

    def test_extract_test_files_deduplicates(self, tmp_path):
        """Same test file from multiple sources should appear only once."""
        (tmp_path / "tests").mkdir()
        (tmp_path / "tests" / "test_e2e_foo.py").touch()

        issue_content = "E2E_FILES_CREATED: tests/test_e2e_foo.py\n"
        changed_files = ["tests/test_e2e_foo.py"]

        result = _extract_test_files(issue_content, changed_files, tmp_path)

        assert result.count("tests/test_e2e_foo.py") == 1

    def test_extract_test_files_from_disk_changes(self, tmp_path):
        """Test files created on disk during workflow should be detected.

        Reproduces the actual issue #588 scenario: issue_content has no
        test file markers, changed_files is empty, but the agent created
        test files on disk. Hash comparison should find them.
        """
        import subprocess
        # Initialize a git repo so _get_modified_and_untracked works
        subprocess.run(["git", "init"], cwd=tmp_path, capture_output=True)
        subprocess.run(["git", "commit", "--allow-empty", "-m", "init"], cwd=tmp_path, capture_output=True)

        (tmp_path / "tests").mkdir()
        test_file = tmp_path / "tests" / "test_issue_588_regression.py"
        test_file.write_text("def test_something(): pass")
        # Also create a non-test file to ensure it's filtered out
        (tmp_path / "src").mkdir()
        (tmp_path / "src" / "webhook.py").write_text("# code")

        # initial_file_hashes is empty (snapshot before workflow started)
        # but the test file now exists on disk as untracked
        initial_hashes: Dict[str, Optional[str]] = {}

        # No markers in issue, no changed_files from LLM output
        result = _extract_test_files(
            "Generic bug description with no test files",
            [],
            tmp_path,
            initial_hashes,
        )

        assert "tests/test_issue_588_regression.py" in result
        assert "src/webhook.py" not in result


class TestIssue797TypeScriptTestFiles:
    """Tests for issue #797: _extract_test_files and _verify_tests_independently
    are Python-only, silently skipping TypeScript/Jest/Playwright tests.

    Bug: All 5 filtering locations in _extract_test_files only accept .py files,
    and _verify_tests_independently only runs pytest. This means TypeScript test
    files (.test.tsx, .test.ts, .spec.ts, .spec.tsx) are invisible to the
    independent verification safety net.
    """

    # ── _extract_test_files: changed_files scan (line 193) ──

    def test_extract_test_files_accepts_jest_tsx_from_changed_files(self, tmp_path):
        """changed_files containing .test.tsx should be extracted (Jest convention)."""
        test_dir = tmp_path / "frontend" / "src" / "components" / "__test__"
        test_dir.mkdir(parents=True)
        (test_dir / "WaitlistPending.test.tsx").touch()

        result = _extract_test_files(
            "No markers",
            ["frontend/src/components/__test__/WaitlistPending.test.tsx"],
            tmp_path,
        )

        assert "frontend/src/components/__test__/WaitlistPending.test.tsx" in result

    def test_extract_test_files_accepts_jest_ts_from_changed_files(self, tmp_path):
        """changed_files containing .test.ts should be extracted (Jest convention)."""
        test_dir = tmp_path / "frontend" / "src"
        test_dir.mkdir(parents=True)
        (test_dir / "utils.test.ts").touch()

        result = _extract_test_files(
            "No markers",
            ["frontend/src/utils.test.ts"],
            tmp_path,
        )

        assert "frontend/src/utils.test.ts" in result

    def test_extract_test_files_accepts_playwright_spec_ts_from_changed_files(self, tmp_path):
        """changed_files containing .spec.ts should be extracted (Playwright convention)."""
        test_dir = tmp_path / "frontend" / "e2e" / "tests"
        test_dir.mkdir(parents=True)
        (test_dir / "auto-refresh.spec.ts").touch()

        result = _extract_test_files(
            "No markers",
            ["frontend/e2e/tests/auto-refresh.spec.ts"],
            tmp_path,
        )

        assert "frontend/e2e/tests/auto-refresh.spec.ts" in result

    def test_extract_test_files_accepts_spec_tsx_from_changed_files(self, tmp_path):
        """changed_files containing .spec.tsx should be extracted."""
        test_dir = tmp_path / "src"
        test_dir.mkdir(parents=True)
        (test_dir / "App.spec.tsx").touch()

        result = _extract_test_files(
            "No markers",
            ["src/App.spec.tsx"],
            tmp_path,
        )

        assert "src/App.spec.tsx" in result

    # ── _extract_test_files: E2E_FILES_CREATED marker (line 187) ──

    def test_extract_test_files_accepts_tsx_from_markers(self, tmp_path):
        """E2E_FILES_CREATED markers with .test.tsx files should be extracted."""
        test_dir = tmp_path / "frontend" / "src" / "__test__"
        test_dir.mkdir(parents=True)
        (test_dir / "WaitlistPending.test.tsx").touch()

        issue_content = "E2E_FILES_CREATED: frontend/src/__test__/WaitlistPending.test.tsx\n"

        result = _extract_test_files(issue_content, [], tmp_path)

        assert "frontend/src/__test__/WaitlistPending.test.tsx" in result

    def test_extract_test_files_accepts_spec_ts_from_markers(self, tmp_path):
        """E2E_FILES_CREATED markers with .spec.ts files should be extracted."""
        test_dir = tmp_path / "frontend" / "e2e"
        test_dir.mkdir(parents=True)
        (test_dir / "auto-refresh.spec.ts").touch()

        issue_content = "E2E_FILES_CREATED: frontend/e2e/auto-refresh.spec.ts\n"

        result = _extract_test_files(issue_content, [], tmp_path)

        assert "frontend/e2e/auto-refresh.spec.ts" in result

    # ── _extract_test_files: disk-change detection (line 205) ──

    def test_extract_test_files_detects_tsx_from_disk_changes(self, tmp_path):
        """TypeScript test files created on disk should be detected via hash comparison."""
        import subprocess
        subprocess.run(["git", "init"], cwd=tmp_path, capture_output=True)
        subprocess.run(["git", "commit", "--allow-empty", "-m", "init"], cwd=tmp_path, capture_output=True)

        test_dir = tmp_path / "frontend" / "src" / "__test__"
        test_dir.mkdir(parents=True)
        (test_dir / "Component.test.tsx").write_text("test('renders', () => {});")

        initial_hashes: Dict[str, Optional[str]] = {}

        result = _extract_test_files(
            "Generic bug description",
            [],
            tmp_path,
            initial_hashes,
        )

        assert "frontend/src/__test__/Component.test.tsx" in result

    def test_extract_test_files_detects_spec_ts_from_disk_changes(self, tmp_path):
        """Playwright spec files created on disk should be detected via hash comparison."""
        import subprocess
        subprocess.run(["git", "init"], cwd=tmp_path, capture_output=True)
        subprocess.run(["git", "commit", "--allow-empty", "-m", "init"], cwd=tmp_path, capture_output=True)

        test_dir = tmp_path / "e2e" / "tests"
        test_dir.mkdir(parents=True)
        (test_dir / "login.spec.ts").write_text("test('login works', async () => {});")

        initial_hashes: Dict[str, Optional[str]] = {}

        result = _extract_test_files(
            "Generic bug description",
            [],
            tmp_path,
            initial_hashes,
        )

        assert "e2e/tests/login.spec.ts" in result

    # ── _extract_test_files: inline regex (line 197) ──

    def test_extract_test_files_inline_regex_matches_tsx_test_files(self, tmp_path):
        """Inline references to .test.tsx files in issue content should be found."""
        test_dir = tmp_path / "src" / "__test__"
        test_dir.mkdir(parents=True)
        (test_dir / "Button.test.tsx").touch()

        issue_content = "The test is at src/__test__/Button.test.tsx and it fails."

        result = _extract_test_files(issue_content, [], tmp_path)

        assert "src/__test__/Button.test.tsx" in result

    # ── _verify_tests_independently: runner dispatch ──

    @patch("pdd.agentic_e2e_fix_orchestrator.run_pytest_and_capture_output")
    def test_verify_independently_uses_pytest_for_py(self, mock_pytest, tmp_path):
        """Python test files should still use pytest (regression guard)."""
        mock_pytest.return_value = {
            "test_results": [{"passed": 1, "failures": 0, "errors": 0, "standard_output": ""}]
        }

        passed, output = _verify_tests_independently(["tests/test_foo.py"], tmp_path)

        assert passed is True
        mock_pytest.assert_called_once()

    @patch("subprocess.run")
    @patch("pdd.agentic_e2e_fix_orchestrator.get_test_command_for_file", return_value="npx jest src/__test__/Widget.test.tsx")
    @patch("pdd.agentic_e2e_fix_orchestrator.run_pytest_and_capture_output")
    def test_verify_independently_does_not_use_pytest_for_tsx(self, mock_pytest, mock_get_cmd, mock_subproc, tmp_path):
        """Jest .test.tsx files should NOT be run through pytest.

        The current buggy code calls run_pytest_and_capture_output for ALL files,
        which fails silently for TypeScript. The fix should use an appropriate
        runner (e.g., npx jest) for .test.tsx files.
        """
        mock_subproc.return_value = MagicMock(returncode=0, stdout="PASS", stderr="")

        test_dir = tmp_path / "src" / "__test__"
        test_dir.mkdir(parents=True)
        (test_dir / "Widget.test.tsx").write_text("test('renders', () => {});")

        passed, output = _verify_tests_independently(
            ["src/__test__/Widget.test.tsx"], tmp_path
        )

        mock_pytest.assert_not_called()
        mock_subproc.assert_called_once()
        # Verify shell=False (no command injection)
        _, kwargs = mock_subproc.call_args
        assert kwargs.get("shell") is False

    @patch("subprocess.run")
    @patch("pdd.agentic_e2e_fix_orchestrator.get_test_command_for_file", return_value="npx playwright test e2e/login.spec.ts")
    @patch("pdd.agentic_e2e_fix_orchestrator.run_pytest_and_capture_output")
    def test_verify_independently_does_not_use_pytest_for_spec_ts(self, mock_pytest, mock_get_cmd, mock_subproc, tmp_path):
        """Playwright .spec.ts files should NOT be run through pytest."""
        mock_subproc.return_value = MagicMock(returncode=0, stdout="PASS", stderr="")

        test_dir = tmp_path / "e2e"
        test_dir.mkdir(parents=True)
        (test_dir / "login.spec.ts").write_text("test('login', async () => {});")

        passed, output = _verify_tests_independently(
            ["e2e/login.spec.ts"], tmp_path
        )

        mock_pytest.assert_not_called()
        mock_subproc.assert_called_once()
        _, kwargs = mock_subproc.call_args
        assert kwargs.get("shell") is False

    @patch("pdd.agentic_e2e_fix_orchestrator.get_test_command_for_file", return_value=None)
    @patch("pdd.agentic_e2e_fix_orchestrator.run_pytest_and_capture_output")
    def test_verify_independently_fails_when_no_runner_available(self, mock_pytest, mock_get_cmd, tmp_path):
        """When no test runner is available for a non-Python file, verification should fail."""
        test_dir = tmp_path / "src"
        test_dir.mkdir(parents=True)
        (test_dir / "app.test.tsx").write_text("test('x', () => {});")

        passed, output = _verify_tests_independently(
            ["src/app.test.tsx"], tmp_path
        )

        assert passed is False
        assert "no test runner available" in output.lower()


# ============================================================================
# Issue #791: E2E test step times out on every cycle
# ============================================================================


class TestIssue791PromptVerification:
    """Tests 1-2: Verify prompt specifies E2E pre-flight check and cross-cycle memory.

    Issue #791: The prompt should now include requirements for:
    1. _check_e2e_environment pre-flight check before Step 2
    2. skipped_steps cross-cycle memory to avoid retrying failed steps
    """

    def test_prompt_specifies_check_e2e_environment(self):
        """Test 1: Prompt must specify _check_e2e_environment pre-flight check.

        The prompt should instruct the code generator to create a
        _check_e2e_environment helper that checks for playwright/browser
        before running Step 2.
        """
        template = load_prompt_template("agentic_e2e_fix_orchestrator_python")
        assert template is not None, "Orchestrator prompt should load"

        assert "_check_e2e_environment" in template, (
            "Prompt must specify _check_e2e_environment helper function. "
            "Without this, Step 2 dispatches E2E tests to LLM agent without "
            "checking if the environment can run them, causing 240s timeouts."
        )

    def test_prompt_specifies_skipped_steps_memory(self):
        """Test 2: Prompt must specify skipped_steps cross-cycle memory.

        The prompt should instruct the code generator to maintain a
        skipped_steps dict that persists across cycles, preventing
        retries of environmentally-failed steps.
        """
        template = load_prompt_template("agentic_e2e_fix_orchestrator_python")
        assert template is not None, "Orchestrator prompt should load"

        assert "skipped_steps" in template, (
            "Prompt must specify skipped_steps cross-cycle memory. "
            "Without this, step_outputs is cleared between cycles (line 859), "
            "destroying failure information and causing identical retries."
        )

        # Verify skipped_steps is NOT cleared with step_outputs
        assert "NOT cleared when" in template or "Persists across cycles" in template, (
            "Prompt must explicitly state skipped_steps persists across cycles "
            "and is NOT cleared when step_outputs is cleared."
        )


class TestIssue791E2EEnvironmentCheck:
    """Tests 3-5: Verify E2E skip when environment unavailable.

    Issue #791: The orchestrator should skip Step 2 immediately when the
    executor environment lacks E2E infrastructure (playwright/browser/dev-server).
    """

    def test_step2_skipped_when_e2e_environment_unavailable(self, e2e_fix_mock_dependencies, e2e_fix_default_args):
        """Test 3: Step 2 should be skipped when E2E environment is unavailable.

        Bug: The current code dispatches Step 2 to the LLM agent without
        checking if playwright/browser exist, consuming a full 240s timeout.

        Fix: _check_e2e_environment should detect missing infrastructure and
        skip Step 2 immediately with E2E_SKIP output.

        This test FAILS on buggy code because _check_e2e_environment doesn't exist.
        """
        mock_run, _, _ = e2e_fix_mock_dependencies

        # All steps succeed, step 9 signals completion
        def side_effect(*args, **kwargs):
            label = kwargs.get('label', '')
            if 'step9' in label:
                return (True, "ALL_TESTS_PASS", 0.1, "gpt-4")
            return (True, f"Output for {label}", 0.1, "gpt-4")

        mock_run.side_effect = side_effect

        # Mock _check_e2e_environment to report environment unavailable
        with patch("pdd.agentic_e2e_fix_orchestrator._check_e2e_environment") as mock_check:
            mock_check.return_value = (False, "playwright not installed")

            success, msg, cost, model, files = run_agentic_e2e_fix_orchestrator(
                **e2e_fix_default_args
            )

            # Verify _check_e2e_environment was called
            mock_check.assert_called_once()

            # Step 2 should NOT have been dispatched to the LLM agent
            step_labels = [c.kwargs.get('label', '') for c in mock_run.call_args_list]
            assert not any('step2' in label for label in step_labels), (
                f"Step 2 should be skipped when E2E environment is unavailable, "
                f"but it was dispatched. Labels: {step_labels}"
            )

    def test_step2_timeout_converts_to_skip(self, e2e_fix_mock_dependencies, e2e_fix_default_args):
        """Test 4: Step 2 timeout should be converted to E2E_SKIP for future cycles.

        Bug: When Step 2 times out with 'All agent providers failed: Timeout expired',
        the failure is stored in step_outputs but cleared between cycles (line 859).

        Fix: Timeout failures should be added to skipped_steps so Step 2 is
        skipped immediately on subsequent cycles.

        This test FAILS on buggy code because skipped_steps doesn't exist.
        """
        mock_run, _, _ = e2e_fix_mock_dependencies

        call_count = [0]

        def side_effect(*args, **kwargs):
            call_count[0] += 1
            label = kwargs.get('label', '')
            if 'step2' in label:
                # Step 2 times out (simulating the real bug scenario)
                return (False, "All agent providers failed: anthropic: Timeout expired", 0.1, "gpt-4")
            if 'step9' in label:
                # Cycle 1: continue, Cycle 2: max cycles
                if 'cycle1' in label:
                    return (True, "CONTINUE_CYCLE", 0.1, "gpt-4")
                return (True, "MAX_CYCLES_REACHED", 0.1, "gpt-4")
            return (True, f"Output for {label}", 0.1, "gpt-4")

        mock_run.side_effect = side_effect

        # Run with 2 max cycles so we can observe cycle 2 behavior
        e2e_fix_default_args["max_cycles"] = 2

        # Need _check_e2e_environment to exist (returns True = environment is fine)
        with patch("pdd.agentic_e2e_fix_orchestrator._check_e2e_environment") as mock_check:
            mock_check.return_value = (True, "")  # Environment appears fine initially

            run_agentic_e2e_fix_orchestrator(**e2e_fix_default_args)

            # Count how many times Step 2 was dispatched to LLM
            step2_calls = [c for c in mock_run.call_args_list if 'step2' in c.kwargs.get('label', '')]

            # Step 2 should only be dispatched ONCE (cycle 1).
            # In cycle 2, skipped_steps should prevent retry.
            assert len(step2_calls) == 1, (
                f"Step 2 should only be dispatched once (cycle 1), then skipped in cycle 2 "
                f"via skipped_steps memory. But it was called {len(step2_calls)} times. "
                f"All labels: {[c.kwargs.get('label', '') for c in mock_run.call_args_list]}"
            )

    def test_normal_failure_still_retried(self, e2e_fix_mock_dependencies, e2e_fix_default_args):
        """Test 5: Normal test failures (not timeouts) should still be retried.

        Only environmental/timeout failures should be added to skipped_steps.
        Normal test failures (e.g., 'FAILED: 3 tests failed') should be retried
        on subsequent cycles.
        """
        mock_run, _, _ = e2e_fix_mock_dependencies

        cycle_tracker = [0]

        def side_effect(*args, **kwargs):
            label = kwargs.get('label', '')
            if 'step2' in label:
                # Normal test failure (NOT a timeout)
                return (False, "FAILED: 3 of 5 e2e tests failed", 0.1, "gpt-4")
            if 'step9' in label:
                cycle_tracker[0] += 1
                if cycle_tracker[0] < 2:
                    return (True, "CONTINUE_CYCLE", 0.1, "gpt-4")
                return (True, "MAX_CYCLES_REACHED", 0.1, "gpt-4")
            return (True, f"Output for {label}", 0.1, "gpt-4")

        mock_run.side_effect = side_effect

        e2e_fix_default_args["max_cycles"] = 2

        with patch("pdd.agentic_e2e_fix_orchestrator._check_e2e_environment") as mock_check:
            mock_check.return_value = (True, "")  # Environment is fine

            run_agentic_e2e_fix_orchestrator(**e2e_fix_default_args)

            # Step 2 should be dispatched in BOTH cycles (normal failure = retryable)
            step2_calls = [c for c in mock_run.call_args_list if 'step2' in c.kwargs.get('label', '')]
            assert len(step2_calls) == 2, (
                f"Normal test failures should be retried on subsequent cycles. "
                f"Expected Step 2 to run in both cycles (2 calls), got {len(step2_calls)}."
            )


class TestIssue791CrossCycleMemory:
    """Tests 6-8: Verify cross-cycle state management.

    Issue #791: skipped_steps should persist across cycles while
    step_outputs is correctly cleared.
    """

    def test_skipped_steps_not_cleared_between_cycles(self, e2e_fix_mock_dependencies, e2e_fix_default_args):
        """Test 6: skipped_steps should NOT be cleared when step_outputs is cleared.

        Bug: Lines 857-859 clear step_outputs and reset last_completed_step
        between cycles. The fix must NOT clear skipped_steps alongside them.

        This test FAILS on buggy code because skipped_steps doesn't exist,
        so all state including failure memory is lost between cycles.
        """
        mock_run, _, _ = e2e_fix_mock_dependencies

        step2_dispatch_count = [0]

        def side_effect(*args, **kwargs):
            label = kwargs.get('label', '')
            if 'step2' in label:
                step2_dispatch_count[0] += 1
                return (False, "All agent providers failed: anthropic: Timeout expired", 0.1, "gpt-4")
            if 'step9' in label:
                if 'cycle1' in label:
                    return (True, "CONTINUE_CYCLE", 0.1, "gpt-4")
                if 'cycle2' in label:
                    return (True, "CONTINUE_CYCLE", 0.1, "gpt-4")
                return (True, "MAX_CYCLES_REACHED", 0.1, "gpt-4")
            return (True, f"Output for {label}", 0.1, "gpt-4")

        mock_run.side_effect = side_effect

        e2e_fix_default_args["max_cycles"] = 3

        with patch("pdd.agentic_e2e_fix_orchestrator._check_e2e_environment") as mock_check:
            mock_check.return_value = (True, "")  # Environment seems fine initially

            run_agentic_e2e_fix_orchestrator(**e2e_fix_default_args)

            # Step 2 should only be dispatched once (cycle 1), then remembered as
            # skipped for cycles 2 and 3
            assert step2_dispatch_count[0] == 1, (
                f"Step 2 timed out in cycle 1 and should be skipped in cycles 2-3 "
                f"via skipped_steps memory, but was dispatched {step2_dispatch_count[0]} times. "
                f"This means skipped_steps was cleared between cycles."
            )

    def test_e2e_skip_output_set_correctly(self, e2e_fix_mock_dependencies, e2e_fix_default_args):
        """Test 7: When E2E environment is unavailable, step_outputs['2'] should contain E2E_SKIP.

        The orchestrator should set step_outputs['2'] = 'E2E_SKIP: {reason}'
        so that Step 3 receives the skip reason as context.
        """
        mock_run, _, _ = e2e_fix_mock_dependencies

        step3_received_context = [None]

        def side_effect(*args, **kwargs):
            label = kwargs.get('label', '')
            instruction = kwargs.get('instruction', '') or (args[0] if args else '')
            if 'step3' in label:
                # Capture what Step 3 receives as context (includes step2_output)
                step3_received_context[0] = instruction
                return (True, "Root cause analysis", 0.1, "gpt-4")
            if 'step9' in label:
                return (True, "ALL_TESTS_PASS", 0.1, "gpt-4")
            return (True, f"Output for {label}", 0.1, "gpt-4")

        mock_run.side_effect = side_effect

        with patch("pdd.agentic_e2e_fix_orchestrator._check_e2e_environment") as mock_check:
            mock_check.return_value = (False, "playwright not installed")

            run_agentic_e2e_fix_orchestrator(**e2e_fix_default_args)

            # Step 3's formatted prompt should contain E2E_SKIP info
            assert step3_received_context[0] is not None, (
                "Step 3 should have been called"
            )
            assert "E2E_SKIP" in step3_received_context[0], (
                "Step 3 context should include E2E_SKIP information from Step 2, "
                "so the root cause analysis knows E2E tests were skipped."
            )

    def test_check_e2e_environment_function_exists(self):
        """Test 8: _check_e2e_environment helper function must exist in the module.

        The orchestrator must have a _check_e2e_environment function that checks
        for playwright/browser availability before running Step 2.

        This test FAILS on buggy code because the function doesn't exist yet.
        """
        from pdd import agentic_e2e_fix_orchestrator
        assert hasattr(agentic_e2e_fix_orchestrator, '_check_e2e_environment'), (
            "agentic_e2e_fix_orchestrator must have _check_e2e_environment function. "
            "Without this, Step 2 always dispatches to LLM, causing 240s timeouts "
            "in environments without E2E infrastructure."
        )

        import inspect
        sig = inspect.signature(agentic_e2e_fix_orchestrator._check_e2e_environment)
        params = list(sig.parameters.keys())
        assert 'cwd' in params, (
            "_check_e2e_environment must accept 'cwd' parameter"
        )


class TestIssue791CheckE2EEnvironmentUnit:
    """Unit tests for _check_e2e_environment helper function.

    Issue #791 Cycle 2: Direct unit tests for the pre-flight check that
    detects whether the executor environment can run E2E tests.
    """

    def test_returns_false_when_npx_not_found(self, tmp_path):
        """_check_e2e_environment returns (False, reason) when npx is not on PATH.

        Without npx, playwright cannot run — the check should detect this
        before the orchestrator wastes 240s dispatching Step 2 to the LLM.
        """
        from pdd.agentic_e2e_fix_orchestrator import _check_e2e_environment

        # Create a playwright config so the only missing piece is npx
        (tmp_path / "playwright.config.ts").write_text("export default {}")

        with patch("pdd.agentic_e2e_fix_orchestrator.shutil.which", return_value=None):
            available, reason = _check_e2e_environment(tmp_path)

        assert available is False, "Should return False when npx is not found"
        assert "npx" in reason.lower(), f"Reason should mention npx, got: {reason}"

    def test_returns_false_when_no_playwright_config(self, tmp_path):
        """_check_e2e_environment returns (False, reason) when no playwright config exists.

        Even if npx is available, without a playwright config file the project
        doesn't have E2E tests to run.
        """
        from pdd.agentic_e2e_fix_orchestrator import _check_e2e_environment

        with patch("pdd.agentic_e2e_fix_orchestrator.shutil.which", return_value="/usr/bin/npx"):
            available, reason = _check_e2e_environment(tmp_path)

        assert available is False, "Should return False when no playwright config exists"
        assert "playwright" in reason.lower(), f"Reason should mention playwright, got: {reason}"

    def test_returns_true_when_npx_and_config_present(self, tmp_path):
        """_check_e2e_environment returns (True, '') when both npx and config exist.

        When the environment has both npx and a playwright config file,
        the pre-flight check should allow Step 2 to proceed.
        """
        from pdd.agentic_e2e_fix_orchestrator import _check_e2e_environment

        (tmp_path / "playwright.config.ts").write_text("export default {}")

        with patch("pdd.agentic_e2e_fix_orchestrator.shutil.which", return_value="/usr/bin/npx"):
            available, reason = _check_e2e_environment(tmp_path)

        assert available is True, "Should return True when npx and config are present"
        assert reason == "", f"Reason should be empty, got: {reason}"

    def test_detects_js_playwright_config(self, tmp_path):
        """_check_e2e_environment detects playwright.config.js (not just .ts)."""
        from pdd.agentic_e2e_fix_orchestrator import _check_e2e_environment

        (tmp_path / "playwright.config.js").write_text("module.exports = {}")

        with patch("pdd.agentic_e2e_fix_orchestrator.shutil.which", return_value="/usr/bin/npx"):
            available, reason = _check_e2e_environment(tmp_path)

        assert available is True, "Should detect playwright.config.js"

    def test_detects_mjs_playwright_config(self, tmp_path):
        """_check_e2e_environment detects playwright.config.mjs."""
        from pdd.agentic_e2e_fix_orchestrator import _check_e2e_environment

        (tmp_path / "playwright.config.mjs").write_text("export default {}")

        with patch("pdd.agentic_e2e_fix_orchestrator.shutil.which", return_value="/usr/bin/npx"):
            available, reason = _check_e2e_environment(tmp_path)

        assert available is True, "Should detect playwright.config.mjs"

    def test_return_type_is_tuple(self, tmp_path):
        """_check_e2e_environment must return a (bool, str) tuple."""
        from pdd.agentic_e2e_fix_orchestrator import _check_e2e_environment

        with patch("pdd.agentic_e2e_fix_orchestrator.shutil.which", return_value=None):
            result = _check_e2e_environment(tmp_path)

        assert isinstance(result, tuple), f"Expected tuple, got {type(result)}"
        assert len(result) == 2, f"Expected 2-element tuple, got {len(result)}"
        assert isinstance(result[0], bool), f"First element should be bool, got {type(result[0])}"
        assert isinstance(result[1], str), f"Second element should be str, got {type(result[1])}"


class TestIssue791SkippedStepsEdgeCases:
    """Edge case tests for skipped_steps cross-cycle memory.

    Issue #791 Cycle 2: Tests for edge cases in the timeout-to-skip conversion
    and E2E_SKIP note propagation to subsequent steps.
    """

    def test_e2e_skip_note_appended_to_step4_prompt(self, e2e_fix_mock_dependencies, e2e_fix_default_args):
        """When Step 2 is skipped, subsequent steps (3, 4, ...) should receive
        an appended note about the skip so LLM agents have context.

        The orchestrator appends 'Note: Step 2 was skipped — E2E_SKIP: ...'
        to the formatted prompt for steps after the skipped step.
        """
        mock_run, _, _ = e2e_fix_mock_dependencies

        step4_instruction = [None]

        def side_effect(*args, **kwargs):
            label = kwargs.get('label', '')
            instruction = kwargs.get('instruction', '') or (args[0] if args else '')
            if 'step4' in label:
                step4_instruction[0] = instruction
            if 'step9' in label:
                return (True, "ALL_TESTS_PASS", 0.1, "gpt-4")
            return (True, f"Output for {label}", 0.1, "gpt-4")

        mock_run.side_effect = side_effect

        with patch("pdd.agentic_e2e_fix_orchestrator._check_e2e_environment") as mock_check:
            mock_check.return_value = (False, "playwright not installed")
            run_agentic_e2e_fix_orchestrator(**e2e_fix_default_args)

        assert step4_instruction[0] is not None, "Step 4 should have been called"
        assert "E2E_SKIP" in step4_instruction[0], (
            "Step 4 prompt should contain E2E_SKIP note from skipped Step 2"
        )

    def test_timeout_skip_only_for_all_providers_failed(self, e2e_fix_mock_dependencies, e2e_fix_default_args):
        """Only 'All agent providers failed' timeouts should trigger skip memory.

        Other failure types (e.g., prompt errors, partial failures) should NOT
        be added to skipped_steps, ensuring they can be retried after code fixes.
        """
        mock_run, _, _ = e2e_fix_mock_dependencies

        step2_call_count = [0]

        def side_effect(*args, **kwargs):
            label = kwargs.get('label', '')
            if 'step2' in label:
                step2_call_count[0] += 1
                # Partial failure — NOT a provider timeout
                return (False, "FAILED: 2 of 5 tests timed out individually", 0.1, "gpt-4")
            if 'step9' in label:
                if 'cycle1' in label:
                    return (True, "CONTINUE_CYCLE", 0.1, "gpt-4")
                return (True, "MAX_CYCLES_REACHED", 0.1, "gpt-4")
            return (True, f"Output for {label}", 0.1, "gpt-4")

        mock_run.side_effect = side_effect
        e2e_fix_default_args["max_cycles"] = 2

        with patch("pdd.agentic_e2e_fix_orchestrator._check_e2e_environment") as mock_check:
            mock_check.return_value = (True, "")
            run_agentic_e2e_fix_orchestrator(**e2e_fix_default_args)

        # Step 2 should be called in BOTH cycles since it's not a provider timeout
        assert step2_call_count[0] == 2, (
            f"Non-provider failures should be retried. Step 2 was called "
            f"{step2_call_count[0]} times, expected 2."
        )

    def test_skipped_step_cost_is_zero(self, e2e_fix_mock_dependencies, e2e_fix_default_args):
        """Skipped steps should not incur any LLM cost.

        When Step 2 is skipped via pre-flight check, no run_agentic_task call
        is made, so the cost for that step should be $0.
        """
        mock_run, _, _ = e2e_fix_mock_dependencies

        def side_effect(*args, **kwargs):
            label = kwargs.get('label', '')
            if 'step9' in label:
                return (True, "ALL_TESTS_PASS", 0.1, "gpt-4")
            return (True, f"Output for {label}", 0.1, "gpt-4")

        mock_run.side_effect = side_effect
        e2e_fix_default_args["max_cycles"] = 1

        with patch("pdd.agentic_e2e_fix_orchestrator._check_e2e_environment") as mock_check:
            mock_check.return_value = (False, "no playwright")
            success, msg, cost, model, files = run_agentic_e2e_fix_orchestrator(
                **e2e_fix_default_args
            )

        # With Step 2 skipped, we should have 8 steps * $0.1 = $0.8
        # NOT 9 steps * $0.1 = $0.9
        step_labels = [c.kwargs.get('label', '') for c in mock_run.call_args_list]
        assert not any('step2' in label for label in step_labels), (
            "Step 2 should not have been dispatched"
        )
        # Cost should reflect only 8 dispatched steps
        assert cost == pytest.approx(0.8, abs=0.01), (
            f"Cost should be ~$0.80 (8 steps at $0.10 each, Step 2 skipped), got ${cost:.4f}"
        )


# ============================================================================
# Issue #830: Missing Loop Control Token, State Divergence
#
# Bug 1: When Step 9 output has no loop control token, the orchestrator
# prints a warning but falls through to cycle increment (CONTINUE_CYCLE
# by default), causing an unnecessary Cycle 2.
# Fix: treat missing token as terminal — break out of the loop.
#
# Bug 3 (orchestrator side): save_workflow_state() returning stale
# github_comment_id when GitHub save fails, masking state divergence.
# ============================================================================


class TestIssue830MissingLoopControlToken:
    """Tests for issue #830 Bug 1: Step 9 missing loop control token.

    When Step 9 output contains none of the recognized loop control tokens
    (ALL_TESTS_PASS, CONTINUE_CYCLE, MAX_CYCLES_REACHED), the orchestrator
    should treat it as a terminal condition and break, not default to
    CONTINUE_CYCLE.
    """

    def test_no_loop_control_token_breaks_loop(self, e2e_fix_mock_dependencies, e2e_fix_default_args):
        """Step 9 with no control token should NOT start Cycle 2.

        Bug: The orchestrator defaults to CONTINUE_CYCLE when no token is
        found, causing unnecessary Cycle 2. Fix: break the loop.
        """
        mock_run, _, mock_console = e2e_fix_mock_dependencies
        e2e_fix_default_args["max_cycles"] = 3

        def side_effect(*args, **kwargs):
            label = kwargs.get('label', '')
            if 'step9' in label:
                # Step 9 output with NO loop control token
                return (True, "Verification complete. Some output without any token.", 0.1, "gpt-4")
            return (True, f"Output for {label}", 0.1, "gpt-4")

        mock_run.side_effect = side_effect

        success, msg, cost, model, files = run_agentic_e2e_fix_orchestrator(
            **e2e_fix_default_args
        )

        # Should only run 9 steps (1 cycle), NOT 18+ (2+ cycles)
        assert mock_run.call_count == 9, (
            f"Expected exactly 9 step calls (1 cycle only) but got {mock_run.call_count}. "
            f"Missing loop control token should break the loop, not default to CONTINUE_CYCLE."
        )

    def test_no_loop_control_token_logs_warning(self, e2e_fix_mock_dependencies, e2e_fix_default_args):
        """Step 9 with no control token should log a warning.

        The orchestrator should clearly indicate that no loop control token
        was found, rather than silently continuing.
        """
        mock_run, _, mock_console = e2e_fix_mock_dependencies
        e2e_fix_default_args["max_cycles"] = 2

        def side_effect(*args, **kwargs):
            label = kwargs.get('label', '')
            if 'step9' in label:
                return (True, "Verification complete. No token here.", 0.1, "gpt-4")
            return (True, f"Output for {label}", 0.1, "gpt-4")

        mock_run.side_effect = side_effect

        run_agentic_e2e_fix_orchestrator(**e2e_fix_default_args)

        # Verify a warning was logged about the missing token
        warning_logged = any(
            "No loop control token" in str(call) or "no loop control token" in str(call).lower()
            for call in mock_console.print.call_args_list
        )
        assert warning_logged, (
            "Expected a warning about missing loop control token in console output. "
            f"Console calls: {[str(c) for c in mock_console.print.call_args_list]}"
        )

    def test_continue_cycle_token_still_works(self, e2e_fix_mock_dependencies, e2e_fix_default_args):
        """CONTINUE_CYCLE token should still trigger another cycle.

        Regression guard: explicit CONTINUE_CYCLE should still cause a
        new cycle to start.
        """
        mock_run, _, _ = e2e_fix_mock_dependencies
        e2e_fix_default_args["max_cycles"] = 2

        call_count = 0

        def side_effect(*args, **kwargs):
            nonlocal call_count
            call_count += 1
            label = kwargs.get('label', '')
            if 'step9' in label:
                return (True, "Some tests still failing. CONTINUE_CYCLE", 0.1, "gpt-4")
            return (True, f"Output for {label}", 0.1, "gpt-4")

        mock_run.side_effect = side_effect

        run_agentic_e2e_fix_orchestrator(**e2e_fix_default_args)

        # Should run 2 full cycles = 18 steps
        assert mock_run.call_count == 18, (
            f"Expected 18 step calls (2 cycles) but got {mock_run.call_count}. "
            f"CONTINUE_CYCLE should still trigger another cycle."
        )

    def test_max_cycles_reached_token_still_works(self, e2e_fix_mock_dependencies, e2e_fix_default_args):
        """MAX_CYCLES_REACHED token should still allow natural loop exit.

        Regression guard: MAX_CYCLES_REACHED is informational and the loop
        should exit naturally via the max_cycles check.
        """
        mock_run, _, _ = e2e_fix_mock_dependencies
        e2e_fix_default_args["max_cycles"] = 1

        def side_effect(*args, **kwargs):
            label = kwargs.get('label', '')
            if 'step9' in label:
                return (True, "Max cycles reached. MAX_CYCLES_REACHED", 0.1, "gpt-4")
            return (True, f"Output for {label}", 0.1, "gpt-4")

        mock_run.side_effect = side_effect

        success, msg, cost, model, files = run_agentic_e2e_fix_orchestrator(
            **e2e_fix_default_args
        )

        # Should run exactly 9 steps (1 cycle), then exit naturally
        assert mock_run.call_count == 9, (
            f"Expected 9 step calls (1 cycle) but got {mock_run.call_count}."
        )


class TestIssue830SaveWorkflowStateOrchestratorIntegration:
    """Tests for issue #830 Bug 3: save_workflow_state failure masking.

    When save_workflow_state() fails to save to GitHub, it should return
    None (not the stale comment_id), so the orchestrator can detect the
    divergence.
    """

    def test_save_state_github_failure_returns_none_not_stale_id(self, e2e_fix_mock_dependencies, e2e_fix_default_args):
        """When GitHub save fails, save_workflow_state should return None.

        Bug: save_workflow_state returns the old github_comment_id when
        GitHub save fails, making the caller think the save succeeded.
        """
        mock_run, _, _ = e2e_fix_mock_dependencies
        e2e_fix_default_args["use_github_state"] = True
        e2e_fix_default_args["max_cycles"] = 1

        def side_effect(*args, **kwargs):
            label = kwargs.get('label', '')
            if 'step9' in label:
                return (True, "CONTINUE_CYCLE", 0.1, "gpt-4")
            return (True, f"Output for {label}", 0.1, "gpt-4")

        mock_run.side_effect = side_effect

        # Test the save_workflow_state function directly for this bug
        from pdd.agentic_common import save_workflow_state, github_save_state

        state = {"last_completed_step": 5, "step_outputs": {}}
        stale_comment_id = 12345

        with patch("pdd.agentic_common.github_save_state") as mock_gh_save, \
             patch("pdd.agentic_common._should_use_github_state") as mock_should:
            mock_should.return_value = True
            # GitHub save fails — returns None
            mock_gh_save.return_value = None

            result = save_workflow_state(
                cwd=e2e_fix_default_args["cwd"],
                issue_number=1,
                workflow_type="e2e_fix",
                state=state,
                state_dir=e2e_fix_default_args["cwd"] / ".pdd" / "state",
                repo_owner="owner",
                repo_name="repo",
                use_github_state=True,
                github_comment_id=stale_comment_id,
            )

        # Bug: returns stale_comment_id (12345) instead of None
        assert result is None or result != stale_comment_id, (
            f"save_workflow_state returned stale comment_id {result} when GitHub save failed. "
            f"Should return None to signal failure, not the old id {stale_comment_id}."
        )
