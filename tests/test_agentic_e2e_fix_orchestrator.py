"""Tests for agentic_e2e_fix_orchestrator prompt formatting and runtime behavior.

These tests verify that all e2e fix workflow prompts can be formatted
with the context variables provided by the orchestrator, without
raising KeyError on undefined placeholders.

Additionally, tests verify the orchestrator's runtime behavior including
early exit conditions (issue #468).
"""
import json
import re
import subprocess
import sys
from typing import Dict, Optional

import pytest
from unittest.mock import patch, MagicMock
from pathlib import Path

from pdd.load_prompt_template import load_prompt_template
from pdd.agentic_e2e_fix_orchestrator import _extract_test_files, _verify_tests_independently, _classify_verification_failure, _handle_verification_failure


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


def test_agentic_e2e_fix_orchestrator_example_runs_successfully():
    """The example should run against the current worktree without external setup."""
    repo_root = Path(__file__).resolve().parents[1]
    example_path = repo_root / "context" / "agentic_e2e_fix_orchestrator_example.py"

    result = subprocess.run(
        [sys.executable, str(example_path)],
        cwd=repo_root,
        capture_output=True,
        text=True,
        check=False,
    )

    combined_output = f"{result.stdout}\n{result.stderr}"
    assert result.returncode == 0, combined_output
    assert "Success: True" in combined_output, combined_output


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
    - _detect_changed_files: Returns ["module.py"] (simulate progress so
      per-cycle file-hash comparison doesn't block multi-cycle tests)
    - _commit_and_push: No-op (skip git operations)
    """
    with patch("pdd.agentic_e2e_fix_orchestrator.run_agentic_task") as mock_run, \
         patch("pdd.agentic_e2e_fix_orchestrator.load_prompt_template") as mock_load, \
         patch("pdd.agentic_e2e_fix_orchestrator.console") as mock_console, \
         patch("pdd.agentic_e2e_fix_orchestrator.load_workflow_state") as mock_load_state, \
         patch("pdd.agentic_e2e_fix_orchestrator.save_workflow_state") as mock_save_state, \
         patch("pdd.agentic_e2e_fix_orchestrator.clear_workflow_state") as mock_clear_state, \
         patch("pdd.agentic_e2e_fix_orchestrator._get_file_hashes") as mock_hashes, \
         patch("pdd.agentic_e2e_fix_orchestrator._detect_changed_files") as mock_detect, \
         patch("pdd.agentic_e2e_fix_orchestrator._commit_and_push") as mock_commit, \
         patch("pdd.agentic_e2e_fix_orchestrator._check_e2e_environment") as mock_check_e2e, \
         patch("pdd.agentic_e2e_fix_orchestrator.classify_step_output", return_value=None) as mock_classify, \
         patch("pdd.agentic_e2e_fix_orchestrator.post_final_comment") as mock_post_comment, \
         patch("pdd.agentic_e2e_fix_orchestrator._run_step11_code_cleanup", side_effect=lambda **kw: (kw["total_cost"], kw["changed_files"])):

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
        # Default: simulate file changes so per-cycle progress check passes
        mock_detect.return_value = ["module.py"]
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


class TestPushWithRetryNonFastForward:
    """Tests for _push_with_retry handling non-fast-forward push errors.

    When checkout_existing_issue_branch() rebases an issue branch onto
    origin/main, commit SHAs diverge from the remote branch. A plain
    `git push` fails with non-fast-forward. The fix should detect this
    and retry with --force-with-lease (safe force push).

    Regression test for issue #608 pdd fix failure.
    """

    def test_non_fast_forward_retries_with_force_with_lease(self, tmp_path):
        """Non-fast-forward push error should trigger --force-with-lease retry."""
        from pdd.agentic_e2e_fix_orchestrator import _push_with_retry

        calls = []

        def mock_run_side_effect(cmd, **kwargs):
            calls.append(cmd)
            result = type("Result", (), {"returncode": 0, "stdout": "", "stderr": ""})()

            if cmd == ["git", "push", "-u", "origin", "HEAD"]:
                result.returncode = 1
                result.stderr = (
                    "To https://github.com/owner/repo.git\n"
                    " ! [rejected]        HEAD -> fix/issue-608 (non-fast-forward)\n"
                    "error: failed to push some refs to 'https://github.com/owner/repo.git'\n"
                    "hint: Updates were rejected because the tip of your current branch is behind\n"
                    "hint: its remote counterpart."
                )
            return result

        with patch("pdd.agentic_e2e_fix_orchestrator.subprocess.run", side_effect=mock_run_side_effect):
            success, err = _push_with_retry(tmp_path, "owner", "repo")

        assert success is True, f"Expected success after --force-with-lease retry, got error: {err}"
        # Should have retried with --force-with-lease
        force_push_calls = [c for c in calls if "--force-with-lease" in c]
        assert len(force_push_calls) == 1, (
            f"Expected exactly one --force-with-lease retry, got {len(force_push_calls)}. "
            f"All calls: {calls}"
        )

    def test_non_fast_forward_logs_warning(self, tmp_path):
        """Non-fast-forward retry should log a warning via console.print."""
        from pdd.agentic_e2e_fix_orchestrator import _push_with_retry

        def mock_run_side_effect(cmd, **kwargs):
            result = type("Result", (), {"returncode": 0, "stdout": "", "stderr": ""})()
            if cmd == ["git", "push", "-u", "origin", "HEAD"]:
                result.returncode = 1
                result.stderr = (
                    " ! [rejected]        HEAD -> fix/issue-1 (non-fast-forward)\n"
                    "hint: Updates were rejected because the tip of your current branch is behind"
                )
            return result

        with patch("pdd.agentic_e2e_fix_orchestrator.subprocess.run", side_effect=mock_run_side_effect), \
             patch("pdd.agentic_e2e_fix_orchestrator.console") as mock_console:
            _push_with_retry(tmp_path, "owner", "repo")

        mock_console.print.assert_called()
        warning_text = mock_console.print.call_args[0][0]
        assert "yellow" in warning_text.lower() or "[yellow]" in warning_text
        assert "force-with-lease" in warning_text.lower() or "non-fast-forward" in warning_text.lower()

    def test_non_fast_forward_fetch_first_not_detected(self, tmp_path):
        """'fetch first' rejection (without non-fast-forward) should NOT trigger force-with-lease.

        Only specific non-fast-forward markers should trigger the retry,
        not generic [rejected] which could be protected branches or hooks.
        """
        from pdd.agentic_e2e_fix_orchestrator import _push_with_retry

        def mock_run_side_effect(cmd, **kwargs):
            result = type("Result", (), {"returncode": 0, "stdout": "", "stderr": ""})()
            if cmd == ["git", "push", "-u", "origin", "HEAD"]:
                result.returncode = 1
                result.stderr = (
                    " ! [rejected]        HEAD -> main (fetch first)\n"
                    "error: failed to push some refs\n"
                    "hint: Updates were rejected because the remote contains work that you do not\n"
                    "hint: have locally."
                )
            return result

        with patch("pdd.agentic_e2e_fix_orchestrator.subprocess.run", side_effect=mock_run_side_effect):
            success, err = _push_with_retry(tmp_path, "owner", "repo")

        # Should NOT retry — "fetch first" means remote has new work, force-push would lose it
        assert success is False

    def test_protected_branch_rejection_not_detected(self, tmp_path):
        """Protected branch rejection should NOT trigger force-with-lease retry."""
        from pdd.agentic_e2e_fix_orchestrator import _push_with_retry

        def mock_run_side_effect(cmd, **kwargs):
            result = type("Result", (), {"returncode": 0, "stdout": "", "stderr": ""})()
            if cmd == ["git", "push", "-u", "origin", "HEAD"]:
                result.returncode = 1
                result.stderr = (
                    " ! [remote rejected] HEAD -> main (protected branch hook declined)\n"
                    "error: failed to push some refs"
                )
            return result

        with patch("pdd.agentic_e2e_fix_orchestrator.subprocess.run", side_effect=mock_run_side_effect):
            success, err = _push_with_retry(tmp_path, "owner", "repo")

        assert success is False
        assert "protected branch" in err

    def test_non_fast_forward_force_with_lease_also_fails(self, tmp_path):
        """If --force-with-lease also fails, return the error."""
        from pdd.agentic_e2e_fix_orchestrator import _push_with_retry

        def mock_run_side_effect(cmd, **kwargs):
            result = type("Result", (), {"returncode": 0, "stdout": "", "stderr": ""})()

            if "push" in cmd:
                result.returncode = 1
                if "--force-with-lease" in cmd:
                    result.stderr = (
                        "! [rejected]        HEAD -> fix/issue-1 (stale info)\n"
                        "error: failed to push some refs (--force-with-lease)"
                    )
                else:
                    result.stderr = (
                        " ! [rejected]        HEAD -> fix/issue-1 (non-fast-forward)\n"
                        "hint: Updates were rejected because the tip of your current branch is behind"
                    )
            return result

        with patch("pdd.agentic_e2e_fix_orchestrator.subprocess.run", side_effect=mock_run_side_effect):
            success, err = _push_with_retry(tmp_path, "owner", "repo")

        assert success is False
        assert "force-with-lease" in err

    def test_non_fast_forward_takes_precedence_over_auth_retry(self, tmp_path, monkeypatch):
        """Non-fast-forward should be detected before auth failure check.

        An error containing both non-ff markers and auth-like text should
        be handled as non-fast-forward, not as an auth failure.
        """
        from pdd.agentic_e2e_fix_orchestrator import _push_with_retry

        # Set up a token file that should NOT be used for non-ff errors
        token_file = tmp_path / "gh_token"
        token_file.write_text("ghp_should_not_be_used")
        monkeypatch.setenv("PDD_GH_TOKEN_FILE", str(token_file))

        calls = []

        def mock_run_side_effect(cmd, **kwargs):
            calls.append(cmd)
            result = type("Result", (), {"returncode": 0, "stdout": "", "stderr": ""})()

            if cmd == ["git", "push", "-u", "origin", "HEAD"]:
                result.returncode = 1
                result.stderr = (
                    " ! [rejected]        HEAD -> fix/issue-1 (non-fast-forward)\n"
                    "hint: Updates were rejected because the tip of your current branch is behind\n"
                    "hint: its remote counterpart.\n"
                    "remote: HTTP 401: Unauthorized\n"
                    "fatal: Authentication failed for 'https://example.com/owner/repo.git'\n"
                )
            return result

        with patch("pdd.agentic_e2e_fix_orchestrator.subprocess.run", side_effect=mock_run_side_effect):
            success, err = _push_with_retry(tmp_path, "owner", "repo")

        assert success is True
        # Should NOT have called git remote set-url (auth retry path)
        set_url_calls = [c for c in calls if "set-url" in c]
        assert len(set_url_calls) == 0, (
            f"Non-fast-forward should not trigger auth retry. set-url calls: {set_url_calls}"
        )

    def test_commit_and_push_surfaces_force_push_success(self, tmp_path):
        """_commit_and_push should return success when _push_with_retry uses --force-with-lease."""
        from pdd.agentic_e2e_fix_orchestrator import _commit_and_push

        with patch("pdd.agentic_e2e_fix_orchestrator._get_file_hashes") as mock_hashes, \
             patch("pdd.agentic_e2e_fix_orchestrator._push_with_retry") as mock_push, \
             patch("pdd.agentic_e2e_fix_orchestrator.subprocess.run") as mock_run:

            # Simulate a file that changed during workflow
            mock_hashes.return_value = {"backend/functions/get_waitlist_status.py": "new_hash"}
            # Simulate _push_with_retry succeeding via --force-with-lease
            mock_push.return_value = (True, "")
            mock_run.return_value = type("Result", (), {"returncode": 0, "stdout": "", "stderr": ""})()

            success, message = _commit_and_push(
                cwd=tmp_path, issue_number=608,
                issue_title="Add fallback in get_waitlist_status.py",
                repo_owner="promptdriven", repo_name="pdd_cloud",
                initial_file_hashes={
                    "backend/functions/get_waitlist_status.py": "old_hash"
                },
                quiet=True
            )

        assert success is True
        assert "1 file(s)" in message
        mock_push.assert_called_once_with(tmp_path, "promptdriven", "pdd_cloud")


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

    @pytest.mark.parametrize("path", [
        ".pdd/backups/2026-03-09_123456/module.py",
        ".pdd/backups/2026-03-09_123456/test_module.py",
        ".pdd/core_dumps/pdd-core-abc123.json",
        ".pdd/debug/trace.json",
    ])
    def test_pdd_directory_artifacts_filtered(self, is_intermediate, path):
        """Artifacts under .pdd/ should be filtered (Issue #824)."""
        assert is_intermediate(path) is True

    @pytest.mark.parametrize("path", [
        "step3_output.md",
        "step9_output.md",
        "step12_output.md",
    ])
    def test_step_output_files_filtered(self, is_intermediate, path):
        """Workflow step output files should be filtered (Issue #824)."""
        assert is_intermediate(path) is True

    @pytest.mark.parametrize("path", [
        "waitlist_fix_errors.txt",
        "waitlist_test_errors.txt",
        "module_errors.txt",
        "auth_fix_errors.txt",
    ])
    def test_errors_txt_files_filtered(self, is_intermediate, path):
        """Workflow error logs ending in _errors.txt should be filtered."""
        assert is_intermediate(path) is True

    @pytest.mark.parametrize("path", [
        "test_issue_824_reproduction.py",
        "test_issue_383_reproduction.py",
        "test_issue_100_reproduction.py",
    ])
    def test_reproduction_test_files_filtered(self, is_intermediate, path):
        """Issue reproduction leftovers should be filtered (Issue #824)."""
        assert is_intermediate(path) is True

    # --- .pdd/e2e-fix-state/ must NOT be filtered (state files) ---

    @pytest.mark.parametrize("path", [
        ".pdd/e2e-fix-state/e2e_fix_state_824.json",
        ".pdd/e2e-fix-state/e2e_fix_state_830.json",
        ".pdd/e2e-fix-state/bug_state_824.json",
    ])
    def test_pdd_state_files_not_filtered(self, is_intermediate, path):
        """State files under .pdd/e2e-fix-state/ must NOT be filtered.

        The _is_intermediate_file filter catches .pdd/** artifacts, but
        state files are needed for workflow resume and must be preserved.
        """
        assert is_intermediate(path) is False, (
            f"State file {path} was incorrectly filtered as intermediate. "
            f".pdd/e2e-fix-state/ must be excluded from the .pdd/ catch-all."
        )

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
        ".pddrc",
        "pdd/step_handler.py",
        "tests/test_errors.py",
        "fixed_point_errors.log",
        "tests/test_issue_reproduction_helper.py",
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
    """Tests for issue #383/#824 intermediate file filtering in _commit_and_push.

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

    def test_commit_and_push_filters_issue824_artifact_files(self, mock_git_repo):
        """_commit_and_push should filter newer workflow artifacts (Issue #824)."""
        from unittest.mock import MagicMock
        from pdd.agentic_e2e_fix_orchestrator import _commit_and_push

        cwd = mock_git_repo
        artifact_files = [
            ".pdd/backups/2026-03-09_123456/module.py",
            ".pdd/core_dumps/pdd-core-abc123.json",
            "step9_output.md",
            "waitlist_fix_errors.txt",
            "waitlist_test_errors.txt",
            "test_issue_824_reproduction.py",
        ]
        legitimate_files = [
            "module.py",
            "tests/test_module.py",
        ]

        for filepath in artifact_files + legitimate_files:
            full_path = cwd / filepath
            full_path.parent.mkdir(parents=True, exist_ok=True)
            full_path.write_text(f"# {full_path.name}\n")

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
                issue_number=824,
                issue_title="Artifact filtering",
                repo_owner="test",
                repo_name="repo",
                initial_file_hashes=initial_hashes,
                quiet=True,
            )

        for filepath in legitimate_files:
            assert filepath in staged_files, f"Legitimate file {filepath} should be staged"
        for filepath in artifact_files:
            assert filepath not in staged_files, f"Artifact file {filepath} should NOT be staged"

    def test_commit_and_push_fallback_filters_issue824_artifacts(self, mock_git_repo):
        """Fallback staging path should apply the same Issue #824 filter."""
        from unittest.mock import MagicMock
        from pdd.agentic_e2e_fix_orchestrator import _commit_and_push, _get_file_hashes

        cwd = mock_git_repo
        legitimate_file = "module.py"
        artifact_files = [
            "step9_output.md",
            "waitlist_fix_errors.txt",
        ]

        for filepath in [legitimate_file] + artifact_files:
            full_path = cwd / filepath
            full_path.parent.mkdir(parents=True, exist_ok=True)
            full_path.write_text(f"# {full_path.name}\n")

        initial_hashes = _get_file_hashes(cwd)
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

        with patch(
            "pdd.agentic_e2e_fix_orchestrator._get_modified_and_untracked",
            return_value={legitimate_file, *artifact_files},
        ):
            with patch("subprocess.run", side_effect=mock_run):
                _commit_and_push(
                    cwd=cwd,
                    issue_number=824,
                    issue_title="Artifact filtering",
                    repo_owner="test",
                    repo_name="repo",
                    initial_file_hashes=initial_hashes,
                    quiet=True,
                )

        assert legitimate_file in staged_files, "Legitimate file should be staged via fallback"
        for filepath in artifact_files:
            assert filepath not in staged_files, f"Artifact file {filepath} should NOT be staged"

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

    # ── _extract_test_files: inline regex removed (issue #633) ──

    def test_extract_test_files_narrative_mentions_not_extracted(self, tmp_path):
        """Inline references in issue narrative should NOT be extracted.

        The inline regex was removed because it picked up files mentioned as
        examples, not just files to verify. Files should be discovered via
        markers, changed_files, or disk/git detection instead.
        """
        test_dir = tmp_path / "src" / "__test__"
        test_dir.mkdir(parents=True)
        (test_dir / "Button.test.tsx").touch()

        issue_content = "The test is at src/__test__/Button.test.tsx and it fails."

        result = _extract_test_files(issue_content, [], tmp_path)

        assert "src/__test__/Button.test.tsx" not in result

    def test_extract_test_files_does_not_match_narrative_examples(self, tmp_path):
        """Files mentioned as examples in issue narrative should NOT be extracted.

        Issue #633 mentioned link-github-save-navigation.spec.ts as an example
        of a broken test, and the regex incorrectly picked it up for verification.
        The inline regex should only match files from markers or changed_files,
        not from unstructured narrative text.
        """
        # The example file exists on disk (as it would in a real project)
        e2e_dir = tmp_path / "frontend" / "e2e" / "tests" / "settings"
        e2e_dir.mkdir(parents=True)
        (e2e_dir / "link-github-save-navigation.spec.ts").touch()

        issue_content = (
            "## Problem\n\n"
            "PDD bug step 11 generates Playwright E2E tests that look correct but contain subtle bugs.\n\n"
            "**Concrete example**: PR #627 generated `frontend/e2e/tests/settings/link-github-save-navigation.spec.ts` with 3 bugs.\n\n"
            "## Fix\n\nUpdate the step 11 prompt."
        )

        result = _extract_test_files(issue_content, [], tmp_path)

        assert "frontend/e2e/tests/settings/link-github-save-navigation.spec.ts" not in result

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
    @patch("pdd.agentic_e2e_fix_orchestrator.get_test_command_for_file")
    @patch("pdd.agentic_e2e_fix_orchestrator.run_pytest_and_capture_output")
    def test_verify_independently_does_not_use_pytest_for_tsx(self, mock_pytest, mock_get_cmd, mock_subproc, tmp_path):
        """Jest .test.tsx files should NOT be run through pytest.

        The current buggy code calls run_pytest_and_capture_output for ALL files,
        which fails silently for TypeScript. The fix should use an appropriate
        runner (e.g., npx jest) for .test.tsx files.
        """
        from pdd.get_test_command import TestCommand
        mock_get_cmd.return_value = TestCommand(command="npx jest src/__test__/Widget.test.tsx", cwd=None)
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
    @patch("pdd.agentic_e2e_fix_orchestrator.get_test_command_for_file")
    @patch("pdd.agentic_e2e_fix_orchestrator.run_pytest_and_capture_output")
    def test_verify_independently_does_not_use_pytest_for_spec_ts(self, mock_pytest, mock_get_cmd, mock_subproc, tmp_path):
        """Playwright .spec.ts files should NOT be run through pytest."""
        from pdd.get_test_command import TestCommand
        mock_get_cmd.return_value = TestCommand(command="npx playwright test e2e/login.spec.ts", cwd=None)
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


@pytest.mark.private_prompt
class TestIssue791PromptVerification:
    """Tests 1-2: Verify prompt specifies E2E pre-flight check and cross-cycle memory.

    Issue #791: The prompt should now include requirements for:
    1. _check_e2e_environment pre-flight check before Step 2
    2. skipped_steps cross-cycle memory to avoid retrying failed steps

    These tests check the full private _python.prompt (not synced to public repo).
    Marked private_prompt so public CI can skip them.
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

        # Should only run 1 cycle worth of steps plus a single Step 9 retry:
        # 9 initial steps + 1 retry call = 10 total, NOT 18+ (2+ full cycles).
        assert mock_run.call_count == 10, (
            f"Expected 10 step calls (1 cycle + Step 9 retry) but got {mock_run.call_count}. "
            "Missing loop control token should not start Cycle 2."
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


class TestStep9PromptRequiresControlToken:
    """The Step 9 prompt must explicitly require the LLM to emit a control token.

    Without a mandatory instruction, the LLM may write a valid verification
    summary but skip the control token entirely (as happened on issue #824),
    causing the orchestrator to treat it as a missing token and stop.
    """

    def test_step9_prompt_mandates_control_token(self):
        """The Step 9 prompt must contain a mandatory instruction to always
        emit exactly one of ALL_TESTS_PASS, CONTINUE_CYCLE, or MAX_CYCLES_REACHED."""
        from pdd.load_prompt_template import load_prompt_template

        prompt = load_prompt_template("agentic_e2e_fix_step9_verify_all_LLM")
        assert prompt is not None, "Could not load Step 9 prompt template"

        prompt_lower = prompt.lower()

        # Must contain a mandatory requirement, not just an informational note
        has_mandatory_language = any(phrase in prompt_lower for phrase in [
            "you must emit",
            "you must include",
            "you must output",
            "always emit",
            "required to emit",
            "mandatory",
            "must appear in your output",
            "must be present in your response",
            "your response must contain exactly one of",
            "always include exactly one",
        ])

        assert has_mandatory_language, (
            "Step 9 prompt does not contain mandatory language requiring the LLM to emit "
            "a control token. The current wording ('these strings control the outer loop') "
            "is informational, not imperative. The LLM can write a valid response without "
            "emitting any token, causing the orchestrator to stop with 'missing token'. "
            "Add explicit mandatory instruction like 'You MUST include exactly one of "
            "ALL_TESTS_PASS, CONTINUE_CYCLE, or MAX_CYCLES_REACHED in your response.'"
        )


# ---------------------------------------------------------------------------
# _classify_step_output — semantic fallback for control tokens (Issue #865)
# ---------------------------------------------------------------------------

class TestClassifyStepOutput:
    """Test semantic fallback when LLMs don't emit exact control tokens."""

    def test_exact_token_local_tests_pass(self):
        from pdd.agentic_e2e_fix_orchestrator import _classify_step_output
        assert _classify_step_output("**Status:** LOCAL_TESTS_PASS", step_num=9) == "LOCAL_TESTS_PASS"

    def test_exact_token_all_tests_pass(self):
        from pdd.agentic_e2e_fix_orchestrator import _classify_step_output
        # Step 9 normalizes ALL_TESTS_PASS to LOCAL_TESTS_PASS
        assert _classify_step_output("**Status:** ALL_TESTS_PASS", step_num=9) == "LOCAL_TESTS_PASS"

    def test_exact_token_continue_cycle(self):
        from pdd.agentic_e2e_fix_orchestrator import _classify_step_output
        assert _classify_step_output("CONTINUE_CYCLE", step_num=9) == "CONTINUE_CYCLE"

    def test_exact_token_max_cycles_reached(self):
        from pdd.agentic_e2e_fix_orchestrator import _classify_step_output
        assert _classify_step_output("MAX_CYCLES_REACHED", step_num=9) == "MAX_CYCLES_REACHED"

    def test_exact_token_not_a_bug(self):
        from pdd.agentic_e2e_fix_orchestrator import _classify_step_output
        assert _classify_step_output("NOT_A_BUG", step_num=3) == "NOT_A_BUG"

    def test_semantic_all_tests_passed_step9(self):
        """Real Step 9 output from pdd_cloud#673 — says tests pass but no token."""
        from pdd.agentic_e2e_fix_orchestrator import _classify_step_output
        output = (
            "The fix appears complete for issue #673. "
            "full extensions/github_pdd_app/tests: 788 passed, 25 skipped. "
            "no additional cycle is indicated from test results."
        )
        assert _classify_step_output(output, step_num=9) == "LOCAL_TESTS_PASS"

    def test_semantic_all_n_tests_pass(self):
        from pdd.agentic_e2e_fix_orchestrator import _classify_step_output
        output = "All 18 tests pass. The fix is complete."
        assert _classify_step_output(output, step_num=9) == "LOCAL_TESTS_PASS"

    def test_semantic_tests_still_failing(self):
        from pdd.agentic_e2e_fix_orchestrator import _classify_step_output
        output = "3 tests still failing. Need another cycle to fix the remaining issues."
        assert _classify_step_output(output, step_num=9) == "CONTINUE_CYCLE"

    def test_semantic_not_a_bug_paraphrase(self):
        from pdd.agentic_e2e_fix_orchestrator import _classify_step_output
        output = "This is not a bug. The behavior is working as intended."
        assert _classify_step_output(output, step_num=3) == "NOT_A_BUG"

    def test_semantic_already_fixed(self):
        from pdd.agentic_e2e_fix_orchestrator import _classify_step_output
        output = "The issue is already fixed on this branch. Both tests passed."
        assert _classify_step_output(output, step_num=3) == "NOT_A_BUG"

    def test_ambiguous_returns_none(self):
        from pdd.agentic_e2e_fix_orchestrator import _classify_step_output
        output = "I analyzed the code and found several potential issues."
        assert _classify_step_output(output, step_num=9) is None

    def test_verification_failed_not_classified_as_pass(self):
        from pdd.agentic_e2e_fix_orchestrator import _classify_step_output
        output = "VERIFICATION_FAILED: LLM claimed LOCAL_TESTS_PASS but pytest failed.\n5 tests failed."
        assert _classify_step_output(output, step_num=9) != "LOCAL_TESTS_PASS"

    def test_step1_all_tests_pass(self):
        from pdd.agentic_e2e_fix_orchestrator import _classify_step_output
        output = "Verified with npx jest... both passed. All tests are passing."
        assert _classify_step_output(output, step_num=1) == "ALL_TESTS_PASS"

    def test_mixed_pass_fail_not_classified_as_pass(self):
        """If some tests fail, don't classify as pass even if 'passed' appears."""
        from pdd.agentic_e2e_fix_orchestrator import _classify_step_output
        output = "18 passed, 3 failed. The fix needs more work."
        assert _classify_step_output(output, step_num=9) != "LOCAL_TESTS_PASS"


class TestClassifyStepOutputCodeBugPriority:
    """Bug: _classify_step_output for step 3 only checks for NOT_A_BUG, missing
    CODE_BUG/TEST_BUG/BOTH. When the LLM correctly emits CODE_BUG, tiers 1-3
    return None, and tier 4 misclassifies as NOT_A_BUG — killing the workflow.

    Fix: check positive tokens (CODE_BUG, TEST_BUG, BOTH) before NOT_A_BUG,
    matching the fail-before-pass pattern used for Steps 1/2/9.
    """

    def test_code_bug_detected_in_step3(self):
        """When Step 3 output contains CODE_BUG, return it (not None)."""
        from pdd.agentic_e2e_fix_orchestrator import _classify_step_output
        output = "## Step 3: Root Cause Analysis (Cycle 1)\n\n**Status:** CODE_BUG\n\n### Failure Analysis\n..."
        assert _classify_step_output(output, step_num=3) == "CODE_BUG"

    def test_test_bug_detected_in_step3(self):
        """When Step 3 output contains TEST_BUG, return it."""
        from pdd.agentic_e2e_fix_orchestrator import _classify_step_output
        output = "**Status:** TEST_BUG\n\nThe test expectations are wrong."
        assert _classify_step_output(output, step_num=3) == "TEST_BUG"

    def test_both_detected_in_step3(self):
        """When Step 3 output contains BOTH, return it."""
        from pdd.agentic_e2e_fix_orchestrator import _classify_step_output
        output = "**Status:** BOTH\n\nCode and tests both need fixing."
        assert _classify_step_output(output, step_num=3) == "BOTH"

    def test_code_bug_prevents_not_a_bug_false_positive(self):
        """Real failure case: long output with CODE_BUG at top and 'not caused
        by the bug' language in the tail. Must return CODE_BUG, not None."""
        from pdd.agentic_e2e_fix_orchestrator import _classify_step_output
        output = (
            "## Step 3: Root Cause Analysis (Cycle 1)\n\n"
            "**Status:** CODE_BUG\n\n"
            "### Failure Analysis\n\n"
            "The Step 2 full-suite run reported failures across multiple test files. "
            "I categorized every failure and traced each to its root cause. "
            "**None are caused by the issue #449 fix** — they are all pre-existing.\n\n"
            "#### Category A: `python` binary not found (6 tests)\n"
            "- **Root cause:** Pre-existing environment issue.\n\n"
            "#### Category B: Missing `pytest-mock` package (94 errors)\n"
            "- **Root cause:** Pre-existing dependency issue.\n\n"
            "### Root Cause\n\n"
            "The **code bug** is confirmed and localized.\n"
            "No test fixes needed — the issue #449 tests are correctly written.\n"
            "The 111 other failures are pre-existing environmental issues.\n"
        )
        result = _classify_step_output(output, step_num=3)
        assert result == "CODE_BUG", (
            f"Expected CODE_BUG but got {result!r}. "
            "Tier 4 would misclassify this as NOT_A_BUG because the tail "
            "discusses 'not caused by the bug' — but CODE_BUG at the top "
            "should take priority."
        )

    def test_not_a_bug_still_works(self):
        """Regression: NOT_A_BUG detection still works when no positive token present."""
        from pdd.agentic_e2e_fix_orchestrator import _classify_step_output
        assert _classify_step_output("NOT_A_BUG", step_num=3) == "NOT_A_BUG"

    def test_code_bug_takes_priority_over_not_a_bug(self):
        """If both CODE_BUG and NOT_A_BUG appear, CODE_BUG wins (checked first)."""
        from pdd.agentic_e2e_fix_orchestrator import _classify_step_output
        output = "**Status:** CODE_BUG\n\nNote: this is NOT_A_BUG for the unrelated issue."
        assert _classify_step_output(output, step_num=3) == "CODE_BUG"


class TestIssue673CheckE2ESubdirectory:
    """Bug: _check_e2e_environment only checks repo root for playwright config.

    In pdd_cloud, playwright.config.ts lives at frontend/playwright.config.ts.
    The current check only looks at cwd/ and misses subdirectory configs,
    causing Step 2 to be skipped unnecessarily.
    """

    def test_detects_playwright_config_in_frontend_subdir(self, tmp_path):
        """_check_e2e_environment should find playwright.config.ts in frontend/."""
        from pdd.agentic_e2e_fix_orchestrator import _check_e2e_environment

        (tmp_path / "frontend").mkdir()
        (tmp_path / "frontend" / "playwright.config.ts").write_text("export default {}")

        with patch("pdd.agentic_e2e_fix_orchestrator.shutil.which", return_value="/usr/bin/npx"):
            available, reason = _check_e2e_environment(tmp_path)

        assert available is True, (
            f"Should detect playwright.config.ts in frontend/ subdirectory. "
            f"Got reason: {reason}"
        )

    def test_detects_playwright_config_in_e2e_subdir(self, tmp_path):
        """_check_e2e_environment should find playwright.config.ts in e2e/."""
        from pdd.agentic_e2e_fix_orchestrator import _check_e2e_environment

        (tmp_path / "e2e").mkdir()
        (tmp_path / "e2e" / "playwright.config.js").write_text("module.exports = {}")

        with patch("pdd.agentic_e2e_fix_orchestrator.shutil.which", return_value="/usr/bin/npx"):
            available, reason = _check_e2e_environment(tmp_path)

        assert available is True, (
            f"Should detect playwright.config.js in e2e/ subdirectory. "
            f"Got reason: {reason}"
        )

    def test_still_returns_false_when_no_config_anywhere(self, tmp_path):
        """_check_e2e_environment still returns False when no config exists at all."""
        from pdd.agentic_e2e_fix_orchestrator import _check_e2e_environment

        (tmp_path / "frontend").mkdir()
        (tmp_path / "src").mkdir()
        # No playwright config anywhere

        with patch("pdd.agentic_e2e_fix_orchestrator.shutil.which", return_value="/usr/bin/npx"):
            available, reason = _check_e2e_environment(tmp_path)

        assert available is False

    def test_does_not_crash_on_nonexistent_cwd(self):
        """_check_e2e_environment should return False, not crash, for non-existent paths."""
        from pdd.agentic_e2e_fix_orchestrator import _check_e2e_environment

        with patch("pdd.agentic_e2e_fix_orchestrator.shutil.which", return_value="/usr/bin/npx"):
            available, reason = _check_e2e_environment(Path("/nonexistent/path"))

        assert available is False


class TestIssue673SkippedStepEarlyExit:
    """Bug: Early exit when Step 1 passes + Step 2 skipped is unreachable on Cycle 2+.

    On Cycle 1, Step 2 is skipped via _check_e2e_environment (which adds to
    skipped_steps). On Cycle 2+, Step 2 is skipped via the skipped_steps block,
    which has NO early exit check. So even when Step 1 says ALL_TESTS_PASS,
    the workflow falls through to Step 3+ wasting cycles.
    """

    def test_early_exit_when_step1_passes_and_step2_skipped_cycle1(
        self, e2e_fix_mock_dependencies, e2e_fix_default_args
    ):
        """When Step 1 ALL_TESTS_PASS and Step 2 is E2E_SKIP, exit early on Cycle 1."""
        mock_run, _, _ = e2e_fix_mock_dependencies

        # Step 1 returns ALL_TESTS_PASS
        mock_run.return_value = (True, "**Status:** ALL_TESTS_PASS\n792 passed, 0 failed", 0.1, "gpt-4")

        # Mock _check_e2e_environment to skip Step 2
        with patch("pdd.agentic_e2e_fix_orchestrator._check_e2e_environment", return_value=(False, "no playwright config found in project")), \
             patch("pdd.agentic_e2e_fix_orchestrator._extract_test_files", return_value=[]), \
             patch("pdd.agentic_e2e_fix_orchestrator.post_final_comment"):

            success, msg, cost, model, files = run_agentic_e2e_fix_orchestrator(
                **e2e_fix_default_args
            )

        assert success is True, f"Should succeed when Step 1 passes and Step 2 skipped. msg={msg}"
        assert mock_run.call_count == 1, (
            f"Expected only 1 LLM call (Step 1) but got {mock_run.call_count}. "
            f"Workflow should exit early, not fall through to Step 3+."
        )

    def test_early_exit_when_step1_passes_and_step2_skipped_cycle2(
        self, e2e_fix_mock_dependencies, e2e_fix_default_args
    ):
        """On Cycle 2, Step 2 is skipped via skipped_steps — early exit must still fire.

        This is the critical bug: skipped_steps path (line 960) bypasses the
        _check_e2e_environment block where the early exit lives, so on Cycle 2+
        the early exit never fires.
        """
        mock_run, _, _ = e2e_fix_mock_dependencies

        call_count = 0
        def side_effect(*args, **kwargs):
            nonlocal call_count
            call_count += 1
            label = kwargs.get('label', '')
            # Cycle 1: Step 1 fails (tests not passing yet)
            if 'cycle1_step1' in label:
                return (True, "**Status:** CODE_BUG\n3 tests failing", 0.1, "gpt-4")
            # Cycle 1: Steps 3-9 run normally, Step 9 says CONTINUE_CYCLE
            if 'cycle1_step9' in label:
                return (True, "**Status:** CONTINUE_CYCLE\n3 tests still failing", 0.1, "gpt-4")
            # Cycle 2: Step 1 passes (fix was applied)
            if 'cycle2_step1' in label:
                return (True, "**Status:** ALL_TESTS_PASS\n792 passed, 0 failed", 0.1, "gpt-4")
            # All other steps return generic output
            return (True, f"Output for {label}", 0.1, "gpt-4")

        mock_run.side_effect = side_effect

        # Step 2 skipped from Cycle 1
        with patch("pdd.agentic_e2e_fix_orchestrator._check_e2e_environment", return_value=(False, "no playwright config found in project")), \
             patch("pdd.agentic_e2e_fix_orchestrator._extract_test_files", return_value=[]), \
             patch("pdd.agentic_e2e_fix_orchestrator.post_final_comment"):

            success, msg, cost, model, files = run_agentic_e2e_fix_orchestrator(
                **e2e_fix_default_args
            )

        # Cycle 2 should exit early at Step 2 skip, not continue to Step 3+
        cycle2_labels = [c.kwargs.get('label', '') for c in mock_run.call_args_list if 'cycle2' in c.kwargs.get('label', '')]
        assert success is True, f"Should succeed when Cycle 2 Step 1 passes. msg={msg}"
        # Only cycle2_step1 should run — after that, Step 2 skip + early exit
        cycle2_step_count = len(cycle2_labels)
        assert cycle2_step_count == 1, (
            f"Expected only 1 LLM call in Cycle 2 (Step 1) but got {cycle2_step_count}: {cycle2_labels}. "
            f"Step 2 skip via skipped_steps should trigger early exit."
        )


class TestIssue673NotABugAfterFixesApplied:
    """Bug: NOT_A_BUG is allowed on Cycle 2+ even after fixes were applied.

    In pdd_cloud#673, the workflow applied fixes in Cycle 1, verified them
    in Cycle 2, but then on Cycle 4 Step 3 misclassified an E2E infrastructure
    issue as NOT_A_BUG, stopping the workflow with the wrong exit message.
    """

    def test_not_a_bug_blocked_after_fixes_applied(
        self, e2e_fix_mock_dependencies, e2e_fix_default_args
    ):
        """NOT_A_BUG should be ignored when dev_unit_states has fixed units.

        If the workflow already applied fixes (dev_unit_states has entries
        marked as fixed), NOT_A_BUG in Step 3 should be treated as
        CONTINUE_CYCLE, not as a workflow terminator.
        """
        mock_run, _, _ = e2e_fix_mock_dependencies

        def side_effect(*args, **kwargs):
            label = kwargs.get('label', '')
            # Cycle 1: normal flow, Step 8 reports fixes applied
            if 'cycle1_step5' in label:
                return (True, "DEV_UNITS_IDENTIFIED: firestore_client, installation_service", 0.1, "gpt-4")
            if 'cycle1_step8' in label:
                return (True, "firestore_client: FIXED — added delete_installation\ninstallation_service: FIXED — added deduplication", 0.1, "gpt-4")
            if 'cycle1_step9' in label:
                return (True, "**Status:** CONTINUE_CYCLE\n2 tests still failing", 0.1, "gpt-4")
            # Cycle 2: Step 3 says NOT_A_BUG (the bug we're testing)
            if 'cycle2_step3' in label:
                return (True, "**Status:** NOT_A_BUG\nThis is not a bug, the E2E skip is an infrastructure issue.", 0.1, "gpt-4")
            return (True, f"Output for {label}", 0.1, "gpt-4")

        mock_run.side_effect = side_effect

        with patch("pdd.agentic_e2e_fix_orchestrator._extract_test_files", return_value=[]), \
             patch("pdd.agentic_e2e_fix_orchestrator.post_final_comment"):

            success, msg, cost, model, files = run_agentic_e2e_fix_orchestrator(
                **e2e_fix_default_args
            )

        # The workflow should NOT have stopped with "not a bug" — fixes were already applied
        assert "not a bug" not in msg.lower(), (
            f"NOT_A_BUG should be blocked after fixes were applied in Cycle 1. "
            f"Got: {msg}"
        )


class TestDetectControlTokenUnit:
    """Unit tests for detect_control_token from shared agentic_common."""

    def test_exact_match(self):
        from pdd.agentic_common import detect_control_token
        assert detect_control_token("Status: ALL_TESTS_PASS", "ALL_TESTS_PASS")

    def test_case_insensitive_match(self):
        from pdd.agentic_common import detect_control_token
        assert detect_control_token("Status: all_tests_pass", "ALL_TESTS_PASS")
        assert detect_control_token("Status: Not_A_Bug", "NOT_A_BUG")

    def test_empty_output(self):
        from pdd.agentic_common import detect_control_token
        assert not detect_control_token("", "ALL_TESTS_PASS")
        assert not detect_control_token(None, "ALL_TESTS_PASS")

    def test_semantic_all_tests_pass_patterns(self):
        from pdd.agentic_common import detect_control_token
        assert detect_control_token("all 18 tests pass", "ALL_TESTS_PASS")
        assert detect_control_token("18/18 passing", "ALL_TESTS_PASS")
        assert detect_control_token("both passed", "ALL_TESTS_PASS")
        assert detect_control_token("all tests are green", "ALL_TESTS_PASS")
        assert detect_control_token("All tests passed successfully", "ALL_TESTS_PASS")
        assert detect_control_token("100% passing", "ALL_TESTS_PASS")

    def test_semantic_not_a_bug_patterns(self):
        from pdd.agentic_common import detect_control_token
        assert detect_control_token("this is not a bug", "NOT_A_BUG")
        assert detect_control_token("it is already fixed", "NOT_A_BUG")
        assert detect_control_token("expected behavior", "NOT_A_BUG")
        assert detect_control_token("working correctly", "NOT_A_BUG")
        assert detect_control_token("working as designed", "NOT_A_BUG")
        assert detect_control_token("not actually a code issue", "NOT_A_BUG")

    def test_semantic_continue_cycle_patterns(self):
        from pdd.agentic_common import detect_control_token
        assert detect_control_token("tests still failing", "CONTINUE_CYCLE")
        assert detect_control_token("more work needed", "CONTINUE_CYCLE")
        assert detect_control_token("not yet fixed", "CONTINUE_CYCLE")

    def test_semantic_max_cycles_patterns(self):
        from pdd.agentic_common import detect_control_token
        assert detect_control_token("max cycles reached", "MAX_CYCLES_REACHED")
        assert detect_control_token("maximum cycle limit exceeded", "MAX_CYCLES_REACHED")

    def test_no_false_positive_on_unrelated_text(self):
        from pdd.agentic_common import detect_control_token
        assert not detect_control_token("I'm investigating the test failures", "ALL_TESTS_PASS")
        assert not detect_control_token("The bug is in the authentication module", "NOT_A_BUG")
        assert not detect_control_token("I'll fix this in the next step", "CONTINUE_CYCLE")

    def test_unknown_token_only_uses_exact_and_case_insensitive(self):
        from pdd.agentic_common import detect_control_token
        assert detect_control_token("CUSTOM_TOKEN", "CUSTOM_TOKEN")
        assert detect_control_token("custom_token", "CUSTOM_TOKEN")
        assert not detect_control_token("something else", "CUSTOM_TOKEN")


class TestClassifyStepOutputWiring:
    """Item 1: classify_step_output must be called as tier-4 fallback in the orchestrator."""

    @patch("pdd.agentic_e2e_fix_orchestrator.classify_step_output")
    def test_step9_calls_classify_when_tiers123_fail(
        self, mock_classify, e2e_fix_mock_dependencies, e2e_fix_default_args
    ):
        """When Step 9 output has no token detectable by tiers 1-3,
        the orchestrator should call classify_step_output as tier 4."""
        from pdd.agentic_e2e_fix_orchestrator import run_agentic_e2e_fix_orchestrator
        from pdd.agentic_common import TokenMatch

        mock_run, _, _ = e2e_fix_mock_dependencies

        # Return None for Step 3 classify (not a bug), TokenMatch for Step 9
        def classify_side_effect(output, tokens, **kwargs):
            if "ALL_TESTS_PASS" in tokens:
                return TokenMatch(tier="llm_classification", token="CONTINUE_CYCLE")
            return None

        mock_classify.side_effect = classify_side_effect

        def side_effect(*args, **kwargs):
            label = kwargs.get('label', '')
            if 'step9' in label:
                # Output with no token and no semantic match
                return (True, "I ran the tests. Here are the results.", 0.1, "gpt-4")
            return (True, "Step output", 0.1, "gpt-4")

        mock_run.side_effect = side_effect
        run_agentic_e2e_fix_orchestrator(**e2e_fix_default_args)

        # Should have been called for Step 9 (and possibly Step 3)
        step9_calls = [
            c for c in mock_classify.call_args_list
            if "ALL_TESTS_PASS" in c[0][1]
        ]
        assert len(step9_calls) >= 1, (
            f"Expected classify_step_output to be called with ALL_TESTS_PASS for Step 9. "
            f"Calls: {mock_classify.call_args_list}"
        )

    @patch("pdd.agentic_e2e_fix_orchestrator.classify_step_output")
    def test_step9_classify_prevents_safety_stop(
        self, mock_classify, e2e_fix_mock_dependencies, e2e_fix_default_args
    ):
        """If classify_step_output returns a match, orchestrator should continue
        cycling instead of triggering the safety stop."""
        from pdd.agentic_e2e_fix_orchestrator import run_agentic_e2e_fix_orchestrator
        from pdd.agentic_common import TokenMatch

        mock_run, _, _ = e2e_fix_mock_dependencies
        e2e_fix_default_args["max_cycles"] = 2

        cycle = [0]

        def classify_side_effect(output, tokens, **kwargs):
            if "ALL_TESTS_PASS" in tokens:
                return TokenMatch(tier="llm_classification", token="CONTINUE_CYCLE")
            return None

        mock_classify.side_effect = classify_side_effect

        def side_effect(*args, **kwargs):
            label = kwargs.get('label', '')
            if 'step9' in label:
                cycle[0] += 1
                if cycle[0] >= 2:
                    return (True, "ALL_TESTS_PASS", 0.1, "gpt-4")
                return (True, "I verified everything looks good.", 0.1, "gpt-4")
            return (True, "Step output", 0.1, "gpt-4")

        mock_run.side_effect = side_effect
        success, msg, _, _, _ = run_agentic_e2e_fix_orchestrator(**e2e_fix_default_args)

        # Classify prevented safety stop on cycle 1, exact match succeeded on cycle 2
        assert mock_run.call_count > 9, (
            f"Expected >9 calls (classify should prevent safety stop and allow cycle 2) "
            f"but got {mock_run.call_count}. msg={msg}"
        )

    @patch("pdd.agentic_e2e_fix_orchestrator.classify_step_output")
    def test_step9_classify_not_called_when_tier1_matches(
        self, mock_classify, e2e_fix_mock_dependencies, e2e_fix_default_args
    ):
        """classify_step_output should NOT be called when exact match succeeds at Step 9."""
        from pdd.agentic_e2e_fix_orchestrator import run_agentic_e2e_fix_orchestrator

        mock_run, _, _ = e2e_fix_mock_dependencies

        def side_effect(*args, **kwargs):
            label = kwargs.get('label', '')
            if 'step9' in label:
                return (True, "ALL_TESTS_PASS", 0.1, "gpt-4")
            return (True, "Step output", 0.1, "gpt-4")

        mock_run.side_effect = side_effect
        run_agentic_e2e_fix_orchestrator(**e2e_fix_default_args)

        # classify may be called for Step 3 (no exact token), but NOT for Step 9
        step9_calls = [
            c for c in mock_classify.call_args_list
            if "ALL_TESTS_PASS" in c[0][1]
        ]
        assert len(step9_calls) == 0, (
            f"classify_step_output should not be called for Step 9 when exact match succeeds. "
            f"Step 9 calls: {step9_calls}"
        )

    @patch("pdd.agentic_e2e_fix_orchestrator.classify_step_output")
    def test_step3_calls_classify_when_tiers123_fail(
        self, mock_classify, e2e_fix_mock_dependencies, e2e_fix_default_args
    ):
        """When Step 3 output has no NOT_A_BUG detectable by tiers 1-3,
        classify_step_output should be called."""
        from pdd.agentic_e2e_fix_orchestrator import run_agentic_e2e_fix_orchestrator
        from pdd.agentic_common import TokenMatch

        mock_run, _, _ = e2e_fix_mock_dependencies
        mock_classify.return_value = TokenMatch(tier="llm_classification", token="NOT_A_BUG")

        def side_effect(*args, **kwargs):
            label = kwargs.get('label', '')
            if 'step3' in label:
                return (True, "The issue has already been addressed upstream.", 0.1, "gpt-4")
            return (True, "Step output", 0.1, "gpt-4")

        mock_run.side_effect = side_effect
        success, msg, _, _, _ = run_agentic_e2e_fix_orchestrator(**e2e_fix_default_args)

        mock_classify.assert_called_once()

    @patch("pdd.agentic_e2e_fix_orchestrator.classify_step_output")
    def test_step9_classify_failure_falls_through_to_safety_stop(
        self, mock_classify, e2e_fix_mock_dependencies, e2e_fix_default_args
    ):
        """If classify_step_output returns confident NONE, safety stop should still trigger."""
        from pdd.agentic_e2e_fix_orchestrator import run_agentic_e2e_fix_orchestrator

        mock_run, _, _ = e2e_fix_mock_dependencies
        mock_classify.return_value = None

        def side_effect(*args, **kwargs):
            label = kwargs.get('label', '')
            if 'step9' in label:
                return (True, "Ambiguous results.", 0.1, "gpt-4")
            return (True, "Step output", 0.1, "gpt-4")

        mock_run.side_effect = side_effect
        success, msg, _, _, _ = run_agentic_e2e_fix_orchestrator(**e2e_fix_default_args)

        assert "no loop control token" in msg.lower() or "stopped" in msg.lower()

    @patch("pdd.agentic_e2e_fix_orchestrator.classify_step_output")
    def test_step9_classify_error_continues_cycle(
        self, mock_classify, e2e_fix_mock_dependencies, e2e_fix_default_args
    ):
        """If tier-4 classifier fails, Step 9 should continue cycle (not terminal-stop)."""
        from pdd.agentic_e2e_fix_orchestrator import run_agentic_e2e_fix_orchestrator
        from pdd.agentic_common import TokenMatch

        mock_run, _, _ = e2e_fix_mock_dependencies
        e2e_fix_default_args["max_cycles"] = 2
        cycle = [0]

        def classify_side_effect(output, tokens, **kwargs):
            if "ALL_TESTS_PASS" in tokens:
                return TokenMatch(tier="llm_classification_error", token="CLASSIFICATION_ERROR")
            return None

        mock_classify.side_effect = classify_side_effect

        def side_effect(*args, **kwargs):
            label = kwargs.get("label", "")
            if "step9" in label:
                cycle[0] += 1
                if cycle[0] >= 2:
                    return (True, "ALL_TESTS_PASS", 0.1, "gpt-4")
                return (True, "Ambiguous results.", 0.1, "gpt-4")
            return (True, "Step output", 0.1, "gpt-4")

        mock_run.side_effect = side_effect
        success, msg, _, _, _ = run_agentic_e2e_fix_orchestrator(**e2e_fix_default_args)

        assert success is True, f"Expected cycle to continue after classifier error, got msg={msg}"


class TestSemanticTierConsoleLogging:
    """Item 6: Console should log when semantic tier (tier 3) fires."""

    def test_semantic_match_logs_to_console(self, e2e_fix_mock_dependencies, e2e_fix_default_args):
        """When semantic fallback detects a token, console should print a notice."""
        from pdd.agentic_e2e_fix_orchestrator import run_agentic_e2e_fix_orchestrator

        mock_run, _, mock_console = e2e_fix_mock_dependencies

        def side_effect(*args, **kwargs):
            label = kwargs.get('label', '')
            if 'step3' in label:
                # Triggers semantic match, no exact token
                return (True, "After investigation, this is not a bug.", 0.1, "gpt-4")
            return (True, "Step output", 0.1, "gpt-4")

        mock_run.side_effect = side_effect
        run_agentic_e2e_fix_orchestrator(**e2e_fix_default_args)

        console_output = " ".join(str(c) for c in mock_console.print.call_args_list)
        assert "semantic" in console_output.lower(), (
            f"Expected console log about semantic detection but got: {console_output}"
        )


class TestParseDevUnitsMarkerDistinction:
    """Tests for _parse_dev_units to ensure it distinguishes absent vs empty markers."""

    def test_parse_dev_units_returns_none_when_marker_absent(self):
        from pdd.agentic_e2e_fix_orchestrator import _parse_dev_units
        output = "Analysis complete. I found some issues in the auth module."
        assert _parse_dev_units(output) is None

    def test_parse_dev_units_returns_empty_when_marker_present_but_empty(self):
        from pdd.agentic_e2e_fix_orchestrator import _parse_dev_units
        output = "DEV_UNITS_IDENTIFIED: \nI found no issues."
        assert _parse_dev_units(output) == ""

    def test_parse_dev_units_returns_zero_when_marker_says_zero(self):
        from pdd.agentic_e2e_fix_orchestrator import _parse_dev_units
        output = "DEV_UNITS_IDENTIFIED: 0"
        assert _parse_dev_units(output) == "0"

    def test_parse_dev_units_returns_value_when_marker_has_units(self):
        from pdd.agentic_e2e_fix_orchestrator import _parse_dev_units
        output = "DEV_UNITS_IDENTIFIED: auth_service, login_tests"
        assert _parse_dev_units(output) == "auth_service, login_tests"


class TestEmptyDevUnitsShortCircuit:
    """Issue #903: When Step 5 returns 0 dev units, Steps 6-8 should be skipped
    and the cycle loop should break immediately."""

    def test_zero_dev_units_skips_steps_6_through_8(self, e2e_fix_mock_dependencies, e2e_fix_default_args):
        """When Step 5 returns 'DEV_UNITS_IDENTIFIED: 0', steps 6-8 must not run."""
        from pdd.agentic_e2e_fix_orchestrator import run_agentic_e2e_fix_orchestrator

        mock_run, _, _ = e2e_fix_mock_dependencies
        e2e_fix_default_args["max_cycles"] = 1

        def side_effect(*args, **kwargs):
            label = kwargs.get('label', '')
            if 'step5' in label:
                return (True, "Analysis complete.\nDEV_UNITS_IDENTIFIED: 0\nNo dev units need fixing.", 0.1, "gpt-4")
            if 'step9' in label:
                return (True, "ALL_TESTS_PASS", 0.1, "gpt-4")
            return (True, f"Output for {label}", 0.1, "gpt-4")

        mock_run.side_effect = side_effect

        run_agentic_e2e_fix_orchestrator(**e2e_fix_default_args)

        # Steps 6, 7, 8 should be skipped when dev units = 0.
        # Only steps 1-5 should run (5 calls), then cycle breaks.
        step_labels = [call.kwargs.get('label', '') for call in mock_run.call_args_list]
        steps_that_ran = [label for label in step_labels if any(f'step{s}' in label for s in [6, 7, 8])]
        assert len(steps_that_ran) == 0, (
            f"Steps 6-8 should be skipped when dev units = 0, but these ran: {steps_that_ran}"
        )

    def test_zero_slash_zero_dev_units_skips_steps_6_through_8(self, e2e_fix_mock_dependencies, e2e_fix_default_args):
        """When Step 5 returns 'DEV_UNITS_IDENTIFIED: 0/0', steps 6-8 must not run."""
        from pdd.agentic_e2e_fix_orchestrator import run_agentic_e2e_fix_orchestrator

        mock_run, _, _ = e2e_fix_mock_dependencies
        e2e_fix_default_args["max_cycles"] = 1

        def side_effect(*args, **kwargs):
            label = kwargs.get('label', '')
            if 'step5' in label:
                return (True, "DEV_UNITS_IDENTIFIED: 0/0\n0/0 Dev Units Needed Fix", 0.1, "gpt-4")
            if 'step9' in label:
                return (True, "ALL_TESTS_PASS", 0.1, "gpt-4")
            return (True, f"Output for {label}", 0.1, "gpt-4")

        mock_run.side_effect = side_effect

        run_agentic_e2e_fix_orchestrator(**e2e_fix_default_args)

        step_labels = [call.kwargs.get('label', '') for call in mock_run.call_args_list]
        steps_that_ran = [label for label in step_labels if any(f'step{s}' in label for s in [6, 7, 8])]
        assert len(steps_that_ran) == 0, (
            f"Steps 6-8 should be skipped when dev units = 0/0, but these ran: {steps_that_ran}"
        )

    def test_marker_present_but_empty_value_skips_steps_6_through_8(self, e2e_fix_mock_dependencies, e2e_fix_default_args):
        """When Step 5 returns 'DEV_UNITS_IDENTIFIED: ' (empty), steps 6-8 must be skipped."""
        from pdd.agentic_e2e_fix_orchestrator import run_agentic_e2e_fix_orchestrator

        mock_run, _, _ = e2e_fix_mock_dependencies
        e2e_fix_default_args["max_cycles"] = 1

        def side_effect(*args, **kwargs):
            label = kwargs.get('label', '')
            if 'step5' in label:
                return (True, "Analysis complete.\nDEV_UNITS_IDENTIFIED: \nI found no issues.", 0.1, "gpt-4")
            if 'step9' in label:
                return (True, "ALL_TESTS_PASS", 0.1, "gpt-4")
            return (True, f"Output for {label}", 0.1, "gpt-4")

        mock_run.side_effect = side_effect

        run_agentic_e2e_fix_orchestrator(**e2e_fix_default_args)

        step_labels = [call.kwargs.get('label', '') for call in mock_run.call_args_list]
        steps_that_ran = [label for label in step_labels if any(f'step{s}' in label for s in [6, 7, 8])]
        assert len(steps_that_ran) == 0, (
            f"Steps 6-8 should be skipped when marker is present but empty, but these ran: {steps_that_ran}"
        )

    def test_marker_absent_does_not_short_circuit(self, e2e_fix_mock_dependencies, e2e_fix_default_args):
        """When Step 5 returns output without DEV_UNITS_IDENTIFIED marker, steps 6-8 must run normally."""
        from pdd.agentic_e2e_fix_orchestrator import run_agentic_e2e_fix_orchestrator

        mock_run, _, _ = e2e_fix_mock_dependencies
        e2e_fix_default_args["max_cycles"] = 1

        def side_effect(*args, **kwargs):
            label = kwargs.get('label', '')
            if 'step5' in label:
                # No DEV_UNITS_IDENTIFIED line at all — implies unknown state, should continue
                return (True, "Analysis complete. I found some issues in the auth module.", 0.1, "gpt-4")
            if 'step9' in label:
                return (True, "ALL_TESTS_PASS", 0.1, "gpt-4")
            return (True, f"Output for {label}", 0.1, "gpt-4")

        mock_run.side_effect = side_effect

        run_agentic_e2e_fix_orchestrator(**e2e_fix_default_args)

        step_labels = [call.kwargs.get('label', '') for call in mock_run.call_args_list]
        steps_that_ran = [label for label in step_labels if any(f'step{s}' in label for s in [6, 7, 8])]
        assert len(steps_that_ran) == 3, (
            f"Steps 6-8 should run when marker is absent, but these ran: {steps_that_ran}"
        )

    def test_nonempty_dev_units_runs_steps_6_through_8(self, e2e_fix_mock_dependencies, e2e_fix_default_args):
        """Regression guard: when dev units ARE found, steps 6-8 must still run."""
        from pdd.agentic_e2e_fix_orchestrator import run_agentic_e2e_fix_orchestrator

        mock_run, _, _ = e2e_fix_mock_dependencies
        e2e_fix_default_args["max_cycles"] = 1

        def side_effect(*args, **kwargs):
            label = kwargs.get('label', '')
            if 'step5' in label:
                return (True, "DEV_UNITS_IDENTIFIED: auth_module, api_handler\n2 dev units need fixing.", 0.1, "gpt-4")
            if 'step9' in label:
                return (True, "ALL_TESTS_PASS", 0.1, "gpt-4")
            return (True, f"Output for {label}", 0.1, "gpt-4")

        mock_run.side_effect = side_effect

        run_agentic_e2e_fix_orchestrator(**e2e_fix_default_args)

        step_labels = [call.kwargs.get('label', '') for call in mock_run.call_args_list]
        steps_that_ran = [label for label in step_labels if any(f'step{s}' in label for s in [6, 7, 8])]
        assert len(steps_that_ran) == 3, (
            f"Steps 6-8 should run when dev units exist, but got: {step_labels}"
        )


class TestPerCycleFileHashComparison:
    """Issue #903: The orchestrator should detect when a cycle made zero code
    changes and stop cycling instead of burning wasted iterations."""

    def test_no_file_changes_breaks_cycle_loop(self, e2e_fix_mock_dependencies, e2e_fix_default_args):
        """When file hashes are identical before and after a cycle,
        the next cycle should NOT start."""
        from pdd.agentic_e2e_fix_orchestrator import run_agentic_e2e_fix_orchestrator

        mock_run, _, mock_console = e2e_fix_mock_dependencies
        e2e_fix_default_args["max_cycles"] = 3

        def side_effect(*args, **kwargs):
            label = kwargs.get('label', '')
            if 'step5' in label:
                return (True, "DEV_UNITS_IDENTIFIED: auth_module\n1 dev unit needs fixing.", 0.1, "gpt-4")
            if 'step9' in label:
                return (True, "Some tests still failing. CONTINUE_CYCLE", 0.1, "gpt-4")
            return (True, f"Output for {label}", 0.1, "gpt-4")

        mock_run.side_effect = side_effect

        # _get_file_hashes returns same {} for all calls, and _detect_changed_files
        # returns [] (no progress) to trigger the no-progress stop.
        with patch("pdd.agentic_e2e_fix_orchestrator._get_file_hashes", return_value={}), \
             patch("pdd.agentic_e2e_fix_orchestrator._detect_changed_files", return_value=[]):
            run_agentic_e2e_fix_orchestrator(**e2e_fix_default_args)

        # Should run exactly 9 steps (1 cycle) then break on no-progress detection.
        assert mock_run.call_count == 9, (
            f"Expected 9 step calls (1 cycle) but got {mock_run.call_count}."
        )

    def test_file_changes_allow_next_cycle(self, e2e_fix_mock_dependencies, e2e_fix_default_args):
        """When files DO change between cycles, the orchestrator should continue
        to the next cycle as normal."""
        from pdd.agentic_e2e_fix_orchestrator import run_agentic_e2e_fix_orchestrator

        mock_run, _, _ = e2e_fix_mock_dependencies
        e2e_fix_default_args["max_cycles"] = 2

        call_count = [0]

        def side_effect(*args, **kwargs):
            label = kwargs.get('label', '')
            if 'step5' in label:
                return (True, "DEV_UNITS_IDENTIFIED: auth_module\n1 dev unit needs fixing.", 0.1, "gpt-4")
            if 'step9' in label:
                return (True, "Some tests still failing. CONTINUE_CYCLE", 0.1, "gpt-4")
            return (True, f"Output for {label}", 0.1, "gpt-4")

        mock_run.side_effect = side_effect

        # Override _get_file_hashes to return different hashes each call,
        # simulating actual code changes.
        hash_values = [
            {},  # initial (before cycle 1)
            {"pdd/auth.py": "hash_after_cycle1"},  # after cycle 1 — different from initial
            {"pdd/auth.py": "hash_after_cycle2"},  # after cycle 2 — different from cycle 1
        ]
        hash_call_idx = [0]

        def hash_side_effect(*args, **kwargs):
            idx = min(hash_call_idx[0], len(hash_values) - 1)
            hash_call_idx[0] += 1
            return hash_values[idx]

        with patch("pdd.agentic_e2e_fix_orchestrator._get_file_hashes", side_effect=hash_side_effect):
            run_agentic_e2e_fix_orchestrator(**e2e_fix_default_args)

        # When files change, both cycles should run = 18 steps
        assert mock_run.call_count == 18, (
            f"Expected 2 full cycles (18 steps) when files changed each cycle, "
            f"but got {mock_run.call_count} step calls"
        )


class TestStep9ScopedTestExecution:
    """Issue #903: Step 9 prompt should run only issue-related tests,
    not the entire test suite."""

    def test_step9_prompt_does_not_run_all_tests(self):
        """The Step 9 prompt file must NOT instruct running 'pytest tests/ -v'
        (all tests). Pre-existing failures in unrelated tests should not drive
        cycle decisions."""
        import pathlib

        prompt_path = pathlib.Path(__file__).parent.parent / "pdd" / "prompts" / "agentic_e2e_fix_step9_verify_all_LLM.prompt"
        assert prompt_path.exists(), f"Step 9 prompt not found at {prompt_path}"

        prompt = prompt_path.read_text()

        # The old prompt had "Run all unit tests: `pytest tests/ -v`"
        # The fixed prompt should NOT contain this instruction.
        assert "Run all unit tests: `pytest tests/ -v`" not in prompt, (
            "Step 9 prompt still contains 'Run all unit tests: `pytest tests/ -v`' which runs "
            "ALL tests. It should scope to issue-related tests only."
        )

    def test_step9_prompt_scopes_to_issue_related_tests(self):
        """The Step 9 prompt file must instruct running only issue-related tests,
        not the full test suite."""
        import pathlib

        prompt_path = pathlib.Path(__file__).parent.parent / "pdd" / "prompts" / "agentic_e2e_fix_step9_verify_all_LLM.prompt"
        assert prompt_path.exists(), f"Step 9 prompt not found at {prompt_path}"

        prompt = prompt_path.read_text()

        # The fixed prompt should explicitly prohibit running the entire test suite
        assert "Do NOT run the entire test suite" in prompt, (
            "Step 9 prompt should explicitly instruct NOT to run the entire test suite. "
            "Pre-existing failures in unrelated tests must not influence cycle decisions."
        )


class TestConvergencePromptRequirements:
    """Issue #903: The orchestrator prompt must contain convergence requirements
    so that regenerated code implements them."""

    def test_orchestrator_prompt_contains_empty_dev_units_requirement(self):
        """The orchestrator prompt file must contain requirement 5a
        (empty dev-units short-circuit) so code generation includes it."""
        import pathlib

        prompt_path = pathlib.Path(__file__).parent.parent / "pdd" / "prompts" / "agentic_e2e_fix_orchestrator_python.prompt"
        assert prompt_path.exists(), f"Orchestrator prompt not found at {prompt_path}"

        prompt = prompt_path.read_text()

        # Requirement 5a should mention skipping steps when dev units are empty/0
        assert "empty dev-units short-circuit" in prompt.lower() or "Empty dev-units short-circuit" in prompt, (
            "Orchestrator prompt is missing requirement 5a: empty dev-units short-circuit"
        )

    def test_orchestrator_prompt_contains_file_hash_comparison_requirement(self):
        """The orchestrator prompt file must contain requirement 5b
        (per-cycle file-hash comparison) so code generation includes it."""
        import pathlib

        prompt_path = pathlib.Path(__file__).parent.parent / "pdd" / "prompts" / "agentic_e2e_fix_orchestrator_python.prompt"
        assert prompt_path.exists(), f"Orchestrator prompt not found at {prompt_path}"

        prompt = prompt_path.read_text()

        # Requirement 5b should mention per-cycle file hash comparison
        assert "per-cycle file-hash" in prompt.lower() or "Per-cycle file-hash comparison" in prompt, (
            "Orchestrator prompt is missing requirement 5b: per-cycle file-hash comparison"
        )

class TestClassifyVerificationFailure:
    """Tests for _classify_verification_failure (issue #934).

    All tests are deterministic pattern matching — no LLM mocks needed.
    Unrecognized patterns default to test_failure without any LLM call.
    """

    def test_python_import_error(self):
        """Python ImportError in pytest ^E format should be classified as import_error."""
        output = "tests/test_login.py::test_auth\nE   ImportError: No module named 'login'"
        assert _classify_verification_failure(output) == "import_error"

    def test_python_module_not_found_error(self):
        """Python ModuleNotFoundError in pytest ^E format should be classified as import_error."""
        output = "tests/test_login.py::test_auth\nE   ModuleNotFoundError: No module named 'pdd.login'"
        assert _classify_verification_failure(output) == "import_error"

    def test_python_name_error_pytest_format(self):
        """NameError in pytest traceback format should be classified as import_error."""
        output = "tests/test_login.py::test_retry\nE   NameError: name '_count_planned_tests' is not defined"
        assert _classify_verification_failure(output) == "import_error"

    def test_python_attribute_error_pytest_format(self):
        """AttributeError in pytest traceback format should be classified as import_error."""
        output = "tests/test_login.py::test_retry\nE   AttributeError: module 'login' has no attribute 'handle'"
        assert _classify_verification_failure(output) == "import_error"

    def test_python_syntax_error_pytest_format(self):
        """SyntaxError in pytest traceback format should be classified as import_error."""
        output = "tests/test_login.py\nE   SyntaxError: invalid syntax"
        assert _classify_verification_failure(output) == "import_error"

    def test_js_cannot_find_module(self):
        """JS/TS 'Cannot find module' in pytest ^E format should be classified as import_error."""
        output = "tests/test_app.js\nE   Cannot find module './login' from 'src/index.ts'"
        assert _classify_verification_failure(output) == "import_error"

    def test_js_module_not_found(self):
        """JS/TS 'Module not found' in pytest ^E format should be classified as import_error."""
        output = "tests/test_app.js\nE   Module not found: Error: Can't resolve './login'"
        assert _classify_verification_failure(output) == "import_error"

    def test_js_reference_error(self):
        """JS/TS ReferenceError in pytest ^E format should be classified as import_error."""
        output = "tests/test_app.js\nE   ReferenceError: handleLogin is not defined"
        assert _classify_verification_failure(output) == "import_error"

    def test_no_test_runner_available(self):
        """'FAILED (no test runner available)' should be classified as import_error."""
        assert _classify_verification_failure("test_login.ts: FAILED (no test runner available)") == "import_error"

    def test_assertion_error_is_test_failure(self):
        """AssertionError (no import patterns) should be classified as test_failure."""
        assert _classify_verification_failure("FAILED tests/test_login.py::test_retry - AssertionError: assert 1 == 2") == "test_failure"

    def test_empty_output_is_test_failure(self):
        """Empty output should default to test_failure."""
        assert _classify_verification_failure("") == "test_failure"

    def test_name_error_outside_pytest_format_no_match(self):
        """NameError NOT in pytest ^E format should not match (avoids false positives)."""
        output = "FAILED - assert 'NameError' in error_messages"
        assert _classify_verification_failure(output) == "test_failure"

    def test_unrecognized_pattern_defaults_to_test_failure(self):
        """Unrecognized patterns (e.g. Go compile errors) default to test_failure."""
        assert _classify_verification_failure("./main.go:10:2: undefined: handleLogin") == "test_failure"

    def test_unknown_output_defaults_to_test_failure(self):
        """Completely unknown output defaults to test_failure."""
        assert _classify_verification_failure("some unknown error output") == "test_failure"


class TestHandleVerificationFailure:
    """Tests for _handle_verification_failure helper (deduplication of retry logic)."""

    @patch("pdd.agentic_e2e_fix_orchestrator._classify_verification_failure", return_value="import_error")
    def test_import_error_returns_should_retry(self, _mock_classify):
        """First import_error should return should_retry=True."""
        console = MagicMock()
        failure_type, retries, should_retry = _handle_verification_failure(
            "ImportError: No module named 'login'", 0, console
        )
        assert failure_type == "import_error"
        assert retries == 1
        assert should_retry is True

    @patch("pdd.agentic_e2e_fix_orchestrator._classify_verification_failure", return_value="import_error")
    def test_import_error_exhausted_returns_no_retry(self, _mock_classify):
        """Second import_error (retries=1) should return should_retry=False."""
        console = MagicMock()
        failure_type, retries, should_retry = _handle_verification_failure(
            "ImportError: No module named 'login'", 1, console
        )
        assert failure_type == "import_error"
        assert retries == 1
        assert should_retry is False

    @patch("pdd.agentic_e2e_fix_orchestrator._classify_verification_failure", return_value="test_failure")
    def test_test_failure_returns_no_retry(self, _mock_classify):
        """test_failure should never retry."""
        console = MagicMock()
        failure_type, retries, should_retry = _handle_verification_failure(
            "FAILED tests/test_login.py::test_retry - AssertionError", 0, console
        )
        assert failure_type == "test_failure"
        assert retries == 0
        assert should_retry is False


class TestImportErrorRetryBehavior:
    """Tests for import_error retry routing at verification call sites (issue #934).

    When verification fails with an import error, the orchestrator should retry
    from Step 1 instead of falling through to expensive Steps 3-9.
    """

    @patch("pdd.agentic_e2e_fix_orchestrator._classify_verification_failure", return_value="import_error")
    @patch("pdd.agentic_e2e_fix_orchestrator._verify_tests_independently")
    @patch("pdd.agentic_e2e_fix_orchestrator._extract_test_files")
    def test_step2_import_error_retries_step1(self, mock_extract, mock_verify, _mock_classify, e2e_fix_mock_dependencies, e2e_fix_default_args):
        """Step 2 verification ImportError should retry from Step 1."""
        mock_run, _, mock_console = e2e_fix_mock_dependencies

        mock_extract.return_value = ["tests/test_login.py"]
        mock_verify.return_value = (False, "ImportError: No module named 'login'")

        def side_effect(*args, **kwargs):
            label = kwargs.get('label', '')
            if 'step2' in label:
                return (True, "All tests pass. ALL_TESTS_PASS", 0.1, "gpt-4")
            return (True, f"Output for {label}", 0.1, "gpt-4")

        mock_run.side_effect = side_effect
        e2e_fix_default_args["max_cycles"] = 2

        success, msg, cost, model, files = run_agentic_e2e_fix_orchestrator(
            **e2e_fix_default_args
        )

        # Should have retried — step1 called in cycle 1 and again in cycle 2 (retry)
        step1_calls = sum(1 for c in mock_run.call_args_list if 'step1' in str(c))
        assert step1_calls >= 2, (
            f"Expected Step 1 to be called at least twice (original + retry) but got {step1_calls}"
        )

    @patch("pdd.agentic_e2e_fix_orchestrator._classify_verification_failure", return_value="test_failure")
    @patch("pdd.agentic_e2e_fix_orchestrator._verify_tests_independently")
    @patch("pdd.agentic_e2e_fix_orchestrator._extract_test_files")
    def test_step2_test_failure_falls_through(self, mock_extract, mock_verify, _mock_classify, e2e_fix_mock_dependencies, e2e_fix_default_args):
        """Step 2 verification AssertionError should fall through to Steps 3-9."""
        mock_run, _, _ = e2e_fix_mock_dependencies

        mock_extract.return_value = ["tests/test_login.py"]
        mock_verify.return_value = (False, "FAILED tests/test_login.py::test_retry - AssertionError")

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

        # Step 1 should NOT be retried — should proceed to Step 3+
        step1_calls = sum(1 for c in mock_run.call_args_list if 'step1' in str(c))
        assert step1_calls == 1, (
            f"Expected Step 1 to be called exactly once (no retry for test_failure) but got {step1_calls}"
        )
        # Should have continued past Step 2 (at least to Step 3)
        assert mock_run.call_count > 2

    @patch("pdd.agentic_e2e_fix_orchestrator._classify_verification_failure", return_value="import_error")
    @patch("pdd.agentic_e2e_fix_orchestrator._verify_tests_independently")
    @patch("pdd.agentic_e2e_fix_orchestrator._extract_test_files")
    def test_import_error_retry_limited_to_one(self, mock_extract, mock_verify, _mock_classify, e2e_fix_mock_dependencies, e2e_fix_default_args):
        """Import error retry should be limited to 1 total (global budget) to prevent infinite loops."""
        mock_run, _, _ = e2e_fix_mock_dependencies

        mock_extract.return_value = ["tests/test_login.py"]
        mock_verify.return_value = (False, "ImportError: No module named 'login'")

        def side_effect(*args, **kwargs):
            label = kwargs.get('label', '')
            if 'step2' in label:
                return (True, "All tests pass. ALL_TESTS_PASS", 0.1, "gpt-4")
            return (True, f"Output for {label}", 0.1, "gpt-4")

        mock_run.side_effect = side_effect
        e2e_fix_default_args["max_cycles"] = 3

        success, msg, cost, model, files = run_agentic_e2e_fix_orchestrator(
            **e2e_fix_default_args
        )

        # Global budget of 1 retry, so step1 calls <= max_cycles + 1
        step1_calls = sum(1 for c in mock_run.call_args_list if 'step1' in str(c))
        max_cycles = e2e_fix_default_args["max_cycles"]
        assert step1_calls <= max_cycles + 1, (
            f"Expected at most {max_cycles + 1} Step 1 calls (max_cycles + 1 retry) "
            f"but got {step1_calls}. Global retry budget should prevent excessive retries."
        )

    @patch("pdd.agentic_e2e_fix_orchestrator._classify_verification_failure", return_value="import_error")
    @patch("pdd.agentic_e2e_fix_orchestrator._verify_tests_independently")
    @patch("pdd.agentic_e2e_fix_orchestrator._extract_test_files")
    def test_step9_import_error_retries_step1(self, mock_extract, mock_verify, _mock_classify, e2e_fix_mock_dependencies, e2e_fix_default_args):
        """Step 9 verification ImportError should retry from Step 1."""
        mock_run, _, _ = e2e_fix_mock_dependencies

        mock_extract.return_value = ["tests/test_login.py"]
        mock_verify.return_value = (False, "ImportError: No module named 'login'")

        call_labels = []
        def side_effect(*args, **kwargs):
            label = kwargs.get('label', '')
            call_labels.append(label)
            if 'step9' in label:
                return (True, "Verification complete. ALL_TESTS_PASS", 0.1, "gpt-4")
            return (True, f"Output for {label}", 0.1, "gpt-4")

        mock_run.side_effect = side_effect
        e2e_fix_default_args["max_cycles"] = 2

        success, msg, cost, model, files = run_agentic_e2e_fix_orchestrator(
            **e2e_fix_default_args
        )

        # Should have retried Step 1 after Step 9 import error
        step9_indices = [i for i, l in enumerate(call_labels) if 'step9' in l]
        step1_after_step9 = any(
            i > s9_idx and 'step1' in call_labels[i]
            for s9_idx in step9_indices
            for i in range(s9_idx + 1, len(call_labels))
        )
        assert step9_indices, "Step 9 should have been called"
        assert step1_after_step9, (
            f"Expected Step 1 to be retried after Step 9 import_error but call sequence was: {call_labels}"
        )


class TestReviewFix1NoLLMFallback:
    """Review item 1: _classify_verification_failure must NOT call LLM.

    The most common failure (AssertionError) won't match any tier-1 pattern.
    The old tier-2 LLM fallback added an LLM call on the most frequent path,
    defeating the purpose of the optimization. Default should be test_failure
    with no LLM call.
    """

    def test_no_llm_call_for_assertion_error(self):
        """AssertionError should be classified as test_failure WITHOUT any LLM call."""
        with patch("pdd.agentic_e2e_fix_orchestrator.classify_step_output") as mock_llm:
            result = _classify_verification_failure(
                "FAILED tests/test_login.py::test_retry - AssertionError: assert 1 == 2"
            )
            assert result == "test_failure"
            mock_llm.assert_not_called()

    def test_no_llm_call_for_unknown_output(self):
        """Unknown/unrecognized output should default to test_failure WITHOUT LLM call."""
        with patch("pdd.agentic_e2e_fix_orchestrator.classify_step_output") as mock_llm:
            result = _classify_verification_failure("some completely unknown error output")
            assert result == "test_failure"
            mock_llm.assert_not_called()

    def test_no_llm_call_for_empty_output(self):
        """Empty output should default to test_failure WITHOUT LLM call."""
        with patch("pdd.agentic_e2e_fix_orchestrator.classify_step_output") as mock_llm:
            result = _classify_verification_failure("")
            assert result == "test_failure"
            mock_llm.assert_not_called()

    def test_no_llm_call_for_go_compile_error(self):
        """Go compile errors should default to test_failure WITHOUT LLM call.

        Previously these went through tier-2 LLM fallback. Now they should
        just be test_failure (conservative default).
        """
        with patch("pdd.agentic_e2e_fix_orchestrator.classify_step_output") as mock_llm:
            result = _classify_verification_failure(
                "./main.go:10:2: undefined: handleLogin"
            )
            assert result == "test_failure"
            mock_llm.assert_not_called()

    def test_tier1_patterns_still_work_without_llm(self):
        """Tier-1 patterns should still detect import_error without any LLM involvement."""
        with patch("pdd.agentic_e2e_fix_orchestrator.classify_step_output") as mock_llm:
            # Use pytest traceback format (anchored)
            result = _classify_verification_failure(
                "tests/test_login.py::test_retry\nE   NameError: name '_count_planned_tests' is not defined"
            )
            assert result == "import_error"
            mock_llm.assert_not_called()


class TestReviewFix2AnchoredPatterns:
    """Review item 2: ImportError/ReferenceError patterns must be anchored.

    Unanchored patterns false-positive on test output containing
    'pytest.raises(ImportError)' or assertion messages mentioning error types.
    """

    def test_pytest_raises_import_error_not_false_positive(self):
        """'pytest.raises(ImportError)' in test output should NOT trigger import_error."""
        result = _classify_verification_failure(
            "PASSED tests/test_routes_init.py::test_invalid_import - "
            "with pytest.raises(ImportError): import nonexistent"
        )
        assert result == "test_failure", (
            "pytest.raises(ImportError) in passing test output should not trigger import_error"
        )

    def test_import_error_in_assertion_message_not_false_positive(self):
        """ImportError mentioned in an assertion string should NOT trigger import_error."""
        result = _classify_verification_failure(
            "FAILED tests/test_error_handling.py::test_error_msg - "
            "AssertionError: assert 'ImportError: no module' in error_messages"
        )
        assert result == "test_failure", (
            "ImportError inside assertion message should not trigger false positive"
        )

    def test_reference_error_in_test_name_not_false_positive(self):
        """ReferenceError in test name/description should NOT trigger import_error."""
        result = _classify_verification_failure(
            "PASSED tests/test_errors.py::test_handles_ReferenceError_gracefully"
        )
        assert result == "test_failure", (
            "ReferenceError in test name should not trigger false positive"
        )

    def test_bare_import_error_at_line_start_not_matched(self):
        """Bare ImportError at line start (not ^E format) should NOT trigger import_error.

        Only pytest ^E format is matched to avoid false positives from log/print lines.
        """
        output = "ImportError: cannot import name '_count_planned_tests' from 'pdd.agentic_bug_orchestrator'"
        assert _classify_verification_failure(output) == "test_failure"

    def test_real_import_error_pytest_E_format_detected(self):
        """Real ImportError in pytest ^E format should be detected."""
        output = "tests/test_login.py::test_auth\nE   ImportError: No module named 'login'"
        assert _classify_verification_failure(output) == "import_error"

    def test_bare_module_not_found_at_line_start_not_matched(self):
        """Bare ModuleNotFoundError at line start should NOT trigger import_error."""
        output = "ModuleNotFoundError: No module named 'pdd.login'"
        assert _classify_verification_failure(output) == "test_failure"

    def test_bare_reference_error_at_line_start_not_matched(self):
        """Bare ReferenceError at line start should NOT trigger import_error."""
        output = "ReferenceError: handleLogin is not defined\n    at Object.<anonymous>"
        assert _classify_verification_failure(output) == "test_failure"

    def test_real_reference_error_pytest_E_format_detected(self):
        """Real ReferenceError in pytest ^E format should be detected."""
        output = "tests/test_app.js\nE   ReferenceError: handleLogin is not defined"
        assert _classify_verification_failure(output) == "import_error"

    def test_cannot_find_module_mid_line_not_false_positive(self):
        """'Cannot find module' mid-line (e.g. in assertion) should NOT trigger import_error."""
        result = _classify_verification_failure(
            "FAILED - assert error.message == 'Cannot find module ./login'"
        )
        assert result == "test_failure"

    def test_real_cannot_find_module_pytest_E_format_detected(self):
        """Real 'Cannot find module' in pytest ^E format should be detected."""
        output = "tests/test_app.js\nE   Cannot find module './login' from 'src/index.ts'"
        assert _classify_verification_failure(output) == "import_error"

    def test_real_module_not_found_pytest_E_format_detected(self):
        """Real 'Module not found' in pytest ^E format should be detected."""
        output = "tests/test_app.js\nE   Module not found: Error: Can't resolve './login'"
        assert _classify_verification_failure(output) == "import_error"


class TestReviewFix3VerificationContextInjection:
    """Review item 3: Retry prompt must include verification failure output.

    When retrying from Step 1 after import_error, the LLM needs to see what
    went wrong so it doesn't re-hallucinate the same failure.
    """

    @patch("pdd.agentic_e2e_fix_orchestrator._classify_verification_failure", return_value="import_error")
    @patch("pdd.agentic_e2e_fix_orchestrator._verify_tests_independently")
    @patch("pdd.agentic_e2e_fix_orchestrator._extract_test_files")
    def test_retry_prompt_contains_verification_output(
        self, mock_extract, mock_verify, _mock_classify,
        e2e_fix_mock_dependencies, e2e_fix_default_args
    ):
        """Step 1 retry prompt should contain the verification failure output."""
        mock_run, _, _ = e2e_fix_mock_dependencies
        verification_error = "ImportError: cannot import name '_count_planned_tests' from 'pdd.agentic_bug_orchestrator'"

        mock_extract.return_value = ["tests/test_login.py"]
        mock_verify.return_value = (False, verification_error)

        prompts_by_label = {}
        def side_effect(*args, **kwargs):
            label = kwargs.get('label', '')
            instruction = kwargs.get('instruction', '') or (args[0] if args else '')
            prompts_by_label[label] = instruction
            if 'step2' in label:
                return (True, "All tests pass. ALL_TESTS_PASS", 0.1, "gpt-4")
            return (True, f"Output for {label}", 0.1, "gpt-4")

        mock_run.side_effect = side_effect
        e2e_fix_default_args["max_cycles"] = 2

        run_agentic_e2e_fix_orchestrator(**e2e_fix_default_args)

        # Find the retry Step 1 call (second time step1 appears)
        step1_labels = [l for l in prompts_by_label if 'step1' in l]
        assert len(step1_labels) >= 2, (
            f"Expected at least 2 Step 1 calls (original + retry) but got: {step1_labels}"
        )
        retry_label = step1_labels[1]
        retry_prompt = prompts_by_label[retry_label]

        # The retry prompt must contain the verification failure output
        assert "_count_planned_tests" in retry_prompt, (
            f"Retry Step 1 prompt should contain the verification failure details "
            f"(ImportError about _count_planned_tests) but got:\n{retry_prompt[:500]}"
        )

    @patch("pdd.agentic_e2e_fix_orchestrator._classify_verification_failure", return_value="import_error")
    @patch("pdd.agentic_e2e_fix_orchestrator._verify_tests_independently")
    @patch("pdd.agentic_e2e_fix_orchestrator._extract_test_files")
    def test_non_retry_prompt_does_not_contain_stale_context(
        self, mock_extract, mock_verify, _mock_classify,
        e2e_fix_mock_dependencies, e2e_fix_default_args
    ):
        """Normal (non-retry) Step 1 prompt should NOT contain verification failure context."""
        mock_run, _, _ = e2e_fix_mock_dependencies

        mock_extract.return_value = ["tests/test_login.py"]
        mock_verify.return_value = (False, "ImportError: cannot import name 'missing_func'")

        prompts_by_label = {}
        def side_effect(*args, **kwargs):
            label = kwargs.get('label', '')
            instruction = kwargs.get('instruction', '') or (args[0] if args else '')
            prompts_by_label[label] = instruction
            if 'step2' in label:
                return (True, "All tests pass. ALL_TESTS_PASS", 0.1, "gpt-4")
            return (True, f"Output for {label}", 0.1, "gpt-4")

        mock_run.side_effect = side_effect
        e2e_fix_default_args["max_cycles"] = 2

        run_agentic_e2e_fix_orchestrator(**e2e_fix_default_args)

        # The FIRST Step 1 call should NOT have verification failure context
        step1_labels = [l for l in prompts_by_label if 'step1' in l]
        assert len(step1_labels) >= 1
        first_prompt = prompts_by_label[step1_labels[0]]
        assert "PREVIOUS ATTEMPT FAILED" not in first_prompt, (
            "First Step 1 call should not contain verification failure context"
        )


class TestReviewFix4ConsistentRetryState:
    """Review item 4: All 4 verification call sites should have consistent state on retry.

    When should_retry is True, all sites should set step_outputs to indicate
    what happened before breaking, so orchestrator state is clean.
    """

    @patch("pdd.agentic_e2e_fix_orchestrator._classify_verification_failure", return_value="import_error")
    @patch("pdd.agentic_e2e_fix_orchestrator._verify_tests_independently")
    @patch("pdd.agentic_e2e_fix_orchestrator._extract_test_files")
    def test_step2_main_path_sets_verification_failed_on_retry(
        self, mock_extract, mock_verify, _mock_classify,
        e2e_fix_mock_dependencies, e2e_fix_default_args
    ):
        """Step 2 main-path retry should set step_output to VERIFICATION_FAILED before breaking."""
        mock_run, _, _ = e2e_fix_mock_dependencies

        mock_extract.return_value = ["tests/test_login.py"]
        mock_verify.return_value = (False, "ImportError: No module named 'login'")

        call_count = [0]
        def side_effect(*args, **kwargs):
            label = kwargs.get('label', '')
            call_count[0] += 1
            if 'step2' in label:
                return (True, "All tests pass. ALL_TESTS_PASS", 0.1, "gpt-4")
            return (True, f"Output for {label}", 0.1, "gpt-4")

        mock_run.side_effect = side_effect
        e2e_fix_default_args["max_cycles"] = 2

        with patch("pdd.agentic_e2e_fix_orchestrator.save_workflow_state") as mock_save:
            run_agentic_e2e_fix_orchestrator(**e2e_fix_default_args)

            # Check that save_workflow_state was called with step_outputs containing
            # a VERIFICATION_FAILED or IMPORT_ERROR_RETRY marker for step 2
            # At minimum, the state should reflect that verification failed
            save_calls = mock_save.call_args_list
            # Find the save call after the verification failure
            found_verification_state = False
            for call in save_calls:
                args, kwargs_call = call
                # state_data is positional arg index 4 or keyword
                state_data = args[3] if len(args) > 3 else kwargs_call.get('state_data', {})
                if isinstance(state_data, dict):
                    step_outputs = state_data.get('step_outputs', {})
                    step2_output = step_outputs.get('2', '')
                    if 'VERIFICATION_FAILED' in step2_output or 'IMPORT_ERROR_RETRY' in step2_output:
                        found_verification_state = True
                        break

            assert found_verification_state, (
                "Step 2 main-path retry should save state with VERIFICATION_FAILED "
                "or IMPORT_ERROR_RETRY in step_outputs['2']"
            )


class TestIssue1031WorkflowStateMarkers:
    """Tests for issue #1031: _extract_test_files misses FILES_CREATED markers
    embedded inside PDD_WORKFLOW_STATE JSON comments.

    Bug: When pdd-issue chains bug → fix in separate Cloud Run Jobs, the fix
    executor runs in a fresh clone. FILES_CREATED markers from pdd bug are
    embedded inside a JSON-serialized PDD_WORKFLOW_STATE HTML comment where
    newlines become \\n escape sequences. splitlines() misses them, causing
    _extract_test_files to fall back to scanning all test files (multi-hour stall).

    These tests use the exact production format from _serialize_state_comment:
    indent=2 JSON, <!-- PDD_WORKFLOW_STATE:{type}:issue-{N} --> markers.
    """

    @staticmethod
    def _make_workflow_comment(
        step_output: str,
        workflow_type: str = "bug",
        issue_number: int = 1026,
        step_key: str = "9",
    ) -> str:
        """Build a PDD_WORKFLOW_STATE comment matching production format exactly.

        Uses json.dumps(indent=2) and the real marker format from
        agentic_common._serialize_state_comment.
        """
        state = {"step_outputs": {step_key: step_output}}
        json_str = json.dumps(state, indent=2)
        return (
            f"<!-- PDD_WORKFLOW_STATE:{workflow_type}:issue-{issue_number}\n"
            f"{json_str}\n"
            f"-->"
        )

    def test_json_embedded_files_created_marker(self, tmp_path):
        """FILES_CREATED: inside a PDD_WORKFLOW_STATE JSON must be found.

        This is the core bug: pdd bug produces step output with a real newline
        before FILES_CREATED:. json.dumps() serializes it as \\n in JSON text.
        splitlines() on the raw HTML comment never sees it as a line start.
        """
        (tmp_path / "tests").mkdir()
        (tmp_path / "tests" / "test_webhook.py").write_text("def test_x(): pass")
        # Decoy files — if the directory scan fallback fires, these get included
        for i in range(5):
            (tmp_path / "tests" / f"test_decoy_{i}.py").write_text(f"def test_{i}(): pass")

        step_output = "Analysis complete.\nFILES_CREATED: tests/test_webhook.py"
        issue_content = (
            "Bug description here.\n"
            + self._make_workflow_comment(step_output)
            + "\nMore text."
        )

        with patch(
            "pdd.agentic_e2e_fix_orchestrator._get_modified_and_untracked",
            return_value=[],
        ):
            result = _extract_test_files(
                issue_content=issue_content,
                changed_files=[],
                cwd=tmp_path,
                initial_file_hashes=None,
            )

        assert result == ["tests/test_webhook.py"], (
            f"Expected ['tests/test_webhook.py'] from JSON-embedded marker, "
            f"got {result!r}"
        )

    def test_json_embedded_e2e_files_created_marker(self, tmp_path):
        """E2E_FILES_CREATED: inside a PDD_WORKFLOW_STATE JSON must also be found."""
        (tmp_path / "tests").mkdir()
        (tmp_path / "tests" / "test_e2e_login.py").write_text("def test_x(): pass")
        for i in range(5):
            (tmp_path / "tests" / f"test_decoy_{i}.py").write_text(f"def test_{i}(): pass")

        step_output = "Done.\nE2E_FILES_CREATED: tests/test_e2e_login.py"
        issue_content = self._make_workflow_comment(step_output)

        with patch(
            "pdd.agentic_e2e_fix_orchestrator._get_modified_and_untracked",
            return_value=[],
        ):
            result = _extract_test_files(
                issue_content=issue_content,
                changed_files=[],
                cwd=tmp_path,
                initial_file_hashes=None,
            )

        assert result == ["tests/test_e2e_login.py"], (
            f"Expected ['tests/test_e2e_login.py'] from JSON-embedded E2E marker, "
            f"got {result!r}"
        )

    def test_json_embedded_comma_separated_markers(self, tmp_path):
        """Multiple comma-separated files in a JSON-embedded marker are all found."""
        (tmp_path / "tests").mkdir()
        (tmp_path / "tests" / "test_alpha.py").write_text("def test_a(): pass")
        (tmp_path / "tests" / "test_beta.py").write_text("def test_b(): pass")
        for i in range(5):
            (tmp_path / "tests" / f"test_decoy_{i}.py").write_text(f"def test_{i}(): pass")

        step_output = "Created.\nFILES_CREATED: tests/test_alpha.py, tests/test_beta.py"
        issue_content = self._make_workflow_comment(step_output)

        with patch(
            "pdd.agentic_e2e_fix_orchestrator._get_modified_and_untracked",
            return_value=[],
        ):
            result = _extract_test_files(
                issue_content=issue_content,
                changed_files=[],
                cwd=tmp_path,
                initial_file_hashes=None,
            )

        assert sorted(result) == ["tests/test_alpha.py", "tests/test_beta.py"], (
            f"Expected both test files from comma-separated marker, got {result!r}"
        )

    def test_json_embedded_marker_prevents_directory_scan_fallback(self, tmp_path):
        """When a JSON-embedded marker is found, the directory scan must NOT fire.

        Without the fix, the marker is invisible to splitlines(), no files are
        found by any discovery path, and the ultimate fallback scans the entire
        tests/ directory — returning hundreds of files.
        """
        (tmp_path / "tests").mkdir()
        (tmp_path / "tests" / "test_target.py").write_text("def test_t(): pass")
        # Decoy files that the directory scan fallback would pick up
        for i in range(10):
            (tmp_path / "tests" / f"test_decoy_{i}.py").write_text(f"def test_{i}(): pass")

        step_output = "Fix applied.\nFILES_CREATED: tests/test_target.py"
        issue_content = self._make_workflow_comment(step_output)

        with patch(
            "pdd.agentic_e2e_fix_orchestrator._get_modified_and_untracked",
            return_value=[],
        ):
            result = _extract_test_files(
                issue_content=issue_content,
                changed_files=[],
                cwd=tmp_path,
                initial_file_hashes=None,
            )

        assert result == ["tests/test_target.py"], (
            f"Expected only ['tests/test_target.py'] but got {len(result)} files — "
            f"directory scan fallback likely fired: {result!r}"
        )


# ============================================================================
# Issue #1080: Non-Python test verification uses wrong cwd — breaks monorepos
# ============================================================================

class TestIssue1080MonorepoCwd:
    """Tests for issue #1080: _verify_tests_independently must use config dir as cwd.

    Bug: _verify_tests_independently() runs non-Python tests (Jest, Vitest, Playwright)
    from the repo root instead of the directory containing the test runner config.
    This causes every monorepo with tests in a subdirectory to fail verification.
    """

    # --- Test 9: _verify_tests_independently uses config dir cwd ---

    @patch("subprocess.run")
    def test_verify_independently_uses_config_dir_not_repo_root(self, mock_subproc, tmp_path):
        """_verify_tests_independently must pass the test runner config directory as cwd.

        Before fix: subprocess.run(cwd=str(repo_root)) — always repo root
        After fix: subprocess.run(cwd=str(config_dir)) — where jest.config.js lives

        Uses real filesystem so get_test_command_for_file finds the config naturally.
        """
        # Set up monorepo: frontend/jest.config.js + frontend/src/lib/__test__/api.test.ts
        config_dir = tmp_path / "frontend"
        config_dir.mkdir()
        (config_dir / "jest.config.js").write_text("module.exports = {};")

        test_dir = config_dir / "src" / "lib" / "__test__"
        test_dir.mkdir(parents=True)
        (test_dir / "api.test.ts").write_text("test('api', () => {});")

        mock_subproc.return_value = MagicMock(returncode=0, stdout="PASS", stderr="")

        passed, output = _verify_tests_independently(
            ["frontend/src/lib/__test__/api.test.ts"], tmp_path
        )

        mock_subproc.assert_called_once()
        actual_cwd = mock_subproc.call_args.kwargs['cwd']
        assert actual_cwd == str(config_dir), (
            f"Bug #1080: Expected cwd={config_dir} (where jest.config.js lives), "
            f"got cwd={actual_cwd} (repo root). Non-Python test verification uses "
            f"wrong cwd, breaking all monorepos."
        )

    # --- Test 10: Backward compat — falls back to repo root when cwd=None ---

    @patch("subprocess.run")
    @patch("pdd.agentic_e2e_fix_orchestrator.get_test_command_for_file")
    def test_verify_independently_falls_back_to_repo_root_when_cwd_none(
        self, mock_get_cmd, mock_subproc, tmp_path
    ):
        """When TestCommand.cwd is None, _verify_tests_independently falls back to repo root.

        On buggy code: get_test_command_for_file returns str → caller does shlex.split(str)
            which works, but this test returns a TestCommand-like object → crash (TypeError).
        On fixed code: caller extracts .command and .cwd, falls back to repo root when cwd=None.
        """
        from types import SimpleNamespace

        # Return a TestCommand-like object with cwd=None
        mock_cmd = SimpleNamespace(
            command="some_runner src/test.rb",
            cwd=None
        )
        mock_get_cmd.return_value = mock_cmd
        mock_subproc.return_value = MagicMock(returncode=0, stdout="OK", stderr="")

        passed, output = _verify_tests_independently(["src/test.rb"], tmp_path)

        # On buggy code, shlex.split(SimpleNamespace) raises TypeError which is
        # caught silently → subprocess.run never called. On fixed code, the caller
        # extracts .command and .cwd from the TestCommand correctly.
        assert mock_subproc.called, (
            "subprocess.run was never called — the caller can't handle a TestCommand "
            "return type from get_test_command_for_file. The fix must extract .command "
            "from the result before passing to shlex.split()."
        )
        actual_cwd = mock_subproc.call_args.kwargs['cwd']
        assert actual_cwd == str(tmp_path), (
            f"Expected fallback to repo root ({tmp_path}) when cwd=None, got {actual_cwd}"
        )

# ============================================================================
# Step 11: Code Cleanup Tests (Issue #1073)
# ============================================================================


class TestStep11CodeCleanup:
    """Tests for Step 11: Code cleanup after CI validation.

    Step 11 collects the full diff and changed file contents, invokes the
    cleanup LLM, re-runs tests to verify, and commits as a separate commit
    if tests pass. Reverts all cleanup changes if tests fail.
    """

    def test_step11_skipped_when_no_files_changed(self, tmp_path):
        """Step 11 should be skipped when no files changed during workflow."""
        from pdd.agentic_e2e_fix_orchestrator import _run_step11_code_cleanup

        with patch("pdd.agentic_e2e_fix_orchestrator._detect_changed_files", return_value=[]):
            cost, files = _run_step11_code_cleanup(
                cwd=tmp_path,
                issue_number=1,
                issue_content="test",
                initial_file_hashes={},
                total_cost=1.0,
                changed_files=["old.py"],
                timeout_adder=0.0,
                verbose=False,
                quiet=False,
            )

        assert cost == 1.0
        assert files == ["old.py"]

    def test_step11_skipped_when_template_missing(self, tmp_path):
        """Step 11 should be skipped when cleanup prompt template is missing."""
        from pdd.agentic_e2e_fix_orchestrator import _run_step11_code_cleanup

        with patch("pdd.agentic_e2e_fix_orchestrator._detect_changed_files", return_value=["module.py"]), \
             patch("pdd.agentic_e2e_fix_orchestrator.load_prompt_template", return_value=None):
            cost, files = _run_step11_code_cleanup(
                cwd=tmp_path,
                issue_number=1,
                issue_content="test",
                initial_file_hashes={},
                total_cost=1.0,
                changed_files=["module.py"],
                timeout_adder=0.0,
                verbose=False,
                quiet=False,
            )

        assert cost == 1.0

    def test_step11_reverts_on_test_failure(self, tmp_path):
        """Step 11 should revert changes when tests fail after cleanup."""
        from pdd.agentic_e2e_fix_orchestrator import _run_step11_code_cleanup

        (tmp_path / "module.py").write_text("x = 1")

        with patch("pdd.agentic_e2e_fix_orchestrator._detect_changed_files", return_value=["module.py"]), \
             patch("pdd.agentic_e2e_fix_orchestrator.load_prompt_template", return_value="Cleanup {issue_number}"), \
             patch("pdd.agentic_e2e_fix_orchestrator.run_agentic_task", return_value=(True, "Cleaned up", 0.05, "gpt-4")), \
             patch("pdd.agentic_e2e_fix_orchestrator._extract_test_files", return_value=["tests/test_mod.py"]), \
             patch("pdd.agentic_e2e_fix_orchestrator._verify_tests_independently", return_value=(False, "1 failed")), \
             patch("pdd.agentic_e2e_fix_orchestrator.subprocess.run") as mock_subprocess, \
             patch("pdd.agentic_e2e_fix_orchestrator.console"):

            mock_subprocess.return_value = type("R", (), {"returncode": 0, "stdout": "", "stderr": ""})()

            cost, files = _run_step11_code_cleanup(
                cwd=tmp_path,
                issue_number=1,
                issue_content="test",
                initial_file_hashes={},
                total_cost=1.0,
                changed_files=["module.py"],
                timeout_adder=0.0,
                verbose=False,
                quiet=False,
            )

        # Should have called git checkout . to revert
        checkout_calls = [c for c in mock_subprocess.call_args_list if "checkout" in str(c)]
        assert len(checkout_calls) > 0, "Should revert via git checkout when tests fail"
        assert cost == 1.05  # Original + cleanup cost

    def test_step11_commits_on_test_pass(self, tmp_path):
        """Step 11 should commit cleanup when tests pass."""
        from pdd.agentic_e2e_fix_orchestrator import _run_step11_code_cleanup

        (tmp_path / "module.py").write_text("x = 1")

        with patch("pdd.agentic_e2e_fix_orchestrator._detect_changed_files", return_value=["module.py"]), \
             patch("pdd.agentic_e2e_fix_orchestrator.load_prompt_template", return_value="Cleanup {issue_number}"), \
             patch("pdd.agentic_e2e_fix_orchestrator.run_agentic_task", return_value=(True, "Cleaned up", 0.05, "gpt-4")), \
             patch("pdd.agentic_e2e_fix_orchestrator._extract_test_files", return_value=["tests/test_mod.py"]), \
             patch("pdd.agentic_e2e_fix_orchestrator._verify_tests_independently", return_value=(True, "1 passed")), \
             patch("pdd.agentic_e2e_fix_orchestrator.subprocess.run") as mock_subprocess, \
             patch("pdd.agentic_e2e_fix_orchestrator.console"):

            mock_subprocess.return_value = type("R", (), {"returncode": 0, "stdout": "", "stderr": ""})()

            cost, files = _run_step11_code_cleanup(
                cwd=tmp_path,
                issue_number=1,
                issue_content="test",
                initial_file_hashes={},
                total_cost=1.0,
                changed_files=["module.py"],
                timeout_adder=0.0,
                verbose=False,
                quiet=False,
            )

        # Should have called git commit
        commit_calls = [c for c in mock_subprocess.call_args_list if "commit" in str(c)]
        assert len(commit_calls) > 0, "Should commit cleanup when tests pass"

    def test_step11_llm_failure_skips_cleanup(self, tmp_path):
        """Step 11 should skip cleanup when the LLM task fails."""
        from pdd.agentic_e2e_fix_orchestrator import _run_step11_code_cleanup

        with patch("pdd.agentic_e2e_fix_orchestrator._detect_changed_files", return_value=["module.py"]), \
             patch("pdd.agentic_e2e_fix_orchestrator.load_prompt_template", return_value="Cleanup {issue_number}"), \
             patch("pdd.agentic_e2e_fix_orchestrator.run_agentic_task", return_value=(False, "LLM error", 0.02, "gpt-4")), \
             patch("pdd.agentic_e2e_fix_orchestrator.subprocess.run") as mock_subprocess, \
             patch("pdd.agentic_e2e_fix_orchestrator.console"):

            mock_subprocess.return_value = type("R", (), {"returncode": 0, "stdout": "", "stderr": ""})()

            cost, files = _run_step11_code_cleanup(
                cwd=tmp_path,
                issue_number=1,
                issue_content="test",
                initial_file_hashes={},
                total_cost=1.0,
                changed_files=["module.py"],
                timeout_adder=0.0,
                verbose=False,
                quiet=False,
            )

        assert cost == 1.02  # Original + failed LLM cost still accumulated

    def test_step11_timeout_in_dict(self):
        """E2E_FIX_STEP_TIMEOUTS should include step 11."""
        from pdd.agentic_e2e_fix_orchestrator import E2E_FIX_STEP_TIMEOUTS
        assert 11 in E2E_FIX_STEP_TIMEOUTS
        assert E2E_FIX_STEP_TIMEOUTS[11] == 600.0

    def test_step11_integrated_with_orchestrator_skip_ci(self, e2e_fix_mock_dependencies, e2e_fix_default_args):
        """Step 11 should run before CI validation on the skip_ci path."""
        mock_run, _, _ = e2e_fix_mock_dependencies

        # Make Step 9 pass so we reach commit/push -> skip_ci -> step 11
        def side_effect(*args, **kwargs):
            label = kwargs.get('label', '')
            if 'step9' in label:
                return (True, "ALL_TESTS_PASS", 0.1, "gpt-4")
            return (True, f"Output for {label}", 0.1, "gpt-4")

        mock_run.side_effect = side_effect
        e2e_fix_default_args["skip_ci"] = True

        # Remove the step 11 mock to test integration
        with patch("pdd.agentic_e2e_fix_orchestrator._run_step11_code_cleanup") as mock_step11:
            mock_step11.return_value = (0.9, ["module.py"])

            with patch("pdd.agentic_e2e_fix_orchestrator._verify_tests_independently", return_value=(True, "1 passed")), \
                 patch("pdd.agentic_e2e_fix_orchestrator._extract_test_files", return_value=["tests/test_foo.py"]):
                success, msg, cost, model, files = run_agentic_e2e_fix_orchestrator(
                    **e2e_fix_default_args
                )

            assert success is True
            mock_step11.assert_called_once()


# ---------------------------------------------------------------------------
# Regression tests for issue #1155: _verify_tests_independently safety nets
# ---------------------------------------------------------------------------


class TestVerifyTestsIndependentlyTimeout:
    """_verify_tests_independently must stop after VERIFY_TIMEOUT_SECONDS."""

    def test_stops_processing_after_timeout_elapsed(self, tmp_path):
        """Timeout triggers after elapsed time exceeds VERIFY_TIMEOUT_SECONDS,
        remaining files are skipped, and the output includes a diagnostic."""
        test_files = [f"tests/test_{i}.py" for i in range(50)]
        for tf in test_files:
            (tmp_path / tf).parent.mkdir(parents=True, exist_ok=True)
            (tmp_path / tf).write_text("pass")

        call_count = 0

        def mock_pytest(path):
            nonlocal call_count
            call_count += 1
            return {"test_results": [{"failures": 0, "errors": 0, "passed": 1, "standard_output": ""}]}

        # Time jumps past 600s after 3rd file
        time_values = iter([0, 100, 200, 300, 700, 800, 900])

        with patch("pdd.agentic_e2e_fix_orchestrator.run_pytest_and_capture_output", side_effect=mock_pytest), \
             patch("pdd.agentic_e2e_fix_orchestrator.time.monotonic", side_effect=lambda: next(time_values)):
            _, output = _verify_tests_independently(test_files, tmp_path)

        assert call_count < 50, f"Expected timeout to stop processing, but all {call_count} files were processed"
        assert "TIMEOUT" in output
        assert str(call_count) in output, "TIMEOUT message should include count of files processed"

    def test_completes_normally_when_under_timeout(self, tmp_path):
        """All files processed and no TIMEOUT when time stays under the limit."""
        test_files = [f"tests/test_{i}.py" for i in range(3)]
        for tf in test_files:
            (tmp_path / tf).parent.mkdir(parents=True, exist_ok=True)
            (tmp_path / tf).write_text("pass")

        call_count = 0

        def mock_pytest(path):
            nonlocal call_count
            call_count += 1
            return {"test_results": [{"failures": 0, "errors": 0, "passed": 1, "standard_output": ""}]}

        time_values = iter([0, 10, 20, 30, 40, 50, 60])

        with patch("pdd.agentic_e2e_fix_orchestrator.run_pytest_and_capture_output", side_effect=mock_pytest), \
             patch("pdd.agentic_e2e_fix_orchestrator.time.monotonic", side_effect=lambda: next(time_values)):
            passed, output = _verify_tests_independently(test_files, tmp_path)

        assert call_count == 3
        assert passed is True
        assert "TIMEOUT" not in output


class TestExtractTestFilesFallbackCap:
    """_extract_test_files fallback scan must cap at MAX_FALLBACK_TEST_FILES."""

    def test_fallback_scan_caps_at_max_files(self, tmp_path):
        """When the fallback scan finds more files than the cap, only
        MAX_FALLBACK_TEST_FILES are returned."""
        tests_dir = tmp_path / "tests"
        tests_dir.mkdir()
        for i in range(50):
            (tests_dir / f"test_module_{i}.py").write_text(f"def test_f{i}(): pass")

        with patch("pdd.agentic_e2e_fix_orchestrator._get_modified_and_untracked", return_value=set()):
            result = _extract_test_files(
                issue_content="no markers here",
                changed_files=[],
                cwd=tmp_path,
                initial_file_hashes=None,
            )

        assert len(result) <= 20, (
            f"Fallback scan returned {len(result)} files, expected at most 20"
        )

    def test_fallback_scan_returns_all_when_under_cap(self, tmp_path):
        """When fewer files than the cap exist, all are returned."""
        tests_dir = tmp_path / "tests"
        tests_dir.mkdir()
        for i in range(5):
            (tests_dir / f"test_mod_{i}.py").write_text(f"def test_f{i}(): pass")

        with patch("pdd.agentic_e2e_fix_orchestrator._get_modified_and_untracked", return_value=set()):
            result = _extract_test_files(
                issue_content="no markers here",
                changed_files=[],
                cwd=tmp_path,
                initial_file_hashes=None,
            )

        assert len(result) == 5, f"Expected all 5 files, got {len(result)}"

    def test_fallback_scan_prefers_recently_modified(self, tmp_path):
        """When capped, the most recently modified files are kept."""
        import os
        import time as _time

        tests_dir = tmp_path / "tests"
        tests_dir.mkdir()
        for i in range(30):
            p = tests_dir / f"test_{i:03d}.py"
            p.write_text(f"def test_f{i}(): pass")

        # Set the first 25 files to an old mtime
        old_ts = _time.time() - 86400
        for i in range(25):
            f = tests_dir / f"test_{i:03d}.py"
            os.utime(f, (old_ts, old_ts))

        with patch("pdd.agentic_e2e_fix_orchestrator._get_modified_and_untracked", return_value=set()):
            result = _extract_test_files(
                issue_content="",
                changed_files=[],
                cwd=tmp_path,
                initial_file_hashes=None,
            )

        # The 5 recent files (test_025..test_029) should all be in the result
        recent_names = {f"tests/test_{i:03d}.py" for i in range(25, 30)}
        assert recent_names.issubset(set(result)), (
            f"Recently modified files missing from capped result: "
            f"{recent_names - set(result)}"
        )


class TestGetModifiedAndUntrackedOriginRefs:
    """_get_modified_and_untracked must try origin/ refs for shallow clones."""

    def test_tries_origin_refs_when_local_refs_fail(self, tmp_path):
        """When local main/master fail, origin/main and origin/master are tried."""
        from pdd.agentic_e2e_fix_orchestrator import _get_modified_and_untracked

        call_log = []

        def mock_subprocess_run(cmd, **kwargs):
            call_log.append(cmd)
            cmd_str = " ".join(cmd)
            mock_result = MagicMock()

            if "merge-base" in cmd_str:
                if "origin/main" in cmd_str:
                    mock_result.returncode = 0
                    mock_result.stdout = "abc123\n"
                    return mock_result
                else:
                    mock_result.returncode = 128
                    mock_result.stdout = ""
                    return mock_result

            if "diff" in cmd_str and "abc123" in cmd_str:
                mock_result.returncode = 0
                mock_result.stdout = "tests/test_new.py\nsrc/module.py\n"
                return mock_result

            mock_result.returncode = 0
            mock_result.stdout = ""
            return mock_result

        with patch("pdd.agentic_e2e_fix_orchestrator.subprocess.run", side_effect=mock_subprocess_run):
            files = _get_modified_and_untracked(tmp_path)

        merge_base_cmds = [c for c in call_log if "merge-base" in " ".join(c)]
        origin_tried = any("origin/main" in " ".join(c) for c in merge_base_cmds)
        assert origin_tried, f"origin/main never tried. Commands: {merge_base_cmds}"
        assert "tests/test_new.py" in files

    def test_falls_through_all_refs_gracefully(self, tmp_path):
        """When all 4 refs fail, uncommitted/untracked files still returned."""
        from pdd.agentic_e2e_fix_orchestrator import _get_modified_and_untracked

        def mock_subprocess_run(cmd, **kwargs):
            cmd_str = " ".join(cmd)
            mock_result = MagicMock()

            if "merge-base" in cmd_str:
                mock_result.returncode = 128
                mock_result.stdout = ""
                return mock_result

            if "diff" in cmd_str and "HEAD" in cmd_str:
                mock_result.returncode = 0
                mock_result.stdout = "modified_file.py\n"
                return mock_result

            if "ls-files" in cmd_str:
                mock_result.returncode = 0
                mock_result.stdout = "untracked_file.py\n"
                return mock_result

            mock_result.returncode = 0
            mock_result.stdout = ""
            return mock_result

        with patch("pdd.agentic_e2e_fix_orchestrator.subprocess.run", side_effect=mock_subprocess_run):
            files = _get_modified_and_untracked(tmp_path)

        assert "modified_file.py" in files
        assert "untracked_file.py" in files


class TestGetModifiedAndUntrackedSubprocessTimeout:
    """_get_modified_and_untracked must use timeout=30 and handle TimeoutExpired."""

    def test_handles_timeout_on_git_diff_head(self, tmp_path):
        """TimeoutExpired on git diff HEAD is caught; partial results returned."""
        from pdd.agentic_e2e_fix_orchestrator import _get_modified_and_untracked

        def mock_subprocess_run(cmd, **kwargs):
            cmd_str = " ".join(cmd)

            if "diff" in cmd_str and "HEAD" in cmd_str:
                raise subprocess.TimeoutExpired(cmd=cmd, timeout=30)

            mock_result = MagicMock()
            if "ls-files" in cmd_str:
                mock_result.returncode = 0
                mock_result.stdout = "untracked.py\n"
                return mock_result

            mock_result.returncode = 128
            mock_result.stdout = ""
            return mock_result

        with patch("pdd.agentic_e2e_fix_orchestrator.subprocess.run", side_effect=mock_subprocess_run):
            files = _get_modified_and_untracked(tmp_path)

        assert isinstance(files, set)
        assert "untracked.py" in files

    def test_handles_timeout_on_merge_base_call(self, tmp_path):
        """TimeoutExpired on merge-base is caught; other refs still tried."""
        from pdd.agentic_e2e_fix_orchestrator import _get_modified_and_untracked

        def mock_subprocess_run(cmd, **kwargs):
            cmd_str = " ".join(cmd)
            mock_result = MagicMock()

            if "merge-base" in cmd_str and "main" in cmd_str and "origin" not in cmd_str:
                raise subprocess.TimeoutExpired(cmd=cmd, timeout=30)

            if "diff" in cmd_str and "HEAD" in cmd_str:
                mock_result.returncode = 0
                mock_result.stdout = "changed.py\n"
                return mock_result

            if "ls-files" in cmd_str:
                mock_result.returncode = 0
                mock_result.stdout = ""
                return mock_result

            mock_result.returncode = 128
            mock_result.stdout = ""
            return mock_result

        with patch("pdd.agentic_e2e_fix_orchestrator.subprocess.run", side_effect=mock_subprocess_run):
            files = _get_modified_and_untracked(tmp_path)

        assert "changed.py" in files
