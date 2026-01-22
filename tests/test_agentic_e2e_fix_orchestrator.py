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
    """E2E tests for issue #360: Verify CLI behavior when log file is passed in loop mode.

    These tests exercise the full CLI path to verify that passing a .log file
    as a positional argument in --loop mode causes pytest to fail with collection
    errors. This is the actual user-facing bug behavior.

    The unit tests in TestLoopModeNoLogFile check the prompt templates.
    These E2E tests verify the CLI behavior that results from following
    those buggy prompt instructions.
    """

    @pytest.fixture
    def loop_mode_test_files(self, tmp_path):
        """Create minimal files needed to run pdd fix --manual --loop.

        Returns a dict with paths to:
        - prompt_file: A minimal prompt file
        - code_file: A simple code file with a bug
        - test_file: A passing test file
        - log_file: An empty .log file (the problematic extra argument)
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

        # Create the problematic log file (what the buggy prompt instructs LLM to create)
        log_file = tmp_path / "pdd_fix_errors_calculator.log"
        log_file.write_text("")  # Empty log file

        return {
            "prompt_file": str(prompt_file),
            "code_file": str(code_file),
            "test_file": str(test_file),
            "log_file": str(log_file),
            "tmp_path": tmp_path,
        }

    def test_loop_mode_with_log_file_causes_pytest_collection_error(
        self, loop_mode_test_files, monkeypatch
    ):
        """E2E Test: Passing a .log file to pdd fix --loop causes pytest failures.

        Issue #360: The prompts instruct the LLM to run:
            pdd fix --manual PROMPT CODE TEST /tmp/pdd_fix_errors.log --loop

        In loop mode, fix.py treats ALL args after CODE as test files:
            unit_test_files = args[2:]  # [TEST, /tmp/.../errors.log]

        Then pytest is invoked with both files, and fails because it cannot
        collect tests from the .log file (exit code 4 = collection error).

        This E2E test verifies this bug by:
        1. Calling the CLI with the exact pattern from the buggy prompts
        2. Checking that the command fails due to pytest collection errors
        3. Verifying the error message mentions the log file

        The test FAILS on buggy code (the bug causes the error we're testing for).
        The test PASSES once the prompts are fixed (no log file = no error).
        """
        from click.testing import CliRunner
        from pdd import cli

        files = loop_mode_test_files
        monkeypatch.chdir(files["tmp_path"])
        monkeypatch.setenv("PDD_FORCE_LOCAL", "1")
        monkeypatch.setenv("OPENAI_API_KEY", "fake-key-for-testing")

        runner = CliRunner()

        # This is the exact command pattern from the buggy prompts (Step 1 & Step 8):
        # pdd fix --manual PROMPT CODE TEST LOG_FILE --loop
        # Note: The log file comes BEFORE --loop, making it a positional arg
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
                files["log_file"],  # This is the bug: log file as positional arg
            ],
            catch_exceptions=False,
        )

        # THE BUG: The command should NOT fail with collection errors
        # But on buggy code, pytest tries to collect from .log file and fails

        # Check if the output mentions the log file being processed as a test file
        # This pattern indicates the bug: pytest treating .log as test file
        log_file_in_output = "pdd_fix_errors_calculator.log" in result.output
        processing_multiple_files = "Processing test file" in result.output and "/2" in result.output

        # If either condition is true, the bug is present
        bug_is_present = log_file_in_output or processing_multiple_files

        # This assertion is designed to FAIL when the bug exists
        # (which means it correctly detects the bug on buggy code)
        assert not bug_is_present, (
            "BUG DETECTED (Issue #360): The log file was incorrectly treated as a test file!\n\n"
            f"Command output shows the .log file being processed:\n{result.output}\n\n"
            "This happens because fix.py in loop mode treats ALL args after CODE as test files.\n"
            "The prompts should NOT include the log file argument when using --loop mode."
        )

    def test_loop_mode_without_log_file_processes_single_test_file(
        self, loop_mode_test_files, monkeypatch
    ):
        """E2E Test: pdd fix --loop without log file only processes one test file.

        This test verifies the CORRECT behavior: when pdd fix --manual --loop
        is called with just PROMPT CODE TEST (no log file), it should only
        process one test file, not two.

        This is a contrast to test_loop_mode_with_log_file_causes_pytest_collection_error
        which shows "Processing test file 1/2" due to the bug.

        This test should PASS on both buggy and fixed code - it's a baseline
        to ensure the fix doesn't break the normal case.
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
