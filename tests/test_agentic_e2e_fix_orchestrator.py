"""Tests for agentic_e2e_fix_orchestrator prompt formatting and runtime behavior.

These tests verify that all e2e fix workflow prompts can be formatted
with the context variables provided by the orchestrator, without
raising KeyError on undefined placeholders.

Additionally, tests verify the orchestrator's runtime behavior including
early exit conditions (issue #468).
"""
import pytest
from unittest.mock import patch
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

            if cmd == ["git", "push"] and call_count == 1:
                # First push fails with auth error
                result.returncode = 1
                result.stderr = "fatal: Authentication failed for 'https://github.com/owner/repo.git'"
            elif cmd[0:3] == ["git", "remote", "get-url"]:
                result.stdout = "https://github.com/owner/repo.git"
            elif cmd[0:3] == ["git", "remote", "set-url"]:
                pass  # No-op
            elif cmd == ["git", "push"] and call_count > 1:
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

            if cmd == ["git", "push"]:
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

            if cmd == ["git", "push"] and call_count == 1:
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
