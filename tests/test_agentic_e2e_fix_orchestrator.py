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


# --- Template preprocessing fix Tests: Preprocessing and Format Error Handling ---


class TestTemplatePreprocessingAndFormatErrorHandling:
    """Tests for template preprocessing fix: Template .format(**context) failure handling.

    The bug: Template `.format(**context)` calls fail when:
    1. `<include>` directives aren't preprocessed (LLM doesn't receive full context)
    2. Curly braces in included content (JSON, shell vars) break `format()`
    3. No try/except around `.format()` call

    These tests verify the fix:
    1. Templates are preprocessed before formatting
    2. Curly braces in included content are escaped
    3. KeyError, ValueError, and other exceptions are caught gracefully
    4. Preprocessing failures are non-fatal (logged as warnings)
    """

    @pytest.fixture
    def mock_dependencies(self, tmp_path):
        """
        Mocks external dependencies for e2e fix orchestrator tests.
        """
        from unittest.mock import patch, MagicMock

        with patch("pdd.agentic_e2e_fix_orchestrator.run_agentic_task") as mock_run, \
             patch("pdd.agentic_e2e_fix_orchestrator.load_prompt_template") as mock_load, \
             patch("pdd.agentic_e2e_fix_orchestrator.console") as mock_console, \
             patch("pdd.agentic_e2e_fix_orchestrator.preprocess") as mock_preprocess, \
             patch("pdd.agentic_e2e_fix_orchestrator.load_workflow_state") as mock_load_state, \
             patch("pdd.agentic_e2e_fix_orchestrator.save_workflow_state") as mock_save_state, \
             patch("pdd.agentic_e2e_fix_orchestrator.clear_workflow_state") as mock_clear_state:

            # Default behavior: successful run
            mock_run.return_value = (True, "Step output", 0.1, "gpt-4")
            # Default: return a simple template
            mock_load.return_value = "Prompt for {issue_number}"
            # Default: preprocess returns template unchanged
            mock_preprocess.side_effect = lambda t, **kwargs: t
            # Default: no saved state
            mock_load_state.return_value = (None, None)
            mock_save_state.return_value = None
            mock_clear_state.return_value = None

            yield {
                "run": mock_run,
                "load": mock_load,
                "console": mock_console,
                "preprocess": mock_preprocess,
                "load_state": mock_load_state,
                "save_state": mock_save_state,
                "clear_state": mock_clear_state,
            }

    @pytest.fixture
    def default_args(self, tmp_path):
        """Provides default arguments for the orchestrator function."""
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

    def test_template_preprocessing_include_directives_are_preprocessed(
        self, mock_dependencies, default_args
    ):
        """Verify that <include> directives are expanded via preprocess().

        Template preprocessing fix: Templates containing <include> directives were not being
        preprocessed, so the LLM received unexpanded directives instead of
        the included file content.

        This test verifies that preprocess() is called for each step's template.
        """
        from pdd.agentic_e2e_fix_orchestrator import run_agentic_e2e_fix_orchestrator

        mocks = mock_dependencies

        # Track preprocess calls
        preprocess_calls = []

        def track_preprocess(template, **kwargs):
            preprocess_calls.append({
                "template": template,
                "kwargs": kwargs,
            })
            return template  # Return unchanged for simplicity

        mocks["preprocess"].side_effect = track_preprocess

        # Mock step 2 to return ALL_TESTS_PASS for early exit
        def side_effect_run(*args, **kwargs):
            label = kwargs.get("label", "")
            if "step2" in label:
                return (True, "ALL_TESTS_PASS", 0.1, "gpt-4")
            return (True, "Step output", 0.1, "gpt-4")

        mocks["run"].side_effect = side_effect_run

        run_agentic_e2e_fix_orchestrator(**default_args)

        # Verify preprocess was called at least once (for step 1 and step 2)
        assert len(preprocess_calls) >= 2, (
            f"preprocess() should be called for each step, but was called "
            f"{len(preprocess_calls)} times"
        )

        # Verify preprocess was called with correct parameters
        for call in preprocess_calls:
            assert "recursive" in call["kwargs"], "preprocess should be called with recursive parameter"
            assert call["kwargs"]["recursive"] is False, "recursive should be False"
            assert "double_curly_brackets" in call["kwargs"], "preprocess should be called with double_curly_brackets"
            assert call["kwargs"]["double_curly_brackets"] is True, "double_curly_brackets should be True"
            assert "exclude_keys" in call["kwargs"], "preprocess should be called with exclude_keys"

    def test_template_preprocessing_curly_braces_in_included_content_are_escaped(
        self, mock_dependencies, default_args
    ):
        """Verify that curly braces in included content are escaped via double_curly_brackets.

        Template preprocessing fix: When <include> directives pulled in content containing
        JSON objects or shell variables like `${VAR}`, the curly braces would
        break Python's str.format() method.

        This test verifies that preprocess() is called with double_curly_brackets=True,
        which escapes single braces to prevent format() failures.
        """
        from pdd.agentic_e2e_fix_orchestrator import run_agentic_e2e_fix_orchestrator

        mocks = mock_dependencies

        # Template with include directive that would expand to JSON
        mocks["load"].return_value = "Config: <include>config.json</include> for {issue_number}"

        # Track what preprocess receives
        preprocess_kwargs = []

        def track_preprocess(template, **kwargs):
            preprocess_kwargs.append(kwargs)
            # Simulate preprocessing with double_curly_brackets enabled
            # This would escape {"key": "value"} to {{"key": "value"}}
            return template.replace("<include>config.json</include>", '{{\"key\": \"value\"}}')

        mocks["preprocess"].side_effect = track_preprocess

        # Early exit at step 2
        def side_effect_run(*args, **kwargs):
            label = kwargs.get("label", "")
            if "step2" in label:
                return (True, "ALL_TESTS_PASS", 0.1, "gpt-4")
            return (True, "Step output", 0.1, "gpt-4")

        mocks["run"].side_effect = side_effect_run

        success, msg, cost, model, files = run_agentic_e2e_fix_orchestrator(**default_args)

        # Should succeed (early exit at step 2)
        assert success is True, f"Should succeed with ALL_TESTS_PASS, but got: {msg}"

        # Verify double_curly_brackets=True was passed
        assert len(preprocess_kwargs) > 0, "preprocess should have been called"
        for kwargs in preprocess_kwargs:
            assert kwargs.get("double_curly_brackets") is True, (
                "preprocess should be called with double_curly_brackets=True to escape JSON braces"
            )

    def test_template_preprocessing_valueerror_from_format_is_caught(
        self, mock_dependencies, default_args
    ):
        """Verify that ValueError from format() is caught and returns graceful error.

        Template preprocessing fix: When format() encounters invalid format strings (e.g., unmatched
        braces like `{` without `}`), it raises ValueError. Without try/except,
        this would crash the orchestrator.

        This test verifies that ValueError is caught and returns a proper error tuple.
        """
        from pdd.agentic_e2e_fix_orchestrator import run_agentic_e2e_fix_orchestrator

        mocks = mock_dependencies

        # Return a template with an invalid format string (unmatched brace)
        mocks["load"].return_value = "Invalid format: {unclosed brace"

        # preprocess returns it unchanged (simulating failed brace escaping)
        mocks["preprocess"].side_effect = lambda t, **kwargs: t

        success, msg, cost, model, files = run_agentic_e2e_fix_orchestrator(**default_args)

        # Should fail gracefully
        assert success is False, "Should fail when format() raises ValueError"
        assert "formatting error" in msg.lower() or "invalid format" in msg.lower(), (
            f"Error message should mention formatting error, got: {msg}"
        )
        assert "step 1" in msg.lower(), f"Error should mention which step failed, got: {msg}"

    def test_template_preprocessing_generic_exception_from_format_is_caught(
        self, mock_dependencies, default_args
    ):
        """Verify that generic exceptions from format() are caught.

        Template preprocessing fix: Any unexpected exception from format() should be caught
        and converted to a graceful error return.

        This test verifies that generic Exception is caught by using a template
        class that raises an exception when format() is called.
        """
        from pdd.agentic_e2e_fix_orchestrator import run_agentic_e2e_fix_orchestrator

        mocks = mock_dependencies

        # Create a custom string subclass that raises on format()
        class BadFormatString(str):
            def format(self, *args, **kwargs):
                raise RuntimeError("Simulated format failure")

        # Return a template that will raise on format()
        bad_template = BadFormatString("Template: {issue_number}")
        mocks["load"].return_value = bad_template
        # preprocess returns the same bad template
        mocks["preprocess"].side_effect = lambda t, **kwargs: t

        success, msg, cost, model, files = run_agentic_e2e_fix_orchestrator(**default_args)

        # Should fail gracefully
        assert success is False, "Should fail when format() raises RuntimeError"
        assert "formatting error" in msg.lower() or "runtimeerror" in msg.lower(), (
            f"Error message should mention the error type, got: {msg}"
        )

    def test_template_preprocessing_preprocessing_failure_is_non_fatal(
        self, mock_dependencies, default_args
    ):
        """Verify that preprocessing failures are logged as warnings but don't halt execution.

        Template preprocessing fix: If preprocess() fails (e.g., missing include file), it should
        log a warning but continue with the unpreprocessed template. This allows
        the workflow to continue and potentially succeed if the include wasn't
        critical.

        This test verifies that preprocessing exceptions are caught and logged,
        and the workflow continues.
        """
        from pdd.agentic_e2e_fix_orchestrator import run_agentic_e2e_fix_orchestrator

        mocks = mock_dependencies
        default_args["quiet"] = False  # Enable console output to verify warning

        # Make preprocess raise an exception
        mocks["preprocess"].side_effect = FileNotFoundError("Include file not found: missing.txt")

        # Template that would work without preprocessing
        mocks["load"].return_value = "Simple template for issue {issue_number}"

        # Early exit at step 2
        def side_effect_run(*args, **kwargs):
            label = kwargs.get("label", "")
            if "step2" in label:
                return (True, "ALL_TESTS_PASS", 0.1, "gpt-4")
            return (True, "Step output", 0.1, "gpt-4")

        mocks["run"].side_effect = side_effect_run

        success, msg, cost, model, files = run_agentic_e2e_fix_orchestrator(**default_args)

        # Should still succeed because preprocessing failure is non-fatal
        assert success is True, (
            f"Workflow should continue after preprocessing failure, but got: {msg}"
        )

        # Verify warning was printed (check console.print calls)
        warning_calls = [
            call for call in mocks["console"].print.call_args_list
            if "Warning" in str(call) and "Preprocessing failed" in str(call)
        ]
        assert len(warning_calls) > 0, (
            "Should have printed a warning about preprocessing failure"
        )

    def test_template_preprocessing_exclude_keys_contains_context_variables(
        self, mock_dependencies, default_args
    ):
        """Verify that context keys are passed to preprocess as exclude_keys.

        Template preprocessing fix: The preprocess function should receive the context keys
        as exclude_keys so that template placeholders like {issue_number}
        are not escaped (they need to remain as single braces for format()).

        This test verifies that exclude_keys matches the context keys.
        """
        from pdd.agentic_e2e_fix_orchestrator import run_agentic_e2e_fix_orchestrator

        mocks = mock_dependencies

        # Track exclude_keys passed to preprocess
        exclude_keys_received = []

        def track_preprocess(template, **kwargs):
            exclude_keys_received.append(kwargs.get("exclude_keys", []))
            return template

        mocks["preprocess"].side_effect = track_preprocess

        # Early exit at step 2
        def side_effect_run(*args, **kwargs):
            label = kwargs.get("label", "")
            if "step2" in label:
                return (True, "ALL_TESTS_PASS", 0.1, "gpt-4")
            return (True, "Step output", 0.1, "gpt-4")

        mocks["run"].side_effect = side_effect_run

        run_agentic_e2e_fix_orchestrator(**default_args)

        # Verify exclude_keys contains expected context variables
        assert len(exclude_keys_received) > 0, "preprocess should have been called"

        # Check step 1 context keys (first call)
        step1_keys = exclude_keys_received[0]
        expected_keys = [
            "issue_url",
            "repo_owner",
            "repo_name",
            "issue_number",
            "cycle_number",
            "max_cycles",
            "issue_content",
            "protect_tests",
            "protect_tests_flag",
        ]
        for key in expected_keys:
            assert key in step1_keys, (
                f"Expected context key '{key}' in exclude_keys, got: {step1_keys}"
            )

    def test_template_preprocessing_keyerror_from_format_is_caught(
        self, mock_dependencies, default_args
    ):
        """Verify that KeyError from format() is caught and returns graceful error.

        Template preprocessing fix: When format() encounters a placeholder like {missing_var}
        that doesn't exist in the context dict, it raises KeyError. Without try/except,
        this would crash the orchestrator.

        This test verifies that KeyError is caught and returns a proper error tuple
        with the missing key name.
        """
        from pdd.agentic_e2e_fix_orchestrator import run_agentic_e2e_fix_orchestrator

        mocks = mock_dependencies

        # Return a template with a placeholder not in context
        mocks["load"].return_value = "Template with {issue_number} and {nonexistent_variable}"

        # preprocess returns it unchanged
        mocks["preprocess"].side_effect = lambda t, **kwargs: t

        success, msg, cost, model, files = run_agentic_e2e_fix_orchestrator(**default_args)

        # Should fail gracefully
        assert success is False, "Should fail when format() raises KeyError"
        assert "formatting error" in msg.lower() or "missing key" in msg.lower(), (
            f"Error message should mention formatting error or missing key, got: {msg}"
        )
        assert "nonexistent_variable" in msg, (
            f"Error message should mention the missing key name, got: {msg}"
        )
        assert "step 1" in msg.lower(), f"Error should mention which step failed, got: {msg}"

    def test_template_preprocessing_quiet_mode_suppresses_warning(
        self, mock_dependencies, default_args
    ):
        """Verify that quiet=True suppresses preprocessing warning output.

        Template preprocessing fix: When preprocessing fails and quiet=True, no warning should
        be printed to the console. This keeps output clean in automated/batch runs.

        This test verifies that console.print is NOT called with a warning when quiet=True.
        """
        from pdd.agentic_e2e_fix_orchestrator import run_agentic_e2e_fix_orchestrator

        mocks = mock_dependencies
        default_args["quiet"] = True  # Ensure quiet mode is on

        # Make preprocess raise an exception
        mocks["preprocess"].side_effect = FileNotFoundError("Include file not found: missing.txt")

        # Template that would work without preprocessing
        mocks["load"].return_value = "Simple template for issue {issue_number}"

        # Early exit at step 2
        def side_effect_run(*args, **kwargs):
            label = kwargs.get("label", "")
            if "step2" in label:
                return (True, "ALL_TESTS_PASS", 0.1, "gpt-4")
            return (True, "Step output", 0.1, "gpt-4")

        mocks["run"].side_effect = side_effect_run

        success, msg, cost, model, files = run_agentic_e2e_fix_orchestrator(**default_args)

        # Should still succeed because preprocessing failure is non-fatal
        assert success is True, (
            f"Workflow should continue after preprocessing failure, but got: {msg}"
        )

        # Verify NO warning was printed (quiet=True should suppress it)
        warning_calls = [
            call for call in mocks["console"].print.call_args_list
            if "Warning" in str(call) and "Preprocessing failed" in str(call)
        ]
        assert len(warning_calls) == 0, (
            f"Should NOT print warning when quiet=True, but found: {warning_calls}"
        )

    def test_template_preprocessing_formatted_prompt_reaches_run_agentic_task(
        self, mock_dependencies, default_args
    ):
        """Verify that the preprocessed and formatted prompt is passed to run_agentic_task.

        Template preprocessing fix: This is an integration check to ensure the preprocessing
        and formatting pipeline actually delivers the correct content to the LLM task runner.

        This test verifies that run_agentic_task receives the fully processed prompt.
        """
        from pdd.agentic_e2e_fix_orchestrator import run_agentic_e2e_fix_orchestrator

        mocks = mock_dependencies

        # Template with include directive
        mocks["load"].return_value = "Issue {issue_number}: <include>file.txt</include>"

        # Simulate preprocessing that expands the include
        def simulate_preprocess(template, **kwargs):
            return template.replace("<include>file.txt</include>", "INCLUDED_CONTENT")

        mocks["preprocess"].side_effect = simulate_preprocess

        # Track what run_agentic_task receives
        received_instructions = []

        def track_run(*args, **kwargs):
            received_instructions.append(kwargs.get("instruction", ""))
            label = kwargs.get("label", "")
            if "step2" in label:
                return (True, "ALL_TESTS_PASS", 0.1, "gpt-4")
            return (True, "Step output", 0.1, "gpt-4")

        mocks["run"].side_effect = track_run

        run_agentic_e2e_fix_orchestrator(**default_args)

        # Verify run_agentic_task was called
        assert len(received_instructions) >= 1, "run_agentic_task should have been called"

        # Verify the instruction contains the preprocessed content
        step1_instruction = received_instructions[0]
        assert "INCLUDED_CONTENT" in step1_instruction, (
            f"Preprocessed content should be in instruction, got: {step1_instruction}"
        )
        assert "Issue 1:" in step1_instruction, (
            f"Formatted issue_number should be in instruction, got: {step1_instruction}"
        )
        assert "<include>" not in step1_instruction, (
            f"Include directive should be expanded, got: {step1_instruction}"
        )

    def test_template_preprocessing_step9_includes_next_cycle_in_exclude_keys(
        self, mock_dependencies, default_args
    ):
        """Verify that step 9 adds next_cycle to the context and exclude_keys.

        Template preprocessing fix: Step 9 is special because it adds `next_cycle` to context
        (for cycle transition). This test verifies that when step 9 runs,
        the exclude_keys includes `next_cycle`.

        This test runs through to step 9 to verify the context accumulation.
        """
        from pdd.agentic_e2e_fix_orchestrator import run_agentic_e2e_fix_orchestrator

        mocks = mock_dependencies

        # Track exclude_keys for each step
        exclude_keys_by_step = {}

        def track_preprocess(template, **kwargs):
            # We'll identify step by counting calls
            call_num = len(exclude_keys_by_step) + 1
            exclude_keys_by_step[call_num] = kwargs.get("exclude_keys", [])
            return template

        mocks["preprocess"].side_effect = track_preprocess

        # Run through all steps without early exit, but stop at step 9
        step_counter = [0]

        def side_effect_run(*args, **kwargs):
            step_counter[0] += 1
            label = kwargs.get("label", "")
            # Step 2 should not return ALL_TESTS_PASS to continue workflow
            if "step2" in label:
                return (True, "Tests failed: test_foo.py", 0.1, "gpt-4")
            # Step 5 needs to return dev units
            if "step5" in label:
                return (True, "dev_unit: module_a", 0.1, "gpt-4")
            # Step 8 signals need for another cycle (triggers step 9)
            if "step8" in label:
                return (True, "NEEDS_ANOTHER_CYCLE", 0.1, "gpt-4")
            # Step 9 completes the cycle
            if "step9" in label:
                return (True, "Cycle transition complete", 0.1, "gpt-4")
            return (True, "Step output", 0.1, "gpt-4")

        mocks["run"].side_effect = side_effect_run

        # Set max_cycles=1 so we only do one cycle and step 9 triggers
        default_args["max_cycles"] = 2

        run_agentic_e2e_fix_orchestrator(**default_args)

        # Find the step 9 call (should be call #9)
        # Note: Steps are 1,2,3,4,5,6,7,8,9 so step 9 is the 9th preprocess call
        assert 9 in exclude_keys_by_step, (
            f"Step 9 should have been reached, only got steps: {list(exclude_keys_by_step.keys())}"
        )

        step9_keys = exclude_keys_by_step[9]
        assert "next_cycle" in step9_keys, (
            f"Step 9 should have 'next_cycle' in exclude_keys, got: {step9_keys}"
        )

    def test_template_preprocessing_later_steps_have_accumulated_context(
        self, mock_dependencies, default_args
    ):
        """Verify that later steps have accumulated outputs from earlier steps in context.

        Template preprocessing fix: As the workflow progresses, step outputs are accumulated
        in the context dict. For example, step 3 should have access to step 1 and 2 outputs.
        This test verifies that exclude_keys grows as steps complete.

        This test runs through multiple steps and checks context accumulation.
        """
        from pdd.agentic_e2e_fix_orchestrator import run_agentic_e2e_fix_orchestrator

        mocks = mock_dependencies

        # Track exclude_keys for each preprocess call
        exclude_keys_per_call = []

        def track_preprocess(template, **kwargs):
            exclude_keys_per_call.append(kwargs.get("exclude_keys", []))
            return template

        mocks["preprocess"].side_effect = track_preprocess

        # Run through steps 1-3 (step 2 fails tests, triggering step 3)
        def side_effect_run(*args, **kwargs):
            label = kwargs.get("label", "")
            if "step2" in label:
                # Return failing tests to continue to step 3
                return (True, "Tests failed: test_foo.py::test_bar", 0.1, "gpt-4")
            if "step3" in label:
                # Step 3 completes, then we'll exit by having step 4-8 succeed quickly
                return (True, "Root cause: missing null check", 0.1, "gpt-4")
            if "step4" in label:
                return (True, "E2E tests analysis complete", 0.1, "gpt-4")
            if "step5" in label:
                return (True, "dev_unit: module_a", 0.1, "gpt-4")
            if "step6" in label:
                return (True, "Fix applied", 0.1, "gpt-4")
            if "step7" in label:
                return (True, "Fix verified", 0.1, "gpt-4")
            if "step8" in label:
                # Return ALL_TESTS_PASS to end the workflow
                return (True, "ALL_TESTS_PASS", 0.1, "gpt-4")
            return (True, "Step output", 0.1, "gpt-4")

        mocks["run"].side_effect = side_effect_run

        run_agentic_e2e_fix_orchestrator(**default_args)

        # Should have at least 8 preprocess calls (steps 1-8)
        assert len(exclude_keys_per_call) >= 8, (
            f"Should have run at least 8 steps, but only got {len(exclude_keys_per_call)} preprocess calls"
        )

        # Step 1 should have base context keys
        step1_keys = set(exclude_keys_per_call[0])
        assert "issue_number" in step1_keys, "Step 1 should have issue_number"

        # Step 3 (index 2) should have step 1 and 2 outputs added
        step3_keys = set(exclude_keys_per_call[2])
        assert "step1_output" in step3_keys, (
            f"Step 3 should have step1_output in context, got: {step3_keys}"
        )
        assert "step2_output" in step3_keys, (
            f"Step 3 should have step2_output in context, got: {step3_keys}"
        )

        # Step 7 (index 6) should have outputs from steps 1-6
        step7_keys = set(exclude_keys_per_call[6])
        for i in range(1, 7):
            assert f"step{i}_output" in step7_keys, (
                f"Step 7 should have step{i}_output in context, got: {step7_keys}"
            )
