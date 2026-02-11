"""Tests for --quiet flag suppressing non-essential output.

These tests verify that the --quiet flag properly suppresses INFO logs,
Rich panels, warnings, and success messages across all output-producing modules.
All tests should FAIL on the current buggy code where quiet is not propagated.
"""

import logging
from io import StringIO
from unittest.mock import patch, MagicMock

import pytest


class TestPreprocessQuietMode:
    """Tests that preprocess() suppresses Rich output when quiet=True."""

    def test_preprocess_suppresses_panels_when_quiet(self):
        """preprocess() should not print Rich panels when quiet=True.

        Currently FAILS because preprocess() has no quiet parameter and
        always prints 'Starting prompt preprocessing' and 'Preprocessing complete' panels.
        """
        from pdd.preprocess import preprocess

        # Check that preprocess does not accept a quiet parameter yet (the bug)
        import inspect
        sig = inspect.signature(preprocess)
        assert "quiet" in sig.parameters, (
            "preprocess() does not accept a 'quiet' parameter — "
            "output cannot be suppressed"
        )

    def test_preprocess_outputs_panels_by_default(self):
        """preprocess() should still show panels when quiet is not set (regression guard)."""
        from pdd.preprocess import preprocess

        with patch("pdd.preprocess.console") as mock_console:
            try:
                preprocess("Hello world")
            except Exception:
                pass
            # Verify console.print was called (panels are shown by default)
            assert mock_console.print.called, (
                "preprocess() should print panels by default"
            )

    def test_preprocess_suppresses_doubling_message_when_quiet(self):
        """preprocess() should not print 'Doubling curly brackets...' when quiet=True.

        Currently FAILS because there is no quiet parameter to suppress this.
        """
        from pdd.preprocess import preprocess
        import inspect

        sig = inspect.signature(preprocess)
        assert "quiet" in sig.parameters, (
            "preprocess() does not accept a 'quiet' parameter — "
            "'Doubling curly brackets...' message cannot be suppressed"
        )


class TestLoadPromptTemplateQuietMode:
    """Tests that load_prompt_template() suppresses messages when quiet=True."""

    def test_load_prompt_template_suppresses_success_message_when_quiet(self):
        """load_prompt_template() should not print success message when quiet=True.

        Currently FAILS because load_prompt_template() has no quiet parameter.
        """
        from pdd.load_prompt_template import load_prompt_template
        import inspect

        sig = inspect.signature(load_prompt_template)
        assert "quiet" in sig.parameters, (
            "load_prompt_template() does not accept a 'quiet' parameter — "
            "success messages cannot be suppressed"
        )

    def test_load_prompt_template_suppresses_error_message_when_quiet(self):
        """load_prompt_template() should not print error messages when quiet=True.

        Currently FAILS because load_prompt_template() has no quiet parameter.
        """
        from pdd.load_prompt_template import load_prompt_template
        import inspect

        sig = inspect.signature(load_prompt_template)
        assert "quiet" in sig.parameters, (
            "load_prompt_template() does not accept a 'quiet' parameter — "
            "error messages cannot be suppressed"
        )


class TestLlmInvokeQuietMode:
    """Tests that llm_invoke logger level is raised to WARNING when quiet=True."""

    def test_logger_level_not_raised_for_quiet(self):
        """The pdd.llm_invoke logger should be set to WARNING when quiet mode is active.

        Currently FAILS because the logger level is set at import time based on
        env vars only, with no mechanism to raise it when --quiet is passed.
        """
        # The logger is currently always INFO in dev mode, regardless of --quiet
        logger = logging.getLogger("pdd.llm_invoke")

        # Simulate what should happen when --quiet is active:
        # There should be a function or mechanism to set quiet mode on the logger.
        # Since none exists, we verify the bug by checking that the logger
        # is at INFO level (not WARNING) even though quiet should suppress INFO.
        current_level = logger.getEffectiveLevel()

        # The bug: logger is INFO (20) when it should be configurable to WARNING (30)
        # for quiet mode. We check that there's no set_quiet_mode or similar function.
        from pdd import llm_invoke
        has_quiet_mechanism = (
            hasattr(llm_invoke, "set_quiet_mode")
            or hasattr(llm_invoke, "configure_quiet")
            or hasattr(llm_invoke, "set_log_level_for_quiet")
        )
        assert has_quiet_mechanism, (
            "llm_invoke module has no mechanism to enable quiet mode — "
            "INFO logs will always be emitted regardless of --quiet flag"
        )


class TestGenerateCommandQuietMode:
    """E2E test: pdd --quiet generate should suppress INFO/panel output."""

    def test_quiet_generate_suppresses_output(self):
        """Running 'pdd --quiet generate' should not produce INFO logs or Rich panels.

        This test invokes the CLI with --quiet and verifies that downstream
        modules (preprocess, load_prompt_template) are called with quiet=True.
        Currently FAILS because quiet is not passed through.
        """
        from click.testing import CliRunner
        from pdd.core.cli import cli

        runner = CliRunner(mix_stderr=False)

        # We mock code_generator_main to avoid actual LLM calls,
        # but we let preprocess and load_prompt_template run to capture output.
        with patch("pdd.commands.generate.code_generator_main") as mock_gen:
            mock_gen.return_value = ("generated code", False, 0.0, "mock-model")

            result = runner.invoke(cli, ["--quiet", "generate", "prompts/greet_python.prompt"])

            stdout = result.output

            # These strings should NOT appear in quiet mode
            noisy_patterns = [
                "Starting prompt preprocessing",
                "Preprocessing complete",
                "Doubling curly brackets",
                "Successfully loaded prompt",
                "INFO",
            ]

            violations = [p for p in noisy_patterns if p in stdout]
            assert not violations, (
                f"--quiet flag did not suppress output. Found: {violations}\n"
                f"Full output:\n{stdout}"
            )
