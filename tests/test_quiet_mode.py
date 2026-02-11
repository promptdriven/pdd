"""Tests for --quiet flag suppressing non-essential output.

These tests verify that the --quiet flag properly suppresses INFO logs,
Rich panels, warnings, and success messages across all output-producing modules.
"""

import logging
from unittest.mock import patch
from pathlib import Path

import pytest


class TestPreprocessQuietMode:
    """Tests that preprocess() suppresses Rich output when quiet=True."""

    def test_preprocess_suppresses_panels_when_quiet(self):
        """preprocess(quiet=True) should not call console.print for panels."""
        from pdd.preprocess import preprocess

        with patch("pdd.preprocess.console") as mock_console:
            preprocess("Hello world", quiet=True)
            # Check none of the print calls contain panel output
            for c in mock_console.print.call_args_list:
                args_str = str(c)
                assert "Starting prompt preprocessing" not in args_str
                assert "Preprocessing complete" not in args_str
                assert "Doubling curly brackets" not in args_str

    def test_preprocess_outputs_panels_by_default(self):
        """preprocess() should still show panels when quiet is not set (regression guard)."""
        from pdd.preprocess import preprocess

        with patch("pdd.preprocess.console") as mock_console:
            preprocess("Hello world")
            all_output = " ".join(str(c) for c in mock_console.print.call_args_list)
            assert "Starting prompt preprocessing" in all_output or mock_console.print.called

    def test_preprocess_suppresses_doubling_message_when_quiet(self):
        """preprocess(quiet=True) should not print 'Doubling curly brackets...'."""
        from pdd.preprocess import preprocess

        with patch("pdd.preprocess.console") as mock_console:
            preprocess("Hello {world}", quiet=True)
            for c in mock_console.print.call_args_list:
                assert "Doubling curly brackets" not in str(c)

    def test_preprocess_shows_doubling_message_by_default(self):
        """preprocess() should print 'Doubling curly brackets...' by default."""
        from pdd.preprocess import preprocess

        with patch("pdd.preprocess.console") as mock_console:
            preprocess("Hello {world}")
            all_output = " ".join(str(c) for c in mock_console.print.call_args_list)
            assert "Doubling curly brackets" in all_output


class TestLoadPromptTemplateQuietMode:
    """Tests that load_prompt_template() suppresses messages when quiet=True."""

    def test_load_prompt_template_suppresses_success_message_when_quiet(self, tmp_path):
        """load_prompt_template(quiet=True) should not print success message."""
        from pdd.load_prompt_template import load_prompt_template

        # Create a real prompt file
        prompt_file = tmp_path / "prompts" / "test_quiet.prompt"
        prompt_file.parent.mkdir(parents=True, exist_ok=True)
        prompt_file.write_text("test prompt content")

        with patch("pdd.load_prompt_template.print_formatted") as mock_print, \
             patch("pdd.load_prompt_template.get_default_resolver") as mock_resolver:
            mock_resolver.return_value.resolve_prompt_template.return_value = prompt_file
            result = load_prompt_template("test_quiet", quiet=True)
            assert result == "test prompt content"
            # Should not have printed success message
            for c in mock_print.call_args_list:
                assert "Successfully loaded" not in str(c)

    def test_load_prompt_template_suppresses_not_found_when_quiet(self):
        """load_prompt_template(quiet=True) should not print error for missing files."""
        from pdd.load_prompt_template import load_prompt_template

        with patch("pdd.load_prompt_template.print_formatted") as mock_print, \
             patch("pdd.load_prompt_template.get_default_resolver") as mock_resolver:
            mock_resolver.return_value.resolve_prompt_template.return_value = None
            mock_resolver.return_value.pdd_path_env = None
            mock_resolver.return_value.repo_root = None
            mock_resolver.return_value.cwd = Path("/tmp")
            result = load_prompt_template("nonexistent", quiet=True)
            assert result is None
            mock_print.assert_not_called()

    def test_load_prompt_template_shows_success_by_default(self, tmp_path):
        """load_prompt_template() should print success message by default."""
        from pdd.load_prompt_template import load_prompt_template

        prompt_file = tmp_path / "prompts" / "test_loud.prompt"
        prompt_file.parent.mkdir(parents=True, exist_ok=True)
        prompt_file.write_text("test prompt content")

        with patch("pdd.load_prompt_template.print_formatted") as mock_print, \
             patch("pdd.load_prompt_template.get_default_resolver") as mock_resolver:
            mock_resolver.return_value.resolve_prompt_template.return_value = prompt_file
            load_prompt_template("test_loud")
            all_output = " ".join(str(c) for c in mock_print.call_args_list)
            assert "Successfully loaded" in all_output


class TestLlmInvokeQuietMode:
    """Tests that llm_invoke logger level is raised to CRITICAL when quiet=True."""

    def test_set_quiet_mode_raises_log_level(self):
        """set_quiet_mode() should set both loggers to CRITICAL level."""
        from pdd.llm_invoke import set_quiet_mode

        set_quiet_mode()

        logger = logging.getLogger("pdd.llm_invoke")
        assert logger.level >= logging.WARNING, (
            f"Expected WARNING (30) or higher, got {logger.level}"
        )

        litellm_logger = logging.getLogger("litellm")
        assert litellm_logger.level >= logging.WARNING

    def test_set_quiet_mode_suppresses_info(self):
        """After set_quiet_mode(), INFO messages should not propagate."""
        from pdd.llm_invoke import set_quiet_mode

        set_quiet_mode()
        logger = logging.getLogger("pdd.llm_invoke")

        with patch.object(logger, "handle") as mock_handle:
            logger.info("This should be suppressed")
            mock_handle.assert_not_called()

    def test_cli_quiet_sets_logger_to_critical(self):
        """The CLI --quiet flag should raise llm_invoke logger to CRITICAL."""
        from click.testing import CliRunner
        from pdd.core.cli import cli

        runner = CliRunner(mix_stderr=False)
        # Use 'which' command (not --help, which exits before callback)
        runner.invoke(cli, ["--quiet", "which"])

        logger = logging.getLogger("pdd.llm_invoke")
        assert logger.level >= logging.CRITICAL, (
            f"After --quiet, logger should be CRITICAL, got level {logger.level}"
        )


class TestGenerateCommandQuietMode:
    """Tests that pdd --quiet generate suppresses noisy output."""

    def test_quiet_generate_suppresses_output(self):
        """Running 'pdd --quiet generate' should not produce Rich panels or success messages."""
        from click.testing import CliRunner
        from pdd.core.cli import cli

        runner = CliRunner(mix_stderr=False)

        with patch("pdd.commands.generate.code_generator_main") as mock_gen:
            mock_gen.return_value = ("generated code", False, 0.0, "mock-model")

            result = runner.invoke(cli, ["--quiet", "generate", "prompts/greet_python.prompt"])

            stdout = result.output

            noisy_patterns = [
                "Starting prompt preprocessing",
                "Preprocessing complete",
                "Doubling curly brackets",
                "Successfully loaded prompt",
            ]

            violations = [p for p in noisy_patterns if p in stdout]
            assert not violations, (
                f"--quiet flag did not suppress output. Found: {violations}\n"
                f"Full output:\n{stdout}"
            )
