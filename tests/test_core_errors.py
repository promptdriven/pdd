# tests/test_core_errors.py
"""Tests for core/errors."""
import os
import sys
import subprocess
from pathlib import Path
from unittest.mock import patch, ANY, MagicMock, call

import pytest
from click.testing import CliRunner
import click

from pdd import cli, __version__, DEFAULT_STRENGTH, DEFAULT_TIME

RUN_ALL_TESTS_ENABLED = os.getenv("PDD_RUN_ALL_TESTS") == "1"

# Get the actual generate module (not the Click command).
# pdd.commands.__init__.py shadows the 'generate' submodule with the Click
# command object via `from .generate import generate`, so
# @patch('pdd.commands.generate.X') targets the wrong object once __init__.py
# has been imported by another test. Using sys.modules bypasses this.
_generate_module = sys.modules.get('pdd.commands.generate')
if _generate_module is None:
    import importlib
    _generate_module = importlib.import_module('pdd.commands.generate')


def _console_output(mock_console):
    """Join all positional args from mock_console.print() calls into one string."""
    parts = []
    for c in mock_console.print.call_args_list:
        for arg in c.args:
            parts.append(str(arg))
    return " ".join(parts)


@patch('pdd.core.errors.console', new_callable=MagicMock)
@patch('pdd.core.cli.auto_update')
@patch.object(_generate_module, 'code_generator_main')
def test_cli_handle_error_filenotfound(mock_main, mock_auto_update, mock_console, create_dummy_files):
    """Test handle_error for FileNotFoundError."""
    files = create_dummy_files("test.prompt")

    # Simulate FileNotFoundError
    mock_main.side_effect = FileNotFoundError("Input file missing")

    result = CliRunner().invoke(cli.cli, ["generate", str(files["test.prompt"])])

    # Expect exit code 0 because the exception is caught by the command's
    # try-except, calling handle_error (which prints), and returning None.
    assert result.exit_code == 0
    assert result.exception is None  # Exception should be handled, not re-raised to runner
    output = _console_output(mock_console)
    assert "Error during 'generate' command" in output
    assert "File not found" in output
    mock_main.assert_called_once()  # Main is called before raising the error
    mock_auto_update.assert_called_once_with()  # Auto update runs before command error

@patch('pdd.core.errors.console', new_callable=MagicMock)
@patch('pdd.core.cli.auto_update')
@patch.object(_generate_module, 'code_generator_main')
def test_cli_handle_error_valueerror(mock_main, mock_auto_update, mock_console, create_dummy_files):
    """Test handle_error for ValueError."""
    files = create_dummy_files("test.prompt")

    # Simulate ValueError
    mock_main.side_effect = ValueError("Invalid prompt content")

    result = CliRunner().invoke(cli.cli, ["generate", str(files["test.prompt"])])

    assert result.exit_code == 0  # Should be 0
    assert result.exception is None  # Exception should be handled
    output = _console_output(mock_console)
    assert "Error during 'generate' command" in output
    assert "Input/Output Error" in output  # ValueError maps to this
    assert "Invalid prompt content" in output
    mock_main.assert_called_once()

@patch('pdd.core.errors.console', new_callable=MagicMock)
@patch('pdd.core.cli.auto_update')
@patch.object(_generate_module, 'code_generator_main')
def test_cli_handle_error_generic(mock_main, mock_auto_update, mock_console, create_dummy_files):
    """Test handle_error for generic Exception."""
    files = create_dummy_files("test.prompt")

    # Simulate generic Exception
    mock_main.side_effect = Exception("Unexpected LLM issue")

    result = CliRunner().invoke(cli.cli, ["generate", str(files["test.prompt"])])

    assert result.exit_code == 0  # Should be 0
    assert result.exception is None  # Exception should be handled
    output = _console_output(mock_console)
    assert "Error during 'generate' command" in output
    assert "An unexpected error occurred" in output
    assert "Unexpected LLM issue" in output
    mock_main.assert_called_once()

@patch('pdd.core.errors.console', new_callable=MagicMock)
@patch('pdd.core.cli.auto_update')
@patch.object(_generate_module, 'code_generator_main')
def test_cli_handle_error_quiet(mock_main, mock_auto_update, mock_console, create_dummy_files):
    """Test handle_error respects --quiet."""
    files = create_dummy_files("test.prompt")

    # Simulate FileNotFoundError
    mock_main.side_effect = FileNotFoundError("Input file missing")

    result = CliRunner().invoke(cli.cli, ["--quiet", "generate", str(files["test.prompt"])])

    assert result.exit_code == 0
    assert result.exception is None  # Exception should be handled
    # Error messages should be suppressed by handle_error when quiet=True
    output = _console_output(mock_console)
    assert "Error during 'generate' command" not in output
    assert "File not found" not in output
    mock_main.assert_called_once()
    # Auto update still runs but prints nothing when quiet
    mock_auto_update.assert_called_once_with()


@patch('pdd.core.errors.console', new_callable=MagicMock)
def test_handle_error_keyboard_interrupt_messages(mock_console):
    """KeyboardInterrupt should produce clear Ctrl+C messaging."""
    # Import here to ensure patched console is used
    from pdd.core.errors import handle_error

    exc = KeyboardInterrupt()
    # Simulate a bug command, not quiet
    handle_error(exc, "bug", quiet=False)

    output = _console_output(mock_console)
    # Top-level line should clearly mention Ctrl+C and the command
    assert "You pressed Ctrl+C in your terminal." in output
    assert "Interrupted during 'bug' command" in output
    # Hint about how to proceed
    assert "Re-run the same command to start fresh." in output


@patch('pdd.core.errors.console', new_callable=MagicMock)
@patch('pdd.core.cli.auto_update')
@patch.object(_generate_module, 'code_generator_main')
def test_keyboard_interrupt_reports_correct_command_name(
    mock_main, mock_auto_update, mock_console, create_dummy_files
):
    """KeyboardInterrupt during a subcommand should report the subcommand name, not 'unknown'."""
    files = create_dummy_files("test.prompt")

    mock_main.side_effect = KeyboardInterrupt()

    result = CliRunner().invoke(cli.cli, ["generate", str(files["test.prompt"])])

    output = _console_output(mock_console)
    # Must say "generate", NOT "unknown"
    assert "Interrupted during 'generate' command" in output, (
        f"Expected 'generate' in interrupt message but got: {output}"
    )
    assert "'unknown'" not in output, (
        f"Command name should not be 'unknown': {output}"
    )


def test_record_core_dump_error_adds_structured_entry():
    from pdd.core.errors import clear_core_dump_errors, get_core_dump_errors, record_core_dump_error

    clear_core_dump_errors()
    record_core_dump_error(
        command="sync",
        type="LogicalFailure",
        message="Budget exhausted",
        details={"remaining_budget": 0.0},
    )

    errs = get_core_dump_errors()
    assert len(errs) == 1
    assert errs[0]["command"] == "sync"
    assert errs[0]["type"] == "LogicalFailure"
    assert errs[0]["message"] == "Budget exhausted"
    assert errs[0]["details"]["remaining_budget"] == 0.0
