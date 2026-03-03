# tests/test_core_errors.py
"""Tests for core/errors."""
import os
import sys
import subprocess
from pathlib import Path
from unittest.mock import patch, ANY, MagicMock

import pytest
from click.testing import CliRunner
import click

from pdd import cli, __version__, DEFAULT_STRENGTH, DEFAULT_TIME

RUN_ALL_TESTS_ENABLED = os.getenv("PDD_RUN_ALL_TESTS") == "1"


def _get_full_output(result):
    """Get combined stdout + stderr from a Click test result.

    handle_error uses Rich Console() which writes to stderr by default.
    In non-TTY environments (like CI/cloud), Rich properly separates stderr,
    so we must check both streams.
    """
    full = result.output or ""
    if hasattr(result, "stderr") and result.stderr:
        full += result.stderr
    return full


@patch('pdd.core.cli.auto_update')
@patch('pdd.commands.generate.code_generator_main')
def test_cli_handle_error_filenotfound(mock_main, mock_auto_update, create_dummy_files):
    """Test handle_error for FileNotFoundError."""
    files = create_dummy_files("test.prompt")

    # Simulate FileNotFoundError
    mock_main.side_effect = FileNotFoundError("Input file missing")

    # mix_stderr=False so we can capture stderr separately
    result = CliRunner(mix_stderr=False).invoke(cli.cli, ["generate", str(files["test.prompt"])])

    # Expect exit code 0 because the exception is caught by the command's
    # try-except, calling handle_error (which prints), and returning None.
    assert result.exit_code == 0
    assert result.exception is None # Exception should be handled, not re-raised to runner
    full = _get_full_output(result)
    assert "Error during 'generate' command" in full
    assert "File not found" in full
    mock_main.assert_called_once() # Main is called before raising the error
    mock_auto_update.assert_called_once_with() # Auto update runs before command error

@patch('pdd.core.cli.auto_update')
@patch('pdd.commands.generate.code_generator_main')
def test_cli_handle_error_valueerror(mock_main, mock_auto_update, create_dummy_files):
    """Test handle_error for ValueError."""
    files = create_dummy_files("test.prompt")

    # Simulate ValueError
    mock_main.side_effect = ValueError("Invalid prompt content")

    result = CliRunner(mix_stderr=False).invoke(cli.cli, ["generate", str(files["test.prompt"])])

    assert result.exit_code == 0 # Should be 0
    assert result.exception is None # Exception should be handled
    full = _get_full_output(result)
    assert "Error during 'generate' command" in full
    assert "Input/Output Error" in full # ValueError maps to this
    assert "Invalid prompt content" in full
    mock_main.assert_called_once()
    mock_auto_update.assert_called_once_with()

@patch('pdd.core.cli.auto_update')
@patch('pdd.commands.generate.code_generator_main')
def test_cli_handle_error_generic(mock_main, mock_auto_update, create_dummy_files):
    """Test handle_error for generic Exception."""
    files = create_dummy_files("test.prompt")

    # Simulate generic Exception
    mock_main.side_effect = Exception("Unexpected LLM issue")

    result = CliRunner(mix_stderr=False).invoke(cli.cli, ["generate", str(files["test.prompt"])])

    assert result.exit_code == 0 # Should be 0
    assert result.exception is None # Exception should be handled
    full = _get_full_output(result)
    assert "Error during 'generate' command" in full
    assert "An unexpected error occurred" in full
    assert "Unexpected LLM issue" in full
    mock_main.assert_called_once()
    mock_auto_update.assert_called_once_with()

@patch('pdd.core.cli.auto_update')
@patch('pdd.commands.generate.code_generator_main')
def test_cli_handle_error_quiet(mock_main, mock_auto_update, create_dummy_files):
    """Test handle_error respects --quiet."""
    files = create_dummy_files("test.prompt")

    # Simulate FileNotFoundError
    mock_main.side_effect = FileNotFoundError("Input file missing")

    result = CliRunner(mix_stderr=False).invoke(cli.cli, ["--quiet", "generate", str(files["test.prompt"])])

    # Expect exit code 0 because the exception is handled gracefully.
    assert result.exit_code == 0
    assert result.exception is None # Exception should be handled
    # Error messages should be suppressed by handle_error when quiet=True
    full = _get_full_output(result)
    assert "Error during 'generate' command" not in full
    assert "File not found" not in full
    mock_main.assert_called_once()
    # Auto update still runs but prints nothing when quiet
    mock_auto_update.assert_called_once_with()