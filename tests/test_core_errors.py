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


@patch('pdd.core.cli.auto_update')
@patch('pdd.commands.generate.code_generator_main')
def test_cli_handle_error_filenotfound(mock_main, mock_auto_update, runner, create_dummy_files):
    """Test handle_error for FileNotFoundError."""
    files = create_dummy_files("test.prompt")
    
    # Simulate FileNotFoundError
    mock_main.side_effect = FileNotFoundError("Input file missing")
    
    result = runner.invoke(cli.cli, ["generate", str(files["test.prompt"])])

    # Expect exit code 0 because the exception is caught by the command's
    # try-except, calling handle_error (which prints), and returning None.
    assert result.exit_code == 0
    assert result.exception is None # Exception should be handled, not re-raised to runner
    assert "Error during 'generate' command" in result.output
    assert "File not found" in result.output
    # assert "Input file missing" in result.output # Depending on how handle_error formats it
    mock_main.assert_called_once() # Main is called before raising the error
    mock_auto_update.assert_called_once_with() # Auto update runs before command error

@patch('pdd.core.cli.auto_update')
@patch('pdd.commands.generate.code_generator_main')
def test_cli_handle_error_valueerror(mock_main, mock_auto_update, runner, create_dummy_files):
    """Test handle_error for ValueError."""
    files = create_dummy_files("test.prompt")

    # Simulate ValueError
    mock_main.side_effect = ValueError("Invalid prompt content")

    result = runner.invoke(cli.cli, ["generate", str(files["test.prompt"])])

    assert result.exit_code == 0 # Should be 0
    assert result.exception is None # Exception should be handled
    assert "Error during 'generate' command" in result.output
    assert "Input/Output Error" in result.output # ValueError maps to this
    assert "Invalid prompt content" in result.output
    mock_main.assert_called_once()
    mock_auto_update.assert_called_once_with()

@patch('pdd.core.cli.auto_update')
@patch('pdd.commands.generate.code_generator_main')
def test_cli_handle_error_generic(mock_main, mock_auto_update, runner, create_dummy_files):
    """Test handle_error for generic Exception."""
    files = create_dummy_files("test.prompt")

    # Simulate generic Exception
    mock_main.side_effect = Exception("Unexpected LLM issue")

    result = runner.invoke(cli.cli, ["generate", str(files["test.prompt"])])

    assert result.exit_code == 0 # Should be 0
    assert result.exception is None # Exception should be handled
    # assert "Unexpected LLM issue" in str(result.exception) # No exception propagated
    assert "Error during 'generate' command" in result.output
    assert "An unexpected error occurred" in result.output
    assert "Unexpected LLM issue" in result.output
    mock_main.assert_called_once()
    mock_auto_update.assert_called_once_with()

@patch('pdd.core.cli.auto_update')
@patch('pdd.commands.generate.code_generator_main')
def test_cli_handle_error_quiet(mock_main, mock_auto_update, runner, create_dummy_files):
    """Test handle_error respects --quiet."""
    files = create_dummy_files("test.prompt")
    
    # Simulate FileNotFoundError
    mock_main.side_effect = FileNotFoundError("Input file missing")
    
    result = runner.invoke(cli.cli, ["--quiet", "generate", str(files["test.prompt"])])

    # Expect exit code 0 because the exception is handled gracefully.
    assert result.exit_code == 0
    assert result.exception is None # Exception should be handled
    # Error messages should be suppressed by handle_error when quiet=True
    assert "Error during 'generate' command" not in result.output
    assert "File not found" not in result.output
    mock_main.assert_called_once()
    # Auto update still runs but prints nothing when quiet
    mock_auto_update.assert_called_once_with()