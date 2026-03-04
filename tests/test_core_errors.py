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


@patch('pdd.core.cli.auto_update')
@patch.object(_generate_module, 'handle_error')
@patch.object(_generate_module, 'code_generator_main')
def test_cli_handle_error_filenotfound(mock_main, mock_handle_error, mock_auto_update, runner, create_dummy_files):
    """Test handle_error for FileNotFoundError."""
    files = create_dummy_files("test.prompt")

    # Simulate FileNotFoundError
    mock_main.side_effect = FileNotFoundError("Input file missing")

    result = runner.invoke(cli.cli, ["generate", str(files["test.prompt"])])

    # Expect exit code 0 because the exception is caught by the command's
    # try-except, calling handle_error (which prints), and returning None.
    assert result.exit_code == 0
    assert result.exception is None

    # Verify handle_error was called with the right exception and command name
    mock_handle_error.assert_called_once()
    exc_arg, cmd_arg, quiet_arg = mock_handle_error.call_args[0]
    assert isinstance(exc_arg, FileNotFoundError)
    assert str(exc_arg) == "Input file missing"
    assert cmd_arg == "generate"
    assert quiet_arg is False
    mock_main.assert_called_once()

@patch('pdd.core.cli.auto_update')
@patch.object(_generate_module, 'handle_error')
@patch.object(_generate_module, 'code_generator_main')
def test_cli_handle_error_valueerror(mock_main, mock_handle_error, mock_auto_update, runner, create_dummy_files):
    """Test handle_error for ValueError."""
    files = create_dummy_files("test.prompt")

    # Simulate ValueError
    mock_main.side_effect = ValueError("Invalid prompt content")

    result = runner.invoke(cli.cli, ["generate", str(files["test.prompt"])])

    assert result.exit_code == 0
    assert result.exception is None

    mock_handle_error.assert_called_once()
    exc_arg, cmd_arg, quiet_arg = mock_handle_error.call_args[0]
    assert isinstance(exc_arg, ValueError)
    assert str(exc_arg) == "Invalid prompt content"
    assert cmd_arg == "generate"
    assert quiet_arg is False
    mock_main.assert_called_once()

@patch('pdd.core.cli.auto_update')
@patch.object(_generate_module, 'handle_error')
@patch.object(_generate_module, 'code_generator_main')
def test_cli_handle_error_generic(mock_main, mock_handle_error, mock_auto_update, runner, create_dummy_files):
    """Test handle_error for generic Exception."""
    files = create_dummy_files("test.prompt")

    # Simulate generic Exception
    mock_main.side_effect = Exception("Unexpected LLM issue")

    result = runner.invoke(cli.cli, ["generate", str(files["test.prompt"])])

    assert result.exit_code == 0
    assert result.exception is None

    mock_handle_error.assert_called_once()
    exc_arg, cmd_arg, quiet_arg = mock_handle_error.call_args[0]
    assert isinstance(exc_arg, Exception)
    assert str(exc_arg) == "Unexpected LLM issue"
    assert cmd_arg == "generate"
    assert quiet_arg is False
    mock_main.assert_called_once()

@patch('pdd.core.cli.auto_update')
@patch.object(_generate_module, 'handle_error')
@patch.object(_generate_module, 'code_generator_main')
def test_cli_handle_error_quiet(mock_main, mock_handle_error, mock_auto_update, runner, create_dummy_files):
    """Test handle_error respects --quiet flag by passing quiet=True."""
    files = create_dummy_files("test.prompt")

    # Simulate FileNotFoundError
    mock_main.side_effect = FileNotFoundError("Input file missing")

    result = runner.invoke(cli.cli, ["--quiet", "generate", str(files["test.prompt"])])

    assert result.exit_code == 0
    assert result.exception is None

    mock_handle_error.assert_called_once()
    exc_arg, cmd_arg, quiet_arg = mock_handle_error.call_args[0]
    assert isinstance(exc_arg, FileNotFoundError)
    assert cmd_arg == "generate"
    assert quiet_arg is True
    mock_main.assert_called_once()
