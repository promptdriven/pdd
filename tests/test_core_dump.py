# tests/test_core_dump.py
"""Tests for core/dump."""
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
def test_cli_core_dump_default_flag_false(mock_main, mock_auto_update, runner, create_dummy_files):
    """By default, core_dump flag in context should be False (or missing)."""
    files = create_dummy_files("test_core_default.prompt")
    mock_main.return_value = ('code', False, 0.0, 'model')

    result = runner.invoke(cli.cli, ["generate", str(files["test_core_default.prompt"])])

    if result.exit_code != 0:
        print(f"Unexpected exit code: {result.exit_code}")
        print(result.output)
        if result.exception:
            raise result.exception

    mock_main.assert_called_once()
    ctx = mock_main.call_args.kwargs.get("ctx")
    assert ctx is not None
    # If implementation does not set it explicitly, this assertion can be relaxed
    assert ctx.obj.get("core_dump", False) is False
    mock_auto_update.assert_called_once_with()

@patch('pdd.core.cli.auto_update')
@patch('pdd.commands.generate.code_generator_main')
def test_cli_core_dump_flag_sets_ctx_true(mock_main, mock_auto_update, runner, create_dummy_files):
    """`--core-dump` should set ctx.obj['core_dump'] to True."""
    files = create_dummy_files("test_core_enabled.prompt")
    mock_main.return_value = ('code', False, 0.0, 'model')

    result = runner.invoke(
        cli.cli,
        [
            "--core-dump",
            "generate",
            str(files["test_core_enabled.prompt"]),
        ],
    )

    if result.exit_code != 0:
        print(f"Unexpected exit code: {result.exit_code}")
        print(result.output)
        if result.exception:
            raise result.exception

    mock_main.assert_called_once()
    ctx = mock_main.call_args.kwargs.get("ctx")
    assert ctx is not None
    assert ctx.obj.get("core_dump") is True
    mock_auto_update.assert_called_once_with()

@patch('pdd.core.cli.auto_update')
@patch('pdd.commands.generate.code_generator_main', side_effect=Exception("Core dump test error"))
def test_cli_core_dump_does_not_propagate_exception(mock_main, mock_auto_update, runner, create_dummy_files):
    """
    When --core-dump is enabled and the command raises,
    the CLI should still handle the error gracefully (exit_code == 0),
    allowing core-dump machinery to run without crashing the CLI.
    """
    files = create_dummy_files("test_core_error.prompt")

    result = runner.invoke(
        cli.cli,
        [
            "--core-dump",
            "generate",
            str(files["test_core_error.prompt"]),
        ],
    )

    # Error should be handled by the CLI's error handler (no traceback propagated)
    assert result.exit_code == 0
    assert result.exception is None
    # We don't assert on the exact output text to avoid coupling to wording.
    mock_main.assert_called_once()
    mock_auto_update.assert_called_once_with()

