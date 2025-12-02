# tests/test_commands_maintenance.py
"""Tests for commands/maintenance."""
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


@patch('pdd.core.cli.auto_update') # Patch auto_update
@patch('pdd.cli.construct_paths') # Now this patch should work
@patch('pdd.commands.maintenance.auto_deps_main')
def test_cli_auto_deps_strips_quotes(mock_main, mock_construct, mock_auto_update, runner, create_dummy_files, tmp_path):
    """Test that auto-deps strips quotes from directory_path."""
    files = create_dummy_files("dep.prompt")
    dep_dir_path = tmp_path / "deps"
    dep_dir_path.mkdir()
    quoted_path = f'"{dep_dir_path}/*"' # Path with quotes

    # construct_paths is NOT called by auto_deps command wrapper, only potentially inside auto_deps_main
    mock_main.return_value = ('modified prompt', 0.1, 'model-deps')

    result = runner.invoke(cli.cli, ["auto-deps", str(files["dep.prompt"]), quoted_path])

    if result.exit_code != 0:
        print(f"Unexpected exit code: {result.exit_code}")
        print(f"Output:\n{result.output}")
        if result.exception:
            print(f"Exception:\n{result.exception}")
            raise result.exception

    assert result.exit_code == 0
    mock_main.assert_called_once()
    # Check that the path passed to auto_deps_main has quotes stripped
    call_args = mock_main.call_args.kwargs
    assert call_args['directory_path'] == f'{dep_dir_path}/*' # No quotes
    mock_construct.assert_not_called() # auto_deps command wrapper does not call construct_paths
    mock_auto_update.assert_called_once_with()


# --- Command Chaining Tests ---

@patch('pdd.core.utils._should_show_onboarding_reminder', return_value=False)
@patch('pdd.core.utils.subprocess.run')
@patch('pdd.cli.install_completion')  # Patch the actual function, not cli_module
@patch('pdd.core.cli.auto_update')
def test_cli_setup_command(mock_auto_update, mock_install, mock_run, _mock_reminder, runner):
    """`pdd setup` should install completions and run the setup utility."""
    mock_run.return_value = subprocess.CompletedProcess(args=[], returncode=0)

    result = runner.invoke(cli.cli, ["setup"])

    assert result.exit_code == 0
    mock_auto_update.assert_called_once_with()
    mock_install.assert_called_once_with(quiet=False)

    mock_run.assert_called_once_with([sys.executable, "-m", "pdd.setup_tool"])
    # assert "Setup completed" in result.output

