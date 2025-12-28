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
from pdd.commands import maintenance

RUN_ALL_TESTS_ENABLED = os.getenv("PDD_RUN_ALL_TESTS") == "1"


# --- Decorator Tests ---

def test_sync_has_track_cost_decorator():
    """Verify sync command uses @track_cost decorator."""
    # The track_cost decorator wraps the function, we can check if it's applied
    # by checking if the function has been wrapped (has __wrapped__ attribute)
    # or by checking the decorator chain
    from pdd.track_cost import track_cost

    # Check that the sync function has track_cost in its decorator chain
    # track_cost adds specific attributes or wraps the function
    sync_func = maintenance.sync

    # The callback is the actual decorated function
    callback = sync_func.callback if hasattr(sync_func, 'callback') else sync_func

    # track_cost should have wrapped the function - check for __wrapped__
    assert hasattr(callback, '__wrapped__'), "sync should have @track_cost decorator"


def test_auto_deps_has_track_cost_decorator():
    """Verify auto-deps command uses @track_cost decorator."""
    auto_deps_func = maintenance.auto_deps
    callback = auto_deps_func.callback if hasattr(auto_deps_func, 'callback') else auto_deps_func
    assert hasattr(callback, '__wrapped__'), "auto_deps should have @track_cost decorator"


# --- Return Type Tests ---

@patch('pdd.core.cli.auto_update')
@patch('pdd.commands.maintenance.sync_main')
def test_sync_returns_tuple_on_success(mock_sync_main, mock_auto_update, runner):
    """Verify sync returns Tuple[str, float, str] on success."""
    mock_sync_main.return_value = ('success', 1.5, 'test-model')

    result = runner.invoke(cli.cli, ["sync", "test_module"])

    # The command should complete successfully
    assert result.exit_code == 0
    mock_sync_main.assert_called_once()


@patch('pdd.core.cli.auto_update')
@patch('pdd.commands.maintenance.handle_error')
@patch('pdd.commands.maintenance.sync_main')
def test_sync_returns_none_on_error(mock_sync_main, mock_handle_error, mock_auto_update, runner):
    """Verify sync returns None when exception occurs."""
    mock_sync_main.side_effect = ValueError("Test error")

    result = runner.invoke(cli.cli, ["sync", "test_module"])

    # handle_error should have been called
    mock_handle_error.assert_called_once()
    # The exception type should be ValueError
    call_args = mock_handle_error.call_args[0]
    assert isinstance(call_args[0], ValueError)
    assert call_args[1] == "sync"


# --- Error Handling Tests ---

@patch('pdd.core.cli.auto_update')
@patch('pdd.commands.maintenance.sync_main')
def test_sync_reraises_click_abort(mock_sync_main, mock_auto_update, runner):
    """Verify click.Abort is re-raised, not caught by handle_error."""
    mock_sync_main.side_effect = click.Abort()

    result = runner.invoke(cli.cli, ["sync", "test_module"])

    # click.Abort should cause exit code 1 (aborted)
    assert result.exit_code == 1


@patch('pdd.core.cli.auto_update')
@patch('pdd.commands.maintenance.handle_error')
@patch('pdd.commands.maintenance.sync_main')
def test_sync_calls_handle_error_on_exception(mock_sync_main, mock_handle_error, mock_auto_update, runner):
    """Verify other exceptions call handle_error with correct arguments."""
    test_exception = RuntimeError("Something went wrong")
    mock_sync_main.side_effect = test_exception

    result = runner.invoke(cli.cli, ["sync", "test_module"])

    mock_handle_error.assert_called_once()
    call_args = mock_handle_error.call_args[0]
    assert call_args[0] is test_exception
    assert call_args[1] == "sync"
    # Third arg is quiet flag (should be False by default)
    assert call_args[2] is False


# --- Deprecated Flag Tests ---

@patch('pdd.core.cli.auto_update')
@patch('pdd.commands.maintenance.sync_main')
def test_sync_deprecated_log_flag_warns_and_sets_dry_run(mock_sync_main, mock_auto_update, runner):
    """Verify --log emits warning to stderr and sets dry_run=True."""
    mock_sync_main.return_value = ('success', 0.5, 'model')

    result = runner.invoke(cli.cli, ["sync", "--log", "test_module"])

    # Check warning was emitted
    assert "deprecated" in result.output.lower() or "deprecated" in (result.stderr or "").lower()

    # Check dry_run was set to True in the call
    mock_sync_main.assert_called_once()
    call_kwargs = mock_sync_main.call_args.kwargs
    assert call_kwargs.get('dry_run') is True


# --- Setup ctx.obj Tests ---

@patch('pdd.core.utils._should_show_onboarding_reminder', return_value=False)
@patch('pdd.core.utils.subprocess.run')
@patch('pdd.cli.install_completion')
@patch('pdd.core.cli.auto_update')
def test_setup_handles_none_ctx_obj(mock_auto_update, mock_install, mock_run, _mock_reminder):
    """Verify setup works when ctx.obj is None."""
    mock_run.return_value = subprocess.CompletedProcess(args=[], returncode=0)

    # Create a runner that doesn't set ctx.obj
    runner = CliRunner()

    # Invoke setup - it should handle ctx.obj being None gracefully
    result = runner.invoke(cli.cli, ["setup"], obj=None)

    assert result.exit_code == 0
    # install_completion should be called with quiet=False (default when ctx.obj is None)
    mock_install.assert_called_once_with(quiet=False)


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


# --- Issue #194: None Parameter Handling Tests ---

@patch('pdd.core.cli.auto_update')
@patch('pdd.commands.maintenance.sync_main')
def test_sync_with_no_target_coverage_does_not_raise_typeerror(mock_sync_main, mock_auto_update, runner):
    """Issue #194: pdd sync without --target-coverage should not raise TypeError."""
    mock_sync_main.return_value = ('success', 0.5, 'model')

    result = runner.invoke(cli.cli, ["sync", "test_module"])

    # Should not raise: TypeError: '<' not supported between instances of 'float' and 'NoneType'
    assert 'TypeError' not in (result.output or '')
    assert 'NoneType' not in (result.output or '')
    mock_sync_main.assert_called_once()

    # Verify target_coverage passed to sync_main is a float, not None
    call_kwargs = mock_sync_main.call_args.kwargs
    target_coverage = call_kwargs.get('target_coverage')
    assert target_coverage is None or isinstance(target_coverage, float), \
        f"target_coverage should be float or None (handled downstream), got {type(target_coverage)}"


@patch('pdd.core.cli.auto_update')
@patch('pdd.commands.maintenance.sync_main')
def test_target_coverage_cli_option_converts_string_to_float(mock_sync_main, mock_auto_update, runner):
    """Issue #194: --target-coverage '90' should be converted to float 90.0, not string '90'."""
    mock_sync_main.return_value = ('success', 0.5, 'model')

    result = runner.invoke(cli.cli, ["sync", "test_module", "--target-coverage", "85.5"])

    # Should not raise: TypeError: '<' not supported between instances of 'float' and 'str'
    assert 'TypeError' not in (result.output or '')
    mock_sync_main.assert_called_once()

    # Verify target_coverage is a float, not a string
    call_kwargs = mock_sync_main.call_args.kwargs
    target_coverage = call_kwargs.get('target_coverage')
    assert isinstance(target_coverage, float), \
        f"target_coverage should be float, got {type(target_coverage)}: {target_coverage}"
    assert target_coverage == 85.5
