# tests/test_commands_maintenance.py
"""Tests for commands/maintenance."""
import json
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
@patch('pdd.commands.maintenance.sync_main')
@patch('pdd.commands.maintenance.run_agentic_sync')
@patch('pdd.commands.maintenance.run_global_sync')
def test_sync_without_basename_dispatches_global_sync(
    mock_global_sync,
    mock_agentic_sync,
    mock_sync_main,
    mock_auto_update,
    runner,
):
    """No-argument `pdd sync` should run global architecture sync."""
    mock_global_sync.return_value = (True, "Global sync dry run: 1 module(s) would sync.", 0.0, "global-sync")

    result = runner.invoke(cli.cli, ["sync", "--dry-run"])

    assert result.exit_code == 0
    mock_global_sync.assert_called_once()
    mock_agentic_sync.assert_not_called()
    mock_sync_main.assert_not_called()
    call_kwargs = mock_global_sync.call_args.kwargs
    assert call_kwargs["dry_run"] is True
    assert call_kwargs["budget"] is not None
    assert call_kwargs["local"] is False


@patch('pdd.core.cli.auto_update')
@patch('pdd.commands.maintenance.run_global_sync')
def test_sync_without_basename_forwards_global_local_flag(
    mock_global_sync,
    mock_auto_update,
    runner,
):
    """Top-level --local must be preserved when global sync dispatches children."""
    mock_global_sync.return_value = (True, "ok", 0.0, "global-sync")

    result = runner.invoke(cli.cli, ["--local", "sync", "--dry-run"])

    assert result.exit_code == 0
    assert mock_global_sync.call_args.kwargs["local"] is True


@patch('pdd.core.cli.auto_update')
@patch('pdd.commands.maintenance.run_global_sync')
def test_sync_without_basename_uses_default_budget_without_pddrc(
    mock_global_sync,
    mock_auto_update,
    runner,
    monkeypatch,
    tmp_path,
):
    """No-argument global sync should use the advertised default budget cap."""
    monkeypatch.chdir(tmp_path)
    mock_global_sync.return_value = (True, "ok", 0.0, "global-sync")

    result = runner.invoke(cli.cli, ["sync", "--dry-run"])

    assert result.exit_code == 0
    assert mock_global_sync.call_args.kwargs["budget"] == pytest.approx(20.0)


@patch('pdd.core.cli.auto_update')
@patch('pdd.commands.maintenance.run_global_sync')
def test_sync_without_basename_uses_pddrc_default_budget(
    mock_global_sync,
    mock_auto_update,
    runner,
    monkeypatch,
    tmp_path,
):
    """No-argument global sync should honor .pddrc default budget."""
    monkeypatch.chdir(tmp_path)
    (tmp_path / ".pddrc").write_text(
        """
version: "1.0"
contexts:
  default:
    defaults:
      budget: 7.5
""",
        encoding="utf-8",
    )
    mock_global_sync.return_value = (True, "ok", 0.0, "global-sync")

    result = runner.invoke(cli.cli, ["sync", "--dry-run"])

    assert result.exit_code == 0
    assert mock_global_sync.call_args.kwargs["budget"] == pytest.approx(7.5)


@patch('pdd.core.cli.auto_update')
@patch('pdd.commands.maintenance.run_global_sync')
def test_sync_without_basename_uses_pddrc_default_target_coverage(
    mock_global_sync,
    mock_auto_update,
    runner,
    monkeypatch,
    tmp_path,
):
    """Global sync analysis should honor .pddrc target coverage like child sync."""
    monkeypatch.chdir(tmp_path)
    (tmp_path / ".pddrc").write_text(
        """
version: "1.0"
contexts:
  default:
    defaults:
      target_coverage: 12.5
""",
        encoding="utf-8",
    )
    mock_global_sync.return_value = (True, "ok", 0.0, "global-sync")

    result = runner.invoke(cli.cli, ["sync", "--dry-run"])

    assert result.exit_code == 0
    assert mock_global_sync.call_args.kwargs["target_coverage"] == pytest.approx(12.5)


@patch('pdd.core.cli.auto_update')
@patch('pdd.commands.maintenance.run_global_sync')
def test_sync_without_basename_target_coverage_cli_overrides_pddrc(
    mock_global_sync,
    mock_auto_update,
    runner,
    monkeypatch,
    tmp_path,
):
    """Explicit --target-coverage should take precedence over .pddrc defaults."""
    monkeypatch.chdir(tmp_path)
    (tmp_path / ".pddrc").write_text(
        """
version: "1.0"
contexts:
  default:
    defaults:
      target_coverage: 12.5
""",
        encoding="utf-8",
    )
    mock_global_sync.return_value = (True, "ok", 0.0, "global-sync")

    result = runner.invoke(cli.cli, ["sync", "--dry-run", "--target-coverage", "80"])

    assert result.exit_code == 0
    assert mock_global_sync.call_args.kwargs["target_coverage"] == pytest.approx(80.0)


@patch('pdd.core.cli.auto_update')
@patch('pdd.commands.maintenance.run_global_sync')
def test_sync_without_basename_exits_on_global_sync_failure(mock_global_sync, mock_auto_update, runner):
    """A failed global sync dispatch should produce a non-zero CLI exit."""
    mock_global_sync.return_value = (False, "No architecture.json found", 0.0, "global-sync")

    result = runner.invoke(cli.cli, ["sync"])

    assert result.exit_code == 1
    mock_global_sync.assert_called_once()


@patch('pdd.core.cli.auto_update')
@patch('pdd.commands.maintenance.run_global_sync')
@patch('pdd.commands.maintenance.run_agentic_sync')
@patch('pdd.commands.maintenance.sync_main')
def test_sync_with_basename_keeps_single_module_dispatch(
    mock_sync_main,
    mock_agentic_sync,
    mock_global_sync,
    mock_auto_update,
    runner,
):
    """A basename argument should still use the original single-module sync path."""
    mock_sync_main.return_value = ('success', 0.5, 'model')

    result = runner.invoke(cli.cli, ["sync", "--dry-run", "--one-session", "test_module"])

    assert result.exit_code == 0
    mock_sync_main.assert_called_once()
    mock_agentic_sync.assert_not_called()
    mock_global_sync.assert_not_called()
    call_kwargs = mock_sync_main.call_args.kwargs
    assert call_kwargs["basename"] == "test_module"
    assert call_kwargs["dry_run"] is True
    assert call_kwargs["one_session"] is True


@patch('pdd.core.cli.auto_update')
@patch('pdd.commands.maintenance.run_global_sync')
@patch('pdd.commands.maintenance.sync_main')
@patch('pdd.commands.maintenance.run_agentic_sync')
def test_sync_with_github_issue_url_keeps_agentic_dispatch(
    mock_agentic_sync,
    mock_sync_main,
    mock_global_sync,
    mock_auto_update,
    runner,
):
    """A GitHub issue URL should still dispatch to agentic issue sync."""
    mock_agentic_sync.return_value = (True, "Sync completed", 0.25, "agentic-sync")
    issue_url = "https://github.com/gltanaka/pdd/issues/636"

    result = runner.invoke(
        cli.cli,
        ["sync", "--budget", "3.5", "--no-one-session", issue_url],
    )

    assert result.exit_code == 0
    mock_agentic_sync.assert_called_once()
    mock_sync_main.assert_not_called()
    mock_global_sync.assert_not_called()
    call_kwargs = mock_agentic_sync.call_args.kwargs
    assert call_kwargs["issue_url"] == issue_url
    assert call_kwargs["budget"] == 3.5
    assert call_kwargs["one_session"] is False
    assert call_kwargs["use_github_state"] is True


@patch('pdd.core.cli.auto_update')
@patch('pdd.commands.maintenance.run_global_sync')
@patch('pdd.commands.maintenance.run_agentic_sync')
@patch('pdd.commands.maintenance.sync_main')
def test_sync_with_architecture_json_keeps_single_module_dispatch(
    mock_sync_main,
    mock_agentic_sync,
    mock_global_sync,
    mock_auto_update,
    runner,
    monkeypatch,
    tmp_path,
):
    """`pdd sync architecture.json` stays on the single-module sync path."""
    monkeypatch.chdir(tmp_path)
    (tmp_path / "architecture.json").write_text("[]", encoding="utf-8")
    mock_sync_main.return_value = ("success", 0.0, "model")

    result = runner.invoke(cli.cli, ["sync", "architecture.json", "--dry-run"])

    assert result.exit_code == 0
    mock_global_sync.assert_not_called()
    mock_sync_main.assert_called_once()
    assert mock_sync_main.call_args.kwargs["basename"] == "architecture.json"
    mock_agentic_sync.assert_not_called()


@patch('pdd.core.cli.auto_update')
@patch('pdd.commands.maintenance.run_global_sync')
@patch('pdd.commands.maintenance.sync_main')
def test_sync_with_architecture_json_subpath_keeps_single_module_dispatch(
    mock_sync_main,
    mock_global_sync,
    mock_auto_update,
    runner,
    monkeypatch,
    tmp_path,
):
    """A path ending in `/architecture.json` stays on single-module sync."""
    monkeypatch.chdir(tmp_path)
    nested = tmp_path / "subdir"
    nested.mkdir()
    (nested / "architecture.json").write_text("[]", encoding="utf-8")
    mock_sync_main.return_value = ("success", 0.0, "model")

    result = runner.invoke(
        cli.cli, ["sync", "subdir/architecture.json", "--dry-run"]
    )

    assert result.exit_code == 0
    mock_global_sync.assert_not_called()
    mock_sync_main.assert_called_once()
    assert mock_sync_main.call_args.kwargs["basename"] == "subdir/architecture.json"


@patch('pdd.core.cli.auto_update')
@patch('pdd.commands.maintenance.run_global_sync')
@patch('pdd.commands.maintenance.sync_main')
def test_sync_with_unrelated_json_falls_through_to_single_module(
    mock_sync_main,
    mock_global_sync,
    mock_auto_update,
    runner,
    monkeypatch,
    tmp_path,
):
    """Non-`architecture.json` `.json` arguments must NOT trigger global sync."""
    monkeypatch.chdir(tmp_path)
    (tmp_path / "config.json").write_text("{}", encoding="utf-8")
    mock_sync_main.return_value = ("success", 0.0, "model")

    result = runner.invoke(cli.cli, ["sync", "config.json"])

    assert result.exit_code == 0
    mock_global_sync.assert_not_called()
    mock_sync_main.assert_called_once()
    assert mock_sync_main.call_args.kwargs["basename"] == "config.json"


@patch('pdd.core.cli.auto_update')
@patch('pdd.commands.maintenance.run_global_sync')
@patch('pdd.commands.maintenance.sync_main')
def test_sync_with_missing_architecture_json_falls_through(
    mock_sync_main,
    mock_global_sync,
    mock_auto_update,
    runner,
    monkeypatch,
    tmp_path,
):
    """`pdd sync architecture.json` remains a normal basename when missing."""
    monkeypatch.chdir(tmp_path)  # no architecture.json on disk
    mock_sync_main.return_value = ("success", 0.0, "model")

    result = runner.invoke(cli.cli, ["sync", "architecture.json"])

    assert result.exit_code == 0
    mock_global_sync.assert_not_called()
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


@patch('pdd.core.cli.auto_update')
@patch('pdd.commands.maintenance.sync_prompts_to_architecture')
def test_sync_architecture_reports_summary_and_success(mock_sync_prompts, mock_auto_update, runner):
    """Explicit architecture sync command should call the shared helper and print a summary."""
    mock_sync_prompts.return_value = {
        "success": True,
        "updated_count": 2,
        "skipped_count": 1,
        "results": [
            {"filename": "core_python.prompt", "success": True, "updated": True, "changes": {"reason": {"old": "old", "new": "new"}}, "error": None},
            {"filename": "dep_python.prompt", "success": True, "updated": False, "changes": {}, "error": None},
        ],
        "validation": {"valid": True, "errors": [], "warnings": []},
        "errors": [],
    }

    result = runner.invoke(cli.cli, ["sync-architecture"])

    assert result.exit_code == 0
    mock_sync_prompts.assert_called_once_with(filenames=None, dry_run=False)
    assert "Updated 2 module(s); skipped 1." in result.output
    assert "core_python.prompt" in result.output
    assert "Unexpected result format" not in result.output


@patch('pdd.core.cli.auto_update')
@patch('pdd.commands.maintenance.sync_prompts_to_architecture')
def test_sync_architecture_passes_filenames_and_dry_run(mock_sync_prompts, mock_auto_update, runner):
    """Specific prompt filenames and --dry-run should flow into the shared helper."""
    mock_sync_prompts.return_value = {
        "success": True,
        "updated_count": 1,
        "skipped_count": 0,
        "results": [
            {"filename": "core_python.prompt", "success": True, "updated": True, "changes": {"reason": {"old": "old", "new": "new"}}, "error": None},
        ],
        "validation": {"valid": True, "errors": [], "warnings": []},
        "errors": [],
    }

    result = runner.invoke(
        cli.cli,
        ["sync-architecture", "--dry-run", "prompts/core_python.prompt"],
    )

    assert result.exit_code == 0
    mock_sync_prompts.assert_called_once_with(
        filenames=["prompts/core_python.prompt"],
        dry_run=True,
    )
    assert "Dry run: would update 1 module(s); skipped 0." in result.output


@patch('pdd.core.cli.auto_update')
@patch('pdd.commands.maintenance.sync_prompts_to_architecture')
def test_sync_architecture_exits_nonzero_on_validation_failure(mock_sync_prompts, mock_auto_update, runner):
    """Validation failures should surface clearly and fail the command."""
    mock_sync_prompts.return_value = {
        "success": False,
        "updated_count": 1,
        "skipped_count": 0,
        "results": [
            {"filename": "core_python.prompt", "success": True, "updated": True, "changes": {"reason": {"old": "old", "new": "new"}}, "error": None},
        ],
        "validation": {
            "valid": False,
            "errors": [
                {
                    "type": "missing_dependency",
                    "message": "Module 'core_python.prompt' depends on non-existent module 'dep_python.prompt'",
                    "modules": ["core_python.prompt", "dep_python.prompt"],
                }
            ],
            "warnings": [],
        },
        "errors": [],
    }

    result = runner.invoke(cli.cli, ["sync-architecture"])

    assert result.exit_code == 1
    assert "Validation errors:" in result.output
    assert "depends on non-existent module" in result.output


@patch('pdd.core.cli.auto_update')
@patch('pdd.commands.maintenance.handle_error')
@patch('pdd.commands.maintenance.sync_prompts_to_architecture')
def test_sync_architecture_calls_handle_error_on_exception(mock_sync_prompts, mock_handle_error, mock_auto_update, runner):
    """Unexpected sync failures should still go through shared CLI error handling."""
    mock_sync_prompts.side_effect = RuntimeError("boom")

    result = runner.invoke(cli.cli, ["sync-architecture"])

    mock_handle_error.assert_called_once()
    call_args = mock_handle_error.call_args[0]
    assert isinstance(call_args[0], RuntimeError)
    assert call_args[1] == "sync-architecture"


@patch('pdd.core.cli.auto_update')
def test_sync_architecture_uses_nearest_cwd_project(mock_auto_update, runner, tmp_path, monkeypatch):
    """CLI should target the nearest ancestor project, not always the repo root."""
    repo_root = tmp_path / "repo"
    repo_root.mkdir()
    (repo_root / ".git").mkdir()

    root_prompts = repo_root / "prompts"
    root_prompts.mkdir()
    (root_prompts / "root_python.prompt").write_text(
        "<pdd-reason>Updated root reason</pdd-reason>",
        encoding="utf-8",
    )
    (repo_root / "architecture.json").write_text(
        '[{"filename":"root_python.prompt","filepath":"root.py","description":"Root module","reason":"Original root reason","dependencies":[],"priority":1}]',
        encoding="utf-8",
    )

    nested_root = repo_root / "apps" / "nested"
    nested_root.mkdir(parents=True)
    nested_prompts = nested_root / "prompts"
    nested_prompts.mkdir()
    (nested_prompts / "nested_python.prompt").write_text(
        "<pdd-reason>Updated nested reason</pdd-reason>",
        encoding="utf-8",
    )
    (nested_root / "architecture.json").write_text(
        '[{"filename":"nested_python.prompt","filepath":"nested.py","description":"Nested module","reason":"Original nested reason","dependencies":[],"priority":1}]',
        encoding="utf-8",
    )

    monkeypatch.chdir(nested_root)

    result = runner.invoke(cli.cli, ["sync-architecture"])

    assert result.exit_code == 0
    assert "Updated 1 module(s); skipped 0." in result.output
    assert json.loads((repo_root / "architecture.json").read_text(encoding="utf-8"))[0]["reason"] == "Original root reason"
    assert json.loads((nested_root / "architecture.json").read_text(encoding="utf-8"))[0]["reason"] == "Updated nested reason"
