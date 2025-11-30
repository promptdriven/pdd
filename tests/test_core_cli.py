# tests/test_core_cli.py
"""Tests for core/cli."""
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

# Helper to capture summary output by invoking process_commands directly
def _capture_summary(invoked_subcommands, results):
    """
    Helper to test process_commands callback logic without running full CLI.
    Simulates the context and captures console output.
    """
    ctx = click.Context(cli.cli)
    ctx.obj = {'quiet': False, 'invoked_subcommands': invoked_subcommands}
    # Ensure the summary callback sees the actual command names
    ctx.invoked_subcommands = invoked_subcommands
    with patch.object(cli.console, 'print') as mock_print:
        with ctx:
            cli.process_commands(results=results)
    return ["".join(str(arg) for arg in call.args) for call in mock_print.call_args_list]

def test_cli_list_contexts(runner):
    """Test `pdd --list-contexts`."""
    result = runner.invoke(cli.cli, ["--list-contexts"])
    assert result.exit_code == 0
    assert "default" in result.output

@patch('pdd.core.cli.auto_update')
def test_cli_list_contexts_early_exit_no_auto_update(mock_auto_update, runner, tmp_path, monkeypatch):
    """Ensure --list-contexts exits early and does not call auto_update."""
    # Create a .pddrc with multiple contexts
    pddrc = tmp_path / ".pddrc"
    pddrc.write_text(
        'contexts:\n'
        '  default:\n'
        '    paths: ["**"]\n'
        '  alt:\n'
        '    paths: ["src/**"]\n'
    )
    monkeypatch.chdir(tmp_path)

    result = runner.invoke(cli.cli, ["--list-contexts"])
    assert result.exit_code == 0
    # Should list both contexts, one per line
    assert "default" in result.output
    assert "alt" in result.output
    # Must not perform auto-update when listing
    mock_auto_update.assert_not_called()

def test_cli_list_contexts_malformed_pddrc_shows_usage_error(runner, tmp_path, monkeypatch):
    """Malformed .pddrc should cause --list-contexts to fail with usage error."""
    (tmp_path / ".pddrc").write_text('version: "1.0"\n')  # Missing contexts
    monkeypatch.chdir(tmp_path)
    result = runner.invoke(cli.cli, ["--list-contexts"])
    assert result.exit_code == 2
    assert "Failed to load .pddrc" in result.output

@patch('pdd.core.cli.auto_update')
@patch('pdd.commands.generate.code_generator_main')
def test_cli_context_known_passed_to_subcommand(mock_main, mock_auto_update, runner, tmp_path, monkeypatch):
    """--context NAME sets ctx.obj['context'] and threads into the subcommand."""
    # Setup .pddrc with an alt context
    (tmp_path / "prompts").mkdir()
    (tmp_path / ".pddrc").write_text(
        'contexts:\n'
        '  default:\n'
        '    paths: ["**"]\n'
        '  alt:\n'
        '    paths: ["**"]\n'
    )
    prompt = tmp_path / "prompts" / "demo_python.prompt"
    prompt.write_text("dummy")
    monkeypatch.chdir(tmp_path)

    mock_main.return_value = ('code', False, 0.0, 'model')

    result = runner.invoke(cli.cli, ["--context", "alt", "generate", str(prompt)])
    assert result.exit_code == 0
    # Verify subcommand was called and ctx carries the override
    mock_main.assert_called_once()
    passed_ctx = mock_main.call_args.kwargs.get('ctx')
    assert passed_ctx is not None
    assert passed_ctx.obj.get('context') == 'alt'

@patch('pdd.core.cli.auto_update')
@patch('pdd.commands.generate.code_generator_main')
def test_cli_context_unknown_raises_usage_error(mock_main, mock_auto_update, runner, tmp_path, monkeypatch):
    """Unknown --context fails early with UsageError (exit code 2) and no subcommand runs."""
    # .pddrc only has default
    (tmp_path / ".pddrc").write_text('contexts:\n  default:\n    paths: ["**"]\n')
    # Create a dummy prompt path (should not be used due to early error)
    (tmp_path / "prompts").mkdir()
    prompt = tmp_path / "prompts" / "x_python.prompt"
    prompt.write_text("dummy")
    monkeypatch.chdir(tmp_path)

    result = runner.invoke(cli.cli, ["--context", "missing", "generate", str(prompt)])
    assert result.exit_code == 2  # click.UsageError
    assert "Unknown context 'missing'" in result.output
    mock_main.assert_not_called()
    mock_auto_update.assert_not_called()

@patch('pdd.core.cli.auto_update')
@patch('pdd.commands.generate.code_generator_main')
def test_cli_context_unknown_without_pddrc(mock_main, mock_auto_update, runner, tmp_path, monkeypatch):
    """Unknown context should still fail even when no .pddrc exists (only 'default' is available)."""
    (tmp_path / "prompts").mkdir()
    prompt = tmp_path / "prompts" / "x_python.prompt"
    prompt.write_text("dummy")
    monkeypatch.chdir(tmp_path)

    result = runner.invoke(cli.cli, ["--context", "alt", "generate", str(prompt)])
    assert result.exit_code == 2
    assert "Unknown context 'alt'" in result.output
    mock_main.assert_not_called()
    mock_auto_update.assert_not_called()

def test_cli_version(runner):
    """Test `pdd --version`."""
    result = runner.invoke(cli.cli, ["--version"])
    assert result.exit_code == 0
    assert __version__ in result.output

def test_cli_help(runner):
    """Test `pdd --help`."""
    result = runner.invoke(cli.cli, ["--help"])
    assert result.exit_code == 0
    # Use looser check for Usage line as it might vary slightly
    assert "Usage: cli [OPTIONS] COMMAND" in result.output
    # Check if a few commands are listed
    assert "generate" in result.output
    assert "fix" in result.output
    assert "install_completion" in result.output

def test_cli_help_shows_core_dump_flag(runner):
    """Global --core-dump option should be visible in top-level help."""
    result = runner.invoke(cli.cli, ["--help"])
    assert result.exit_code == 0
    assert "--core-dump" in result.output

def test_cli_command_help(runner):
    """Test `pdd [COMMAND] --help`."""
    result = runner.invoke(cli.cli, ["generate", "--help"])
    assert result.exit_code == 0
    assert "Usage: cli generate [OPTIONS] PROMPT_FILE" in result.output
    assert "--output" in result.output

@patch('pdd.core.cli.auto_update') # Patch auto_update here as well
@patch('pdd.commands.generate.code_generator_main')
@patch('pdd.cli.construct_paths') # Now this patch should work
def test_cli_global_options_defaults(mock_construct, mock_main, mock_auto_update, runner, create_dummy_files):
    """Test default global options are passed in context."""
    files = create_dummy_files("test.prompt")
    # mock_construct is not called directly by the CLI command wrapper, only potentially by the main func
    # mock_construct.return_value = ({}, {'output': 'out.py'}, 'python') # Not needed if main is mocked
    mock_main.return_value = ('code', False, 0.0, 'model') # Corrected: 4-tuple

    result = runner.invoke(cli.cli, ["generate", str(files["test.prompt"])])

    # Check for underlying error if exit code is not 0
    if result.exit_code != 0:
        print(f"Unexpected exit code: {result.exit_code}")
        print(f"Output:\n{result.output}")
        if result.exception:
            print(f"Exception:\n{result.exception}")
            raise result.exception # Re-raise the captured exception

    assert result.exit_code == 0
    mock_main.assert_called_once()
    ctx = mock_main.call_args.kwargs.get('ctx')
    assert ctx is not None
    assert ctx.obj['force'] is False
    assert ctx.obj['strength'] == DEFAULT_STRENGTH
    assert ctx.obj['temperature'] == 0.0
    assert ctx.obj['verbose'] is False
    assert ctx.obj['quiet'] is False
    assert ctx.obj['output_cost'] is None
    assert ctx.obj['local'] is False
    assert ctx.obj['review_examples'] is False # Check default for review_examples
    assert ctx.obj['time'] == DEFAULT_TIME # Check default for time
    mock_auto_update.assert_called_once_with() # Check auto_update was called

@patch('pdd.core.cli.auto_update') # Patch auto_update here as well
@patch('pdd.commands.generate.code_generator_main')
@patch('pdd.cli.construct_paths') # Now this patch should work
def test_cli_global_options_explicit(mock_construct, mock_main, mock_auto_update, runner, create_dummy_files):
    """Test explicit global options override defaults."""
    files = create_dummy_files("test.prompt")
    # mock_construct.return_value = ({}, {'output': 'out.py'}, 'python') # Not needed if main is mocked
    mock_main.return_value = ('code', False, 0.0, 'model') # Corrected: 4-tuple

    result = runner.invoke(cli.cli, [
        "--force",
        "--strength", f"{DEFAULT_STRENGTH}",
        "--temperature", "0.5",
        "--verbose",
        "--output-cost", "./output/costs.csv",
        "--local",
        "--review-examples",
        "--time", "0.7", # Added --time to explicit options test
        "generate", str(files["test.prompt"])
    ])

    if result.exit_code != 0:
        print(f"Unexpected exit code: {result.exit_code}")
        print(f"Output:\n{result.output}")
        if result.exception:
            print(f"Exception:\n{result.exception}")
            raise result.exception

    assert result.exit_code == 0
    mock_main.assert_called_once()
    ctx = mock_main.call_args.kwargs.get('ctx')
    assert ctx is not None
    assert ctx.obj['force'] is True
    assert ctx.obj['strength'] == DEFAULT_STRENGTH
    assert ctx.obj['temperature'] == 0.5
    assert ctx.obj['verbose'] is True # Not overridden by quiet
    assert ctx.obj['quiet'] is False
    assert ctx.obj['output_cost'] == "./output/costs.csv"
    assert ctx.obj['local'] is True
    assert ctx.obj['review_examples'] is True # Check review_examples override
    assert ctx.obj['time'] == 0.7 # Check time override
    mock_auto_update.assert_called_once_with() # Check auto_update was called

@patch('pdd.core.cli.auto_update') # Patch auto_update here as well
@patch('pdd.commands.generate.code_generator_main')
@patch('pdd.cli.construct_paths') # Now this patch should work
def test_cli_global_options_quiet_overrides_verbose(mock_construct, mock_main, mock_auto_update, runner, create_dummy_files):
    """Test --quiet overrides --verbose."""
    files = create_dummy_files("test.prompt")
    # mock_construct.return_value = ({}, {'output': 'out.py'}, 'python') # Not needed if main is mocked
    mock_main.return_value = ('code', False, 0.0, 'model') # Corrected: 4-tuple

    result = runner.invoke(cli.cli, [
        "--verbose",
        "--quiet",
        "generate", str(files["test.prompt"])
    ])

    if result.exit_code != 0:
        print(f"Unexpected exit code: {result.exit_code}")
        print(f"Output:\n{result.output}")
        if result.exception:
            print(f"Exception:\n{result.exception}")
            raise result.exception

    assert result.exit_code == 0
    mock_main.assert_called_once()
    ctx = mock_main.call_args.kwargs.get('ctx')
    assert ctx is not None
    assert ctx.obj['verbose'] is False # Should be forced to False
    assert ctx.obj['quiet'] is True
    # Auto update is called, but doesn't print when quiet
    # The check is whether auto_update *function* was called, not its output
    mock_auto_update.assert_called_once_with() # Check auto_update was called

# --- Auto Update Tests ---

@patch('pdd.core.cli.auto_update')
@patch('pdd.commands.generate.code_generator_main') # Need to mock a command to trigger cli execution
@patch('pdd.cli.construct_paths') # Now this patch should work
def test_cli_auto_update_called_by_default(mock_construct, mock_main, mock_auto_update, runner, create_dummy_files):
    """Test auto_update is called by default."""
    files = create_dummy_files("test.prompt")
    # mock_construct.return_value = ({}, {'output': 'out.py'}, 'python') # Not needed if main is mocked
    mock_main.return_value = ('code', False, 0.0, 'model') # Corrected: 4-tuple

    result = runner.invoke(cli.cli, ["generate", str(files["test.prompt"])] )

    if result.exit_code != 0:
        print(f"Unexpected exit code: {result.exit_code}")
        print(f"Output:\n{result.output}")
        if result.exception:
            print(f"Exception:\n{result.exception}")
            raise result.exception

    # Check auto_update was called (no args needed as quiet default is False)
    mock_auto_update.assert_called_once_with()
    mock_main.assert_called_once() # Ensure command still ran

@patch.dict(os.environ, {"PDD_AUTO_UPDATE": "false"}, clear=True)
@patch('pdd.core.cli.auto_update')
@patch('pdd.commands.generate.code_generator_main')
@patch('pdd.cli.construct_paths') # Now this patch should work
def test_cli_auto_update_not_called_when_disabled(mock_construct, mock_main, mock_auto_update, runner, create_dummy_files):
    """Test auto_update is not called when PDD_AUTO_UPDATE=false."""
    files = create_dummy_files("test.prompt")
    # mock_construct.return_value = ({}, {'output': 'out.py'}, 'python') # Not needed if main is mocked
    mock_main.return_value = ('code', False, 0.0, 'model') # Corrected: 4-tuple

    result = runner.invoke(cli.cli, ["generate", str(files["test.prompt"])] )

    if result.exit_code != 0:
        print(f"Unexpected exit code: {result.exit_code}")
        print(f"Output:\n{result.output}")
        if result.exception:
            print(f"Exception:\n{result.exception}")
            raise result.exception

    mock_auto_update.assert_not_called()
    mock_main.assert_called_once() # Ensure command still ran

@patch('pdd.core.cli.auto_update', side_effect=Exception("Network error"))
@patch('pdd.commands.generate.code_generator_main')
@patch('pdd.cli.construct_paths') # Now this patch should work
def test_cli_auto_update_handles_exception(mock_construct, mock_main, mock_auto_update, runner, create_dummy_files):
    """Test auto_update exceptions are handled gracefully."""
    files = create_dummy_files("test.prompt")
    # mock_construct.return_value = ({}, {'output': 'out.py'}, 'python') # Not needed if main is mocked
    mock_main.return_value = ('code', False, 0.0, 'model') # Corrected: 4-tuple

    result = runner.invoke(cli.cli, ["generate", str(files["test.prompt"])] )

    # Should still proceed and exit cleanly from the command itself
    # The exception in auto_update is caught and printed as a warning.
    if result.exit_code != 0:
        print(f"Unexpected exit code: {result.exit_code}")
        print(f"Output:\n{result.output}")
        if result.exception:
            print(f"Exception:\n{result.exception}")
            raise result.exception

    assert result.exit_code == 0
    assert "Auto-update check failed" in result.output
    assert "Network error" in result.output
    mock_auto_update.assert_called_once_with() # auto_update is called
    mock_main.assert_called_once() # Ensure command still ran

# --- Error Handling Tests ---
# Note: With handle_error NOT re-raising, we expect exit code 0
# and the tests need to assert the specific error message in the output.

def test_cli_chaining_cost_aggregation():
    """Summary output should include every subcommand's cost and the total."""
    lines = _capture_summary(
        ['generate', 'example'],
        [
            ('generated code', 0.123, 'model-A'),
            ('example code', 0.045, 'model-B'),
        ],
    )

    summary = "\n".join(lines)
    assert "Command Execution Summary" in summary
    assert "Step 1 (generate):[/info] Cost: $0.123000" in summary
    assert "Step 2 (example):[/info] Cost: $0.045000" in summary
    assert "Total Estimated Cost" in summary and "$0.168000" in summary

def test_cli_chaining_with_no_cost_command():
    """Local commands should report zero cost but remain in the summary."""
    lines = _capture_summary(
        ['preprocess', 'generate'],
        [
            ('', 0.0, 'local'),
            ('generated code', 0.111, 'model-C'),
        ],
    )

    summary = "\n".join(lines)
    assert "Command Execution Summary" in summary
    assert "Step 1 (preprocess):[/info] Command completed (local)." in summary
    assert "Step 2 (generate):[/info] Cost: $0.111000" in summary
    assert "Total Estimated Cost" in summary and "$0.111000" in summary

def test_cli_result_callback_single_tuple_normalization():
    """When Click passes a single 3-tuple, it should count as one step."""
    lines = _capture_summary(
        ['generate'],
        # Simulate Click delivering a single 3-tuple rather than a list
        ('generated code', 0.0040675, 'gpt-5.1-codex-mini'),
    )

    summary = "\n".join(lines)
    assert "Command Execution Summary" in summary
    # Should show exactly one step associated with 'generate'
    expected_cost = f"{0.0040675:.6f}"
    assert f"Step 1 (generate):[/info] Cost: ${expected_cost}, Model: gpt-5.1-codex-mini" in summary
    # Should NOT emit Unknown Command 2/3 lines from mis-iterating over tuple elements
    assert "Unknown Command 2" not in summary
    assert "Unknown Command 3" not in summary
    # No unexpected format warnings should be printed
    assert "Unexpected result format" not in summary

def test_cli_result_callback_non_tuple_result_warning():
    """A non-tuple result should be wrapped and warned once, not split."""
    lines = _capture_summary(
        ['generate'],
        # Simulate an unexpected scalar return type
        "unexpected string result",
    )

    summary = "\n".join(lines)
    assert "Command Execution Summary" in summary
    # Should warn exactly once for step 1
    assert "Step 1 (generate):[/warning] Unexpected result format: str" in summary
    # No phantom Unknown Command entries
    assert "Unknown Command 2" not in summary
    assert "Unknown Command 3" not in summary


# --- install_completion Command Test ---