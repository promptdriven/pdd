import os
import sys
import subprocess
from pathlib import Path
from unittest.mock import patch, ANY, MagicMock, Mock

import pytest
from click.testing import CliRunner
import click

from pdd import __version__, DEFAULT_STRENGTH, DEFAULT_TEMPERATURE, DEFAULT_TIME
# Import necessary components from pdd.core.cli for testing
from pdd.core.cli import _strip_ansi_codes, OutputCapture, PDDCLI, cli as cli_command, process_commands
import pdd.core.cli as core_cli_module
import pdd.cli  # noqa: F401 — ensure register_commands() populates cli before fixture snapshots

RUN_ALL_TESTS_ENABLED = os.getenv("PDD_RUN_ALL_TESTS") == "1"

@pytest.fixture(autouse=True)
def setup_cli_environment():
    """
    Fixture to setup CLI environment for tests.
    1. Mocks get_local_pdd_path to prevent errors.
    2. Registers dummy commands (generate, fix, etc.) so CLI parsing works.
    3. Cleans up commands after test.
    """
    # Defense-in-depth: ensure all real commands are registered before snapshotting.
    # Without this, the snapshot may miss commands like 'auth' that other test files
    # in the same pytest-xdist worker depend on (see cloud batch chunk 23 failure).
    from pdd.commands import register_commands
    register_commands(cli_command)

    with patch('pdd.core.cli.get_local_pdd_path'):
        # Save original commands
        original_commands = cli_command.commands.copy()
        
        # Register dummy commands if missing
        # Note: Click converts underscores to hyphens in command names
        if "generate" not in cli_command.commands:
            @cli_command.command(context_settings=dict(ignore_unknown_options=True, allow_extra_args=True))
            def generate(ctx): pass

        if "fix" not in cli_command.commands:
            @cli_command.command()
            def fix(): pass

        if "example" not in cli_command.commands:
            @cli_command.command()
            def example(): pass

        if "install-completion" not in cli_command.commands:
            @cli_command.command("install-completion")
            def install_completion(): pass
            
        yield

        # Restore commands in-place to preserve the dict object reference
        cli_command.commands.clear()
        cli_command.commands.update(original_commands)

def _capture_summary(invoked_subcommands, results):
    """
    Helper to test process_commands callback logic without running full CLI.
    Simulates the context and captures console output.
    """
    ctx = click.Context(cli_command)
    ctx.obj = {'quiet': False, 'invoked_subcommands': invoked_subcommands}
    ctx.invoked_subcommands = invoked_subcommands
    
    with patch('pdd.core.cli.console.print') as mock_print:
        with ctx:
            process_commands(results=results)
            
    return ["".join(str(arg) for arg in call.args) for call in mock_print.call_args_list]

def test_cli_list_contexts(runner):
    """Test `pdd --list-contexts`."""
    result = runner.invoke(cli_command, ["--list-contexts"])
    assert result.exit_code == 0
    assert "default" in result.output

@patch('pdd.core.cli.auto_update')
def test_cli_list_contexts_early_exit_no_auto_update(mock_auto_update, runner, tmp_path, monkeypatch):
    """Ensure --list-contexts exits early and does not call auto_update."""
    pddrc = tmp_path / ".pddrc"
    pddrc.write_text(
        'contexts:\n'
        '  default:\n'
        '    paths: ["**"]\n'
        '  alt:\n'
        '    paths: ["src/**"]\n'
    )
    monkeypatch.chdir(tmp_path)

    result = runner.invoke(cli_command, ["--list-contexts"])
    assert result.exit_code == 0
    assert "default" in result.output
    assert "alt" in result.output
    mock_auto_update.assert_not_called()

def test_cli_list_contexts_malformed_pddrc_shows_usage_error(runner, tmp_path, monkeypatch):
    """Malformed .pddrc should cause --list-contexts to fail with usage error."""
    (tmp_path / ".pddrc").write_text('version: "1.0"\n')
    monkeypatch.chdir(tmp_path)
    result = runner.invoke(cli_command, ["--list-contexts"])
    assert result.exit_code == 2
    assert "Failed to load .pddrc" in result.output

@patch('pdd.core.cli.auto_update')
@patch('pdd.commands.generate.code_generator_main')
def test_cli_context_known_passed_to_subcommand(mock_main, mock_auto_update, runner, tmp_path, monkeypatch):
    """--context NAME sets ctx.obj['context'] and threads into the subcommand."""
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

    @cli_command.command()
    @click.argument('prompt_file')
    @click.pass_context
    def generate(ctx, prompt_file):
        mock_main(ctx=ctx)

    result = runner.invoke(cli_command, ["--context", "alt", "generate", str(prompt)])
    assert result.exit_code == 0
    mock_main.assert_called_once()
    passed_ctx = mock_main.call_args.kwargs.get('ctx')
    assert passed_ctx is not None
    assert passed_ctx.obj.get('context') == 'alt'

@patch('pdd.core.cli.auto_update')
@patch('pdd.commands.generate.code_generator_main')
def test_cli_context_unknown_raises_usage_error(mock_main, mock_auto_update, runner, tmp_path, monkeypatch):
    """Unknown --context fails early with UsageError (exit code 2) and no subcommand runs."""
    (tmp_path / ".pddrc").write_text('contexts:\n  default:\n    paths: ["**"]\n')
    (tmp_path / "prompts").mkdir()
    prompt = tmp_path / "prompts" / "x_python.prompt"
    prompt.write_text("dummy")
    monkeypatch.chdir(tmp_path)

    result = runner.invoke(cli_command, ["--context", "missing", "generate", str(prompt)])
    assert result.exit_code == 2
    assert "Unknown context 'missing'" in result.output
    mock_main.assert_not_called()
    mock_auto_update.assert_not_called()

@patch('pdd.core.cli.auto_update')
@patch('pdd.commands.generate.code_generator_main')
def test_cli_context_unknown_without_pddrc(mock_main, mock_auto_update, runner, tmp_path, monkeypatch):
    """Unknown context should still fail even when no .pddrc exists."""
    (tmp_path / "prompts").mkdir()
    prompt = tmp_path / "prompts" / "x_python.prompt"
    prompt.write_text("dummy")
    monkeypatch.chdir(tmp_path)

    result = runner.invoke(cli_command, ["--context", "alt", "generate", str(prompt)])
    assert result.exit_code == 2
    assert "Unknown context 'alt'" in result.output
    mock_main.assert_not_called()
    mock_auto_update.assert_not_called()

def test_cli_version(runner):
    """Test `pdd --version`."""
    result = runner.invoke(cli_command, ["--version"])
    assert result.exit_code == 0
    assert __version__ in result.output

def test_cli_help(runner):
    """Test `pdd --help`."""
    result = runner.invoke(cli_command, ["--help"])
    assert result.exit_code == 0
    assert "Usage: cli [OPTIONS] COMMAND" in result.output
    assert "generate" in result.output
    assert "fix" in result.output
    assert "install-completion" in result.output

def test_cli_help_shows_core_dump_flag(runner):
    """Global --core-dump option should be visible in top-level help."""
    result = runner.invoke(cli_command, ["--help"])
    assert result.exit_code == 0
    assert "--core-dump" in result.output

def test_cli_command_help(runner):
    """Test `pdd [COMMAND] --help`."""
    result = runner.invoke(cli_command, ["generate", "--help"])
    assert result.exit_code == 0
    assert "Usage: cli generate [OPTIONS]" in result.output

@patch('pdd.core.cli.auto_update')
@patch('pdd.commands.generate.code_generator_main')
@patch('pdd.cli.construct_paths')
def test_cli_global_options_defaults(mock_construct, mock_main, mock_auto_update, runner, create_dummy_files):
    """Test default global options are passed in context."""
    files = create_dummy_files("test.prompt")
    mock_main.return_value = ('code', False, 0.0, 'model')
    
    @cli_command.command()
    @click.argument('prompt_file')
    @click.pass_context
    def generate(ctx, prompt_file):
        mock_main(ctx=ctx)

    result = runner.invoke(cli_command, ["generate", str(files["test.prompt"])])
    assert result.exit_code == 0
    mock_main.assert_called_once()
    ctx = mock_main.call_args.kwargs.get('ctx')
    assert ctx.obj['force'] is False
    assert 'strength' not in ctx.obj
    assert 'temperature' not in ctx.obj
    assert ctx.obj['verbose'] is False
    assert ctx.obj['quiet'] is False
    assert ctx.obj['output_cost'] is None
    assert ctx.obj['local'] is False
    assert ctx.obj['review_examples'] is False
    assert ctx.obj['time'] == DEFAULT_TIME
    mock_auto_update.assert_called_once_with()

@patch('pdd.core.cli.auto_update')
@patch('pdd.commands.generate.code_generator_main')
@patch('pdd.cli.construct_paths')
def test_cli_global_options_explicit(mock_construct, mock_main, mock_auto_update, runner, create_dummy_files):
    """Test explicit global options override defaults."""
    files = create_dummy_files("test.prompt")
    mock_main.return_value = ('code', False, 0.0, 'model')
    
    @cli_command.command()
    @click.argument('prompt_file')
    @click.pass_context
    def generate(ctx, prompt_file):
        mock_main(ctx=ctx)

    result = runner.invoke(cli_command, [
        "--force",
        "--strength", f"{DEFAULT_STRENGTH}",
        "--temperature", "0.5",
        "--verbose",
        "--output-cost", "./output/costs.csv",
        "--local",
        "--review-examples",
        "--time", "0.7",
        "generate", str(files["test.prompt"])
    ])
    assert result.exit_code == 0
    mock_main.assert_called_once()
    ctx = mock_main.call_args.kwargs.get('ctx')
    assert ctx.obj['force'] is True
    assert ctx.obj['strength'] == DEFAULT_STRENGTH
    assert ctx.obj['temperature'] == 0.5
    assert ctx.obj['verbose'] is True
    assert ctx.obj['quiet'] is False
    assert ctx.obj['output_cost'] == "./output/costs.csv"
    assert ctx.obj['local'] is True
    assert ctx.obj['review_examples'] is True
    assert ctx.obj['time'] == 0.7
    mock_auto_update.assert_called_once_with()

@patch('pdd.core.cli.auto_update')
@patch('pdd.commands.generate.code_generator_main')
@patch('pdd.cli.construct_paths')
def test_cli_global_options_quiet_overrides_verbose(mock_construct, mock_main, mock_auto_update, runner, create_dummy_files):
    """Test --quiet overrides --verbose."""
    files = create_dummy_files("test.prompt")
    mock_main.return_value = ('code', False, 0.0, 'model')
    
    @cli_command.command()
    @click.argument('prompt_file')
    @click.pass_context
    def generate(ctx, prompt_file):
        mock_main(ctx=ctx)

    result = runner.invoke(cli_command, ["--verbose", "--quiet", "generate", str(files["test.prompt"])])
    assert result.exit_code == 0
    ctx = mock_main.call_args.kwargs.get('ctx')
    assert ctx.obj['verbose'] is False
    assert ctx.obj['quiet'] is True
    mock_auto_update.assert_called_once_with()

@patch('pdd.core.cli.auto_update')
@patch('pdd.commands.generate.code_generator_main')
@patch('pdd.cli.construct_paths')
def test_cli_auto_update_called_by_default(mock_construct, mock_main, mock_auto_update, runner, create_dummy_files):
    """Test auto_update is called by default."""
    files = create_dummy_files("test.prompt")
    mock_main.return_value = ('code', False, 0.0, 'model')
    
    @cli_command.command()
    @click.argument('prompt_file')
    @click.pass_context
    def generate(ctx, prompt_file):
        mock_main(ctx=ctx)

    runner.invoke(cli_command, ["generate", str(files["test.prompt"])])
    mock_auto_update.assert_called_once_with()

@patch.dict(os.environ, {"PDD_AUTO_UPDATE": "false"}, clear=True)
@patch('pdd.core.cli.auto_update')
@patch('pdd.commands.generate.code_generator_main')
@patch('pdd.cli.construct_paths')
def test_cli_auto_update_not_called_when_disabled(mock_construct, mock_main, mock_auto_update, runner, create_dummy_files):
    """Test auto_update is not called when PDD_AUTO_UPDATE=false."""
    files = create_dummy_files("test.prompt")
    mock_main.return_value = ('code', False, 0.0, 'model')
    
    @cli_command.command()
    @click.argument('prompt_file')
    @click.pass_context
    def generate(ctx, prompt_file):
        mock_main(ctx=ctx)

    runner.invoke(cli_command, ["generate", str(files["test.prompt"])])
    mock_auto_update.assert_not_called()

@patch('pdd.core.cli.auto_update', side_effect=Exception("Network error"))
@patch('pdd.commands.generate.code_generator_main')
@patch('pdd.cli.construct_paths')
def test_cli_auto_update_handles_exception(mock_construct, mock_main, mock_auto_update, runner, create_dummy_files):
    """Test auto_update exceptions are handled gracefully."""
    files = create_dummy_files("test.prompt")
    mock_main.return_value = ('code', False, 0.0, 'model')
    
    @cli_command.command()
    @click.argument('prompt_file')
    @click.pass_context
    def generate(ctx, prompt_file):
        mock_main(ctx=ctx)

    result = runner.invoke(cli_command, ["generate", str(files["test.prompt"])])
    assert result.exit_code == 0
    assert "Auto-update check failed" in result.output
    assert "Network error" in result.output

def test_cli_chaining_cost_aggregation():
    lines = _capture_summary(['generate', 'example'], [('generated code', 0.123, 'model-A'), ('example code', 0.045, 'model-B')])
    summary = "\n".join(lines)
    assert "Command Execution Summary" in summary
    assert "Step 1 (generate):[/info] Cost: $0.123000" in summary
    assert "Step 2 (example):[/info] Cost: $0.045000" in summary
    assert "Total Estimated Cost" in summary and "$0.168000" in summary

def test_cli_chaining_with_no_cost_command():
    lines = _capture_summary(['preprocess', 'generate'], [('', 0.0, 'local'), ('generated code', 0.111, 'model-C')])
    summary = "\n".join(lines)
    assert "Command Execution Summary" in summary
    assert "Step 1 (preprocess):[/info] Command completed (local)." in summary
    assert "Step 2 (generate):[/info] Cost: $0.111000" in summary

def test_cli_result_callback_single_tuple_normalization():
    lines = _capture_summary(['generate'], ('generated code', 0.0040675, 'gpt-5.1-codex-mini'))
    summary = "\n".join(lines)
    assert "Command Execution Summary" in summary
    assert f"Step 1 (generate):[/info] Cost: ${0.0040675:.6f}, Model: gpt-5.1-codex-mini" in summary

def test_cli_result_callback_non_tuple_result_warning():
    lines = _capture_summary(['generate'], "unexpected string result")
    summary = "\n".join(lines)
    assert "Step 1 (generate):[/warning] Unexpected result format: str" in summary

@patch('pdd.core.cli.auto_update')
@patch('pdd.commands.generate.code_generator_main')
def test_user_cancellation_does_not_show_error_message_issue_186(mock_main, mock_auto_update, runner, tmp_path, monkeypatch):
    monkeypatch.chdir(tmp_path)
    prompt_file = tmp_path / "demo_python.prompt"
    prompt_file.write_text("// demo_python.prompt\n")
    def cancel_side_effect(*args, **kwargs):
        click.secho("Operation cancelled.", fg="red", err=True)
        raise click.Abort()
    mock_main.side_effect = cancel_side_effect
    
    @cli_command.command()
    @click.argument('prompt_file')
    @click.pass_context
    def generate(ctx, prompt_file):
        mock_main(ctx=ctx)

    result = runner.invoke(cli_command, ['generate', str(prompt_file)])
    assert result.exit_code != 0
    assert 'Operation cancelled' in result.output
    assert "Error during" not in result.output

@patch('pdd.core.cli.auto_update')
@patch('pdd.commands.generate.code_generator_main')
def test_bug_cli_default_strength_shadows_pddrc(mock_main, mock_auto_update, runner, tmp_path, monkeypatch):
    (tmp_path / "prompts").mkdir()
    (tmp_path / ".pddrc").write_text('version: "1.0"\ncontexts:\n  backend:\n    paths: ["**"]\n    defaults:\n      strength: 0.8\n')
    prompt = tmp_path / "prompts" / "demo_python.prompt"
    prompt.write_text("dummy prompt")
    monkeypatch.chdir(tmp_path)
    mock_main.return_value = ('code', False, 0.0, 'model')
    
    @cli_command.command()
    @click.argument('prompt_file')
    @click.pass_context
    def generate(ctx, prompt_file):
        mock_main(ctx=ctx)

    result = runner.invoke(cli_command, ["--context", "backend", "generate", str(prompt)])
    assert result.exit_code == 0
    passed_ctx = mock_main.call_args.kwargs.get('ctx')
    assert passed_ctx.obj.get('strength') is None

@patch('pdd.core.cli.auto_update')
@patch('pdd.commands.generate.code_generator_main')
def test_bug_cli_default_temperature_shadows_pddrc(mock_main, mock_auto_update, runner, tmp_path, monkeypatch):
    (tmp_path / "prompts").mkdir()
    (tmp_path / ".pddrc").write_text('version: "1.0"\ncontexts:\n  backend:\n    paths: ["**"]\n    defaults:\n      temperature: 0.5\n')
    prompt = tmp_path / "prompts" / "demo_python.prompt"
    prompt.write_text("dummy prompt")
    monkeypatch.chdir(tmp_path)
    mock_main.return_value = ('code', False, 0.0, 'model')
    
    @cli_command.command()
    @click.argument('prompt_file')
    @click.pass_context
    def generate(ctx, prompt_file):
        mock_main(ctx=ctx)

    result = runner.invoke(cli_command, ["--context", "backend", "generate", str(prompt)])
    assert result.exit_code == 0
    passed_ctx = mock_main.call_args.kwargs.get('ctx')
    assert passed_ctx.obj.get('temperature') is None

@patch('pdd.core.cli.auto_update')
@patch('pdd.commands.generate.code_generator_main')
def test_cli_explicit_strength_overrides_pddrc(mock_main, mock_auto_update, runner, tmp_path, monkeypatch):
    (tmp_path / "prompts").mkdir()
    (tmp_path / ".pddrc").write_text('version: "1.0"\ncontexts:\n  backend:\n    paths: ["**"]\n    defaults:\n      strength: 0.8\n')
    prompt = tmp_path / "prompts" / "demo_python.prompt"
    prompt.write_text("dummy prompt")
    monkeypatch.chdir(tmp_path)
    mock_main.return_value = ('code', False, 0.0, 'model')
    
    @cli_command.command()
    @click.argument('prompt_file')
    @click.pass_context
    def generate(ctx, prompt_file):
        mock_main(ctx=ctx)

    result = runner.invoke(cli_command, ["--context", "backend", "--strength", "0.5", "generate", str(prompt)])
    assert result.exit_code == 0
    passed_ctx = mock_main.call_args.kwargs.get('ctx')
    assert passed_ctx.obj.get('strength') == 0.5

@patch('pdd.core.cli.auto_update')
@patch('pdd.commands.generate.code_generator_main')
def test_ctx_obj_get_returns_default_when_strength_not_passed(mock_main, mock_auto_update, runner, tmp_path, monkeypatch):
    (tmp_path / "prompts").mkdir()
    prompt = tmp_path / "prompts" / "demo_python.prompt"
    prompt.write_text("dummy prompt")
    monkeypatch.chdir(tmp_path)
    mock_main.return_value = ('code', False, 0.0, 'model')
    
    @cli_command.command()
    @click.argument('prompt_file')
    @click.pass_context
    def generate(ctx, prompt_file):
        mock_main(ctx=ctx)

    result = runner.invoke(cli_command, ["generate", str(prompt)])
    assert result.exit_code == 0
    passed_ctx = mock_main.call_args.kwargs.get('ctx')
    assert 'strength' not in passed_ctx.obj
    assert passed_ctx.obj.get("strength", DEFAULT_STRENGTH) == DEFAULT_STRENGTH

@patch('pdd.core.cli.auto_update')
@patch('pdd.commands.generate.code_generator_main')
def test_ctx_obj_get_returns_default_when_temperature_not_passed(mock_main, mock_auto_update, runner, tmp_path, monkeypatch):
    (tmp_path / "prompts").mkdir()
    prompt = tmp_path / "prompts" / "demo_python.prompt"
    prompt.write_text("dummy prompt")
    monkeypatch.chdir(tmp_path)
    mock_main.return_value = ('code', False, 0.0, 'model')
    
    @cli_command.command()
    @click.argument('prompt_file')
    @click.pass_context
    def generate(ctx, prompt_file):
        mock_main(ctx=ctx)

    result = runner.invoke(cli_command, ["generate", str(prompt)])
    assert result.exit_code == 0
    passed_ctx = mock_main.call_args.kwargs.get('ctx')
    assert 'temperature' not in passed_ctx.obj
    assert passed_ctx.obj.get("temperature", DEFAULT_TEMPERATURE) == DEFAULT_TEMPERATURE

def test_strip_ansi_codes_removes_colors():
    text = "\x1b[31mRed Text\x1b[0m and Normal Text"
    assert _strip_ansi_codes(text) == "Red Text and Normal Text"

def test_strip_ansi_codes_removes_complex_sequences():
    text = "\x1b[1;31;42mComplex\x1b[0m"
    assert _strip_ansi_codes(text) == "Complex"

def test_strip_ansi_codes_leaves_plain_text():
    text = "Just plain text"
    assert _strip_ansi_codes(text) == text

def test_output_capture_writes_to_both():
    mock_stream = Mock()
    capture = OutputCapture(mock_stream)
    capture.write("Hello")
    mock_stream.write.assert_called_with("Hello")
    assert capture.get_captured_output() == "Hello"

def test_output_capture_delegates_methods():
    mock_stream = Mock()
    mock_stream.isatty.return_value = True
    mock_stream.fileno.return_value = 123
    capture = OutputCapture(mock_stream)
    assert capture.isatty() is True
    assert capture.fileno() == 123

def test_output_capture_flush():
    mock_stream = Mock()
    capture = OutputCapture(mock_stream)
    capture.flush()
    mock_stream.flush.assert_called_once()

def test_output_capture_resilience():
    mock_stream = Mock()
    capture = OutputCapture(mock_stream)
    capture.buffer = Mock()
    capture.buffer.write.side_effect = Exception("Buffer full")
    capture.write("test")
    mock_stream.write.assert_called_with("test")

def test_pddcli_format_help_includes_suite():
    group = PDDCLI(name="pdd")
    ctx = click.Context(group)
    formatter = click.HelpFormatter()
    group.format_help(ctx, formatter)
    output = formatter.getvalue()
    assert "Generate Suite (related commands)" in output
    assert "generate" in output

@patch('pdd.core.cli.handle_error')
@patch('pdd.core.cli._write_core_dump')
def test_pddcli_invoke_handles_exception(mock_write_dump, mock_handle_error):
    def failing_cmd(): raise ValueError("Boom")
    cmd = click.Command("fail", callback=failing_cmd)
    group = PDDCLI(commands={"fail": cmd})
    runner = CliRunner()
    result = runner.invoke(group, ["fail"])
    assert result.exit_code == 1
    mock_handle_error.assert_called_once()

@patch('pdd.core.cli.handle_error')
def test_pddcli_invoke_handles_system_exit_error(mock_handle_error):
    def exit_cmd(): sys.exit(1)
    cmd = click.Command("exit", callback=exit_cmd)
    group = PDDCLI(commands={"exit": cmd})
    runner = CliRunner()
    result = runner.invoke(group, ["exit"])
    assert result.exit_code == 1
    mock_handle_error.assert_called_once()

@patch('pdd.core.cli._write_core_dump')
def test_pddcli_invoke_captures_output_for_dump(mock_write_dump):
    # Create mocks for the capture objects
    stdout_capture = Mock()
    stderr_capture = Mock()
    stdout_capture.get_captured_output.return_value = "Captured STDOUT"
    stderr_capture.get_captured_output.return_value = "Captured STDERR"
    # Don't set original_stream to avoid CliRunner stream restoration issues
    # The code checks `if stdout_capture:` before restoring, so we let it try
    # but we'll capture the current streams at runtime
    stdout_capture.original_stream = None
    stderr_capture.original_stream = None

    ctx_obj = {"core_dump": True, "_stdout_capture": stdout_capture, "_stderr_capture": stderr_capture}

    def dump_cmd():
        ctx = click.get_current_context()
        # Capture the current streams so restoration doesn't break CliRunner
        ctx_obj["_stdout_capture"].original_stream = sys.stdout
        ctx_obj["_stderr_capture"].original_stream = sys.stderr
        # Update the PARENT context's obj (group context) since that's what
        # PDDCLI.invoke checks when handling exceptions
        parent_ctx = ctx.parent
        if parent_ctx is not None:
            if parent_ctx.obj is None:
                parent_ctx.obj = {}
            parent_ctx.obj.update(ctx_obj)
        raise ValueError("Trigger Dump")
    cmd = click.Command("dump", callback=dump_cmd)
    group = PDDCLI(commands={"dump": cmd})
    CliRunner().invoke(group, ["dump"])
    mock_write_dump.assert_called_once()
    terminal_output = mock_write_dump.call_args[0][4]
    assert "=== STDOUT ===" in terminal_output
    assert "Captured STDOUT" in terminal_output

@patch('pdd.core.cli.get_local_pdd_path')
@patch('pdd.core.cli.clear_core_dump_errors')
@patch('pdd.core.cli.auto_update')
def test_cli_initialization_calls(mock_update, mock_clear, mock_get_path, runner):
    runner.invoke(cli_command, [])
    mock_get_path.assert_called_once()
    mock_clear.assert_called_once()

@patch('pdd.core.cli.auto_update')
def test_cli_core_dump_enables_capture(mock_update, runner):
    @cli_command.command()
    @click.pass_context
    def check_capture(ctx):
        assert ctx.obj["core_dump"] is True
        assert isinstance(sys.stdout, OutputCapture)
    # Use hyphen in command name since Click converts underscores to hyphens
    result = runner.invoke(cli_command, ["--core-dump", "check-capture"])
    assert result.exit_code == 0

@patch('pdd.core.cli.auto_update')
def test_cli_time_default(mock_update, runner):
    @cli_command.command()
    @click.pass_context
    def check_time(ctx):
        assert ctx.obj["time"] == DEFAULT_TIME
    # Use hyphen in command name since Click converts underscores to hyphens
    result = runner.invoke(cli_command, ["check-time"])
    assert result.exit_code == 0

@patch('pdd.core.cli._should_show_onboarding_reminder')
@patch('pdd.core.cli.console.print')
def test_cli_onboarding_reminder(mock_print, mock_should_show, runner):
    mock_should_show.return_value = True
    @cli_command.command()
    def dummy(): pass
    runner.invoke(cli_command, ["dummy"])
    found = False
    for call in mock_print.call_args_list:
        if call.args and "[warning]Complete onboarding" in str(call.args[0]):
            found = True
            break
    assert found

@patch('pdd.core.cli.console.print')
@patch('pdd.core.cli._write_core_dump')
def test_process_commands_examples_used(mock_write_dump, mock_print):
    ctx = click.Context(cli_command)
    ctx.obj = {"quiet": False, "core_dump": False}
    ctx.invoked_subcommands = ["generate"]
    results = [({"examplesUsed": [{"slug": "ex1", "title": "Example 1"}]}, 0.1, "gpt-4")]
    with ctx:
        process_commands(results=results)
    printed_text = " ".join(str(call.args[0]) for call in mock_print.call_args_list)
    assert "Examples used:" in printed_text

@patch('pdd.core.cli.console.print')
@patch('pdd.core.cli._write_core_dump')
def test_process_commands_preprocess_local(mock_write_dump, mock_print):
    ctx = click.Context(cli_command)
    ctx.obj = {"quiet": False, "core_dump": False}
    ctx.invoked_subcommands = ["preprocess"]
    with ctx:
        process_commands(results=[({}, 0.0, "local")])
    printed_text = " ".join(str(call.args[0]) for call in mock_print.call_args_list)
    assert "Command completed (local)" in printed_text

@patch('pdd.core.cli.console.print')
@patch('pdd.core.cli._write_core_dump')
def test_process_commands_install_completion_success(mock_write_dump, mock_print):
    ctx = click.Context(cli_command)
    ctx.obj = {"quiet": False, "core_dump": False}
    ctx.invoked_subcommands = ["install_completion"]
    with ctx:
        process_commands(results=[None])
    printed_text = " ".join(str(call.args[0]) for call in mock_print.call_args_list)
    assert "Command completed" in printed_text

@patch('pdd.core.cli.console.print')
@patch('pdd.core.cli._write_core_dump')
def test_process_commands_fatal_exception(mock_write_dump, mock_print):
    ctx = click.Context(cli_command)
    ctx.obj = {"quiet": False, "core_dump": False, "_fatal_exception": True}
    ctx.invoked_subcommands = ["generate"]
    ctx.exit = Mock()
    with ctx:
        process_commands(results=[({}, 0.1, "gpt-4")])
    ctx.exit.assert_called_with(1)

if __name__ == "__main__":
    import pytest
    sys.exit(pytest.main([__file__]))
