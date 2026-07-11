import os
import sys
import subprocess
from pathlib import Path
from unittest.mock import patch, ANY, MagicMock, Mock

import pytest
from click.testing import CliRunner
import click

from pdd import __version__, DEFAULT_STRENGTH, DEFAULT_TEMPERATURE, DEFAULT_TIME
from pdd.cli_branding import PDD_FULL_TAGLINE, PDD_POSITIONING
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
            try:
                process_commands(results=results)
            except click.exceptions.Exit as exc:
                if exc.exit_code != 1:
                    raise
            
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
    assert PDD_FULL_TAGLINE in result.output
    assert PDD_POSITIONING in result.output
    assert "generate" in result.output
    assert "fix" in result.output
    assert "install-completion" in result.output

def test_cli_help_shows_core_dump_flag(runner):
    """Global --core-dump option should be visible in top-level help."""
    result = runner.invoke(cli_command, ["--help"])
    assert result.exit_code == 0
    assert "--core-dump" in result.output


def test_cli_help_shows_current_strength_default(runner):
    """Strength help text should stay aligned with the package default."""
    result = runner.invoke(cli_command, ["--help"])
    assert result.exit_code == 0
    assert f"Default: {DEFAULT_STRENGTH} or .pddrc value." in result.output

def test_cli_command_help(runner):
    """Test `pdd [COMMAND] --help`."""
    result = runner.invoke(cli_command, ["generate", "--help"])
    assert result.exit_code == 0
    assert "Usage: cli generate [OPTIONS]" in result.output

@patch.dict(os.environ, {"PDD_AUTO_UPDATE": "true"})
@patch('pdd.core.cli.auto_update')
@patch('pdd.commands.generate.code_generator_main')
@patch('pdd.cli.construct_paths')
def test_cli_global_options_defaults(mock_construct, mock_main, mock_auto_update, runner, create_dummy_files, monkeypatch):
    """Test default global options are passed in context."""
    monkeypatch.delenv("PDD_FORCE_LOCAL", raising=False)
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
    assert 'grounding_review_decisions' not in ctx.obj
    assert ctx.obj.get('compress_examples') is None
    assert ctx.obj.get('compress_test_context') is None
    assert ctx.obj.get('context_compression') is None
    assert ctx.obj.get('compression_fallback') is None
    assert ctx.obj['time'] == DEFAULT_TIME
    mock_auto_update.assert_called_once_with()

@patch.dict(os.environ, {"PDD_AUTO_UPDATE": "true"})
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
    assert ctx.obj['grounding_review_decisions'] == []
    assert ctx.obj['time'] == 0.7
    mock_auto_update.assert_called_once_with()


@patch('pdd.core.cli.auto_update')
@patch('pdd.commands.generate.code_generator_main')
@patch('pdd.cli.construct_paths')
def test_cli_context_compression_flags(mock_construct, mock_main, mock_auto_update, runner, create_dummy_files):
    """Global compression flags populate ctx.obj and export env vars."""
    files = create_dummy_files("test.prompt")
    mock_main.return_value = ('code', False, 0.0, 'model')

    @cli_command.command()
    @click.argument('prompt_file')
    @click.pass_context
    def generate(ctx, prompt_file):
        mock_main(ctx=ctx)

    result = runner.invoke(cli_command, [
        "--compress-examples",
        "--compress-test-context",
        "--context-compression", "all",
        "--compression-fallback", "error",
        "generate", str(files["test.prompt"]),
    ])
    assert result.exit_code == 0
    ctx = mock_main.call_args.kwargs.get('ctx')
    assert ctx.obj['compress_examples'] is True
    assert ctx.obj['compress_test_context'] is True
    assert ctx.obj['context_compression'] == "all"
    assert ctx.obj['compression_fallback'] == "error"
    assert os.environ.get("PDD_COMPRESS_EXAMPLES") == "1"
    assert os.environ.get("PDD_COMPRESS_TEST_CONTEXT") == "1"
    assert os.environ.get("PDD_CONTEXT_COMPRESSION") == "all"
    assert os.environ.get("PDD_COMPRESSION_FALLBACK") == "error"
    for key in (
        "PDD_COMPRESS_EXAMPLES",
        "PDD_COMPRESS_TEST_CONTEXT",
        "PDD_CONTEXT_COMPRESSION",
        "PDD_COMPRESSION_FALLBACK",
    ):
        os.environ.pop(key, None)


def test_generate_rejects_subcommand_local_context_compression(runner):
    """Compression flags are global; they must appear before the subcommand."""
    import pdd.cli

    result = runner.invoke(
        pdd.cli.cli,
        ["generate", "--context-compression", "all", "--help"],
        env={"PDD_AUTO_UPDATE": "false"},
    )
    assert result.exit_code == 2


def test_preprocess_rejects_subcommand_local_context_compression(runner):
    import pdd.cli

    result = runner.invoke(
        pdd.cli.cli,
        ["preprocess", "--context-compression", "all", "--help"],
        env={"PDD_AUTO_UPDATE": "false"},
    )
    assert result.exit_code == 2


@patch('pdd.core.cli.auto_update')
@patch('pdd.commands.generate.code_generator_main')
@patch('pdd.cli.construct_paths')
def test_cli_context_compression_off_clears_env(
    mock_construct, mock_main, mock_auto_update, runner, create_dummy_files, monkeypatch
):
    monkeypatch.setenv("PDD_CONTEXT_COMPRESSION", "examples")
    files = create_dummy_files("test.prompt")
    mock_main.return_value = ('code', False, 0.0, 'model')

    @cli_command.command()
    @click.argument('prompt_file')
    @click.pass_context
    def generate(ctx, prompt_file):
        mock_main(ctx=ctx)

    result = runner.invoke(
        cli_command,
        ["--context-compression", "off", "generate", str(files["test.prompt"])],
    )
    assert result.exit_code == 0
    assert "PDD_CONTEXT_COMPRESSION" not in os.environ
    assert "PDD_COMPRESS_EXAMPLES" not in os.environ
    assert "PDD_COMPRESS_TEST_CONTEXT" not in os.environ


@patch('pdd.core.cli.auto_update')
def test_process_commands_includes_compression_summary(mock_auto_update):
    import pdd.compression_reporting as cr

    cr.clear_compression_fallback_events()
    os.environ["PDD_CONTEXT_COMPRESSION"] = "examples"
    try:
        lines = _capture_summary(['generate'], [('ok', 0.01, 'model-x')])
        assert "Context compression active" in "\n".join(lines)
    finally:
        os.environ.pop("PDD_CONTEXT_COMPRESSION", None)
        cr.clear_compression_fallback_events()


@patch.dict(os.environ, {"PDD_AUTO_UPDATE": "true"})
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

@patch.dict(os.environ, {"PDD_AUTO_UPDATE": "true"})
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

@patch.dict(os.environ, {"PDD_AUTO_UPDATE": "true"})
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


@pytest.mark.parametrize("model_name", ["", "unknown", "Unknown", "N/A", "n/a", "none", "skipped"])
def test_cli_summary_suppresses_blank_or_placeholder_model(model_name):
    """#1103: zero-cost no-ops (e.g. an all_synced sync) return an empty or
    placeholder model name; the summary must not render a trailing blank
    'Model: ' label or a meaningless 'Model: unknown' string."""
    lines = _capture_summary(['sync'], ('aggregated', 0.0, model_name))
    summary = "\n".join(lines)
    assert "Step 1 (sync):[/info] Cost: $0.000000" in summary
    # Whichever placeholder model is returned must be suppressed entirely.
    assert f"Model: {model_name}" not in summary
    # And we must not emit a trailing-space "Model: " literal either.
    assert "Model: \n" not in summary
    assert not any(line.rstrip().endswith("Model:") for line in lines)


def test_cli_summary_renders_real_model_name():
    """Sanity guard for the suppression rule: a real model name still renders."""
    lines = _capture_summary(['generate'], ('generated', 0.05, 'claude-opus-4-7'))
    summary = "\n".join(lines)
    assert "Cost: $0.050000, Model: claude-opus-4-7" in summary

def test_cli_result_callback_non_tuple_result_warning():
    lines = _capture_summary(['generate'], "unexpected string result")
    summary = "\n".join(lines)
    assert "Step 1 (generate):[/warning] Unexpected result format: str" in summary


def test_cli_summary_uses_shared_status_glyphs():
    """EPIC #1540, workstream 2: the execution summary speaks the same
    SUCCESS/FAILURE vocabulary as every other command, so each step line is
    prefixed with the shared cli_status glyph (✓ for success, ✗ for failure)."""
    from pdd.cli_status import GLYPHS, Status

    ok, fail = GLYPHS[Status.SUCCESS], GLYPHS[Status.FAILURE]

    # A successful (cost-bearing) step is marked with the success glyph.
    success = "\n".join(_capture_summary(['generate'], ('code', 0.1, 'model-A')))
    assert ok in success
    assert f"[success]{ok}[/success]" in success

    # A failed step (None result) is marked with the failure glyph.
    failure = "\n".join(_capture_summary(['generate'], [None]))
    assert fail in failure
    assert f"[error]{fail}[/error]" in failure


def test_shared_console_uses_brand_palette():
    """EPIC #1540, workstream 1: the shared CLI console renders semantic roles
    from the central brand palette by default (not an ad-hoc per-module theme),
    so the enhanced color system is on without any flag."""
    from pdd.core.errors import custom_theme
    from pdd.cli_theme import ELECTRIC_CYAN, BUILD_GREEN

    # 'command' is the hero role -> Electric-Cyan (brand), not the old magenta.
    assert ELECTRIC_CYAN.lower() in str(custom_theme.styles.get("command")).lower()
    assert BUILD_GREEN.lower() in str(custom_theme.styles.get("success")).lower()


import io as _io
from contextlib import contextmanager as _contextmanager


@_contextmanager
def _restore_shared_console_color():
    """Snapshot/restore the shared console's color state and NO_COLOR/FORCE_COLOR
    so a test that flips the global color preference never leaks into others."""
    from pdd.core import errors as _errors

    con = _errors.console
    saved = (con.no_color, con._force_terminal, con._color_system)
    saved_env = {k: os.environ.get(k) for k in ("NO_COLOR", "FORCE_COLOR")}
    try:
        yield con
    finally:
        con.no_color, con._force_terminal, con._color_system = saved
        for k, v in saved_env.items():
            if v is None:
                os.environ.pop(k, None)
            else:
                os.environ[k] = v


def _render(con):
    buf = _io.StringIO()
    saved_file = getattr(con, "_file", None)
    try:
        con.file = buf
        con.print("[command]pdd[/command]")
        return buf.getvalue()
    finally:
        con._file = saved_file


def test_set_console_color_toggles_a_console():
    """_set_console_color forces color on (even non-TTY) and strips it off."""
    from rich.console import Console
    from rich.theme import Theme
    from pdd.core.errors import _set_console_color
    from pdd.cli_theme import SEMANTIC_STYLES

    con = Console(theme=Theme(SEMANTIC_STYLES), force_terminal=True)
    _set_console_color(con, False)
    assert "\x1b[" not in _render(con)
    _set_console_color(con, True)
    assert "\x1b[" in _render(con)


def test_apply_color_preference_env_and_shared_console():
    """The global preference sets NO_COLOR/FORCE_COLOR (so later-built consoles
    inherit it) and updates the already-constructed shared console in place."""
    from pdd.core import errors

    with _restore_shared_console_color() as con:
        restore_no_color = errors.apply_color_preference(False)
        try:
            assert os.environ.get("NO_COLOR") == "1"
            assert "FORCE_COLOR" not in os.environ
            assert con.no_color is True

            restore_color = errors.apply_color_preference(True)
            try:
                assert os.environ.get("FORCE_COLOR") == "1"
                assert "NO_COLOR" not in os.environ
                assert con.no_color is False
                assert "\x1b[" in _render(con)

                # None is auto (the default) and must change nothing it was just set to.
                errors.apply_color_preference(None)
                assert os.environ.get("FORCE_COLOR") == "1"
            finally:
                restore_color()

            assert os.environ.get("NO_COLOR") == "1"
            assert "FORCE_COLOR" not in os.environ
        finally:
            restore_no_color()


def test_apply_color_preference_updates_preexisting_command_consoles():
    """Module-level command consoles imported before the root callback must
    honor the later global ``--no-color`` preference."""
    from pdd.commands.auth import console as auth_console
    from pdd.cmd_test_main import console as test_console
    from pdd.core import errors

    consoles = (errors.console, auth_console, test_console)
    before = [
        (con.no_color, con._force_terminal, con._color_system)
        for con in consoles
    ]

    restore = errors.apply_color_preference(False)
    try:
        assert all(con.no_color is True for con in consoles)
    finally:
        restore()

    assert [
        (con.no_color, con._force_terminal, con._color_system)
        for con in consoles
    ] == before


def test_apply_color_preference_forces_later_bare_console_output(monkeypatch):
    """A Rich ``Console()`` built after ``--color`` must emit ANSI even when
    output is captured or piped."""
    from rich.console import Console
    from pdd.core import errors

    monkeypatch.delenv("NO_COLOR", raising=False)
    restore = errors.apply_color_preference(True)
    try:
        con = Console()
        assert con.no_color is False
        assert con._force_terminal is True
        with con.capture() as cap:
            con.print("[red]RED[/red]")
        assert "\x1b[" in cap.get()
    finally:
        restore()


def test_apply_color_preference_restores_later_bare_console_to_auto(monkeypatch):
    """A console constructed during ``--no-color`` must not keep the temporary
    preference after the invocation cleanup restores a clean environment."""
    from rich.console import Console
    from pdd.core import errors

    monkeypatch.delenv("NO_COLOR", raising=False)
    monkeypatch.delenv("FORCE_COLOR", raising=False)

    restore = errors.apply_color_preference(False)
    con = Console()
    assert con.no_color is True
    restore()

    assert "NO_COLOR" not in os.environ
    assert "FORCE_COLOR" not in os.environ
    assert con.no_color is False
    assert con._force_terminal is None
    assert con._color_system is None


def test_apply_color_preference_reaches_construct_paths_early_import():
    """Regression for CLI import order: ``pdd.core.cli`` imports
    ``construct_paths`` before ``pdd.core.errors``. The construct_paths module
    console must still be registered for global color preferences."""
    script = """
from pdd.core import cli as _cli
from pdd import construct_paths
from pdd.core.errors import apply_color_preference

restore = apply_color_preference(False)
try:
    print('no-color', construct_paths.console.no_color)
finally:
    restore()

restore = apply_color_preference(True)
try:
    print(
        'color',
        construct_paths.console.no_color,
        construct_paths.console._force_terminal,
        construct_paths.console._color_system is not None,
    )
finally:
    restore()
"""
    env = os.environ.copy()
    env.pop("NO_COLOR", None)
    result = subprocess.run(
        [sys.executable, "-c", script],
        cwd=Path(__file__).resolve().parents[2],
        env=env,
        text=True,
        capture_output=True,
        check=True,
    )

    assert "no-color True" in result.stdout
    assert "color False True True" in result.stdout


def test_apply_color_preference_survives_cli_theme_reload():
    """Regression: ``pdd.core.errors.console`` exists before reloading
    ``pdd.cli_theme``; later ``apply_color_preference(...)`` calls must still
    update it.

    The console registry is anchored on the process-global ``Console`` class, so
    ``importlib.reload(pdd.cli_theme)`` (which resets the module's globals) must
    not drop consoles that were registered before the reload. Run in a fresh
    interpreter so the in-place reload cannot perturb the rest of the suite."""
    script = """
import importlib
from pdd.core.errors import apply_color_preference, console as core_console
import pdd.cli_theme as cli_theme

importlib.reload(cli_theme)

restore = apply_color_preference(False)
try:
    print('no-color', core_console.no_color)
finally:
    restore()

restore = apply_color_preference(True)
try:
    print('color', core_console.no_color, core_console._force_terminal)
finally:
    restore()
"""
    env = os.environ.copy()
    env.pop("NO_COLOR", None)
    result = subprocess.run(
        [sys.executable, "-c", script],
        cwd=Path(__file__).resolve().parents[2],
        env=env,
        text=True,
        capture_output=True,
        check=True,
    )

    assert "no-color True" in result.stdout
    assert "color False True" in result.stdout


def test_cli_no_color_flag_disables_color(runner):
    """`pdd --no-color …` is invocation-scoped and does not leak into later runs."""
    with _restore_shared_console_color() as con:
        before = (con.no_color, con._force_terminal, con._color_system)
        before_env = {k: os.environ.get(k) for k in ("NO_COLOR", "FORCE_COLOR")}
        result = runner.invoke(cli_command, ["--no-color", "--list-contexts"])
        assert result.exit_code == 0
        assert {k: os.environ.get(k) for k in ("NO_COLOR", "FORCE_COLOR")} == before_env
        assert (con.no_color, con._force_terminal, con._color_system) == before


def test_cli_color_flag_forces_color(runner):
    """`pdd --color …` is invocation-scoped and does not leak into later runs."""
    with _restore_shared_console_color() as con:
        before = (con.no_color, con._force_terminal, con._color_system)
        before_env = {k: os.environ.get(k) for k in ("NO_COLOR", "FORCE_COLOR")}
        result = runner.invoke(cli_command, ["--color", "--list-contexts"])
        assert result.exit_code == 0
        assert {k: os.environ.get(k) for k in ("NO_COLOR", "FORCE_COLOR")} == before_env
        assert (con.no_color, con._force_terminal, con._color_system) == before


def test_cli_color_flags_do_not_break_later_output_capture(runner, monkeypatch, tmp_path):
    """Regression guard for full-suite ordering: a forced-color invocation must not
    leave the shared Rich console writing outside the next CliRunner capture."""
    import pdd.cli as package_cli
    from pdd.core import utils as core_utils

    home_dir = tmp_path / "home"
    home_dir.mkdir()
    rc_path = home_dir / ".bashrc"

    monkeypatch.setattr(core_cli_module, "auto_update", lambda: None)
    monkeypatch.setattr(core_utils, "get_current_shell", lambda: "bash")
    monkeypatch.setattr(core_utils, "get_shell_rc_path", lambda _shell: str(rc_path))
    monkeypatch.delenv("PDD_SUPPRESS_SETUP_REMINDER", raising=False)

    with _restore_shared_console_color():
        first = runner.invoke(cli_command, ["--color", "--list-contexts"])
        assert first.exit_code == 0

        with patch("pdd.core.utils.Path.home", return_value=home_dir):
            with runner.isolated_filesystem():
                second = runner.invoke(package_cli.cli, [])

    assert second.exit_code == 0
    assert "Complete onboarding with `pdd setup`" in second.output

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

def test_strip_ansi_codes_removes_osc_sequences():
    # OSC title set + BEL terminator
    text = "pre\x1b]0;mytitle\x07post"
    assert _strip_ansi_codes(text) == "prepost"

def test_strip_ansi_codes_removes_cursor_sequences():
    # CSI cursor movement and erase-in-line
    text = "a\x1b[2Kb\x1b[1Dc"
    assert _strip_ansi_codes(text) == "abc"

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
    assert PDD_FULL_TAGLINE in output
    assert PDD_POSITIONING in output
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
    """Intentional SystemExit(1) from a command is not reported as an error (issue #593)."""
    def exit_cmd(): sys.exit(1)
    cmd = click.Command("exit", callback=exit_cmd)
    group = PDDCLI(commands={"exit": cmd})
    runner = CliRunner()
    result = runner.invoke(group, ["exit"])
    assert result.exit_code == 1
    # PDDCLI catches SystemExit and calls ctx.exit(1) without calling handle_error
    mock_handle_error.assert_not_called()

@patch('pdd.core.cli.handle_error')
def test_pddcli_invoke_re_raises_click_exit_without_handle_error(mock_handle_error):
    """click.exceptions.Exit(1) is intentional failure, not an unexpected error."""
    def fail_cmd(): raise click.exceptions.Exit(1)
    cmd = click.Command("fail", callback=fail_cmd)
    group = PDDCLI(commands={"fail": cmd})
    runner = CliRunner()
    result = runner.invoke(group, ["fail"])
    assert result.exit_code == 1
    mock_handle_error.assert_not_called()

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
    ctx.exit = Mock()
    with ctx:
        process_commands(results=[None])
    printed_text = " ".join(str(call.args[0]) for call in mock_print.call_args_list)
    assert "Command completed" in printed_text
    ctx.exit.assert_not_called()

@patch('pdd.core.cli.console.print')
@patch('pdd.core.cli._write_core_dump')
def test_process_commands_failed_normalized_result_exits_nonzero(mock_write_dump, mock_print):
    ctx = click.Context(cli_command)
    ctx.obj = {"quiet": False, "core_dump": False}
    ctx.invoked_subcommands = ["detect"]
    ctx.exit = Mock()
    with ctx:
        process_commands(results=[None])
    printed_text = " ".join(str(call.args[0]) for call in mock_print.call_args_list)
    assert "Command failed" in printed_text
    ctx.exit.assert_called_with(1)

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

# ---------------------------------------------------------------------------
# Issue #1634: summary line format and apply_color_preference edge cases
# ---------------------------------------------------------------------------

def test_cli_summary_step_line_has_glyph_and_step_substring():
    """EPIC #1540 — the execution summary line for a successful step must contain
    both the shared cli_status SUCCESS glyph *and* the 'Step N (cmd):[/info] Cost:'
    substring in the same captured output, proving they coexist rather than one
    replacing the other."""
    from pdd.cli_status import GLYPHS, Status

    success_glyph = GLYPHS[Status.SUCCESS]
    lines = _capture_summary(['generate'], [('code', 0.05, 'model-X')])
    summary = "\n".join(lines)

    # Both the glyph (within its semantic markup) and the step cost label must appear.
    assert f"[success]{success_glyph}[/success]" in summary
    assert "Step 1 (generate):[/info] Cost:" in summary


def test_cli_summary_failure_line_has_glyph_and_step_info():
    """A failed step (None result) shows the FAILURE glyph AND 'Step N (cmd)'
    in the same output — glyph prefix and step label coexist on failure too."""
    from pdd.cli_status import GLYPHS, Status

    failure_glyph = GLYPHS[Status.FAILURE]
    lines = _capture_summary(['generate'], [None])
    summary = "\n".join(lines)

    assert f"[error]{failure_glyph}[/error]" in summary
    assert "Step 1 (generate)" in summary


def test_apply_color_preference_none_is_noop(monkeypatch):
    """apply_color_preference(None) must leave the environment and shared console
    color state exactly as it found them — it is the auto-detect path and calling
    it without prior flags must be a no-op (EPIC #1540, workstream 3)."""
    import pdd.core.errors as errors

    # Ensure a clean slate: neither flag is set.
    monkeypatch.delenv("NO_COLOR", raising=False)
    monkeypatch.delenv("FORCE_COLOR", raising=False)

    # Snapshot the shared console's color attributes before the call.
    con = errors.console
    before_no_color = con.no_color
    before_force_terminal = con._force_terminal

    errors.apply_color_preference(None)

    # Environment must be unchanged.
    assert "NO_COLOR" not in os.environ
    assert "FORCE_COLOR" not in os.environ
    # Shared console must be unchanged.
    assert con.no_color == before_no_color
    assert con._force_terminal == before_force_terminal


if __name__ == "__main__":
    import pytest
    sys.exit(pytest.main([__file__]))
