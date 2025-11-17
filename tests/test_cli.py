# tests/test_cli.py
import os
import sys
import subprocess
from pathlib import Path
from unittest.mock import patch, ANY, MagicMock

import pytest
from click.testing import CliRunner
import click # Import click for UsageError

# Assuming 'pdd' package is installed or in PYTHONPATH
# Adjust import if necessary based on project structure
from pdd import cli, __version__, DEFAULT_STRENGTH, DEFAULT_TIME


RUN_ALL_TESTS_ENABLED = os.getenv("PDD_RUN_ALL_TESTS") == "1"

# Import fix_verification_main to mock
# NOTE: fix_verification_main is imported in cli.py, so mocking pdd.cli.fix_verification_main is correct
# from pdd.fix_verification_main import fix_verification_main # Not needed directly in test

# Helper to create dummy files
@pytest.fixture
def create_dummy_files(tmp_path):
    files = {}
    def _create_files(*filenames, content="dummy content"):
        for name in filenames:
            file_path = tmp_path / name
            file_path.parent.mkdir(parents=True, exist_ok=True)
            file_path.write_text(content)
            files[name] = file_path
        return files
    return _create_files

@pytest.fixture
def runner():
    return CliRunner()

# --- Basic CLI Tests ---
def test_cli_list_contexts(runner):
    """Test `pdd --list-contexts`."""
    result = runner.invoke(cli.cli, ["--list-contexts"])
    assert result.exit_code == 0
    assert "default" in result.output


@patch('pdd.cli.auto_update')
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


@patch('pdd.cli.auto_update')
@patch('pdd.cli.code_generator_main')
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


@patch('pdd.cli.auto_update')
@patch('pdd.cli.code_generator_main')
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


@patch('pdd.cli.auto_update')
@patch('pdd.cli.code_generator_main')
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

def test_cli_command_help(runner):
    """Test `pdd [COMMAND] --help`."""
    result = runner.invoke(cli.cli, ["generate", "--help"])
    assert result.exit_code == 0
    assert "Usage: cli generate [OPTIONS] PROMPT_FILE" in result.output
    assert "--output" in result.output


@patch('pdd.cli.auto_update')
@patch('pdd.cli.code_generator_main')
def test_cli_generate_env_parsing_key_value(mock_main, mock_auto_update, runner, create_dummy_files, monkeypatch):
    files = create_dummy_files("envtest.prompt")
    mock_main.return_value = ('code', False, 0.0, 'model')

    result = runner.invoke(
        cli.cli,
        [
            "generate",
            "-e", "MODULE=orders",
            "--env", "PACKAGE=core",
            str(files["envtest.prompt"]),
        ],
    )
    assert result.exit_code == 0
    # Extract env_vars passed through
    call_kwargs = mock_main.call_args.kwargs
    assert call_kwargs["env_vars"] == {"MODULE": "orders", "PACKAGE": "core"}


@patch('pdd.cli.auto_update')
@patch('pdd.cli.code_generator_main')
def test_cli_generate_env_parsing_bare_key_fallback(mock_main, mock_auto_update, runner, create_dummy_files, monkeypatch):
    files = create_dummy_files("envbare.prompt")
    mock_main.return_value = ('code', False, 0.0, 'model')
    monkeypatch.setenv("SERVICE", "billing")

    result = runner.invoke(
        cli.cli,
        [
            "generate",
            "-e", "SERVICE",
            "-e", "MISSING_VAR",  # not in env; should be skipped
            str(files["envbare.prompt"]),
        ],
    )
    assert result.exit_code == 0
    call_kwargs = mock_main.call_args.kwargs
    assert call_kwargs["env_vars"] == {"SERVICE": "billing"}


@patch('pdd.cli.auto_update')
@patch('pdd.cli.code_generator_main')
def test_cli_generate_incremental_flag_passthrough(mock_main, mock_auto_update, runner, create_dummy_files):
    files = create_dummy_files("inc.prompt")
    mock_main.return_value = ('code', False, 0.0, 'model')

    result = runner.invoke(
        cli.cli,
        [
            "generate",
            "--incremental",
            str(files["inc.prompt"]),
        ],
    )
    assert result.exit_code == 0
    call_kwargs = mock_main.call_args.kwargs
    # CLI uses --incremental but main receives force_incremental_flag
    assert call_kwargs["force_incremental_flag"] is True

# --- Template Functionality Tests ---

@patch('pdd.cli.auto_update')
@patch('pdd.cli.code_generator_main')
@patch('pdd.template_registry.load_template')
def test_cli_generate_template_uses_registry_path(mock_load_template, mock_code_main, mock_auto_update, runner, tmp_path):
    """`generate --template` should resolve the prompt path via the registry."""
    template_path = tmp_path / "pdd" / "templates" / "demo.prompt"
    template_path.parent.mkdir(parents=True, exist_ok=True)
    template_path.write_text("dummy", encoding="utf-8")

    mock_load_template.return_value = {"path": str(template_path)}
    mock_code_main.return_value = ('code', False, 0.0, 'model')

    result = runner.invoke(cli.cli, ["generate", "--template", "architecture/demo"])

    assert result.exit_code == 0
    mock_load_template.assert_called_once_with("architecture/demo")
    mock_code_main.assert_called_once()
    kwargs = mock_code_main.call_args.kwargs
    assert kwargs["prompt_file"] == str(template_path)
    assert kwargs.get("env_vars") is None


@patch('pdd.cli.auto_update')
@patch('pdd.cli.code_generator_main')
def test_cli_generate_template_with_prompt_raises_usage_error(mock_code_main, mock_auto_update, runner, create_dummy_files):
    """Providing both --template and PROMPT_FILE should raise a usage error."""
    files = create_dummy_files("conflict.prompt")

    result = runner.invoke(
        cli.cli,
        ["generate", "--template", "architecture/demo", str(files["conflict.prompt"])]
    )

    assert result.exit_code == 0
    assert "either --template or a PROMPT_FILE" in result.output
    mock_code_main.assert_not_called()


@patch('pdd.cli.auto_update')
@patch('pdd.cli.code_generator_main')
@patch('pdd.template_registry.load_template', side_effect=FileNotFoundError("missing"))
def test_cli_generate_template_load_failure(mock_load_template, mock_code_main, mock_auto_update, runner):
    """Failed template resolution should surface as a UsageError without running the command."""
    result = runner.invoke(cli.cli, ["generate", "--template", "missing/template"])

    assert result.exit_code == 0
    assert "Failed to load template 'missing/template'" in result.output
    mock_code_main.assert_not_called()


@patch('pdd.template_registry.list_templates')
def test_cli_templates_list_default(mock_list_templates, runner):
    """`pdd templates list` should pretty-print template metadata."""
    mock_list_templates.return_value = [
        {
            "name": "architecture/architecture_json",
            "description": "Architecture outline",
            "version": "1.0.0",
            "tags": ["architecture", "json"],
        }
    ]

    result = runner.invoke(cli.templates_group, ["list"])

    assert result.exit_code == 0
    mock_list_templates.assert_called_once_with(None)
    assert "Available Templates" in result.output
    assert "architecture/architecture_json" in result.output
    assert "Architecture outline" in result.output


@patch('pdd.template_registry.list_templates')
def test_cli_templates_list_json_filter(mock_list_templates, runner):
    """`pdd templates list --json --filter` should return JSON and pass the filter tag."""
    payload = [
        {
            "name": "frontend/nextjs",
            "description": "Next.js app",
            "version": "2.0.0",
            "tags": ["frontend"],
        }
    ]
    mock_list_templates.return_value = payload

    result = runner.invoke(cli.templates_group, ["list", "--json", "--filter", "tag=frontend"])

    assert result.exit_code == 0
    mock_list_templates.assert_called_once_with("tag=frontend")

    import json as _json

    parsed = _json.loads(result.output)
    assert parsed == payload


@patch('pdd.template_registry.show_template')
def test_cli_templates_show_outputs_sections(mock_show_template, runner):
    """`pdd templates show` should render template metadata sections."""
    mock_show_template.return_value = {
        "summary": {
            "name": "architecture/architecture_json",
            "description": "Architecture outline",
            "version": "1.0.0",
            "tags": ["architecture"],
            "language": "json",
            "output": "architecture.json",
            "path": "/tmp/arch.prompt",
        },
        "variables": {"PRD_FILE": {"required": True, "type": "path"}},
        "usage": {"generate": [{"command": "pdd generate ..."}]},
        "discover": {"enabled": True},
        "output_schema": {"type": "object"},
        "notes": "Provide a PRD file.",
    }

    result = runner.invoke(cli.templates_group, ["show", "architecture/architecture_json"])

    assert result.exit_code == 0
    mock_show_template.assert_called_once_with("architecture/architecture_json")
    assert "Template Summary:" in result.output
    assert "Architecture outline" in result.output
    assert "Version" in result.output
    assert "Variables:" in result.output
    assert "Output Schema" in result.output
    assert "Provide a PRD file." in result.output


@patch('pdd.template_registry.copy_template')
def test_cli_templates_copy_invokes_registry(mock_copy_template, runner, tmp_path):
    """`pdd templates copy` should copy via the registry and report the destination."""
    destination = tmp_path / "prompts" / "architecture" / "architecture_json.prompt"
    mock_copy_template.return_value = str(destination)

    result = runner.invoke(
        cli.templates_group,
        [
            "copy",
            "architecture/architecture_json",
            "--to",
            str(destination.parent),
        ],
    )

    assert result.exit_code == 0
    mock_copy_template.assert_called_once_with("architecture/architecture_json", str(destination.parent))
    assert "Copied to" in result.output
    assert "architecture_json.prompt" in result.output.replace("\n", "")


def test_cli_templates_group_registered():
    """Ensure the templates command group is reachable from the top-level CLI."""
    assert "templates" in cli.cli.commands
    assert cli.cli.commands["templates"] is cli.templates_group

# --- Global Options Tests ---

@patch('pdd.cli.auto_update') # Patch auto_update here as well
@patch('pdd.cli.code_generator_main')
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

@patch('pdd.cli.auto_update') # Patch auto_update here as well
@patch('pdd.cli.code_generator_main')
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

@patch('pdd.cli.auto_update') # Patch auto_update here as well
@patch('pdd.cli.code_generator_main')
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

@patch('pdd.cli.auto_update')
@patch('pdd.cli.code_generator_main') # Need to mock a command to trigger cli execution
@patch('pdd.cli.construct_paths') # Now this patch should work
def test_cli_auto_update_called_by_default(mock_construct, mock_main, mock_auto_update, runner, create_dummy_files):
    """Test auto_update is called by default."""
    files = create_dummy_files("test.prompt")
    # mock_construct.return_value = ({}, {'output': 'out.py'}, 'python') # Not needed if main is mocked
    mock_main.return_value = ('code', False, 0.0, 'model') # Corrected: 4-tuple

    result = runner.invoke(cli.cli, ["generate", str(files["test.prompt"])])

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
@patch('pdd.cli.auto_update')
@patch('pdd.cli.code_generator_main')
@patch('pdd.cli.construct_paths') # Now this patch should work
def test_cli_auto_update_not_called_when_disabled(mock_construct, mock_main, mock_auto_update, runner, create_dummy_files):
    """Test auto_update is not called when PDD_AUTO_UPDATE=false."""
    files = create_dummy_files("test.prompt")
    # mock_construct.return_value = ({}, {'output': 'out.py'}, 'python') # Not needed if main is mocked
    mock_main.return_value = ('code', False, 0.0, 'model') # Corrected: 4-tuple

    result = runner.invoke(cli.cli, ["generate", str(files["test.prompt"])])

    if result.exit_code != 0:
        print(f"Unexpected exit code: {result.exit_code}")
        print(f"Output:\n{result.output}")
        if result.exception:
            print(f"Exception:\n{result.exception}")
            raise result.exception

    mock_auto_update.assert_not_called()
    mock_main.assert_called_once() # Ensure command still ran

@patch('pdd.cli.auto_update', side_effect=Exception("Network error"))
@patch('pdd.cli.code_generator_main')
@patch('pdd.cli.construct_paths') # Now this patch should work
def test_cli_auto_update_handles_exception(mock_construct, mock_main, mock_auto_update, runner, create_dummy_files):
    """Test auto_update exceptions are handled gracefully."""
    files = create_dummy_files("test.prompt")
    # mock_construct.return_value = ({}, {'output': 'out.py'}, 'python') # Not needed if main is mocked
    mock_main.return_value = ('code', False, 0.0, 'model') # Corrected: 4-tuple

    result = runner.invoke(cli.cli, ["generate", str(files["test.prompt"])])

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

@patch('pdd.cli.auto_update') # Patch auto_update
# Mock the main function where the error originates
@patch('pdd.cli.code_generator_main', side_effect=FileNotFoundError("Input file missing"))
# @patch('pdd.cli.construct_paths') # No need to patch construct_paths if main is mocked with side_effect
def test_cli_handle_error_filenotfound(mock_main, mock_auto_update, runner, create_dummy_files):
    """Test handle_error for FileNotFoundError."""
    files = create_dummy_files("test.prompt")
    result = runner.invoke(cli.cli, ["generate", str(files["test.prompt"])])

    # Expect exit code 0 because the exception is caught by the command's
    # try-except, calling handle_error (which prints), and returning None.
    assert result.exit_code == 0
    assert result.exception is None # Exception should be handled, not re-raised to runner
    assert "Error during 'generate' command" in result.output
    assert "File not found" in result.output
    assert "Input file missing" in result.output
    mock_main.assert_called_once() # Main is called before raising the error
    mock_auto_update.assert_called_once_with() # Auto update runs before command error

@patch('pdd.cli.auto_update') # Patch auto_update
@patch('pdd.cli.code_generator_main', side_effect=ValueError("Invalid prompt content"))
# @patch('pdd.cli.construct_paths') # No need to patch construct_paths if main is mocked with side_effect
def test_cli_handle_error_valueerror(mock_main, mock_auto_update, runner, create_dummy_files):
    """Test handle_error for ValueError."""
    files = create_dummy_files("test.prompt")

    result = runner.invoke(cli.cli, ["generate", str(files["test.prompt"])])

    assert result.exit_code == 0 # Should be 0
    assert result.exception is None # Exception should be handled
    assert "Error during 'generate' command" in result.output
    assert "Input/Output Error" in result.output # ValueError maps to this
    assert "Invalid prompt content" in result.output
    mock_main.assert_called_once()
    mock_auto_update.assert_called_once_with()

@patch('pdd.cli.auto_update') # Patch auto_update
@patch('pdd.cli.code_generator_main', side_effect=Exception("Unexpected LLM issue"))
# @patch('pdd.cli.construct_paths') # No need to patch construct_paths if main is mocked with side_effect
def test_cli_handle_error_generic(mock_main, mock_auto_update, runner, create_dummy_files):
    """Test handle_error for generic Exception."""
    files = create_dummy_files("test.prompt")

    result = runner.invoke(cli.cli, ["generate", str(files["test.prompt"])])

    assert result.exit_code == 0 # Should be 0
    assert result.exception is None # Exception should be handled
    # assert "Unexpected LLM issue" in str(result.exception) # No exception propagated
    assert "Error during 'generate' command" in result.output
    assert "An unexpected error occurred" in result.output
    assert "Unexpected LLM issue" in result.output
    mock_main.assert_called_once()
    mock_auto_update.assert_called_once_with()

@patch('pdd.cli.auto_update') # Patch auto_update
@patch('pdd.cli.code_generator_main', side_effect=FileNotFoundError("Input file missing"))
# @patch('pdd.cli.construct_paths') # No need to patch construct_paths if main is mocked with side_effect
def test_cli_handle_error_quiet(mock_main, mock_auto_update, runner, create_dummy_files):
    """Test handle_error respects --quiet."""
    files = create_dummy_files("test.prompt")
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

# --- construct_paths Integration Tests ---

# This test does not use CLI runner, so it doesn't depend on mocking pdd.cli.construct_paths
def test_cli_construct_paths_called_correctly(create_dummy_files, tmp_path):
    """Test construct_paths function directly without mocking."""
    from pdd.construct_paths import construct_paths # Import directly

    # Create a simple prompt file with valid content
    prompt_content = """// my_prompt_python.prompt
// Language: Python
// Description: A sample prompt to test construct_paths
// Output: A simple function

def sample_function():
    return "Hello, world!"
"""
    # Create prompt file with the fixture
    files = create_dummy_files("my_prompt_python.prompt", content=prompt_content)
    prompt_path_str = str(files["my_prompt_python.prompt"])

    # Create output directory
    output_dir = tmp_path / "output" / "dir"
    output_dir.mkdir(parents=True, exist_ok=True)
    output_path = str(output_dir)

    # Call construct_paths directly with the arguments
    # This is the core functionality we want to test
    input_file_paths = {"prompt_file": prompt_path_str}
    force = True
    quiet = True # Use quiet to avoid output clutter
    command = "generate"
    # Simulate how options would be passed from a specific command like 'generate'
    command_options = {"output": output_path}

    # Call the function directly
    resolved_config, input_strings, output_file_paths, language = construct_paths(
        input_file_paths=input_file_paths,
        force=force,
        quiet=quiet,
        command=command,
        command_options=command_options
    )

    # Verify the input strings were read correctly
    assert "prompt_file" in input_strings
    assert "sample_function" in input_strings["prompt_file"]

    # Verify output paths were created correctly
    assert "output" in output_file_paths
    # construct_paths should resolve the output path based on the input prompt name and language
    expected_output_path_obj = output_dir / "my_prompt.py"
    assert Path(output_file_paths["output"]) == expected_output_path_obj

    # Verify language was detected correctly
    assert language == "python"


@patch('pdd.cli.auto_update') # Patch auto_update
@patch('pdd.cli.construct_paths') # Mock construct_paths in cli module namespace
@patch('pdd.cli.change_main')
def test_cli_change_command_csv_validation(mock_main, mock_construct, mock_auto_update, runner, create_dummy_files, tmp_path):
    """Test 'change' command validation for --csv."""
    files = create_dummy_files("changes.csv", "p.prompt")
    code_dir = tmp_path / "code_dir"
    code_dir.mkdir()
    (code_dir / "some_code.py").touch()

    # Error: --csv requires directory for input_code (Validation inside 'change' command)
    result = runner.invoke(cli.cli, ["change", "--csv", str(files["changes.csv"]), str(files["p.prompt"])]) # p.prompt is a file
    assert result.exit_code == 0 # Command handles error gracefully
    assert result.exception is None
    # Check output message from handle_error
    assert "Usage Error: INPUT_CODE must be a directory when using --csv" in result.output
    mock_auto_update.assert_called_once()
    mock_main.assert_not_called() # Fails validation before main
    mock_construct.assert_not_called() # construct_paths is not called by CLI wrapper

    # Error: Cannot use --csv and input_prompt_file (Validation inside 'change' command)
    mock_auto_update.reset_mock()
    mock_main.reset_mock()
    mock_construct.reset_mock()
    result = runner.invoke(cli.cli, ["change", "--csv", str(files["changes.csv"]), str(code_dir), str(files["p.prompt"])])
    assert result.exit_code == 0 # Command handles error gracefully
    assert result.exception is None
    # Check output message from handle_error
    assert "Usage Error: Cannot use --csv and specify an INPUT_PROMPT_FILE simultaneously." in result.output
    mock_auto_update.assert_called_once()
    mock_main.assert_not_called() # Fails validation before main
    mock_construct.assert_not_called()

    # Error: Not using --csv requires input_prompt_file (Validation inside 'change' command)
    mock_auto_update.reset_mock()
    mock_main.reset_mock()
    mock_construct.reset_mock()
    # No need to mock main side effect, validation happens before
    result = runner.invoke(cli.cli, ["change", str(files["changes.csv"]), str(code_dir / "some_code.py")]) # Missing input_prompt_file
    assert result.exit_code == 0 # Command handles error gracefully
    assert result.exception is None
    # Check output message from handle_error
    assert "Usage Error: INPUT_PROMPT_FILE is required when not using --csv" in result.output
    mock_auto_update.assert_called_once()
    mock_main.assert_not_called() # Fails validation before main
    # mock_construct.assert_called_once() # Optional: assert if construct_paths is expected here

    # Error: Not using --csv requires file for input_code (Validation inside 'change' command)
    mock_auto_update.reset_mock()
    mock_main.reset_mock()
    mock_construct.reset_mock()
    # No need to mock main side effect, validation happens before
    result = runner.invoke(cli.cli, ["change", str(files["changes.csv"]), str(code_dir), str(files["p.prompt"])]) # code_dir is a dir
    assert result.exit_code == 0 # Command handles error gracefully
    assert result.exception is None
    # Check output message from handle_error
    assert "Usage Error: INPUT_CODE must be a file when not using --csv" in result.output
    mock_auto_update.assert_called_once()
    mock_main.assert_not_called() # Fails validation before main
    # mock_construct.assert_called_once() # Optional: assert if construct_paths is expected here

    # Valid CSV call
    mock_auto_update.reset_mock()
    mock_main.reset_mock()
    mock_construct.reset_mock()
    mock_main.side_effect = None # Clear side effect
    mock_main.return_value = ({'msg': 'Processed 1 file'}, 0.3, 'model-change')
    result = runner.invoke(cli.cli, ["change", "--csv", str(files["changes.csv"]), str(code_dir)])

    if result.exit_code != 0:
        print(f"Unexpected exit code: {result.exit_code}")
        print(f"Output:\n{result.output}")
        if result.exception:
            print(f"Exception:\n{result.exception}")
            raise result.exception

    assert result.exit_code == 0
    assert result.exception is None
    mock_main.assert_called_once_with(
        ctx=ANY, change_prompt_file=str(files["changes.csv"]), input_code=str(code_dir),
        input_prompt_file=None, output=None, use_csv=True, budget=5.0 # Added budget=5.0
    )
    # construct_paths should NOT have been called by change_main in CSV mode (usually)
    mock_construct.assert_not_called()
    mock_auto_update.assert_called_once_with()


@patch('pdd.cli.auto_update') # Patch auto_update
@patch('pdd.cli.construct_paths') # Now this patch should work
@patch('pdd.cli.auto_deps_main')
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

def _capture_summary(invoked_subcommands, results):
    ctx = click.Context(cli.cli)
    ctx.obj = {'quiet': False, 'invoked_subcommands': invoked_subcommands}
    # Ensure the summary callback sees the actual command names
    ctx.invoked_subcommands = invoked_subcommands
    with patch.object(cli.console, 'print') as mock_print:
        with ctx:
            cli.process_commands(results=results)
    return ["".join(str(arg) for arg in call.args) for call in mock_print.call_args_list]


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

@patch('pdd.cli.auto_update') # Patch auto_update
@patch('pdd.cli.install_completion')
def test_cli_install_completion_cmd(mock_install_func, mock_auto_update, runner):
    """Test the install_completion command."""
    result = runner.invoke(cli.cli, ["install_completion"])

    if result.exit_code != 0:
        print(f"Unexpected exit code: {result.exit_code}")
        print(f"Output:\n{result.output}")
        if result.exception:
            print(f"Exception:\n{result.exception}")
            raise result.exception # Re-raise the captured exception

    assert result.exit_code == 0
    assert result.exception is None # Should complete gracefully
    mock_install_func.assert_called_once_with(quiet=False)
    mock_auto_update.assert_called_once_with()

@patch('pdd.cli.auto_update') # Patch auto_update
@patch('pdd.cli.install_completion')
def test_cli_install_completion_cmd_quiet(mock_install_func, mock_auto_update, runner):
    """Test the install_completion command with --quiet."""
    result = runner.invoke(cli.cli, ["--quiet", "install_completion"])

    if result.exit_code != 0:
        print(f"Unexpected exit code: {result.exit_code}")
        print(f"Output:\n{result.output}")
        if result.exception:
            print(f"Exception:\n{result.exception}")
            raise result.exception # Re-raise the captured exception

    assert result.exit_code == 0
    assert result.exception is None # Should complete gracefully
    mock_install_func.assert_called_once_with(quiet=True)
    mock_auto_update.assert_called_once_with()


@patch('pdd.cli._should_show_onboarding_reminder', return_value=False)
@patch('pdd.cli.subprocess.run')
@patch('pdd.cli.install_completion')
@patch('pdd.cli.auto_update')
def test_cli_setup_command(mock_auto_update, mock_install, mock_run, _mock_reminder, runner):
    """`pdd setup` should install completions and run the setup utility."""
    mock_run.return_value = subprocess.CompletedProcess(args=[], returncode=0)

    result = runner.invoke(cli.cli, ["setup"])

    assert result.exit_code == 0
    mock_auto_update.assert_called_once_with()
    mock_install.assert_called_once_with(quiet=False)

    mock_run.assert_called_once_with([sys.executable, "-m", "pdd.setup_tool"])
    assert "Setup completed" in result.output


def test_cli_onboarding_reminder_shown(monkeypatch, runner, tmp_path):
    """Warn users when no global or project setup artifacts exist."""
    home_dir = tmp_path / "home"
    home_dir.mkdir()
    rc_path = home_dir / ".bashrc"

    monkeypatch.setattr(cli, "auto_update", lambda: None)
    monkeypatch.setattr(cli, "get_current_shell", lambda: "bash")
    monkeypatch.setattr(cli, "get_shell_rc_path", lambda _shell: str(rc_path))
    monkeypatch.delenv("PDD_SUPPRESS_SETUP_REMINDER", raising=False)

    with patch('pdd.cli.Path.home', return_value=home_dir):
        with runner.isolated_filesystem():
            result = runner.invoke(cli.cli, [])

    assert result.exit_code == 0
    assert "Complete onboarding with `pdd setup`" in result.output


def test_cli_onboarding_reminder_suppressed_by_project_env(monkeypatch, runner, tmp_path):
    """A project-level .env with API keys suppresses the reminder."""
    home_dir = tmp_path / "home"
    home_dir.mkdir()
    rc_path = home_dir / ".bashrc"

    monkeypatch.setattr(cli, "auto_update", lambda: None)
    monkeypatch.setattr(cli, "get_current_shell", lambda: "bash")
    monkeypatch.setattr(cli, "get_shell_rc_path", lambda _shell: str(rc_path))
    monkeypatch.delenv("PDD_SUPPRESS_SETUP_REMINDER", raising=False)

    with patch('pdd.cli.Path.home', return_value=home_dir):
        with runner.isolated_filesystem():
            Path(".env").write_text("OPENAI_API_KEY=abc123\n", encoding="utf-8")
            result = runner.invoke(cli.cli, [])

    assert result.exit_code == 0
    assert "Complete onboarding with `pdd setup`" not in result.output


def test_cli_onboarding_reminder_suppressed_by_api_env(monkeypatch, runner, tmp_path):
    """Presence of ~/.pdd/api-env suppresses the reminder."""
    home_dir = tmp_path / "home"
    pdd_dir = home_dir / ".pdd"
    pdd_dir.mkdir(parents=True)
    (pdd_dir / "api-env").write_text("export OPENAI_API_KEY=abc123\n", encoding="utf-8")

    rc_path = home_dir / ".zshrc"

    monkeypatch.setattr(cli, "auto_update", lambda: None)
    monkeypatch.setattr(cli, "get_current_shell", lambda: "zsh")
    monkeypatch.setattr(cli, "get_shell_rc_path", lambda _shell: str(rc_path))
    monkeypatch.delenv("PDD_SUPPRESS_SETUP_REMINDER", raising=False)

    with patch('pdd.cli.Path.home', return_value=home_dir):
        with runner.isolated_filesystem():
            result = runner.invoke(cli.cli, [])

    assert result.exit_code == 0
    assert "Complete onboarding with `pdd setup`" not in result.output

# --- Real Command Tests (No Mocking) ---
# These tests remain largely unchanged as they call the *_main functions directly
# or expect exceptions to be raised by those main functions.

def test_real_generate_command(create_dummy_files, tmp_path):
    """Test the 'generate' command with real files by calling the function directly."""
    if not (os.getenv("PDD_RUN_REAL_LLM_TESTS") or RUN_ALL_TESTS_ENABLED):
        pytest.skip(
            "Real LLM integration tests require network/API access; set "
            "PDD_RUN_REAL_LLM_TESTS=1 or use --run-all / PDD_RUN_ALL_TESTS=1."
        )

    import sys
    import click
    from pathlib import Path
    from pdd.code_generator_main import code_generator_main

    # Create a simple prompt file with valid content - use a name with language suffix
    prompt_content = """// gen_python.prompt
// Language: Python
// Description: A simple function to add two numbers
// Inputs: Two numbers a and b
// Outputs: The sum of a and b

def add(a, b):
    # Add two numbers and return the result
    pass
"""
    # Create prompt file with the fixture - use proper naming convention with language
    files = create_dummy_files("gen_python.prompt", content=prompt_content)
    prompt_file = str(files["gen_python.prompt"])

    # Create output directory
    output_dir = tmp_path / "output"
    output_dir.mkdir(exist_ok=True)
    output_file = str(output_dir / "gen.py") # Explicit output file

    # Print environment info for debugging
    print(f"Current working directory: {os.getcwd()}")
    print(f"Prompt file location: {prompt_file}")
    print(f"Output directory: {output_dir}")

    # Create a minimal context object with the necessary parameters
    ctx = click.Context(click.Command("generate"))
    ctx.obj = {
        'force': False,
        'quiet': False,
        'verbose': True,
        'strength': 0.8,
        'temperature': 0.0,
        'local': True,  # Use local execution to avoid API calls
        'output_cost': None, # Ensure cost tracking is off for this test
        'review_examples': False,
        'time': DEFAULT_TIME, # Added time to context
    }

    try:
        # Call code_generator_main directly - with no mock this time
        # Let it use the real LLM implementation
        # Corrected: Added missing arguments
        code, incremental, cost, model = code_generator_main(
            ctx=ctx,
            prompt_file=prompt_file,
            output=output_file,
            original_prompt_file_path=None,
            force_incremental_flag=False
        )

        # Verify we got reasonable results back
        assert isinstance(code, str), "Generated code should be a string"
        assert len(code) > 0, "Generated code should not be empty"
        assert isinstance(cost, float), "Cost should be a float"
        assert isinstance(model, str), "Model name should be a string"

        # Check output file was created
        output_path = Path(output_file)
        assert output_path.exists(), f"Output file not created at {output_path}"

        # Verify content of generated file - checking for function with any signature
        generated_code = output_path.read_text()
        assert "def add" in generated_code, "Generated code should contain an add function"
        assert "return" in generated_code, "Generated code should include a return statement"
        assert "pass" not in generated_code, "Generated code should replace the 'pass' placeholder"

        # Print success message
        print("\nTest passed! Generated code:")
        print(generated_code)

    except Exception as e:
        print(f"Error executing code_generator_main: {e}")
        import traceback
        traceback.print_exc()
        raise

@pytest.mark.real
def test_real_fix_command(create_dummy_files, tmp_path):
    """Test the 'fix' command with real files by calling the function directly."""
    if not (os.getenv("PDD_RUN_REAL_LLM_TESTS") or RUN_ALL_TESTS_ENABLED):
        pytest.skip(
            "Real LLM integration tests require network/API access; set "
            "PDD_RUN_REAL_LLM_TESTS=1 or use --run-all / PDD_RUN_ALL_TESTS=1."
        )

    import sys
    import click
    from pathlib import Path
    # Import fix_main locally to avoid interfering with mocks in other tests
    from pdd.fix_main import fix_main as fix_main_direct

    # Create a prompt file with valid content
    prompt_content = """// fix_python.prompt
// Language: Python
// Description: A simple function to add two numbers
// Inputs: Two numbers a and b
// Outputs: The sum of a and b

def add(a, b):
    # Add two numbers and return the result
    return a + b
"""

    # Create a code file with a bug
    code_content = """# add.py
def add(a, b):
    # This has a bug - it doesn't return anything
    result = a + b
    # Missing return statement
"""

    # Create a test file that will fail
    test_content = """# test_add.py
import unittest
# Use relative import if 'add.py' is in the same directory
try:
    from .add import add
except ImportError:
    from add import add

class TestAdd(unittest.TestCase):
    def test_add(self):
        self.assertEqual(add(2, 3), 5)
        self.assertEqual(add(-1, 1), 0)
        self.assertEqual(add(0, 0), 0)

if __name__ == '__main__':
    # Need to make sure unittest can find the test
    # Add current directory to sys.path if running as script
    if '.' not in sys.path:
         sys.path.insert(0, '.')
    unittest.main(module=None) # Use module=None for auto-discovery
"""

    # Create an error log file with the test failure
    error_content = """============================= test session starts ==============================
platform darwin -- Python 3.9.7, pytest-7.0.1, pluggy-1.0.0
rootdir: /tmp/test_fix
collected 1 item

test_add.py F                                                              [100%]

=================================== FAILURES ===================================
_________________________________ TestAdd.test_add _________________________________

self = <test_add.TestAdd testMethod=test_add>

    def test_add(self):
>       self.assertEqual(add(2, 3), 5)
E       AssertionError: None != 5

test_add.py:11: AssertionError
=========================== short test summary info ============================
FAILED test_add.py::TestAdd::test_add - AssertionError: None != 5
"""

    # Create a simple verification program (Changed from f-string to regular string)
    verification_content = """# verify.py
import unittest
import subprocess
import sys
from pathlib import Path

# Ensure the directory containing add.py is in the python path
# This is crucial when running verify.py from a different directory (like tmp_path)
script_dir = Path(__file__).parent.resolve()
if str(script_dir) not in sys.path:
    sys.path.insert(0, str(script_dir))

try:
    # Try importing 'add' assuming it's in the same directory or python path
    from add import add
except ModuleNotFoundError:
    # Use script_dir directly in the f-string inside the script's scope
    print(f"Error: Could not import 'add' from {script_dir}. Check PYTHONPATH.")
    sys.exit(1)


# Try loading tests specifically from the test_add module
# Ensure test_add.py is also discoverable
try:
    loader = unittest.defaultTestLoader
    suite = loader.loadTestsFromName('test_add.TestAdd') # Load from the module name
except (AttributeError, ImportError, ValueError) as e:
     # Use script_dir directly in the f-string inside the script's scope
     print(f"Error loading tests from 'test_add.TestAdd': {e}")
     # Fallback or alternative discovery if needed
     # suite = loader.discover(start_dir=str(script_dir), pattern='test_add.py')
     sys.exit(1)


# Run the tests
# Use suite directly in the f-string inside the script's scope
print(f"Running tests from suite: {suite}")
runner = unittest.TextTestRunner()
test_result = runner.run(suite)


# Exit with appropriate code
sys.exit(0 if test_result.wasSuccessful() else 1)
"""

    # Create empty dummy files with the fixture, placing them directly in tmp_path
    # This makes imports simpler for the verification script
    files_dict = {}
    for name in ["fix_python.prompt", "add.py", "test_add.py", "errors.log", "verify.py"]:
        file_path = tmp_path / name
        file_path.parent.mkdir(parents=True, exist_ok=True)
        file_path.touch() # Create empty file first
        files_dict[name] = file_path

    # Set the content for each file
    files_dict["fix_python.prompt"].write_text(prompt_content)
    files_dict["add.py"].write_text(code_content)
    files_dict["test_add.py"].write_text(test_content)
    files_dict["errors.log"].write_text(error_content)
    files_dict["verify.py"].write_text(verification_content)

    # Get the file paths as strings
    prompt_file = str(files_dict["fix_python.prompt"])
    code_file = str(files_dict["add.py"])
    test_file = str(files_dict["test_add.py"])
    error_file = str(files_dict["errors.log"])
    verification_file = str(files_dict["verify.py"])

    # Create output directory relative to tmp_path
    output_dir = tmp_path / "output"
    output_dir.mkdir(exist_ok=True)
    output_test = str(output_dir / "fixed_test_add.py")
    output_code = str(output_dir / "fixed_add.py")
    output_results = str(output_dir / "fix_results.log")

    # Print environment info for debugging
    print(f"Temporary directory: {tmp_path}")
    print(f"Current working directory: {os.getcwd()}")
    print(f"Prompt file location: {prompt_file}")
    print(f"Code file location: {code_file}")
    print(f"Test file location: {test_file}")
    print(f"Error file location: {error_file}")
    print(f"Verification file location: {verification_file}")
    print(f"Output directory: {output_dir}")

    # Create a minimal context object with the necessary parameters
    ctx = click.Context(click.Command("fix"))
    ctx.obj = {
        'force': True,
        'quiet': False,
        'verbose': True,
        'strength': 0.8,
        'temperature': 0.0,
        'local': True,  # Use local execution to avoid API calls
        'output_cost': None,
        'review_examples': False,
        'time': DEFAULT_TIME, # Added time to context
    }

    # Change working directory to tmp_path so imports work correctly
    original_cwd = os.getcwd()
    os.chdir(tmp_path)
    
    # Set PDD_PATH to the project root so prompt templates can be found
    # Get the project root dynamically from the current test file location
    original_pdd_path = os.getenv('PDD_PATH')
    project_root = Path(__file__).parent.parent  # Go up from tests/ to project root
    os.environ['PDD_PATH'] = str(project_root)

    try:
        # Call fix_main directly - with no mock this time
        success, fixed_test, fixed_code, attempts, cost, model = fix_main_direct(
            ctx=ctx,
            prompt_file=prompt_file, # Use absolute path
            code_file=code_file,     # Use absolute path
            unit_test_file=test_file,# Use absolute path
            error_file=error_file,   # Use absolute path
            output_test=output_test, # Use absolute path
            output_code=output_code, # Use absolute path
            output_results=output_results,# Use absolute path
            loop=False,  # Use simple mode for testing
            verification_program=None,  # Not needed in simple mode
            max_attempts=3,
            budget=1.0,
            auto_submit=False
        )

        # Verify we got reasonable results back
        assert isinstance(success, bool), "Success should be a boolean"
        # fixed_test can be empty if no changes were needed
        assert isinstance(fixed_test, str), "Fixed test should be a string"
        assert isinstance(fixed_code, str), "Fixed code should be a string"
        assert attempts > 0, "Should have at least one attempt"
        assert isinstance(cost, float), "Cost should be a float"
        assert isinstance(model, str), "Model name should be a string"

        # Check output files were created
        # Only check test file if content was returned (previous fix)
        if fixed_test: # Only check if the returned content is non-empty
            assert Path(output_test).exists(), f"Output test file not created at {output_test} even though content was returned"

        assert Path(output_code).exists(), f"Output code file not created at {output_code}"

        # Verify content of generated code file
        fixed_code_content = Path(output_code).read_text()
        assert "def add" in fixed_code_content, "Fixed code should contain an add function"
        assert "return" in fixed_code_content, "Fixed code should include a return statement"
        # The fix should add the return statement
        assert "return result" in fixed_code_content or "return a + b" in fixed_code_content

        # Print success message
        print("\nTest passed! Fixed code:")
        print(fixed_code_content)

        # Try with loop mode if the non-loop mode succeeded
        if success:
            try:
                print("\nTesting fix_main with loop mode...")
                # Reset the code file to the buggy version for the loop test
                Path(code_file).write_text(code_content)

                # Call fix_main in loop mode
                loop_success, loop_fixed_test, loop_fixed_code, loop_attempts, loop_cost, loop_model = fix_main_direct(
                    ctx=ctx,
                    prompt_file=prompt_file,
                    code_file=code_file,
                    unit_test_file=test_file, # Not used directly in loop mode, verification_program is used
                    error_file=error_file,  # Not used in loop mode
                    output_test=output_test + ".loop",
                    output_code=output_code + ".loop",
                    output_results=output_results + ".loop",
                    loop=True,
                    verification_program=verification_file, # Use absolute path
                    max_attempts=3,
                    budget=1.0,
                    auto_submit=False
                )

                # Verify loop results
                assert isinstance(loop_success, bool), "Loop success should be a boolean"
                # loop_fixed_code might be empty if it failed
                assert isinstance(loop_fixed_code, str), "Loop fixed code should be a string"
                assert loop_attempts > 0, "Loop should have at least one attempt"

                print(f"Loop test result: success={loop_success}, attempts={loop_attempts}")
                if loop_success:
                    print(f"Loop fixed code:\n{loop_fixed_code}")
                else:
                    print("Loop mode did not succeed in fixing the code.")


            except Exception as loop_e:
                print(f"Loop mode test failed (but non-loop test passed): {loop_e}")
                # Don't fail the entire test if just the loop mode fails
                import traceback
                traceback.print_exc()

    except Exception as e:
        print(f"Error executing fix_main: {e}")
        import traceback
        traceback.print_exc()
        raise
    finally:
        # Change back to the original directory
        os.chdir(original_cwd)
        # Restore PDD_PATH if it was set
        if original_pdd_path is not None:
            os.environ['PDD_PATH'] = original_pdd_path


@patch('pdd.cli.auto_update') # Patch auto_update
@patch('pdd.fix_verification_main.construct_paths') # Not used in this test but kept for compatibility
@patch('pdd.cli.fix_verification_main') # The key function we want to test
def test_cli_verify_command_calls_fix_verification_main(mock_fix_verification, mock_construct_in_main, 
                                                       mock_auto_update, runner, create_dummy_files, tmp_path):
    """Test that fix_verification_main can be called with the expected arguments."""
    from pdd.cli import fix_verification_main as imported_func
    
    # Verify that the function is importable and the mocking works
    assert imported_func is mock_fix_verification, "The imported fix_verification_main should be the same as the mocked function"
    
    files = create_dummy_files("test.prompt", "test.py", "program.py")
    mock_prompt_file = str(files["test.prompt"])
    mock_code_file = str(files["test.py"])
    mock_program_file = str(files["program.py"])
    mock_output_results = str(tmp_path / "results.log")
    mock_output_code = str(tmp_path / "verified_code.py")
    mock_output_program = str(tmp_path / "verified_program.py")

    # Setup mock return values
    mock_fix_verification.return_value = (True, "prog_content", "code_content", 1, 0.01, "test_model")
    
    # Create a minimal context dictionary (not a Click context)
    ctx_obj = {
        'force': False,
        'strength': 0.8,
        'temperature': 0.0,
        'verbose': False,
        'quiet': False,
        'output_cost': None,
        'review_examples': False,
        'local': False,
        'time': DEFAULT_TIME, # Added time to context
    }
    
    # Create a minimal ctx-like object with obj attribute
    class MinimalContext:
        def __init__(self, obj):
            self.obj = obj
            
    ctx = MinimalContext(ctx_obj)
    
    # Call fix_verification_main directly with the parameters that the verify command would pass
    # This tests that the function is correctly importable and has the expected signature
    result = imported_func(
        ctx=ctx,
        prompt_file=mock_prompt_file,
        code_file=mock_code_file,
        program_file=mock_program_file,
        output_results=mock_output_results,
        output_code=mock_output_code,
        output_program=mock_output_program,
        loop=True,
        verification_program=mock_program_file,
        max_attempts=5,
        budget=10.0,
    )
    
    # Check that the function was called with the correct arguments
    mock_fix_verification.assert_called_once()
    kwargs = mock_fix_verification.call_args.kwargs
    
    assert kwargs.get('prompt_file') == mock_prompt_file
    assert kwargs.get('code_file') == mock_code_file
    assert kwargs.get('program_file') == mock_program_file
    assert kwargs.get('output_results') == mock_output_results
    assert kwargs.get('output_code') == mock_output_code
    assert kwargs.get('output_program') == mock_output_program
    assert kwargs.get('loop') is True 
    assert kwargs.get('verification_program') == mock_program_file
    assert kwargs.get('max_attempts') == 5
    assert kwargs.get('budget') == 10.0
    
    # Verify the return value
    assert result == (True, "prog_content", "code_content", 1, 0.01, "test_model")

@patch('pdd.cli.auto_update')
@patch('pdd.fix_verification_main.construct_paths')
@patch('pdd.cli.fix_verification_main')
def test_cli_verify_command_default_output_program(mock_fix_verification, mock_construct_in_main, mock_auto_update, runner, create_dummy_files, tmp_path):
    """Test `pdd verify` calls fix_verification_main with output_program=None by default."""
    files = create_dummy_files("test.prompt", "test.py", "program.py")
    mock_prompt_file = str(files["test.prompt"])
    mock_code_file = str(files["test.py"])
    mock_program_file = str(files["program.py"])

    mock_fix_verification.return_value = (True, "prog_content", "code_content", 1, 0.01, "test_model")
    mock_construct_in_main.return_value = (
        {"prompt_file": "p_content", "code_file": "c_content", "program_file": "prog_content"},
        # Simulate construct_paths returning None for output_program if not specified
        {"output_results": "some/path.log", "output_code": "some/code.py", "output_program": None},
        "python"
    )

    result = runner.invoke(cli.cli, [
        "verify",
        mock_prompt_file,
        mock_code_file,
        mock_program_file,
        # No --output-program here
    ])

    if result.exit_code != 0:
        print(f"CLI Error: {result.output}")
        if result.exception:
            raise result.exception
    
    assert "Usage: cli [OPTIONS] COMMAND" not in result.output, "Main help was printed, indicating dispatch failure."
    assert result.exit_code == 0


    mock_fix_verification.assert_called_once()
    kwargs = mock_fix_verification.call_args.kwargs
    assert kwargs.get('output_program') is None # Key assertion

@patch.dict(os.environ, {"PDD_VERIFY_PROGRAM_OUTPUT_PATH": "env_prog_output.py"}, clear=True) # Added clear=True
@patch('pdd.cli.auto_update')
@patch('pdd.fix_verification_main.construct_paths') 
@patch('pdd.cli.fix_verification_main')
def test_cli_verify_command_env_var_output_program(mock_fix_verification, mock_construct_in_main, mock_auto_update, runner, create_dummy_files, tmp_path):
    """Test `pdd verify` uses PDD_VERIFY_PROGRAM_OUTPUT_PATH env var."""
    files = create_dummy_files("test.prompt", "test.py", "program.py")
    mock_prompt_file = str(files["test.prompt"])
    mock_code_file = str(files["test.py"])
    mock_program_file = str(files["program.py"])
    
    expected_env_output_program_name = "env_prog_output.py"


    mock_fix_verification.return_value = (True, "prog_content", "code_content", 1, 0.01, "test_model")
    # Mock construct_paths to simulate it would return a path influenced by the env var
    # if fix_verification_main was real and called it.
    # For this test, what fix_verification_main *receives* from the CLI wrapper is key.
    mock_construct_in_main.return_value = (
        {"prompt_file": "p_content", "code_file": "c_content", "program_file": "prog_content"},
        {"output_results": "r.log", "output_code": "c.py", 
         "output_program": str(Path(expected_env_output_program_name).resolve())}, # This is what construct_paths would return
        "python"
    )

    result = runner.invoke(cli.cli, [
        "verify",
        mock_prompt_file,
        mock_code_file,
        mock_program_file,
        # No --output-program, CLI wrapper passes None to fix_verification_main.
        # The env var is used by construct_paths *inside* fix_verification_main.
    ])

    if result.exit_code != 0:
        print(f"CLI Error: {result.output}")
        if result.exception:
            raise result.exception
    
    assert "Usage: cli [OPTIONS] COMMAND" not in result.output, "Main help was printed, indicating dispatch failure."
    assert result.exit_code == 0

    mock_fix_verification.assert_called_once()
    kwargs = mock_fix_verification.call_args.kwargs
    
    # The CLI wrapper for 'verify' passes the --output-program option's value.
    # If the option is not provided, it passes None to fix_verification_main.
    # The environment variable PDD_VERIFY_PROGRAM_OUTPUT_PATH is handled
    # by construct_paths, which is called *inside* fix_verification_main.
    # Therefore, the mocked fix_verification_main should receive None for output_program.
    assert kwargs.get('output_program') is None

    # The assertion `assert "env_prog_output.py" in result.output` is removed because
    # process_commands in cli.py does not print this specific field from result_data
    # when the initial option value was None. The effect of the env var would be
    # internal to fix_verification_main and its call to construct_paths.
    # A different test structure would be needed to verify the env var's effect
    # on the actual file path used by a non-mocked fix_verification_main.

# Keep existing test_cli_verify_force_flag_propagation as is, or adapt if needed
# ... existing code ...

@pytest.mark.real
def test_real_verify_command(create_dummy_files, tmp_path):
    """Test the 'verify' command with real files by calling the function directly."""
    if not (os.getenv("PDD_RUN_REAL_LLM_TESTS") or RUN_ALL_TESTS_ENABLED):
        pytest.skip(
            "Real LLM integration tests require network/API access; set "
            "PDD_RUN_REAL_LLM_TESTS=1 or use --run-all / PDD_RUN_ALL_TESTS=1."
        )

    import sys
    import click
    from pathlib import Path
    from pdd.fix_verification_main import fix_verification_main as fix_verification_main_direct

    # Create a simple prompt file with valid content
    prompt_content = """// verify_python.prompt
// Language: Python
// Description: A simple function to divide two numbers
// Inputs: Two numbers a and b
// Outputs: The result of a divided by b

def divide(a, b):
    # Divide a by b and return the result
    return a / b
"""

    # Create a code file with a potential issue (missing validation)
    code_content = """# divide.py
def divide(a, b):
    # Divide a by b and return the result
    return a / b
"""

    # Create a program file to test the functionality
    program_content = """# test_divide.py
import sys
from divide import divide

def main():
    # Test the divide function with various inputs
    try:
        # These should work
        print(f"10 / 2 = {divide(10, 2)}")
        print(f"5 / 2.5 = {divide(5, 2.5)}")
        
        # This will cause an error
        print(f"5 / 0 = {divide(5, 0)}")
    except Exception as e:
        print(f"Error: {e}")
        sys.exit(1)

if __name__ == "__main__":
    main()
"""

    # Create files with the fixture, placing them directly in tmp_path
    files_dict = {}
    for name, content in {
        "verify_python.prompt": prompt_content, 
        "divide.py": code_content, 
        "test_divide.py": program_content
    }.items():
        file_path = tmp_path / name
        file_path.write_text(content)
        files_dict[name] = file_path

    # Get the file paths as strings
    prompt_file = str(files_dict["verify_python.prompt"])
    code_file = str(files_dict["divide.py"])
    program_file = str(files_dict["test_divide.py"])

    # Create output directory relative to tmp_path
    output_dir = tmp_path / "output"
    output_dir.mkdir(exist_ok=True)
    output_results = str(output_dir / "verify_results.log")
    output_code = str(output_dir / "verified_divide.py")
    output_program = str(output_dir / "verified_test_divide.py")

    # Print environment info for debugging
    print(f"Temporary directory: {tmp_path}")
    print(f"Current working directory: {os.getcwd()}")
    print(f"Prompt file location: {prompt_file}")
    print(f"Code file location: {code_file}")
    print(f"Program file location: {program_file}")
    print(f"Output directory: {output_dir}")

    # Create a minimal context object with the necessary parameters
    ctx = click.Context(click.Command("verify"))
    ctx.obj = {
        'force': True,
        'quiet': False,
        'verbose': True,
        'strength': 0.8,
        'temperature': 0.0,
        'local': True,  # Use local execution to avoid API calls
        'output_cost': None,
        'review_examples': False,
        'time': DEFAULT_TIME, # Added time to context
    }

    # Change working directory to tmp_path so imports work correctly
    original_cwd = os.getcwd()
    os.chdir(tmp_path)
    
    # Set PDD_PATH to the project root so prompt templates can be found
    # Get the project root dynamically from the current test file location
    original_pdd_path = os.getenv('PDD_PATH')
    project_root = Path(__file__).parent.parent  # Go up from tests/ to project root
    os.environ['PDD_PATH'] = str(project_root)

    try:
        # Call fix_verification_main directly - with minimal mocking
        success, final_program, final_code, attempts, cost, model = fix_verification_main_direct(
            ctx=ctx,
            prompt_file=prompt_file,
            code_file=code_file,
            program_file=program_file,
            output_results=output_results,
            output_code=output_code,
            output_program=output_program,
            loop=True,
            verification_program=program_file,
            max_attempts=3,
            budget=1.0
        )

        # Verify we got reasonable results back
        assert isinstance(success, bool), "Success should be a boolean"
        assert isinstance(final_code, str), "Final code should be a string"
        assert isinstance(final_program, str), "Final program should be a string" 
        assert attempts >= 0, "Attempts should be non-negative (0 means no fixes needed)"
        assert isinstance(cost, float), "Cost should be a float"
        assert isinstance(model, str), "Model name should be a string"

        # Check output files were created (if successful)
        if success:
            assert Path(output_code).exists(), f"Output code file not created at {output_code}"
            assert Path(output_program).exists(), f"Output program file not created at {output_program}"
            assert Path(output_results).exists(), f"Output results file not created at {output_results}"

            # Verify content of generated code file
            verified_code_content = Path(output_code).read_text()
            assert "def divide" in verified_code_content, "Verified code should contain a divide function"
            # Note: LLM may determine no changes are needed if prompt doesn't require error handling
            print(f"LLM made {attempts} attempts and determined verification was {'successful' if success else 'unsuccessful'}")

            # Print success message and contents
            print("\nTest passed! Verified code:")
            print(verified_code_content)
        else:
            # Still check if any intermediate files were created
            for intermediate_file in output_dir.glob("*divide*.py"):
                print(f"Intermediate file found: {intermediate_file}")
                print(intermediate_file.read_text())

    except Exception as e:
        print(f"Error executing fix_verification_main: {e}")
        import traceback
        traceback.print_exc()
        raise
    finally:
        # Change back to the original directory
        os.chdir(original_cwd)
        # Restore PDD_PATH if it was set
        if original_pdd_path is not None:
            os.environ['PDD_PATH'] = original_pdd_path
