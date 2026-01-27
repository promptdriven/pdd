# tests/test_commands_generate.py
"""Tests for commands/generate."""
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

@patch('pdd.core.cli.auto_update')
@patch('pdd.commands.generate.code_generator_main')
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

@patch('pdd.core.cli.auto_update')
@patch('pdd.commands.generate.code_generator_main')
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

@patch('pdd.core.cli.auto_update')
@patch('pdd.commands.generate.code_generator_main')
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

@patch('pdd.core.cli.auto_update')
@patch('pdd.commands.generate.code_generator_main')
def test_cli_generate_template_with_prompt_raises_usage_error(mock_code_main, mock_auto_update, runner, create_dummy_files):
    """Providing both --template and PROMPT_FILE should raise a usage error."""
    files = create_dummy_files("conflict.prompt")

    result = runner.invoke(
        cli.cli,
        ["generate", "--template", "architecture/demo", str(files["conflict.prompt"])]
    )

    assert result.exit_code == 2  # UsageError exits with code 2
    assert "either --template or a PROMPT_FILE" in result.output or "Usage" in result.output
    mock_code_main.assert_not_called()

@patch('pdd.core.cli.auto_update')
@patch('pdd.commands.generate.code_generator_main')
@patch('pdd.template_registry.load_template', side_effect=FileNotFoundError("missing"))
def test_cli_generate_template_load_failure(mock_load_template, mock_code_main, mock_auto_update, runner):
    """Failed template resolution should surface as a UsageError without running the command."""
    result = runner.invoke(cli.cli, ["generate", "--template", "missing/template"])

    assert result.exit_code == 2  # UsageError exits with code 2
    assert "Failed to load template 'missing/template'" in result.output or "Usage" in result.output
    mock_code_main.assert_not_called()

# --- GitHub Issue URL Detection Tests ---

@patch('pdd.core.cli.auto_update')
@patch('pdd.agentic_architecture.run_agentic_architecture')
def test_cli_generate_github_issue_url_triggers_agentic_mode(mock_agentic, mock_auto_update, runner):
    """A GitHub issue URL should trigger agentic architecture mode instead of file generation."""
    mock_agentic.return_value = (True, "Architecture generated", 2.5, "anthropic", ["architecture.json"])

    result = runner.invoke(
        cli.cli,
        ["generate", "https://github.com/owner/repo/issues/42"],
    )
    assert result.exit_code == 0
    mock_agentic.assert_called_once_with(
        issue_url="https://github.com/owner/repo/issues/42",
        verbose=False,
        quiet=False,
        skip_prompts=False,
    )
    assert "Architecture generated" in result.output


@patch('pdd.core.cli.auto_update')
@patch('pdd.agentic_architecture.run_agentic_architecture')
def test_cli_generate_github_issue_url_failure(mock_agentic, mock_auto_update, runner):
    """Agentic architecture failure should be reported gracefully."""
    mock_agentic.return_value = (False, "gh CLI not found", 0.0, "", [])

    result = runner.invoke(
        cli.cli,
        ["generate", "https://github.com/owner/repo/issues/99"],
    )
    assert result.exit_code == 0
    assert "Failed" in result.output or "gh CLI not found" in result.output


@patch('pdd.core.cli.auto_update')
@patch('pdd.commands.generate.code_generator_main')
def test_cli_generate_nonexistent_file_raises_error(mock_main, mock_auto_update, runner, tmp_path):
    """A non-existent file path should raise a UsageError."""
    result = runner.invoke(
        cli.cli,
        ["generate", str(tmp_path / "nonexistent.prompt")],
    )
    assert result.exit_code == 2
    assert "does not exist" in result.output
    mock_main.assert_not_called()


@patch('pdd.core.cli.auto_update')
@patch('pdd.commands.generate.code_generator_main')
def test_cli_generate_directory_path_raises_error(mock_main, mock_auto_update, runner, tmp_path):
    """A directory path should raise a UsageError."""
    result = runner.invoke(
        cli.cli,
        ["generate", str(tmp_path)],
    )
    assert result.exit_code == 2
    assert "is a directory" in result.output
    mock_main.assert_not_called()


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
        print(f"Successfully generated code at {output_path}")
    except Exception as e:
        pytest.fail(f"Real generation test failed: {e}")


# --- Issue #409: Environment Variable Pollution Tests ---


@patch('pdd.core.cli.auto_update')
@patch('pdd.commands.generate.code_generator_main')
def test_issue_409_env_vars_do_not_pollute_os_environ(mock_main, mock_auto_update, runner, create_dummy_files, monkeypatch):
    """Test that environment variables set via -e flag do not persist in os.environ after command completion.

    This test detects the bug reported in issue #409 where os.environ.update(env_vars) at
    pdd/commands/generate.py:152 permanently pollutes the process environment with variables
    passed via the -e/--env flag.

    Expected behavior (per documentation and code comment):
    - Variables passed with -e should be available "for the duration of this command"
    - After command completes, os.environ should be restored to its original state

    Actual behavior (before fix):
    - Variables persist permanently in os.environ due to missing cleanup
    - Causes test pollution, security leaks, and unpredictable behavior
    """
    # Create test files
    files = create_dummy_files("pollution_test.prompt")
    mock_main.return_value = ('code', False, 0.0, 'model')

    # Define test variables that should NOT persist
    test_vars = {
        'TEST_VAR_409': 'test_value',
        'SECRET_KEY_409': 'secret123',
        'API_TOKEN_409': 'token456'
    }

    # Capture os.environ state BEFORE command execution
    # Store keys that exist before the test
    env_before = set(os.environ.keys())

    # Ensure test variables don't exist before the test
    for key in test_vars.keys():
        monkeypatch.delenv(key, raising=False)

    # Build command line arguments with -e flags
    cmd_args = ["generate"]
    for key, value in test_vars.items():
        cmd_args.extend(["-e", f"{key}={value}"])
    cmd_args.append(str(files["pollution_test.prompt"]))

    # Execute the generate command with environment variables
    result = runner.invoke(cli.cli, cmd_args)
    assert result.exit_code == 0, f"Command failed: {result.output}"

    # Verify code_generator_main was called with correct env_vars parameter
    call_kwargs = mock_main.call_args.kwargs
    assert call_kwargs["env_vars"] == test_vars, "env_vars parameter should contain test variables"

    # CRITICAL CHECK: Environment variables should NOT persist in os.environ after command completion
    # This is the primary bug detection - this assertion will FAIL on the buggy code
    env_after = set(os.environ.keys())
    pollution_detected = []

    for key in test_vars.keys():
        if key in os.environ:
            pollution_detected.append(f"{key}={os.environ[key]}")

    # Assert that no test variables leaked into os.environ
    assert len(pollution_detected) == 0, (
        f"BUG DETECTED (Issue #409): Environment variables persist after command completion! "
        f"Polluted variables: {pollution_detected}. "
        f"These variables were set via -e flag and should NOT exist in os.environ after the command. "
        f"Root cause: pdd/commands/generate.py:152 calls os.environ.update(env_vars) without cleanup."
    )

    # Additional check: Verify no NEW keys were added to os.environ
    new_keys = env_after - env_before
    # Filter out keys that might be legitimately added by the test framework
    unexpected_new_keys = [k for k in new_keys if k in test_vars]

    assert len(unexpected_new_keys) == 0, (
        f"Unexpected new environment variables detected: {unexpected_new_keys}. "
        f"These should not persist after command completion."
    )