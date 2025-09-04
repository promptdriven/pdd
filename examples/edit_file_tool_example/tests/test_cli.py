# tests/test_cli.py

# To run this test:
# Option 1: From project root: pytest tests/test_cli.py
# Option 2: From project root: python -m pytest tests/test_cli.py

"""
Test Plan for edit_file_tool/cli.py

The cli.py module is the user-facing entry point of the application.
Testing focuses on ensuring it correctly handles user input, environment
configuration, and delegation to the core logic, while providing clear
feedback.

**Testing Strategy:**
- Use `click.testing.CliRunner` to simulate command-line invocations.
- Use `unittest.mock.patch` to isolate the CLI from the core logic (`edit_file`)
  and API constants (`DEFAULT_MODEL`, `SUPPORTED_MODELS`). This is crucial
  because the CLI's primary job is to *delegate*, not to perform the edits itself.
- Use `monkeypatch` to control environment variables, which is a key part of
  the CLI's configuration mechanism.
- Use `tmp_path` to create real temporary files, ensuring that path handling
  by `click` and the OS works as expected.

**Test Cases:**


1.  **Core Logic Delegation & Output:**
    - `test_cli_successful_edit`: Verify the "happy path". The CLI should call
      `core.edit_file`, report success, print the cost, and exit with code 0.
    - `test_cli_failed_edit`: Verify handling of a controlled failure from the core
      logic. The CLI should report the error message to stderr and exit with code 1.
    - `test_cli_unexpected_exception`: Ensure the CLI's top-level exception
      handler catches unexpected errors from the core logic and exits cleanly.
    - `test_cli_zero_cost`: Ensure the cost is not printed if it's zero.

2.  **Argument and Option Parsing:**
    - `test_cli_argument_passing`: Confirm that all arguments and options are
      correctly parsed and passed to the `core.edit_file` function.
    - `test_cli_verbose_output`: Check that the `--verbose` flag triggers
      additional, helpful output.
    - `test_cli_missing_arguments`: A parametrized test to ensure `click`'s
      built-in validation for required arguments is working.

3.  **Model Resolution and Validation:**
    - `test_cli_model_resolution_precedence`: A parametrized test to verify the
      correct model resolution order: CLI > Environment Variable > Default.
    - `test_cli_unsupported_model`: Ensure the CLI rejects an unsupported model
      name before calling the core logic.

4.  **Robustness and Edge Cases:**
    - `test_cli_dynamic_import_failure`: A critical test to ensure the CLI
      handles a broken installation where `core` or `claude_api` cannot be imported.
    - `test_main_entry_point`: A simple test for the synchronous `main` wrapper
      function to ensure it correctly invokes the CLI and handles exceptions.
"""

import sys
from unittest.mock import patch, MagicMock, AsyncMock

import click.testing
import pytest

# Import the function and entry point to be tested
from edit_file_tool.cli import cli, main

# Define constants for mocking
MOCK_DEFAULT_MODEL = "claude-default"
MOCK_SUPPORTED_MODELS = {
    "claude-default",
    "claude-cli",
    "claude-env",
    "claude-3-5-sonnet-20240620",
}


@pytest.fixture
def runner():
    """Provides a Click test runner instance."""
    return click.testing.CliRunner()




def test_cli_successful_edit(runner, tmp_path, monkeypatch):
    """
    Test the happy path: a successful edit.
    """
    monkeypatch.setenv("ANTHROPIC_API_KEY", "test-key")
    test_file = tmp_path / "test.txt"
    test_file.touch()

    mock_edit_file = AsyncMock(return_value=(True, "Final message from model.", 0.12345))
    mock_core_module = MagicMock(edit_file=mock_edit_file)
    mock_api_module = MagicMock(DEFAULT_MODEL=MOCK_DEFAULT_MODEL, SUPPORTED_MODELS=MOCK_SUPPORTED_MODELS)

    with patch.dict(sys.modules, {
        'edit_file_tool.core': mock_core_module,
        'edit_file_tool.claude_api': mock_api_module,
    }):
        result = runner.invoke(
            cli, [str(test_file), "do the thing", "--verbose"]
        )

    assert result.exit_code == 0, f"CLI failed with output:\n{result.output}"
    assert "edited successfully" in result.output
    assert "LLM cost: $0.1235" in result.output
    assert "Final message from model." in result.output
    mock_edit_file.assert_called_once()


def test_cli_failed_edit(runner, tmp_path, monkeypatch):
    """
    Test the scenario where the core logic returns a failure.
    """
    monkeypatch.setenv("ANTHROPIC_API_KEY", "test-key")
    test_file = tmp_path / "test.txt"
    test_file.touch()

    mock_edit_file = AsyncMock(return_value=(False, "Something went wrong in core.", 0.05))
    mock_core_module = MagicMock(edit_file=mock_edit_file)
    mock_api_module = MagicMock(DEFAULT_MODEL=MOCK_DEFAULT_MODEL, SUPPORTED_MODELS=MOCK_SUPPORTED_MODELS)

    with patch.dict(sys.modules, {
        'edit_file_tool.core': mock_core_module,
        'edit_file_tool.claude_api': mock_api_module,
    }):
        result = runner.invoke(cli, [str(test_file), "do the thing"])

    assert result.exit_code == 1
    assert "LLM cost: $0.0500" in result.output # Cost is still reported
    assert "Error: Failed to edit file. Reason: Something went wrong in core." in result.output


def test_cli_unexpected_exception(runner, tmp_path, monkeypatch):
    """
    Test that the CLI handles unexpected exceptions from the core logic.
    """
    monkeypatch.setenv("ANTHROPIC_API_KEY", "test-key")
    test_file = tmp_path / "test.txt"
    test_file.touch()

    mock_edit_file = AsyncMock(side_effect=ValueError("Core module exploded!"))
    mock_core_module = MagicMock(edit_file=mock_edit_file)
    mock_api_module = MagicMock(DEFAULT_MODEL=MOCK_DEFAULT_MODEL, SUPPORTED_MODELS=MOCK_SUPPORTED_MODELS)

    with patch.dict(sys.modules, {
        'edit_file_tool.core': mock_core_module,
        'edit_file_tool.claude_api': mock_api_module,
    }):
        result = runner.invoke(cli, [str(test_file), "do the thing"])

    assert result.exit_code == 1
    assert "An unexpected error occurred" in result.output
    assert "Core module exploded!" in result.output


def test_cli_zero_cost(runner, tmp_path, monkeypatch):
    """
    Test that the cost is not printed if it is zero (e.g., for a file-not-found error).
    """
    monkeypatch.setenv("ANTHROPIC_API_KEY", "test-key")
    
    mock_edit_file = AsyncMock(return_value=(False, "File not found", 0.0))
    mock_core_module = MagicMock(edit_file=mock_edit_file)
    mock_api_module = MagicMock(DEFAULT_MODEL=MOCK_DEFAULT_MODEL, SUPPORTED_MODELS=MOCK_SUPPORTED_MODELS)

    with patch.dict(sys.modules, {
        'edit_file_tool.core': mock_core_module,
        'edit_file_tool.claude_api': mock_api_module,
    }):
        result = runner.invoke(cli, ["nonexistent.txt", "do the thing"])

    assert result.exit_code == 1
    assert "LLM cost" not in result.output
    assert "File not found" in result.output


@pytest.mark.parametrize(
    "cli_model, env_model, expected_model",
    [
        ("claude-cli", "claude-env", "claude-cli"),  # CLI option wins
        (None, "claude-env", "claude-env"),         # Env var wins
        (None, None, MOCK_DEFAULT_MODEL),           # Default wins
    ],
)
def test_cli_model_resolution_precedence(
    cli_model, env_model, expected_model, runner, tmp_path, monkeypatch
):
    """
    Test the model resolution precedence: CLI > Environment > Default.
    """
    monkeypatch.setenv("ANTHROPIC_API_KEY", "test-key")
    if env_model:
        monkeypatch.setenv("EDIT_FILE_TOOL_MODEL", env_model)
    else:
        monkeypatch.delenv("EDIT_FILE_TOOL_MODEL", raising=False)

    test_file = tmp_path / "test.txt"
    test_file.touch()

    args = [str(test_file), "instruction"]
    if cli_model:
        args.extend(["--model", cli_model])

    mock_edit_file = AsyncMock(return_value=(True, "Success", 0.1))
    mock_core_module = MagicMock(edit_file=mock_edit_file)
    mock_api_module = MagicMock(DEFAULT_MODEL=MOCK_DEFAULT_MODEL, SUPPORTED_MODELS=MOCK_SUPPORTED_MODELS)

    with patch.dict(sys.modules, {
        'edit_file_tool.core': mock_core_module,
        'edit_file_tool.claude_api': mock_api_module,
    }):
        runner.invoke(cli, args)

    mock_edit_file.assert_called_once()
    call_args, call_kwargs = mock_edit_file.call_args
    assert call_kwargs["model"] == expected_model


def test_cli_unsupported_model(runner, tmp_path, monkeypatch):
    """
    Test that the CLI rejects an unsupported model.
    """
    monkeypatch.setenv("ANTHROPIC_API_KEY", "test-key")
    test_file = tmp_path / "test.txt"
    test_file.touch()

    mock_edit_file = AsyncMock()
    mock_core_module = MagicMock(edit_file=mock_edit_file)
    mock_api_module = MagicMock(DEFAULT_MODEL=MOCK_DEFAULT_MODEL, SUPPORTED_MODELS=MOCK_SUPPORTED_MODELS)

    with patch.dict(sys.modules, {
        'edit_file_tool.core': mock_core_module,
        'edit_file_tool.claude_api': mock_api_module,
    }):
        result = runner.invoke(
            cli, [str(test_file), "instruction", "--model", "unsupported-llama"]
        )

    assert result.exit_code == 1
    assert "Error: Model 'unsupported-llama' is not supported." in result.output
    assert "Supported models are:" in result.output
    mock_edit_file.assert_not_called()


def test_cli_argument_passing(runner, tmp_path, monkeypatch):
    """
    Test that all arguments and options are passed correctly to the core function.
    """
    monkeypatch.setenv("ANTHROPIC_API_KEY", "test-key")
    test_file = tmp_path / "args.txt"
    test_file.touch()

    mock_edit_file = AsyncMock(return_value=(True, "Success", 0.1))
    mock_core_module = MagicMock(edit_file=mock_edit_file)
    mock_api_module = MagicMock(DEFAULT_MODEL=MOCK_DEFAULT_MODEL, SUPPORTED_MODELS=MOCK_SUPPORTED_MODELS)

    with patch.dict(sys.modules, {
        'edit_file_tool.core': mock_core_module,
        'edit_file_tool.claude_api': mock_api_module,
    }):
        runner.invoke(
            cli,
            [
                str(test_file),
                "my specific instruction",
                "--cache",
                "always",
                "--max-iterations",
                "5",
                "--verbose",
            ],
        )

    mock_edit_file.assert_called_once_with(
        file_path=str(test_file),
        edit_instructions="my specific instruction",
        model=MOCK_DEFAULT_MODEL, # Patched default
        use_cache="always",
        verbose=True,
        max_iterations=5,
    )


@pytest.mark.parametrize(
    "args, expected_error",
    [
        (["instruction only"], "Missing argument 'EDIT_INSTRUCTIONS'"),
        ([], "Missing argument 'FILE_PATH'"),
    ],
)
def test_cli_missing_arguments(args, expected_error, runner, tmp_path):
    """
    Test that click handles missing required arguments.
    Note: `click` checks arguments from left to right, so we only test the first missing one.
    """
    # No need to set API key, as click validation happens before our code runs.
    result = runner.invoke(cli, args)
    assert result.exit_code == 2  # click's exit code for usage errors
    assert expected_error in result.output


def test_cli_dynamic_import_failure(runner, monkeypatch):
    """
    Test robustness if a required module cannot be imported.
    """
    monkeypatch.setenv("ANTHROPIC_API_KEY", "test-key")
    # Simulate a failed import by removing the module from sys.modules if it exists
    # and then patching __import__ to raise an error for it.
    with patch.dict(sys.modules, {"edit_file_tool.core": None}):
        result = runner.invoke(cli, ["file.txt", "instruction"])

    assert result.exit_code == 1
    assert "Error: Failed to import required modules." in result.output


@patch("edit_file_tool.cli.cli")
def test_main_entry_point(mock_cli_func):
    """
    Test the synchronous main() wrapper function.
    """
    main()
    mock_cli_func.assert_called_once()


@patch("edit_file_tool.cli.cli")
def test_main_entry_point_exception_handling(mock_cli_func, capsys):
    """
    Test that the main() wrapper catches unexpected exceptions.
    """
    mock_cli_func.side_effect = RuntimeError("Critical failure during CLI setup")
    with pytest.raises(SystemExit) as e:
        main()

    assert e.value.code == 1
    captured = capsys.readouterr()
    assert "A critical error occurred: Critical failure during CLI setup" in captured.err
