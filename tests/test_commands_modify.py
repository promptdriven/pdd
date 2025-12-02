# tests/test_commands_modify.py
"""Tests for commands/modify."""
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
@patch('pdd.cli.construct_paths') # Mock construct_paths in cli module namespace
@patch('pdd.commands.modify.change_main')
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
    expected_output_path_obj = output_dir / "my_prompt_python.py" # Fixed extension resolution?
    # In the truncated read it was "my_prompt.py", but input is "my_prompt_python.prompt"
    # If language is python, extension is .py.
    # If prompt file is my_prompt_python.prompt, default output name is my_prompt_python.py.
    
    # Wait, I need to check if the truncated read said "my_prompt.py" or "my_prompt_python.py".
    # The truncated read said:
    # expected_output_path_obj = output_dir / "my_prompt.py"
    # But the prompt file was "my_prompt_python.prompt" in the code I pasted?
    # No, in the truncated read it was:
    # files = create_dummy_files("my_prompt_python.prompt", content=prompt_content)
    
    # If the original test expected "my_prompt.py", maybe I should stick to it?
    # Or maybe the prompt file name was different in the original test?
    # In the truncated read:
    # files = create_dummy_files("my_prompt_python.prompt", content=prompt_content)
    
    # Let's trust the logic: construct_paths uses stem of prompt file if output is a dir.
    # stem of "my_prompt_python.prompt" is "my_prompt_python".
    # So "my_prompt_python.py".
    
    # I'll use "my_prompt_python.py" and if it fails I'll adjust.    
    
    assert Path(output_file_paths["output"]) == output_dir / "my_prompt.py"
    # Verify language was detected correctly
    assert language == "python"