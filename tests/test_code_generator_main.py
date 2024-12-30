import pytest
from unittest.mock import patch, MagicMock
from click.testing import CliRunner
import sys
from pdd.code_generator_main import code_generator_main

#if output directory does not exist, create it
import os   
os.makedirs("output", exist_ok=True)


# Mock the construct_paths and code_generator functions
@patch('pdd.code_generator_main.construct_paths')
@patch('pdd.code_generator_main.code_generator')
def test_code_generator_main_success(mock_code_generator, mock_construct_paths):
    """
    Test case for successful code generation.
    """
    # Setup mock objects
    mock_ctx = MagicMock()
    mock_ctx.params = {'force': False, 'quiet': False}
    mock_ctx.obj = {'strength': 0.5, 'temperature': 0.0}

    mock_construct_paths.return_value = (
        {"prompt_file": "mock_prompt_content"},
        {"output": "output/mock_output_path"},
        "python"
    )

    mock_code_generator.return_value = ("mock_generated_code", 0.01, "mock_model_name")

    # Call the function
    result = code_generator_main(mock_ctx, "mock_prompt_file", "mock_output")

    # Assertions
    assert result == ("mock_generated_code", 0.01, "mock_model_name")
    mock_construct_paths.assert_called_once_with(
        input_file_paths={"prompt_file": "mock_prompt_file"},
        force=False,
        quiet=False,
        command="generate",
        command_options={"output": "mock_output"}
    )
    mock_code_generator.assert_called_once_with(
        "mock_prompt_content",
        "python",
        0.5,
        0.0,
        verbose=True
    )

@patch('pdd.code_generator_main.construct_paths')
def test_code_generator_main_file_not_found(mock_construct_paths):
    """
    Test case for handling file not found error.
    """
    # Setup mock objects
    mock_ctx = MagicMock()
    mock_ctx.params = {'force': False, 'quiet': False}
    mock_ctx.obj = {'strength': 0.5, 'temperature': 0.0}

    mock_construct_paths.side_effect = FileNotFoundError("File not found")

    # Call the function and expect SystemExit
    with pytest.raises(SystemExit):
        code_generator_main(mock_ctx, "nonexistent_prompt_file", "mock_output")

@patch('pdd.code_generator_main.construct_paths')
@patch('pdd.code_generator_main.code_generator')
def test_code_generator_main_generation_error(mock_code_generator, mock_construct_paths):
    """
    Test case for handling code generation error.
    """
    # Setup mock objects
    mock_ctx = MagicMock()
    mock_ctx.params = {'force': False, 'quiet': False}
    mock_ctx.obj = {'strength': 0.5, 'temperature': 0.0}

    mock_construct_paths.return_value = (
        {"prompt_file": "mock_prompt_content"},
        {"output": "output/mock_output_path"},
        "python"
    )

    mock_code_generator.side_effect = Exception("Generation error")

    # Call the function and expect SystemExit
    with pytest.raises(SystemExit):
        code_generator_main(mock_ctx, "mock_prompt_file", "mock_output")

@patch('pdd.code_generator_main.construct_paths')
@patch('pdd.code_generator_main.code_generator')
def test_code_generator_main_quiet_mode(mock_code_generator, mock_construct_paths):
    """
    Test case for quiet mode operation.
    """
    # Setup mock objects
    mock_ctx = MagicMock()
    mock_ctx.params = {'force': False, 'quiet': True}
    mock_ctx.obj = {'strength': 0.5, 'temperature': 0.0}

    mock_construct_paths.return_value = (
        {"prompt_file": "mock_prompt_content"},
        {"output": "output/mock_output_path"},
        "python"
    )

    mock_code_generator.return_value = ("mock_generated_code", 0.01, "mock_model_name")

    # Call the function
    result = code_generator_main(mock_ctx, "mock_prompt_file", "mock_output")

    # Assertions
    assert result == ("mock_generated_code", 0.01, "mock_model_name")
    mock_code_generator.assert_called_once_with(
        "mock_prompt_content",
        "python",
        0.5,
        0.0,
        verbose=False
    )

@patch('pdd.code_generator_main.construct_paths')
@patch('pdd.code_generator_main.code_generator')
def test_code_generator_main_no_output(mock_code_generator, mock_construct_paths):
    """
    Test case for no output file specified.
    """
    # Setup mock objects
    mock_ctx = MagicMock()
    mock_ctx.params = {'force': False, 'quiet': False}
    mock_ctx.obj = {'strength': 0.5, 'temperature': 0.0}

    mock_construct_paths.return_value = (
        {"prompt_file": "mock_prompt_content"},
        {"output": None},
        "python"
    )

    mock_code_generator.return_value = ("mock_generated_code", 0.01, "mock_model_name")

    # Call the function
    result = code_generator_main(mock_ctx, "mock_prompt_file", None)

    # Assertions
    assert result == ("mock_generated_code", 0.01, "mock_model_name")
    mock_construct_paths.assert_called_once_with(
        input_file_paths={"prompt_file": "mock_prompt_file"},
        force=False,
        quiet=False,
        command="generate",
        command_options={"output": None}
    )