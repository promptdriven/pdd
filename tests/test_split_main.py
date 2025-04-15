# File: tests/test_split_main.py

import pytest
import sys
from unittest.mock import patch, mock_open, MagicMock
import click

from pdd.split_main import split_main

@pytest.fixture
def mock_ctx():
    """
    Returns a mock Click context with default parameters and object settings.
    Adjust the params and obj dictionaries as needed for specific tests.
    """
    ctx = MagicMock(spec=click.Context)
    ctx.params = {
        "force": False,
        "quiet": False
    }
    ctx.obj = {
        "strength": 0.5,
        "temperature": 0.0
    }
    return ctx

@pytest.mark.parametrize("quiet_mode", [False, True])
def test_split_main_success(mock_ctx, quiet_mode, capsys):
    """
    Test that split_main executes successfully, writes correct content,
    and returns the expected values.
    """
    # Arrange
    mock_ctx.obj["quiet"] = quiet_mode

    # Prepare mock return values for construct_paths and split
    mock_input_strings = {
        "input_prompt": "prompt content",
        "input_code": "code content",
        "example_code": "example code content"
    }
    mock_output_paths = {
        "output_sub": "/fake_dir/sub_prompt.prompt",
        "output_modified": "/fake_dir/modified_prompt.prompt"
    }
    mock_language = "python"

    extracted_functionality_result = "sub prompt result"
    remaining_prompt_result = "modified prompt result"
    total_cost_result = 0.123456
    mock_model_name = "mock_model" # Added mock model name

    with patch("pdd.split_main.construct_paths") as mock_construct_paths, \
         patch("pdd.split_main.split") as mock_split, \
         patch("builtins.open", mock_open()) as m_file:

        # Set up our patched functions
        mock_construct_paths.return_value = (mock_input_strings, mock_output_paths, mock_language)
        mock_split.return_value = (extracted_functionality_result, remaining_prompt_result, mock_model_name, total_cost_result) # Corrected mock return

        # Act
        extracted_functionality, remaining_prompt, total_cost, model_name = split_main( # Corrected unpacking
            mock_ctx,
            "input_prompt_file.prompt",
            "input_code_file.py",
            "example_code_file.py",
            None,
            None
        )

        # Assert
        assert extracted_functionality == extracted_functionality_result
        assert remaining_prompt == remaining_prompt_result
        assert total_cost == total_cost_result
        assert model_name == mock_model_name # Added model name assertion


        # Check that construct_paths was called with correct arguments
        mock_construct_paths.assert_called_once()
        call_args, call_kwargs = mock_construct_paths.call_args
        assert call_kwargs["input_file_paths"] == {
            "input_prompt": "input_prompt_file.prompt",
            "input_code": "input_code_file.py",
            "example_code": "example_code_file.py",
        }
        assert call_kwargs["force"] == mock_ctx.params["force"]
        assert call_kwargs["quiet"] == quiet_mode
        assert call_kwargs["command"] == "split"

        # Check that the files were written with the correct contents
        assert m_file.call_count == 2  # sub-prompt and modified-prompt
        file_calls = [call[0][0] for call in m_file.call_args_list]
        assert "/fake_dir/sub_prompt.prompt" in file_calls
        assert "/fake_dir/modified_prompt.prompt" in file_calls

        # Check console output
        captured = capsys.readouterr()
        if quiet_mode:
            # No success message should appear in quiet mode
            assert "Successfully split the prompt!" not in captured.out
            assert "Extracted functionality saved to:" not in captured.out
        else:
            # Success messages should appear
            assert "Successfully split the prompt!" in captured.out
            assert "sub_prompt.prompt" in captured.out
            assert "modified_prompt.prompt" in captured.out
            assert f"Total cost: $0.123456" in captured.out

def test_split_main_file_not_found(mock_ctx, capsys):
    """
    Test that split_main properly handles FileNotFoundError
    by printing an error message and exiting with code 1.
    """
    with patch("pdd.split_main.construct_paths", side_effect=FileNotFoundError("Test file not found")), \
         pytest.raises(SystemExit) as exc_info:

        split_main(
            mock_ctx,
            "input_prompt_file.prompt",
            "input_code_file.py",
            "example_code_file.py",
            None,
            None
        )

    captured = capsys.readouterr()
    assert exc_info.value.code == 1
    assert "Error:" in captured.out
    assert "Test file not found" in captured.out
    assert "Hint: Check if all input files exist and are accessible." in captured.out

def test_split_main_io_error_during_write(mock_ctx, capsys):
    """
    Test that split_main properly handles an IOError when writing
    the output files, printing an error message and exiting with code 1.
    """
    mock_input_strings = {
        "input_prompt": "prompt content",
        "input_code": "code content",
        "example_code": "example code content"
    }
    mock_output_paths = {
        "output_sub": "/fake_dir/sub_prompt.prompt",
        "output_modified": "/fake_dir/modified_prompt.prompt"
    }
    mock_language = "python"
    mock_model_name = "mock_model"

    with patch("pdd.split_main.construct_paths") as mock_construct_paths, \
         patch("pdd.split_main.split") as mock_split, \
         patch("builtins.open", side_effect=IOError("Disk full")), \
         pytest.raises(SystemExit) as exc_info:

        mock_construct_paths.return_value = (mock_input_strings, mock_output_paths, mock_language)
        mock_split.return_value = ("extracted functionality", "remaining prompt", mock_model_name, 0.5)

        split_main(
            mock_ctx,
            "input_prompt_file.prompt",
            "input_code_file.py",
            "example_code_file.py",
            None,
            None
        )

    captured = capsys.readouterr()
    assert exc_info.value.code == 1
    assert "Error:" in captured.out
    assert "Failed to save output files: Disk full" in captured.out  # Corrected assertion
    assert "Hint: Check file permissions and disk space." in captured.out

def test_split_main_value_error(mock_ctx, capsys):
    """
    Test that split_main properly handles a generic ValueError and provides a relevant hint.
    """
    with patch("pdd.split_main.construct_paths") as mock_construct_paths, \
         patch("pdd.split_main.split", side_effect=ValueError("Invalid content")), \
         pytest.raises(SystemExit) as exc_info:

        mock_construct_paths.return_value = (
            {
                "input_prompt": "prompt content",
                "input_code": "code content",
                "example_code": "example code content"
            },
            {
                "output_sub": "/fake_dir/sub_prompt.prompt",
                "output_modified": "/fake_dir/modified_prompt.prompt"
            },
            "python"
        )

        split_main(
            mock_ctx,
            "input_prompt_file.prompt",
            "input_code_file.py",
            "example_code_file.py",
            None,
            None
        )

    captured = capsys.readouterr()
    assert exc_info.value.code == 1
    assert "Error:" in captured.out
    assert "Invalid content" in captured.out
    assert "Hint: Check if input files have valid content." in captured.out

def test_split_main_quiet_mode(mock_ctx, capsys):
    """
    Test that no user feedback is printed in quiet mode except for errors.
    In normal operation, it should return without printing anything.
    """
    mock_ctx.obj["quiet"] = True

    mock_input_strings = {
        "input_prompt": "prompt content",
        "input_code": "code content",
        "example_code": "example code content"
    }
    mock_output_paths = {
        "output_sub": "/fake_dir/sub_prompt.prompt",
        "output_modified": "/fake_dir/modified_prompt.prompt"
    }
    mock_model_name = "mock_model"

    with patch("pdd.split_main.construct_paths") as mock_construct_paths, \
         patch("pdd.split_main.split") as mock_split, \
         patch("builtins.open", mock_open()):
        mock_construct_paths.return_value = (mock_input_strings, mock_output_paths, None)
        mock_split.return_value = ("extracted functionality", "remaining prompt", mock_model_name, 1.234) # Corrected Mock

        # Call function
        split_main(
            mock_ctx,
            "input_prompt_file.prompt",
            "input_code_file.py",
            "example_code_file.py",
            None,
            None
        )

        # There should be no success message in quiet mode
        captured = capsys.readouterr()
        assert "Successfully split the prompt!" not in captured.out
        assert "Total cost:" not in captured.out
        assert mock_ctx.obj["quiet"] is True
