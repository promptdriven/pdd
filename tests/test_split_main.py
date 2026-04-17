# File: tests/test_split_main.py
#
# Test Plan:
# 1. test_split_main_success - Success path with quiet=False and quiet=True (parametrized)
# 2. test_split_main_file_not_found - FileNotFoundError handling with hint
# 3. test_split_main_io_error_during_write - IOError during file write with hint
# 4. test_split_main_value_error - ValueError handling with hint
# 5. test_split_main_quiet_mode - Quiet mode suppresses success output
# 6. test_split_forwards_strength_temperature_time - split called with correct ctx.obj params
# 7. test_split_main_default_ctx_values - Defaults for missing ctx.obj keys (strength=0.5, temperature=0, time=None)
# 8. test_split_main_custom_output_paths - output_sub/output_modified forwarded in command_options
# 9. test_split_main_context_override - context_override passed to construct_paths
# 10. test_split_main_legacy_param_accepted - legacy parameter accepted without error
# 11. test_split_main_return_paths_from_output_file_paths - Return dict paths come from output_file_paths
# 12. test_split_main_error_quiet_suppresses_output - Errors in quiet mode produce no output
# 13. test_split_main_generic_exception - Non-specific exceptions exit(1) without specific hint
# 14. test_split_main_verbose_forwarded_to_split - verbose=not quiet forwarded to split

import pytest
import sys
from unittest.mock import patch, mock_open, MagicMock, call
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
        mock_construct_paths.return_value = ({}, mock_input_strings, mock_output_paths, mock_language)
        # Use standardized return order (result_data, cost, model_name)
        mock_split.return_value = ((extracted_functionality_result, remaining_prompt_result), total_cost_result, mock_model_name)

        # Act
        result_data, total_cost, model_name = split_main(
            mock_ctx,
            "input_prompt_file.prompt",
            "input_code_file.py",
            "example_code_file.py",
            None,
            None
        )

        # Assert that we get the expected dictionary with file paths and content
        assert "sub_prompt_content" in result_data
        assert "modified_prompt_content" in result_data
        assert "output_sub" in result_data
        assert "output_modified" in result_data
        assert result_data["sub_prompt_content"] == extracted_functionality_result
        assert result_data["modified_prompt_content"] == remaining_prompt_result
        assert total_cost == total_cost_result
        assert model_name == mock_model_name


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

        mock_construct_paths.return_value = ({}, mock_input_strings, mock_output_paths, mock_language)
        # Use standardized return order (result_data, cost, model_name)
        mock_split.return_value = (("extracted functionality", "remaining prompt"), 0.5, mock_model_name)

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
            {},  # resolved_config
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
        mock_construct_paths.return_value = ({}, mock_input_strings, mock_output_paths, None)
        # Use standardized return order (result_data, cost, model_name)
        mock_split.return_value = (("extracted functionality", "remaining prompt"), 1.234, mock_model_name)

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


def _make_success_mocks():
    """Helper to create standard mock return values for construct_paths and split."""
    input_strings = {
        "input_prompt": "prompt content",
        "input_code": "code content",
        "example_code": "example code content",
    }
    output_paths = {
        "output_sub": "/fake_dir/sub_prompt.prompt",
        "output_modified": "/fake_dir/modified_prompt.prompt",
    }
    return input_strings, output_paths


def test_split_forwards_strength_temperature_time(mock_ctx):
    """Test that strength, temperature, and time from ctx.obj are forwarded to split."""
    mock_ctx.obj["strength"] = 0.8
    mock_ctx.obj["temperature"] = 0.3
    mock_ctx.obj["time"] = 0.75
    mock_ctx.obj["quiet"] = True

    input_strings, output_paths = _make_success_mocks()

    with patch("pdd.split_main.construct_paths") as mock_cp, \
         patch("pdd.split_main.split") as mock_split, \
         patch("builtins.open", mock_open()):
        mock_cp.return_value = ({}, input_strings, output_paths, "python")
        mock_split.return_value = (("sub", "mod"), 0.01, "model-x")

        split_main(mock_ctx, "p.prompt", "c.py", "e.py", None, None)

        _, kwargs = mock_split.call_args
        assert kwargs["strength"] == 0.8
        assert kwargs["temperature"] == 0.3
        assert kwargs["time"] == 0.75


def test_split_main_default_ctx_values():
    """Test that missing ctx.obj keys use correct defaults: strength=0.5, temperature=0, time=None."""
    ctx = MagicMock(spec=click.Context)
    ctx.obj = {}  # Empty - all defaults should be used

    input_strings, output_paths = _make_success_mocks()

    with patch("pdd.split_main.construct_paths") as mock_cp, \
         patch("pdd.split_main.split") as mock_split, \
         patch("builtins.open", mock_open()):
        mock_cp.return_value = ({}, input_strings, output_paths, "python")
        mock_split.return_value = (("sub", "mod"), 0.0, "model")

        split_main(ctx, "p.prompt", "c.py", "e.py", None, None)

        _, kwargs = mock_split.call_args
        assert kwargs["strength"] == 0.5
        assert kwargs["temperature"] == 0
        assert kwargs["time"] is None
        assert kwargs["verbose"] is True  # not quiet (default False) -> verbose True


def test_split_main_custom_output_paths(mock_ctx):
    """Test that custom output_sub and output_modified are passed in command_options."""
    mock_ctx.obj["quiet"] = True
    input_strings, output_paths = _make_success_mocks()

    with patch("pdd.split_main.construct_paths") as mock_cp, \
         patch("pdd.split_main.split") as mock_split, \
         patch("builtins.open", mock_open()):
        mock_cp.return_value = ({}, input_strings, output_paths, "python")
        mock_split.return_value = (("sub", "mod"), 0.0, "model")

        split_main(
            mock_ctx, "p.prompt", "c.py", "e.py",
            output_sub="/custom/sub.prompt",
            output_modified="/custom/modified.prompt",
        )

        _, kwargs = mock_cp.call_args
        assert kwargs["command_options"] == {
            "output_sub": "/custom/sub.prompt",
            "output_modified": "/custom/modified.prompt",
        }


def test_split_main_context_override(mock_ctx):
    """Test that context from ctx.obj is forwarded as context_override to construct_paths."""
    mock_ctx.obj["quiet"] = True
    mock_ctx.obj["context"] = "backend"
    input_strings, output_paths = _make_success_mocks()

    with patch("pdd.split_main.construct_paths") as mock_cp, \
         patch("pdd.split_main.split") as mock_split, \
         patch("builtins.open", mock_open()):
        mock_cp.return_value = ({}, input_strings, output_paths, "python")
        mock_split.return_value = (("sub", "mod"), 0.0, "model")

        split_main(mock_ctx, "p.prompt", "c.py", "e.py", None, None)

        _, kwargs = mock_cp.call_args
        assert kwargs["context_override"] == "backend"


def test_split_main_accepts_basic_args(mock_ctx):
    """Test that split_main works with standard arguments (legacy param removed)."""
    mock_ctx.obj["quiet"] = True
    input_strings, output_paths = _make_success_mocks()

    with patch("pdd.split_main.construct_paths") as mock_cp, \
         patch("pdd.split_main.split") as mock_split, \
         patch("builtins.open", mock_open()):
        mock_cp.return_value = ({}, input_strings, output_paths, "python")
        mock_split.return_value = (("sub", "mod"), 0.0, "model")

        result_data, cost, model = split_main(
            mock_ctx, "p.prompt", "c.py", "e.py", None, None,
        )
        assert isinstance(result_data, dict)
        assert isinstance(cost, float)
        assert isinstance(model, str)


def test_split_main_return_paths_from_output_file_paths(mock_ctx):
    """Test that returned dict paths come from output_file_paths, not from input args."""
    mock_ctx.obj["quiet"] = True
    input_strings, _ = _make_success_mocks()
    custom_output_paths = {
        "output_sub": "/resolved/path/sub.prompt",
        "output_modified": "/resolved/path/modified.prompt",
    }

    with patch("pdd.split_main.construct_paths") as mock_cp, \
         patch("pdd.split_main.split") as mock_split, \
         patch("builtins.open", mock_open()):
        mock_cp.return_value = ({}, input_strings, custom_output_paths, "python")
        mock_split.return_value = (("sub_content", "mod_content"), 0.05, "gpt-4")

        result_data, cost, model = split_main(
            mock_ctx, "p.prompt", "c.py", "e.py", None, None,
        )

        assert result_data["output_sub"] == "/resolved/path/sub.prompt"
        assert result_data["output_modified"] == "/resolved/path/modified.prompt"
        assert result_data["sub_prompt_content"] == "sub_content"
        assert result_data["modified_prompt_content"] == "mod_content"
        assert cost == 0.05
        assert model == "gpt-4"


def test_split_main_error_quiet_suppresses_output(mock_ctx, capsys):
    """Test that errors in quiet mode produce no console output."""
    mock_ctx.obj["quiet"] = True

    with patch("pdd.split_main.construct_paths", side_effect=RuntimeError("boom")), \
         pytest.raises(SystemExit) as exc_info:
        split_main(mock_ctx, "p.prompt", "c.py", "e.py", None, None)

    assert exc_info.value.code == 1
    captured = capsys.readouterr()
    assert "Error:" not in captured.out
    assert "boom" not in captured.out


def test_split_main_generic_exception(mock_ctx, capsys):
    """Test that a non-specific exception exits with code 1 and no specific hint."""
    with patch("pdd.split_main.construct_paths", side_effect=RuntimeError("unexpected")), \
         pytest.raises(SystemExit) as exc_info:
        split_main(mock_ctx, "p.prompt", "c.py", "e.py", None, None)

    assert exc_info.value.code == 1
    captured = capsys.readouterr()
    assert "Error:" in captured.out
    assert "unexpected" in captured.out
    # No specific hint for RuntimeError
    assert "Hint:" not in captured.out


def test_split_main_verbose_forwarded_to_split(mock_ctx):
    """Test verbose=not quiet is correctly forwarded to split for both quiet values."""
    input_strings, output_paths = _make_success_mocks()

    for quiet_val, expected_verbose in [(False, True), (True, False)]:
        mock_ctx.obj["quiet"] = quiet_val

        with patch("pdd.split_main.construct_paths") as mock_cp, \
             patch("pdd.split_main.split") as mock_split, \
             patch("builtins.open", mock_open()):
            mock_cp.return_value = ({}, input_strings, output_paths, "python")
            mock_split.return_value = (("sub", "mod"), 0.0, "model")

            split_main(mock_ctx, "p.prompt", "c.py", "e.py", None, None)

            _, kwargs = mock_split.call_args
            assert kwargs["verbose"] == expected_verbose
