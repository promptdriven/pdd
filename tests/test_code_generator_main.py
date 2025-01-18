import os
import sys
import pytest
import click.testing
import requests
from unittest.mock import patch, MagicMock, mock_open
from pdd.code_generator_main import code_generator_main

@pytest.fixture
def mock_ctx():
    """
    Creates a reusable Click context fixture with default values in ctx.obj.
    Individual tests can override specific context overrides as needed.
    """
    runner = click.testing.CliRunner()
    with runner.isolated_filesystem():
        # By default, quiet=False so that output messages are printed
        ctx = click.Context(click.Command("generate"))
        ctx.obj = {
            "force": False,
            "quiet": False,
            "strength": 0.5,
            "temperature": 0.0,
            "local": True,  # default to local for brevity, can override
        }
        yield ctx

@patch("pdd.code_generator_main.construct_paths")
@patch("pdd.code_generator_main.code_generator")
def test_local_mode_generates_code(mock_code_generator, mock_construct_paths, mock_ctx):
    """
    Test that code_generator_main generates code in local mode without cloud calls,
    writes output to file when output is specified, and returns correct tuple.
    """
    # Arrange
    mock_construct_paths.return_value = (
        {"prompt_file": "mock prompt content"},
        {"output": "generated_local.py"},
        "python"
    )
    mock_code_generator.return_value = ("generated_code_local", 0.1, "local-model")

    # Act
    generated_code, total_cost, model_name = code_generator_main(
        mock_ctx, "fake_prompt_file.prompt", "my_output.py"
    )

    # Assert
    mock_construct_paths.assert_called_once()
    mock_code_generator.assert_called_once_with(
        "mock prompt content", "python", 0.5, 0.0, verbose=True
    )
    assert generated_code == "generated_code_local"
    assert total_cost == 0.1
    assert model_name == "local-model"

@patch("pdd.code_generator_main.construct_paths")
@patch("pdd.code_generator_main.get_jwt_token")
@patch("pdd.code_generator_main.requests.post")
def test_cloud_mode_generates_code(
    mock_requests_post, mock_get_jwt_token, mock_construct_paths, mock_ctx
):
    """
    Test that code_generator_main generates code in cloud mode, using JWT token
    and calling the remote endpoint, returning the correct tuple.
    """
    # Arrange
    mock_ctx.obj["local"] = False  # force cloud mode
    mock_construct_paths.return_value = (
        {"prompt_file": "cloud prompt content"},
        {"output": "generated_cloud.py"},
        "python"
    )
    mock_get_jwt_token.return_value = "fake_jwt_token"

    # Mock the response from the cloud endpoint
    mock_response = MagicMock()
    mock_response.status_code = 200
    mock_response.json.return_value = {
        "generatedCode": "generated_code_cloud",
        "totalCost": 0.2,
        "modelName": "cloud-model"
    }
    mock_requests_post.return_value = mock_response

    # Act
    generated_code, total_cost, model_name = code_generator_main(
        mock_ctx, "fake_prompt_file.prompt", "my_output_cloud.py"
    )

    # Assert
    mock_construct_paths.assert_called_once()
    mock_get_jwt_token.assert_called_once()
    mock_requests_post.assert_called_once()
    assert generated_code == "generated_code_cloud"
    assert total_cost == 0.2
    assert model_name == "cloud-model"

@patch("pdd.code_generator_main.construct_paths")
@patch("pdd.code_generator_main.code_generator")
@patch("pdd.code_generator_main.requests.post", side_effect=Exception("Cloud failure"))
@patch("pdd.code_generator_main.get_jwt_token", return_value="fake_jwt_token")
def test_cloud_fallback_to_local(
    mock_get_jwt_token,
    mock_requests_post,
    mock_code_generator,
    mock_construct_paths,
    mock_ctx
):
    """
    Test that if the cloud call fails in cloud mode, it falls back to the local code_generator.
    """
    # Arrange
    mock_ctx.obj["local"] = False  # try cloud first
    mock_construct_paths.return_value = (
        {"prompt_file": "fallback prompt content"},
        {"output": "generated_fallback.py"},
        "python"
    )
    mock_code_generator.return_value = ("fallback_code_local", 0.3, "fallback-model")

    # Act
    generated_code, total_cost, model_name = code_generator_main(
        mock_ctx, "some_prompt_file.prompt", "output_fallback.py"
    )

    # Assert
    # The request should have raised an exception, so local code_generator is used.
    mock_code_generator.assert_called_once_with(
        "fallback prompt content", "python", 0.5, 0.0, verbose=True
    )
    assert generated_code == "fallback_code_local"
    assert total_cost == 0.3
    assert model_name == "fallback-model"

@patch("pdd.code_generator_main.construct_paths", side_effect=Exception("Construct paths error"))
def test_exception_handling_exits(mock_construct_paths, mock_ctx):
    """
    Test that code_generator_main exits with sys.exit(1) if any exception occurs during execution.
    """
    with pytest.raises(SystemExit) as exit_info:
        code_generator_main(mock_ctx, "fake_prompt_file.prompt", None)

    assert exit_info.type == SystemExit
    assert exit_info.value.code == 1  # confirm it exits with code 1

@patch("pdd.code_generator_main.construct_paths")
@patch("pdd.code_generator_main.code_generator")
def test_quiet_mode_suppresses_output(mock_code_generator, mock_construct_paths, mock_ctx, capsys):
    """
    Test that when ctx.obj['quiet'] is True, no success or error messages are printed.
    """
    # Arrange
    mock_ctx.obj["quiet"] = True  # suppress output
    mock_construct_paths.return_value = (
        {"prompt_file": "quiet prompt content"},
        {"output": None},
        "python"
    )
    mock_code_generator.return_value = ("quiet_code_local", 0.4, "quiet-model")

    # Act
    generated_code, total_cost, model_name = code_generator_main(
        mock_ctx, "quiet_prompt_file.prompt", None
    )

    # Assert
    captured = capsys.readouterr()
    # Should not contain success messages
    assert "[bold green]Code generation completed successfully." not in captured.out
    assert generated_code == "quiet_code_local"
    assert total_cost == 0.4
    assert model_name == "quiet-model"

@patch("pdd.code_generator_main.construct_paths")
@patch("pdd.code_generator_main.code_generator")
def test_output_file_written(mock_code_generator, mock_construct_paths, mock_ctx, tmp_path):
    """
    Test that an output file is written when provided, containing the generated code.
    """
    # Arrange
    test_output_path = tmp_path / "test_output_file.py"
    mock_construct_paths.return_value = (
        {"prompt_file": "some prompt content"},
        {"output": str(test_output_path)},
        "python"
    )
    mock_code_generator.return_value = ("file_contents_here", 0.55, "test-model")

    # Act
    code_generator_main(
        mock_ctx, "another_fake_prompt_file.prompt", str(test_output_path)
    )

    # Assert
    assert test_output_path.exists()
    with open(test_output_path, "r") as f:
        content = f.read()
    assert "file_contents_here" in content


from unittest.mock import patch, MagicMock
from click.testing import CliRunner



# if output directory does not exist, create it

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
    # Add 'local': True so that we call the local code_generator
    mock_ctx.obj = {'strength': 0.5, 'temperature': 0.0, 'force': False, 'quiet': False, 'local': True}

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
    # Setting local True or not doesn't matter here, but we can keep it for consistency
    mock_ctx.obj = {'strength': 0.5, 'temperature': 0.0, 'force': False, 'quiet': False, 'local': True}

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
    # Must have local=True so the local code_generator is invoked
    mock_ctx.obj = {'strength': 0.5, 'temperature': 0.0, 'force': False, 'quiet': False, 'local': True}

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
    # Here we want quiet=True, but also local=True so that we call code_generator
    mock_ctx.obj = {'strength': 0.5, 'temperature': 0.0, 'force': False, 'quiet': True, 'local': True}

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
    mock_ctx.obj = {'strength': 0.5, 'temperature': 0.0, 'force': False, 'quiet': False, 'local': True}

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