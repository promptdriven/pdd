"""Tests for the auto_deps_main function."""
from unittest.mock import patch, MagicMock
import pytest
import click

# Import DEFAULT_STRENGTH
from pdd import DEFAULT_STRENGTH, DEFAULT_TIME
from pdd.auto_deps_main import auto_deps_main

@pytest.fixture
def mock_ctx():
    """
    Provide a mock for Click's context object.
    """
    ctx = MagicMock(spec=click.Context)
    # Simulate default quiet and force params if not specified otherwise
    ctx.params = {
        'quiet': False,
        'force': False
    }
    ctx.obj = {
        'strength': DEFAULT_STRENGTH,
        'temperature': 0,
        'time': DEFAULT_TIME
    }
    return ctx

@pytest.mark.parametrize("csv_path_return", [None, "custom_deps.csv"])
@patch("pdd.auto_deps_main.construct_paths")
@patch("pdd.auto_deps_main.insert_includes")
@patch("pdd.auto_deps_main.Path")
def test_auto_deps_normal_operation(
    mock_path,  # pylint: disable=unused-argument
    mock_insert_includes,
    mock_construct_paths,
    mock_ctx,  # pylint: disable=redefined-outer-name
    csv_path_return
):
    """
    Test a normal operation of auto_deps_main without force-scan.
    Ensures that construct_paths and insert_includes are called with expected parameters,
    files are written correctly, and the function returns the correct tuple.
    """

    # Arrange
    prompt_file = "sample_prompt_python.prompt"
    directory_path = "context/"
    mock_construct_paths.return_value = (
        {},  # resolved_config
        {"prompt_file": "Contents of prompt file"},
        {
            "output": "output/sample_prompt_python_with_deps.prompt",
            "csv": csv_path_return or "project_dependencies.csv",
        },
        None,
    )
    mock_insert_includes.return_value = (
        "Modified prompt with includes",
        "csv content",
        0.123456,
        "text-davinci-003",
    )

    # Mock Path object
    mock_path_obj = MagicMock()
    mock_path.return_value = mock_path_obj
    mock_path_obj.write_text = MagicMock()
    mock_path_obj.exists.return_value = False

    # Act
    modified_prompt, total_cost, model_name = auto_deps_main(
        ctx=mock_ctx,
        prompt_file=prompt_file,
        directory_path=directory_path,
        auto_deps_csv_path=csv_path_return,
        output=None,
        force_scan=False
    )

    # Assert
    mock_construct_paths.assert_called_once()
    mock_insert_includes.assert_called_once_with(
        input_prompt="Contents of prompt file",
        directory_path=directory_path,
        csv_filename=mock_construct_paths.return_value[2]["csv"],
        prompt_filename=prompt_file,
        strength=mock_ctx.obj["strength"],
        temperature=mock_ctx.obj["temperature"],
        time=mock_ctx.obj["time"],
        verbose=not mock_ctx.params["quiet"],
        progress_callback=None  # No progress callback when called directly
    )
    assert modified_prompt == "Modified prompt with includes"
    assert total_cost == 0.123456
    assert model_name == "text-davinci-003"
    assert mock_path_obj.write_text.call_count == 2
    written_prompt = mock_path_obj.write_text.call_args_list[0][0][0]
    written_csv = mock_path_obj.write_text.call_args_list[1][0][0]
    assert "Modified prompt with includes" in written_prompt
    assert "csv content" in written_csv

@patch("pdd.auto_deps_main.construct_paths")
@patch("pdd.auto_deps_main.insert_includes")
@patch("pdd.auto_deps_main.Path")
def test_auto_deps_force_scan_operation(
    mock_path,  # pylint: disable=unused-argument
    mock_insert_includes,
    mock_construct_paths,
    mock_ctx  # pylint: disable=redefined-outer-name
):
    """
    Test the operation of auto_deps_main when force-scan is True.
    Ensures that an existing CSV file is removed before processing.
    """
    # Arrange
    prompt_file = "another_prompt_python.prompt"
    directory_path = "context/"
    mock_construct_paths.return_value = (
        {},  # resolved_config
        {"prompt_file": "Contents of prompt file"},
        {
            "output": "output/another_prompt_python_with_deps.prompt",
            "csv": "forced_scan_deps.csv",
        },
        None,
    )
    mock_insert_includes.return_value = (
        "Modified prompt after force scan",
        "csv content for forced scan",
        0.111111,
        "gpt-4",
    )

    mock_path_obj = MagicMock()
    mock_path.return_value = mock_path_obj
    mock_path_obj.exists.return_value = True
    mock_path_obj.write_text = MagicMock()

    # Act
    modified_prompt, total_cost, model_name = auto_deps_main(
        ctx=mock_ctx,
        prompt_file=prompt_file,
        directory_path=directory_path,
        auto_deps_csv_path=None,
        output="output/here",
        force_scan=True
    )

    # Assert
    mock_path_obj.unlink.assert_called_once()

    mock_construct_paths.assert_called_once()
    mock_insert_includes.assert_called_once_with(
        input_prompt="Contents of prompt file",
        directory_path=directory_path,
        csv_filename="forced_scan_deps.csv",
        prompt_filename=prompt_file,
        strength=mock_ctx.obj["strength"],
        temperature=mock_ctx.obj["temperature"],
        time=mock_ctx.obj["time"],
        verbose=not mock_ctx.params["quiet"],
        progress_callback=None  # No progress callback when called directly
    )
    assert modified_prompt == "Modified prompt after force scan"
    assert total_cost == 0.111111
    assert model_name == "gpt-4"

@patch("pdd.auto_deps_main.construct_paths")
@patch("pdd.auto_deps_main.insert_includes")
@patch("pdd.auto_deps_main.Path")
def test_auto_deps_handles_error_scenario(
    mock_path,  # pylint: disable=unused-argument
    mock_insert_includes,
    mock_construct_paths,
    mock_ctx  # pylint: disable=redefined-outer-name
):
    """
    Test that auto_deps_main returns an error tuple when an exception is raised.
    Per the spec, errors should return ("", 0.0, "Error: {exc}") to allow
    the orchestrator to handle failures gracefully.
    """
    # Arrange
    mock_construct_paths.side_effect = Exception("Test exception")

    # Act
    modified_prompt, total_cost, model_name = auto_deps_main(
        ctx=mock_ctx,
        prompt_file="bad_prompt_file.prompt",
        directory_path="context/",
        auto_deps_csv_path=None,
        output=None,
        force_scan=False
    )

    # Assert - should return error tuple instead of raising
    assert modified_prompt == ""
    assert total_cost == 0.0
    assert "Error:" in model_name
    assert "Test exception" in model_name
    mock_insert_includes.assert_not_called()

@patch("pdd.auto_deps_main.construct_paths")
@patch("pdd.auto_deps_main.insert_includes")
@patch("pdd.auto_deps_main.Path")
def test_auto_deps_reraises_click_abort(
    mock_path,  # pylint: disable=unused-argument
    mock_insert_includes,
    mock_construct_paths,
    mock_ctx  # pylint: disable=redefined-outer-name
):
    """
    Test that auto_deps_main re-raises click.Abort to allow the orchestrator
    to stop the sync loop when the user cancels.
    """
    # Arrange
    mock_construct_paths.side_effect = click.Abort()

    # Act / Assert - click.Abort should be re-raised, not caught
    with pytest.raises(click.Abort):
        auto_deps_main(
            ctx=mock_ctx,
            prompt_file="cancelled_prompt.prompt",
            directory_path="context/",
            auto_deps_csv_path=None,
            output=None,
            force_scan=False
        )
    mock_insert_includes.assert_not_called()