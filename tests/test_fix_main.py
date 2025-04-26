import pytest
import sys
from unittest.mock import patch, MagicMock, mock_open, call # Import call
import click
from click import Context, UsageError
from rich.console import Console
from pathlib import Path # Import Path

# Import DEFAULT_STRENGTH
from pdd import DEFAULT_STRENGTH

# Since the code under test is in pdd/fix_main.py, we import the fix_main function here:
from pdd.fix_main import fix_main

# create the output directory if it does not exist
import os
os.makedirs("output", exist_ok=True)
# Create results directory if it doesn't exist, needed for file writing mocks/assertions
os.makedirs("results", exist_ok=True)


@pytest.fixture
def mock_ctx():
    """
    Pytest fixture to create a mock Click context object with default parameters.
    You can override params or obj fields in specific tests if needed.
    """
    ctx = MagicMock(spec=Context)

    # Mimic ctx.obj with default values
    ctx.obj = {
        'force': False,
        'quiet': False,
        'strength': DEFAULT_STRENGTH,
        'temperature': 0.0,
        'verbose': False # Add verbose default
    }
    return ctx

# Patch Path.exists for tests where error_file check happens before construct_paths
@patch('pdd.fix_main.Path') # Patch Path where it's used in fix_main
@patch('pdd.fix_main.construct_paths')
@patch('pdd.fix_main.fix_error_loop')
@patch('pdd.fix_main.fix_errors_from_unit_tests')
def test_fix_main_without_loop(
    mock_fix_errors_from_unit_tests,
    mock_fix_error_loop,
    mock_construct_paths,
    mock_path, # Add mock_path fixture
    mock_ctx
):
    """
    Test that calling fix_main without the loop option uses fix_errors_from_unit_tests
    and saves the outputs correctly.
    """
    # Arrange
    # Configure the mock Path object's exists method
    # Ensure Path('errors.log').exists() returns True
    mock_path_instance = mock_path.return_value
    mock_path_instance.exists.return_value = True

    mock_construct_paths.return_value = (
        {
            'prompt_file': 'Test prompt file content',
            'code_file': 'Test code file content',
            'unit_test_file': 'Test unit test file content',
            'error_file': 'Error message content'
        },
        {
            'output_test': 'output/test_code_fixed.py',
            'output_code': 'output/code_fixed.py',
            'output_results': 'results/fix_results.log'
        },
        None
    )

    # fix_errors_from_unit_tests mock return
    mock_fix_errors_from_unit_tests.return_value = (
        True,  # update_unit_test
        False, # update_code
        "Fixed unit test content",
        "",
        "Analysis results",
        0.75,  # total_cost
        "gpt-4"
    )

    # Use mock_open for file writing assertions
    m_open = mock_open()
    with patch('builtins.open', m_open):
        # Act
        success, fixed_test, fixed_code, attempts, total_cost, model_name = fix_main(
            ctx=mock_ctx,
            prompt_file="prompt_file.prompt",
            code_file="code_file.py",
            unit_test_file="test_code_file.py",
            error_file="errors.log",
            output_test=None,
            output_code=None,
            output_results=None,
            loop=False,
            verification_program=None,
            max_attempts=3,
            budget=5.0,
            auto_submit=False
        )

    # Assert
    mock_fix_error_loop.assert_not_called()
    mock_fix_errors_from_unit_tests.assert_called_once()
    # Check construct_paths call includes create_error_file=False
    mock_construct_paths.assert_called_once_with(
        input_file_paths={
            'prompt_file': 'prompt_file.prompt',
            'code_file': 'code_file.py',
            'unit_test_file': 'test_code_file.py',
            'error_file': 'errors.log',
        },
        force=False,
        quiet=False,
        command='fix',
        command_options={
            'output_test': None,
            'output_code': None,
            'output_results': None
        },
        create_error_file=False # Explicitly check this argument
    )
    assert success is True
    assert fixed_test == "Fixed unit test content"
    assert fixed_code == ""
    assert attempts == 1
    assert total_cost == 0.75
    assert model_name == "gpt-4"

    # Assert file writing
    m_open.assert_called_once_with('output/test_code_fixed.py', 'w')
    handle = m_open()
    handle.write.assert_called_once_with("Fixed unit test content")


@patch('pdd.fix_main.construct_paths')
@patch('pdd.fix_main.fix_error_loop')
@patch('pdd.fix_main.fix_errors_from_unit_tests')
def test_fix_main_with_loop(
    mock_fix_errors_from_unit_tests,
    mock_fix_error_loop,
    mock_construct_paths,
    mock_ctx
):
    """
    Test that calling fix_main with the loop option uses fix_error_loop
    and properly handles the returned values.
    """
    # Arrange
    # No need to patch Path.exists here as the check is skipped when loop=True

    mock_construct_paths.return_value = (
        {
            'prompt_file': 'Test prompt file content',
            'code_file': 'Test code file content',
            'unit_test_file': 'Test unit test file content'
            # error_file is not included when loop=True before construct_paths
        },
        {
            'output_test': 'output/test_code_fixed.py',
            'output_code': 'output/code_fixed.py',
            'output_results': 'results/fix_results.log'
        },
        None
    )

    # fix_error_loop mock return
    mock_fix_error_loop.return_value = (
        True,                   # success
        "Iteratively fixed test",
        "Iteratively fixed code",
        2,                      # attempts
        1.25,                   # total_cost
        "gpt-4-loop"
    )

    # Use mock_open for file writing assertions
    m_open = mock_open()
    with patch('builtins.open', m_open):
        # Act
        success, fixed_test, fixed_code, attempts, total_cost, model_name = fix_main(
            ctx=mock_ctx,
            prompt_file="prompt_file.prompt",
            code_file="code_file.py",
            unit_test_file="test_code_file.py",
            error_file="errors.log",  # This should not matter when loop=True
            output_test=None,
            output_code=None,
            output_results=None,
            loop=True,
            verification_program="verify.py",
            max_attempts=3,
            budget=5.0,
            auto_submit=False
        )

    # Assert
    mock_fix_errors_from_unit_tests.assert_not_called()
    mock_fix_error_loop.assert_called_once()
    # Update assertion to include create_error_file=True
    mock_construct_paths.assert_called_once_with(
        input_file_paths={
            'prompt_file': 'prompt_file.prompt',
            'code_file': 'code_file.py',
            'unit_test_file': 'test_code_file.py'
            # error_file is not in input_file_paths dict when loop=True
        },
        force=False,
        quiet=False,
        command='fix',
        command_options={
            'output_test': None,
            'output_code': None,
            'output_results': None
        },
        create_error_file=True # Add this expected argument
    )
    assert success is True
    assert fixed_test == "Iteratively fixed test"
    assert fixed_code == "Iteratively fixed code"
    assert attempts == 2
    assert total_cost == 1.25
    assert model_name == "gpt-4-loop"

    # Assert file writing calls
    expected_calls = [
        call('output/test_code_fixed.py', 'w'),
        call('output/code_fixed.py', 'w')
    ]
    m_open.assert_has_calls(expected_calls, any_order=True)
    handle_test = m_open()
    handle_code = m_open()
    # Check write calls - order might vary depending on dict iteration
    write_calls = [call("Iteratively fixed test"), call("Iteratively fixed code")]
    handle_test.write.assert_has_calls(write_calls, any_order=True)


def test_fix_main_loop_requires_verification_program(mock_ctx):
    """
    Test that calling fix_main with loop=True but no verification_program
    raises a click.UsageError.
    """
    # No file system interaction here, no need to patch Path
    with pytest.raises(UsageError):
        fix_main(
            ctx=mock_ctx,
            prompt_file="prompt_file.prompt",
            code_file="code_file.py",
            unit_test_file="test_code_file.py",
            error_file="errors.log",
            output_test=None,
            output_code=None,
            output_results=None,
            loop=True,
            verification_program=None,
            max_attempts=3,
            budget=5.0,
            auto_submit=False
        )

# Patch Path.exists for this test as well
@patch('pdd.fix_main.Path') # Patch Path where it's used in fix_main
@patch('pdd.fix_main.construct_paths', side_effect=Exception("Construct paths failed"))
def test_fix_main_handles_exception_and_exits(mocked_construct_paths, mock_path, mock_ctx): # Add mock_path
    """
    Test that fix_main handles an exception from construct_paths, prints an error,
    and calls sys.exit(1).
    """
    # Arrange
    # Configure the mock Path object's exists method to return True
    mock_path_instance = mock_path.return_value
    mock_path_instance.exists.return_value = True
    mock_ctx.obj['quiet'] = False  # so we can see the printed error

    # Act & Assert
    with pytest.raises(SystemExit) as sys_exit:
        fix_main(
            ctx=mock_ctx,
            prompt_file="prompt_file.prompt",
            code_file="code_file.py",
            unit_test_file="test_code_file.py",
            error_file="errors.log", # This check will now pass
            output_test=None,
            output_code=None,
            output_results=None,
            loop=False,
            verification_program=None,
            max_attempts=3,
            budget=5.0,
            auto_submit=False
        )
    assert sys_exit.type == SystemExit
    assert sys_exit.value.code == 1

    # Now construct_paths should be called because Path.exists returned True
    mocked_construct_paths.assert_called_once()
    # Check that Path('errors.log').exists() was called
    mock_path.assert_called_once_with('errors.log')
    mock_path_instance.exists.assert_called_once()