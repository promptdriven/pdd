import pytest
import sys
from unittest.mock import patch, MagicMock, mock_open
import click
from click import Context, UsageError
from rich.console import Console

# Since the code under test is in pdd/fix_main.py, we import the fix_main function here:
from pdd.fix_main import fix_main

# create the output directory if it does not exist
import os
os.makedirs("output", exist_ok=True)


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
        'strength': 0.9,
        'temperature': 0.0
    }
    return ctx

@patch('pdd.fix_main.construct_paths')
@patch('pdd.fix_main.fix_error_loop')
@patch('pdd.fix_main.fix_errors_from_unit_tests')
def test_fix_main_without_loop(
    mock_fix_errors_from_unit_tests,
    mock_fix_error_loop,
    mock_construct_paths,
    mock_ctx
):
    """
    Test that calling fix_main without the loop option uses fix_errors_from_unit_tests
    and saves the outputs correctly.
    """
    # Arrange
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
        }
    )
    assert success is True
    assert fixed_test == "Fixed unit test content"
    assert fixed_code == ""
    assert attempts == 1
    assert total_cost == 0.75
    assert model_name == "gpt-4"

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
    mock_construct_paths.return_value = (
        {
            'prompt_file': 'Test prompt file content',
            'code_file': 'Test code file content',
            'unit_test_file': 'Test unit test file content'
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
    mock_construct_paths.assert_called_once_with(
        input_file_paths={
            'prompt_file': 'prompt_file.prompt',
            'code_file': 'code_file.py',
            'unit_test_file': 'test_code_file.py'
        },
        force=False,
        quiet=False,
        command='fix',
        command_options={
            'output_test': None,
            'output_code': None,
            'output_results': None
        }
    )
    assert success is True
    assert fixed_test == "Iteratively fixed test"
    assert fixed_code == "Iteratively fixed code"
    assert attempts == 2
    assert total_cost == 1.25
    assert model_name == "gpt-4-loop"

def test_fix_main_loop_requires_verification_program(mock_ctx):
    """
    Test that calling fix_main with loop=True but no verification_program
    raises a click.UsageError.
    """
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

@patch('pdd.fix_main.construct_paths', side_effect=Exception("Construct paths failed"))
def test_fix_main_handles_exception_and_exits(mocked_construct_paths, mock_ctx):
    """
    Test that fix_main handles an exception, prints an error (unless quiet=True),
    and calls sys.exit(1).
    """
    mock_ctx.obj['quiet'] = False  # so we can see the printed error
    with pytest.raises(SystemExit) as sys_exit:
        fix_main(
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
    assert sys_exit.type == SystemExit
    assert sys_exit.value.code == 1

    # We can't easily capture rprint output without extra setup, so we just confirm sys.exit was raised.
    mocked_construct_paths.assert_called_once()