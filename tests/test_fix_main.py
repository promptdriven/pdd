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
        'verbose': False,
        'time': None,
        'context': None,
        'confirm_callback': None
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
    # Configure the mock Path to return real Path objects for output paths,
    # but allow controlling exists() for error.log
    from pathlib import Path as RealPath

    def path_side_effect(path_str):
        real_path = RealPath(path_str)
        # For error.log, return a mock with controlled exists()
        if 'errors.log' in str(path_str):
            mock_error_path = MagicMock(spec=RealPath)
            mock_error_path.exists.return_value = True
            return mock_error_path
        # For other paths, return real Path objects
        return real_path

    mock_path.side_effect = path_side_effect

    mock_construct_paths.return_value = (
        {},  # resolved_config
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
        create_error_file=False,
        context_override=None,
        confirm_callback=None
    )
    assert success is True
    assert fixed_test == "Fixed unit test content"
    assert fixed_code == ""
    assert attempts == 1
    assert total_cost == 0.75
    assert model_name == "gpt-4"

    # Assert file writing - fix_main now uses Path objects
    from pathlib import Path as PathLib
    m_open.assert_called_once_with(PathLib('output/test_code_fixed.py'), 'w')
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
        {},  # resolved_config
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
        create_error_file=True,
        context_override=None,
        confirm_callback=None
    )
    assert success is True
    assert fixed_test == "Iteratively fixed test"
    assert fixed_code == "Iteratively fixed code"
    assert attempts == 2
    assert total_cost == 1.25
    assert model_name == "gpt-4-loop"

    # Assert file writing calls - fix_main now uses Path objects
    from pathlib import Path as PathLib
    expected_calls = [
        call(PathLib('output/test_code_fixed.py'), 'w'),
        call(PathLib('output/code_fixed.py'), 'w')
    ]
    m_open.assert_has_calls(expected_calls, any_order=True)
    handle = m_open()
    # Check write calls - order might vary depending on dict iteration
    write_calls = [call("Iteratively fixed test"), call("Iteratively fixed code")]
    handle.write.assert_has_calls(write_calls, any_order=True)


@patch('pdd.fix_main.construct_paths')
@patch('pdd.fix_main.fix_error_loop')
def test_fix_main_passes_agentic_fallback_to_fix_error_loop(
    mock_fix_error_loop,
    mock_construct_paths,
    mock_ctx
):
    """
    Test that fix_main passes agentic_fallback parameter to fix_error_loop
    as specified in the prompt.
    """
    # Arrange
    mock_construct_paths.return_value = (
        {},  # resolved_config
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

    mock_fix_error_loop.return_value = (
        True,
        "Fixed test",
        "Fixed code",
        1,
        0.5,
        "gpt-4"
    )

    m_open = mock_open()
    with patch('builtins.open', m_open):
        # Act - call with agentic_fallback=False (non-default)
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
            verification_program="verify.py",
            max_attempts=3,
            budget=5.0,
            auto_submit=False,
            agentic_fallback=False  # Explicitly set to False
        )

    # Assert - verify agentic_fallback was passed to fix_error_loop
    mock_fix_error_loop.assert_called_once()
    call_kwargs = mock_fix_error_loop.call_args.kwargs
    assert 'agentic_fallback' in call_kwargs
    assert call_kwargs['agentic_fallback'] is False


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


@patch('pdd.fix_main.Path')
def test_fix_main_error_file_not_found_in_non_loop_mode(mock_path, mock_ctx):
    """
    Test that fix_main returns an error tuple when error_file doesn't exist
    in non-loop mode, as per spec: 'pre-validate the provided error_file exists
    before constructing paths'.
    """
    # Arrange - configure Path to report file doesn't exist
    mock_path_instance = mock_path.return_value
    mock_path_instance.exists.return_value = False

    # Act
    success, fixed_test, fixed_code, attempts, total_cost, model_name = fix_main(
        ctx=mock_ctx,
        prompt_file="prompt_file.prompt",
        code_file="code_file.py",
        unit_test_file="test_code_file.py",
        error_file="nonexistent_errors.log",
        output_test=None,
        output_code=None,
        output_results=None,
        loop=False,
        verification_program=None,
        max_attempts=3,
        budget=5.0,
        auto_submit=False
    )

    # Assert - should return error tuple with FileNotFoundError message
    assert success is False
    assert fixed_test == ""
    assert fixed_code == ""
    assert attempts == 0
    assert total_cost == 0.0
    assert "Error:" in model_name
    assert "nonexistent_errors.log" in model_name or "does not exist" in model_name

    # Verify Path was called to check existence
    mock_path.assert_called_once_with('nonexistent_errors.log')
    mock_path_instance.exists.assert_called_once()


@patch('pdd.fix_main.Path')
@patch('pdd.fix_main.construct_paths', side_effect=click.Abort())
def test_fix_main_reraises_click_abort(mock_construct_paths, mock_path, mock_ctx):
    """
    Test that fix_main re-raises click.Abort without catching it, allowing
    orchestrators (TUI/CLI) to handle user cancellation gracefully.
    """
    # Arrange - configure Path to report file exists (so we get past the check)
    mock_path_instance = mock_path.return_value
    mock_path_instance.exists.return_value = True

    # Act & Assert - click.Abort should be re-raised, not caught
    with pytest.raises(click.Abort):
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


# Patch Path.exists for this test as well
@patch('pdd.fix_main.Path') # Patch Path where it's used in fix_main
@patch('pdd.fix_main.construct_paths', side_effect=Exception("Construct paths failed"))
def test_fix_main_handles_exception_returns_error_tuple(mocked_construct_paths, mock_path, mock_ctx):
    """
    Test that fix_main handles an exception from construct_paths and returns
    an error tuple instead of calling sys.exit(1), allowing orchestrators to
    handle failures gracefully.
    """
    # Arrange
    # Configure the mock Path object's exists method to return True
    mock_path_instance = mock_path.return_value
    mock_path_instance.exists.return_value = True
    mock_ctx.obj['quiet'] = False  # so we can see the printed error

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

    # Assert - should return error tuple per spec
    assert success is False
    assert fixed_test == ""
    assert fixed_code == ""
    assert attempts == 0
    assert total_cost == 0.0
    assert model_name.startswith("Error:")
    assert "Construct paths failed" in model_name

    # Now construct_paths should be called because Path.exists returned True
    mocked_construct_paths.assert_called_once()
    # Check that Path('errors.log').exists() was called
    mock_path.assert_called_once_with('errors.log')
    mock_path_instance.exists.assert_called_once()


# ============================================================================
# Tests for actual business logic (not just mock wiring)
# ============================================================================

@patch('pdd.fix_main.Path')
@patch('pdd.fix_main.construct_paths')
@patch('pdd.fix_main.fix_errors_from_unit_tests')
def test_fix_main_success_is_false_when_no_updates(
    mock_fix_errors,
    mock_construct_paths,
    mock_path,
    mock_ctx
):
    """
    Test that success is False when fix_errors_from_unit_tests returns
    update_unit_test=False AND update_code=False.
    This tests the actual logic: success = update_unit_test or update_code
    """
    # Arrange
    mock_path.return_value.exists.return_value = True

    mock_construct_paths.return_value = (
        {},
        {
            'prompt_file': 'prompt content',
            'code_file': 'code content',
            'unit_test_file': 'test content',
            'error_file': 'error content'
        },
        {
            'output_test': 'output/test.py',
            'output_code': 'output/code.py',
            'output_results': 'results/results.log'
        },
        None
    )

    # Both update flags are False - no fix was made
    mock_fix_errors.return_value = (
        False,  # update_unit_test
        False,  # update_code
        "",     # fixed_unit_test (empty)
        "",     # fixed_code (empty)
        "No changes needed",
        0.50,
        "gpt-4"
    )

    # Act
    success, fixed_test, fixed_code, attempts, total_cost, model_name = fix_main(
        ctx=mock_ctx,
        prompt_file="prompt.prompt",
        code_file="code.py",
        unit_test_file="test.py",
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

    # Assert - success should be False because neither update flag was True
    assert success is False
    assert attempts == 1  # Still counted as 1 attempt
    assert total_cost == 0.50
    assert model_name == "gpt-4"


@patch('pdd.fix_main.Path')
@patch('pdd.fix_main.construct_paths')
@patch('pdd.fix_main.fix_errors_from_unit_tests')
def test_fix_main_success_when_only_code_updated(
    mock_fix_errors,
    mock_construct_paths,
    mock_path,
    mock_ctx
):
    """
    Test that success is True when only update_code=True (update_unit_test=False).
    Verifies the OR logic: success = update_unit_test or update_code
    """
    mock_path.return_value.exists.return_value = True

    mock_construct_paths.return_value = (
        {},
        {
            'prompt_file': 'prompt',
            'code_file': 'code',
            'unit_test_file': 'test',
            'error_file': 'error'
        },
        {
            'output_test': 'output/test.py',
            'output_code': 'output/code.py',
            'output_results': 'results/results.log'
        },
        None
    )

    # Only code was updated, not the test
    mock_fix_errors.return_value = (
        False,  # update_unit_test
        True,   # update_code
        "",     # fixed_unit_test (empty - not updated)
        "fixed code content",
        "Fixed the code",
        0.60,
        "gpt-4"
    )

    m_open = mock_open()
    with patch('builtins.open', m_open):
        success, fixed_test, fixed_code, attempts, total_cost, model_name = fix_main(
            ctx=mock_ctx,
            prompt_file="prompt.prompt",
            code_file="code.py",
            unit_test_file="test.py",
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
    assert success is True  # True because update_code was True
    assert fixed_test == ""
    assert fixed_code == "fixed code content"

    # Verify only code file was written (not test file since it's empty)
    from pathlib import Path as PathLib
    m_open.assert_called_once_with(PathLib('output/code.py'), 'w')


@patch('pdd.fix_main.Path')
@patch('pdd.fix_main.construct_paths')
@patch('pdd.fix_main.fix_errors_from_unit_tests')
def test_fix_main_does_not_write_empty_files(
    mock_fix_errors,
    mock_construct_paths,
    mock_path,
    mock_ctx
):
    """
    Test that fix_main does NOT write files when fixed content is empty.
    Spec: 'Write fixed files only when the corresponding fixed content is non-empty.'
    """
    mock_path.return_value.exists.return_value = True

    mock_construct_paths.return_value = (
        {},
        {
            'prompt_file': 'prompt',
            'code_file': 'code',
            'unit_test_file': 'test',
            'error_file': 'error'
        },
        {
            'output_test': 'output/test.py',
            'output_code': 'output/code.py',
            'output_results': 'results/results.log'
        },
        None
    )

    # Both fixed contents are empty strings
    mock_fix_errors.return_value = (
        False,  # update_unit_test
        False,  # update_code
        "",     # fixed_unit_test (empty)
        "",     # fixed_code (empty)
        "Analysis",
        0.25,
        "gpt-4"
    )

    m_open = mock_open()
    with patch('builtins.open', m_open):
        fix_main(
            ctx=mock_ctx,
            prompt_file="prompt.prompt",
            code_file="code.py",
            unit_test_file="test.py",
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

    # Assert - open should NOT have been called since both contents are empty
    m_open.assert_not_called()


@patch('pdd.fix_main.construct_paths')
@patch('pdd.fix_main.fix_error_loop')
def test_fix_main_passes_time_to_fix_error_loop(
    mock_fix_error_loop,
    mock_construct_paths,
    mock_ctx
):
    """
    Test that the time parameter from context is passed to fix_error_loop.
    """
    # Set a specific time value in context
    mock_ctx.obj['time'] = 120

    mock_construct_paths.return_value = (
        {},
        {'prompt_file': 'p', 'code_file': 'c', 'unit_test_file': 't'},
        {'output_test': 'o/t.py', 'output_code': 'o/c.py', 'output_results': 'r/r.log'},
        None
    )

    mock_fix_error_loop.return_value = (True, "test", "code", 1, 0.5, "gpt-4")

    m_open = mock_open()
    with patch('builtins.open', m_open):
        fix_main(
            ctx=mock_ctx,
            prompt_file="p.prompt",
            code_file="c.py",
            unit_test_file="t.py",
            error_file="e.log",
            output_test=None,
            output_code=None,
            output_results=None,
            loop=True,
            verification_program="verify.py",
            max_attempts=3,
            budget=5.0,
            auto_submit=False
        )

    # Assert time was passed correctly
    call_kwargs = mock_fix_error_loop.call_args.kwargs
    assert call_kwargs['time'] == 120


@patch('pdd.fix_main.Path')
@patch('pdd.fix_main.construct_paths')
@patch('pdd.fix_main.fix_errors_from_unit_tests')
def test_fix_main_passes_time_to_fix_errors_from_unit_tests(
    mock_fix_errors,
    mock_construct_paths,
    mock_path,
    mock_ctx
):
    """
    Test that the time parameter from context is passed to fix_errors_from_unit_tests.
    """
    mock_ctx.obj['time'] = 90
    mock_path.return_value.exists.return_value = True

    mock_construct_paths.return_value = (
        {},
        {'prompt_file': 'p', 'code_file': 'c', 'unit_test_file': 't', 'error_file': 'e'},
        {'output_test': 'o/t.py', 'output_code': 'o/c.py', 'output_results': 'r/r.log'},
        None
    )

    mock_fix_errors.return_value = (False, False, "", "", "analysis", 0.5, "gpt-4")

    fix_main(
        ctx=mock_ctx,
        prompt_file="p.prompt",
        code_file="c.py",
        unit_test_file="t.py",
        error_file="e.log",
        output_test=None,
        output_code=None,
        output_results=None,
        loop=False,
        verification_program=None,
        max_attempts=3,
        budget=5.0,
        auto_submit=False
    )

    # Assert time was passed correctly
    call_kwargs = mock_fix_errors.call_args.kwargs
    assert call_kwargs['time'] == 90


@patch('pdd.fix_main.Path')
@patch('pdd.fix_main.construct_paths')
@patch('pdd.fix_main.fix_errors_from_unit_tests')
def test_fix_main_passes_verbose_to_fix_errors_from_unit_tests(
    mock_fix_errors,
    mock_construct_paths,
    mock_path,
    mock_ctx
):
    """
    Test that verbose parameter is passed to fix_errors_from_unit_tests.
    """
    mock_ctx.obj['verbose'] = True
    mock_path.return_value.exists.return_value = True

    mock_construct_paths.return_value = (
        {},
        {'prompt_file': 'p', 'code_file': 'c', 'unit_test_file': 't', 'error_file': 'e'},
        {'output_test': 'o/t.py', 'output_code': 'o/c.py', 'output_results': 'r/r.log'},
        None
    )

    mock_fix_errors.return_value = (False, False, "", "", "analysis", 0.5, "gpt-4")

    fix_main(
        ctx=mock_ctx,
        prompt_file="p.prompt",
        code_file="c.py",
        unit_test_file="t.py",
        error_file="e.log",
        output_test=None,
        output_code=None,
        output_results=None,
        loop=False,
        verification_program=None,
        max_attempts=3,
        budget=5.0,
        auto_submit=False
    )

    call_kwargs = mock_fix_errors.call_args.kwargs
    assert call_kwargs['verbose'] is True


@patch('pdd.fix_main.construct_paths')
@patch('pdd.fix_main.fix_error_loop')
def test_fix_main_loop_mode_excludes_error_file_from_input_paths(
    mock_fix_error_loop,
    mock_construct_paths,
    mock_ctx
):
    """
    Test that in loop mode, error_file is NOT included in input_file_paths
    passed to construct_paths (since the error log is generated during the loop).
    """
    mock_construct_paths.return_value = (
        {},
        {'prompt_file': 'p', 'code_file': 'c', 'unit_test_file': 't'},
        {'output_test': 'o/t.py', 'output_code': 'o/c.py', 'output_results': 'r/r.log'},
        None
    )

    mock_fix_error_loop.return_value = (True, "test", "code", 1, 0.5, "gpt-4")

    m_open = mock_open()
    with patch('builtins.open', m_open):
        fix_main(
            ctx=mock_ctx,
            prompt_file="p.prompt",
            code_file="c.py",
            unit_test_file="t.py",
            error_file="e.log",  # This is passed but should NOT be in input_file_paths
            output_test=None,
            output_code=None,
            output_results=None,
            loop=True,
            verification_program="verify.py",
            max_attempts=3,
            budget=5.0,
            auto_submit=False
        )

    # Verify error_file was NOT in the input_file_paths
    call_kwargs = mock_construct_paths.call_args.kwargs
    assert 'error_file' not in call_kwargs['input_file_paths']
    # But create_error_file should be True
    assert call_kwargs['create_error_file'] is True


@patch('pdd.fix_main.Path')
@patch('pdd.fix_main.construct_paths')
@patch('pdd.fix_main.fix_errors_from_unit_tests')
def test_fix_main_non_loop_mode_includes_error_file_in_input_paths(
    mock_fix_errors,
    mock_construct_paths,
    mock_path,
    mock_ctx
):
    """
    Test that in non-loop mode, error_file IS included in input_file_paths.
    """
    mock_path.return_value.exists.return_value = True

    mock_construct_paths.return_value = (
        {},
        {'prompt_file': 'p', 'code_file': 'c', 'unit_test_file': 't', 'error_file': 'e'},
        {'output_test': 'o/t.py', 'output_code': 'o/c.py', 'output_results': 'r/r.log'},
        None
    )

    mock_fix_errors.return_value = (False, False, "", "", "analysis", 0.5, "gpt-4")

    fix_main(
        ctx=mock_ctx,
        prompt_file="p.prompt",
        code_file="c.py",
        unit_test_file="t.py",
        error_file="my_errors.log",
        output_test=None,
        output_code=None,
        output_results=None,
        loop=False,
        verification_program=None,
        max_attempts=3,
        budget=5.0,
        auto_submit=False
    )

    # Verify error_file WAS in the input_file_paths
    call_kwargs = mock_construct_paths.call_args.kwargs
    assert call_kwargs['input_file_paths']['error_file'] == 'my_errors.log'
    # And create_error_file should be False
    assert call_kwargs['create_error_file'] is False


@patch('pdd.fix_main.construct_paths')
@patch('pdd.fix_main.fix_error_loop')
def test_fix_main_loop_returns_multiple_attempts(
    mock_fix_error_loop,
    mock_construct_paths,
    mock_ctx
):
    """
    Test that fix_main correctly returns the attempt count from fix_error_loop.
    In loop mode, attempts can be > 1.
    """
    mock_construct_paths.return_value = (
        {},
        {'prompt_file': 'p', 'code_file': 'c', 'unit_test_file': 't'},
        {'output_test': 'o/t.py', 'output_code': 'o/c.py', 'output_results': 'r/r.log'},
        None
    )

    # Simulate 5 attempts before success
    mock_fix_error_loop.return_value = (True, "test", "code", 5, 2.50, "gpt-4")

    m_open = mock_open()
    with patch('builtins.open', m_open):
        success, fixed_test, fixed_code, attempts, total_cost, model_name = fix_main(
            ctx=mock_ctx,
            prompt_file="p.prompt",
            code_file="c.py",
            unit_test_file="t.py",
            error_file="e.log",
            output_test=None,
            output_code=None,
            output_results=None,
            loop=True,
            verification_program="verify.py",
            max_attempts=10,
            budget=5.0,
            auto_submit=False
        )

    assert attempts == 5
    assert total_cost == 2.50


@patch('pdd.fix_main.Path')
@patch('pdd.fix_main.construct_paths')
@patch('pdd.fix_main.fix_errors_from_unit_tests')
def test_fix_main_non_loop_always_has_one_attempt(
    mock_fix_errors,
    mock_construct_paths,
    mock_path,
    mock_ctx
):
    """
    Test that in non-loop mode, attempts is always 1 regardless of success.
    """
    mock_path.return_value.exists.return_value = True

    mock_construct_paths.return_value = (
        {},
        {'prompt_file': 'p', 'code_file': 'c', 'unit_test_file': 't', 'error_file': 'e'},
        {'output_test': 'o/t.py', 'output_code': 'o/c.py', 'output_results': 'r/r.log'},
        None
    )

    # Even when fix fails, attempts should be 1
    mock_fix_errors.return_value = (False, False, "", "", "analysis", 0.5, "gpt-4")

    success, fixed_test, fixed_code, attempts, total_cost, model_name = fix_main(
        ctx=mock_ctx,
        prompt_file="p.prompt",
        code_file="c.py",
        unit_test_file="t.py",
        error_file="e.log",
        output_test=None,
        output_code=None,
        output_results=None,
        loop=False,
        verification_program=None,
        max_attempts=3,
        budget=5.0,
        auto_submit=False
    )

    assert success is False
    assert attempts == 1  # Always 1 in non-loop mode
