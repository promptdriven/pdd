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
@patch('pdd.fix_main.run_pytest_on_file')
@patch('pdd.fix_main.Path') # Patch Path where it's used in fix_main
@patch('pdd.fix_main.construct_paths')
@patch('pdd.fix_main.fix_error_loop')
@patch('pdd.fix_main.fix_errors_from_unit_tests')
def test_fix_main_without_loop(
    mock_fix_errors_from_unit_tests,
    mock_fix_error_loop,
    mock_construct_paths,
    mock_path, # Add mock_path fixture
    mock_run_pytest,
    mock_ctx
):
    """
    Test that calling fix_main without the loop option uses fix_errors_from_unit_tests
    and saves the outputs correctly.
    """
    # Arrange
    # Force local execution to prevent cloud path from being taken
    mock_ctx.obj['local'] = True

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

    # Mock pytest to return passing tests (validates the fix)
    mock_run_pytest.return_value = (0, 0, 0, "All tests passed")

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
    # Verify test validation was performed
    mock_run_pytest.assert_called_once()


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
    Test that fix_main raises FileNotFoundError when error_file doesn't exist
    in non-loop mode, as per spec: 'pre-validate the provided error_file exists
    before constructing paths'. Input validation errors propagate to caller
    for proper exit code handling.
    """
    # Arrange - configure Path to report file doesn't exist
    mock_path_instance = mock_path.return_value
    mock_path_instance.exists.return_value = False

    # Act & Assert - should raise FileNotFoundError for input validation
    with pytest.raises(FileNotFoundError) as exc_info:
        fix_main(
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

    # Verify the error message contains useful information
    assert "nonexistent_errors.log" in str(exc_info.value)
    assert "does not exist" in str(exc_info.value)

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
    # Force local execution to prevent cloud path from being taken
    mock_ctx.obj['local'] = True
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


@patch('pdd.fix_main.run_pytest_on_file')
@patch('pdd.fix_main.construct_paths')
@patch('pdd.fix_main.fix_errors_from_unit_tests')
def test_fix_main_success_when_only_code_updated(
    mock_fix_errors,
    mock_construct_paths,
    mock_run_pytest,
    mock_ctx
):
    """
    Test that success is True when only update_code=True (update_unit_test=False)
    AND the tests pass after validation.
    """
    # Force local execution to prevent cloud path from being taken
    mock_ctx.obj['local'] = True

    from pathlib import Path as RealPath

    # Use real Path objects but wrap to track exists() calls
    class MockPath(type(RealPath())):
        """A Path subclass that always returns True for exists()"""
        def exists(self):
            return True

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

    # Mock pytest to return passing tests (validates the fix works)
    mock_run_pytest.return_value = (0, 0, 0, "All tests passed")

    m_open = mock_open()
    with patch('pdd.fix_main.Path', MockPath):
        with patch.object(MockPath, 'mkdir'):
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
    assert success is True  # True because tests passed after the fix
    assert fixed_test == ""
    assert fixed_code == "fixed code content"
    # Verify test validation was performed
    mock_run_pytest.assert_called_once()


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
    # Force local execution to prevent cloud path from being taken
    mock_ctx.obj['local'] = True
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

    # Assert - no write calls should have been made since both contents are empty
    # (read calls may happen for language detection, etc.)
    write_calls = [call for call in m_open.call_args_list if len(call[0]) > 1 and 'w' in call[0][1]]
    assert len(write_calls) == 0, f"Expected no write calls, but got: {write_calls}"


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
    # Force local execution to prevent cloud path from being taken
    mock_ctx.obj['local'] = True
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
    # Force local execution to prevent cloud path from being taken
    mock_ctx.obj['local'] = True
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
    # Force local execution to prevent cloud path from being taken
    mock_ctx.obj['local'] = True
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
    # Force local execution to prevent cloud path from being taken
    mock_ctx.obj['local'] = True
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


# ============================================================================
# Bug Regression Tests - Issue #158
# ============================================================================

@patch('pdd.fix_main.run_pytest_on_file')
@patch('pdd.fix_main.Path')
@patch('pdd.fix_main.construct_paths')
@patch('pdd.fix_main.fix_errors_from_unit_tests')
def test_fix_main_non_loop_should_not_report_success_without_test_validation(
    mock_fix_errors,
    mock_construct_paths,
    mock_path,
    mock_run_pytest,
    mock_ctx
):
    """
    BUG TEST - Issue #158: fix_main reports success=True when LLM suggests
    changes, but never validates that the changes actually fix the tests.

    This test exposes the bug where:
    - Current behavior (BUG): success = update_unit_test or update_code
    - Expected behavior: success should only be True if tests pass after fixes

    The LLM returning update_code=True means "I suggest updating the code",
    NOT "the code is now fixed". Without running tests, we cannot know if
    the suggested fix actually works.

    Evidence from issue: model="" and actual_cost=0.0 with success=true
    indicates no LLM was actually invoked, yet success was claimed.
    """
    # Force local execution to prevent cloud path from being taken
    mock_ctx.obj['local'] = True
    mock_path.return_value.exists.return_value = True

    mock_construct_paths.return_value = (
        {},
        {'prompt_file': 'prompt content', 'code_file': 'def broken():\n    return 1/0',
         'unit_test_file': 'def test_broken():\n    assert broken() == 1',
         'error_file': 'ZeroDivisionError: division by zero'},
        {'output_test': 'output/test.py', 'output_code': 'output/code.py',
         'output_results': 'results/results.log'},
        None
    )

    # LLM suggests a fix (update_code=True), but the fix is WRONG
    mock_fix_errors.return_value = (
        False,  # update_unit_test - LLM says don't update test
        True,   # update_code - LLM says update code (suggests a fix)
        "",     # fixed_unit_test
        "def broken():\n    return 'still wrong'",  # LLM's suggested fix - WRONG!
        "Analysis: Changed the function to return a string",
        0.75,
        "gpt-4"
    )

    # Simulate tests STILL FAILING after the fix is applied
    # This is the key: the LLM suggested a fix, but it didn't actually work
    mock_run_pytest.return_value = (1, 0, 0, "FAILED: test_broken - AssertionError")

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

    # After the fix for issue #158:
    # success should be False because run_pytest_on_file returned failures
    assert success is False, (
        "Bug #158: success should be False when test validation fails. "
        f"Got success={success}, but expected False because tests still fail."
    )
    # Verify that test validation was actually performed
    mock_run_pytest.assert_called_once()


@patch('pdd.fix_main.run_pytest_on_file')
@patch('pdd.fix_main.Path')
@patch('pdd.fix_main.construct_paths')
@patch('pdd.fix_main.fix_errors_from_unit_tests')
def test_fix_main_non_loop_success_requires_test_validation_both_flags_true(
    mock_fix_errors,
    mock_construct_paths,
    mock_path,
    mock_run_pytest,
    mock_ctx
):
    """
    BUG TEST - Issue #158: Demonstrates that success=True should require
    actual test validation, not just LLM suggesting changes.

    This test shows that when both update_unit_test=True AND update_code=True,
    the current code reports success=True, but this is wrong because:
    1. No tests were run to validate the fix
    2. The LLM could have suggested completely wrong fixes
    3. success=True gives users false confidence

    The log evidence shows model="" and actual_cost=0.0 with success=true,
    meaning the system claimed success without any LLM invocation at all.
    """
    # Force local execution to prevent cloud path from being taken
    mock_ctx.obj['local'] = True
    mock_path.return_value.exists.return_value = True
    mock_ctx.obj['quiet'] = True  # Suppress output for cleaner test

    mock_construct_paths.return_value = (
        {},
        {'prompt_file': 'p', 'code_file': 'c', 'unit_test_file': 't', 'error_file': 'e'},
        {'output_test': 'output/t.py', 'output_code': 'output/c.py', 'output_results': 'results/r.log'},
        None
    )

    # Simulate: LLM suggests updating BOTH test and code
    # But what if the suggestions are wrong? Current code would still say success=True
    mock_fix_errors.return_value = (
        True,   # update_unit_test - LLM wants to change test
        True,   # update_code - LLM wants to change code
        "def test_foo(): pass",  # Bad test suggestion
        "def foo(): raise Exception()",  # Bad code suggestion
        "Analysis: Made both worse",
        0.50,
        "gpt-4"
    )

    # Simulate tests STILL FAILING after the bad fix is applied
    mock_run_pytest.return_value = (1, 0, 0, "FAILED: test_foo")

    m_open = mock_open()
    with patch('builtins.open', m_open):
        success, _, _, _, _, _ = fix_main(
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

    # After the fix for issue #158:
    # success should be False because run_pytest_on_file returned failures
    assert success is False, (
        "Bug #158: success=True is reported based on LLM suggestion flags "
        "(update_unit_test or update_code), not actual test results. "
        "The system should run tests after applying fixes to validate success."
    )
    # Verify that test validation was performed
    mock_run_pytest.assert_called_once()


@patch('pdd.fix_main.run_pytest_on_file')
@patch('pdd.fix_main.Path')
@patch('pdd.fix_main.construct_paths')
@patch('pdd.fix_main.fix_errors_from_unit_tests')
def test_fix_main_non_loop_success_when_tests_pass_after_fix(
    mock_fix_errors,
    mock_construct_paths,
    mock_path,
    mock_run_pytest,
    mock_ctx
):
    """
    Test that success=True when the LLM suggests a fix AND tests pass after validation.
    This is the positive case: the fix actually works.
    """
    # Force local execution to prevent cloud path from being taken
    mock_ctx.obj['local'] = True
    mock_path.return_value.exists.return_value = True
    mock_ctx.obj['quiet'] = True

    mock_construct_paths.return_value = (
        {},
        {'prompt_file': 'p', 'code_file': 'c', 'unit_test_file': 't', 'error_file': 'e'},
        {'output_test': 'output/t.py', 'output_code': 'output/c.py', 'output_results': 'results/r.log'},
        None
    )

    # LLM suggests a fix that actually works
    mock_fix_errors.return_value = (
        False,  # update_unit_test
        True,   # update_code - LLM fixed the code
        "",     # fixed_unit_test
        "def foo(): return 42",  # Good fix
        "Analysis: Fixed the return value",
        0.50,
        "gpt-4"
    )

    # Simulate tests PASSING after the fix is applied
    mock_run_pytest.return_value = (0, 0, 0, "All tests passed!")

    m_open = mock_open()
    with patch('builtins.open', m_open):
        success, _, _, _, _, _ = fix_main(
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

    # success should be True because tests pass after the fix
    assert success is True, (
        f"success should be True when tests pass after fix. Got success={success}"
    )
    mock_run_pytest.assert_called_once()


# ============================================================================
# Cloud Execution Tests
# ============================================================================

@patch('pdd.fix_main.run_pytest_on_file')
@patch('pdd.fix_main.requests.post')
@patch('pdd.fix_main.CloudConfig.get_jwt_token')
@patch('pdd.fix_main.Path')
@patch('pdd.fix_main.construct_paths')
def test_fix_main_cloud_success(
    mock_construct_paths,
    mock_path,
    mock_get_jwt,
    mock_post,
    mock_run_pytest,
    mock_ctx
):
    """
    Test that fix_main uses cloud execution successfully when available.
    """
    mock_path.return_value.exists.return_value = True
    mock_ctx.obj['local'] = False  # Not forcing local

    mock_construct_paths.return_value = (
        {},
        {'prompt_file': 'prompt', 'code_file': 'code', 'unit_test_file': 'test', 'error_file': 'error'},
        {'output_test': 'output/test.py', 'output_code': 'output/code.py', 'output_results': 'results/fix.log'},
        'python'
    )

    mock_get_jwt.return_value = "mock_jwt_token"

    # Mock successful cloud response
    mock_response = MagicMock()
    mock_response.status_code = 200
    mock_response.json.return_value = {
        'success': True,
        'fixedUnitTest': 'fixed test content',
        'fixedCode': 'fixed code content',
        'analysis': 'analysis content',
        'updateUnitTest': True,
        'updateCode': True,
        'totalCost': 0.05,
        'modelName': 'cloud-model'
    }
    mock_post.return_value = mock_response

    # Mock pytest to pass after validation
    mock_run_pytest.return_value = (0, 0, 0, "All tests passed")

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

    # Assert cloud was used
    mock_get_jwt.assert_called_once()
    mock_post.assert_called_once()
    assert success is True
    assert fixed_test == 'fixed test content'
    assert fixed_code == 'fixed code content'
    assert total_cost == 0.05
    assert model_name == 'cloud-model'


@patch('pdd.fix_main.fix_errors_from_unit_tests')
@patch('pdd.fix_main.CloudConfig.get_jwt_token')
@patch('pdd.fix_main.Path')
@patch('pdd.fix_main.construct_paths')
def test_fix_main_cloud_fallback_on_auth_failure(
    mock_construct_paths,
    mock_path,
    mock_get_jwt,
    mock_fix_errors,
    mock_ctx
):
    """
    Test that fix_main falls back to local when cloud authentication fails.
    """
    mock_path.return_value.exists.return_value = True
    mock_ctx.obj['local'] = False

    mock_construct_paths.return_value = (
        {},
        {'prompt_file': 'prompt', 'code_file': 'code', 'unit_test_file': 'test', 'error_file': 'error'},
        {'output_test': 'output/test.py', 'output_code': 'output/code.py', 'output_results': 'results/fix.log'},
        'python'
    )

    # Cloud auth fails
    mock_get_jwt.return_value = None

    # Local fix returns result
    mock_fix_errors.return_value = (False, False, "", "", "analysis", 0.5, "local-model")

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

    # Assert fallback to local was used
    mock_get_jwt.assert_called_once()
    mock_fix_errors.assert_called_once()


@patch('pdd.fix_main.fix_errors_from_unit_tests')
@patch('pdd.fix_main.requests.post')
@patch('pdd.fix_main.CloudConfig.get_jwt_token')
@patch('pdd.fix_main.Path')
@patch('pdd.fix_main.construct_paths')
def test_fix_main_cloud_fallback_on_timeout(
    mock_construct_paths,
    mock_path,
    mock_get_jwt,
    mock_post,
    mock_fix_errors,
    mock_ctx
):
    """
    Test that fix_main falls back to local on cloud timeout.
    """
    import requests as real_requests

    mock_path.return_value.exists.return_value = True
    mock_ctx.obj['local'] = False

    mock_construct_paths.return_value = (
        {},
        {'prompt_file': 'prompt', 'code_file': 'code', 'unit_test_file': 'test', 'error_file': 'error'},
        {'output_test': 'output/test.py', 'output_code': 'output/code.py', 'output_results': 'results/fix.log'},
        'python'
    )

    mock_get_jwt.return_value = "mock_jwt_token"
    mock_post.side_effect = real_requests.exceptions.Timeout("Request timed out")

    mock_fix_errors.return_value = (False, False, "", "", "analysis", 0.5, "local-model")

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

    # Assert fallback to local was used after timeout
    mock_post.assert_called_once()
    mock_fix_errors.assert_called_once()


@patch('pdd.fix_main.requests.post')
@patch('pdd.fix_main.CloudConfig.get_jwt_token')
@patch('pdd.fix_main.Path')
@patch('pdd.fix_main.construct_paths')
def test_fix_main_cloud_insufficient_credits_raises_error(
    mock_construct_paths,
    mock_path,
    mock_get_jwt,
    mock_post,
    mock_ctx
):
    """
    Test that fix_main raises UsageError on insufficient credits (HTTP 402).
    """
    import requests as real_requests

    mock_path.return_value.exists.return_value = True
    mock_ctx.obj['local'] = False

    mock_construct_paths.return_value = (
        {},
        {'prompt_file': 'prompt', 'code_file': 'code', 'unit_test_file': 'test', 'error_file': 'error'},
        {'output_test': 'output/test.py', 'output_code': 'output/code.py', 'output_results': 'results/fix.log'},
        'python'
    )

    mock_get_jwt.return_value = "mock_jwt_token"

    # Mock 402 error response
    mock_response = MagicMock()
    mock_response.status_code = 402
    mock_response.text = "Insufficient credits"
    mock_response.json.return_value = {'currentBalance': 0, 'estimatedCost': 100}

    http_error = real_requests.exceptions.HTTPError(response=mock_response)
    mock_post.return_value.raise_for_status.side_effect = http_error

    with pytest.raises(UsageError) as exc_info:
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

    assert "credits" in str(exc_info.value).lower()


@patch('pdd.fix_main.fix_error_loop')
@patch('pdd.fix_main.construct_paths')
def test_fix_main_loop_mode_with_local_flag_uses_local(
    mock_construct_paths,
    mock_fix_error_loop,
    mock_ctx
):
    """
    Test that loop mode with --local flag uses purely local execution (use_cloud=False).
    """
    mock_ctx.obj['local'] = True  # Force local execution

    mock_construct_paths.return_value = (
        {},
        {'prompt_file': 'prompt', 'code_file': 'code', 'unit_test_file': 'test'},
        {'output_test': 'output/test.py', 'output_code': 'output/code.py', 'output_results': 'results/fix.log'},
        'python'
    )

    mock_fix_error_loop.return_value = (True, "fixed test", "fixed code", 2, 1.0, "local-model")

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
            loop=True,
            verification_program="verify.py",
            max_attempts=3,
            budget=5.0,
            auto_submit=False
        )

    # fix_error_loop should be called with use_cloud=False
    mock_fix_error_loop.assert_called_once()
    call_kwargs = mock_fix_error_loop.call_args[1]
    assert call_kwargs.get('use_cloud') == False


@patch('pdd.fix_main.fix_error_loop')
@patch('pdd.fix_main.construct_paths')
def test_fix_main_loop_mode_uses_hybrid_cloud_by_default(
    mock_construct_paths,
    mock_fix_error_loop,
    mock_ctx
):
    """
    Test that loop mode without --local flag uses hybrid cloud mode (use_cloud=True).
    Hybrid mode means local test execution + cloud LLM calls.
    """
    mock_ctx.obj['local'] = False  # Default - not forcing local

    mock_construct_paths.return_value = (
        {},
        {'prompt_file': 'prompt', 'code_file': 'code', 'unit_test_file': 'test'},
        {'output_test': 'output/test.py', 'output_code': 'output/code.py', 'output_results': 'results/fix.log'},
        'python'
    )

    mock_fix_error_loop.return_value = (True, "fixed test", "fixed code", 2, 1.0, "cloud-model")

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
            loop=True,
            verification_program="verify.py",
            max_attempts=3,
            budget=5.0,
            auto_submit=False
        )

    # fix_error_loop should be called with use_cloud=True
    mock_fix_error_loop.assert_called_once()
    call_kwargs = mock_fix_error_loop.call_args[1]
    assert call_kwargs.get('use_cloud') == True


@patch('pdd.fix_main.fix_errors_from_unit_tests')
@patch('pdd.fix_main.CloudConfig.get_jwt_token')
@patch('pdd.fix_main.Path')
@patch('pdd.fix_main.construct_paths')
def test_fix_main_local_flag_skips_cloud(
    mock_construct_paths,
    mock_path,
    mock_get_jwt,
    mock_fix_errors,
    mock_ctx
):
    """
    Test that --local flag forces local execution, skipping cloud entirely.
    """
    mock_path.return_value.exists.return_value = True
    mock_ctx.obj['local'] = True  # Force local

    mock_construct_paths.return_value = (
        {},
        {'prompt_file': 'prompt', 'code_file': 'code', 'unit_test_file': 'test', 'error_file': 'error'},
        {'output_test': 'output/test.py', 'output_code': 'output/code.py', 'output_results': 'results/fix.log'},
        'python'
    )

    mock_fix_errors.return_value = (False, False, "", "", "analysis", 0.5, "local-model")

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

    # Cloud auth should not be called when --local is set
    mock_get_jwt.assert_not_called()
    # Local fix should be used
    mock_fix_errors.assert_called_once()


@patch('pdd.fix_main.fix_errors_from_unit_tests')
@patch('pdd.fix_main.requests.post')
@patch('pdd.fix_main.CloudConfig.get_jwt_token')
@patch('pdd.fix_main.Path')
@patch('pdd.fix_main.construct_paths')
def test_fix_main_cloud_fallback_on_network_error(
    mock_construct_paths,
    mock_path,
    mock_get_jwt,
    mock_post,
    mock_fix_errors,
    mock_ctx
):
    """
    Test that fix_main falls back to local on cloud network error.
    """
    import requests as real_requests

    mock_path.return_value.exists.return_value = True
    mock_ctx.obj['local'] = False

    mock_construct_paths.return_value = (
        {},
        {'prompt_file': 'prompt', 'code_file': 'code', 'unit_test_file': 'test', 'error_file': 'error'},
        {'output_test': 'output/test.py', 'output_code': 'output/code.py', 'output_results': 'results/fix.log'},
        'python'
    )

    mock_get_jwt.return_value = "mock_jwt_token"
    mock_post.side_effect = real_requests.exceptions.ConnectionError("Network unreachable")

    mock_fix_errors.return_value = (False, False, "", "", "analysis", 0.5, "local-model")

    success, _, _, _, _, model_name = fix_main(
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

    # Assert fallback to local was used after network error
    mock_post.assert_called_once()
    mock_fix_errors.assert_called_once()
    assert model_name == "local-model"


@patch('pdd.fix_main.fix_errors_from_unit_tests')
@patch('pdd.fix_main.requests.post')
@patch('pdd.fix_main.CloudConfig.get_jwt_token')
@patch('pdd.fix_main.Path')
@patch('pdd.fix_main.construct_paths')
def test_fix_main_cloud_fallback_on_5xx_error(
    mock_construct_paths,
    mock_path,
    mock_get_jwt,
    mock_post,
    mock_fix_errors,
    mock_ctx
):
    """
    Test that fix_main falls back to local on 5xx server errors.
    """
    import requests as real_requests

    mock_path.return_value.exists.return_value = True
    mock_ctx.obj['local'] = False

    mock_construct_paths.return_value = (
        {},
        {'prompt_file': 'prompt', 'code_file': 'code', 'unit_test_file': 'test', 'error_file': 'error'},
        {'output_test': 'output/test.py', 'output_code': 'output/code.py', 'output_results': 'results/fix.log'},
        'python'
    )

    mock_get_jwt.return_value = "mock_jwt_token"

    # Mock 500 error response
    mock_response = MagicMock()
    mock_response.status_code = 500
    mock_response.text = "Internal Server Error"

    http_error = real_requests.exceptions.HTTPError(response=mock_response)
    mock_post.return_value.raise_for_status.side_effect = http_error

    mock_fix_errors.return_value = (False, False, "", "", "analysis", 0.5, "local-model")

    success, _, _, _, _, model_name = fix_main(
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

    # Assert fallback to local was used after 500 error
    mock_fix_errors.assert_called_once()
    assert model_name == "local-model"


# ============ Tests for cloud_fix_errors function ============

@patch('pdd.fix_error_loop.requests.post')
@patch('pdd.fix_error_loop.CloudConfig.get_jwt_token')
def test_cloud_fix_errors_success(mock_get_jwt, mock_post):
    """
    Test that cloud_fix_errors successfully calls the cloud endpoint and returns results.
    """
    from pdd.fix_error_loop import cloud_fix_errors

    mock_get_jwt.return_value = "test-jwt-token"

    mock_response = MagicMock()
    mock_response.status_code = 200
    mock_response.json.return_value = {
        "success": True,
        "fixedUnitTest": "fixed unit test code",
        "fixedCode": "fixed code",
        "analysis": "Analysis of fix",
        "updateUnitTest": True,
        "updateCode": True,
        "totalCost": 0.05,
        "modelName": "cloud-fix-model"
    }
    mock_post.return_value = mock_response

    update_ut, update_code, fixed_ut, fixed_code, analysis, cost, model = cloud_fix_errors(
        unit_test="original unit test",
        code="original code",
        prompt="test prompt",
        error="test error logs",
        error_file="error.log",
        strength=0.7,
        temperature=0.0,
        verbose=False,
        time=0.25,
        code_file_ext=".py"
    )

    assert update_ut == True
    assert update_code == True
    assert fixed_ut == "fixed unit test code"
    assert fixed_code == "fixed code"
    assert analysis == "Analysis of fix"
    assert cost == 0.05
    assert model == "cloud-fix-model"

    # Verify request was made correctly
    mock_post.assert_called_once()
    call_kwargs = mock_post.call_args
    assert "Bearer test-jwt-token" in call_kwargs[1]["headers"]["Authorization"]


@patch('pdd.fix_error_loop.CloudConfig.get_jwt_token')
def test_cloud_fix_errors_auth_failure(mock_get_jwt):
    """
    Test that cloud_fix_errors raises RuntimeError when JWT token is unavailable.
    """
    from pdd.fix_error_loop import cloud_fix_errors

    mock_get_jwt.return_value = None  # No JWT token

    with pytest.raises(RuntimeError) as exc_info:
        cloud_fix_errors(
            unit_test="test",
            code="code",
            prompt="prompt",
            error="error",
            error_file="error.log",
            strength=0.7,
            temperature=0.0
        )

    assert "authentication failed" in str(exc_info.value).lower()


@patch('pdd.fix_error_loop.requests.post')
@patch('pdd.fix_error_loop.CloudConfig.get_jwt_token')
def test_cloud_fix_errors_insufficient_credits(mock_get_jwt, mock_post):
    """
    Test that cloud_fix_errors raises RuntimeError for 402 insufficient credits.
    """
    from pdd.fix_error_loop import cloud_fix_errors
    import requests as real_requests

    mock_get_jwt.return_value = "test-jwt-token"

    mock_response = MagicMock()
    mock_response.status_code = 402
    mock_response.text = '{"error": "Insufficient credits"}'
    mock_response.json.return_value = {"currentBalance": 0, "estimatedCost": 50}
    mock_post.return_value = mock_response
    mock_post.return_value.raise_for_status.side_effect = real_requests.HTTPError(
        response=mock_response
    )

    with pytest.raises(RuntimeError) as exc_info:
        cloud_fix_errors(
            unit_test="test",
            code="code",
            prompt="prompt",
            error="error",
            error_file="error.log",
            strength=0.7,
            temperature=0.0
        )

    assert "insufficient credits" in str(exc_info.value).lower()


@patch('pdd.fix_error_loop.requests.post')
@patch('pdd.fix_error_loop.CloudConfig.get_jwt_token')
def test_cloud_fix_errors_timeout(mock_get_jwt, mock_post):
    """
    Test that cloud_fix_errors raises RuntimeError on timeout.
    """
    from pdd.fix_error_loop import cloud_fix_errors
    import requests as real_requests

    mock_get_jwt.return_value = "test-jwt-token"
    mock_post.side_effect = real_requests.exceptions.Timeout("Request timed out")

    with pytest.raises(RuntimeError) as exc_info:
        cloud_fix_errors(
            unit_test="test",
            code="code",
            prompt="prompt",
            error="error",
            error_file="error.log",
            strength=0.7,
            temperature=0.0
        )

    assert "timed out" in str(exc_info.value).lower()


# ============ Tests for fix_error_loop with use_cloud parameter ============

@patch('pdd.fix_error_loop.cloud_fix_errors')
@patch('pdd.fix_error_loop.run_pytest_on_file')
def test_fix_error_loop_uses_cloud_when_use_cloud_true(mock_pytest, mock_cloud_fix):
    """
    Test that fix_error_loop calls cloud_fix_errors when use_cloud=True.
    """
    from pdd.fix_error_loop import fix_error_loop
    import tempfile
    import os

    # Create temp files for the test
    with tempfile.TemporaryDirectory() as tmpdir:
        unit_test_file = os.path.join(tmpdir, "test_code.py")
        code_file = os.path.join(tmpdir, "code.py")
        verification_file = os.path.join(tmpdir, "verify.py")
        error_log_file = os.path.join(tmpdir, "error.log")

        # Write minimal test files
        with open(unit_test_file, "w") as f:
            f.write("def test_example(): pass")
        with open(code_file, "w") as f:
            f.write("def example(): pass")
        with open(verification_file, "w") as f:
            f.write("print('verified')")

        # Mock pytest to return failures initially, then success
        mock_pytest.side_effect = [
            (1, 0, 0, "1 failed"),  # Initial failure
            (0, 0, 0, "1 passed"),  # After fix - success
        ]

        # Mock cloud fix to return successful fix
        mock_cloud_fix.return_value = (
            True,   # update_unit_test
            True,   # update_code
            "fixed test code",
            "fixed code",
            "Cloud analysis",
            0.05,   # cost
            "cloud-model"
        )

        success, final_ut, final_code, attempts, cost, model = fix_error_loop(
            unit_test_file=unit_test_file,
            code_file=code_file,
            prompt_file="prompt.prompt",
            prompt="test prompt",
            verification_program=verification_file,
            strength=0.7,
            temperature=0.0,
            max_attempts=3,
            budget=5.0,
            error_log_file=error_log_file,
            verbose=False,
            use_cloud=True
        )

        # cloud_fix_errors should have been called
        mock_cloud_fix.assert_called()


@patch('pdd.fix_error_loop.fix_errors_from_unit_tests')
@patch('pdd.fix_error_loop.run_pytest_on_file')
def test_fix_error_loop_uses_local_when_use_cloud_false(mock_pytest, mock_local_fix):
    """
    Test that fix_error_loop calls fix_errors_from_unit_tests when use_cloud=False.
    """
    from pdd.fix_error_loop import fix_error_loop
    import tempfile
    import os

    # Create temp files for the test
    with tempfile.TemporaryDirectory() as tmpdir:
        unit_test_file = os.path.join(tmpdir, "test_code.py")
        code_file = os.path.join(tmpdir, "code.py")
        verification_file = os.path.join(tmpdir, "verify.py")
        error_log_file = os.path.join(tmpdir, "error.log")

        # Write minimal test files
        with open(unit_test_file, "w") as f:
            f.write("def test_example(): pass")
        with open(code_file, "w") as f:
            f.write("def example(): pass")
        with open(verification_file, "w") as f:
            f.write("print('verified')")

        # Mock pytest to return failures initially, then success
        mock_pytest.side_effect = [
            (1, 0, 0, "1 failed"),  # Initial failure
            (0, 0, 0, "1 passed"),  # After fix - success
        ]

        # Mock local fix to return successful fix
        mock_local_fix.return_value = (
            True,   # update_unit_test
            True,   # update_code
            "fixed test code",
            "fixed code",
            "Local analysis",
            0.03,   # cost
            "local-model"
        )

        success, final_ut, final_code, attempts, cost, model = fix_error_loop(
            unit_test_file=unit_test_file,
            code_file=code_file,
            prompt_file="prompt.prompt",
            prompt="test prompt",
            verification_program=verification_file,
            strength=0.7,
            temperature=0.0,
            max_attempts=3,
            budget=5.0,
            error_log_file=error_log_file,
            verbose=False,
            use_cloud=False
        )

        # fix_errors_from_unit_tests should have been called
        mock_local_fix.assert_called()


@patch('pdd.fix_error_loop.fix_errors_from_unit_tests')
@patch('pdd.fix_error_loop.cloud_fix_errors')
@patch('pdd.fix_error_loop.run_pytest_on_file')
def test_fix_error_loop_cloud_fallback_to_local(mock_pytest, mock_cloud_fix, mock_local_fix):
    """
    Test that fix_error_loop falls back to local when cloud fails with recoverable error.
    """
    from pdd.fix_error_loop import fix_error_loop
    import tempfile
    import os

    # Create temp files for the test
    with tempfile.TemporaryDirectory() as tmpdir:
        unit_test_file = os.path.join(tmpdir, "test_code.py")
        code_file = os.path.join(tmpdir, "code.py")
        verification_file = os.path.join(tmpdir, "verify.py")
        error_log_file = os.path.join(tmpdir, "error.log")

        # Write minimal test files
        with open(unit_test_file, "w") as f:
            f.write("def test_example(): pass")
        with open(code_file, "w") as f:
            f.write("def example(): pass")
        with open(verification_file, "w") as f:
            f.write("print('verified')")

        # Mock pytest to return failures initially, then success
        mock_pytest.side_effect = [
            (1, 0, 0, "1 failed"),  # Initial failure
            (0, 0, 0, "1 passed"),  # After fix - success
        ]

        # Mock cloud fix to fail with recoverable error
        mock_cloud_fix.side_effect = RuntimeError("Cloud timeout error")

        # Mock local fix to return successful fix (fallback)
        mock_local_fix.return_value = (
            True,   # update_unit_test
            True,   # update_code
            "fixed test code",
            "fixed code",
            "Local fallback analysis",
            0.03,   # cost
            "local-fallback-model"
        )

        success, final_ut, final_code, attempts, cost, model = fix_error_loop(
            unit_test_file=unit_test_file,
            code_file=code_file,
            prompt_file="prompt.prompt",
            prompt="test prompt",
            verification_program=verification_file,
            strength=0.7,
            temperature=0.0,
            max_attempts=3,
            budget=5.0,
            error_log_file=error_log_file,
            verbose=False,
            use_cloud=True  # Request cloud, but will fall back to local
        )

        # Cloud should have been attempted
        mock_cloud_fix.assert_called()
        # Local fallback should have been used
        mock_local_fix.assert_called()


# ============================================================================
# E2E Cloud Tests
# ============================================================================

def _has_cloud_credentials() -> bool:
    """Check if cloud credentials (API keys) are available for E2E testing."""
    import os
    return bool(
        os.environ.get("NEXT_PUBLIC_FIREBASE_API_KEY") and
        os.environ.get("GITHUB_CLIENT_ID")
    )


def _has_cloud_jwt_token() -> bool:
    """Check if a JWT token is available (env var, cache file, or stored refresh token)."""
    import os
    # First check for env var (fast path)
    if os.environ.get("PDD_JWT_TOKEN"):
        return True
    # Check for valid (non-expired) cached JWT
    try:
        from pdd.get_jwt_token import _get_cached_jwt
        if _get_cached_jwt(verbose=False):
            return True
    except Exception:
        pass
    # Check for stored refresh token (requires keyring)
    try:
        import keyring
        token = keyring.get_password("firebase-auth-PDD Code Generator", "refresh_token")
        return bool(token)
    except Exception:
        return False


def _wait_for_cloud_credentials(max_retries: int = 3, delay: float = 1.0) -> bool:
    """
    Retry checking for cloud credentials with delays.

    pytest-xdist workers may have delayed access to keyring or env vars.
    This gives the system a chance to make credentials available.
    """
    import time
    for attempt in range(max_retries):
        if _has_cloud_credentials() and _has_cloud_jwt_token():
            return True
        if attempt < max_retries - 1:
            time.sleep(delay)
    return False


requires_cloud_e2e = pytest.mark.skipif(
    not (_has_cloud_credentials() and _has_cloud_jwt_token()),
    reason="Cloud E2E tests require credentials (API keys) and auth token (PDD_JWT_TOKEN or stored refresh token)"
)


@requires_cloud_e2e
def test_fix_main_cloud_e2e_non_loop(tmp_path, capsys):
    """
    E2E test that fix_main (non-loop mode) successfully uses cloud execution.
    This test requires valid cloud credentials and makes real API calls.
    """
    import os
    import click

    # Retry credentials check (pytest-xdist workers may have delayed keyring access)
    if not _wait_for_cloud_credentials(max_retries=3, delay=1.0):
        pytest.skip("Cloud credentials not available in this worker process after retries")

    # Set PDD_CLOUD_ONLY to prevent silent fallback to local
    os.environ['PDD_CLOUD_ONLY'] = '1'

    try:
        # Create test files in tmp_path
        prompt_file = tmp_path / "prompt.txt"
        prompt_file.write_text("Write a function that calculates the sum of a list")

        code_file = tmp_path / "sum_list.py"
        code_file.write_text("""
def sum_list(numbers):
    total = 0
    for n in numbers:
        total += n
    return total
""")

        unit_test_file = tmp_path / "test_sum_list.py"
        unit_test_file.write_text("""
from sum_list import sum_list

def test_sum_list():
    # This test has a bug - wrong expected value
    assert sum_list([1, 2, 3]) == 10  # Should be 6
""")

        error_file = tmp_path / "error.log"
        error_file.write_text("""
FAILED test_sum_list.py::test_sum_list - AssertionError: assert 6 == 10
""")

        output_test = tmp_path / "test_sum_list_fixed.py"
        output_code = tmp_path / "sum_list_fixed.py"

        # Create context for cloud execution
        ctx = click.Context(click.Command('fix'))
        ctx.params = {}
        ctx.obj = {
            'strength': 0.25,  # Use lowest strength for faster cloud response
            'temperature': 0,
            'force': True,
            'quiet': False,
            'verbose': True,
            'local': False,  # Enable cloud execution
            'time': None,
            'context': None,
            'confirm_callback': None
        }

        try:
            success, fixed_test, fixed_code, attempts, cost, model = fix_main(
                ctx=ctx,
                prompt_file=str(prompt_file),
                code_file=str(code_file),
                unit_test_file=str(unit_test_file),
                error_file=str(error_file),
                output_test=str(output_test),
                output_code=str(output_code),
                output_results=None,
                loop=False,
                verification_program=None,
                max_attempts=3,
                budget=5.0,
                auto_submit=False
            )
        except UsageError as e:
            error_msg = str(e)
            if "Account not approved" in error_msg:
                pytest.skip(
                    "PDD Cloud account not approved. Visit https://pdd.ai to request access, "
                    "or run tests with --local flag to skip cloud E2E tests."
                )
            elif "No response content" in error_msg or "HTTP" in error_msg:
                pytest.skip(
                    f"PDD Cloud authentication failed: {error_msg}. "
                    "Ensure your account is approved at https://pdd.ai"
                )
            raise

        # Capture output to check for cloud success
        captured = capsys.readouterr()

        # Assertions
        assert cost > 0, f"Expected cost > 0 for cloud execution, got {cost}"
        assert attempts == 1, f"Expected attempts == 1 in non-loop mode, got {attempts}"
        assert "Cloud Success" in captured.out, f"Expected 'Cloud Success' in output, got: {captured.out[:500]}"

    finally:
        # Clean up environment variable
        os.environ.pop('PDD_CLOUD_ONLY', None)


@requires_cloud_e2e
def test_fix_main_cloud_e2e_loop(tmp_path, capsys):
    """
    E2E test that fix_main (loop mode) successfully uses hybrid cloud execution.
    This test requires valid cloud credentials and makes real API calls.
    """
    import os
    import click

    # Retry credentials check (pytest-xdist workers may have delayed keyring access)
    if not _wait_for_cloud_credentials(max_retries=3, delay=1.0):
        pytest.skip("Cloud credentials not available in this worker process after retries")

    # Set PDD_CLOUD_ONLY to prevent silent fallback to local
    os.environ['PDD_CLOUD_ONLY'] = '1'

    try:
        # Create test files in tmp_path
        prompt_file = tmp_path / "prompt.txt"
        prompt_file.write_text("Write a function that calculates factorial")

        code_file = tmp_path / "factorial.py"
        code_file.write_text("""
def factorial(n):
    if n == 0:
        return 1
    return n * factorial(n - 1)
""")

        unit_test_file = tmp_path / "test_factorial.py"
        unit_test_file.write_text("""
from factorial import factorial

def test_factorial():
    assert factorial(5) == 120
    assert factorial(0) == 1
    assert factorial(-1) == 1  # Bug: negative numbers not handled
""")

        # Create verification program
        verification_file = tmp_path / "verify_factorial.py"
        verification_file.write_text("""
import subprocess
import sys

result = subprocess.run(
    [sys.executable, "-m", "pytest", "test_factorial.py", "-v"],
    capture_output=True,
    text=True,
    cwd=str(__file__).rsplit('/', 1)[0]
)
sys.exit(result.returncode)
""")

        output_test = tmp_path / "test_factorial_fixed.py"
        output_code = tmp_path / "factorial_fixed.py"

        # Create context for cloud execution
        ctx = click.Context(click.Command('fix'))
        ctx.params = {}
        ctx.obj = {
            'strength': 0.25,  # Use lowest strength for faster cloud response
            'temperature': 0,
            'force': True,
            'quiet': False,
            'verbose': True,
            'local': False,  # Enable hybrid cloud mode
            'time': None,
            'context': None,
            'confirm_callback': None
        }

        try:
            success, fixed_test, fixed_code, attempts, cost, model = fix_main(
                ctx=ctx,
                prompt_file=str(prompt_file),
                code_file=str(code_file),
                unit_test_file=str(unit_test_file),
                error_file=None,  # Loop mode generates errors
                output_test=str(output_test),
                output_code=str(output_code),
                output_results=None,
                loop=True,
                verification_program=str(verification_file),
                max_attempts=3,
                budget=5.0,
                auto_submit=False
            )
        except UsageError as e:
            error_msg = str(e)
            if "Account not approved" in error_msg:
                pytest.skip(
                    "PDD Cloud account not approved. Visit https://pdd.ai to request access, "
                    "or run tests with --local flag to skip cloud E2E tests."
                )
            elif "No response content" in error_msg or "HTTP" in error_msg:
                pytest.skip(
                    f"PDD Cloud authentication failed: {error_msg}. "
                    "Ensure your account is approved at https://pdd.ai"
                )
            raise

        # Capture output to check for cloud usage
        captured = capsys.readouterr()

        # Assertions
        assert isinstance(success, bool), f"Expected success to be bool, got {type(success)}"
        assert cost > 0, f"Expected cost > 0 for cloud execution, got {cost}"
        assert attempts >= 1, f"Expected at least 1 attempt, got {attempts}"
        # In loop mode with cloud, we should see cloud-related output
        assert "cloud" in captured.out.lower() or "Cloud" in captured.out, \
            f"Expected cloud-related output, got: {captured.out[:500]}"

    finally:
        # Clean up environment variable
        os.environ.pop('PDD_CLOUD_ONLY', None)


def test_fix_errors_prompt_preserves_all_existing_tests():
    """
    Tests that the fix_errors_from_unit_tests LLM prompt includes explicit
    instructions to preserve ALL existing test functions, not just the ones
    being fixed.

    This test ensures we don't regress on the bug where the LLM would drop
    unrelated tests when fixing a subset of failing tests.

    Related: Root cause was the LLM prompt instructing to write tests "in entirety"
    without specifying that ALL original tests must be preserved.
    """
    from pathlib import Path
    import pdd

    # Get the path to the prompt file
    pdd_package_dir = Path(pdd.__file__).parent
    prompt_path = pdd_package_dir / "prompts" / "fix_errors_from_unit_tests_LLM.prompt"

    assert prompt_path.exists(), f"Prompt file not found at {prompt_path}"

    prompt_content = prompt_path.read_text()

    # Verify the preservation instruction exists
    assert "preserve ALL existing test functions" in prompt_content, \
        "Prompt must instruct LLM to preserve all existing test functions"
    assert "Do not remove, skip, or omit any test functions" in prompt_content, \
        "Prompt must explicitly forbid removing test functions"
    assert "every single test function from the input" in prompt_content, \
        "Prompt must require output to include every input test function"


# ============================================================================
# Regression Tests for protect_tests Feature (Issue #303)
# ============================================================================

@patch('pdd.fix_main.construct_paths')
@patch('pdd.fix_main.fix_error_loop')
def test_fix_main_passes_protect_tests_to_fix_error_loop(
    mock_fix_error_loop,
    mock_construct_paths,
    mock_ctx
):
    """
    REGRESSION TEST (Issue #303): Test that fix_main passes protect_tests
    parameter to fix_error_loop as specified in the prompt.
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
            error_file="e.log",
            output_test=None,
            output_code=None,
            output_results=None,
            loop=True,
            verification_program="verify.py",
            max_attempts=3,
            budget=5.0,
            auto_submit=False,
            protect_tests=True  # KEY: Set to True (non-default)
        )

    mock_fix_error_loop.assert_called_once()
    call_kwargs = mock_fix_error_loop.call_args.kwargs
    assert 'protect_tests' in call_kwargs, "protect_tests must be passed to fix_error_loop"
    assert call_kwargs['protect_tests'] is True


@patch('pdd.fix_main.Path')
@patch('pdd.fix_main.construct_paths')
@patch('pdd.fix_main.fix_errors_from_unit_tests')
def test_fix_main_passes_protect_tests_to_fix_errors_from_unit_tests(
    mock_fix_errors,
    mock_construct_paths,
    mock_path,
    mock_ctx
):
    """
    REGRESSION TEST (Issue #303): Test that fix_main passes protect_tests
    parameter to fix_errors_from_unit_tests in non-loop mode.
    """
    mock_ctx.obj['local'] = True  # Force local execution
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
        auto_submit=False,
        protect_tests=True  # KEY: Set to True (non-default)
    )

    mock_fix_errors.assert_called_once()
    call_kwargs = mock_fix_errors.call_args.kwargs
    assert 'protect_tests' in call_kwargs, "protect_tests must be passed to fix_errors_from_unit_tests"
    assert call_kwargs['protect_tests'] is True


def test_fix_main_code_checks_protect_tests_before_writing_test():
    """fix_main.py should check protect_tests before writing test file.

    This is a source code inspection test to ensure the conditional:
        if fixed_unit_test and not protect_tests:
    exists in fix_main.py, preventing test file writes when protect_tests=True.
    """
    from pathlib import Path

    # Read the fix_main.py source code
    fix_main_path = Path(__file__).parent.parent / "pdd" / "fix_main.py"
    source = fix_main_path.read_text()

    # Check that the code includes "protect_tests" check when writing test file
    assert "if fixed_unit_test and not protect_tests:" in source, \
        "fix_main.py should check 'if fixed_unit_test and not protect_tests:' before writing test file"


# --- CI auth hang regression tests (GitHub Actions #462) ---

@patch('pdd.fix_main.run_pytest_on_file')
@patch('pdd.fix_main.Path')
@patch('pdd.fix_main.construct_paths')
@patch('pdd.fix_main.fix_errors_from_unit_tests')
@patch('pdd.fix_main.CloudConfig.get_jwt_token', return_value=None)
@patch('pdd.fix_main.get_jwt_token')
def test_fix_main_auto_submit_skipped_when_pdd_force_local(
    mock_get_jwt_token,
    mock_cloud_jwt,
    mock_fix_errors,
    mock_construct_paths,
    mock_path,
    mock_run_pytest,
    mock_ctx,
    monkeypatch
):
    """
    Regression test for CI auth hang: when PDD_FORCE_LOCAL=1, auto_submit=True
    must NOT call get_jwt_token, which would trigger the GitHub device code flow
    and hang in CI for ~15 minutes.
    """
    monkeypatch.setenv("PDD_FORCE_LOCAL", "1")
    mock_path.return_value.exists.return_value = True
    mock_ctx.obj['local'] = True  # PDD_FORCE_LOCAL implies local mode

    mock_construct_paths.return_value = (
        {},
        {
            'prompt_file': 'Test prompt content',
            'code_file': 'Test code content',
            'unit_test_file': 'Test test content',
            'error_file': 'Error content'
        },
        {
            'output_test': 'output/test_fixed.py',
            'output_code': 'output/code_fixed.py',
            'output_results': 'results/fix.log'
        },
        None
    )

    mock_fix_errors.return_value = (
        True,   # update_unit_test
        True,   # update_code
        "fixed test",
        "fixed code",
        "analysis",
        0.50,
        "gpt-4"
    )

    mock_run_pytest.return_value = (0, 0, 0, "All tests passed")

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
            auto_submit=True
        )

    assert success is True
    mock_get_jwt_token.assert_not_called(), \
        "get_jwt_token must NOT be called when PDD_FORCE_LOCAL=1 (would hang CI)"


@patch('pdd.fix_main.run_pytest_on_file')
@patch('pdd.fix_main.Path')
@patch('pdd.fix_main.construct_paths')
@patch('pdd.fix_main.fix_errors_from_unit_tests')
@patch('pdd.fix_main.CloudConfig.get_jwt_token', return_value=None)
@patch('pdd.fix_main.asyncio')
@patch('pdd.fix_main.get_jwt_token')
def test_fix_main_auto_submit_calls_auth_when_not_local(
    mock_get_jwt_token,
    mock_asyncio,
    mock_cloud_jwt,
    mock_fix_errors,
    mock_construct_paths,
    mock_path,
    mock_run_pytest,
    mock_ctx,
    monkeypatch
):
    """
    Complementary test: when PDD_FORCE_LOCAL is NOT set and auto_submit=True,
    the auth flow SHOULD be triggered (verifying the guard is specific to local mode).
    """
    monkeypatch.delenv("PDD_FORCE_LOCAL", raising=False)
    mock_path.return_value.exists.return_value = True
    mock_ctx.obj['local'] = False

    mock_construct_paths.return_value = (
        {},
        {
            'prompt_file': 'Test prompt content',
            'code_file': 'Test code content',
            'unit_test_file': 'Test test content',
            'error_file': 'Error content'
        },
        {
            'output_test': 'output/test_fixed.py',
            'output_code': 'output/code_fixed.py',
            'output_results': 'results/fix.log'
        },
        None
    )

    mock_fix_errors.return_value = (
        True,
        True,
        "fixed test",
        "fixed code",
        "analysis",
        0.50,
        "gpt-4"
    )

    mock_run_pytest.return_value = (0, 0, 0, "All tests passed")

    # Mock asyncio.run to return a fake JWT so submission proceeds without real auth
    mock_asyncio.run.return_value = "fake_jwt_token"

    m_open = mock_open()
    with patch('builtins.open', m_open), \
         patch('pdd.fix_main.preprocess', return_value="processed prompt"), \
         patch('pdd.fix_main.requests') as mock_requests:
        mock_response = MagicMock()
        mock_response.status_code = 200
        mock_requests.post.return_value = mock_response

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
            auto_submit=True
        )

    assert success is True
    mock_asyncio.run.assert_called_once(), \
        "asyncio.run(get_jwt_token(...)) should be called when not in local mode"


def test_fix_main_auto_submit_guard_exists_in_source():
    """
    Source-level regression test: the auto_submit block in fix_main.py must
    include a PDD_FORCE_LOCAL guard to prevent CI auth hangs.
    """
    from pathlib import Path as RealPath

    fix_main_path = RealPath(__file__).parent.parent / "pdd" / "fix_main.py"
    source = fix_main_path.read_text()

    assert 'auto_submit and not _env_flag_enabled("PDD_FORCE_LOCAL")' in source, \
        "fix_main.py must guard auto_submit with _env_flag_enabled('PDD_FORCE_LOCAL') check"
