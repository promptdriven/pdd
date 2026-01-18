"""
Reproduction test for GitHub Issue #232:
    pdd fix incorrectly prints the name of an output code file when
    no new code file was generated

Issue URL: https://github.com/promptdriven/pdd/issues/232

Bug Description:
    When `pdd fix` only modifies the test file (not the code file), the output
    still prints both file paths:
        Test file: /path/to/test_fixed.py
        Code file: /path/to/code_fixed.py  <-- BUG: This should NOT appear

    The file-saving logic correctly only writes files that have content,
    but the output messaging doesn't follow the same logic.

Location of bug: pdd/fix_main.py lines 418-423
"""

import pytest
from unittest.mock import patch, MagicMock, mock_open
import click
from io import StringIO

from pdd import DEFAULT_STRENGTH
from pdd.fix_main import fix_main


@pytest.fixture
def mock_ctx():
    """Create a mock Click context with default parameters."""
    ctx = MagicMock(spec=click.Context)
    ctx.obj = {
        'force': False,
        'quiet': False,  # IMPORTANT: quiet=False to see output
        'strength': DEFAULT_STRENGTH,
        'temperature': 0.0,
        'verbose': False,
        'time': None,
        'context': None,
        'confirm_callback': None,
        'local': True  # Force local execution
    }
    return ctx


@patch('pdd.fix_main.rprint')
@patch('pdd.fix_main.run_pytest_on_file')
@patch('pdd.fix_main.Path')
@patch('pdd.fix_main.construct_paths')
@patch('pdd.fix_main.fix_errors_from_unit_tests')
def test_issue_232_only_test_file_modified_should_not_print_code_file(
    mock_fix_errors,
    mock_construct_paths,
    mock_path,
    mock_run_pytest,
    mock_rprint,
    mock_ctx
):
    """
    REPRODUCTION TEST for Issue #232.

    Scenario:
        - pdd fix is called
        - The LLM only fixes the test file (fixed_unit_test has content)
        - The LLM does NOT fix the code file (fixed_code is empty)

    Expected behavior:
        - Output should ONLY show: "Test file: ..."
        - Output should NOT show: "Code file: ..." (since it wasn't modified)

    Current buggy behavior:
        - Output shows BOTH paths, even though code file wasn't modified
    """
    mock_path.return_value.exists.return_value = True

    mock_construct_paths.return_value = (
        {},  # resolved_config
        {
            'prompt_file': 'Test prompt',
            'code_file': 'def add(a, b): return a + b',
            'unit_test_file': 'def test_add(): assert add(1, 2) == 4',  # Wrong assertion
            'error_file': 'AssertionError: 3 != 4'
        },
        {
            'output_test': '/home/james/pdd_cap/tests/test_fixed.py',
            'output_code': '/home/james/pdd_cap/code_fixed.py',  # This path should NOT be printed
            'output_results': '/home/james/pdd_cap/fix_results.log'
        },
        None
    )

    # LLM only fixes the test file, NOT the code file
    mock_fix_errors.return_value = (
        True,   # update_unit_test = True (test was fixed)
        False,  # update_code = False (code was NOT modified)
        "def test_add(): assert add(1, 2) == 3",  # Fixed test content
        "",     # Empty string - code was NOT modified
        "Analysis: The test had wrong assertion, fixed expected value",
        0.50,
        "gpt-4"
    )

    # Simulate tests passing after the fix
    mock_run_pytest.return_value = (0, 0, 0, "All tests passed")

    # Execute fix_main
    m_open = mock_open()
    with patch('builtins.open', m_open):
        success, fixed_test, fixed_code, attempts, total_cost, model_name = fix_main(
            ctx=mock_ctx,
            prompt_file="prompt.prompt",
            code_file="code.py",
            unit_test_file="test_code.py",
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

    # Verify the fix was successful
    assert success is True, "Fix should succeed since tests pass"
    assert fixed_test == "def test_add(): assert add(1, 2) == 3"
    assert fixed_code == ""  # Code was NOT modified

    # Collect all rprint calls
    all_rprint_calls = [str(call) for call in mock_rprint.call_args_list]
    output_text = '\n'.join(all_rprint_calls)

    # ASSERTION FOR ISSUE #232:
    # The code file path should NOT be printed when no code file was generated

    # First, verify the test file path WAS printed (expected behavior)
    assert any('/home/james/pdd_cap/tests/test_fixed.py' in str(call) for call in mock_rprint.call_args_list), \
        f"Expected test file path to be printed. Got calls: {all_rprint_calls}"

    # Now check if the code file path was incorrectly printed (THE BUG)
    code_file_printed = any('code_fixed.py' in str(call) for call in mock_rprint.call_args_list)

    # This assertion will FAIL until the bug is fixed
    assert not code_file_printed, (
        "BUG #232: Code file path is being printed even though no code file was modified.\n"
        f"Output included: {output_text}\n"
        "Expected: Only 'Test file: ...' should be printed\n"
        "Got: Both 'Test file: ...' and 'Code file: ...' were printed"
    )


@patch('pdd.fix_main.rprint')
@patch('pdd.fix_main.run_pytest_on_file')
@patch('pdd.fix_main.Path')
@patch('pdd.fix_main.construct_paths')
@patch('pdd.fix_main.fix_errors_from_unit_tests')
def test_issue_232_only_code_file_modified_should_not_print_test_file(
    mock_fix_errors,
    mock_construct_paths,
    mock_path,
    mock_run_pytest,
    mock_rprint,
    mock_ctx
):
    """
    Related test for Issue #232 - opposite scenario.

    Scenario:
        - pdd fix is called
        - The LLM only fixes the code file (fixed_code has content)
        - The LLM does NOT fix the test file (fixed_unit_test is empty)

    Expected behavior:
        - Output should ONLY show: "Code file: ..."
        - Output should NOT show: "Test file: ..." (since it wasn't modified)
    """
    mock_path.return_value.exists.return_value = True

    mock_construct_paths.return_value = (
        {},
        {
            'prompt_file': 'Test prompt',
            'code_file': 'def divide(a, b): return a / b',  # Bug: no zero check
            'unit_test_file': 'def test_divide(): assert divide(10, 2) == 5',
            'error_file': 'ZeroDivisionError when dividing by zero'
        },
        {
            'output_test': '/path/to/test_fixed.py',
            'output_code': '/path/to/code_fixed.py',
            'output_results': '/path/to/fix_results.log'
        },
        None
    )

    # LLM only fixes the code file, NOT the test
    mock_fix_errors.return_value = (
        False,  # update_unit_test = False (test was NOT modified)
        True,   # update_code = True (code was fixed)
        "",     # Empty - test was NOT modified
        "def divide(a, b):\n    if b == 0:\n        raise ValueError('Cannot divide by zero')\n    return a / b",
        "Analysis: Added zero check to divide function",
        0.60,
        "gpt-4"
    )

    mock_run_pytest.return_value = (0, 0, 0, "All tests passed")

    m_open = mock_open()
    with patch('builtins.open', m_open):
        success, fixed_test, fixed_code, attempts, total_cost, model_name = fix_main(
            ctx=mock_ctx,
            prompt_file="prompt.prompt",
            code_file="code.py",
            unit_test_file="test_code.py",
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

    assert success is True
    assert fixed_test == ""  # Test was NOT modified
    assert "raise ValueError" in fixed_code  # Code was modified

    all_rprint_calls = [str(call) for call in mock_rprint.call_args_list]

    # Verify code file path WAS printed
    assert any('code_fixed.py' in str(call) for call in mock_rprint.call_args_list), \
        f"Expected code file path to be printed. Got calls: {all_rprint_calls}"

    # Verify test file path was NOT printed (symmetrical bug)
    test_file_printed = any('test_fixed.py' in str(call) for call in mock_rprint.call_args_list)

    assert not test_file_printed, (
        "BUG #232 (related): Test file path is being printed even though no test file was modified.\n"
        f"Output included: {'\n'.join(all_rprint_calls)}\n"
        "Expected: Only 'Code file: ...' should be printed"
    )


@patch('pdd.fix_main.rprint')
@patch('pdd.fix_main.run_pytest_on_file')
@patch('pdd.fix_main.Path')
@patch('pdd.fix_main.construct_paths')
@patch('pdd.fix_main.fix_errors_from_unit_tests')
def test_both_files_modified_should_print_both_paths(
    mock_fix_errors,
    mock_construct_paths,
    mock_path,
    mock_run_pytest,
    mock_rprint,
    mock_ctx
):
    """
    Positive test: When both files are modified, both paths should be printed.
    This should work correctly both before and after the bug fix.
    """
    mock_path.return_value.exists.return_value = True

    mock_construct_paths.return_value = (
        {},
        {
            'prompt_file': 'Test prompt',
            'code_file': 'original code',
            'unit_test_file': 'original test',
            'error_file': 'Some error'
        },
        {
            'output_test': '/path/to/test_fixed.py',
            'output_code': '/path/to/code_fixed.py',
            'output_results': '/path/to/fix_results.log'
        },
        None
    )

    # LLM fixes BOTH files
    mock_fix_errors.return_value = (
        True,   # update_unit_test = True
        True,   # update_code = True
        "fixed test content",
        "fixed code content",
        "Analysis: Fixed both files",
        0.75,
        "gpt-4"
    )

    mock_run_pytest.return_value = (0, 0, 0, "All tests passed")

    m_open = mock_open()
    with patch('builtins.open', m_open):
        success, _, _, _, _, _ = fix_main(
            ctx=mock_ctx,
            prompt_file="prompt.prompt",
            code_file="code.py",
            unit_test_file="test_code.py",
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

    assert success is True

    all_rprint_calls = [str(call) for call in mock_rprint.call_args_list]

    # Both paths should be printed
    assert any('test_fixed.py' in str(call) for call in mock_rprint.call_args_list), \
        "Test file path should be printed when test was modified"
    assert any('code_fixed.py' in str(call) for call in mock_rprint.call_args_list), \
        "Code file path should be printed when code was modified"
