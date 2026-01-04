"""
Test Plan for pdd/commands/analysis.py

1.  **Code Analysis**:
    The module `pdd/commands/analysis.py` defines five Click commands: `detect`, `conflicts`, `bug`, `crash`, and `trace`.
    These commands act as an interface layer (CLI) that parses arguments, validates inputs (file existence, counts), and delegates execution to specific logic functions (`detect_change_main`, `conflicts_main`, etc.).
    They are decorated with `@track_cost` and use `handle_error` for exception management.

2.  **Z3 Formal Verification Analysis**:
    Z3 is a theorem prover used for verifying logical constraints, complex state machines, or mathematical algorithms.
    The code under test is primarily "glue code": it maps CLI arguments to function calls. The logic consists of simple conditional checks (e.g., `if len(args) < 2`) and file existence checks.
    There are no complex algorithms, constraint satisfaction problems, or intricate state transitions here.
    **Conclusion**: Z3 formal verification is not suitable or necessary for this module. Standard unit/integration tests using mocks are the most effective way to verify that the CLI commands correctly parse arguments and invoke the underlying logic.

3.  **Unit Test Strategy**:
    We will use `pytest` and `click.testing.CliRunner` to simulate CLI execution.
    We will use `unittest.mock.patch` to mock the underlying "main" functions (`detect_change_main`, `bug_main`, etc.) to verify they are called with the expected arguments.
    We will verify:
    *   **Argument Parsing**: Correct handling of positional arguments and options.
    *   **Validation**: File existence checks and argument count validation.
    *   **Delegation**: The correct underlying function is called with the correct parameters.
    *   **Error Handling**: Exceptions raised by underlying functions are caught and passed to `handle_error`.
    *   **Modes**: Specifically for `bug`, verify switching between "Agentic" and "Manual" modes.

4.  **Test Cases**:
    *   `test_detect_change_success`: Verify `detect` splits files into prompts and change file correctly.
    *   `test_detect_change_insufficient_args`: Verify error when < 2 files provided.
    *   `test_conflicts_success`: Verify `conflicts` calls `conflicts_main`.
    *   `test_bug_agentic_success`: Verify `bug` (default) calls `run_agentic_bug`.
    *   `test_bug_manual_success`: Verify `bug --manual` calls `bug_main` with 5 files.
    *   `test_bug_manual_validation_errors`: Verify errors for wrong arg count or missing files.
    *   `test_crash_success`: Verify `crash` calls `crash_main`.
    *   `test_trace_success`: Verify `trace` calls `trace_main`.
    *   `test_generic_exception_handling`: Verify `handle_error` is used when an exception occurs.
"""

import os
import pytest
from unittest.mock import patch, MagicMock
from click.testing import CliRunner
from pdd.commands.analysis import detect_change, conflicts, bug, crash, trace

# -----------------------------------------------------------------------------
# Fixtures
# -----------------------------------------------------------------------------

@pytest.fixture
def runner():
    """Fixture for Click CliRunner."""
    return CliRunner()

@pytest.fixture
def mock_context_obj():
    """Fixture for the context object expected by the commands."""
    return {'verbose': False, 'quiet': False}

# -----------------------------------------------------------------------------
# Tests for 'detect' command
# -----------------------------------------------------------------------------

def test_detect_change_success(runner, mock_context_obj):
    """Test 'detect' command with valid arguments."""
    with patch('pdd.commands.analysis.detect_change_main') as mock_main:
        # Setup mock return
        mock_main.return_value = ([], 0.0, "gpt-4")
        
        with runner.isolated_filesystem():
            # Create dummy files
            with open("p1.prompt", "w") as f: f.write("content")
            with open("p2.prompt", "w") as f: f.write("content")
            with open("change.txt", "w") as f: f.write("change")

            result = runner.invoke(detect_change, ['p1.prompt', 'p2.prompt', 'change.txt', '--output', 'out.csv'], obj=mock_context_obj)

            assert result.exit_code == 0
            
            # Verify detect_change_main was called correctly
            # The last file is the change file, others are prompt files
            args, kwargs = mock_main.call_args
            assert kwargs['prompt_files'] == ['p1.prompt', 'p2.prompt']
            assert kwargs['change_file'] == 'change.txt'
            assert kwargs['output'] == 'out.csv'

def test_detect_change_insufficient_args(runner, mock_context_obj):
    """Test 'detect' command fails with fewer than 2 files."""
    with runner.isolated_filesystem():
        with open("p1.prompt", "w") as f: f.write("content")
        
        result = runner.invoke(detect_change, ['p1.prompt'], obj=mock_context_obj)
        
        assert result.exit_code != 0
        assert "Requires at least one PROMPT_FILE and one CHANGE_FILE" in result.output

# -----------------------------------------------------------------------------
# Tests for 'conflicts' command
# -----------------------------------------------------------------------------

def test_conflicts_success(runner, mock_context_obj):
    """Test 'conflicts' command with valid arguments."""
    with patch('pdd.commands.analysis.conflicts_main') as mock_main:
        mock_main.return_value = ([], 0.0, "gpt-4")
        
        with runner.isolated_filesystem():
            with open("p1.prompt", "w") as f: f.write("c")
            with open("p2.prompt", "w") as f: f.write("c")

            result = runner.invoke(conflicts, ['p1.prompt', 'p2.prompt'], obj=mock_context_obj)
            
            assert result.exit_code == 0
            mock_main.assert_called_once()
            assert mock_main.call_args[1]['prompt1'] == 'p1.prompt'
            assert mock_main.call_args[1]['prompt2'] == 'p2.prompt'

# -----------------------------------------------------------------------------
# Tests for 'bug' command
# -----------------------------------------------------------------------------

def test_bug_agentic_success(runner, mock_context_obj):
    """Test 'bug' command in default agentic mode."""
    with patch('pdd.commands.analysis.run_agentic_bug') as mock_agentic:
        # Mock return: success, message, cost, model, changed_files
        mock_agentic.return_value = (True, "Fixed", 0.5, "gpt-4", ["file.py"])
        
        result = runner.invoke(bug, ['https://github.com/issues/1'], obj=mock_context_obj)
        
        assert result.exit_code == 0
        mock_agentic.assert_called_once()
        assert mock_agentic.call_args[1]['issue_url'] == 'https://github.com/issues/1'

def test_bug_agentic_wrong_args(runner, mock_context_obj):
    """Test 'bug' agentic mode fails with wrong number of arguments."""
    result = runner.invoke(bug, ['arg1', 'arg2'], obj=mock_context_obj)
    assert result.exit_code != 0
    assert "Agentic mode requires exactly one argument" in result.output

def test_bug_manual_success(runner, mock_context_obj):
    """Test 'bug' command in manual mode."""
    with patch('pdd.commands.analysis.bug_main') as mock_main:
        mock_main.return_value = ("test code", 0.1, "gpt-4")
        
        with runner.isolated_filesystem():
            # Create 5 dummy files
            files = ['p.prompt', 'c.py', 'prog.py', 'curr.txt', 'des.txt']
            for f in files:
                with open(f, 'w') as fh: fh.write("content")

            args = ['--manual'] + files + ['--language', 'Python']
            result = runner.invoke(bug, args, obj=mock_context_obj)
            
            assert result.exit_code == 0
            mock_main.assert_called_once()
            kwargs = mock_main.call_args[1]
            assert kwargs['prompt_file'] == 'p.prompt'
            assert kwargs['code_file'] == 'c.py'
            assert kwargs['program_file'] == 'prog.py'
            assert kwargs['current_output'] == 'curr.txt'
            assert kwargs['desired_output'] == 'des.txt'
            assert kwargs['language'] == 'Python'

def test_bug_manual_missing_file(runner, mock_context_obj):
    """Test 'bug' manual mode fails if a file does not exist."""
    with runner.isolated_filesystem():
        # Only create 4 files
        files = ['p.prompt', 'c.py', 'prog.py', 'curr.txt']
        for f in files:
            with open(f, 'w') as fh: fh.write("content")
        
        # Pass a 5th non-existent file
        args = ['--manual'] + files + ['missing.txt']
        result = runner.invoke(bug, args, obj=mock_context_obj)
        
        assert result.exit_code != 0
        assert "File does not exist" in result.output

def test_bug_manual_wrong_arg_count(runner, mock_context_obj):
    """Test 'bug' manual mode fails with wrong number of arguments."""
    with runner.isolated_filesystem():
        args = ['--manual', 'f1']
        result = runner.invoke(bug, args, obj=mock_context_obj)
        assert result.exit_code != 0
        assert "Manual mode requires 5 arguments" in result.output

# -----------------------------------------------------------------------------
# Tests for 'crash' command
# -----------------------------------------------------------------------------

def test_crash_success(runner, mock_context_obj):
    """Test 'crash' command with valid arguments."""
    with patch('pdd.commands.analysis.crash_main') as mock_main:
        # success, final_code, final_program, attempts, cost, model
        mock_main.return_value = (True, "code", "prog", 1, 0.1, "gpt-4")
        
        with runner.isolated_filesystem():
            files = ['p.prompt', 'c.py', 'prog.py', 'err.log']
            for f in files:
                with open(f, 'w') as fh: fh.write("content")

            args = files + ['--loop', '--budget', '10.0']
            result = runner.invoke(crash, args, obj=mock_context_obj)
            
            assert result.exit_code == 0
            mock_main.assert_called_once()
            kwargs = mock_main.call_args[1]
            assert kwargs['prompt_file'] == 'p.prompt'
            assert kwargs['error_file'] == 'err.log'
            assert kwargs['loop'] is True
            assert kwargs['budget'] == 10.0

# -----------------------------------------------------------------------------
# Tests for 'trace' command
# -----------------------------------------------------------------------------

def test_trace_success(runner, mock_context_obj):
    """Test 'trace' command with valid arguments."""
    with patch('pdd.commands.analysis.trace_main') as mock_main:
        mock_main.return_value = (10, 0.05, "gpt-4")
        
        with runner.isolated_filesystem():
            with open("p.prompt", "w") as f: f.write("content")
            with open("c.py", "w") as f: f.write("content")

            result = runner.invoke(trace, ['p.prompt', 'c.py', '15'], obj=mock_context_obj)
            
            assert result.exit_code == 0
            mock_main.assert_called_once()
            assert mock_main.call_args[1]['code_line'] == 15

# -----------------------------------------------------------------------------
# Tests for Error Handling
# -----------------------------------------------------------------------------

def test_generic_exception_handling(runner, mock_context_obj):
    """Test that exceptions are caught and passed to handle_error."""
    with patch('pdd.commands.analysis.detect_change_main') as mock_main, \
         patch('pdd.commands.analysis.handle_error') as mock_handle_error:
        
        # Simulate an unexpected error
        mock_main.side_effect = ValueError("Something went wrong")
        
        with runner.isolated_filesystem():
            with open("p1.prompt", "w") as f: f.write("c")
            with open("p2.prompt", "w") as f: f.write("c")
            with open("change.txt", "w") as f: f.write("c")

            result = runner.invoke(detect_change, ['p1.prompt', 'p2.prompt', 'change.txt'], obj=mock_context_obj)
            
            # The command should exit gracefully (exit code 0 usually if handled, or whatever handle_error does)
            # Since handle_error is mocked, the function returns None.
            # Click commands returning None usually exit with 0 unless exception raised.
            assert result.exit_code == 0
            mock_handle_error.assert_called_once()
            assert isinstance(mock_handle_error.call_args[0][0], ValueError)
            assert mock_handle_error.call_args[0][1] == "detect"
