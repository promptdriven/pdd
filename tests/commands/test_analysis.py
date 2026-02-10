import os
import pytest
from unittest.mock import patch, MagicMock
from click.testing import CliRunner
from pdd.commands.analysis import detect_change, conflicts, bug, crash, trace, story_test

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
# Tests for 'story-test' command
# -----------------------------------------------------------------------------

def test_story_test_success(runner, mock_context_obj):
    """Test 'story-test' command invokes runner with defaults."""
    with patch("pdd.commands.analysis.run_user_story_tests") as mock_runner:
        mock_runner.return_value = (True, [{"story": "s", "passed": True}], 0.1, "gpt-4")
        result = runner.invoke(story_test, [], obj=mock_context_obj)

        assert result.exit_code == 0
        args, kwargs = mock_runner.call_args
        assert kwargs["prompts_dir"] is None
        assert kwargs["stories_dir"] is None
        assert kwargs["include_llm_prompts"] is False
        assert kwargs["fail_fast"] is True


def test_story_test_options(runner, mock_context_obj):
    """Test 'story-test' command forwards options."""
    with patch("pdd.commands.analysis.run_user_story_tests") as mock_runner:
        mock_runner.return_value = (True, [], 0.0, "gpt-4")
        result = runner.invoke(
            story_test,
            ["--stories-dir", "stories", "--prompts-dir", "prompts", "--include-llm", "--no-fail-fast"],
            obj=mock_context_obj,
        )

        assert result.exit_code == 0
        args, kwargs = mock_runner.call_args
        assert kwargs["prompts_dir"] == "prompts"
        assert kwargs["stories_dir"] == "stories"
        assert kwargs["include_llm_prompts"] is True
        assert kwargs["fail_fast"] is False

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
            
            assert result.exit_code == 0
            mock_handle_error.assert_called_once()
            assert isinstance(mock_handle_error.call_args[0][0], ValueError)
            assert mock_handle_error.call_args[0][1] == "detect"

# -----------------------------------------------------------------------------
# Additional Tests (Fixed to pass context object)
# -----------------------------------------------------------------------------

@patch("pdd.commands.analysis.detect_change_main")
def test_detect_change_success_v2(mock_main, runner, mock_context_obj):
    """Test that detect command parses arguments correctly and calls the main logic."""
    mock_main.return_value = (["result"], 0.5, "gpt-4")
    with runner.isolated_filesystem():
        with open("prompt1.txt", "w") as f: f.write("p1")
        with open("prompt2.txt", "w") as f: f.write("p2")
        with open("change.txt", "w") as f: f.write("change")
        result = runner.invoke(detect_change, ["prompt1.txt", "prompt2.txt", "change.txt", "--output", "out.csv"], obj=mock_context_obj)
        assert result.exit_code == 0
        args, kwargs = mock_main.call_args
        assert kwargs["prompt_files"] == ["prompt1.txt", "prompt2.txt"]
        assert kwargs["change_file"] == "change.txt"
        assert kwargs["output"] == "out.csv"

def test_detect_change_not_enough_args_v2(runner, mock_context_obj):
    """Test that detect command fails if fewer than 2 files are provided."""
    with runner.isolated_filesystem():
        with open("file1.txt", "w") as f: f.write("content")
        result = runner.invoke(detect_change, ["file1.txt"], obj=mock_context_obj)
        assert result.exit_code != 0
        assert "Requires at least one PROMPT_FILE and one CHANGE_FILE" in result.output

@patch("pdd.commands.analysis.detect_change_main")
@patch("pdd.commands.analysis.handle_error")
def test_detect_change_exception_handling_v2(mock_handle_error, mock_main, runner, mock_context_obj):
    """Test that generic exceptions are caught and handled."""
    mock_main.side_effect = Exception("Boom")
    with runner.isolated_filesystem():
        with open("p.txt", "w") as f: f.write("p")
        with open("c.txt", "w") as f: f.write("c")
        result = runner.invoke(detect_change, ["p.txt", "c.txt"], obj=mock_context_obj)
        assert mock_handle_error.called
        assert "Boom" in str(mock_handle_error.call_args[0][0])

@patch("pdd.commands.analysis.conflicts_main")
def test_conflicts_success_v2(mock_main, runner, mock_context_obj):
    """Test conflicts command success path."""
    mock_main.return_value = ([], 0.1, "gpt-4")
    with runner.isolated_filesystem():
        with open("p1.txt", "w") as f: f.write("content")
        with open("p2.txt", "w") as f: f.write("content")
        result = runner.invoke(conflicts, ["p1.txt", "p2.txt", "--output", "res.csv"], obj=mock_context_obj)
        assert result.exit_code == 0
        args, kwargs = mock_main.call_args
        assert kwargs["prompt1"] == "p1.txt"
        assert kwargs["prompt2"] == "p2.txt"
        assert kwargs["output"] == "res.csv"

@patch("pdd.commands.analysis.run_agentic_bug")
def test_bug_agentic_mode_v2(mock_agentic, runner, mock_context_obj):
    """Test bug command in default agentic mode (URL)."""
    mock_agentic.return_value = (True, "Fixed", 1.0, "gpt-4", [])
    result = runner.invoke(bug, ["https://github.com/user/repo/issues/1", "--timeout-adder", "5.0", "--no-github-state"], obj=mock_context_obj)
    assert result.exit_code == 0
    args, kwargs = mock_agentic.call_args
    assert kwargs["issue_url"] == "https://github.com/user/repo/issues/1"
    assert kwargs["timeout_adder"] == 5.0
    assert kwargs["use_github_state"] is False

def test_bug_agentic_mode_missing_arg_v2(runner, mock_context_obj):
    """Test bug command fails in agentic mode without URL."""
    result = runner.invoke(bug, [], obj=mock_context_obj)
    assert result.exit_code != 0
    assert "Agentic mode requires exactly one argument" in result.output

@patch("pdd.commands.analysis.bug_main")
def test_bug_manual_mode_success_v2(mock_bug_main, runner, mock_context_obj):
    """Test bug command in manual mode with 5 files."""
    mock_bug_main.return_value = ("TestCode", 0.5, "gpt-4")
    with runner.isolated_filesystem():
        files = ["p.txt", "c.py", "prog.py", "curr.txt", "des.txt"]
        for f in files:
            with open(f, "w") as fh: fh.write("content")
        result = runner.invoke(bug, ["--manual", "--language", "Java"] + files, obj=mock_context_obj)
        assert result.exit_code == 0
        args, kwargs = mock_bug_main.call_args
        assert kwargs["prompt_file"] == "p.txt"
        assert kwargs["code_file"] == "c.py"
        assert kwargs["program_file"] == "prog.py"
        assert kwargs["current_output"] == "curr.txt"
        assert kwargs["desired_output"] == "des.txt"
        assert kwargs["language"] == "Java"

def test_bug_manual_mode_wrong_arg_count_v2(runner, mock_context_obj):
    """Test bug command manual mode fails with wrong number of args."""
    with runner.isolated_filesystem():
        with open("f1.txt", "w") as f: f.write("x")
        result = runner.invoke(bug, ["--manual", "f1.txt"], obj=mock_context_obj)
        assert result.exit_code != 0
        assert "Manual mode requires 5 arguments" in result.output

def test_bug_manual_mode_file_not_found_v2(runner, mock_context_obj):
    """Test bug command manual mode fails if files don't exist."""
    with runner.isolated_filesystem():
        result = runner.invoke(bug, ["--manual", "a", "b", "c", "d", "e"], obj=mock_context_obj)
        assert result.exit_code != 0
        assert "File does not exist" in result.output

@patch("pdd.commands.analysis.crash_main")
def test_crash_success_v2(mock_crash_main, runner, mock_context_obj):
    """Test crash command success path."""
    mock_crash_main.return_value = (True, "code", "prog", 2, 1.5, "gpt-4")
    with runner.isolated_filesystem():
        files = ["prompt.txt", "code.py", "prog.py", "err.txt"]
        for f in files:
            with open(f, "w") as fh: fh.write("x")
        result = runner.invoke(crash, files + ["--loop", "--max-attempts", "5"], obj=mock_context_obj)
        assert result.exit_code == 0
        args, kwargs = mock_crash_main.call_args
        assert kwargs["prompt_file"] == "prompt.txt"
        assert kwargs["code_file"] == "code.py"
        assert kwargs["program_file"] == "prog.py"
        assert kwargs["error_file"] == "err.txt"
        assert kwargs["loop"] is True
        assert kwargs["max_attempts"] == 5

@patch("pdd.commands.analysis.trace_main")
def test_trace_success_v2(mock_trace_main, runner, mock_context_obj):
    """Test trace command success path."""
    mock_trace_main.return_value = ("Line 10", 0.2, "gpt-4")
    with runner.isolated_filesystem():
        with open("p.txt", "w") as f: f.write("p")
        with open("c.py", "w") as f: f.write("c")
        result = runner.invoke(trace, ["p.txt", "c.py", "42"], obj=mock_context_obj)
        assert result.exit_code == 0
        args, kwargs = mock_trace_main.call_args
        assert kwargs["prompt_file"] == "p.txt"
        assert kwargs["code_file"] == "c.py"
        assert kwargs["code_line"] == 42

def test_trace_invalid_int_v2(runner, mock_context_obj):
    """Test trace command fails if line number is not an int."""
    with runner.isolated_filesystem():
        with open("p.txt", "w") as f: f.write("p")
        with open("c.py", "w") as f: f.write("c")
        result = runner.invoke(trace, ["p.txt", "c.py", "not-an-int"], obj=mock_context_obj)
        assert result.exit_code != 0
        assert "Invalid value for 'CODE_LINE'" in result.output

"""
Test Plan for pdd/commands/analysis.py

1.  **Scope**: This module implements CLI commands (`detect`, `conflicts`, `bug`, `crash`, `trace`) using the `click` library. It acts as an interface layer, parsing arguments, validating inputs, and dispatching execution to underlying logic functions (e.g., `detect_change_main`, `bug_main`).

2.  **Testing Strategy**:
    *   **Unit Tests**: The primary strategy. We will use `click.testing.CliRunner` to simulate CLI execution. This ensures that argument parsing, option handling, and custom validation logic (like the manual file checks in `bug`) work correctly.
    *   **Mocking**: We will mock the underlying "main" functions (e.g., `detect_change_main`) to isolate the CLI layer. We verify that these functions are called with the expected arguments.
    *   **Isolation**: Each test will run in an isolated filesystem (using `runner.isolated_filesystem()`) to handle file existence checks without polluting the real filesystem.

3.  **Z3 Formal Verification**:
    *   **Assessment**: The code primarily consists of imperative glue code, argument parsing, and function dispatch. It does not contain complex algorithmic logic, mathematical constraints, or state machine transitions that benefit significantly from SMT solving.
    *   **Decision**: Z3 is not applicable for this specific module. The logic is best verified through direct functional testing of the CLI interface.

4.  **Test Cases**:
    *   **`detect`**:
        *   Verify success with >= 2 files.
        *   Verify failure with < 2 files.
        *   Verify exception handling (generic exceptions caught and handled).
    *   **`conflicts`**:
        *   Verify success with 2 valid files.
    *   **`bug`**:
        *   **Agentic Mode**: Verify success with 1 URL argument. Verify failure with wrong arg count.
        *   **Manual Mode**: Verify success with 5 valid files. Verify failure with missing files or directories. Verify failure with wrong arg count.
    *   **`crash`**:
        *   Verify success with 4 valid files. Check parameter passing (loop, budget, etc.).
    *   **`trace`**:
        *   Verify success with valid files and line number.

"""

import os
import pytest
from unittest.mock import MagicMock, patch
from click.testing import CliRunner
from pdd.commands.analysis import detect_change, conflicts, bug, crash, trace

# -----------------------------------------------------------------------------
# Fixtures
# -----------------------------------------------------------------------------

@pytest.fixture
def runner():
    """Returns a Click CLI runner."""
    return CliRunner()

@pytest.fixture
def mock_context_obj():
    """Mock context object usually passed via click.obj."""
    return {"verbose": True, "quiet": False}

# -----------------------------------------------------------------------------
# Tests for 'detect' command
# -----------------------------------------------------------------------------

def test_detect_change_success(runner):
    """Test 'detect' command with valid arguments."""
    with runner.isolated_filesystem():
        # Setup
        with open("prompt1.txt", "w") as f: f.write("p1")
        with open("prompt2.txt", "w") as f: f.write("p2")
        with open("change.txt", "w") as f: f.write("change")

        # Mock the underlying main function
        with patch("pdd.commands.analysis.detect_change_main") as mock_main:
            mock_main.return_value = (["result"], 1.0, "gpt-4")
            
            result = runner.invoke(detect_change, ["prompt1.txt", "prompt2.txt", "change.txt"])
            
            assert result.exit_code == 0
            mock_main.assert_called_once()
            
            # Verify args parsing: last file is change_file, rest are prompt_files
            call_kwargs = mock_main.call_args[1]
            assert call_kwargs["change_file"] == "change.txt"
            assert call_kwargs["prompt_files"] == ["prompt1.txt", "prompt2.txt"]

def test_detect_change_insufficient_args(runner):
    """Test 'detect' fails if fewer than 2 files are provided."""
    with runner.isolated_filesystem():
        with open("file1.txt", "w") as f: f.write("content")
        
        result = runner.invoke(detect_change, ["file1.txt"])
        
        assert result.exit_code != 0
        assert "Requires at least one PROMPT_FILE and one CHANGE_FILE" in result.output

def test_detect_change_exception_handling(runner):
    """Test that generic exceptions are handled via handle_error."""
    with runner.isolated_filesystem():
        with open("p.txt", "w") as f: f.write("p")
        with open("c.txt", "w") as f: f.write("c")

        with patch("pdd.commands.analysis.detect_change_main", side_effect=ValueError("Boom")):
            with patch("pdd.commands.analysis.handle_error") as mock_handle_error:
                result = runner.invoke(detect_change, ["p.txt", "c.txt"])
                
                # Should exit cleanly (return None) but handle_error should be called
                assert result.exit_code == 0 
                mock_handle_error.assert_called_once()
                assert "Boom" in str(mock_handle_error.call_args[0][0])

# -----------------------------------------------------------------------------
# Tests for 'conflicts' command
# -----------------------------------------------------------------------------

def test_conflicts_success(runner):
    """Test 'conflicts' command with valid files."""
    with runner.isolated_filesystem():
        with open("p1.txt", "w") as f: f.write("content")
        with open("p2.txt", "w") as f: f.write("content")

        with patch("pdd.commands.analysis.conflicts_main") as mock_main:
            mock_main.return_value = ([], 0.5, "gpt-4")
            
            result = runner.invoke(conflicts, ["p1.txt", "p2.txt", "--output", "out.csv"])
            
            assert result.exit_code == 0
            mock_main.assert_called_once()
            assert mock_main.call_args[1]["prompt1"] == "p1.txt"
            assert mock_main.call_args[1]["prompt2"] == "p2.txt"
            assert mock_main.call_args[1]["output"] == "out.csv"

# -----------------------------------------------------------------------------
# Tests for 'bug' command
# -----------------------------------------------------------------------------

def test_bug_agentic_mode_success(runner):
    """Test 'bug' in default agentic mode (URL argument)."""
    with patch("pdd.commands.analysis.run_agentic_bug") as mock_agentic:
        mock_agentic.return_value = (True, "Fixed", 1.0, "gpt-4", [])
        
        result = runner.invoke(bug, ["https://github.com/user/repo/issues/1", "--timeout-adder", "5.0"])
        
        assert result.exit_code == 0
        mock_agentic.assert_called_once()
        assert mock_agentic.call_args[1]["issue_url"] == "https://github.com/user/repo/issues/1"
        assert mock_agentic.call_args[1]["timeout_adder"] == 5.0
        assert mock_agentic.call_args[1]["use_github_state"] is True

def test_bug_agentic_mode_no_github_state(runner):
    """Test 'bug' agentic mode with --no-github-state flag."""
    with patch("pdd.commands.analysis.run_agentic_bug") as mock_agentic:
        mock_agentic.return_value = (True, "Fixed", 1.0, "gpt-4", [])
        
        result = runner.invoke(bug, ["https://github.com/u/r/i/1", "--no-github-state"])
        
        assert result.exit_code == 0
        assert mock_agentic.call_args[1]["use_github_state"] is False

def test_bug_manual_mode_success(runner):
    """Test 'bug' in manual mode with 5 valid files."""
    with runner.isolated_filesystem():
        files = ["prompt.txt", "code.py", "prog.py", "curr.txt", "des.txt"]
        for f in files:
            with open(f, "w") as fh: fh.write("content")

        with patch("pdd.commands.analysis.bug_main") as mock_main:
            mock_main.return_value = ("TestCode", 1.0, "gpt-4")
            
            args = ["--manual"] + files + ["--language", "Java"]
            result = runner.invoke(bug, args)
            
            assert result.exit_code == 0
            mock_main.assert_called_once()
            kwargs = mock_main.call_args[1]
            assert kwargs["prompt_file"] == "prompt.txt"
            assert kwargs["code_file"] == "code.py"
            assert kwargs["language"] == "Java"

def test_bug_manual_mode_wrong_arg_count(runner):
    """Test 'bug --manual' fails if not exactly 5 arguments."""
    with runner.isolated_filesystem():
        result = runner.invoke(bug, ["--manual", "file1", "file2"])
        assert result.exit_code != 0
        assert "Manual mode requires 5 arguments" in result.output

def test_bug_manual_mode_file_not_found(runner):
    """Test 'bug --manual' fails if a file does not exist."""
    with runner.isolated_filesystem():
        # Create only 4 files
        files = ["f1", "f2", "f3", "f4"]
        for f in files:
            with open(f, "w") as fh: fh.write(".")
        
        # Pass 5 args, last one missing
        args = ["--manual"] + files + ["missing_file"]
        result = runner.invoke(bug, args)
        
        assert result.exit_code != 0
        assert "File does not exist: missing_file" in result.output

def test_bug_manual_mode_directory_error(runner):
    """Test 'bug --manual' fails if an argument is a directory."""
    with runner.isolated_filesystem():
        os.mkdir("mydir")
        files = ["f1", "f2", "f3", "f4"]
        for f in files:
            with open(f, "w") as fh: fh.write(".")
            
        args = ["--manual"] + files + ["mydir"]
        result = runner.invoke(bug, args)
        
        assert result.exit_code != 0
        assert "Path is a directory" in result.output

# -----------------------------------------------------------------------------
# Tests for 'crash' command
# -----------------------------------------------------------------------------

def test_crash_success(runner):
    """Test 'crash' command with valid arguments."""
    with runner.isolated_filesystem():
        files = ["prompt.txt", "code.py", "prog.py", "err.txt"]
        for f in files:
            with open(f, "w") as fh: fh.write(".")

        with patch("pdd.commands.analysis.crash_main") as mock_main:
            # success, final_code, final_program, attempts, total_cost, model_name
            mock_main.return_value = (True, "code", "prog", 2, 0.5, "gpt-4")
            
            result = runner.invoke(crash, files + ["--loop", "--max-attempts", "5"])
            
            assert result.exit_code == 0
            mock_main.assert_called_once()
            kwargs = mock_main.call_args[1]
            assert kwargs["prompt_file"] == "prompt.txt"
            assert kwargs["loop"] is True
            assert kwargs["max_attempts"] == 5

# -----------------------------------------------------------------------------
# Tests for 'trace' command
# -----------------------------------------------------------------------------

def test_trace_success(runner):
    """Test 'trace' command with valid arguments."""
    with runner.isolated_filesystem():
        with open("prompt.txt", "w") as f: f.write(".")
        with open("code.py", "w") as f: f.write(".")

        with patch("pdd.commands.analysis.trace_main") as mock_main:
            mock_main.return_value = ("Line 10", 0.1, "gpt-4")
            
            result = runner.invoke(trace, ["prompt.txt", "code.py", "42"])
            
            assert result.exit_code == 0
            mock_main.assert_called_once()
            kwargs = mock_main.call_args[1]
            assert kwargs["prompt_file"] == "prompt.txt"
            assert kwargs["code_line"] == 42
