import pytest
from unittest.mock import mock_open, patch, MagicMock, call
import os
from typing import Tuple, Optional
import git

# Absolute import based on the provided directory structure
from pdd.git_update import git_update, DEFAULT_TIME
from rich.panel import Panel
from pdd import DEFAULT_STRENGTH

# Sample data for tests
INPUT_PROMPT = "Please add two numbers and return the sum."
MODIFIED_CODE_FILE = "/path/to/modified_code.py"
STRENGTH = DEFAULT_STRENGTH
TEMPERATURE = 0.5
ORIGINAL_CODE = "def add(a, b): return a + b"
MODIFIED_CODE = "def add(a, b): return a + b + 1"
MODIFIED_PROMPT = "Please add two numbers and return the sum plus one."
TOTAL_COST = 0.123456
MODEL_NAME = "gpt-4"
# Expected relative path based on MODIFIED_CODE_FILE and mocked repo_root
EXPECTED_RELATIVE_PATH = os.path.basename(MODIFIED_CODE_FILE)

@pytest.fixture
def mock_repo():
    with patch('pdd.git_update.git.Repo') as mock_repo_class:
        mock_repo_instance = MagicMock()
        # Mock rev_parse to return the directory of MODIFIED_CODE_FILE as repo_root
        # This makes os.path.relpath(MODIFIED_CODE_FILE, repo_root) yield the basename.
        mock_repo_instance.git.rev_parse.return_value = os.path.dirname(MODIFIED_CODE_FILE)
        mock_repo_class.return_value = mock_repo_instance
        yield mock_repo_instance

@pytest.fixture
def mock_update_prompt():
    with patch('pdd.git_update.update_prompt') as mock_func:
        yield mock_func

@pytest.fixture
def mock_console_print():
    with patch('pdd.git_update.console.print') as mock_print:
        yield mock_print

# Helper to set up mock_open side effects
def setup_mock_open_side_effects(mock_open_patcher, read_modified_data, read_original_data, expect_write=True):
    mock_read_modified_handle = MagicMock()
    mock_read_modified_handle.read.return_value = read_modified_data
    mock_read_modified_handle.__enter__.return_value = mock_read_modified_handle
    mock_read_modified_handle.__exit__.return_value = None

    mock_read_original_handle = MagicMock()
    mock_read_original_handle.read.return_value = read_original_data
    mock_read_original_handle.__enter__.return_value = mock_read_original_handle
    mock_read_original_handle.__exit__.return_value = None

    mock_write_handle = None
    side_effects = [mock_read_modified_handle, mock_read_original_handle]

    if expect_write:
        mock_write_handle = MagicMock()
        mock_write_handle.__enter__.return_value = mock_write_handle
        mock_write_handle.__exit__.return_value = None
        side_effects.append(mock_write_handle)

    mock_open_patcher.side_effect = side_effects
    return mock_write_handle

@patch('pdd.git_update.open')
def test_git_update_success(mock_open_func, mock_repo, mock_update_prompt, mock_console_print):
    """
    Test the successful execution of git_update with valid inputs.
    """
    mock_write_handle = setup_mock_open_side_effects(mock_open_func, MODIFIED_CODE, ORIGINAL_CODE, expect_write=True)
    
    with patch('pdd.git_update.os.path.exists', return_value=True):
        mock_update_prompt.return_value = (MODIFIED_PROMPT, TOTAL_COST, MODEL_NAME)
        
        result = git_update(
            input_prompt=INPUT_PROMPT,
            modified_code_file=MODIFIED_CODE_FILE,
            strength=STRENGTH,
            temperature=TEMPERATURE,
            verbose=False,
            time=DEFAULT_TIME
        )
        
        assert result == (MODIFIED_PROMPT, TOTAL_COST, MODEL_NAME)
        
        mock_repo.git.checkout.assert_called_once_with('HEAD', '--', EXPECTED_RELATIVE_PATH)
        
        expected_open_calls = [
            call(MODIFIED_CODE_FILE, 'r'),
            call(MODIFIED_CODE_FILE, 'r'),
            call(MODIFIED_CODE_FILE, 'w')
        ]
        mock_open_func.assert_has_calls(expected_open_calls)
        assert mock_open_func.call_count == 3

        mock_update_prompt.assert_called_once_with(
            input_prompt=INPUT_PROMPT,
            input_code=ORIGINAL_CODE,
            modified_code=MODIFIED_CODE,
            strength=STRENGTH,
            temperature=TEMPERATURE,
            verbose=False,
            time=DEFAULT_TIME
        )
        
        assert mock_write_handle is not None
        mock_write_handle.write.assert_called_once_with(MODIFIED_CODE)

        expected_panel = Panel.fit(
            f"[bold green]Success:[/bold green]\n"
            f"Modified prompt: {MODIFIED_PROMPT}\n"
            f"Total cost: ${TOTAL_COST:.6f}\n"
            f"Model name: {MODEL_NAME}"
        )
        assert mock_console_print.call_count == 1
        printed_panel = mock_console_print.call_args[0][0]
        assert isinstance(printed_panel, Panel)
        assert MODIFIED_PROMPT in str(printed_panel.renderable)

def test_git_update_missing_input_prompt(mock_repo, mock_update_prompt, mock_console_print):
    """
    Test git_update when input_prompt is missing.
    """
    result = git_update(
        input_prompt="",
        modified_code_file=MODIFIED_CODE_FILE,
        strength=STRENGTH,
        temperature=TEMPERATURE
    )
    assert result == (None, 0.0, "")
    mock_console_print.assert_called()
    mock_update_prompt.assert_not_called()

def test_git_update_missing_modified_code_file(mock_repo, mock_update_prompt, mock_console_print):
    """
    Test git_update when modified_code_file path is missing.
    """
    result = git_update(
        input_prompt=INPUT_PROMPT,
        modified_code_file="",
        strength=STRENGTH,
        temperature=TEMPERATURE
    )
    assert result == (None, 0.0, "")
    mock_console_print.assert_called()
    mock_update_prompt.assert_not_called()

def test_git_update_file_not_found(mock_repo, mock_update_prompt, mock_console_print):
    """
    Test git_update when the modified_code_file does not exist.
    """
    with patch('pdd.git_update.os.path.exists', return_value=False):
        result = git_update(
            input_prompt=INPUT_PROMPT,
            modified_code_file=MODIFIED_CODE_FILE,
            strength=STRENGTH,
            temperature=TEMPERATURE
        )
        assert result == (None, 0.0, "")
        mock_console_print.assert_called()
        mock_update_prompt.assert_not_called()

def test_git_update_not_a_git_repo(mock_repo, mock_update_prompt, mock_console_print):
    """
    Test git_update when the current directory is not a Git repository.
    """
    # Simulate git.Repo raising an exception OR checkout failing
    # If Repo init fails, open won't be called. If checkout fails, first open is called.
    # Let's simulate checkout failure as per original test intent.
    mock_repo.git.checkout.side_effect = git.exc.InvalidGitRepositoryError("Not a git repo")
    
    # The first open (to read modified_code) will still occur
    with patch('pdd.git_update.open', mock_open(read_data=MODIFIED_CODE)):
        with patch('pdd.git_update.os.path.exists', return_value=True):
            result = git_update(
                input_prompt=INPUT_PROMPT,
                modified_code_file=MODIFIED_CODE_FILE,
                strength=STRENGTH,
                temperature=TEMPERATURE
            )
            assert result == (None, 0.0, "")
            mock_console_print.assert_called()
            mock_update_prompt.assert_not_called()

@patch('pdd.git_update.open')
def test_git_update_update_prompt_exception(mock_open_func, mock_repo, mock_update_prompt, mock_console_print):
    """
    Test git_update when update_prompt raises an exception.
    """
    setup_mock_open_side_effects(mock_open_func, MODIFIED_CODE, ORIGINAL_CODE, expect_write=False)
    
    with patch('pdd.git_update.os.path.exists', return_value=True):
        mock_update_prompt.side_effect = Exception("Model error")
        result = git_update(
            input_prompt=INPUT_PROMPT,
            modified_code_file=MODIFIED_CODE_FILE,
            strength=STRENGTH,
            temperature=TEMPERATURE,
            verbose=False,
            time=DEFAULT_TIME
        )
        assert result == (None, 0.0, "")
        mock_console_print.assert_called()
        mock_update_prompt.assert_called_once_with(
            input_prompt=INPUT_PROMPT,
            input_code=ORIGINAL_CODE,
            modified_code=MODIFIED_CODE,
            strength=STRENGTH,
            temperature=TEMPERATURE,
            verbose=False,
            time=DEFAULT_TIME
        )

@patch('pdd.git_update.open')
def test_git_update_file_write_failure(mock_open_func, mock_repo, mock_update_prompt, mock_console_print):
    """
    Test git_update when writing back the modified code file fails.
    """
    mock_write_handle = setup_mock_open_side_effects(mock_open_func, MODIFIED_CODE, ORIGINAL_CODE, expect_write=True)
    
    with patch('pdd.git_update.os.path.exists', return_value=True):
        assert mock_write_handle is not None
        mock_write_handle.write.side_effect = IOError("Write failed")
        mock_update_prompt.return_value = (MODIFIED_PROMPT, TOTAL_COST, MODEL_NAME)
        
        result = git_update(
            input_prompt=INPUT_PROMPT,
            modified_code_file=MODIFIED_CODE_FILE,
            strength=STRENGTH,
            temperature=TEMPERATURE,
            verbose=False,
            time=DEFAULT_TIME
        )
        assert result == (None, 0.0, "")
        mock_console_print.assert_called()
        mock_update_prompt.assert_called_once_with(
            input_prompt=INPUT_PROMPT,
            input_code=ORIGINAL_CODE,
            modified_code=MODIFIED_CODE,
            strength=STRENGTH,
            temperature=TEMPERATURE,
            verbose=False,
            time=DEFAULT_TIME
        )
        mock_write_handle.write.assert_called_once_with(MODIFIED_CODE)

@patch('pdd.git_update.open')
def test_git_update_invalid_strength_temperature(mock_open_func, mock_repo, mock_update_prompt, mock_console_print):
    """
    Test git_update with invalid strength and temperature values.
    """
    # Assuming the function does not explicitly validate strength and temperature,
    # and update_prompt handles them or passes them through.
    mock_write_handle = setup_mock_open_side_effects(mock_open_func, MODIFIED_CODE, ORIGINAL_CODE, expect_write=True)

    with patch('pdd.git_update.os.path.exists', return_value=True):
        mock_update_prompt.return_value = (MODIFIED_PROMPT, TOTAL_COST, MODEL_NAME)
        
        result = git_update(
            input_prompt=INPUT_PROMPT,
            modified_code_file=MODIFIED_CODE_FILE,
            strength=-1.0,        # Invalid strength
            temperature=2.0,      # Invalid temperature
            verbose=False,
            time=DEFAULT_TIME
        )
        
        assert result == (MODIFIED_PROMPT, TOTAL_COST, MODEL_NAME) # Expect success if update_prompt handles it
        
        mock_update_prompt.assert_called_once_with(
            input_prompt=INPUT_PROMPT,
            input_code=ORIGINAL_CODE,
            modified_code=MODIFIED_CODE,
            strength=-1.0,
            temperature=2.0,
            verbose=False,
            time=DEFAULT_TIME
        )
        assert mock_write_handle is not None
        mock_write_handle.write.assert_called_once_with(MODIFIED_CODE)
        
        # Check for success panel print
        expected_panel = Panel.fit(
            f"[bold green]Success:[/bold green]\n"
            f"Modified prompt: {MODIFIED_PROMPT}\n"
            f"Total cost: ${TOTAL_COST:.6f}\n"
            f"Model name: {MODEL_NAME}"
        )
        assert mock_console_print.call_count == 1
        printed_panel = mock_console_print.call_args[0][0]
        assert isinstance(printed_panel, Panel)
        assert MODIFIED_PROMPT in str(printed_panel.renderable)

@patch('pdd.git_update.open')
def test_git_update_empty_original_code(mock_open_func, mock_repo, mock_update_prompt, mock_console_print):
    """
    Test git_update when the original code file is empty (after checkout)
    and the modified code is also empty for this test's purpose.
    """
    # Simulate user modified to empty, and checked-out version is also empty
    empty_code = ""
    mock_write_handle = setup_mock_open_side_effects(mock_open_func, empty_code, empty_code, expect_write=True)

    with patch('pdd.git_update.os.path.exists', return_value=True):
        mock_update_prompt.return_value = (MODIFIED_PROMPT, TOTAL_COST, MODEL_NAME)
        result = git_update(
            input_prompt=INPUT_PROMPT,
            modified_code_file=MODIFIED_CODE_FILE,
            strength=STRENGTH,
            temperature=TEMPERATURE,
            verbose=False,
            time=DEFAULT_TIME
        )
        assert result == (MODIFIED_PROMPT, TOTAL_COST, MODEL_NAME)
        mock_update_prompt.assert_called_once_with(
            input_prompt=INPUT_PROMPT,
            input_code=empty_code,
            modified_code=empty_code,
            strength=STRENGTH,
            temperature=TEMPERATURE,
            verbose=False,
            time=DEFAULT_TIME
        )
        assert mock_write_handle is not None
        mock_write_handle.write.assert_called_once_with(empty_code)

@patch('pdd.git_update.open')
def test_git_update_non_tuple_return(mock_open_func, mock_repo, mock_update_prompt, mock_console_print):
    """
    Test git_update when update_prompt returns a non-tuple value.
    This should cause a TypeError during unpacking, caught by the general Exception handler.
    """
    # update_prompt is called, but then unpacking its result fails. No write should occur.
    setup_mock_open_side_effects(mock_open_func, MODIFIED_CODE, ORIGINAL_CODE, expect_write=False)
    
    with patch('pdd.git_update.os.path.exists', return_value=True):
        mock_update_prompt.return_value = "incorrect return type" # Non-tuple
        
        result = git_update(
            input_prompt=INPUT_PROMPT,
            modified_code_file=MODIFIED_CODE_FILE,
            strength=STRENGTH,
            temperature=TEMPERATURE,
            verbose=False,
            time=DEFAULT_TIME
        )
        
        assert result == (None, 0.0, "") # Expect graceful failure
        mock_console_print.assert_called() # Error panel should be printed
        mock_update_prompt.assert_called_once_with(
            input_prompt=INPUT_PROMPT,
            input_code=ORIGINAL_CODE,
            modified_code=MODIFIED_CODE,
            strength=STRENGTH,
            temperature=TEMPERATURE,
            verbose=False,
            time=DEFAULT_TIME
        )