import pytest
from unittest.mock import mock_open, patch, MagicMock, call
import os
from typing import Tuple, Optional
import git

# Absolute import based on the provided directory structure
from pdd.git_update import git_update, DEFAULT_TIME
from rich.panel import Panel
from pdd import DEFAULT_STRENGTH

# Constants for agentic tests
PROMPT_FILE = "/path/to/prompt.prompt"
UPDATED_PROMPT_CONTENT = "Updated prompt content from agentic"
AGENTIC_COST = 0.05
AGENTIC_PROVIDER = "anthropic"

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
        # Mock the working_tree_dir to return the directory of MODIFIED_CODE_FILE
        # This makes os.path.relpath(MODIFIED_CODE_FILE, repo_root) yield the basename.
        mock_repo_instance.working_tree_dir = os.path.dirname(MODIFIED_CODE_FILE)
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

@pytest.fixture
def mock_get_available_agents():
    with patch('pdd.git_update.get_available_agents') as mock_func:
        yield mock_func

@pytest.fixture
def mock_run_agentic_update():
    with patch('pdd.git_update.run_agentic_update') as mock_func:
        yield mock_func

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
def test_git_update_success(mock_open_func, mock_repo, mock_update_prompt, mock_console_print, mock_get_available_agents):
    """
    Test the successful execution of git_update with valid inputs (legacy path).
    """
    # Return no agents so legacy path is used
    mock_get_available_agents.return_value = []
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
def test_git_update_update_prompt_exception(mock_open_func, mock_repo, mock_update_prompt, mock_console_print, mock_get_available_agents):
    """
    Test git_update when update_prompt raises an exception.
    Modified code should still be restored (bug fix).
    """
    # Return no agents so legacy path is used
    mock_get_available_agents.return_value = []
    # expect_write=True because we now always restore modified code (bug fix)
    mock_write_handle = setup_mock_open_side_effects(mock_open_func, MODIFIED_CODE, ORIGINAL_CODE, expect_write=True)

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
        # Verify modified code was restored even on exception
        assert mock_write_handle is not None
        mock_write_handle.write.assert_called_once_with(MODIFIED_CODE)

@patch('pdd.git_update.open')
def test_git_update_file_write_failure(mock_open_func, mock_repo, mock_update_prompt, mock_console_print, mock_get_available_agents):
    """
    Test git_update when writing back the modified code file fails.
    Note: With try/finally, write failure in finally is caught and ignored (best effort).
    The function should still return success from update_prompt.
    """
    # Return no agents so legacy path is used
    mock_get_available_agents.return_value = []
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
        # With try/finally, write failure in finally is caught and ignored
        # The function returns success from the try block
        assert result == (MODIFIED_PROMPT, TOTAL_COST, MODEL_NAME)
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
def test_git_update_invalid_strength_temperature(mock_open_func, mock_repo, mock_update_prompt, mock_console_print, mock_get_available_agents):
    """
    Test git_update with invalid strength and temperature values.
    """
    # Return no agents so legacy path is used
    mock_get_available_agents.return_value = []
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
def test_git_update_empty_original_code(mock_open_func, mock_repo, mock_update_prompt, mock_console_print, mock_get_available_agents):
    """
    Test git_update when the original code file is empty (after checkout)
    and the modified code is also empty for this test's purpose.
    """
    # Return no agents so legacy path is used
    mock_get_available_agents.return_value = []
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
def test_git_update_non_tuple_return(mock_open_func, mock_repo, mock_update_prompt, mock_console_print, mock_get_available_agents):
    """
    Test git_update when update_prompt returns a non-tuple value.
    This should cause a TypeError during unpacking, caught by the general Exception handler.
    Modified code should still be restored (bug fix).
    """
    # Return no agents so legacy path is used
    mock_get_available_agents.return_value = []
    # expect_write=True because we now always restore modified code (bug fix)
    mock_write_handle = setup_mock_open_side_effects(mock_open_func, MODIFIED_CODE, ORIGINAL_CODE, expect_write=True)

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
        # Verify modified code was restored even on exception
        assert mock_write_handle is not None
        mock_write_handle.write.assert_called_once_with(MODIFIED_CODE)


# ============== AGENTIC PATH TESTS ==============

@patch('pdd.git_update.open')
def test_git_update_agentic_success(mock_open_func, mock_repo, mock_update_prompt, mock_console_print, mock_get_available_agents, mock_run_agentic_update):
    """
    Test git_update using the agentic path successfully.
    """
    mock_get_available_agents.return_value = ["anthropic"]
    mock_run_agentic_update.return_value = (True, "Success", AGENTIC_COST, AGENTIC_PROVIDER, [PROMPT_FILE])

    # Setup: read modified, read original, read updated prompt, write modified back
    mock_read_modified = MagicMock()
    mock_read_modified.read.return_value = MODIFIED_CODE
    mock_read_modified.__enter__ = MagicMock(return_value=mock_read_modified)
    mock_read_modified.__exit__ = MagicMock(return_value=None)

    mock_read_original = MagicMock()
    mock_read_original.read.return_value = ORIGINAL_CODE
    mock_read_original.__enter__ = MagicMock(return_value=mock_read_original)
    mock_read_original.__exit__ = MagicMock(return_value=None)

    mock_read_prompt = MagicMock()
    mock_read_prompt.read.return_value = UPDATED_PROMPT_CONTENT
    mock_read_prompt.__enter__ = MagicMock(return_value=mock_read_prompt)
    mock_read_prompt.__exit__ = MagicMock(return_value=None)

    mock_write = MagicMock()
    mock_write.__enter__ = MagicMock(return_value=mock_write)
    mock_write.__exit__ = MagicMock(return_value=None)

    mock_open_func.side_effect = [mock_read_modified, mock_read_original, mock_read_prompt, mock_write]

    with patch('pdd.git_update.os.path.exists', return_value=True):
        result = git_update(
            input_prompt=INPUT_PROMPT,
            modified_code_file=MODIFIED_CODE_FILE,
            strength=STRENGTH,
            temperature=TEMPERATURE,
            verbose=True,
            time=DEFAULT_TIME,
            simple=False,
            quiet=False,
            prompt_file=PROMPT_FILE
        )

        assert result == (UPDATED_PROMPT_CONTENT, AGENTIC_COST, AGENTIC_PROVIDER)
        mock_run_agentic_update.assert_called_once_with(
            prompt_file=PROMPT_FILE,
            code_file=MODIFIED_CODE_FILE,
            verbose=True,
            quiet=False
        )
        # Legacy update_prompt should NOT be called
        mock_update_prompt.assert_not_called()
        # Modified code should be restored
        mock_write.write.assert_called_once_with(MODIFIED_CODE)


@patch('pdd.git_update.open')
def test_git_update_agentic_fails_fallback_to_legacy(mock_open_func, mock_repo, mock_update_prompt, mock_console_print, mock_get_available_agents, mock_run_agentic_update):
    """
    Test git_update when agentic fails and falls back to legacy.
    """
    mock_get_available_agents.return_value = ["anthropic"]
    # Agentic fails
    mock_run_agentic_update.return_value = (False, "Failed", AGENTIC_COST, "", [])

    mock_write_handle = setup_mock_open_side_effects(mock_open_func, MODIFIED_CODE, ORIGINAL_CODE, expect_write=True)

    with patch('pdd.git_update.os.path.exists', return_value=True):
        mock_update_prompt.return_value = (MODIFIED_PROMPT, TOTAL_COST, MODEL_NAME)

        result = git_update(
            input_prompt=INPUT_PROMPT,
            modified_code_file=MODIFIED_CODE_FILE,
            strength=STRENGTH,
            temperature=TEMPERATURE,
            verbose=False,
            time=DEFAULT_TIME,
            simple=False,
            quiet=False,
            prompt_file=PROMPT_FILE
        )

        # Should return legacy result with accumulated cost
        expected_total_cost = AGENTIC_COST + TOTAL_COST
        assert result == (MODIFIED_PROMPT, expected_total_cost, MODEL_NAME)
        mock_run_agentic_update.assert_called_once()
        mock_update_prompt.assert_called_once()
        mock_write_handle.write.assert_called_once_with(MODIFIED_CODE)


@patch('pdd.git_update.open')
def test_git_update_simple_bypasses_agentic(mock_open_func, mock_repo, mock_update_prompt, mock_console_print, mock_get_available_agents, mock_run_agentic_update):
    """
    Test that simple=True bypasses agentic even when agents are available.
    """
    mock_get_available_agents.return_value = ["anthropic"]
    mock_write_handle = setup_mock_open_side_effects(mock_open_func, MODIFIED_CODE, ORIGINAL_CODE, expect_write=True)

    with patch('pdd.git_update.os.path.exists', return_value=True):
        mock_update_prompt.return_value = (MODIFIED_PROMPT, TOTAL_COST, MODEL_NAME)

        result = git_update(
            input_prompt=INPUT_PROMPT,
            modified_code_file=MODIFIED_CODE_FILE,
            strength=STRENGTH,
            temperature=TEMPERATURE,
            verbose=False,
            time=DEFAULT_TIME,
            simple=True,  # Force legacy path
            quiet=False,
            prompt_file=PROMPT_FILE
        )

        assert result == (MODIFIED_PROMPT, TOTAL_COST, MODEL_NAME)
        # Agentic should NOT be called when simple=True
        mock_run_agentic_update.assert_not_called()
        mock_update_prompt.assert_called_once()


@patch('pdd.git_update.open')
def test_git_update_no_prompt_file_bypasses_agentic(mock_open_func, mock_repo, mock_update_prompt, mock_console_print, mock_get_available_agents, mock_run_agentic_update):
    """
    Test that prompt_file=None bypasses agentic even when agents are available.
    """
    mock_get_available_agents.return_value = ["anthropic"]
    mock_write_handle = setup_mock_open_side_effects(mock_open_func, MODIFIED_CODE, ORIGINAL_CODE, expect_write=True)

    with patch('pdd.git_update.os.path.exists', return_value=True):
        mock_update_prompt.return_value = (MODIFIED_PROMPT, TOTAL_COST, MODEL_NAME)

        result = git_update(
            input_prompt=INPUT_PROMPT,
            modified_code_file=MODIFIED_CODE_FILE,
            strength=STRENGTH,
            temperature=TEMPERATURE,
            verbose=False,
            time=DEFAULT_TIME,
            simple=False,
            quiet=False,
            prompt_file=None  # No prompt file, skip agentic
        )

        assert result == (MODIFIED_PROMPT, TOTAL_COST, MODEL_NAME)
        # Agentic should NOT be called when prompt_file is None
        mock_run_agentic_update.assert_not_called()
        mock_update_prompt.assert_called_once()


@patch('pdd.git_update.open')
def test_git_update_no_agents_bypasses_agentic(mock_open_func, mock_repo, mock_update_prompt, mock_console_print, mock_get_available_agents, mock_run_agentic_update):
    """
    Test that empty agent list bypasses agentic path.
    """
    mock_get_available_agents.return_value = []  # No agents available
    mock_write_handle = setup_mock_open_side_effects(mock_open_func, MODIFIED_CODE, ORIGINAL_CODE, expect_write=True)

    with patch('pdd.git_update.os.path.exists', return_value=True):
        mock_update_prompt.return_value = (MODIFIED_PROMPT, TOTAL_COST, MODEL_NAME)

        result = git_update(
            input_prompt=INPUT_PROMPT,
            modified_code_file=MODIFIED_CODE_FILE,
            strength=STRENGTH,
            temperature=TEMPERATURE,
            verbose=False,
            time=DEFAULT_TIME,
            simple=False,
            quiet=False,
            prompt_file=PROMPT_FILE
        )

        assert result == (MODIFIED_PROMPT, TOTAL_COST, MODEL_NAME)
        # Agentic should NOT be called when no agents
        mock_run_agentic_update.assert_not_called()
        mock_update_prompt.assert_called_once()