import pytest
from unittest.mock import mock_open, patch, MagicMock
from typing import Tuple, Optional

# Absolute import based on the provided directory structure
from pdd.git_update import git_update

# Sample data for tests
INPUT_PROMPT = "Please add two numbers and return the sum."
MODIFIED_CODE_FILE = "/path/to/modified_code.py"
STRENGTH = 0.9
TEMPERATURE = 0.5
ORIGINAL_CODE = "def add(a, b): return a + b"
MODIFIED_CODE = "def add(a, b): return a + b + 1"
MODIFIED_PROMPT = "Please add two numbers and return the sum plus one."
TOTAL_COST = 0.123456
MODEL_NAME = "gpt-4"

@pytest.fixture
def mock_repo():
    with patch('pdd.git_update.git.Repo') as mock_repo_class:
        mock_repo_instance = MagicMock()
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

def test_git_update_success(mock_repo, mock_update_prompt, mock_console_print):
    """
    Test the successful execution of git_update with valid inputs.
    """
    # Mock the existence of the file
    with patch('pdd.git_update.os.path.exists', return_value=True):
        # Mock file reading and writing
        m = mock_open(read_data=ORIGINAL_CODE)
        with patch('pdd.git_update.open', m):
            # Mock update_prompt return value
            mock_update_prompt.return_value = (MODIFIED_PROMPT, TOTAL_COST, MODEL_NAME)
            
            # Call the function
            result = git_update(
                input_prompt=INPUT_PROMPT,
                modified_code_file=MODIFIED_CODE_FILE,
                strength=STRENGTH,
                temperature=TEMPERATURE
            )
            
            # Assertions
            assert result == (MODIFIED_PROMPT, TOTAL_COST, MODEL_NAME)
            mock_repo.git.checkout.assert_called_once()
            mock_update_prompt.assert_called_once_with(
                input_prompt=INPUT_PROMPT,
                input_code=ORIGINAL_CODE,
                modified_code=ORIGINAL_CODE,
                strength=STRENGTH,
                temperature=TEMPERATURE
            )
            # Ensure the file was written with modified code
            m.assert_called_with(MODIFIED_CODE_FILE, 'w')
            handle = m()
            handle.write.assert_called_once_with(ORIGINAL_CODE)

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
    # Simulate git.Repo raising an exception
    mock_repo.git.checkout.side_effect = git.exc.InvalidGitRepositoryError
    with patch('pdd.git_update.os.path.exists', return_value=True):
        with patch('pdd.git_update.open', mock_open(read_data=ORIGINAL_CODE)):
            result = git_update(
                input_prompt=INPUT_PROMPT,
                modified_code_file=MODIFIED_CODE_FILE,
                strength=STRENGTH,
                temperature=TEMPERATURE
            )
            assert result == (None, 0.0, "")
            mock_console_print.assert_called()
            mock_update_prompt.assert_not_called()

def test_git_update_update_prompt_exception(mock_repo, mock_update_prompt, mock_console_print):
    """
    Test git_update when update_prompt raises an exception.
    """
    with patch('pdd.git_update.os.path.exists', return_value=True):
        m = mock_open(read_data=ORIGINAL_CODE)
        with patch('pdd.git_update.open', m):
            # Simulate update_prompt raising an exception
            mock_update_prompt.side_effect = Exception("Model error")
            result = git_update(
                input_prompt=INPUT_PROMPT,
                modified_code_file=MODIFIED_CODE_FILE,
                strength=STRENGTH,
                temperature=TEMPERATURE
            )
            assert result == (None, 0.0, "")
            mock_console_print.assert_called()
            mock_update_prompt.assert_called_once()

def test_git_update_file_write_failure(mock_repo, mock_update_prompt, mock_console_print):
    """
    Test git_update when writing back the modified code file fails.
    """
    with patch('pdd.git_update.os.path.exists', return_value=True):
        m = mock_open(read_data=ORIGINAL_CODE)
        with patch('pdd.git_update.open', m):
            # Simulate write failure
            handle = m()
            handle.write.side_effect = IOError("Write failed")
            mock_update_prompt.return_value = (MODIFIED_PROMPT, TOTAL_COST, MODEL_NAME)
            
            result = git_update(
                input_prompt=INPUT_PROMPT,
                modified_code_file=MODIFIED_CODE_FILE,
                strength=STRENGTH,
                temperature=TEMPERATURE
            )
            assert result == (None, 0.0, "")
            mock_console_print.assert_called()
            mock_update_prompt.assert_called_once()

def test_git_update_invalid_strength_temperature(mock_repo, mock_update_prompt, mock_console_print):
    """
    Test git_update with invalid strength and temperature values.
    """
    # Assuming the function does not explicitly validate strength and temperature,
    # it should still proceed. If validation is required, adjust the test accordingly.
    with patch('pdd.git_update.os.path.exists', return_value=True):
        m = mock_open(read_data=ORIGINAL_CODE)
        with patch('pdd.git_update.open', m):
            mock_update_prompt.return_value = (MODIFIED_PROMPT, TOTAL_COST, MODEL_NAME)
            
            result = git_update(
                input_prompt=INPUT_PROMPT,
                modified_code_file=MODIFIED_CODE_FILE,
                strength=-1.0,        # Invalid strength
                temperature=2.0        # Invalid temperature
            )
            # Assuming no validation, it should still return modified prompt
            assert result == (MODIFIED_PROMPT, TOTAL_COST, MODEL_NAME)
            mock_console_print.assert_called()
            mock_update_prompt.assert_called_once()

def test_git_update_empty_original_code(mock_repo, mock_update_prompt, mock_console_print):
    """
    Test git_update when the original code file is empty.
    """
    with patch('pdd.git_update.os.path.exists', return_value=True):
        m = mock_open(read_data="")
        with patch('pdd.git_update.open', m):
            mock_update_prompt.return_value = (MODIFIED_PROMPT, TOTAL_COST, MODEL_NAME)
            result = git_update(
                input_prompt=INPUT_PROMPT,
                modified_code_file=MODIFIED_CODE_FILE,
                strength=STRENGTH,
                temperature=TEMPERATURE
            )
            assert result == (MODIFIED_PROMPT, TOTAL_COST, MODEL_NAME)
            mock_update_prompt.assert_called_once_with(
                input_prompt=INPUT_PROMPT,
                input_code="",
                modified_code="",
                strength=STRENGTH,
                temperature=TEMPERATURE
            )

def test_git_update_non_tuple_return(mock_repo, mock_update_prompt, mock_console_print):
    """
    Test git_update when update_prompt returns a non-tuple value.
    """
    with patch('pdd.git_update.os.path.exists', return_value=True):
        m = mock_open(read_data=ORIGINAL_CODE)
        with patch('pdd.git_update.open', m):
            # Simulate update_prompt returning incorrect type
            mock_update_prompt.return_value = "incorrect return type"
            
            result = git_update(
                input_prompt=INPUT_PROMPT,
                modified_code_file=MODIFIED_CODE_FILE,
                strength=STRENGTH,
                temperature=TEMPERATURE
            )
            # Function is expected to handle this gracefully, returning None, 0.0, ""
            assert result == (None, 0.0, "")
            mock_console_print.assert_called()
            mock_update_prompt.assert_called_once()
