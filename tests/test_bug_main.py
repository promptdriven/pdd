import pytest
import os
from unittest.mock import patch, MagicMock
from click.testing import CliRunner
from rich.console import Console
from pdd.bug_main import bug_main

# Mock data for testing
MOCK_PROMPT_CONTENT = "Mock prompt content"
MOCK_CODE_CONTENT = "Mock code content"
MOCK_PROGRAM_CONTENT = "Mock program content"
MOCK_CURRENT_OUTPUT = "Mock current output"
MOCK_DESIRED_OUTPUT = "Mock desired output"
MOCK_UNIT_TEST = "Mock unit test"
MOCK_TOTAL_COST = 0.001
MOCK_MODEL_NAME = "gpt-4"

@pytest.fixture
def mock_ctx():
    """Fixture to mock the context object."""
    ctx = MagicMock()
    ctx.params = {'force': False, 'quiet': False}
    ctx.obj = MagicMock()
    ctx.obj.get = MagicMock(side_effect=lambda key, default: default)
    return ctx

@pytest.fixture
def mock_construct_paths():
    """Fixture to mock the construct_paths function."""
    with patch('pdd.bug_main.construct_paths') as mock_construct:
        mock_construct.return_value = (
            {
                "prompt_file": MOCK_PROMPT_CONTENT,
                "code_file": MOCK_CODE_CONTENT,
                "program_file": MOCK_PROGRAM_CONTENT
            },
            {"output": "output/mock_unit_test.py"},
            "Python"
        )
        yield mock_construct

@pytest.fixture
def mock_bug_to_unit_test():
    """Fixture to mock the bug_to_unit_test function."""
    with patch('pdd.bug_main.bug_to_unit_test') as mock_bug:
        mock_bug.return_value = (MOCK_UNIT_TEST, MOCK_TOTAL_COST, MOCK_MODEL_NAME)
        yield mock_bug

def test_bug_main_success(mock_ctx, mock_construct_paths, mock_bug_to_unit_test, tmpdir):
    """Test case for successful execution of bug_main."""
    # Arrange
    output_dir = tmpdir.mkdir("output")
    output_path = str(output_dir.join("mock_unit_test.py"))
    mock_construct_paths.return_value = (
        {
            "prompt_file": MOCK_PROMPT_CONTENT,
            "code_file": MOCK_CODE_CONTENT,
            "program_file": MOCK_PROGRAM_CONTENT
        },
        {"output": output_path},
        "Python"
    )
    
    # Act
    result = bug_main(
        mock_ctx,
        "mock_prompt.prompt",
        "mock_code.py",
        "mock_program.py",
        MOCK_CURRENT_OUTPUT,
        MOCK_DESIRED_OUTPUT,
        output_path
    )
    
    # Assert
    assert result == (MOCK_UNIT_TEST, MOCK_TOTAL_COST, MOCK_MODEL_NAME)
    assert os.path.exists(output_path)
    with open(output_path, 'r') as f:
        assert f.read() == MOCK_UNIT_TEST

def test_bug_main_no_output(mock_ctx, mock_construct_paths, mock_bug_to_unit_test):
    """Test case for bug_main when no output file is specified."""
    # Arrange
    mock_construct_paths.return_value = (
        {
            "prompt_file": MOCK_PROMPT_CONTENT,
            "code_file": MOCK_CODE_CONTENT,
            "program_file": MOCK_PROGRAM_CONTENT
        },
        {"output": None},
        "Python"
    )
    
    # Act
    result = bug_main(
        mock_ctx,
        "mock_prompt.prompt",
        "mock_code.py",
        "mock_program.py",
        MOCK_CURRENT_OUTPUT,
        MOCK_DESIRED_OUTPUT
    )
    
    # Assert
    assert result == (MOCK_UNIT_TEST, MOCK_TOTAL_COST, MOCK_MODEL_NAME)

def test_bug_main_error(mock_ctx, mock_construct_paths, mock_bug_to_unit_test):
    """Test case for bug_main when an error occurs."""
    # Arrange
    mock_bug_to_unit_test.side_effect = Exception("Test error")
    
    # Act
    with pytest.raises(SystemExit):
        bug_main(
            mock_ctx,
            "mock_prompt.prompt",
            "mock_code.py",
            "mock_program.py",
            MOCK_CURRENT_OUTPUT,
            MOCK_DESIRED_OUTPUT
        )
    
    # Assert
    mock_ctx.obj.get.assert_called()

def test_bug_main_quiet_mode(mock_ctx, mock_construct_paths, mock_bug_to_unit_test):
    """Test case for bug_main in quiet mode."""
    # Arrange
    mock_ctx.obj['quiet'] = True
    
    # Act
    result = bug_main(
        mock_ctx,
        "mock_prompt.prompt",
        "mock_code.py",
        "mock_program.py",
        MOCK_CURRENT_OUTPUT,
        MOCK_DESIRED_OUTPUT
    )
    
    # Assert
    assert result == (MOCK_UNIT_TEST, MOCK_TOTAL_COST, MOCK_MODEL_NAME)

def test_bug_main_force_mode(mock_ctx, mock_construct_paths, mock_bug_to_unit_test):
    """Test case for bug_main in force mode."""
    # Arrange
    mock_ctx.obj['force'] = True
    
    # Act
    result = bug_main(
        mock_ctx,
        "mock_prompt.prompt",
        "mock_code.py",
        "mock_program.py",
        MOCK_CURRENT_OUTPUT,
        MOCK_DESIRED_OUTPUT
    )
    
    # Assert
    assert result == (MOCK_UNIT_TEST, MOCK_TOTAL_COST, MOCK_MODEL_NAME)
    mock_construct_paths.assert_called_with(
        input_file_paths={
            "prompt_file": "mock_prompt.prompt",
            "code_file": "mock_code.py",
            "program_file": "mock_program.py"
        },
        force=True,
        quiet=False,
        command="bug",
        command_options={
            "output": None,
            "language": "Python"
        }
    )