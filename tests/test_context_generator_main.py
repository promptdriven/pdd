import pytest
import click
from click.testing import CliRunner
from unittest.mock import patch, mock_open
from pdd.context_generator_main import context_generator_main

# Mock data for testing
MOCK_PROMPT_CONTENT = "Write a function 'add' that adds two numbers."
MOCK_CODE_CONTENT = "def add(a, b):\n    return a + b"
MOCK_EXAMPLE_CODE = "def add(a, b):\n    return a + b\n\n# Example usage:\nprint(add(2, 3))  # Output: 5"
MOCK_TOTAL_COST = 0.000123
MOCK_MODEL_NAME = "gpt-3.5-turbo"

@pytest.fixture
def mock_ctx():
    """
    Creates a mock Click context for testing purposes.
    """
    ctx = click.Context(click.Command('test'))
    ctx.params = {
        'force': False,
        'quiet': False,
        'verbose': False
    }
    ctx.obj = {
        'strength': 0.5,
        'temperature': 0
    }
    return ctx

def test_context_generator_main_success(mock_ctx):
    """
    Test case for successful execution of context_generator_main.
    """
    with patch('pdd.context_generator_main.construct_paths') as mock_construct_paths, \
         patch('pdd.context_generator_main.context_generator') as mock_context_generator, \
         patch('builtins.open', mock_open()) as mock_file:
        
        # Mock construct_paths
        mock_construct_paths.return_value = (
            {},  # resolved_config
            {"prompt_file": MOCK_PROMPT_CONTENT, "code_file": MOCK_CODE_CONTENT},
            {"output": "output/example_code.py"},
            None
        )
        
        # Mock context_generator
        mock_context_generator.return_value = (MOCK_EXAMPLE_CODE, MOCK_TOTAL_COST, MOCK_MODEL_NAME)
        
        # Call the function
        result = context_generator_main(mock_ctx, "prompts/test_prompt.prompt", "src/test_code.py", "output/example_code.py")
        
        # Assertions
        assert result == (MOCK_EXAMPLE_CODE, MOCK_TOTAL_COST, MOCK_MODEL_NAME)
        mock_file().write.assert_called_once_with(MOCK_EXAMPLE_CODE)

def test_context_generator_main_no_output(mock_ctx):
    """
    Test case for context_generator_main when no output file is specified.
    """
    with patch('pdd.context_generator_main.construct_paths') as mock_construct_paths, \
         patch('pdd.context_generator_main.context_generator') as mock_context_generator:
        
        # Mock construct_paths
        mock_construct_paths.return_value = (
            {},  # resolved_config
            {"prompt_file": MOCK_PROMPT_CONTENT, "code_file": MOCK_CODE_CONTENT},
            {"output": None},
            None
        )
        
        # Mock context_generator
        mock_context_generator.return_value = (MOCK_EXAMPLE_CODE, MOCK_TOTAL_COST, MOCK_MODEL_NAME)
        
        # Call the function
        result = context_generator_main(mock_ctx, "prompts/test_prompt.prompt", "src/test_code.py", None)
        
        # Assertions
        assert result == (MOCK_EXAMPLE_CODE, MOCK_TOTAL_COST, MOCK_MODEL_NAME)

def test_context_generator_main_error(mock_ctx):
    """
    Test case for context_generator_main when an error occurs.
    """
    with patch('pdd.context_generator_main.construct_paths') as mock_construct_paths, \
         patch('pdd.context_generator_main.context_generator') as mock_context_generator:
        
        # Mock construct_paths to raise an exception
        mock_construct_paths.side_effect = Exception("File not found")
        
        # Call the function and expect sys.exit(1)
        with pytest.raises(SystemExit) as pytest_wrapped_e:
            context_generator_main(mock_ctx, "prompts/test_prompt.prompt", "src/test_code.py", "output/example_code.py")
        
        assert pytest_wrapped_e.type == SystemExit
        assert pytest_wrapped_e.value.code == 1

def test_context_generator_main_quiet_mode(mock_ctx):
    """
    Test case for context_generator_main in quiet mode.
    """
    mock_ctx.params['quiet'] = True
    with patch('pdd.context_generator_main.construct_paths') as mock_construct_paths, \
         patch('pdd.context_generator_main.context_generator') as mock_context_generator, \
         patch('builtins.open', mock_open()) as mock_file:
        
        # Mock construct_paths
        mock_construct_paths.return_value = (
            {},  # resolved_config
            {"prompt_file": MOCK_PROMPT_CONTENT, "code_file": MOCK_CODE_CONTENT},
            {"output": "output/example_code.py"},
            None
        )
        
        # Mock context_generator
        mock_context_generator.return_value = (MOCK_EXAMPLE_CODE, MOCK_TOTAL_COST, MOCK_MODEL_NAME)
        
        # Call the function
        result = context_generator_main(mock_ctx, "prompts/test_prompt.prompt", "src/test_code.py", "output/example_code.py")
        
        # Assertions
        assert result == (MOCK_EXAMPLE_CODE, MOCK_TOTAL_COST, MOCK_MODEL_NAME)
        mock_file().write.assert_called_once_with(MOCK_EXAMPLE_CODE)

def test_context_generator_main_verbose_mode(mock_ctx):
    """
    Test case for context_generator_main in verbose mode.
    """
    mock_ctx.params['verbose'] = True
    with patch('pdd.context_generator_main.construct_paths') as mock_construct_paths, \
         patch('pdd.context_generator_main.context_generator') as mock_context_generator, \
         patch('builtins.open', mock_open()) as mock_file:
        
        # Mock construct_paths
        mock_construct_paths.return_value = (
            {},  # resolved_config
            {"prompt_file": MOCK_PROMPT_CONTENT, "code_file": MOCK_CODE_CONTENT},
            {"output": "output/example_code.py"},
            None
        )
        
        # Mock context_generator
        mock_context_generator.return_value = (MOCK_EXAMPLE_CODE, MOCK_TOTAL_COST, MOCK_MODEL_NAME)
        
        # Call the function
        result = context_generator_main(mock_ctx, "prompts/test_prompt.prompt", "src/test_code.py", "output/example_code.py")
        
        # Assertions
        assert result == (MOCK_EXAMPLE_CODE, MOCK_TOTAL_COST, MOCK_MODEL_NAME)
        mock_file().write.assert_called_once_with(MOCK_EXAMPLE_CODE)