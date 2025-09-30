import pytest
import click
from click.testing import CliRunner
from unittest.mock import patch, mock_open
from pathlib import Path
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


def test_context_generator_main_output_directory_path_uses_resolved_file(mock_ctx, tmp_path):
    """
    Intended behavior: when --output is a directory path, the main should write
    to the resolved file from construct_paths, not treat the directory as a file.
    """
    out_dir = tmp_path / "out"
    out_dir.mkdir()

    with patch('pdd.context_generator_main.construct_paths') as mock_construct_paths, \
         patch('pdd.context_generator_main.context_generator') as mock_context_generator, \
         patch('builtins.open', mock_open()) as m_open:

        resolved_file = out_dir / "example_code.py"
        mock_construct_paths.return_value = (
            {},
            {"prompt_file": MOCK_PROMPT_CONTENT, "code_file": MOCK_CODE_CONTENT},
            {"output": str(resolved_file)},
            None,
        )
        mock_context_generator.return_value = (MOCK_EXAMPLE_CODE, MOCK_TOTAL_COST, MOCK_MODEL_NAME)

        result = context_generator_main(mock_ctx, "prompts/test_prompt.prompt", "src/test_code.py", str(out_dir))

        # Should succeed and write to the resolved file path
        assert result == (MOCK_EXAMPLE_CODE, MOCK_TOTAL_COST, MOCK_MODEL_NAME)
        m_open.assert_called_once_with(str(resolved_file), 'w')
        handle = m_open()
        handle.write.assert_called_once_with(MOCK_EXAMPLE_CODE)


def test_context_generator_main_with_file_paths():
    """Test that context_generator_main extracts and passes file path information."""
    with tempfile.TemporaryDirectory() as tmp_dir:
        # Create test files
        prompt_file = Path(tmp_dir) / "test.prompt"
        code_file = Path(tmp_dir) / "hello.py"
        output_file = Path(tmp_dir) / "hello_example.py"
        
        prompt_file.write_text("Write a hello function")
        code_file.write_text("def hello():\n    print('hello')")
        
        with patch('pdd.context_generator_main.context_generator') as mock_context_generator:
            mock_context_generator.return_value = (MOCK_EXAMPLE_CODE, MOCK_TOTAL_COST, MOCK_MODEL_NAME)
            
            result = context_generator_main(
                mock_ctx, 
                str(prompt_file), 
                str(code_file), 
                str(output_file)
            )
            
            # Verify context_generator was called with file path parameters
            mock_context_generator.assert_called_once()
            call_args = mock_context_generator.call_args[1]
            
            # Check that file path information was extracted and passed
            assert 'source_file_path' in call_args, "source_file_path should be passed"
            assert 'example_file_path' in call_args, "example_file_path should be passed"
            assert 'module_name' in call_args, "module_name should be passed"
            
            assert call_args['source_file_path'] == str(code_file)
            assert call_args['example_file_path'] == str(output_file)
            assert call_args['module_name'] == "hello"
