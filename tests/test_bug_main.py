import os
import sys
import pytest
from unittest.mock import patch, MagicMock
from click.testing import CliRunner
from rich.console import Console
from pdd import DEFAULT_STRENGTH

# Import the module under test
sys.path.append(os.path.abspath(os.path.join(os.path.dirname(__file__), '..', 'pdd')))
from pdd.bug_main import bug_main

@pytest.fixture
def mock_ctx():
    """Fixture to create a mock context object."""
    ctx = MagicMock()
    ctx.obj = {'force': False, 'quiet': False, 'strength': DEFAULT_STRENGTH, 'temperature': 0}
    # Note: 'time' is not in ctx.obj, so bug_main will use DEFAULT_TIME for time_budget
    return ctx

@pytest.fixture
def mock_input_files(tmpdir):
    """Fixture to create temporary input files for testing."""
    prompt_file = tmpdir.join("prompt.prompt")
    code_file = tmpdir.join("code.py")
    program_file = tmpdir.join("program.py")
    current_output = tmpdir.join("current_output.txt")
    desired_output = tmpdir.join("desired_output.txt")

    prompt_file.write("Prompt content")
    code_file.write("Code content")
    program_file.write("Program content")
    current_output.write("Current output content")
    desired_output.write("Desired output content")

    return {
        "prompt_file": str(prompt_file),
        "code_file": str(code_file),
        "program_file": str(program_file),
        "current_output": str(current_output),
        "desired_output": str(desired_output)
    }

def test_bug_main_success(mock_ctx, mock_input_files, tmpdir):
    """Test case for successful execution of bug_main."""
    output_file = str(tmpdir.join("output_test.py"))
    
    with patch('pdd.bug_main.construct_paths') as mock_construct_paths, \
         patch('pdd.bug_main.bug_to_unit_test') as mock_bug_to_unit_test:
        
        # Mock construct_paths
        mock_construct_paths.return_value = (
            {},  # resolved_config
            {
                "prompt_file": "Prompt content",
                "code_file": "Code content",
                "program_file": "Program content",
                "current_output": "Current output content",
                "desired_output": "Desired output content"
            },
            {"output": output_file},
            None # detected_language, not used in this test path as language is provided
        )
        
        # Mock bug_to_unit_test
        mock_bug_to_unit_test.return_value = ("Generated unit test", 0.001, "gpt-4")
        
        # Call the function
        result = bug_main(
            mock_ctx,
            mock_input_files["prompt_file"],
            mock_input_files["code_file"],
            mock_input_files["program_file"],
            mock_input_files["current_output"],
            mock_input_files["desired_output"],
            output=output_file
            # language defaults to "Python" in bug_main
        )
        
        # Assertions
        assert result == ("Generated unit test", 0.001, "gpt-4")
        assert os.path.exists(output_file)
        with open(output_file, 'r') as f:
            assert f.read() == "Generated unit test"

def test_bug_main_no_output(mock_ctx, mock_input_files):
    """Test case for bug_main when no output file is specified."""
    with patch('pdd.bug_main.construct_paths') as mock_construct_paths, \
         patch('pdd.bug_main.bug_to_unit_test') as mock_bug_to_unit_test:
        
        # Mock construct_paths
        mock_construct_paths.return_value = (
            {},  # resolved_config
            {
                "prompt_file": "Prompt content",
                "code_file": "Code content",
                "program_file": "Program content",
                "current_output": "Current output content",
                "desired_output": "Desired output content"
            },
            {"output": None}, # No output file path
            None # detected_language
        )
        
        # Mock bug_to_unit_test
        mock_bug_to_unit_test.return_value = ("Generated unit test", 0.001, "gpt-4")
        
        # Call the function
        result = bug_main(
            mock_ctx,
            mock_input_files["prompt_file"],
            mock_input_files["code_file"],
            mock_input_files["program_file"],
            mock_input_files["current_output"],
            mock_input_files["desired_output"]
            # output is None by default
            # language defaults to "Python"
        )
        
        # Assertions
        assert result == ("Generated unit test", 0.001, "gpt-4")

def test_bug_main_error_handling(mock_ctx, mock_input_files):
    """Test case for error handling in bug_main."""
    with patch('pdd.bug_main.construct_paths') as mock_construct_paths:
        # Mock construct_paths to raise an exception
        mock_construct_paths.side_effect = Exception("Test error")
        
        # Call the function and expect it to exit
        with pytest.raises(SystemExit):
            bug_main(
                mock_ctx,
                mock_input_files["prompt_file"],
                mock_input_files["code_file"],
                mock_input_files["program_file"],
                mock_input_files["current_output"],
                mock_input_files["desired_output"]
            )

def test_bug_main_quiet_mode(mock_ctx, mock_input_files):
    """Test case for bug_main in quiet mode."""
    mock_ctx.obj['quiet'] = True
    
    with patch('pdd.bug_main.construct_paths') as mock_construct_paths, \
         patch('pdd.bug_main.bug_to_unit_test') as mock_bug_to_unit_test:
        
        # Mock construct_paths
        mock_construct_paths.return_value = (
            {},  # resolved_config
            {
                "prompt_file": "Prompt content",
                "code_file": "Code content",
                "program_file": "Program content",
                "current_output": "Current output content",
                "desired_output": "Desired output content"
            },
            {"output": None},
            None
        )
        
        # Mock bug_to_unit_test
        mock_bug_to_unit_test.return_value = ("Generated unit test", 0.001, "gpt-4")
        
        # Call the function
        result = bug_main(
            mock_ctx,
            mock_input_files["prompt_file"],
            mock_input_files["code_file"],
            mock_input_files["program_file"],
            mock_input_files["current_output"],
            mock_input_files["desired_output"]
        )
        
        # Assertions
        assert result == ("Generated unit test", 0.001, "gpt-4")

def test_bug_main_different_language(mock_ctx, mock_input_files):
    """Test case for bug_main with a different programming language."""
    with patch('pdd.bug_main.construct_paths') as mock_construct_paths, \
         patch('pdd.bug_main.bug_to_unit_test') as mock_bug_to_unit_test:
        
        # Mock construct_paths
        mock_construct_paths.return_value = (
            {},  # resolved_config
            {
                "prompt_file": "Prompt content",
                "code_file": "Code content",
                "program_file": "Program content",
                "current_output": "Current output content",
                "desired_output": "Desired output content"
            },
            {"output": None},
            "JavaScript" # detected_language from construct_paths if it were to detect
        )
        
        # Mock bug_to_unit_test
        mock_bug_to_unit_test.return_value = ("Generated unit test", 0.001, "gpt-4")
        
        # Call the function
        result = bug_main(
            mock_ctx,
            mock_input_files["prompt_file"],
            mock_input_files["code_file"],
            mock_input_files["program_file"],
            mock_input_files["current_output"],
            mock_input_files["desired_output"],
            language="JavaScript" # Explicitly passing "JavaScript"
        )
        
        # Assertions
        assert result == ("Generated unit test", 0.001, "gpt-4")
        # Verify bug_to_unit_test was called with "JavaScript"
        mock_bug_to_unit_test.assert_called_once()
        args, kwargs = mock_bug_to_unit_test.call_args
        assert args[8] == "JavaScript" # language is the 9th argument (index 8)

def test_bug_main_language_from_construct_paths(mock_ctx, mock_input_files):
    """Test case for bug_main using the language detected by construct_paths when language is None."""
    with patch('pdd.bug_main.construct_paths') as mock_construct_paths, \
         patch('pdd.bug_main.bug_to_unit_test') as mock_bug_to_unit_test:
        
        # Mock construct_paths to return "python" as detected language
        mock_construct_paths.return_value = (
            {},  # resolved_config
            {
                "prompt_file": "Prompt content",
                "code_file": "Code content",
                "program_file": "Program content",
                "current_output": "Current output content",
                "desired_output": "Desired output content"
            },
            {"output": None},
            "python"  # Detected language
        )
        
        # Mock bug_to_unit_test
        mock_bug_to_unit_test.return_value = ("Generated unit test", 0.001, "gpt-4")
        
        # Call the function with language=None
        result = bug_main(
            mock_ctx,
            mock_input_files["prompt_file"],
            mock_input_files["code_file"],
            mock_input_files["program_file"],
            mock_input_files["current_output"],
            mock_input_files["desired_output"],
            language=None  # Explicitly passing None to test this logic
        )
        
        # Verify bug_to_unit_test was called with the language from construct_paths
        mock_bug_to_unit_test.assert_called_once()
        args, kwargs = mock_bug_to_unit_test.call_args
        # Corrected assertion: language is the 9th argument (index 8)
        assert args[8] == "python", "The language parameter should be 'python' from construct_paths, not None"
        
        # Assertions on the result
        assert result == ("Generated unit test", 0.001, "gpt-4")

def test_bug_main_output_file_exists(mock_ctx, mock_input_files, tmpdir):
    """Test case for bug_main when the output file already exists."""
    output_file = str(tmpdir.join("output_test.py"))
    
    # Create an existing file
    with open(output_file, 'w') as f:
        f.write("Existing content")
    
    with patch('pdd.bug_main.construct_paths') as mock_construct_paths, \
         patch('pdd.bug_main.bug_to_unit_test') as mock_bug_to_unit_test:
        
        # Mock construct_paths
        mock_construct_paths.return_value = (
            {},  # resolved_config
            {
                "prompt_file": "Prompt content",
                "code_file": "Code content",
                "program_file": "Program content",
                "current_output": "Current output content",
                "desired_output": "Desired output content"
            },
            {"output": output_file},
            None
        )
        
        # Mock bug_to_unit_test
        mock_bug_to_unit_test.return_value = ("Generated unit test", 0.001, "gpt-4")
        
        # Call the function
        bug_main(
            mock_ctx,
            mock_input_files["prompt_file"],
            mock_input_files["code_file"],
            mock_input_files["program_file"],
            mock_input_files["current_output"],
            mock_input_files["desired_output"],
            output=output_file
        )
        
        # Assertions
        new_output_file = str(tmpdir.join("output_test_1.py"))
        assert os.path.exists(new_output_file)
        with open(new_output_file, 'r') as f:
            assert f.read() == "Generated unit test"
        
        # Check that the original file is untouched
        with open(output_file, 'r') as f:
            assert f.read() == "Existing content"
