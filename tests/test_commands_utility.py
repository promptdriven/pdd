# tests/test_commands_utility.py
"""Tests for commands/utility."""
import os
import sys
import subprocess
from pathlib import Path
from unittest.mock import patch, ANY, MagicMock

import pytest
from click.testing import CliRunner
import click

from pdd import cli, __version__, DEFAULT_STRENGTH, DEFAULT_TIME

RUN_ALL_TESTS_ENABLED = os.getenv("PDD_RUN_ALL_TESTS") == "1"


@patch('pdd.core.cli.auto_update') # Patch auto_update
@patch('pdd.cli.install_completion')  # Patch the actual function, not cli_module
def test_cli_install_completion_cmd(mock_install_func, mock_auto_update, runner):
    """Test the install_completion command."""
    result = runner.invoke(cli.cli, ["install_completion"])

    if result.exit_code != 0:
        print(f"Unexpected exit code: {result.exit_code}")
        print(f"Output:\n{result.output}")
        if result.exception:
            print(f"Exception:\n{result.exception}")
            raise result.exception # Re-raise the captured exception

    assert result.exit_code == 0
    assert result.exception is None # Should complete gracefully
    mock_install_func.assert_called_once_with(quiet=False)
    mock_auto_update.assert_called_once_with()

@patch('pdd.core.cli.auto_update') # Patch auto_update
@patch('pdd.cli.install_completion')  # Patch the actual function, not cli_module
def test_cli_install_completion_cmd_quiet(mock_install_func, mock_auto_update, runner):
    """Test the install_completion command with --quiet."""
    result = runner.invoke(cli.cli, ["--quiet", "install_completion"])

    if result.exit_code != 0:
        print(f"Unexpected exit code: {result.exit_code}")
        print(f"Output:\n{result.output}")
        if result.exception:
            print(f"Exception:\n{result.exception}")
            raise result.exception # Re-raise the captured exception

    assert result.exit_code == 0
    assert result.exception is None # Should complete gracefully
    mock_install_func.assert_called_once_with(quiet=True)
    mock_auto_update.assert_called_once_with()

@patch('pdd.core.cli.auto_update')
@patch('pdd.fix_verification_main.construct_paths')
@patch('pdd.cli.fix_verification_main')
def test_cli_verify_command_calls_fix_verification_main(mock_fix_verification, mock_construct_in_main,
                                                       mock_auto_update, runner, create_dummy_files, tmp_path):
    """Test that fix_verification_main can be called with the expected arguments."""
    from pdd.cli import fix_verification_main as imported_func
    
    # Verify that the function is importable and the mocking works
    assert imported_func is mock_fix_verification, "The imported fix_verification_main should be the same as the mocked function"
    
    files = create_dummy_files("test.prompt", "test.py", "program.py")
    mock_prompt_file = str(files["test.prompt"])
    mock_code_file = str(files["test.py"])
    mock_program_file = str(files["program.py"])
    mock_output_results = str(tmp_path / "results.log")
    mock_output_code = str(tmp_path / "verified_code.py")
    mock_output_program = str(tmp_path / "verified_program.py")

    # Setup mock return values
    mock_fix_verification.return_value = (True, "prog_content", "code_content", 1, 0.01, "test_model")
    
    # Create a minimal context dictionary (not a Click context)
    ctx_obj = {
        'force': False,
        'strength': 0.8,
        'temperature': 0.0,
        'verbose': False,
        'quiet': False,
        'output_cost': None,
        'review_examples': False,
        'local': False,
        'time': DEFAULT_TIME, # Added time to context
    }
    
    # Create a minimal ctx-like object with obj attribute
    class MinimalContext:
        def __init__(self, obj):
            self.obj = obj
            
    ctx = MinimalContext(ctx_obj)
    
    # Call fix_verification_main directly with the parameters that the verify command would pass
    # This tests that the function is correctly importable and has the expected signature
    result = imported_func(
        ctx=ctx,
        prompt_file=mock_prompt_file,
        code_file=mock_code_file,
        program_file=mock_program_file,
        output_results=mock_output_results,
        output_code=mock_output_code,
        output_program=mock_output_program,
        loop=True,
        verification_program=mock_program_file,
        max_attempts=5,
        budget=10.0,
    )
    
    # Check that the function was called with the correct arguments
    mock_fix_verification.assert_called_once()
    kwargs = mock_fix_verification.call_args.kwargs
    
    assert kwargs.get('prompt_file') == mock_prompt_file
    assert kwargs.get('code_file') == mock_code_file
    assert kwargs.get('program_file') == mock_program_file
    assert kwargs.get('output_results') == mock_output_results
    assert kwargs.get('output_code') == mock_output_code
    assert kwargs.get('output_program') == mock_output_program
    assert kwargs.get('loop') is True 
    assert kwargs.get('verification_program') == mock_program_file
    assert kwargs.get('max_attempts') == 5
    assert kwargs.get('budget') == 10.0
    
    # Verify the return value
    assert result == (True, "prog_content", "code_content", 1, 0.01, "test_model")

@patch('pdd.core.cli.auto_update')
@patch('pdd.fix_verification_main.construct_paths')
@patch('pdd.commands.utility.fix_verification_main')
def test_cli_verify_command_default_output_program(mock_fix_verification, mock_construct_in_main, mock_auto_update, runner, create_dummy_files, tmp_path):
    """Test `pdd verify` calls fix_verification_main with output_program=None by default."""
    files = create_dummy_files("test.prompt", "test.py", "program.py")
    mock_prompt_file = str(files["test.prompt"])
    mock_code_file = str(files["test.py"])
    mock_program_file = str(files["program.py"])

    mock_fix_verification.return_value = (True, "prog_content", "code_content", 1, 0.01, "test_model")
    mock_construct_in_main.return_value = (
        {"prompt_file": "p_content", "code_file": "c_content", "program_file": "prog_content"},
        # Simulate construct_paths returning None for output_program if not specified
        {"output_results": "some/path.log", "output_code": "some/code.py", "output_program": None},
        "python"
    )

    result = runner.invoke(cli.cli, [
        "verify",
        mock_prompt_file,
        mock_code_file,
        mock_program_file,
        # No --output-program here
    ])

    if result.exit_code != 0:
        print(f"CLI Error: {result.output}")
        if result.exception:
            raise result.exception
    
    assert "Usage: cli [OPTIONS] COMMAND" not in result.output, "Main help was printed, indicating dispatch failure."
    assert result.exit_code == 0


    mock_fix_verification.assert_called_once()
    kwargs = mock_fix_verification.call_args.kwargs
    assert kwargs.get('output_program') is None # Key assertion

@patch.dict(os.environ, {"PDD_VERIFY_PROGRAM_OUTPUT_PATH": "env_prog_output.py"}, clear=True) # Added clear=True
@patch('pdd.core.cli.auto_update')
@patch('pdd.fix_verification_main.construct_paths') 
@patch('pdd.commands.utility.fix_verification_main')
def test_cli_verify_command_env_var_output_program(mock_fix_verification, mock_construct_in_main, mock_auto_update, runner, create_dummy_files, tmp_path):
    """Test `pdd verify` uses PDD_VERIFY_PROGRAM_OUTPUT_PATH env var."""
    files = create_dummy_files("test.prompt", "test.py", "program.py")
    mock_prompt_file = str(files["test.prompt"])
    mock_code_file = str(files["test.py"])
    mock_program_file = str(files["program.py"])
    
    expected_env_output_program_name = "env_prog_output.py"


    mock_fix_verification.return_value = (True, "prog_content", "code_content", 1, 0.01, "test_model")
    # Mock construct_paths to simulate it would return a path influenced by the env var
    # if fix_verification_main was real and called it.
    # For this test, what fix_verification_main *receives* from the CLI wrapper is key.
    mock_construct_in_main.return_value = (
        {"prompt_file": "p_content", "code_file": "c_content", "program_file": "prog_content"},
        {"output_results": "r.log", "output_code": "c.py", 
         "output_program": str(Path(expected_env_output_program_name).resolve())}, # This is what construct_paths would return
        "python"
    )

    result = runner.invoke(cli.cli, [
        "verify",
        mock_prompt_file,
        mock_code_file,
        mock_program_file,
        # No --output-program, CLI wrapper passes None to fix_verification_main.
        # The env var is used by construct_paths *inside* fix_verification_main.
    ])

    if result.exit_code != 0:
        print(f"CLI Error: {result.output}")
        if result.exception:
            raise result.exception
    
    assert "Usage: cli [OPTIONS] COMMAND" not in result.output, "Main help was printed, indicating dispatch failure."
    assert result.exit_code == 0

    mock_fix_verification.assert_called_once()
    kwargs = mock_fix_verification.call_args.kwargs
    
    # The CLI wrapper for 'verify' passes the --output-program option's value.
    # If the option is not provided, it passes None to fix_verification_main.
    # The environment variable PDD_VERIFY_PROGRAM_OUTPUT_PATH is handled
    # by construct_paths, which is called *inside* fix_verification_main.
    # Therefore, the mocked fix_verification_main should receive None for output_program.
    assert kwargs.get('output_program') is None

@pytest.mark.real
def test_real_verify_command(create_dummy_files, tmp_path):
    """Test the 'verify' command with real files by calling the function directly."""
    if not (os.getenv("PDD_RUN_REAL_LLM_TESTS") or RUN_ALL_TESTS_ENABLED):
        pytest.skip(
            "Real LLM integration tests require network/API access; set "
            "PDD_RUN_REAL_LLM_TESTS=1 or use --run-all / PDD_RUN_ALL_TESTS=1."
        )

    import sys
    import click
    from pathlib import Path
    from pdd.fix_verification_main import fix_verification_main as fix_verification_main_direct

    # Create a simple prompt file with valid content
    prompt_content = """// verify_python.prompt
// Language: Python
// Description: A simple function to divide two numbers
// Inputs: Two numbers a and b
// Outputs: The result of a divided by b

def divide(a, b):
    # Divide a by b and return the result
    return a / b
"""

    # Create a code file with a potential issue (missing validation)
    code_content = """# divide.py
def divide(a, b):
    # Divide a by b and return the result
    return a / b
"""

    # Create a program file to test the functionality
    program_content = """# test_divide.py
import sys
from divide import divide

def main():
    # Test the divide function with various inputs
    try:
        # These should work
        print(f"10 / 2 = {divide(10, 2)}")
        print(f"5 / 2.5 = {divide(5, 2.5)}")
        
        # This will cause an error
        print(f"5 / 0 = {divide(5, 0)}")
    except Exception as e:
        print(f"Error: {e}")
        sys.exit(1)

if __name__ == "__main__":
    main()
"""

    # Create files with the fixture, placing them directly in tmp_path
    files_dict = {}
    for name, content in {
        "verify_python.prompt": prompt_content, 
        "divide.py": code_content, 
        "test_divide.py": program_content
    }.items():
        file_path = tmp_path / name
        file_path.write_text(content)
        files_dict[name] = file_path

    # Get the file paths as strings
    prompt_file = str(files_dict["verify_python.prompt"])
    code_file = str(files_dict["divide.py"])
    program_file = str(files_dict["test_divide.py"])

    # Create output directory relative to tmp_path
    output_dir = tmp_path / "output"
    output_dir.mkdir(exist_ok=True)
    output_results = str(output_dir / "verify_results.log")
    output_code = str(output_dir / "verified_divide.py")
    output_program = str(output_dir / "verified_test_divide.py")

    # Print environment info for debugging
    print(f"Temporary directory: {tmp_path}")
    print(f"Current working directory: {os.getcwd()}")
    print(f"Prompt file location: {prompt_file}")
    print(f"Code file location: {code_file}")
    print(f"Program file location: {program_file}")
    print(f"Output directory: {output_dir}")

    # Create a minimal context object with the necessary parameters
    ctx = click.Context(click.Command("verify"))
    ctx.obj = {
        'force': True,
        'quiet': False,
        'verbose': True,
        'strength': 0.8,
        'temperature': 0.0,
        'local': True,  # Use local execution to avoid API calls
        'output_cost': None,
        'review_examples': False,
        'time': DEFAULT_TIME, # Added time to context
    }

    # Change working directory to tmp_path so imports work correctly
    original_cwd = os.getcwd()
    os.chdir(tmp_path)
    
    # Set PDD_PATH to the project root so prompt templates can be found
    # Get the project root dynamically from the current test file location
    original_pdd_path = os.getenv('PDD_PATH')
    project_root = Path(__file__).parent.parent  # Go up from tests/ to project root
    os.environ['PDD_PATH'] = str(project_root)

    try:
        # Call fix_verification_main directly - with minimal mocking
        success, final_program, final_code, attempts, cost, model = fix_verification_main_direct(
            ctx=ctx,
            prompt_file=prompt_file,
            code_file=code_file,
            program_file=program_file,
            output_results=output_results,
            output_code=output_code,
            output_program=output_program,
            loop=True,
            verification_program=program_file,
            max_attempts=3,
            budget=1.0
        )

        # Verify we got reasonable results back
        assert isinstance(success, bool), "Success should be a boolean"
        assert isinstance(final_code, str), "Final code should be a string"
        assert isinstance(final_program, str), "Final program should be a string" 
        assert attempts >= 0, "Attempts should be non-negative (0 means no fixes needed)"
        assert isinstance(cost, float), "Cost should be a float"
        assert isinstance(model, str), "Model name should be a string"

        # Check output files were created (if successful)
        if success:
            assert Path(output_code).exists(), f"Output code file not created at {output_code}"
            assert Path(output_program).exists(), f"Output program file not created at {output_program}"
            assert Path(output_results).exists(), f"Output results file not created at {output_results}"

            # Verify content of generated code file
            verified_code_content = Path(output_code).read_text()
            assert "def divide" in verified_code_content, "Verified code should contain a divide function"
            # Note: LLM may determine no changes are needed if prompt doesn't require error handling
            print(f"LLM made {attempts} attempts and determined verification was {'successful' if success else 'unsuccessful'}")

            # Print success message and contents
            print("\nTest passed! Verified code:")
            print(verified_code_content)
        else:
            # Still check if any intermediate files were created
            for intermediate_file in output_dir.glob("*divide*.py"):
                print(f"Intermediate file found: {intermediate_file}")
                print(intermediate_file.read_text())

    except Exception as e:
        print(f"Error executing fix_verification_main: {e}")
        import traceback
        traceback.print_exc()
        raise
    finally:
        # Change back to the original working directory and environment
        os.chdir(original_cwd)
        if original_pdd_path:
             os.environ['PDD_PATH'] = original_pdd_path
        else:
             if 'PDD_PATH' in os.environ:
                 del os.environ['PDD_PATH']


@patch('pdd.core.cli.auto_update')
@patch('pdd.commands.utility.fix_verification_main')
def test_cli_verify_command_passes_agentic_fallback(
    mock_fix_verification_main,
    mock_auto_update,
    runner,
    create_dummy_files,
    tmp_path
):
    """Test that verify command passes --agentic-fallback to fix_verification_main."""
    files = create_dummy_files("test.prompt", "test.py", "program.py")

    mock_fix_verification_main.return_value = (True, "prog", "code", 1, 0.01, "model")

    # Test with --no-agentic-fallback
    result = runner.invoke(cli.cli, [
        "verify",
        str(files["test.prompt"]),
        str(files["test.py"]),
        str(files["program.py"]),
        "--no-agentic-fallback",
    ])

    assert result.exit_code == 0, f"Expected exit code 0, got {result.exit_code}. Output: {result.output}"
    mock_fix_verification_main.assert_called_once()
    kwargs = mock_fix_verification_main.call_args.kwargs
    assert kwargs.get('agentic_fallback') is False, \
        "Expected agentic_fallback=False when --no-agentic-fallback is passed"