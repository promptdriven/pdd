# tests/test_commands_fix.py
"""Tests for commands/fix."""
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


@pytest.mark.real
def test_real_fix_command(create_dummy_files, tmp_path):
    """Test the 'fix' command with real files by calling the function directly."""
    if not (os.getenv("PDD_RUN_REAL_LLM_TESTS") or RUN_ALL_TESTS_ENABLED):
        pytest.skip(
            "Real LLM integration tests require network/API access; set "
            "PDD_RUN_REAL_LLM_TESTS=1 or use --run-all / PDD_RUN_ALL_TESTS=1."
        )

    import sys
    import click
    from pathlib import Path
    # Import fix_main locally to avoid interfering with mocks in other tests
    from pdd.fix_main import fix_main as fix_main_direct

    # Create a prompt file with valid content
    prompt_content = """// fix_python.prompt
// Language: Python
// Description: A simple function to add two numbers
// Inputs: Two numbers a and b
// Outputs: The sum of a and b

def add(a, b):
    # Add two numbers and return the result
    return a + b
"""

    # Create a code file with a bug
    code_content = """# add.py
def add(a, b):
    # This has a bug - it doesn't return anything
    result = a + b
    # Missing return statement
"""

    # Create a test file that will fail
    test_content = """# test_add.py
import unittest
# Use relative import if 'add.py' is in the same directory
try:
    from .add import add
except ImportError:
    from add import add

class TestAdd(unittest.TestCase):
    def test_add(self):
        self.assertEqual(add(2, 3), 5)
        self.assertEqual(add(-1, 1), 0)
        self.assertEqual(add(0, 0), 0)

if __name__ == '__main__':
    # Need to make sure unittest can find the test
    # Add current directory to sys.path if running as script
    if '.' not in sys.path:
         sys.path.insert(0, '.')
    unittest.main(module=None) # Use module=None for auto-discovery
"""

    # Create an error log file with the test failure
    error_content = """============================= test session starts ==============================
platform darwin -- Python 3.9.7, pytest-7.0.1, pluggy-1.0.0
rootdir: /tmp/test_fix
collected 1 item

test_add.py F                                                              [100%]

=================================== FAILURES ===================================
_________________________________ TestAdd.test_add _________________________________

self = <test_add.TestAdd testMethod=test_add>

    def test_add(self):
>       self.assertEqual(add(2, 3), 5)
E       AssertionError: None != 5

test_add.py:11: AssertionError
=========================== short test summary info ============================
FAILED test_add.py::TestAdd::test_add - AssertionError: None != 5
"""

    # Create a simple verification program (Changed from f-string to regular string)
    verification_content = """# verify.py
import unittest
import subprocess
import sys
from pathlib import Path

# Ensure the directory containing add.py is in the python path
# This is crucial when running verify.py from a different directory (like tmp_path)
script_dir = Path(__file__).parent.resolve()
if str(script_dir) not in sys.path:
    sys.path.insert(0, str(script_dir))

try:
    # Try importing 'add' assuming it's in the same directory or python path
    from add import add
except ModuleNotFoundError:
    # Use script_dir directly in the f-string inside the script's scope
    print(f"Error: Could not import 'add' from {script_dir}. Check PYTHONPATH.")
    sys.exit(1)

# Try loading tests specifically from the test_add module
# Ensure test_add.py is also discoverable
try:
    loader = unittest.defaultTestLoader
    suite = loader.loadTestsFromName('test_add.TestAdd') # Load from the module name
except (AttributeError, ImportError, ValueError) as e:
     # Use script_dir directly in the f-string inside the script's scope
     print(f"Error loading tests from 'test_add.TestAdd': {e}")
     # Fallback or alternative discovery if needed
     # suite = loader.discover(start_dir=str(script_dir), pattern='test_add.py')
     sys.exit(1)


# Run the tests
# Use suite directly in the f-string inside the script's scope
print(f"Running tests from suite: {suite}")
runner = unittest.TextTestRunner()
test_result = runner.run(suite)


# Exit with appropriate code
sys.exit(0 if test_result.wasSuccessful() else 1)
"""

    # Create empty dummy files with the fixture, placing them directly in tmp_path
    # This makes imports simpler for the verification script
    files_dict = {}
    for name in ["fix_python.prompt", "add.py", "test_add.py", "errors.log", "verify.py"]:
        file_path = tmp_path / name
        file_path.parent.mkdir(parents=True, exist_ok=True)
        file_path.touch() # Create empty file first
        files_dict[name] = file_path

    # Set the content for each file
    files_dict["fix_python.prompt"].write_text(prompt_content)
    files_dict["add.py"].write_text(code_content)
    files_dict["test_add.py"].write_text(test_content)
    files_dict["errors.log"].write_text(error_content)
    files_dict["verify.py"].write_text(verification_content)

    # Get the file paths as strings
    prompt_file = str(files_dict["fix_python.prompt"])
    code_file = str(files_dict["add.py"])
    test_file = str(files_dict["test_add.py"])
    error_file = str(files_dict["errors.log"])
    verification_file = str(files_dict["verify.py"])

    # Create output directory relative to tmp_path
    output_dir = tmp_path / "output"
    output_dir.mkdir(exist_ok=True)
    output_test = str(output_dir / "fixed_test_add.py")
    output_code = str(output_dir / "fixed_add.py")
    output_results = str(output_dir / "fix_results.log")

    # Print environment info for debugging
    print(f"Temporary directory: {tmp_path}")
    print(f"Current working directory: {os.getcwd()}")
    print(f"Prompt file location: {prompt_file}")
    print(f"Code file location: {code_file}")
    print(f"Test file location: {test_file}")
    print(f"Error file location: {error_file}")
    print(f"Verification file location: {verification_file}")
    print(f"Output directory: {output_dir}")

    # Create a minimal context object with the necessary parameters
    ctx = click.Context(click.Command("fix"))
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
        # Call fix_main directly - with no mock this time
        success, fixed_test, fixed_code, attempts, cost, model = fix_main_direct(
            ctx=ctx,
            prompt_file=prompt_file, # Use absolute path
            code_file=code_file,     # Use absolute path
            unit_test_file=test_file,# Use absolute path
            error_file=error_file,   # Use absolute path
            output_test=output_test, # Use absolute path
            output_code=output_code, # Use absolute path
            output_results=output_results,# Use absolute path
            loop=False,  # Use simple mode for testing
            verification_program=None,  # Not needed in simple mode
            max_attempts=3,
            budget=1.0,
            auto_submit=False
        )

        # Verify we got reasonable results back
        assert isinstance(success, bool), "Success should be a boolean"
        # fixed_test can be empty if no changes were needed
        assert isinstance(fixed_test, str), "Fixed test should be a string"
        assert isinstance(fixed_code, str), "Fixed code should be a string"
        assert attempts > 0, "Should have at least one attempt"
        assert isinstance(cost, float), "Cost should be a float"
        assert isinstance(model, str), "Model name should be a string"

        # Check output files were created
        # Only check test file if content was returned (previous fix)
        if fixed_test: # Only check if the returned content is non-empty
            assert Path(output_test).exists(), f"Output test file not created at {output_test} even though content was returned"

        assert Path(output_code).exists(), f"Output code file not created at {output_code}"

        # Verify content of generated code file
        fixed_code_content = Path(output_code).read_text()
        assert "def add" in fixed_code_content, "Fixed code should contain an add function"
        assert "return" in fixed_code_content, "Fixed code should include a return statement"
        # The fix should add the return statement
        assert "return result" in fixed_code_content or "return a + b" in fixed_code_content

        # Print success message
        print(f"Successfully fixed code at {output_code}")

    except Exception as e:
        pytest.fail(f"Real fix test failed: {e}")

    finally:
        # Restore original PDD_PATH
        if original_pdd_path:
             os.environ['PDD_PATH'] = original_pdd_path
        else:
             if 'PDD_PATH' in os.environ:
                 del os.environ['PDD_PATH']
        
        # Restore original working directory
        os.chdir(original_cwd)


def test_fix_command_exits_nonzero_for_nonexistent_error_file(tmp_path):
    """
    Test that the 'fix' command exits with a non-zero exit code when the
    error_file does not exist (regression test for error handling).
    """
    runner = CliRunner()

    # Create valid prompt, code, and test files
    prompt_file = tmp_path / "test.prompt"
    prompt_file.write_text("// Test prompt\ndef foo(): pass")

    code_file = tmp_path / "code.py"
    code_file.write_text("def foo(): pass")

    test_file = tmp_path / "test_code.py"
    test_file.write_text("def test_foo(): assert True")

    # Error file intentionally does NOT exist
    nonexistent_error_file = tmp_path / "nonexistent" / "error.log"

    result = runner.invoke(
        cli.cli,
        [
            "--force",
            "fix",
            str(prompt_file),
            str(code_file),
            str(test_file),
            str(nonexistent_error_file),
        ],
    )

    # The command should exit with a non-zero code since the error file doesn't exist
    assert result.exit_code != 0, (
        f"Expected non-zero exit code for nonexistent error file, "
        f"got {result.exit_code}. Output: {result.output}"
    )


def test_cli_fix_multiple_test_files(tmp_path):
    """Test that the fix command accepts multiple test files."""
    runner = CliRunner()

    prompt_file = tmp_path / "prompt.prompt"
    prompt_file.write_text("prompt content")
    code_file = tmp_path / "code.py"
    code_file.write_text("code content")
    test_file_1 = tmp_path / "test_1.py"
    test_file_1.write_text("test 1 content")
    test_file_2 = tmp_path / "test_2.py"
    test_file_2.write_text("test 2 content")
    error_file = tmp_path / "error.txt"
    error_file.write_text("error content")

    with patch('pdd.commands.fix.fix_main') as mock_fix_main:
        mock_fix_main.return_value = (True, "fixed_test", "fixed_code", 1, 0.1, "gpt-4")
        result = runner.invoke(cli.cli, [
            'fix',
            str(prompt_file),
            str(code_file),
            str(test_file_1),
            str(test_file_2),
            str(error_file),
        ])
        assert result.exit_code == 0
        assert mock_fix_main.call_count == 2
        mock_fix_main.assert_any_call(
            ctx=ANY,
            prompt_file=str(prompt_file),
            code_file=str(code_file),
            unit_test_file=str(test_file_1),
            error_file=str(error_file),
            output_test=None,
            output_code=None,
            output_results=None,
            loop=False,
            verification_program=None,
            max_attempts=3,
            budget=5.0,
            auto_submit=False,
            agentic_fallback=True,
            strength=None,
            temperature=None,
        )
        mock_fix_main.assert_any_call(
            ctx=ANY,
            prompt_file=str(prompt_file),
            code_file=str(code_file),
            unit_test_file=str(test_file_2),
            error_file=str(error_file),
            output_test=None,
            output_code=None,
            output_results=None,
            loop=False,
            verification_program=None,
            max_attempts=3,
            budget=5.0,
            auto_submit=False,
            agentic_fallback=True,
            strength=None,
            temperature=None,
        )

@pytest.mark.parametrize("num_test_files", [1, 2])
def test_cli_fix_loop_mode_no_error_file(tmp_path, num_test_files):
    """Test --loop mode doesn't require ERROR_FILE (Issue #233)."""
    runner = CliRunner()

    # Setup files
    prompt_file = tmp_path / "prompt.prompt"
    prompt_file.write_text("prompt content")
    code_file = tmp_path / "code.py"
    code_file.write_text("code content")
    verify_file = tmp_path / "verify.py"
    verify_file.write_text("import sys; sys.exit(0)")

    test_files = [tmp_path / f"test_{i}.py" for i in range(num_test_files)]
    for tf in test_files:
        tf.write_text("test content")

    with patch('pdd.commands.fix.fix_main') as mock_fix_main:
        mock_fix_main.return_value = (True, "fixed_test", "fixed_code", 1, 0.1, "gpt-4")
        result = runner.invoke(cli.cli, [
            'fix', '--manual', '--loop', '--verification-program', str(verify_file),
            str(prompt_file), str(code_file), *[str(tf) for tf in test_files]
        ])

        assert result.exit_code == 0, f"Command failed: {result.output}"
        assert mock_fix_main.call_count == num_test_files
        # Verify error_file=None and loop=True for all calls
        for call in mock_fix_main.call_args_list:
            assert call[1]['error_file'] is None, "error_file should be None in loop mode"
            assert call[1]['loop'] is True, "loop should be True"


def test_cli_fix_non_loop_mode_requires_error_file(tmp_path):
    """Test non-loop mode fails without ERROR_FILE (Issue #233)."""
    runner = CliRunner()

    prompt_file = tmp_path / "prompt.prompt"
    prompt_file.write_text("prompt content")
    code_file = tmp_path / "code.py"
    code_file.write_text("code content")
    test_file = tmp_path / "test.py"
    test_file.write_text("test content")

    # Non-loop mode requires ERROR_FILE as the last argument
    result = runner.invoke(cli.cli, [
        'fix', '--manual', str(prompt_file), str(code_file), str(test_file)
    ])

    # Should fail because ERROR_FILE is missing
    assert result.exit_code != 0, "Should fail without ERROR_FILE in non-loop mode"
    assert "requires at least 4 arguments" in result.output or "ERROR_FILE" in result.output
