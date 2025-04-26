import pytest
import click
import sys
import os
from unittest.mock import patch, MagicMock, mock_open, ANY

# Import DEFAULT_STRENGTH
from pdd import DEFAULT_STRENGTH

# Assuming the structure is tests/test_fix_verification_main.py
# and the code is pdd/fix_verification_main.py
from pdd.fix_verification_main import fix_verification_main, DEFAULT_TEMPERATURE # Import DEFAULT_TEMPERATURE if needed

# --- Fixtures ---

@pytest.fixture
def mock_context(tmp_path):
    """Creates a mock Click context object."""
    ctx = MagicMock(spec=click.Context)
    # Initialize ctx.obj for global options
    ctx.obj = {
        'strength': DEFAULT_STRENGTH,
        'temperature': DEFAULT_TEMPERATURE, # Use imported default
        'force': False,
        'quiet': False,
        'verbose': False,
    }
    # params usually holds command-specific parameters, leave empty for this command
    ctx.params = {}
    return ctx

@pytest.fixture
def setup_files(tmp_path):
    """Creates dummy input files."""
    prompt_path = tmp_path / "prompt.txt"
    code_path = tmp_path / "code.py"
    program_path = tmp_path / "program.py"
    verifier_path = tmp_path / "verifier.py" # For loop mode

    prompt_path.write_text("Original prompt content")
    code_path.write_text("Original code content")
    program_path.write_text("Original program content")
    verifier_path.write_text("Verification program content")

    return {
        "prompt": str(prompt_path),
        "code": str(code_path),
        "program": str(program_path),
        "verifier": str(verifier_path),
    }

@pytest.fixture
def mock_construct_paths_response(tmp_path):
    """Provides a default mock response for construct_paths."""
    output_code_path = tmp_path / "output_verified.py"
    output_results_path = tmp_path / "output_results.log"
    return (
        { # input_strings
            "prompt_file": "Original prompt content",
            "code_file": "Original code content",
            "program_file": "Original program content",
            # Include verifier content if needed by the test calling this
            "verification_program": "Verification program content"
        },
        { # output_file_paths
            "output_code": str(output_code_path),
            "output_results": str(output_results_path),
        },
        "python" # language
    )

# --- Test Cases ---

@patch('pdd.fix_verification_main.fix_verification_errors_loop')
@patch('pdd.fix_verification_main.fix_verification_errors')
@patch('pdd.fix_verification_main.run_program')
@patch('pdd.fix_verification_main.construct_paths')
def test_single_pass_success_no_issues(
    mock_construct, mock_run_prog, mock_fix_errors, mock_fix_loop,
    mock_context, setup_files, mock_construct_paths_response, tmp_path
):
    """Verify single pass success when LLM finds no issues."""
    mock_construct.return_value = mock_construct_paths_response
    mock_run_prog.return_value = (True, "Program ran ok", "")
    mock_fix_errors.return_value = {
        'verification_issues_count': 0,
        'fixed_program': 'Original program content',
        'fixed_code': 'Original code content',
        'total_cost': 0.1,
        'model_name': 'model-a',
        'explanation': ['All good']
    }

    output_code_path = mock_construct_paths_response[1]["output_code"]
    output_results_path = mock_construct_paths_response[1]["output_results"]

    result = fix_verification_main(
        ctx=mock_context,
        prompt_file=setup_files["prompt"],
        code_file=setup_files["code"],
        program_file=setup_files["program"],
        output_results=None, # Use default from construct_paths mock
        output_code=None,    # Use default from construct_paths mock
        loop=False,
        verification_program=None
    )

    mock_construct.assert_called_once()
    # Check force was read from ctx.obj (default is False)
    assert mock_construct.call_args[1]['force'] is False
    mock_run_prog.assert_called_once_with(setup_files["program"])
    mock_fix_errors.assert_called_once_with(
        program='Original program content',
        prompt='Original prompt content',
        code='Original code content',
        output='Program ran ok',
        strength=DEFAULT_STRENGTH,
        temperature=DEFAULT_TEMPERATURE, # Check default temp
        verbose=False # Check default verbose
    )
    mock_fix_loop.assert_not_called()

    assert result == (True, 'Original program content', 'Original code content', 1, 0.1, 'model-a')
    assert os.path.exists(output_code_path)
    assert open(output_code_path).read() == 'Original code content'
    assert os.path.exists(output_results_path)
    assert "Success: True" in open(output_results_path).read()
    assert "Issues Found Count: 0" in open(output_results_path).read()


@patch('pdd.fix_verification_main.fix_verification_errors_loop')
@patch('pdd.fix_verification_main.fix_verification_errors')
@patch('pdd.fix_verification_main.run_program')
@patch('pdd.fix_verification_main.construct_paths')
def test_single_pass_success_with_fixes(
    mock_construct, mock_run_prog, mock_fix_errors, mock_fix_loop,
    mock_context, setup_files, mock_construct_paths_response, tmp_path
):
    """Verify single pass success when LLM finds issues and fixes them."""
    mock_construct.return_value = mock_construct_paths_response
    mock_run_prog.return_value = (True, "Program output with issue", "")
    mock_fix_errors.return_value = {
        'verification_issues_count': 1,
        'fixed_program': 'Fixed program content',
        'fixed_code': 'Fixed code content',
        'total_cost': 0.2,
        'model_name': 'model-b',
        'explanation': ['Found issue', 'Applied fix']
    }

    output_code_path = mock_construct_paths_response[1]["output_code"]
    output_results_path = mock_construct_paths_response[1]["output_results"]

    result = fix_verification_main(
        ctx=mock_context,
        prompt_file=setup_files["prompt"],
        code_file=setup_files["code"],
        program_file=setup_files["program"],
        output_results=None,
        output_code=None,
        loop=False,
        verification_program=None
    )

    mock_construct.assert_called_once()
    mock_run_prog.assert_called_once()
    mock_fix_errors.assert_called_once()
    mock_fix_loop.assert_not_called()

    assert result == (True, 'Fixed program content', 'Fixed code content', 1, 0.2, 'model-b')
    assert os.path.exists(output_code_path)
    assert open(output_code_path).read() == 'Fixed code content'
    assert os.path.exists(output_results_path)
    assert "Success: True" in open(output_results_path).read() # Success because fixes were applied
    assert "Issues Found Count: 1" in open(output_results_path).read()
    assert "Code Updated: True" in open(output_results_path).read()


@patch('pdd.fix_verification_main.fix_verification_errors_loop')
@patch('pdd.fix_verification_main.fix_verification_errors')
@patch('pdd.fix_verification_main.run_program')
@patch('pdd.fix_verification_main.construct_paths')
def test_single_pass_failure_no_fixes(
    mock_construct, mock_run_prog, mock_fix_errors, mock_fix_loop,
    mock_context, setup_files, mock_construct_paths_response, tmp_path
):
    """Verify single pass failure when LLM finds issues but proposes no fixes."""
    mock_construct.return_value = mock_construct_paths_response
    mock_run_prog.return_value = (True, "Program output with issue", "")
    mock_fix_errors.return_value = {
        'verification_issues_count': 1,
        'fixed_program': 'Original program content', # No change
        'fixed_code': 'Original code content',     # No change
        'total_cost': 0.15,
        'model_name': 'model-c',
        'explanation': ['Found issue', 'Could not fix']
    }

    output_code_path = mock_construct_paths_response[1]["output_code"]
    output_results_path = mock_construct_paths_response[1]["output_results"]

    result = fix_verification_main(
        ctx=mock_context,
        prompt_file=setup_files["prompt"],
        code_file=setup_files["code"],
        program_file=setup_files["program"],
        output_results=None,
        output_code=None,
        loop=False,
        verification_program=None
    )

    mock_construct.assert_called_once()
    mock_run_prog.assert_called_once()
    mock_fix_errors.assert_called_once()
    mock_fix_loop.assert_not_called()

    assert result == (False, 'Original program content', 'Original code content', 1, 0.15, 'model-c')
    # Output code should NOT be written on failure
    assert not os.path.exists(output_code_path)
    assert os.path.exists(output_results_path)
    assert "Success: False" in open(output_results_path).read()
    assert "Issues Found Count: 1" in open(output_results_path).read()
    assert "Code Updated: False" in open(output_results_path).read()


@patch('pdd.fix_verification_main.fix_verification_errors_loop')
@patch('pdd.fix_verification_main.fix_verification_errors')
@patch('pdd.fix_verification_main.run_program')
@patch('pdd.fix_verification_main.construct_paths')
def test_single_pass_program_run_fails(
    mock_construct, mock_run_prog, mock_fix_errors, mock_fix_loop,
    mock_context, setup_files, mock_construct_paths_response
):
    """Verify single pass still calls LLM even if program execution fails."""
    mock_construct.return_value = mock_construct_paths_response
    mock_run_prog.return_value = (False, "Partial output", "Traceback error")
    # Assume LLM fails to fix based on error output
    mock_fix_errors.return_value = {
        'verification_issues_count': 1,
        'fixed_program': 'Original program content',
        'fixed_code': 'Original code content',
        'total_cost': 0.1,
        'model_name': 'model-a',
        'explanation': ['Error in program run']
    }

    result = fix_verification_main(
        ctx=mock_context,
        prompt_file=setup_files["prompt"],
        code_file=setup_files["code"],
        program_file=setup_files["program"],
        output_results=None,
        output_code=None,
        loop=False,
        verification_program=None
    )

    mock_construct.assert_called_once()
    mock_run_prog.assert_called_once_with(setup_files["program"])
    mock_fix_errors.assert_called_once_with(
        program='Original program content',
        prompt='Original prompt content',
        code='Original code content',
        output='Partial output\n--- STDERR ---\nTraceback error', # Check combined output
        strength=DEFAULT_STRENGTH,
        temperature=DEFAULT_TEMPERATURE,
        verbose=False
    )
    mock_fix_loop.assert_not_called()
    assert result[0] is False # Should fail if program fails and LLM doesn't fix


@patch('pdd.fix_verification_main.fix_verification_errors_loop')
@patch('pdd.fix_verification_main.fix_verification_errors')
@patch('pdd.fix_verification_main.run_program')
@patch('pdd.fix_verification_main.construct_paths')
def test_loop_mode_success(
    mock_construct, mock_run_prog, mock_fix_errors, mock_fix_loop,
    mock_context, setup_files, mock_construct_paths_response, tmp_path
):
    """Verify loop mode calls fix_verification_errors_loop and handles success."""
    # Adjust mock construct_paths to include verifier path info if needed by loop
    input_strings, output_paths, lang = mock_construct_paths_response
    mock_construct.return_value = (input_strings, output_paths, lang)

    mock_fix_loop.return_value = {
        'success': True,
        'final_program': 'Final program loop',
        'final_code': 'Final code loop',
        'total_attempts': 3,
        'total_cost': 0.6,
        'model_name': 'model-d'
    }
    output_code_path = output_paths["output_code"]
    output_results_path = output_paths["output_results"] # Loop writes this

    result = fix_verification_main(
        ctx=mock_context,
        prompt_file=setup_files["prompt"],
        code_file=setup_files["code"],
        program_file=setup_files["program"],
        output_results=None,
        output_code=None,
        loop=True, # Enable loop
        verification_program=setup_files["verifier"] # Provide verifier
    )

    mock_construct.assert_called_once()
    # Note: construct_paths input_file_paths should include verification_program
    assert "verification_program" in mock_construct.call_args[1]['input_file_paths']
    # Check force was read from ctx.obj (default is False)
    assert mock_construct.call_args[1]['force'] is False

    mock_fix_loop.assert_called_once_with(
        program_file=setup_files["program"],
        code_file=setup_files["code"],
        prompt='Original prompt content', # Pass content
        verification_program=setup_files["verifier"], # Pass path
        strength=DEFAULT_STRENGTH,
        temperature=DEFAULT_TEMPERATURE,
        max_attempts=3, # Default
        budget=5.0,     # Default
        verification_log_file=output_results_path,
        verbose=False, # Check default verbose
        program_args=[] # Default empty args
    )
    mock_fix_errors.assert_not_called()
    mock_run_prog.assert_not_called() # Loop handles its own runs

    assert result == (True, 'Final program loop', 'Final code loop', 3, 0.6, 'model-d')
    assert os.path.exists(output_code_path)
    assert open(output_code_path).read() == 'Final code loop'
    # Main function doesn't write results log in loop mode, loop function does
    # We could check if the file exists if the mock loop created it, but that tests the mock.
    # Instead, we trust the log path was passed correctly.


@patch('pdd.fix_verification_main.fix_verification_errors_loop')
@patch('pdd.fix_verification_main.fix_verification_errors')
@patch('pdd.fix_verification_main.run_program')
@patch('pdd.fix_verification_main.construct_paths')
def test_loop_mode_failure(
    mock_construct, mock_run_prog, mock_fix_errors, mock_fix_loop,
    mock_context, setup_files, mock_construct_paths_response, tmp_path
):
    """Verify loop mode calls fix_verification_errors_loop and handles failure."""
    mock_construct.return_value = mock_construct_paths_response
    mock_fix_loop.return_value = {
        'success': False,
        'final_program': 'Last program loop',
        'final_code': 'Last code loop',
        'total_attempts': 5, # Max attempts reached maybe
        'total_cost': 0.8,
        'model_name': 'model-e'
    }
    output_code_path = mock_construct_paths_response[1]["output_code"]

    result = fix_verification_main(
        ctx=mock_context,
        prompt_file=setup_files["prompt"],
        code_file=setup_files["code"],
        program_file=setup_files["program"],
        output_results=None,
        output_code=None,
        loop=True,
        verification_program=setup_files["verifier"],
        max_attempts=5 # Override default for test clarity
    )

    mock_construct.assert_called_once()
    mock_fix_loop.assert_called_once()
    assert mock_fix_loop.call_args[1]['max_attempts'] == 5 # Check override passed
    mock_fix_errors.assert_not_called()
    mock_run_prog.assert_not_called()

    assert result == (False, 'Last program loop', 'Last code loop', 5, 0.8, 'model-e')
    assert not os.path.exists(output_code_path) # Code not saved on failure


def test_loop_mode_missing_verification_program(mock_context, setup_files):
    """Verify loop mode raises UsageError if verification_program is missing."""
    with pytest.raises(click.UsageError, match="requires '--verification-program'"):
        fix_verification_main(
            ctx=mock_context,
            prompt_file=setup_files["prompt"],
            code_file=setup_files["code"],
            program_file=setup_files["program"],
            output_results=None,
            output_code=None,
            loop=True, # Enable loop
            verification_program=None # MISSING
        )


@patch('pdd.fix_verification_main.construct_paths')
def test_construct_paths_file_not_found(mock_construct, mock_context, setup_files, capsys):
    """Verify SystemExit if construct_paths raises FileNotFoundError."""
    # Simulate construct_paths raising FileNotFoundError AFTER global options are read
    def construct_side_effect(*args, **kwargs):
        raise FileNotFoundError("mock_file.txt not found")
    mock_construct.side_effect = construct_side_effect

    with pytest.raises(SystemExit) as e:
        fix_verification_main(
            ctx=mock_context,
            prompt_file=setup_files["prompt"],
            code_file=setup_files["code"],
            program_file=setup_files["program"],
            output_results=None,
            output_code=None,
            loop=False,
            verification_program=None
        )

    assert e.value.code == 1
    captured = capsys.readouterr()
    # Check for the actual error message prefix printed by the code
    assert "Failed during path construction" in captured.out
    # Ensure global options were read before the error
    assert 'force' in mock_construct.call_args[1]


@patch('builtins.open', new_callable=mock_open)
@patch('pdd.fix_verification_main.rich_print') # Patch rich_print
@patch('pdd.fix_verification_main.fix_verification_errors_loop')
@patch('pdd.fix_verification_main.fix_verification_errors')
@patch('pdd.fix_verification_main.run_program')
@patch('pdd.fix_verification_main.construct_paths')
def test_output_code_write_error(
    mock_construct, mock_run_prog, mock_fix_errors, mock_fix_loop, mock_rich_print, mock_open_func,
    mock_context, setup_files, mock_construct_paths_response, capsys
):
    """Verify error message if writing verified code fails."""
    mock_construct.return_value = mock_construct_paths_response
    mock_run_prog.return_value = (True, "Program ran ok", "")
    mock_fix_errors.return_value = { # Simulate success
        'verification_issues_count': 0,
        'fixed_program': 'Original program content',
        'fixed_code': 'Original code content',
        'total_cost': 0.1, 'model_name': 'model-a', 'explanation': ['OK']
    }

    output_code_path = mock_construct_paths_response[1]["output_code"]
    output_results_path = mock_construct_paths_response[1]["output_results"]

    # Keep a reference to the mock object itself to call its original behavior
    original_open_behavior = mock_open_func

    # Define the side_effect function to simulate IOError for a specific file
    def faulty_open(*args, **kwargs):
        file_path = args[0]
        mode = args[1] if len(args) > 1 else "r" # Default mode is 'r'

        # Raise error only for the specific code file path in write mode
        if file_path == output_code_path and "w" in mode:
            raise IOError("Disk full simulation")
        else:
            # For all other calls, delegate to the original mock_open behavior
            # Temporarily disable the side_effect to prevent recursion
            original_open_behavior.side_effect = None
            try:
                # Call the mock object itself to get the default mock file handle
                result = original_open_behavior(*args, **kwargs)
            finally:
                # IMPORTANT: Restore this function as the side_effect
                original_open_behavior.side_effect = faulty_open
            return result

    # Set the faulty_open function as the side_effect for the mock
    mock_open_func.side_effect = faulty_open

    result = fix_verification_main(
        ctx=mock_context,
        prompt_file=setup_files["prompt"],
        code_file=setup_files["code"],
        program_file=setup_files["program"],
        output_results=None,
        output_code=None,
        loop=False,
        verification_program=None
    )

    assert result[0] is True # Verification itself succeeded
    # Instead of checking capsys, assert that rich_print was called with the error message
    expected_error_msg = f"[bold red]Error:[/bold red] Failed to write verified code file '{output_code_path}': Disk full simulation"
    mock_rich_print.assert_any_call(expected_error_msg)
    # Check that the results file was still attempted to be written
    # This assertion checks if 'open' was called with the results path and write mode
    mock_open_func.assert_any_call(output_results_path, "w")


@patch('pdd.fix_verification_main.fix_verification_errors_loop')
@patch('pdd.fix_verification_main.fix_verification_errors')
@patch('pdd.fix_verification_main.run_program')
@patch('pdd.fix_verification_main.construct_paths')
def test_verbose_flag_propagation(
    mock_construct, mock_run_prog, mock_fix_errors, mock_fix_loop,
    mock_context, setup_files, mock_construct_paths_response
):
    """Verify verbose flag is passed down."""
    # Set verbose=True in ctx.obj
    mock_context.obj['verbose'] = True
    mock_construct.return_value = mock_construct_paths_response
    mock_run_prog.return_value = (True, "Output", "")
    mock_fix_errors.return_value = { 'verification_issues_count': 0, 'fixed_program': 'p', 'fixed_code': 'c', 'total_cost': 0, 'model_name': 'm', 'explanation': [] }
    mock_fix_loop.return_value = { 'success': True, 'final_program': 'p', 'final_code': 'c', 'total_attempts': 1, 'total_cost': 0, 'model_name': 'm' }

    # Test single pass
    fix_verification_main(
        ctx=mock_context, prompt_file=setup_files["prompt"], code_file=setup_files["code"],
        program_file=setup_files["program"], output_results=None, output_code=None,
        loop=False, verification_program=None
    )
    mock_fix_errors.assert_called_once_with(
        program=ANY, prompt=ANY, code=ANY, output=ANY,
        strength=ANY, temperature=ANY, verbose=True # Check verbose=True
    )

    # Reset mocks and test loop mode
    mock_fix_errors.reset_mock()
    mock_construct.reset_mock() # Reset construct_paths mock as well
    # Reset verbose flag for loop test (or ensure it's still True if intended)
    mock_context.obj['verbose'] = True # Ensure it's set for the loop call too

    fix_verification_main(
        ctx=mock_context, prompt_file=setup_files["prompt"], code_file=setup_files["code"],
        program_file=setup_files["program"], output_results=None, output_code=None,
        loop=True, verification_program=setup_files["verifier"]
    )
    mock_fix_loop.assert_called_once_with(
        program_file=ANY, code_file=ANY, prompt=ANY, verification_program=ANY,
        strength=ANY, temperature=ANY, max_attempts=ANY, budget=ANY,
        verification_log_file=ANY, verbose=True, program_args=ANY # Check verbose=True
    )


@patch('pdd.fix_verification_main.fix_verification_errors_loop')
@patch('pdd.fix_verification_main.fix_verification_errors')
@patch('pdd.fix_verification_main.run_program')
@patch('pdd.fix_verification_main.construct_paths')
def test_force_flag_retrieved_from_ctx_obj(
    mock_construct, mock_run_prog, mock_fix_errors, mock_fix_loop,
    mock_context, setup_files, mock_construct_paths_response, tmp_path
):
    """
    Test that fix_verification_main retrieves the 'force' flag from ctx.obj,
    not ctx.params.
    """
    # Modify the mock context to simulate --force being passed globally
    # Set force=True in obj (correct place)
    mock_context.obj['force'] = True
    # Ensure force is NOT in params (or is False) to test correct retrieval
    # ctx.params is already empty in the updated fixture, so no change needed here.

    # Prepare mocks as in a standard successful run (using loop mode for simplicity)
    mock_construct.return_value = mock_construct_paths_response
    mock_fix_loop.return_value = {
        'success': True,
        'final_program': 'Fixed program',
        'final_code': 'Fixed code',
        'total_attempts': 1,
        'total_cost': 0.3,
        'model_name': 'model-loop'
    }

    # Call the function in loop mode (as it's the default for verify)
    fix_verification_main(
        ctx=mock_context,
        prompt_file=setup_files["prompt"],
        code_file=setup_files["code"],
        program_file=setup_files["program"],
        output_results=None,
        output_code=None,
        loop=True,
        verification_program=setup_files["verifier"] # Required for loop mode
    )

    # --- THE CRUCIAL ASSERTION ---
    # Check that construct_paths was called with force=True, which means
    # the value must have been read from ctx.obj, not ctx.params.
    mock_construct.assert_called_once()
    call_args, call_kwargs = mock_construct.call_args
    assert call_kwargs.get('force') is True, "construct_paths should have been called with force=True"

    # Other mocks should not be called in loop mode
    mock_run_prog.assert_not_called()
    mock_fix_errors.assert_not_called()
    mock_fix_loop.assert_called_once() # Ensure loop function was called