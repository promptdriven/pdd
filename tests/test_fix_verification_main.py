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
    output_program_path = tmp_path / "output_verified_program.py"
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
            "output_program": str(output_program_path),
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
    output_program_path = mock_construct_paths_response[1]["output_program"]

    result = fix_verification_main(
        ctx=mock_context,
        prompt_file=setup_files["prompt"],
        code_file=setup_files["code"],
        program_file=setup_files["program"],
        output_results=None,
        output_code=None,
        output_program=None,
        loop=False,
        verification_program=None
    )

    mock_construct.assert_called_once()
    assert mock_construct.call_args[1]['force'] is False
    mock_run_prog.assert_called_once_with(setup_files["program"])
    mock_fix_errors.assert_called_once_with(
        program='Original program content',
        prompt='Original prompt content',
        code='Original code content',
        output='Program ran ok',
        strength=DEFAULT_STRENGTH,
        temperature=DEFAULT_TEMPERATURE,
        verbose=False
    )
    mock_fix_loop.assert_not_called()

    assert result == (True, 'Original program content', 'Original code content', 1, 0.1, 'model-a')
    assert os.path.exists(output_code_path)
    assert open(output_code_path).read() == 'Original code content'
    assert os.path.exists(output_program_path)
    assert open(output_program_path).read() == 'Original program content'
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
    output_program_path = mock_construct_paths_response[1]["output_program"]

    result = fix_verification_main(
        ctx=mock_context,
        prompt_file=setup_files["prompt"],
        code_file=setup_files["code"],
        program_file=setup_files["program"],
        output_results=None,
        output_code=None,
        output_program=None,
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
    assert os.path.exists(output_program_path)
    assert open(output_program_path).read() == 'Fixed program content'
    assert os.path.exists(output_results_path)
    assert "Success: True" in open(output_results_path).read()
    assert "Issues Found Count: 1" in open(output_results_path).read()
    assert "Code Updated: True" in open(output_results_path).read()
    assert "Program Updated: True" in open(output_results_path).read()


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
        'fixed_program': 'Original program content',
        'fixed_code': 'Original code content',
        'total_cost': 0.15,
        'model_name': 'model-c',
        'explanation': ['Found issue', 'Could not fix']
    }

    output_code_path = mock_construct_paths_response[1]["output_code"]
    output_results_path = mock_construct_paths_response[1]["output_results"]
    output_program_path = mock_construct_paths_response[1]["output_program"]

    result = fix_verification_main(
        ctx=mock_context,
        prompt_file=setup_files["prompt"],
        code_file=setup_files["code"],
        program_file=setup_files["program"],
        output_results=None,
        output_code=None,
        output_program=None,
        loop=False,
        verification_program=None
    )

    mock_construct.assert_called_once()
    mock_run_prog.assert_called_once()
    mock_fix_errors.assert_called_once()
    mock_fix_loop.assert_not_called()

    assert result == (False, 'Original program content', 'Original code content', 1, 0.15, 'model-c')
    assert not os.path.exists(output_code_path)
    assert not os.path.exists(output_program_path)
    assert os.path.exists(output_results_path)
    assert "Success: False" in open(output_results_path).read()
    assert "Issues Found Count: 1" in open(output_results_path).read()
    assert "Code Updated: False" in open(output_results_path).read()
    assert "Program Updated: False" in open(output_results_path).read()


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
        output_program=None,
        loop=False,
        verification_program=None
    )

    mock_construct.assert_called_once()
    mock_run_prog.assert_called_once_with(setup_files["program"])
    mock_fix_errors.assert_called_once_with(
        program='Original program content',
        prompt='Original prompt content',
        code='Original code content',
        output='Partial output\n--- STDERR ---\nTraceback error',
        strength=DEFAULT_STRENGTH,
        temperature=DEFAULT_TEMPERATURE,
        verbose=False
    )
    mock_fix_loop.assert_not_called()
    assert result[0] is False


@patch('pdd.fix_verification_main.fix_verification_errors_loop')
@patch('pdd.fix_verification_main.fix_verification_errors')
@patch('pdd.fix_verification_main.run_program')
@patch('pdd.fix_verification_main.construct_paths')
def test_loop_mode_success(
    mock_construct, mock_run_prog, mock_fix_errors, mock_fix_loop,
    mock_context, setup_files, mock_construct_paths_response, tmp_path
):
    """Verify loop mode calls fix_verification_errors_loop and handles success."""
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
    output_program_path = output_paths["output_program"]
    output_results_path = output_paths["output_results"]

    result = fix_verification_main(
        ctx=mock_context,
        prompt_file=setup_files["prompt"],
        code_file=setup_files["code"],
        program_file=setup_files["program"],
        output_results=None,
        output_code=None,
        output_program=None,
        loop=True,
        verification_program=setup_files["verifier"]
    )

    mock_construct.assert_called_once()
    assert "verification_program" in mock_construct.call_args[1]['input_file_paths']
    assert mock_construct.call_args[1]['force'] is False

    mock_fix_loop.assert_called_once_with(
        program_file=setup_files["program"],
        code_file=setup_files["code"],
        prompt='Original prompt content',
        verification_program=setup_files["verifier"],
        strength=DEFAULT_STRENGTH,
        temperature=DEFAULT_TEMPERATURE,
        max_attempts=3,
        budget=5.0,
        verification_log_file=output_results_path,
        verbose=False,
        program_args=[]
    )
    mock_fix_errors.assert_not_called()
    mock_run_prog.assert_not_called()

    assert result == (True, 'Final program loop', 'Final code loop', 3, 0.6, 'model-d')
    assert os.path.exists(output_code_path)
    assert open(output_code_path).read() == 'Final code loop'
    assert os.path.exists(output_program_path)
    assert open(output_program_path).read() == 'Final program loop'


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
        'total_attempts': 5,
        'total_cost': 0.8,
        'model_name': 'model-e'
    }
    output_code_path = mock_construct_paths_response[1]["output_code"]
    output_program_path = mock_construct_paths_response[1]["output_program"]

    result = fix_verification_main(
        ctx=mock_context,
        prompt_file=setup_files["prompt"],
        code_file=setup_files["code"],
        program_file=setup_files["program"],
        output_results=None,
        output_code=None,
        output_program=None,
        loop=True,
        verification_program=setup_files["verifier"],
        max_attempts=5
    )

    mock_construct.assert_called_once()
    mock_fix_loop.assert_called_once()
    assert mock_fix_loop.call_args[1]['max_attempts'] == 5
    mock_fix_errors.assert_not_called()
    mock_run_prog.assert_not_called()

    assert result == (False, 'Last program loop', 'Last code loop', 5, 0.8, 'model-e')
    assert not os.path.exists(output_code_path)
    assert not os.path.exists(output_program_path)


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
            output_program=None,
            loop=True,
            verification_program=None
        )


@patch('pdd.fix_verification_main.construct_paths')
def test_construct_paths_file_not_found(mock_construct, mock_context, setup_files, capsys):
    """Verify SystemExit if construct_paths raises FileNotFoundError."""
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
            output_program=None,
            loop=False,
            verification_program=None
        )

    assert e.value.code == 1
    captured = capsys.readouterr()
    assert "Failed during path construction" in captured.out
    assert 'force' in mock_construct.call_args[1]


@patch('builtins.open', new_callable=mock_open)
@patch('pdd.fix_verification_main.rich_print')
@patch('pdd.fix_verification_main.fix_verification_errors_loop')
@patch('pdd.fix_verification_main.fix_verification_errors')
@patch('pdd.fix_verification_main.run_program')
@patch('pdd.fix_verification_main.construct_paths')
def test_output_code_write_error(
    mock_construct, mock_run_prog, mock_fix_errors, mock_fix_loop, mock_rich_print, mock_open_func,
    mock_context, setup_files, mock_construct_paths_response, capsys
):
    """Verify error message if writing verified code fails, but program file succeeds."""
    mock_construct.return_value = mock_construct_paths_response
    mock_run_prog.return_value = (True, "Program ran ok", "")
    # Simulate success so that the code attempts to write the output file
    mock_fix_errors.return_value = {
        'verification_issues_count': 0, # No issues, so success = True
        'fixed_program': 'Original program content',
        'fixed_code': 'Original code content',
        'total_cost': 0.1, 'model_name': 'model-a', 'explanation': ['OK']
    }

    output_code_path = mock_construct_paths_response[1]["output_code"]
    output_results_path = mock_construct_paths_response[1]["output_results"]
    output_program_path = mock_construct_paths_response[1]["output_program"]


    original_open_behavior = mock_open_func

    def faulty_open(*args, **kwargs):
        file_path = args[0]
        mode = args[1] if len(args) > 1 else "r"

        if file_path == output_code_path and "w" in mode:
            raise IOError("Disk full simulation")
        # For other files, use the original mock_open behavior
        # but ensure the side_effect is reset for subsequent calls within this test
        # This is tricky with mock_open. A simpler way is to have specific mocks for specific paths.
        # However, for this test, we'll try to make it work.
        current_side_effect = original_open_behavior.side_effect
        original_open_behavior.side_effect = None # Temporarily disable side effect for this call
        try:
            # If original_open_behavior is just mock_open(), calling it directly is fine.
            # If it had its own side_effect, that would be more complex.
            # Here, we assume it's the mock_open instance.
            if hasattr(original_open_behavior, '_mock_new_call'): # Check if it's a mock_open instance
                 m = original_open_behavior(*args, **kwargs)
            else: # Fallback if it's not a simple mock_open instance (e.g., already has a side_effect)
                 m = MagicMock() # provide a generic mock
                 if "w" in mode:
                     m.write = MagicMock()
                 else: # "r"
                     m.read = MagicMock(return_value="Default read content") # if needed
                 m.__enter__.return_value = m
        finally:
            original_open_behavior.side_effect = current_side_effect # Restore for next call to faulty_open
        return m


    mock_open_func.side_effect = faulty_open

    result = fix_verification_main(
        ctx=mock_context,
        prompt_file=setup_files["prompt"],
        code_file=setup_files["code"],
        program_file=setup_files["program"],
        output_results=None,
        output_code=None,
        output_program=None,
        loop=False,
        verification_program=None
    )

    assert result[0] is True # Overall success was true before write error
    # The code under test prints: f"[bold red]Error:[/bold red] Failed to write code file '{output_code_path}': {type(e).__name__} - {e}"
    # With e = IOError("Disk full simulation"), this becomes:
    # "[bold red]Error:[/bold red] Failed to write code file '{path}': IOError - Disk full simulation"
    expected_error_msg = f"[bold red]Error:[/bold red] Failed to write code file '{output_code_path}': IOError - Disk full simulation"
    mock_rich_print.assert_any_call(expected_error_msg)

    mock_open_func.assert_any_call(output_results_path, "w")
    mock_open_func.assert_any_call(output_program_path, "w")
    # Check that write was attempted on the program file handle
    # This requires inspecting the mock object returned by mock_open_func when output_program_path is opened
    
    # We need to find the mock handle for output_program_path
    # This is a bit complex because faulty_open returns different mocks.
    # A simpler check is that the program file *was* written successfully if the test logic implies it.
    # The test asserts result[0] is True, and the mock_fix_errors implies success.
    # The faulty_open only fails for output_code_path.
    # So, if the program file exists and has content, that's an indirect check.
    # However, the test setup doesn't allow os.path.exists on the mock_open'd files directly.

    # Let's assume the mock_open_func.return_value is the last opened file handle (program file in this case)
    # if the program file was indeed written.
    # This part of the test might need refinement if it's critical to check the write content precisely
    # when multiple files are opened with a complex side_effect.
    # For now, the primary check is the rich_print error message.


@patch('pdd.fix_verification_main.fix_verification_errors_loop')
@patch('pdd.fix_verification_main.fix_verification_errors')
@patch('pdd.fix_verification_main.run_program')
@patch('pdd.fix_verification_main.construct_paths')
def test_verbose_flag_propagation(
    mock_construct, mock_run_prog, mock_fix_errors, mock_fix_loop,
    mock_context, setup_files, mock_construct_paths_response
):
    """Verify verbose flag is passed down."""
    mock_context.obj['verbose'] = True
    mock_construct.return_value = mock_construct_paths_response
    mock_run_prog.return_value = (True, "Output", "")
    mock_fix_errors.return_value = { 'verification_issues_count': 0, 'fixed_program': 'p', 'fixed_code': 'c', 'total_cost': 0, 'model_name': 'm', 'explanation': [] }
    mock_fix_loop.return_value = { 'success': True, 'final_program': 'p', 'final_code': 'c', 'total_attempts': 1, 'total_cost': 0, 'model_name': 'm' }

    fix_verification_main(
        ctx=mock_context, prompt_file=setup_files["prompt"], code_file=setup_files["code"],
        program_file=setup_files["program"], output_results=None, output_code=None,
        output_program=None,
        loop=False, verification_program=None
    )
    mock_fix_errors.assert_called_once_with(
        program=ANY, prompt=ANY, code=ANY, output=ANY,
        strength=ANY, temperature=ANY, verbose=True
    )

    mock_fix_errors.reset_mock() # Reset for the next call
    mock_construct.reset_mock() # Reset construct_paths as it's called again
    # mock_context.obj['verbose'] is already True

    fix_verification_main(
        ctx=mock_context, prompt_file=setup_files["prompt"], code_file=setup_files["code"],
        program_file=setup_files["program"], output_results=None, output_code=None,
        output_program=None,
        loop=True, verification_program=setup_files["verifier"]
    )
    mock_fix_loop.assert_called_once_with(
        program_file=ANY, code_file=ANY, prompt=ANY, verification_program=ANY,
        strength=ANY, temperature=ANY, max_attempts=ANY, budget=ANY,
        verification_log_file=ANY, verbose=True, program_args=ANY
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
    mock_context.obj['force'] = True # Set force in obj

    mock_construct.return_value = mock_construct_paths_response
    mock_fix_loop.return_value = { # Mock for loop mode
        'success': True,
        'final_program': 'Fixed program',
        'final_code': 'Fixed code',
        'total_attempts': 1,
        'total_cost': 0.3,
        'model_name': 'model-loop'
    }
    mock_fix_errors.return_value = { # Mock for single pass mode (if loop=False was tested)
        'verification_issues_count': 0,
        'fixed_program': 'Fixed program',
        'fixed_code': 'Fixed code',
        'total_cost': 0.3,
        'model_name': 'model-single',
        'explanation': []
    }
    mock_run_prog.return_value = (True, "Program output", "")


    # Test with loop=False first to check construct_paths call with force
    mock_context.obj['force'] = True
    fix_verification_main(
        ctx=mock_context,
        prompt_file=setup_files["prompt"],
        code_file=setup_files["code"],
        program_file=setup_files["program"],
        output_results=None,
        output_code=None,
        output_program=None,
        loop=False, # Test single pass
        verification_program=None
    )
    mock_construct.assert_called_once()
    call_args_single, call_kwargs_single = mock_construct.call_args
    assert call_kwargs_single.get('force') is True, "construct_paths should have been called with force=True in single pass"
    mock_fix_errors.assert_called_once() # Ensure single pass path was taken
    mock_fix_loop.assert_not_called()

    # Reset mocks for loop mode test
    mock_construct.reset_mock()
    mock_fix_errors.reset_mock()
    mock_run_prog.reset_mock() # run_program is called in single pass

    mock_context.obj['force'] = True # Ensure it's still set
    fix_verification_main(
        ctx=mock_context,
        prompt_file=setup_files["prompt"],
        code_file=setup_files["code"],
        program_file=setup_files["program"],
        output_results=None,
        output_code=None,
        output_program=None,
        loop=True, # Test loop mode
        verification_program=setup_files["verifier"]
    )

    mock_construct.assert_called_once()
    call_args_loop, call_kwargs_loop = mock_construct.call_args
    assert call_kwargs_loop.get('force') is True, "construct_paths should have been called with force=True in loop mode"

    mock_run_prog.assert_not_called() # Not called in loop mode by fix_verification_main directly
    mock_fix_errors.assert_not_called() # Not called in loop mode
    mock_fix_loop.assert_called_once() # Ensure loop path was taken
