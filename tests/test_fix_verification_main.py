import pytest
import click
import sys
import os
from unittest.mock import patch, MagicMock, mock_open, ANY

# Import DEFAULT_STRENGTH
from pdd import DEFAULT_STRENGTH, DEFAULT_TIME

# Assuming the structure is tests/test_fix_verification_main.py
# and the code is pdd/fix_verification_main.py
from pdd.fix_verification_main import fix_verification_main, DEFAULT_TEMPERATURE, DEFAULT_MAX_ATTEMPTS, DEFAULT_BUDGET # Import DEFAULT_TEMPERATURE if needed

# --- Fixtures ---

@pytest.fixture
def mock_context(tmp_path):
    """Creates a mock Click context object."""
    ctx = MagicMock(spec=click.Context)
    # Initialize ctx.obj for global options
    ctx.obj = {
        'strength': DEFAULT_STRENGTH,
        'temperature': DEFAULT_TEMPERATURE, # Use imported default
        'time': DEFAULT_TIME,
        'force': False,
        'quiet': False,
        'verbose': False,
        'local': True,  # Force local execution to avoid cloud API calls in tests
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
        {},  # resolved_config
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
        'explanation': None
    }

    output_code_path = mock_construct_paths_response[2]["output_code"]
    output_results_path = mock_construct_paths_response[2]["output_results"]
    output_program_path = mock_construct_paths_response[2]["output_program"]

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
        verbose=False,
        time=DEFAULT_TIME
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
        'explanation': '<verification_details>Found issue</verification_details>\n<fix_explanation>Applied fix</fix_explanation>'
    }

    output_code_path = mock_construct_paths_response[2]["output_code"]
    output_results_path = mock_construct_paths_response[2]["output_results"]
    output_program_path = mock_construct_paths_response[2]["output_program"]

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
    mock_fix_errors.assert_called_once_with(
        program=mock_construct_paths_response[1]["program_file"],
        prompt=mock_construct_paths_response[1]["prompt_file"],
        code=mock_construct_paths_response[1]["code_file"],
        output="Program output with issue",
        strength=DEFAULT_STRENGTH,
        temperature=DEFAULT_TEMPERATURE,
        verbose=False,
        time=DEFAULT_TIME
    )
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
        'explanation': '<verification_details>Found issue</verification_details>\n<fix_explanation>Could not fix</fix_explanation>'
    }

    output_code_path = mock_construct_paths_response[2]["output_code"]
    output_results_path = mock_construct_paths_response[2]["output_results"]
    output_program_path = mock_construct_paths_response[2]["output_program"]

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
    mock_fix_errors.assert_called_once_with(
        program=mock_construct_paths_response[1]["program_file"],
        prompt=mock_construct_paths_response[1]["prompt_file"],
        code=mock_construct_paths_response[1]["code_file"],
        output="Program output with issue",
        strength=DEFAULT_STRENGTH,
        temperature=DEFAULT_TEMPERATURE,
        verbose=False,
        time=DEFAULT_TIME
    )
    mock_fix_loop.assert_not_called()

    assert result == (False, 'Original program content', 'Original code content', 1, 0.15, 'model-c')
    # Files should now be written even on failure to allow inspection
    assert os.path.exists(output_code_path)
    assert open(output_code_path).read() == 'Original code content'
    assert os.path.exists(output_program_path)
    assert open(output_program_path).read() == 'Original program content'
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
        'explanation': '<verification_details>Error in program run</verification_details>\n<fix_explanation>No fix applied</fix_explanation>'
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
        verbose=False,
        time=DEFAULT_TIME
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
    resolved_config, input_strings, output_paths, lang = mock_construct_paths_response
    mock_construct.return_value = (resolved_config, input_strings, output_paths, lang)

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
        prompt_file=setup_files["prompt"],
        verification_program=setup_files["verifier"],
        strength=DEFAULT_STRENGTH,
        temperature=DEFAULT_TEMPERATURE,
        max_attempts=3,
        budget=5.0,
        verification_log_file=output_results_path,
        verbose=False,
        program_args=[],
        llm_time=DEFAULT_TIME,
        agentic_fallback=True
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
    output_code_path = mock_construct_paths_response[2]["output_code"]
    output_program_path = mock_construct_paths_response[2]["output_program"]

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
    mock_fix_loop.assert_called_once_with(
        program_file=setup_files["program"],
        code_file=setup_files["code"],
        prompt='Original prompt content',
        prompt_file=setup_files["prompt"],
        verification_program=setup_files["verifier"],
        strength=DEFAULT_STRENGTH,
        temperature=DEFAULT_TEMPERATURE,
        max_attempts=5,
        budget=5.0,
        verification_log_file=mock_construct_paths_response[2]["output_results"],
        verbose=False,
        program_args=[],
        llm_time=DEFAULT_TIME,
        agentic_fallback=True
    )
    assert mock_fix_loop.call_args[1]['max_attempts'] == 5
    mock_fix_errors.assert_not_called()
    mock_run_prog.assert_not_called()

    assert result == (False, 'Last program loop', 'Last code loop', 5, 0.8, 'model-e')
    # Files should now be written even on failure to allow inspection
    assert os.path.exists(output_code_path)
    assert open(output_code_path).read() == 'Last code loop'
    assert os.path.exists(output_program_path)
    assert open(output_program_path).read() == 'Last program loop'


@patch('pdd.fix_verification_main.fix_verification_errors_loop')
@patch('pdd.fix_verification_main.fix_verification_errors')
@patch('pdd.fix_verification_main.run_program')
@patch('pdd.fix_verification_main.construct_paths')
def test_output_files_written_when_fixes_applied(
    mock_construct, mock_run_prog, mock_fix_errors, mock_fix_loop,
    mock_context, setup_files, mock_construct_paths_response, tmp_path
):
    """Verify output files are written when verification finds issues and applies fixes."""
    mock_construct.return_value = mock_construct_paths_response
    mock_run_prog.return_value = (True, "Program output with issues", "")
    mock_fix_errors.return_value = {
        'verification_issues_count': 2,  # Has issues but fixes were applied
        'fixed_program': 'Partially fixed program content',
        'fixed_code': 'Partially fixed code content',
        'total_cost': 0.25,
        'model_name': 'model-partial',
        'explanation': '<verification_details>Found issues</verification_details>\n<fix_explanation>Applied fixes</fix_explanation>'
    }

    output_code_path = mock_construct_paths_response[2]["output_code"]
    output_results_path = mock_construct_paths_response[2]["output_results"]
    output_program_path = mock_construct_paths_response[2]["output_program"]

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

    # Should return True for success since fixes were applied (current logic considers fixes as success)
    assert result == (True, 'Partially fixed program content', 'Partially fixed code content', 1, 0.25, 'model-partial')
    
    # NEW BEHAVIOR: Files are always written when specified, allowing inspection
    assert os.path.exists(output_code_path)
    assert open(output_code_path).read() == 'Partially fixed code content'
    assert os.path.exists(output_program_path)
    assert open(output_program_path).read() == 'Partially fixed program content'
    assert os.path.exists(output_results_path)
    assert "Success: True" in open(output_results_path).read()
    assert "Issues Found Count: 2" in open(output_results_path).read()


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
    """Verify error tuple is returned if construct_paths raises FileNotFoundError.

    Per the spec: For critical/unrecoverable errors, return an error tuple with
    success=False and an error message in the model_name field. This allows
    orchestrating code (such as `pdd sync`) to handle failures gracefully rather
    than terminating via sys.exit(1).
    """
    def construct_side_effect(*args, **kwargs):
        raise FileNotFoundError("mock_file.txt not found")
    mock_construct.side_effect = construct_side_effect

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

    # Should return error tuple: (success=False, program="", code="", attempts=0, cost=0.0, error_message)
    assert result[0] is False  # success = False
    assert result[1] == ""     # final_program = ""
    assert result[2] == ""     # final_code = ""
    assert result[3] == 0      # attempts = 0
    assert result[4] == 0.0    # total_cost = 0.0
    assert "Error:" in result[5]  # model_name field contains error message

    captured = capsys.readouterr()
    # Check that error message was printed
    assert "Failed during path construction" in captured.out
    assert 'force' in mock_construct.call_args[1]


@patch('builtins.open', new_callable=MagicMock) # Use MagicMock for more control
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
    mock_fix_errors.return_value = {
        'verification_issues_count': 0,
        'fixed_program': 'Original program content',
        'fixed_code': 'Original code content',
        'total_cost': 0.1, 'model_name': 'model-a', 'explanation': None
    }

    output_code_path = mock_construct_paths_response[2]["output_code"]
    output_results_path = mock_construct_paths_response[2]["output_results"]
    output_program_path = mock_construct_paths_response[2]["output_program"]

    # Define a simpler side_effect for mock_open_func
    def open_side_effect(filename_arg, mode_arg="r", *args, **kwargs):
        # nonlocal output_code_path # Not strictly needed due to closure
        # Convert Path objects to strings for comparison
        filename_str = str(filename_arg)
        if filename_str == output_code_path and "w" in mode_arg:
            raise IOError("Disk full simulation")

        # For other files, return a functional mock file handle
        mock_file_handle = MagicMock()
        mock_file_handle.write = MagicMock()
        # mock_file_handle.read = MagicMock(return_value="Simulated read content") # Only if reads are expected
        mock_file_handle.__enter__.return_value = mock_file_handle
        mock_file_handle.__exit__.return_value = None
        return mock_file_handle

    mock_open_func.side_effect = open_side_effect

    result = fix_verification_main(
        ctx=mock_context,
        prompt_file=setup_files["prompt"],
        code_file=setup_files["code"],
        program_file=setup_files["program"],
        output_results=None, # Will use default from construct_paths
        output_code=None,    # Will use default from construct_paths
        output_program=None, # Will use default from construct_paths
        loop=False,
        verification_program=None
    )

    assert result[0] is True # Overall success was true before write error
    
    # Corrected expected message to use OSError as type(IOError()).__name__ is 'OSError'
    expected_error_msg = f"[bold red]Error:[/bold red] Failed to write code file '{output_code_path}': OSError - Disk full simulation"
    mock_rich_print.assert_any_call(expected_error_msg)

    # fix_verification_main now uses Path objects for file operations
    from pathlib import Path
    mock_open_func.assert_any_call(Path(output_results_path), "w")
    mock_open_func.assert_any_call(Path(output_program_path), "w")


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
    mock_fix_errors.return_value = { 'verification_issues_count': 0, 'fixed_program': 'p', 'fixed_code': 'c', 'total_cost': 0, 'model_name': 'm', 'explanation': None }
    mock_fix_loop.return_value = { 'success': True, 'final_program': 'p', 'final_code': 'c', 'total_attempts': 1, 'total_cost': 0, 'model_name': 'm' }

    fix_verification_main(
        ctx=mock_context, prompt_file=setup_files["prompt"], code_file=setup_files["code"],
        program_file=setup_files["program"], output_results=None, output_code=None,
        output_program=None,
        loop=False, verification_program=None
    )
    mock_fix_errors.assert_called_once_with(
        program=ANY, prompt=ANY, code=ANY, output=ANY,
        strength=ANY, temperature=ANY, verbose=True, time=DEFAULT_TIME
    )

    mock_fix_errors.reset_mock() 
    mock_construct.reset_mock() 
    mock_run_prog.reset_mock() # Reset run_program as it's called in single pass

    fix_verification_main(
        ctx=mock_context, prompt_file=setup_files["prompt"], code_file=setup_files["code"],
        program_file=setup_files["program"], output_results=None, output_code=None,
        output_program=None,
        loop=True, verification_program=setup_files["verifier"]
    )
    mock_fix_loop.assert_called_once_with(
        program_file=ANY, code_file=ANY, prompt=ANY, verification_program=ANY,
        strength=ANY, temperature=ANY, max_attempts=ANY, budget=ANY,
        verification_log_file=ANY, verbose=True, program_args=ANY, llm_time=DEFAULT_TIME,
        prompt_file=ANY, agentic_fallback=True
    )


# -----------------------------------------------------------------------------
# Tests for Hybrid Cloud Mode (Bug Fix)
# -----------------------------------------------------------------------------

@pytest.fixture
def mock_context_cloud_enabled(tmp_path):
    """Creates a mock Click context with cloud enabled (local=False)."""
    ctx = MagicMock(spec=click.Context)
    ctx.obj = {
        'strength': DEFAULT_STRENGTH,
        'temperature': DEFAULT_TEMPERATURE,
        'time': DEFAULT_TIME,
        'force': False,
        'quiet': False,
        'verbose': False,
        'local': False,  # Cloud/hybrid mode enabled
    }
    ctx.params = {}
    return ctx


@patch('pdd.fix_verification_main.fix_verification_errors_loop')
@patch('pdd.fix_verification_main.fix_verification_errors')
@patch('pdd.fix_verification_main.run_program')
@patch('pdd.fix_verification_main.construct_paths')
def test_loop_mode_hybrid_cloud_enabled_by_default(
    mock_construct, mock_run_prog, mock_fix_errors, mock_fix_loop,
    mock_context_cloud_enabled, setup_files, mock_construct_paths_response, tmp_path
):
    """Verify loop mode passes use_cloud=True when local=False (hybrid mode enabled by default).

    This tests the bug fix where hybrid mode (local verification + cloud LLM calls)
    should be enabled by default when the user hasn't specified --local.
    """
    mock_construct.return_value = mock_construct_paths_response
    mock_fix_loop.return_value = {
        'success': True,
        'final_program': 'Final program',
        'final_code': 'Final code',
        'total_attempts': 2,
        'total_cost': 0.5,
        'model_name': 'cloud-model'
    }

    result = fix_verification_main(
        ctx=mock_context_cloud_enabled,
        prompt_file=setup_files["prompt"],
        code_file=setup_files["code"],
        program_file=setup_files["program"],
        output_results=None,
        output_code=None,
        output_program=None,
        loop=True,
        verification_program=setup_files["verifier"]
    )

    mock_fix_loop.assert_called_once()
    # Key assertion: use_cloud=True should be passed for hybrid mode
    assert mock_fix_loop.call_args[1].get('use_cloud') is True, \
        "use_cloud=True should be passed when local=False (hybrid mode)"
    assert result[0] is True


@patch('pdd.fix_verification_main.fix_verification_errors_loop')
@patch('pdd.fix_verification_main.fix_verification_errors')
@patch('pdd.fix_verification_main.run_program')
@patch('pdd.fix_verification_main.construct_paths')
def test_loop_mode_local_flag_disables_cloud(
    mock_construct, mock_run_prog, mock_fix_errors, mock_fix_loop,
    mock_context, setup_files, mock_construct_paths_response, tmp_path
):
    """Verify loop mode does NOT pass use_cloud when local=True.

    When the user specifies --local, all execution should stay local,
    including LLM calls in the verification loop.
    """
    # mock_context already has local=True
    mock_construct.return_value = mock_construct_paths_response
    mock_fix_loop.return_value = {
        'success': True,
        'final_program': 'Final program',
        'final_code': 'Final code',
        'total_attempts': 1,
        'total_cost': 0.3,
        'model_name': 'local-model'
    }

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

    mock_fix_loop.assert_called_once()
    # Key assertion: use_cloud should NOT be in kwargs when local=True
    assert 'use_cloud' not in mock_fix_loop.call_args[1], \
        "use_cloud should not be passed when local=True"
    assert result[0] is True


@patch.dict(os.environ, {'PDD_CLOUD_ONLY': '1'})
@patch('pdd.fix_verification_main.fix_verification_errors_loop')
@patch('pdd.fix_verification_main.fix_verification_errors')
@patch('pdd.fix_verification_main.run_program')
@patch('pdd.fix_verification_main.construct_paths')
def test_loop_mode_cloud_only_env_enables_cloud(
    mock_construct, mock_run_prog, mock_fix_errors, mock_fix_loop,
    mock_context_cloud_enabled, setup_files, mock_construct_paths_response, tmp_path
):
    """Verify loop mode passes use_cloud=True when PDD_CLOUD_ONLY=1.

    When PDD_CLOUD_ONLY is set, hybrid mode should be enabled for the loop.
    """
    mock_construct.return_value = mock_construct_paths_response
    mock_fix_loop.return_value = {
        'success': True,
        'final_program': 'Final program',
        'final_code': 'Final code',
        'total_attempts': 1,
        'total_cost': 0.4,
        'model_name': 'cloud-model'
    }

    result = fix_verification_main(
        ctx=mock_context_cloud_enabled,
        prompt_file=setup_files["prompt"],
        code_file=setup_files["code"],
        program_file=setup_files["program"],
        output_results=None,
        output_code=None,
        output_program=None,
        loop=True,
        verification_program=setup_files["verifier"]
    )

    mock_fix_loop.assert_called_once()
    # Key assertion: use_cloud=True should be passed when PDD_CLOUD_ONLY=1
    assert mock_fix_loop.call_args[1].get('use_cloud') is True, \
        "use_cloud=True should be passed when PDD_CLOUD_ONLY=1"
    assert result[0] is True


@patch.dict(os.environ, {'PDD_CLOUD_ONLY': '1'})
@patch('pdd.fix_verification_main.fix_verification_errors_loop')
@patch('pdd.fix_verification_main.fix_verification_errors')
@patch('pdd.fix_verification_main.run_program')
@patch('pdd.fix_verification_main.construct_paths')
def test_loop_mode_local_flag_overrides_cloud_only(
    mock_construct, mock_run_prog, mock_fix_errors, mock_fix_loop,
    mock_context, setup_files, mock_construct_paths_response, tmp_path
):
    """Verify --local flag takes priority over PDD_CLOUD_ONLY env var.

    When user specifies --local, it should override the cloud-only env var.
    """
    # mock_context has local=True
    mock_construct.return_value = mock_construct_paths_response
    mock_fix_loop.return_value = {
        'success': True,
        'final_program': 'Final program',
        'final_code': 'Final code',
        'total_attempts': 1,
        'total_cost': 0.2,
        'model_name': 'local-model'
    }

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

    mock_fix_loop.assert_called_once()
    # Key assertion: local=True should override PDD_CLOUD_ONLY
    assert 'use_cloud' not in mock_fix_loop.call_args[1], \
        "local=True should override PDD_CLOUD_ONLY env var"
    assert result[0] is True


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
    mock_context.obj['force'] = True 

    mock_construct.return_value = mock_construct_paths_response
    mock_fix_loop.return_value = { 
        'success': True,
        'final_program': 'Fixed program',
        'final_code': 'Fixed code',
        'total_attempts': 1,
        'total_cost': 0.3,
        'model_name': 'model-loop'
    }
    mock_fix_errors.return_value = { 
        'verification_issues_count': 0,
        'fixed_program': 'Fixed program',
        'fixed_code': 'Fixed code',
        'total_cost': 0.3,
        'model_name': 'model-single',
        'explanation': None
    }
    mock_run_prog.return_value = (True, "Program output", "")


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
    mock_construct.assert_called_once()
    # Accessing call_args directly can be (call_args, call_kwargs) or just call_args if no kwargs
    # call_args[1] is safer for kwargs
    assert mock_construct.call_args[1].get('force') is True, "construct_paths should have been called with force=True in single pass"
    mock_fix_errors.assert_called_once_with(
        program=mock_construct_paths_response[1]["program_file"],
        prompt=mock_construct_paths_response[1]["prompt_file"],
        code=mock_construct_paths_response[1]["code_file"],
        output="Program output",
        strength=DEFAULT_STRENGTH,
        temperature=DEFAULT_TEMPERATURE,
        verbose=False, # mock_context.obj['verbose'] is False here
        time=DEFAULT_TIME
    )
    mock_fix_loop.assert_not_called()

    mock_construct.reset_mock()
    mock_fix_errors.reset_mock()
    mock_run_prog.reset_mock() 

    fix_verification_main(
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
    assert mock_construct.call_args[1].get('force') is True, "construct_paths should have been called with force=True in loop mode"

    mock_run_prog.assert_not_called() 
    mock_fix_errors.assert_not_called() 
    mock_fix_loop.assert_called_once_with(
        program_file=setup_files["program"],
        code_file=setup_files["code"],
        prompt=mock_construct_paths_response[1]["prompt_file"],
        prompt_file=setup_files["prompt"],
        verification_program=setup_files["verifier"],
        strength=DEFAULT_STRENGTH,
        temperature=DEFAULT_TEMPERATURE,
        max_attempts=DEFAULT_MAX_ATTEMPTS,
        budget=DEFAULT_BUDGET,
        verification_log_file=mock_construct_paths_response[2]["output_results"],
        verbose=False, # mock_context.obj['verbose'] is False here
        program_args=[],
        llm_time=DEFAULT_TIME,
        agentic_fallback=True
    )
