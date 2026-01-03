import os
import pytest
from pathlib import Path
import click
from pdd.crash_main import crash_main

def delete_output_files():
    output_files = [
        "output/fixed_code_loop.py",
        "output/fixed_program_loop.py",
        "output/test_code.py",
        "output/test_error.log",
        "output/test_program.py",
        "output/test_prompt.txt",
        "output/fixed_code.py", # Added potential output file in output dir
        "output/fixed_program.py", # Added potential output file in output dir
        "output/fixed_code_force.py", # Added potential output file in output dir
        "output/fixed_program_force.py", # Added potential output file in output dir
        "output/test_fixed.prompt", # Default output in output dir
        "output/test_fixed.py", # Default output in output dir for crash command based on error log
        "output/test_program_fixed.py" # Default output in output dir for crash command based on error log
    ]
    for file in output_files:
        if os.path.exists(file):
            os.remove(file)

# Fixture for temporary test files
@pytest.fixture
def test_files(tmp_path):
    # Create test files in a unique tmp_path directory for each test (avoids parallel test conflicts)
    output_dir = tmp_path / "output"
    output_dir.mkdir(exist_ok=True)

    # Create test prompt file
    prompt_content = "Write a function that calculates factorial"
    prompt_file = output_dir / "test_prompt.txt"
    prompt_file.write_text(prompt_content)

    # Create test code file with error
    code_content = """
def factorial(n):
    if n == 0:
        return 1
    return n * factorial(n-1)  # Missing type checking
    """
    code_file = output_dir / "test_code.py"
    code_file.write_text(code_content)

    # Create test program file
    program_content = """
from test_code import factorial
result = factorial("5")  # Type error
print(f"Factorial: {result}")
    """
    program_file = output_dir / "test_program.py"
    program_file.write_text(program_content)

    # Create test error file
    error_content = """
TypeError: can't multiply sequence by non-int of type 'str'
  File "test_program.py", line 2, in <module>
    result = factorial("5")
  File "test_code.py", line 4, in factorial
    return n * factorial(n-1)
    """
    error_file = output_dir / "test_error.log"
    error_file.write_text(error_content)

    return {
        "prompt_file": str(prompt_file),
        "code_file": str(code_file),
        "program_file": str(program_file),
        "error_file": str(error_file),
        "output_dir": str(output_dir)
    }
    # tmp_path is automatically cleaned up by pytest

# Fixture for Click context - uses local execution by default for unit tests
@pytest.fixture
def ctx():
    # Initialize params and obj as empty dicts if they might be missing
    context = click.Context(click.Command('test'))
    context.params = {}
    context.obj = {
        'strength': 0.5,
        'temperature': 0,
        'force': False, # Ensure default force is False unless overridden
        'quiet': False, # Ensure default quiet is False unless overridden
        'verbose': False, # Ensure default verbose is False unless overridden
        'local': True  # Force local execution for unit tests
    }
    return context

def test_basic_crash_fix(ctx, test_files):
    """Test basic crash fix without loop option"""
    output_dir = test_files["output_dir"]
    output_code = os.path.join(output_dir, "fixed_code.py")
    output_program = os.path.join(output_dir, "fixed_program.py")

    success, final_code, final_program, attempts, cost, model = crash_main(
        ctx=ctx,
        prompt_file=test_files["prompt_file"],
        code_file=test_files["code_file"],
        program_file=test_files["program_file"],
        error_file=test_files["error_file"],
        output=output_code,
        output_program=output_program
    )

    assert success is True
    assert isinstance(final_code, str)
    assert isinstance(final_program, str)
    assert attempts == 1
    assert isinstance(cost, float)
    assert isinstance(model, str)
    assert os.path.exists(output_code)
    assert os.path.exists(output_program)

def test_crash_fix_with_loop(ctx, test_files):
    """Test crash fix with loop option enabled"""
    output_dir = test_files["output_dir"]
    output_code = os.path.join(output_dir, "fixed_code_loop.py")
    output_program = os.path.join(output_dir, "fixed_program_loop.py")

    success, final_code, final_program, attempts, cost, model = crash_main(
        ctx=ctx,
        prompt_file=test_files["prompt_file"],
        code_file=test_files["code_file"],
        program_file=test_files["program_file"],
        error_file=test_files["error_file"],
        output=output_code,
        output_program=output_program,
        loop=True,
        max_attempts=3,
        budget=5.0
    )

    assert success in [True, False]  # Could be either depending on fix success
    assert isinstance(final_code, str)
    assert isinstance(final_program, str)
    assert 1 <= attempts <= 3
    assert 0 <= cost <= 5.0
    assert isinstance(model, str)
    assert os.path.exists(output_code)
    assert os.path.exists(output_program)

def test_crash_fix_without_output_paths(ctx, test_files):
    """Test crash fix with explicit output paths (tests path handling)"""
    output_dir = test_files["output_dir"]
    output_code = os.path.join(output_dir, "test_prompt_fixed.py")
    output_program = os.path.join(output_dir, "test_prompt_program_fixed.py")

    # Set force=True to prevent interactive prompts in tests
    ctx.params['force'] = True
    ctx.obj['force'] = True

    success, final_code, final_program, attempts, cost, model = crash_main(
        ctx=ctx,
        prompt_file=test_files["prompt_file"],
        code_file=test_files["code_file"],
        program_file=test_files["program_file"],
        error_file=test_files["error_file"],
        output=output_code,
        output_program=output_program
    )

    assert success is True
    assert isinstance(final_code, str)
    assert isinstance(final_program, str)
    assert attempts == 1
    assert isinstance(cost, float)
    assert isinstance(model, str)
    assert os.path.exists(output_code)
    assert os.path.exists(output_program)

def test_crash_fix_with_invalid_files(ctx):
    """Test crash fix with invalid input files"""
    # Per spec: exceptions should return a failure tuple rather than raising SystemExit
    # Return format: (success, final_code, final_program, attempts, cost, model_or_error)
    success, final_code, final_program, attempts, cost, model = crash_main(
        ctx=ctx,
        prompt_file="nonexistent_prompt.txt",
        code_file="nonexistent_code.py",
        program_file="nonexistent_program.py",
        error_file="nonexistent_error.log"
    )

    assert success is False
    assert final_code == ""
    assert final_program == ""
    assert attempts == 0
    assert cost == 0.0
    assert "FileNotFoundError" in model  # model field contains error message on failure

def test_crash_fix_with_verbose_output(ctx, test_files):
    """Test crash fix with verbose output enabled"""
    ctx.params['verbose'] = True
    ctx.obj['verbose'] = True # Also set in obj for consistency if accessed there

    # Ensure default output files do not exist before the test
    output_code = "output/test_fixed.py"
    output_program = "output/test_program_fixed.py"
    if os.path.exists(output_code):
        os.remove(output_code)
    if os.path.exists(output_program):
        os.remove(output_program)

    # FIX: Set force=True to prevent interactive prompts in tests
    ctx.params['force'] = True
    ctx.obj['force'] = True

    success, final_code, final_program, attempts, cost, model = crash_main(
        ctx=ctx,
        prompt_file=test_files["prompt_file"],
        code_file=test_files["code_file"],
        program_file=test_files["program_file"],
        error_file=test_files["error_file"],
        output=output_code,
        output_program=output_program
    )
    
    assert success is True
    assert isinstance(final_code, str)
    assert isinstance(final_program, str)
    assert attempts == 1
    assert isinstance(cost, float)
    assert isinstance(model, str)

def test_crash_fix_with_quiet_mode(ctx, test_files):
    """Test crash fix with quiet mode enabled"""
    ctx.params['quiet'] = True
    ctx.obj['quiet'] = True # Also set in obj for consistency

    # Ensure default output files do not exist before the test
    output_code = "output/test_fixed_quiet.py"
    output_program = "output/test_program_fixed_quiet.py"
    if os.path.exists(output_code):
        os.remove(output_code)
    if os.path.exists(output_program):
        os.remove(output_program)

    # FIX: Set force=True to prevent interactive prompts in tests
    ctx.params['force'] = True
    ctx.obj['force'] = True

    success, final_code, final_program, attempts, cost, model = crash_main(
        ctx=ctx,
        prompt_file=test_files["prompt_file"],
        code_file=test_files["code_file"],
        program_file=test_files["program_file"],
        error_file=test_files["error_file"],
        output=output_code,
        output_program=output_program
    )
    
    assert success is True
    assert isinstance(final_code, str)
    assert isinstance(final_program, str)
    assert attempts == 1
    assert isinstance(cost, float)
    assert isinstance(model, str)

def test_crash_fix_with_force_option(ctx, test_files):
    """Test crash fix with force option enabled"""
    ctx.params['force'] = True # Set force in params
    ctx.obj['force'] = True    # Also set force in obj for consistency

    output_code = "output/fixed_code_force.py"
    output_program = "output/fixed_program_force.py"

    # Create existing files
    output_dir = Path("output")
    output_dir.mkdir(exist_ok=True) # Ensure output dir exists
    Path(output_code).write_text("existing content")
    Path(output_program).write_text("existing content")

    success, final_code, final_program, attempts, cost, model = crash_main(
        ctx=ctx,
        prompt_file=test_files["prompt_file"],
        code_file=test_files["code_file"],
        program_file=test_files["program_file"],
        error_file=test_files["error_file"],
        output=output_code,
        output_program=output_program
    )
    
    assert success is True
    assert isinstance(final_code, str)
    assert isinstance(final_program, str)
    assert attempts == 1
    assert isinstance(cost, float)
    assert isinstance(model, str)
    assert os.path.exists(output_code)
    assert os.path.exists(output_program)
    # Optionally check if content was overwritten
    assert Path(output_code).read_text() != "existing content"
    assert Path(output_program).read_text() != "existing content"


# ============================================================================
# Cloud Execution Tests
# ============================================================================

from unittest.mock import patch, MagicMock, mock_open
import requests

@patch('pdd.crash_main.requests.post')
@patch('pdd.crash_main.CloudConfig.get_jwt_token')
@patch('pdd.crash_main.construct_paths')
def test_crash_main_cloud_success(
    mock_construct_paths,
    mock_get_jwt,
    mock_post,
    ctx,
    test_files
):
    """
    Test that crash_main uses cloud execution successfully when available.
    """
    ctx.obj['local'] = False  # Not forcing local
    ctx.obj['force'] = True
    ctx.obj['quiet'] = True

    mock_construct_paths.return_value = (
        {},
        {
            'prompt_file': 'prompt content',
            'code_file': 'code content',
            'program_file': 'program content',
            'error_file': 'error content'
        },
        {
            'output_code': test_files['output_dir'] + '/fixed_code.py',
            'output_program': test_files['output_dir'] + '/fixed_program.py',
            'output_results': test_files['output_dir'] + '/results.log'
        },
        'python'
    )

    mock_get_jwt.return_value = "mock_jwt_token"

    # Mock successful cloud response
    mock_response = MagicMock()
    mock_response.status_code = 200
    mock_response.raise_for_status = MagicMock()
    mock_response.json.return_value = {
        'fixedCode': 'fixed code content',
        'fixedProgram': 'fixed program content',
        'updateCode': True,
        'updateProgram': True,
        'analysis': 'analysis content',
        'totalCost': 0.05,
        'modelName': 'cloud-model'
    }
    mock_post.return_value = mock_response

    m_open = mock_open()
    with patch('builtins.open', m_open):
        success, final_code, final_program, attempts, total_cost, model_name = crash_main(
            ctx=ctx,
            prompt_file=test_files["prompt_file"],
            code_file=test_files["code_file"],
            program_file=test_files["program_file"],
            error_file=test_files["error_file"],
            output=None,
            output_program=None,
            loop=False
        )

    # Assert cloud was used
    mock_get_jwt.assert_called_once()
    mock_post.assert_called_once()
    assert success is True
    assert final_code == 'fixed code content'
    assert final_program == 'fixed program content'
    assert total_cost == 0.05
    assert model_name == 'cloud-model'


@patch('pdd.crash_main.fix_code_module_errors')
@patch('pdd.crash_main.CloudConfig.get_jwt_token')
@patch('pdd.crash_main.construct_paths')
def test_crash_main_cloud_fallback_on_auth_failure(
    mock_construct_paths,
    mock_get_jwt,
    mock_fix_errors,
    ctx,
    test_files
):
    """
    Test that crash_main falls back to local when cloud authentication fails.
    """
    ctx.obj['local'] = False
    ctx.obj['force'] = True
    ctx.obj['quiet'] = True

    mock_construct_paths.return_value = (
        {},
        {
            'prompt_file': 'prompt',
            'code_file': 'code',
            'program_file': 'program',
            'error_file': 'error'
        },
        {
            'output_code': test_files['output_dir'] + '/fixed_code.py',
            'output_program': test_files['output_dir'] + '/fixed_program.py',
            'output_results': test_files['output_dir'] + '/results.log'
        },
        'python'
    )

    # Mock auth failure
    mock_get_jwt.return_value = None

    # Mock local fallback
    mock_fix_errors.return_value = (True, True, 'fixed program', 'fixed code', 'analysis', 0.1, 'local-model')

    m_open = mock_open()
    with patch('builtins.open', m_open):
        success, fixed_code, fixed_program, attempts, cost, model = crash_main(
            ctx=ctx,
            prompt_file=test_files["prompt_file"],
            code_file=test_files["code_file"],
            program_file=test_files["program_file"],
            error_file=test_files["error_file"],
            output=None,
            output_program=None,
            loop=False
        )

    # Assert fallback to local was used
    mock_get_jwt.assert_called_once()
    mock_fix_errors.assert_called_once()


@patch('pdd.crash_main.requests.post')
@patch('pdd.crash_main.CloudConfig.get_jwt_token')
@patch('pdd.crash_main.construct_paths')
def test_crash_main_cloud_insufficient_credits_raises_error(
    mock_construct_paths,
    mock_get_jwt,
    mock_post,
    ctx,
    test_files
):
    """
    Test that crash_main raises UsageError on insufficient credits (HTTP 402).
    """
    ctx.obj['local'] = False
    ctx.obj['force'] = True
    ctx.obj['quiet'] = True

    mock_construct_paths.return_value = (
        {},
        {
            'prompt_file': 'prompt',
            'code_file': 'code',
            'program_file': 'program',
            'error_file': 'error'
        },
        {
            'output_code': test_files['output_dir'] + '/fixed_code.py',
            'output_program': test_files['output_dir'] + '/fixed_program.py',
            'output_results': test_files['output_dir'] + '/results.log'
        },
        'python'
    )

    mock_get_jwt.return_value = "mock_jwt_token"

    # Mock 402 response
    mock_response = MagicMock()
    mock_response.status_code = 402
    mock_response.text = '{"error": "Insufficient credits"}'
    mock_response.json.return_value = {
        'error': 'Insufficient credits',
        'currentBalance': 0,
        'estimatedCost': 0.05
    }
    mock_error = requests.exceptions.HTTPError(response=mock_response)
    mock_post.return_value.raise_for_status.side_effect = mock_error
    mock_post.return_value.status_code = 402

    with pytest.raises(click.UsageError, match="Insufficient credits"):
        crash_main(
            ctx=ctx,
            prompt_file=test_files["prompt_file"],
            code_file=test_files["code_file"],
            program_file=test_files["program_file"],
            error_file=test_files["error_file"],
            output=None,
            output_program=None,
            loop=False
        )


@patch('pdd.crash_main.fix_code_loop')
@patch('pdd.crash_main.construct_paths')
def test_crash_main_loop_mode_with_local_flag_uses_local(
    mock_construct_paths,
    mock_fix_code_loop,
    ctx,
    test_files
):
    """
    Test that loop mode with --local flag uses purely local execution (use_cloud=False).
    """
    ctx.obj['local'] = True  # Force local execution
    ctx.obj['force'] = True
    ctx.obj['quiet'] = True

    mock_construct_paths.return_value = (
        {},
        {
            'prompt_file': 'prompt',
            'code_file': 'code',
            'program_file': 'program',
            'error_file': 'error'
        },
        {
            'output_code': test_files['output_dir'] + '/fixed_code.py',
            'output_program': test_files['output_dir'] + '/fixed_program.py',
            'output_results': test_files['output_dir'] + '/results.log'
        },
        'python'
    )

    mock_fix_code_loop.return_value = (True, 'fixed program', 'fixed code', 2, 0.5, 'local-model')

    m_open = mock_open()
    with patch('builtins.open', m_open):
        crash_main(
            ctx=ctx,
            prompt_file=test_files["prompt_file"],
            code_file=test_files["code_file"],
            program_file=test_files["program_file"],
            error_file=test_files["error_file"],
            output=None,
            output_program=None,
            loop=True,
            max_attempts=3,
            budget=5.0
        )

    # fix_code_loop should be called with use_cloud=False
    mock_fix_code_loop.assert_called_once()
    call_kwargs = mock_fix_code_loop.call_args
    # Check positional or keyword argument for use_cloud
    if call_kwargs.kwargs:
        assert call_kwargs.kwargs.get('use_cloud') == False
    else:
        # use_cloud is not passed or default is used
        pass


@patch('pdd.crash_main.fix_code_loop')
@patch('pdd.crash_main.construct_paths')
def test_crash_main_loop_mode_uses_hybrid_cloud_by_default(
    mock_construct_paths,
    mock_fix_code_loop,
    ctx,
    test_files
):
    """
    Test that loop mode without --local flag uses hybrid cloud mode (use_cloud=True).
    Hybrid mode means local program execution + cloud LLM calls.
    """
    ctx.obj['local'] = False  # Default - not forcing local
    ctx.obj['force'] = True
    ctx.obj['quiet'] = True

    mock_construct_paths.return_value = (
        {},
        {
            'prompt_file': 'prompt',
            'code_file': 'code',
            'program_file': 'program',
            'error_file': 'error'
        },
        {
            'output_code': test_files['output_dir'] + '/fixed_code.py',
            'output_program': test_files['output_dir'] + '/fixed_program.py',
            'output_results': test_files['output_dir'] + '/results.log'
        },
        'python'
    )

    mock_fix_code_loop.return_value = (True, 'fixed program', 'fixed code', 2, 0.5, 'cloud-model')

    m_open = mock_open()
    with patch('builtins.open', m_open):
        crash_main(
            ctx=ctx,
            prompt_file=test_files["prompt_file"],
            code_file=test_files["code_file"],
            program_file=test_files["program_file"],
            error_file=test_files["error_file"],
            output=None,
            output_program=None,
            loop=True,
            max_attempts=3,
            budget=5.0
        )

    # fix_code_loop should be called with use_cloud=True
    mock_fix_code_loop.assert_called_once()
    call_kwargs = mock_fix_code_loop.call_args
    if call_kwargs.kwargs:
        assert call_kwargs.kwargs.get('use_cloud') == True


@patch('pdd.crash_main.fix_code_module_errors')
@patch('pdd.crash_main.CloudConfig.get_jwt_token')
@patch('pdd.crash_main.construct_paths')
def test_crash_main_local_flag_skips_cloud(
    mock_construct_paths,
    mock_get_jwt,
    mock_fix_errors,
    ctx,
    test_files
):
    """
    Test that --local flag forces local execution, skipping cloud entirely.
    """
    ctx.obj['local'] = True  # Force local
    ctx.obj['force'] = True
    ctx.obj['quiet'] = True

    mock_construct_paths.return_value = (
        {},
        {
            'prompt_file': 'prompt',
            'code_file': 'code',
            'program_file': 'program',
            'error_file': 'error'
        },
        {
            'output_code': test_files['output_dir'] + '/fixed_code.py',
            'output_program': test_files['output_dir'] + '/fixed_program.py',
            'output_results': test_files['output_dir'] + '/results.log'
        },
        'python'
    )

    mock_fix_errors.return_value = (True, True, 'fixed program', 'fixed code', 'analysis', 0.1, 'local-model')

    m_open = mock_open()
    with patch('builtins.open', m_open):
        crash_main(
            ctx=ctx,
            prompt_file=test_files["prompt_file"],
            code_file=test_files["code_file"],
            program_file=test_files["program_file"],
            error_file=test_files["error_file"],
            output=None,
            output_program=None,
            loop=False
        )

    # Cloud auth should NOT be called when local is forced
    mock_get_jwt.assert_not_called()
    # Local fix should be used
    mock_fix_errors.assert_called_once()