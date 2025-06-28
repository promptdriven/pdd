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
@pytest.fixture(autouse=True) # Use autouse to ensure cleanup runs for all tests
def test_files(tmp_path):
    # Create test files in output directory
    output_dir = Path("output")
    output_dir.mkdir(exist_ok=True)
    delete_output_files() # Clean up before creating files

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
    
    yield { # Yield instead of return for fixture cleanup
        "prompt_file": str(prompt_file),
        "code_file": str(code_file),
        "program_file": str(program_file),
        "error_file": str(error_file)
    }

    # Cleanup after test
    delete_output_files()

# Fixture for Click context
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
        'verbose': False # Ensure default verbose is False unless overridden
    }
    return context

def test_basic_crash_fix(ctx, test_files):
    """Test basic crash fix without loop option"""
    output_code = "output/fixed_code.py"
    output_program = "output/fixed_program.py"
        # Delete specific output files for this test (redundant due to autouse fixture, but safe)
    if os.path.exists(output_code):
        os.remove(output_code)
    if os.path.exists(output_program):
        os.remove(output_program)

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
    output_code = "output/fixed_code_loop.py"
    output_program = "output/fixed_program_loop.py"
    
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
    """Test crash fix without specifying output paths"""
    # Ensure default output files do not exist before the test
    # The default basename will be 'test_prompt' from the prompt file
    default_output_code = "output/test_prompt_fixed.py"
    default_output_program = "output/test_prompt_program_fixed.py"
    if os.path.exists(default_output_code):
        os.remove(default_output_code)
    if os.path.exists(default_output_program):
        os.remove(default_output_program)

    # FIX: Set force=True to prevent interactive prompts in tests
    ctx.params['force'] = True
    ctx.obj['force'] = True

    success, final_code, final_program, attempts, cost, model = crash_main(
        ctx=ctx,
        prompt_file=test_files["prompt_file"],
        code_file=test_files["code_file"],
        program_file=test_files["program_file"],
        error_file=test_files["error_file"]
        # No output paths specified, force=True now set in ctx
    )
    
    assert success is True
    assert isinstance(final_code, str)
    assert isinstance(final_program, str)
    assert attempts == 1
    assert isinstance(cost, float)
    assert isinstance(model, str)
    # Check if default files were created in the root directory
    assert os.path.exists(default_output_code)
    assert os.path.exists(default_output_program)

def test_crash_fix_with_invalid_files(ctx):
    """Test crash fix with invalid input files"""
    with pytest.raises(SystemExit): # Expect SystemExit due to internal error handling
         with pytest.raises(FileNotFoundError): # Check for underlying FileNotFoundError
             crash_main(
                 ctx=ctx,
                 prompt_file="nonexistent_prompt.txt",
                 code_file="nonexistent_code.py",
                 program_file="nonexistent_program.py",
                 error_file="nonexistent_error.log"
             )

def test_crash_fix_with_verbose_output(ctx, test_files):
    """Test crash fix with verbose output enabled"""
    ctx.params['verbose'] = True
    ctx.obj['verbose'] = True # Also set in obj for consistency if accessed there

    # Ensure default output files do not exist before the test
    default_output_code = "test_fixed.py"
    default_output_program = "test_program_fixed.py"
    if os.path.exists(default_output_code):
        os.remove(default_output_code)
    if os.path.exists(default_output_program):
        os.remove(default_output_program)

    # FIX: Set force=True to prevent interactive prompts in tests
    ctx.params['force'] = True
    ctx.obj['force'] = True

    success, final_code, final_program, attempts, cost, model = crash_main(
        ctx=ctx,
        prompt_file=test_files["prompt_file"],
        code_file=test_files["code_file"],
        program_file=test_files["program_file"],
        error_file=test_files["error_file"]
        # No output paths specified, force=True now set
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
    default_output_code = "test_fixed.py"
    default_output_program = "test_program_fixed.py"
    if os.path.exists(default_output_code):
        os.remove(default_output_code)
    if os.path.exists(default_output_program):
        os.remove(default_output_program)

    # FIX: Set force=True to prevent interactive prompts in tests
    ctx.params['force'] = True
    ctx.obj['force'] = True

    success, final_code, final_program, attempts, cost, model = crash_main(
        ctx=ctx,
        prompt_file=test_files["prompt_file"],
        code_file=test_files["code_file"],
        program_file=test_files["program_file"],
        error_file=test_files["error_file"]
        # No output paths specified, force=True now set
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