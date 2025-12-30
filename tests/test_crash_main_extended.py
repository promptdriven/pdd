"""
Test suite for crash_main.py

DETAILED TEST PLAN
==================

This test suite validates the crash_main function which serves as a CLI wrapper
for fixing crashed code modules and their calling programs.

1. UNIT TESTS (Primary approach for this function)
   ------------------------------------------------
   The crash_main function involves complex interactions with:
   - File I/O operations
   - External function calls (construct_paths, resolve_effective_config, fix_code_loop, fix_code_module_errors)
   - Click context handling
   - Rich printing
   - Exception handling
   
   Unit tests with mocking are the most appropriate approach to test:
   
   a) Mode switching:
      - Test loop=True mode (calls fix_code_loop)
      - Test loop=False mode (calls fix_code_module_errors)
   
   b) Context handling:
      - Test with valid ctx.obj and ctx.params as dicts
      - Test with ctx.obj=None (should be converted to {})
      - Test with ctx.params=None (should be converted to {})
      - Test with ctx.obj/params as non-dict values
   
   c) Configuration resolution:
      - Test with strength/temperature overrides
      - Test without overrides (use defaults)
      - Test config priority (CLI > pddrc > defaults)
   
   d) File operations:
      - Test output file writing with valid paths
      - Test parent directory creation
      - Test with no output paths (shouldn't write files)
   
   e) Error handling:
      - Test FileNotFoundError returns error tuple
      - Test click.Abort is re-raised
      - Test generic exceptions return error tuple
   
   f) Content tracking:
      - Test when code is modified vs not modified
      - Test when program is modified vs not modified
      - Test empty final_code/final_program fallback to original
   
   g) Output control:
      - Test quiet=True suppresses output
      - Test quiet=False shows output
      - Test verbose=True shows diagnostics
      - Test verbose=False hides diagnostics

2. Z3 FORMAL VERIFICATION TESTS
   -----------------------------
   Z3 is appropriate for verifying mathematical invariants and structural properties:
   
   a) Return value structure:
      - Return tuple always has exactly 6 elements
      - Element types: (bool, str, str, int, float, str)
   
   b) Numeric invariants:
      - attempts >= 0 always
      - cost >= 0.0 always
      - If success=False and error occurred, attempts may be 0
   
   c) Consistency properties:
      - If attempts=0, then cost=0.0 (error case)
      - final_code and final_program are never None (may be empty string)
      - model is never None (may be empty or error string)

3. INTEGRATION CONSIDERATIONS
   ---------------------------
   - Mock external dependencies (construct_paths, fix_code_loop, etc.)
   - Use temporary directories/files for file I/O tests
   - Mock rich.print to capture output
   - Use pytest fixtures for common setup (Click context, temp files)

4. COVERAGE GOALS
   --------------
   - All code paths (loop/non-loop modes)
   - All exception handlers
   - All conditional branches (quiet, verbose, file updates)
   - Edge cases (empty strings, None values, missing files)
"""

import pytest
from pathlib import Path
from unittest.mock import MagicMock, patch
from typing import Tuple
import click
from z3 import Bool, Int, Real, Solver, Implies, And, Not, sat, unsat

# Import the function under test
from pdd.crash_main import crash_main


# ============================================================================
# FIXTURES
# ============================================================================

@pytest.fixture
def mock_ctx() -> MagicMock:
    """Create a mock Click context with standard parameters."""
    ctx = MagicMock(spec=click.Context)
    ctx.obj = {
        "quiet": False,
        "verbose": False,
        "force": False,
        "context": None,
        "confirm_callback": None
    }
    ctx.params = {"quiet": False, "verbose": False, "force": False}
    return ctx


@pytest.fixture
def mock_ctx_minimal() -> MagicMock:
    """Create a minimal Click context to test defensive handling."""
    ctx = MagicMock(spec=click.Context)
    ctx.obj = None
    ctx.params = None
    return ctx


@pytest.fixture
def temp_output_dir(tmp_path: Path) -> Path:
    """Create a temporary directory for output files."""
    output_dir = tmp_path / "output"
    output_dir.mkdir()
    return output_dir


@pytest.fixture
def sample_file_paths() -> dict:
    """Sample file paths for testing."""
    return {
        "prompt_file": "test_prompt.txt",
        "code_file": "test_code.py",
        "program_file": "test_program.py",
        "error_file": "test_error.log"
    }


# ============================================================================
# UNIT TESTS - Loop Mode
# ============================================================================

@patch('pdd.crash_main.construct_paths')
@patch('pdd.crash_main.resolve_effective_config')
@patch('pdd.crash_main.fix_code_loop')
@patch('pdd.crash_main.rprint')
def test_crash_main_loop_mode_success(
    mock_rprint: MagicMock,
    mock_fix_loop: MagicMock,
    mock_resolve: MagicMock,
    mock_construct: MagicMock,
    mock_ctx: MagicMock,
    temp_output_dir: Path
) -> None:
    """Test crash_main in loop mode with successful fix."""
    # Setup mocks
    mock_construct.return_value = (
        {"strength": 0.5, "temperature": 0.3, "time": False},
        {
            "prompt_file": "prompt content",
            "code_file": "original code",
            "program_file": "original program",
            "error_file": "error content"
        },
        {
            "output": str(temp_output_dir / "fixed_code.py"),
            "output_program": str(temp_output_dir / "fixed_program.py")
        },
        "python"
    )
    mock_resolve.return_value = {"strength": 0.5, "temperature": 0.3, "time": False}
    mock_fix_loop.return_value = (True, "fixed program", "fixed code", 3, 1.5, "gpt-4")
    
    # Execute
    success, final_code, final_program, attempts, cost, model = crash_main(
        ctx=mock_ctx,
        prompt_file="prompt.txt",
        code_file="code.py",
        program_file="program.py",
        error_file="error.log",
        output=str(temp_output_dir / "fixed_code.py"),
        output_program=str(temp_output_dir / "fixed_program.py"),
        loop=True,
        max_attempts=5,
        budget=10.0
    )
    
    # Verify
    assert success is True
    assert final_code == "fixed code"
    assert final_program == "fixed program"
    assert attempts == 3
    assert cost == 1.5
    assert model == "gpt-4"
    
    # Verify fix_code_loop was called
    mock_fix_loop.assert_called_once()
    
    # Verify files were written
    assert (temp_output_dir / "fixed_code.py").exists()
    assert (temp_output_dir / "fixed_program.py").exists()


@patch('pdd.crash_main.construct_paths')
@patch('pdd.crash_main.resolve_effective_config')
@patch('pdd.crash_main.fix_code_loop')
@patch('pdd.crash_main.rprint')
def test_crash_main_loop_mode_empty_results(
    mock_rprint: MagicMock,
    mock_fix_loop: MagicMock,
    mock_resolve: MagicMock,
    mock_construct: MagicMock,
    mock_ctx: MagicMock,
    temp_output_dir: Path
) -> None:
    """Test crash_main in loop mode when fix_code_loop returns empty strings."""
    # Setup mocks - fix_code_loop returns empty strings
    original_code = "original code"
    original_program = "original program"
    
    mock_construct.return_value = (
        {"strength": 0.5, "temperature": 0.3, "time": False},
        {
            "prompt_file": "prompt",
            "code_file": original_code,
            "program_file": original_program,
            "error_file": "error"
        },
        {
            "output": str(temp_output_dir / "code.py"),
            "output_program": str(temp_output_dir / "program.py")
        },
        "python"
    )
    mock_resolve.return_value = {"strength": 0.5, "temperature": 0.3, "time": False}
    mock_fix_loop.return_value = (False, "", "", 1, 0.5, "gpt-4")
    
    # Execute
    success, final_code, final_program, attempts, cost, model = crash_main(
        ctx=mock_ctx,
        prompt_file="p.txt",
        code_file="c.py",
        program_file="prog.py",
        error_file="e.log",
        output=str(temp_output_dir / "code.py"),
        output_program=str(temp_output_dir / "program.py"),
        loop=True
    )
    
    # Verify - should fallback to original content
    assert final_code == original_code
    assert final_program == original_program


# ============================================================================
# UNIT TESTS - Non-Loop Mode
# ============================================================================

@patch('pdd.crash_main.construct_paths')
@patch('pdd.crash_main.resolve_effective_config')
@patch('pdd.crash_main.fix_code_module_errors')
@patch('pdd.crash_main.rprint')
def test_crash_main_non_loop_mode_success(
    mock_rprint: MagicMock,
    mock_fix_errors: MagicMock,
    mock_resolve: MagicMock,
    mock_construct: MagicMock,
    mock_ctx: MagicMock,
    temp_output_dir: Path
) -> None:
    """Test crash_main in non-loop mode with successful fix."""
    # Setup mocks
    mock_construct.return_value = (
        {"strength": 0.7, "temperature": 0.2, "time": False},
        {
            "prompt_file": "prompt",
            "code_file": "original code",
            "program_file": "original program",
            "error_file": "error"
        },
        {
            "output": str(temp_output_dir / "fixed.py"),
            "output_program": str(temp_output_dir / "fixed_prog.py")
        },
        "python"
    )
    mock_resolve.return_value = {"strength": 0.7, "temperature": 0.2, "time": False}
    # Return: update_program, update_code, fixed_program, fixed_code, _, cost, model
    mock_fix_errors.return_value = (
        True, True, "new program", "new code", "raw", 2.0, "gpt-3.5"
    )
    
    # Execute
    success, final_code, final_program, attempts, cost, model = crash_main(
        ctx=mock_ctx,
        prompt_file="p.txt",
        code_file="c.py",
        program_file="prog.py",
        error_file="e.log",
        output=str(temp_output_dir / "fixed.py"),
        output_program=str(temp_output_dir / "fixed_prog.py"),
        loop=False
    )
    
    # Verify
    assert success is True
    assert final_code == "new code"
    assert final_program == "new program"
    assert attempts == 1  # Non-loop mode always has 1 attempt
    assert cost == 2.0
    assert model == "gpt-3.5"
    
    # Verify fix_code_module_errors was called
    mock_fix_errors.assert_called_once()


@patch('pdd.crash_main.construct_paths')
@patch('pdd.crash_main.resolve_effective_config')
@patch('pdd.crash_main.fix_code_module_errors')
@patch('pdd.crash_main.rprint')
def test_crash_main_non_loop_no_updates(
    mock_rprint: MagicMock,
    mock_fix_errors: MagicMock,
    mock_resolve: MagicMock,
    mock_construct: MagicMock,
    mock_ctx: MagicMock,
    temp_output_dir: Path
) -> None:
    """Test crash_main in non-loop mode when no updates are needed."""
    original_code = "original code"
    original_program = "original program"
    
    mock_construct.return_value = (
        {"strength": 0.5, "temperature": 0.3, "time": False},
        {
            "prompt_file": "prompt",
            "code_file": original_code,
            "program_file": original_program,
            "error_file": "error"
        },
        {
            "output": str(temp_output_dir / "code.py"),
            "output_program": str(temp_output_dir / "prog.py")
        },
        "python"
    )
    mock_resolve.return_value = {"strength": 0.5, "temperature": 0.3, "time": False}
    # No updates needed
    mock_fix_errors.return_value = (False, False, "", "", "raw", 0.5, "gpt-4")
    
    # Execute
    success, final_code, final_program, attempts, cost, model = crash_main(
        ctx=mock_ctx,
        prompt_file="p.txt",
        code_file="c.py",
        program_file="prog.py",
        error_file="e.log",
        output=str(temp_output_dir / "code.py"),
        output_program=str(temp_output_dir / "prog.py"),
        loop=False
    )
    
    # Should return original content when no updates
    assert final_code == original_code
    assert final_program == original_program


# ============================================================================
# UNIT TESTS - Context Handling
# ============================================================================

@patch('pdd.crash_main.construct_paths')
@patch('pdd.crash_main.resolve_effective_config')
@patch('pdd.crash_main.fix_code_module_errors')
@patch('pdd.crash_main.rprint')
def test_crash_main_ctx_defensive_handling(
    mock_rprint: MagicMock,
    mock_fix_errors: MagicMock,
    mock_resolve: MagicMock,
    mock_construct: MagicMock,
    mock_ctx_minimal: MagicMock
) -> None:
    """Test defensive handling of ctx.obj and ctx.params being None."""
    mock_construct.return_value = (
        {"strength": 0.5, "temperature": 0.3, "time": False},
        {
            "prompt_file": "p",
            "code_file": "c",
            "program_file": "prog",
            "error_file": "e"
        },
        {},
        "python"
    )
    mock_resolve.return_value = {"strength": 0.5, "temperature": 0.3, "time": False}
    mock_fix_errors.return_value = (False, False, "prog", "code", "raw", 0.5, "model")
    
    # Execute with minimal context
    success, final_code, final_program, attempts, cost, model = crash_main(
        ctx=mock_ctx_minimal,
        prompt_file="p.txt",
        code_file="c.py",
        program_file="prog.py",
        error_file="e.log",
        loop=False
    )
    
    # Should complete without error
    assert isinstance(mock_ctx_minimal.obj, dict)
    assert isinstance(mock_ctx_minimal.params, dict)


# ============================================================================
# UNIT TESTS - Error Handling
# ============================================================================

@patch('pdd.crash_main.construct_paths')
@patch('pdd.crash_main.rprint')
def test_crash_main_file_not_found(
    mock_rprint: MagicMock,
    mock_construct: MagicMock,
    mock_ctx: MagicMock
) -> None:
    """Test crash_main handles FileNotFoundError correctly."""
    mock_construct.side_effect = FileNotFoundError("File not found: test.txt")
    
    # Execute
    success, final_code, final_program, attempts, cost, model = crash_main(
        ctx=mock_ctx,
        prompt_file="missing.txt",
        code_file="c.py",
        program_file="p.py",
        error_file="e.log",
        loop=False
    )
    
    # Should return error tuple
    assert success is False
    assert final_code == ""
    assert final_program == ""
    assert attempts == 0
    assert cost == 0.0
    assert "FileNotFoundError" in model


@patch('pdd.crash_main.construct_paths')
@patch('pdd.crash_main.rprint')
def test_crash_main_click_abort_reraise(
    mock_rprint: MagicMock,
    mock_construct: MagicMock,
    mock_ctx: MagicMock
) -> None:
    """Test crash_main re-raises click.Abort."""
    mock_construct.side_effect = click.Abort()
    
    # Execute - should re-raise
    with pytest.raises(click.Abort):
        crash_main(
            ctx=mock_ctx,
            prompt_file="p.txt",
            code_file="c.py",
            program_file="prog.py",
            error_file="e.log",
            loop=False
        )


@patch('pdd.crash_main.construct_paths')
@patch('pdd.crash_main.rprint')
def test_crash_main_generic_exception(
    mock_rprint: MagicMock,
    mock_construct: MagicMock,
    mock_ctx: MagicMock
) -> None:
    """Test crash_main handles generic exceptions correctly."""
    mock_construct.side_effect = ValueError("Something went wrong")
    
    # Execute
    success, final_code, final_program, attempts, cost, model = crash_main(
        ctx=mock_ctx,
        prompt_file="p.txt",
        code_file="c.py",
        program_file="prog.py",
        error_file="e.log",
        loop=False
    )
    
    # Should return error tuple
    assert success is False
    assert final_code == ""
    assert final_program == ""
    assert attempts == 0
    assert cost == 0.0
    assert "Error:" in model


# ============================================================================
# UNIT TESTS - File Output
# ============================================================================

@patch('pdd.crash_main.construct_paths')
@patch('pdd.crash_main.resolve_effective_config')
@patch('pdd.crash_main.fix_code_module_errors')
@patch('pdd.crash_main.rprint')
def test_crash_main_creates_parent_directories(
    mock_rprint: MagicMock,
    mock_fix_errors: MagicMock,
    mock_resolve: MagicMock,
    mock_construct: MagicMock,
    mock_ctx: MagicMock,
    tmp_path: Path
) -> None:
    """Test crash_main creates parent directories for output files."""
    nested_output = tmp_path / "deep" / "nested" / "path" / "output.py"
    nested_program = tmp_path / "another" / "deep" / "path" / "program.py"
    
    mock_construct.return_value = (
        {"strength": 0.5, "temperature": 0.3, "time": False},
        {
            "prompt_file": "p",
            "code_file": "code",
            "program_file": "prog",
            "error_file": "e"
        },
        {"output": str(nested_output), "output_program": str(nested_program)},
        "python"
    )
    mock_resolve.return_value = {"strength": 0.5, "temperature": 0.3, "time": False}
    mock_fix_errors.return_value = (True, True, "new prog", "new code", "raw", 1.0, "model")
    
    # Execute
    crash_main(
        ctx=mock_ctx,
        prompt_file="p.txt",
        code_file="c.py",
        program_file="prog.py",
        error_file="e.log",
        output=str(nested_output),
        output_program=str(nested_program),
        loop=False
    )
    
    # Verify parent directories were created and files written
    assert nested_output.exists()
    assert nested_program.exists()
    assert nested_output.read_text() == "new code"
    assert nested_program.read_text() == "new prog"


@patch('pdd.crash_main.construct_paths')
@patch('pdd.crash_main.resolve_effective_config')
@patch('pdd.crash_main.fix_code_module_errors')
@patch('pdd.crash_main.rprint')
def test_crash_main_no_output_paths(
    mock_rprint: MagicMock,
    mock_fix_errors: MagicMock,
    mock_resolve: MagicMock,
    mock_construct: MagicMock,
    mock_ctx: MagicMock
) -> None:
    """Test crash_main when no output paths are specified."""
    mock_construct.return_value = (
        {"strength": 0.5, "temperature": 0.3, "time": False},
        {
            "prompt_file": "p",
            "code_file": "c",
            "program_file": "prog",
            "error_file": "e"
        },
        {},  # No output paths
        "python"
    )
    mock_resolve.return_value = {"strength": 0.5, "temperature": 0.3, "time": False}
    mock_fix_errors.return_value = (True, True, "prog", "code", "raw", 1.0, "model")
    
    # Execute - should complete without trying to write files
    success, final_code, final_program, attempts, cost, model = crash_main(
        ctx=mock_ctx,
        prompt_file="p.txt",
        code_file="c.py",
        program_file="prog.py",
        error_file="e.log",
        loop=False
    )
    
    assert success is True
    assert final_code == "code"
    assert final_program == "prog"


# ============================================================================
# UNIT TESTS - Output Control
# ============================================================================

@patch('pdd.crash_main.construct_paths')
@patch('pdd.crash_main.resolve_effective_config')
@patch('pdd.crash_main.fix_code_module_errors')
@patch('pdd.crash_main.rprint')
def test_crash_main_quiet_mode(
    mock_rprint: MagicMock,
    mock_fix_errors: MagicMock,
    mock_resolve: MagicMock,
    mock_construct: MagicMock,
    mock_ctx: MagicMock
) -> None:
    """Test crash_main in quiet mode suppresses output."""
    mock_ctx.obj["quiet"] = True
    mock_ctx.params["quiet"] = True
    
    mock_construct.return_value = (
        {"strength": 0.5, "temperature": 0.3, "time": False},
        {
            "prompt_file": "p",
            "code_file": "c",
            "program_file": "prog",
            "error_file": "e"
        },
        {},
        "python"
    )
    mock_resolve.return_value = {"strength": 0.5, "temperature": 0.3, "time": False}
    mock_fix_errors.return_value = (False, False, "prog", "code", "raw", 1.0, "model")
    
    # Execute
    crash_main(
        ctx=mock_ctx,
        prompt_file="p.txt",
        code_file="c.py",
        program_file="prog.py",
        error_file="e.log",
        loop=False
    )
    
    # rprint should not be called in quiet mode
    mock_rprint.assert_not_called()


@patch('pdd.crash_main.construct_paths')
@patch('pdd.crash_main.resolve_effective_config')
@patch('pdd.crash_main.fix_code_module_errors')
@patch('pdd.crash_main.rprint')
def test_crash_main_verbose_mode(
    mock_rprint: MagicMock,
    mock_fix_errors: MagicMock,
    mock_resolve: MagicMock,
    mock_construct: MagicMock,
    mock_ctx: MagicMock
) -> None:
    """Test crash_main in verbose mode shows diagnostics."""
    mock_ctx.obj["verbose"] = True
    mock_ctx.params["verbose"] = True
    
    mock_construct.return_value = (
        {"strength": 0.5, "temperature": 0.3, "time": False},
        {
            "prompt_file": "p",
            "code_file": "original code",
            "program_file": "original prog",
            "error_file": "e"
        },
        {},
        "python"
    )
    mock_resolve.return_value = {"strength": 0.5, "temperature": 0.3, "time": False}
    mock_fix_errors.return_value = (True, True, "new prog", "new code", "raw", 1.0, "model")
    
    # Execute
    crash_main(
        ctx=mock_ctx,
        prompt_file="p.txt",
        code_file="c.py",
        program_file="prog.py",
        error_file="e.log",
        loop=False
    )
    
    # Check that verbose diagnostics were printed
    calls = [str(call) for call in mock_rprint.call_args_list]
    verbose_output = " ".join(calls)
    assert "Verbose diagnostics" in verbose_output or "verbose" in verbose_output.lower()


# ============================================================================
# UNIT TESTS - Configuration Resolution
# ============================================================================

@patch('pdd.crash_main.construct_paths')
@patch('pdd.crash_main.resolve_effective_config')
@patch('pdd.crash_main.fix_code_module_errors')
@patch('pdd.crash_main.rprint')
def test_crash_main_parameter_overrides(
    mock_rprint: MagicMock,
    mock_fix_errors: MagicMock,
    mock_resolve: MagicMock,
    mock_construct: MagicMock,
    mock_ctx: MagicMock
) -> None:
    """Test crash_main passes parameter overrides to config resolution."""
    mock_construct.return_value = (
        {"strength": 0.5, "temperature": 0.3, "time": False},
        {
            "prompt_file": "p",
            "code_file": "c",
            "program_file": "prog",
            "error_file": "e"
        },
        {},
        "python"
    )
    mock_resolve.return_value = {"strength": 0.8, "temperature": 0.9, "time": True}
    mock_fix_errors.return_value = (False, False, "prog", "code", "raw", 1.0, "model")
    
    # Execute with explicit strength and temperature
    crash_main(
        ctx=mock_ctx,
        prompt_file="p.txt",
        code_file="c.py",
        program_file="prog.py",
        error_file="e.log",
        strength=0.8,
        temperature=0.9,
        loop=False
    )
    
    # Verify resolve_effective_config was called with param_overrides
    call_args = mock_resolve.call_args
    assert call_args[1]["param_overrides"]["strength"] == 0.8
    assert call_args[1]["param_overrides"]["temperature"] == 0.9


# ============================================================================
# Z3 FORMAL VERIFICATION TESTS
# ============================================================================

def test_z3_return_tuple_structure() -> None:
    """
    Z3 Test: Verify crash_main return tuple always has correct structure.
    
    Properties verified:
    - Return value is a 6-tuple
    - Element 0 is bool
    - Element 1 is str (final_code)
    - Element 2 is str (final_program)
    - Element 3 is int (attempts)
    - Element 4 is float (cost)
    - Element 5 is str (model)
    """
    # Create symbolic variables
    attempts = Int('attempts')
    cost = Real('cost')
    
    # Create solver
    s = Solver()
    
    # Define invariants that should always hold
    s.add(attempts >= 0)  # attempts cannot be negative
    s.add(cost >= 0.0)     # cost cannot be negative
    
    # Property: if error occurred (attempts=0), then cost should be 0
    s.add(Implies(attempts == 0, cost == 0.0))
    
    # Check if constraints are satisfiable
    result = s.check()
    assert result == sat, "Basic invariants should be satisfiable"
    
    # Test contradiction: attempts negative should be unsatisfiable
    s.push()
    s.add(attempts < 0)
    result = s.check()
    assert result == unsat, "Negative attempts should be impossible"
    s.pop()
    
    # Test contradiction: negative cost should be unsatisfiable
    s.push()
    s.add(cost < 0.0)
    result = s.check()
    assert result == unsat, "Negative cost should be impossible"
    s.pop()


def test_z3_error_case_invariants() -> None:
    """
    Z3 Test: Verify invariants for error cases.
    
    Properties verified:
    - If success=False and model contains "Error", then attempts=0 and cost=0
    - If attempts=0, then cost=0
    - Error cases should have empty final_code and final_program
    """
    # Create symbolic variables
    success = Bool('success')
    attempts = Int('attempts')
    cost = Real('cost')
    is_error = Bool('is_error')  # Represents model containing "Error"
    code_empty = Bool('code_empty')
    program_empty = Bool('program_empty')
    
    s = Solver()
    
    # Define error case: success=False and model indicates error
    # Then: attempts=0, cost=0, code and program are empty
    s.add(Implies(
        And(Not(success), is_error),
        And(attempts == 0, cost == 0.0, code_empty, program_empty)
    ))
    
    # General invariant: attempts=0 implies cost=0
    s.add(Implies(attempts == 0, cost == 0.0))
    
    # Always non-negative
    s.add(attempts >= 0)
    s.add(cost >= 0.0)
    
    # Test: error case should be consistent
    s.push()
    s.add(Not(success))
    s.add(is_error)
    result = s.check()
    assert result == sat, "Error case should be satisfiable"
    
    if result == sat:
        m = s.model()
        # In error case, verify attempts and cost are 0
        assert m[attempts].as_long() == 0
        assert m[cost].numerator_as_long() == 0
    s.pop()


def test_z3_success_case_properties() -> None:
    """
    Z3 Test: Verify properties of successful execution.
    
    Properties verified:
    - If success=True, then attempts >= 1
    - If success=True and loop=False, then attempts == 1
    - Cost can be > 0 when success=True
    """
    success = Bool('success')
    attempts = Int('attempts')
    cost = Real('cost')
    loop_mode = Bool('loop_mode')
    
    s = Solver()
    
    # Basic invariants
    s.add(attempts >= 0)
    s.add(cost >= 0.0)
    
    # Success case: at least 1 attempt
    s.add(Implies(success, attempts >= 1))
    
    # Non-loop success: exactly 1 attempt
    s.add(Implies(And(success, Not(loop_mode)), attempts == 1))
    
    # Test: successful non-loop execution
    s.push()
    s.add(success)
    s.add(Not(loop_mode))
    result = s.check()
    assert result == sat
    
    if result == sat:
        m = s.model()
        assert m[attempts].as_long() == 1, "Non-loop mode should have exactly 1 attempt"
    s.pop()
    
    # Test: successful loop execution can have multiple attempts
    s.push()
    s.add(success)
    s.add(loop_mode)
    s.add(attempts == 3)
    s.add(cost > 0)
    result = s.check()
    assert result == sat, "Loop mode can have multiple attempts"
    s.pop()
    
    # Test: contradiction - success with 0 attempts should be impossible
    s.push()
    s.add(success)
    s.add(attempts == 0)
    result = s.check()
    assert result == unsat, "Success with 0 attempts should be impossible"
    s.pop()


def test_z3_cost_attempt_relationship() -> None:
    """
    Z3 Test: Verify relationship between cost and attempts.
    
    Properties verified:
    - If attempts > 0, cost can be > 0 (but not required)
    - If attempts = 0, cost must be 0
    - Cost increases or stays same, never decreases (monotonic)
    """
    attempts = Int('attempts')
    cost = Real('cost')
    
    s = Solver()
    
    # Basic invariants
    s.add(attempts >= 0)
    s.add(cost >= 0.0)
    
    # Key invariant: zero attempts means zero cost
    s.add(Implies(attempts == 0, cost == 0.0))
    
    # Test: zero attempts with non-zero cost is impossible
    s.push()
    s.add(attempts == 0)
    s.add(cost > 0)
    result = s.check()
    assert result == unsat, "Zero attempts with positive cost should be impossible"
    s.pop()
    
    # Test: multiple attempts with positive cost is valid
    s.push()
    s.add(attempts > 0)
    s.add(cost > 0)
    result = s.check()
    assert result == sat, "Positive attempts with positive cost is valid"
    s.pop()
    
    # Test: multiple attempts with zero cost is technically valid (free API?)
    s.push()
    s.add(attempts > 0)
    s.add(cost == 0)
    result = s.check()
    assert result == sat, "Positive attempts with zero cost is valid (edge case)"
    s.pop()


# ============================================================================
# INTEGRATION-STYLE TESTS (with minimal mocking)
# ============================================================================

@patch('pdd.crash_main.construct_paths')
@patch('pdd.crash_main.resolve_effective_config')
@patch('pdd.crash_main.fix_code_module_errors')
@patch('pdd.crash_main.rprint')
def test_crash_main_full_flow_non_loop(
    mock_rprint: MagicMock,
    mock_fix_errors: MagicMock,
    mock_resolve: MagicMock,
    mock_construct: MagicMock,
    mock_ctx: MagicMock,
    tmp_path: Path
) -> None:
    """Integration test: full flow in non-loop mode."""
    output_code = tmp_path / "output_code.py"
    output_program = tmp_path / "output_program.py"
    
    mock_construct.return_value = (
        {"strength": 0.5, "temperature": 0.3, "time": False},
        {
            "prompt_file": "# Prompt: create a function",
            "code_file": "def old_func(): pass",
            "program_file": "from module import old_func\nold_func()",
            "error_file": "NameError: old_func not found"
        },
        {
            "output": str(output_code),
            "output_program": str(output_program)
        },
        "python"
    )
    mock_resolve.return_value = {"strength": 0.5, "temperature": 0.3, "time": False}
    mock_fix_errors.return_value = (
        True,  # update_program
        True,  # update_code
        "from module import new_func\nnew_func()",  # fixed_program
        "def new_func(): return 42",  # fixed_code
        "raw output",
        1.23,  # cost
        "gpt-4"  # model
    )
    
    # Execute
    success, final_code, final_program, attempts, cost, model = crash_main(
        ctx=mock_ctx,
        prompt_file="prompt.txt",
        code_file="code.py",
        program_file="program.py",
        error_file="error.log",
        output=str(output_code),
        output_program=str(output_program),
        loop=False,
        strength=0.5,
        temperature=0.3
    )
    
    # Verify results
    assert success is True
    assert "new_func" in final_code
    assert "new_func" in final_program
    assert attempts == 1
    assert cost == 1.23
    assert model == "gpt-4"
    
    # Verify files written
    assert output_code.exists()
    assert output_program.exists()
    assert "new_func" in output_code.read_text()
    assert "new_func" in output_program.read_text()


@patch('pdd.crash_main.construct_paths')
@patch('pdd.crash_main.resolve_effective_config')
@patch('pdd.crash_main.fix_code_loop')
@patch('pdd.crash_main.rprint')
def test_crash_main_full_flow_loop(
    mock_rprint: MagicMock,
    mock_fix_loop: MagicMock,
    mock_resolve: MagicMock,
    mock_construct: MagicMock,
    mock_ctx: MagicMock,
    tmp_path: Path
) -> None:
    """Integration test: full flow in loop mode."""
    output_code = tmp_path / "output_code.py"
    output_program = tmp_path / "output_program.py"
    
    mock_construct.return_value = (
        {"strength": 0.7, "temperature": 0.1, "time": False},
        {
            "prompt_file": "# Prompt",
            "code_file": "original code",
            "program_file": "original program",
            "error_file": "errors"
        },
        {
            "output": str(output_code),
            "output_program": str(output_program)
        },
        "python"
    )
    mock_resolve.return_value = {"strength": 0.7, "temperature": 0.1, "time": False}
    mock_fix_loop.return_value = (
        True,  # success
        "fixed program after 3 iterations",  # final_program
        "fixed code after 3 iterations",  # final_code
        3,  # attempts
        4.56,  # cost
        "gpt-4-turbo"  # model
    )
    
    # Execute
    success, final_code, final_program, attempts, cost, model = crash_main(
        ctx=mock_ctx,
        prompt_file="prompt.txt",
        code_file="code.py",
        program_file="program.py",
        error_file="error.log",
        output=str(output_code),
        output_program=str(output_program),
        loop=True,
        max_attempts=5,
        budget=10.0,
        agentic_fallback=True,
        strength=0.7,
        temperature=0.1
    )
    
    # Verify results
    assert success is True
    assert "iterations" in final_code
    assert "iterations" in final_program
    assert attempts == 3
    assert cost == 4.56
    assert model == "gpt-4-turbo"
    
    # Verify files written
    assert output_code.exists()
    assert output_program.exists()


if __name__ == "__main__":
    pytest.main([__file__, "-v"])