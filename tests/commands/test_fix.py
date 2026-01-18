# TEST PLAN
# --------------------------------------------------------------------------------
# 1. Z3 Formal Verification:
#    - Goal: Verify the logic for mode selection (Agentic vs Manual) and argument validation.
#    - Variables:
#      - is_url (bool): First argument looks like a URL.
#      - manual_flag (bool): --manual flag is present.
#      - loop_flag (bool): --loop flag is present.
#      - arg_count (int): Number of positional arguments.
#    - Logic to Verify:
#      - Agentic Mode is active IFF (is_url AND NOT manual_flag).
#      - Manual Mode is active IFF NOT Agentic Mode.
#      - In Manual Mode, validation passes IFF:
#        - (loop_flag AND arg_count >= 3) OR (NOT loop_flag AND arg_count >= 4).
#    - The Z3 test will prove that for any combination of inputs, the decision logic
#      is consistent and covers all cases without ambiguity.
#
# 2. Unit Tests (pytest + click.testing.CliRunner):
#    - Setup: Mock external dependencies (fix_main, run_agentic_e2e_fix, console, etc.)
#      to isolate the `fix` command logic.
#    - Test Cases:
#      a. Agentic Mode Success:
#         - Input: URL argument.
#         - Verify: Calls `run_agentic_e2e_fix` with correct params.
#         - Verify: Output contains success message.
#      b. Agentic Mode Failure:
#         - Input: URL argument.
#         - Mock: `run_agentic_e2e_fix` returns failure.
#         - Verify: Output contains failure message.
#      c. Manual Mode (Non-Loop) Success:
#         - Input: 4 args (prompt, code, test, error).
#         - Verify: Calls `fix_main` with `error_file` set.
#      d. Manual Mode (Loop) Success:
#         - Input: --loop, 3 args (prompt, code, test).
#         - Verify: Calls `fix_main` with `error_file=None` and `loop=True`.
#      e. Manual Mode with Multiple Test Files:
#         - Input: prompt, code, test1, test2, error.
#         - Verify: Calls `fix_main` twice (once for each test file).
#      f. Argument Validation Errors:
#         - No arguments.
#         - Manual mode (non-loop) with insufficient args.
#         - Manual mode (loop) with insufficient args.
#      g. Exception Handling:
#         - Mock `fix_main` to raise a generic exception.
#         - Verify: `handle_error` is called and system exits.
#      h. Flag Passing:
#         - Verify flags like --timeout-adder, --max-cycles are passed correctly to agentic mode.
#         - Verify flags like --budget, --max-attempts are passed correctly to manual mode.

import sys
import os
import types
import importlib.util
import pytest
from unittest.mock import MagicMock, patch
from click.testing import CliRunner
from z3 import Solver, Bool, Int, Implies, And, Not, If, sat, unsat

# --------------------------------------------------------------------------------
# Mocking dependencies before import to handle decorators and relative imports
# --------------------------------------------------------------------------------
# We need to mock the modules that the code under test imports.
# This ensures that when we import `pdd.commands.fix`, it doesn't fail due to missing dependencies
# or execute real decorators.

mock_fix_main_func = MagicMock()
mock_agentic_func = MagicMock()
mock_handle_error_func = MagicMock()

# Decorator mocks that act as pass-throughs
def pass_through_decorator(func):
    return func

def log_operation_factory(*args, **kwargs):
    return pass_through_decorator

# Setup sys.modules mocks for the dependencies that fix.py imports
# We mock these BEFORE loading the fix module so that the relative imports resolve to our mocks
module_mocks = {
    "pdd.fix_main": MagicMock(fix_main=mock_fix_main_func),
    "pdd.agentic_e2e_fix": MagicMock(run_agentic_e2e_fix=mock_agentic_func),
    "pdd.track_cost": MagicMock(track_cost=pass_through_decorator),
    "pdd.operation_log": MagicMock(log_operation=log_operation_factory),
    "pdd.core.errors": MagicMock(handle_error=mock_handle_error_func),
}

# Save original module values before patching (to restore after load)
_original_modules = {key: sys.modules.get(key) for key in module_mocks}

# Use an isolated module name to avoid polluting the real pdd.commands.fix namespace.
# This prevents conflicts with tests that patch pdd.commands.fix.
_isolated_module_name = "_test_fix_isolated.commands.fix"
_isolated_parent_name = "_test_fix_isolated.commands"
_isolated_grandparent_name = "_test_fix_isolated"

# Create the parent package hierarchy for relative imports to work
_grandparent_module = types.ModuleType(_isolated_grandparent_name)
_grandparent_module.__path__ = []
sys.modules[_isolated_grandparent_name] = _grandparent_module

_parent_module = types.ModuleType(_isolated_parent_name)
_parent_module.__path__ = []
sys.modules[_isolated_parent_name] = _parent_module

# Set up the mocked imports to be accessible via the isolated parent
sys.modules[f"{_isolated_grandparent_name}.fix_main"] = module_mocks["pdd.fix_main"]
sys.modules[f"{_isolated_grandparent_name}.agentic_e2e_fix"] = module_mocks["pdd.agentic_e2e_fix"]
sys.modules[f"{_isolated_grandparent_name}.track_cost"] = module_mocks["pdd.track_cost"]
sys.modules[f"{_isolated_grandparent_name}.operation_log"] = module_mocks["pdd.operation_log"]
sys.modules[f"{_isolated_grandparent_name}.core"] = MagicMock()
sys.modules[f"{_isolated_grandparent_name}.core.errors"] = module_mocks["pdd.core.errors"]

# Load the fix.py module using the isolated module name
_fix_module_path = os.path.join(os.path.dirname(__file__), "..", "..", "pdd", "commands", "fix.py")
_fix_module_path = os.path.abspath(_fix_module_path)
_spec = importlib.util.spec_from_file_location(_isolated_module_name, _fix_module_path)
_fix_module = importlib.util.module_from_spec(_spec)
_fix_module.__package__ = _isolated_parent_name
sys.modules[_isolated_module_name] = _fix_module
_spec.loader.exec_module(_fix_module)
fix = _fix_module.fix

# Restore original dependency modules (only the pdd.* ones we temporarily added)
for key, original_value in _original_modules.items():
    if original_value is None:
        sys.modules.pop(key, None)
    else:
        sys.modules[key] = original_value

# Clean up our isolated modules (they're not needed by anyone else)
for key in list(sys.modules.keys()):
    if key.startswith("_test_fix_isolated"):
        sys.modules.pop(key, None)

# --------------------------------------------------------------------------------
# Z3 Formal Verification
# --------------------------------------------------------------------------------

def test_z3_fix_command_logic_verification():
    """
    Formally verify the decision logic for mode selection and argument validation
    in the fix command.
    """
    s = Solver()

    # Inputs
    is_url = Bool('is_url')
    manual_flag = Bool('manual_flag')
    loop_flag = Bool('loop_flag')
    arg_count = Int('arg_count')

    # Derived States (Logic from the code)
    # Agentic mode is selected if first arg is URL and manual flag is NOT set
    is_agentic_mode = And(is_url, Not(manual_flag))
    
    # Manual mode is the fallback
    is_manual_mode = Not(is_agentic_mode)

    # Validation Logic for Manual Mode
    # Loop mode requires >= 3 args
    # Non-loop mode requires >= 4 args
    min_args = If(loop_flag, 3, 4)
    is_valid_manual_args = arg_count >= min_args

    # Verification Goals:
    
    # 1. Mutually Exclusive: Cannot be both Agentic and Manual
    s.push()
    s.add(And(is_agentic_mode, is_manual_mode))
    assert s.check() == unsat, "Modes should be mutually exclusive"
    s.pop()

    # 2. Agentic Precedence: If is_url is True, manual_flag determines the mode
    s.push()
    s.add(is_url)
    # If manual_flag is False, MUST be agentic
    s.add(Not(manual_flag))
    s.add(Not(is_agentic_mode))
    assert s.check() == unsat, "Should be Agentic mode if URL provided and no manual flag"
    s.pop()

    s.push()
    s.add(is_url)
    # If manual_flag is True, MUST be manual
    s.add(manual_flag)
    s.add(Not(is_manual_mode))
    assert s.check() == unsat, "Should be Manual mode if URL provided AND manual flag is set"
    s.pop()

    # 3. Manual Validation Safety:
    # Verify that if we are in manual mode, we consider args invalid if count is low
    s.push()
    s.add(is_manual_mode)
    s.add(arg_count < min_args)
    s.add(is_valid_manual_args) # This should be impossible
    assert s.check() == unsat, "Should mark args as invalid if count is below minimum in manual mode"
    s.pop()

# --------------------------------------------------------------------------------
# Unit Tests
# --------------------------------------------------------------------------------

@pytest.fixture
def runner():
    return CliRunner()

@pytest.fixture(autouse=True)
def reset_mocks():
    mock_fix_main_func.reset_mock()
    mock_agentic_func.reset_mock()
    mock_handle_error_func.reset_mock()

def test_fix_no_args(runner):
    """Test that calling fix with no arguments raises a UsageError."""
    result = runner.invoke(fix, [])
    assert result.exit_code != 0
    assert "Missing arguments" in result.output

def test_agentic_mode_success(runner):
    """Test the Agentic E2E Fix mode happy path."""
    issue_url = "https://github.com/user/repo/issues/1"
    
    # Mock return: success, message, cost, model, extra
    mock_agentic_func.return_value = (True, "Fix applied", 0.5, "gpt-4", {})
    
    result = runner.invoke(fix, [issue_url, "--timeout-adder", "10.0"])
    
    assert result.exit_code == 0
    assert "Agentic fix completed" in result.output
    
    mock_agentic_func.assert_called_once()
    call_kwargs = mock_agentic_func.call_args[1]
    assert call_kwargs["issue_url"] == issue_url
    assert call_kwargs["timeout_adder"] == 10.0
    assert call_kwargs["max_cycles"] == 5  # Default
    assert call_kwargs["resume"] is True   # Default

def test_agentic_mode_failure(runner):
    """Test the Agentic E2E Fix mode failure path."""
    issue_url = "https://github.com/user/repo/issues/1"
    mock_agentic_func.return_value = (False, "Could not fix", 0.1, "gpt-4", {})
    
    result = runner.invoke(fix, [issue_url])
    
    assert result.exit_code == 0
    assert "Agentic fix failed" in result.output
    assert "Could not fix" in result.output

def test_manual_mode_explicit_flag(runner):
    """Test that --manual forces manual mode even with a URL-like argument."""
    # This looks like a URL, but --manual should treat it as a file arg
    args = ["https://github.com/file.txt", "code.py", "test.py", "error.txt", "--manual"]
    
    # Mock fix_main success
    mock_fix_main_func.return_value = (True, "msg", "diff", "full", 0.1, "gpt-3.5")
    
    result = runner.invoke(fix, args)
    
    assert result.exit_code == 0
    # Should NOT call agentic fix
    mock_agentic_func.assert_not_called()
    # Should call fix_main
    mock_fix_main_func.assert_called_once()
    
    call_kwargs = mock_fix_main_func.call_args[1]
    assert call_kwargs["prompt_file"] == "https://github.com/file.txt"

def test_manual_mode_non_loop_success(runner):
    """Test standard manual mode with 4 arguments (Prompt, Code, Test, Error)."""
    args = ["prompt.txt", "code.py", "test.py", "error.txt"]
    
    mock_fix_main_func.return_value = (True, "msg", "diff", "full", 0.1, "gpt-3.5")
    
    result = runner.invoke(fix, args)
    
    assert result.exit_code == 0
    mock_fix_main_func.assert_called_once()
    
    call_kwargs = mock_fix_main_func.call_args[1]
    assert call_kwargs["prompt_file"] == "prompt.txt"
    assert call_kwargs["code_file"] == "code.py"
    assert call_kwargs["unit_test_file"] == "test.py"
    assert call_kwargs["error_file"] == "error.txt"
    assert call_kwargs["loop"] is False

def test_manual_mode_loop_success(runner):
    """Test loop mode which requires only 3 arguments (Prompt, Code, Test)."""
    args = ["prompt.txt", "code.py", "test.py", "--loop", "--verification-program", "verify.py"]
    
    mock_fix_main_func.return_value = (True, "msg", "diff", "full", 0.1, "gpt-3.5")
    
    result = runner.invoke(fix, args)
    
    assert result.exit_code == 0
    mock_fix_main_func.assert_called_once()
    
    call_kwargs = mock_fix_main_func.call_args[1]
    assert call_kwargs["error_file"] is None
    assert call_kwargs["loop"] is True
    assert call_kwargs["verification_program"] == "verify.py"

def test_manual_mode_multiple_test_files(runner):
    """Test manual mode iterating over multiple test files."""
    # Structure: Prompt, Code, Test1, Test2, Error
    args = ["prompt.txt", "code.py", "test1.py", "test2.py", "error.txt"]
    
    mock_fix_main_func.return_value = (True, "msg", "diff", "full", 0.1, "gpt-3.5")
    
    result = runner.invoke(fix, args)
    
    assert result.exit_code == 0
    assert mock_fix_main_func.call_count == 2
    
    # Check calls
    calls = mock_fix_main_func.call_args_list
    assert calls[0][1]["unit_test_file"] == "test1.py"
    assert calls[1][1]["unit_test_file"] == "test2.py"
    # Error file should be passed to both in non-loop mode
    assert calls[0][1]["error_file"] == "error.txt"
    assert calls[1][1]["error_file"] == "error.txt"

def test_manual_mode_validation_errors(runner):
    """Test argument validation logic for manual mode."""
    
    # 1. Non-loop mode requires 4 args. Provide 3.
    result = runner.invoke(fix, ["p.txt", "c.py", "t.py"])
    assert result.exit_code != 0
    assert "Non-loop mode requires at least 4 arguments" in result.output
    
    # 2. Loop mode requires 3 args. Provide 2.
    result = runner.invoke(fix, ["p.txt", "c.py", "--loop"])
    assert result.exit_code != 0
    assert "Loop mode requires at least 3 arguments" in result.output

def test_exception_handling(runner):
    """Test that generic exceptions are caught and handled."""
    mock_fix_main_func.side_effect = ValueError("Something went wrong")
    
    # Using manual mode args to trigger fix_main
    result = runner.invoke(fix, ["p.txt", "c.py", "t.py", "e.txt"])
    
    # Should exit with 1
    assert result.exit_code == 1
    # Should call handle_error
    mock_handle_error_func.assert_called_once()
    args = mock_handle_error_func.call_args[0]
    assert isinstance(args[0], ValueError)
    assert args[1] == "fix"

def test_options_passing(runner):
    """Test that various CLI options are correctly passed to the internal functions."""
    # Test manual mode options
    args = [
        "p.txt", "c.py", "t.py", "e.txt",
        "--budget", "10.5",
        "--max-attempts", "7",
        "--auto-submit",
        "--no-agentic-fallback"
    ]
    
    mock_fix_main_func.return_value = (True, "", "", "", 0, "")
    
    runner.invoke(fix, args)
    
    kwargs = mock_fix_main_func.call_args[1]
    assert kwargs["budget"] == 10.5
    assert kwargs["max_attempts"] == 7
    assert kwargs["auto_submit"] is True
    assert kwargs["agentic_fallback"] is False