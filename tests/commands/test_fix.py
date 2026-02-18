import sys
import pytest
from unittest.mock import MagicMock, patch
from click.testing import CliRunner
from z3 import Solver, Bool, Int, Implies, And, Not, If, sat, unsat, Or

# --------------------------------------------------------------------------------
# Mocking dependencies BEFORE importing the command under test
# --------------------------------------------------------------------------------

# We need to mock the decorators and top-level imports used by fix.py
# BEFORE we import it, otherwise the import will fail or use real modules.
# CRITICAL: We must restore modules IMMEDIATELY after import to prevent test pollution.
# (See PATTERN 7 in context/pytest_isolation_example.py)

_import_mocks = {
    "pdd.track_cost": MagicMock(track_cost=MagicMock(side_effect=lambda f: f)),
    "pdd.operation_log": MagicMock(log_operation=MagicMock(return_value=lambda f: f)),
    "pdd.core.errors": MagicMock(),
    "pdd.fix_main": MagicMock(),
    "pdd.agentic_e2e_fix": MagicMock(),
}

# Save original modules, apply mocks for import phase
_saved_modules = {}
for _mod_name in _import_mocks:
    if _mod_name in sys.modules:
        _saved_modules[_mod_name] = sys.modules[_mod_name]
    sys.modules[_mod_name] = _import_mocks[_mod_name]

# Now we can safely import the command
from pdd.commands.fix import fix

# Restore modules IMMEDIATELY after import to prevent pollution of other tests
for _mod_name in _import_mocks:
    if _mod_name in _saved_modules:
        sys.modules[_mod_name] = _saved_modules[_mod_name]
    elif _mod_name in sys.modules:
        del sys.modules[_mod_name]

# Evict any pdd.core.* modules that were imported as side effects during the
# mocking window (e.g. pdd.core.dump imported via pdd.commands.report).
# These bound MagicMock attributes from the mocked pdd.core.errors and must
# be re-imported fresh with the real module.
_core_side_effects = [
    n for n in sys.modules
    if n.startswith("pdd.core.") and n not in _import_mocks
    and n not in _saved_modules
]
for _name in _core_side_effects:
    sys.modules.pop(_name, None)

# Clean up temporary variables
del _import_mocks, _saved_modules, _mod_name

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
    is_agentic_mode = And(is_url, Not(manual_flag))
    is_manual_mode = Not(is_agentic_mode)

    # Validation Logic for Manual Mode
    min_args = If(loop_flag, 3, 4)
    is_valid_manual_args = arg_count >= min_args

    # 1. Mutually Exclusive
    s.push()
    s.add(And(is_agentic_mode, is_manual_mode))
    assert s.check() == unsat
    s.pop()

    # 2. Agentic Precedence
    s.push()
    s.add(is_url)
    s.add(Not(manual_flag))
    s.add(Not(is_agentic_mode))
    assert s.check() == unsat
    s.pop()

    # 3. Manual Validation Safety
    s.push()
    s.add(is_manual_mode)
    s.add(arg_count < min_args)
    s.add(is_valid_manual_args)
    assert s.check() == unsat
    s.pop()

# --------------------------------------------------------------------------------
# Unit Tests
# --------------------------------------------------------------------------------

@pytest.fixture
def runner():
    return CliRunner()

@pytest.fixture
def mock_deps():
    """
    Fixture to mock the deferred imports inside the fix command.
    Creates fresh mocks for each test to ensure isolation.

    Note: fix_main and agentic_e2e_fix are deferred imports (imported inside functions),
    so we patch them in sys.modules. handle_error is a top-level import that was already
    bound during the module-level import phase, so we patch it directly in the module.
    """
    mock_fix_main_mod = MagicMock()
    mock_fix_main_func = MagicMock()
    mock_fix_main_mod.fix_main = mock_fix_main_func

    mock_agentic_mod = MagicMock()
    mock_agentic_func = MagicMock()
    mock_agentic_mod.run_agentic_e2e_fix = mock_agentic_func

    mock_handle_error_func = MagicMock()

    with patch.dict(sys.modules, {
        "pdd.fix_main": mock_fix_main_mod,
        "pdd.agentic_e2e_fix": mock_agentic_mod,
    }):
        # Patch handle_error directly in the fix module since it's a top-level import
        with patch("pdd.commands.fix.handle_error", mock_handle_error_func):
            yield {
                "fix_main": mock_fix_main_func,
                "run_agentic_e2e_fix": mock_agentic_func,
                "handle_error": mock_handle_error_func,
            }

def test_fix_no_args(runner, mock_deps):
    result = runner.invoke(fix, [])
    assert result.exit_code != 0
    assert "Missing arguments" in result.output

def test_agentic_mode_success(runner, mock_deps):
    issue_url = "https://github.com/user/repo/issues/1"
    mock_deps["run_agentic_e2e_fix"].return_value = (True, "Fix applied", 0.5, "gpt-4", {})
    result = runner.invoke(fix, [issue_url, "--timeout-adder", "10.0"])
    assert result.exit_code == 0
    assert "Agentic fix completed" in result.output
    mock_deps["run_agentic_e2e_fix"].assert_called_once()
    kwargs = mock_deps["run_agentic_e2e_fix"].call_args[1]
    assert kwargs["issue_url"] == issue_url
    assert kwargs["timeout_adder"] == 10.0

def test_agentic_mode_failure(runner, mock_deps):
    issue_url = "https://github.com/user/repo/issues/1"
    mock_deps["run_agentic_e2e_fix"].return_value = (False, "Could not fix", 0.1, "gpt-4", {})
    result = runner.invoke(fix, [issue_url])
    assert "Agentic fix failed" in result.output

def test_manual_mode_explicit_flag(runner, mock_deps):
    args = ["https://github.com/file.txt", "code.py", "test.py", "error.txt", "--manual"]
    mock_deps["fix_main"].return_value = (True, "msg", "diff", 1, 0.1, "gpt-3.5")
    result = runner.invoke(fix, args)
    assert result.exit_code == 0
    mock_deps["run_agentic_e2e_fix"].assert_not_called()
    mock_deps["fix_main"].assert_called_once()

def test_manual_mode_non_loop_success(runner, mock_deps):
    args = ["prompt.txt", "code.py", "test.py", "error.txt"]
    mock_deps["fix_main"].return_value = (True, "msg", "diff", 1, 0.1, "gpt-3.5")
    result = runner.invoke(fix, args)
    assert result.exit_code == 0
    kwargs = mock_deps["fix_main"].call_args[1]
    assert kwargs["error_file"] == "error.txt"
    assert kwargs["loop"] is False

def test_manual_mode_loop_success(runner, mock_deps):
    args = ["prompt.txt", "code.py", "test.py", "--loop", "--verification-program", "verify.py"]
    mock_deps["fix_main"].return_value = (True, "msg", "diff", 1, 0.1, "gpt-3.5")
    result = runner.invoke(fix, args)
    assert result.exit_code == 0
    kwargs = mock_deps["fix_main"].call_args[1]
    assert kwargs["loop"] is True
    assert kwargs["verification_program"] == "verify.py"

def test_manual_mode_multiple_test_files(runner, mock_deps):
    args = ["prompt.txt", "code.py", "test1.py", "test2.py", "error.txt"]
    mock_deps["fix_main"].return_value = (True, "msg", "diff", 1, 0.1, "gpt-3.5")
    result = runner.invoke(fix, args)
    assert mock_deps["fix_main"].call_count == 2

def test_manual_mode_validation_errors(runner, mock_deps):
    result = runner.invoke(fix, ["p.txt", "c.py", "t.py"])
    assert result.exit_code != 0
    assert "Non-loop mode requires at least 4 arguments" in result.output

def test_exception_handling(runner, mock_deps):
    mock_deps["fix_main"].side_effect = ValueError("Something went wrong")
    result = runner.invoke(fix, ["p.txt", "c.py", "t.py", "e.txt"])
    mock_deps["handle_error"].assert_called_once()

def test_options_passing(runner, mock_deps):
    args = ["p.txt", "c.py", "t.py", "e.txt", "--budget", "10.5", "--max-attempts", "7"]
    mock_deps["fix_main"].return_value = (True, "", "", 1, 0, "")
    runner.invoke(fix, args)
    kwargs = mock_deps["fix_main"].call_args[1]
    assert kwargs["budget"] == 10.5


def test_user_story_fix_mode(runner, mock_deps):
    with patch("pdd.user_story_tests.run_user_story_fix") as mock_story_fix:
        mock_story_fix.return_value = (True, "Story fixed", 0.2, "gpt-4", ["prompts/foo.prompt"])
        with runner.isolated_filesystem():
            with open("story__sample.md", "w") as fh:
                fh.write("As a user...")

            result = runner.invoke(fix, ["story__sample.md"])

        assert result.exit_code == 0
        mock_story_fix.assert_called_once()
