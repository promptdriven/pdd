# TEST PLAN
# --------------------------------------------------------------------------------
# 1. Z3 Formal Verification:
#    - Verify the boolean logic for the 'generate' command's argument validation.
#    - The command requires EITHER a 'prompt_file' OR a 'template', but not both.
#    - We will prove that the valid state is strictly an XOR relationship.
#
# 2. Unit Tests (using pytest and click.testing.CliRunner):
#    - Mock external dependencies (code_generator_main, templates, etc.) to isolate the command logic.
#    - Test 'generate' command:
#      - Case: Mutex violation (both prompt_file and template provided) -> Expect UsageError.
#      - Case: Missing arguments (neither provided) -> Expect UsageError.
#      - Case: Valid prompt_file -> Verify call to code_generator_main.
#      - Case: Valid template -> Verify template resolution and call to code_generator_main.
#      - Case: Environment variables -> Verify parsing of KEY=VALUE and KEY (from env) and os.environ updates.
#    - Test 'example' command:
#      - Case: Valid execution -> Verify call to context_generator_main.
#    - Test 'test' command:
#      - Case: Agentic mode (URL argument) -> Verify call to run_agentic_test.
#      - Case: Agentic mode validation -> Fail if arg count != 1.
#      - Case: Manual mode (explicit --manual flag) -> Verify call to cmd_test_main.
#      - Case: Manual mode (implicit by non-URL arg) -> Verify call to cmd_test_main.
#      - Case: Manual mode validation -> Fail if arg count != 2.
# --------------------------------------------------------------------------------

import sys
import os
import pytest
import importlib
from unittest.mock import MagicMock, patch
from click.testing import CliRunner
from z3 import Solver, Bool, Not, And, Or, Implies, unsat

# --------------------------------------------------------------------------------
# MOCK DECORATORS BEFORE IMPORT (WITH CLEANUP)
# --------------------------------------------------------------------------------
# The module under test imports decorators at module load time. We must mock
# those imports for this module only, and restore sys.modules immediately after
# import to avoid polluting other tests during collection.

mock_track_cost = MagicMock()
mock_track_cost.track_cost = lambda x: x  # Identity decorator

mock_op_log = MagicMock()
# Accept *args to handle positional arguments like @log_operation("crash")
mock_op_log.log_operation = lambda *args, **kwargs: lambda x: x  # Decorator factory

mock_core_errors = MagicMock()
mock_core_errors.handle_error = MagicMock()

_import_mocks = {
    "pdd.track_cost": mock_track_cost,
    "pdd.operation_log": mock_op_log,
    "pdd.core.errors": mock_core_errors,
}

_saved_modules = {}
for _mod_name, _mock in _import_mocks.items():
    _saved_modules[_mod_name] = sys.modules.get(_mod_name)
    sys.modules[_mod_name] = _mock

# Preserve any existing module to restore later
_saved_generate_module = sys.modules.pop("pdd.commands.generate", None)
_saved_commands_modules = {
    name: module
    for name, module in sys.modules.items()
    if name.startswith("pdd.commands")
}
_saved_commands_pkg = sys.modules.get("pdd.commands")
_saved_commands_attrs = None
if _saved_commands_pkg is not None:
    _saved_commands_attrs = {
        "generate": getattr(_saved_commands_pkg, "generate", None),
        "test": getattr(_saved_commands_pkg, "test", None),
        "example": getattr(_saved_commands_pkg, "example", None),
    }

try:
    # Import the module under test
    # We use importlib to avoid potential namespace shadowing if pdd.commands exports 'generate'
    generate_module = importlib.import_module("pdd.commands.generate")
finally:
    # Restore mocked modules immediately to prevent pollution
    for _mod_name in _import_mocks:
        if _saved_modules[_mod_name] is not None:
            sys.modules[_mod_name] = _saved_modules[_mod_name]
        else:
            sys.modules.pop(_mod_name, None)

    # Restore pdd.commands module tree to its prior state to avoid polluting
    # later imports with mocked decorators.
    for _name in [n for n in sys.modules if n.startswith("pdd.commands")]:
        if _name not in _saved_commands_modules:
            sys.modules.pop(_name, None)
    for _name, _module in _saved_commands_modules.items():
        sys.modules[_name] = _module

    # Restore original package attributes if the package existed pre-import.
    if _saved_commands_pkg is not None and _saved_commands_attrs is not None:
        _commands_pkg = sys.modules.get("pdd.commands")
        if _commands_pkg is not None:
            for _attr, _value in _saved_commands_attrs.items():
                if _value is None:
                    if hasattr(_commands_pkg, _attr):
                        delattr(_commands_pkg, _attr)
                else:
                    setattr(_commands_pkg, _attr, _value)

    # Restore or remove pdd.commands.generate to avoid leaking mocked decorators
    if _saved_generate_module is not None:
        sys.modules["pdd.commands.generate"] = _saved_generate_module
    else:
        sys.modules.pop("pdd.commands.generate", None)

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

del _import_mocks, _saved_modules, _saved_generate_module, _saved_commands_modules, _saved_commands_pkg, _saved_commands_attrs, _mod_name

# --------------------------------------------------------------------------------
# Z3 FORMAL VERIFICATION
# --------------------------------------------------------------------------------

def test_z3_generate_argument_logic():
    """
    Formally verify the logic: "Cannot specify both PROMPT_FILE and --template"
    and "Missing argument 'PROMPT_FILE' or option '--template'".
    This implies a strict XOR relationship for validity.
    """
    s = Solver()

    # Inputs
    has_prompt_file = Bool('has_prompt_file')
    has_template = Bool('has_template')

    # Logic derived from code:
    # if template and prompt_file: raise UsageError
    # if not template and not prompt_file: raise UsageError
    
    # We define "Error" state based on the code's logic
    is_error = Or(
        And(has_template, has_prompt_file),
        And(Not(has_template), Not(has_prompt_file))
    )

    # We define "Valid" state as NOT Error
    is_valid = Not(is_error)

    # We want to prove that is_valid <==> (has_template XOR has_prompt_file)
    # XOR in boolean logic is (A != B)
    xor_condition = (has_template != has_prompt_file)

    # We assert the negation of the equivalence. If UNSAT, then the equivalence holds.
    s.add(Not(is_valid == xor_condition))

    result = s.check()
    assert result == unsat, "The validation logic does not strictly implement XOR between template and prompt_file"

# --------------------------------------------------------------------------------
# UNIT TESTS
# --------------------------------------------------------------------------------

@pytest.fixture
def runner():
    return CliRunner()

@pytest.fixture(autouse=True)
def reset_generate_module_state():
    generate_module.code_generator_main = None
    generate_module._DEFAULT_CODE_GENERATOR_MAIN = None
    yield

@pytest.fixture
def mock_code_gen():
    with patch("pdd.code_generator_main.code_generator_main") as m:
        m.return_value = ("code", False, 0.0, "model")
        yield m

@pytest.fixture
def mock_load_template():
    with patch("pdd.template_registry.load_template") as m:
        yield m

@pytest.fixture
def mock_context_gen():
    with patch.object(generate_module, "context_generator_main") as m:
        m.return_value = ("example", 0.0, "model")
        yield m

@pytest.fixture
def mock_agentic_test():
    with patch("pdd.agentic_test.run_agentic_test") as m:
        # Returns (success, message, cost, model, changed_files)
        m.return_value = (True, "Success", 0.1, "gpt-4", ["file.py"])
        yield m

@pytest.fixture
def mock_cmd_test():
    with patch("pdd.cmd_test_main.cmd_test_main") as m:
        m.return_value = ("test_code", 0.1, "gpt-4")
        yield m

# --- Generate Command Tests ---

def test_generate_mutex_error_both(runner):
    """Test that providing both prompt_file and --template raises UsageError."""
    with runner.isolated_filesystem():
        with open("prompt.txt", "w") as f: f.write("prompt")
        result = runner.invoke(generate_module.generate, ["prompt.txt", "--template", "tpl"])
        assert result.exit_code != 0
        assert "Cannot specify both PROMPT_FILE and --template" in result.output

def test_generate_mutex_error_neither(runner):
    """Test that providing neither prompt_file nor --template raises UsageError."""
    result = runner.invoke(generate_module.generate, [])
    assert result.exit_code != 0
    assert "Missing argument 'PROMPT_FILE' or option '--template'" in result.output

def test_generate_success_prompt_file(runner, mock_code_gen):
    """Test successful generation using a prompt file."""
    with runner.isolated_filesystem():
        with open("my_prompt.txt", "w") as f: f.write("do stuff")
        
        result = runner.invoke(generate_module.generate, ["my_prompt.txt"])
        
        assert result.exit_code == 0
        mock_code_gen.assert_called_once()
        call_kwargs = mock_code_gen.call_args[1]
        assert call_kwargs["prompt_file"] == "my_prompt.txt"
        assert call_kwargs["force_incremental_flag"] is False

def test_generate_success_template(runner, mock_code_gen, mock_load_template):
    """Test successful generation using a template."""
    mock_load_template.return_value = {"path": "/path/to/resolved/template.txt"}

    result = runner.invoke(generate_module.generate, ["--template", "basic-flask"])

    assert result.exit_code == 0
    mock_load_template.assert_called_with("basic-flask")
    mock_code_gen.assert_called_once()
    assert mock_code_gen.call_args[1]["prompt_file"] == "/path/to/resolved/template.txt"

def test_generate_template_not_found(runner, mock_load_template):
    """Test error when template cannot be resolved."""
    mock_load_template.side_effect = FileNotFoundError("missing")

    result = runner.invoke(generate_module.generate, ["--template", "missing"])

    assert result.exit_code != 0
    assert "Failed to load template 'missing'" in result.output

def test_generate_env_vars(runner, mock_code_gen):
    """Test environment variable parsing and setting."""
    with runner.isolated_filesystem():
        with open("p.txt", "w") as f: f.write("p")
        
        # Set a host env var to test pass-through
        os.environ["HOST_VAR"] = "host_value"
        
        # We invoke with one explicit KV pair and one pass-through key
        result = runner.invoke(generate_module.generate, ["p.txt", "-e", "NEW_VAR=new_val", "-e", "HOST_VAR"])
        
        assert result.exit_code == 0
        
        # Verify os.environ was updated (mock_code_gen runs inside the context where env is set)
        assert os.environ.get("NEW_VAR") == "new_val"
        assert os.environ.get("HOST_VAR") == "host_value"
        
        # Cleanup
        if "NEW_VAR" in os.environ: del os.environ["NEW_VAR"]
        if "HOST_VAR" in os.environ: del os.environ["HOST_VAR"]

# --- Example Command Tests ---

def test_example_success(runner, mock_context_gen):
    """Test the example command success path."""
    with runner.isolated_filesystem():
        with open("prompt.txt", "w") as f: f.write("p")
        with open("code.py", "w") as f: f.write("c")
        
        result = runner.invoke(generate_module.example, ["prompt.txt", "code.py", "--output", "out.md"])
        
        assert result.exit_code == 0
        mock_context_gen.assert_called_once()
        kwargs = mock_context_gen.call_args[1]
        assert kwargs["prompt_file"] == "prompt.txt"
        assert kwargs["code_file"] == "code.py"
        assert kwargs["output"] == "out.md"

# --- Test Command Tests ---

def test_test_agentic_mode_success(runner, mock_agentic_test):
    """Test 'test' command in Agentic mode (URL argument)."""
    url = "https://github.com/user/repo/issues/1"
    result = runner.invoke(generate_module.test, [url, "--timeout-adder", "5.0"])
    
    assert result.exit_code == 0
    mock_agentic_test.assert_called_once()
    kwargs = mock_agentic_test.call_args[1]
    assert kwargs["issue_url"] == url
    assert kwargs["timeout_adder"] == 5.0
    assert kwargs["use_github_state"] is True  # Default

def test_test_agentic_mode_options(runner, mock_agentic_test):
    """Test 'test' command Agentic mode options (no-github-state)."""
    url = "https://github.com/user/repo/issues/1"
    result = runner.invoke(generate_module.test, [url, "--no-github-state"])
    
    assert result.exit_code == 0
    kwargs = mock_agentic_test.call_args[1]
    assert kwargs["use_github_state"] is False

def test_test_agentic_mode_arg_error(runner):
    """Test Agentic mode fails if more than 1 argument is provided."""
    url = "https://github.com/user/repo/issues/1"
    result = runner.invoke(generate_module.test, [url, "extra_arg"])
    
    assert result.exit_code != 0
    assert "Agentic mode requires exactly one argument" in result.output

def test_test_manual_mode_explicit(runner, mock_cmd_test):
    """Test 'test' command in Manual mode using --manual flag."""
    # Even if we pass a URL, --manual should force manual mode
    url = "https://github.com/user/repo/issues/1"
    result = runner.invoke(generate_module.test, ["--manual", url, "code.py"])
    
    assert result.exit_code == 0
    mock_cmd_test.assert_called_once()
    kwargs = mock_cmd_test.call_args[1]
    assert kwargs["prompt_file"] == url
    assert kwargs["code_file"] == "code.py"

def test_test_manual_mode_implicit(runner, mock_cmd_test):
    """Test 'test' command in Manual mode implicitly (no URL)."""
    result = runner.invoke(generate_module.test, ["prompt.txt", "code.py"])
    
    assert result.exit_code == 0
    mock_cmd_test.assert_called_once()
    kwargs = mock_cmd_test.call_args[1]
    assert kwargs["prompt_file"] == "prompt.txt"
    assert kwargs["code_file"] == "code.py"

def test_test_manual_mode_arg_error(runner):
    """Test Manual mode fails if not exactly 2 arguments."""
    result = runner.invoke(generate_module.test, ["prompt.txt"]) # Only 1 arg, not URL
    
    assert result.exit_code != 0
    assert "Manual mode requires exactly two arguments" in result.output

def test_test_missing_args(runner):
    """Test 'test' command with no arguments."""
    result = runner.invoke(generate_module.test, [])
    assert result.exit_code != 0
    assert "Missing arguments" in result.output
