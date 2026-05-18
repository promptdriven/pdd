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
_side_effect_module_names = (
    "pdd.core.cli",
    "pdd.cli",
    "pdd.sync_orchestration",
)
_saved_side_effect_modules = {
    name: sys.modules.get(name)
    for name in _side_effect_module_names
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
    #
    # Popping from sys.modules alone leaves a stale reference on the `pdd.core`
    # parent package: a subsequent `from pdd.core import X` returns the OLD
    # object via parent-attribute lookup, while `from pdd.core.X import Y`
    # triggers a reimport and yields a NEW class. Tests that bind both names
    # end up with a split module identity and patches miss the freshly imported
    # class. Re-importing immediately keeps sys.modules and the parent attribute
    # consistent.
    _core_side_effects = [
        n for n in sys.modules
        if n.startswith("pdd.core.") and n not in _import_mocks
        and n not in _saved_modules
    ]
    for _name in _core_side_effects:
        sys.modules.pop(_name, None)
    for _name in _core_side_effects:
        importlib.import_module(_name)

    # Importing pdd.commands.generate can pull in sync orchestration while
    # pdd.operation_log and pdd.core.errors are mocked above. If that side
    # effect module stays cached, later sync tests inherit MagicMock logging and
    # error handlers. Restore the prior module, or evict the polluted import.
    def _restore_module_cache(_name, _module):
        if _module is not None:
            sys.modules[_name] = _module
        else:
            sys.modules.pop(_name, None)

        _parent_name, _attr = _name.rsplit(".", 1)
        _parent = sys.modules.get(_parent_name)
        if _parent is not None:
            if _module is not None:
                setattr(_parent, _attr, _module)
            elif hasattr(_parent, _attr):
                delattr(_parent, _attr)

    for _name, _module in _saved_side_effect_modules.items():
        _restore_module_cache(_name, _module)

del _import_mocks, _saved_modules, _saved_generate_module, _saved_commands_modules, _side_effect_module_names, _saved_side_effect_modules, _saved_commands_pkg, _saved_commands_attrs, _mod_name, _restore_module_cache

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

        # Verify env_vars dict was also forwarded into code_generator_main so that
        # template / front-matter variable resolution sees them (regression for
        # the codex finding on pdd/commands/generate.py:320).
        call_kwargs = mock_code_gen.call_args[1]
        assert call_kwargs["env_vars"] == {
            "NEW_VAR": "new_val",
            "HOST_VAR": "host_value",
        }

        # Cleanup
        if "NEW_VAR" in os.environ: del os.environ["NEW_VAR"]
        if "HOST_VAR" in os.environ: del os.environ["HOST_VAR"]


def test_generate_unit_test_and_exclude_tests_forwarded(runner, mock_code_gen):
    """Regression: ``--unit-test`` and ``--exclude-tests`` must reach code_generator_main.

    The codex review for issue #1057 flagged that these flags were parsed by the
    CLI but no longer forwarded into ``code_generator_main``, which still
    consumes them. Without this propagation, test inclusion/exclusion behaviour
    silently degrades to the function default.
    """
    with runner.isolated_filesystem():
        with open("p.txt", "w") as f:
            f.write("p")

        result = runner.invoke(
            generate_module.generate,
            ["p.txt", "--unit-test", "tests/test_p.py", "--exclude-tests"],
        )

        assert result.exit_code == 0, result.output
        kwargs = mock_code_gen.call_args[1]
        assert kwargs["unit_test_file"] == "tests/test_p.py"
        assert kwargs["exclude_tests"] is True


def test_generate_exclude_tests_default_false(runner, mock_code_gen):
    """Default for --exclude-tests is False and must propagate verbatim."""
    with runner.isolated_filesystem():
        with open("p.txt", "w") as f:
            f.write("p")

        result = runner.invoke(generate_module.generate, ["p.txt"])

        assert result.exit_code == 0, result.output
        kwargs = mock_code_gen.call_args[1]
        assert kwargs["exclude_tests"] is False
        assert kwargs["unit_test_file"] is None


def test_generate_missing_prompt_file_fails_usage(runner, mock_code_gen):
    """Regression for codex finding on pdd/commands/generate.py:284.

    A missing standard prompt file must short-circuit with a usage error and a
    non-zero exit code. Without this guard, ``code_generator_main`` returns an
    error tuple that the CLI wrapper would otherwise treat as success (exit 0),
    masking failures from scripts.
    """
    with runner.isolated_filesystem():
        result = runner.invoke(generate_module.generate, ["missing.prompt"])

    assert result.exit_code != 0, result.output
    assert "Input file not found" in result.output
    mock_code_gen.assert_not_called()


def test_generate_directory_prompt_fails_usage(runner, mock_code_gen):
    """A directory passed where a prompt file is expected must error out."""
    with runner.isolated_filesystem():
        os.mkdir("prompts_dir")
        result = runner.invoke(generate_module.generate, ["prompts_dir"])

    assert result.exit_code != 0, result.output
    assert "directory" in result.output.lower()
    mock_code_gen.assert_not_called()

# --- Example Command Tests ---

def test_example_success(runner, mock_context_gen):
    """Test the example command success path."""
    with runner.isolated_filesystem():
        # Use a `<basename>_<language>.prompt` filename so infer_module_identity()
        # would resolve to ("foo", "python"); this exercises the same naming
        # contract that `clears_run_report=True` relies on (see #1057).
        with open("foo_python.prompt", "w") as f: f.write("p")
        with open("foo.py", "w") as f: f.write("c")

        result = runner.invoke(generate_module.example, ["foo_python.prompt", "foo.py", "--output", "out.md"])

        assert result.exit_code == 0
        mock_context_gen.assert_called_once()
        kwargs = mock_context_gen.call_args[1]
        assert kwargs["prompt_file"] == "foo_python.prompt"
        assert kwargs["code_file"] == "foo.py"
        assert kwargs["output"] == "out.md"


def test_example_command_declares_clears_run_report():
    """Regression test for issue #1057.

    `pdd example` must be decorated with ``@log_operation(..., clears_run_report=True)``
    so a successful example regeneration invalidates any stale
    ``.pdd/meta/<module>_<language>_run.json``. Without that flag, the
    fingerprint would be refreshed while the run report kept describing the
    pre-mutation example output.

    We assert against the source file because this test module deliberately
    mocks ``pdd.operation_log.log_operation`` with a no-op decorator factory
    at import time (see the top of this file), which strips the decorator
    parameters from the in-memory function object. The source is the
    authoritative record of the decorator stack.
    """
    import importlib
    import inspect
    import re
    from pathlib import Path

    # Resolve the real module file path. ``pdd.commands`` re-exports ``generate``
    # as a Click command at attribute lookup time, which can shadow the module
    # object — use importlib to bypass that and reach the real submodule.
    real_generate = importlib.import_module("pdd.commands.generate")
    module_file = getattr(real_generate, "__file__", None)
    if not module_file:
        # Fall back to filesystem lookup via the package, which should always
        # have a __file__.
        pdd_commands = importlib.import_module("pdd.commands")
        module_file = str(Path(pdd_commands.__file__).parent / "generate.py")
    source = Path(module_file).read_text(encoding="utf-8")

    # Match the @log_operation(...) decorator immediately preceding `def example(`.
    # Allow other decorators (e.g. @track_cost) between them.
    pattern = re.compile(
        r"@log_operation\((?P<args>[^)]*)\)\s*(?:@[\w\.]+(?:\([^)]*\))?\s*)*def\s+example\b",
        re.DOTALL,
    )
    match = pattern.search(source)
    assert match is not None, (
        "pdd.commands.generate.example must be wrapped with @log_operation(...)"
    )
    decorator_args = match.group("args")
    assert 'operation="example"' in decorator_args, (
        "example command's @log_operation must declare operation=\"example\""
    )
    assert "clears_run_report=True" in decorator_args, (
        "Regression for issue #1057: `pdd example` must declare "
        "clears_run_report=True on its @log_operation decorator so a fresh "
        "fingerprint never coexists with a stale per-module run report."
    )

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


def test_test_agentic_mode_failure(runner):
    """Test 'test' command exits with 1 when agentic test generation fails (issue #593)."""
    url = "https://github.com/user/repo/issues/1"
    with patch("pdd.agentic_test.run_agentic_test") as mock_run:
        mock_run.return_value = (False, "Workflow failed", 0.0, "gpt-4", [])
        result = runner.invoke(generate_module.test, [url])
    assert result.exit_code == 1


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
    # Regression for the codex finding on pdd/commands/generate.py:523 — when
    # the user supplies --manual we must forward manual=True so cmd_test_main
    # does not silently fall back to agentic test generation for non-Python or
    # API-enabled inputs.
    assert kwargs["manual"] is True

def test_test_manual_mode_implicit(runner, mock_cmd_test):
    """Test 'test' command in Manual mode implicitly (no URL)."""
    result = runner.invoke(generate_module.test, ["prompt.txt", "code.py"])

    assert result.exit_code == 0
    mock_cmd_test.assert_called_once()
    kwargs = mock_cmd_test.call_args[1]
    assert kwargs["prompt_file"] == "prompt.txt"
    assert kwargs["code_file"] == "code.py"
    # Without --manual the implicit manual-mode dispatch must forward
    # manual=False so cmd_test_main can choose the right path.
    assert kwargs["manual"] is False

def test_test_manual_mode_arg_error(runner):
    """Test Manual mode fails if not exactly 2 arguments."""
    result = runner.invoke(generate_module.test, ["prompt.txt"]) # Only 1 arg, not URL
    
    assert result.exit_code != 0
    assert "Manual mode requires exactly two arguments" in result.output


def test_test_story_mode_links_metadata(runner):
    """Test 'test' command auto-detects story mode for story__*.md files."""
    with runner.isolated_filesystem():
        with open("story__upload_flow.md", "w") as f:
            f.write("As a user...")

        with patch.object(generate_module, "cache_story_prompt_links") as mock_link:
            mock_link.return_value = (True, "Story prompt metadata linked.", 0.2, "gpt-4", ["upload_python.prompt"])
            result = runner.invoke(generate_module.test, ["story__upload_flow.md"])

    assert result.exit_code == 0
    mock_link.assert_called_once()
    kwargs = mock_link.call_args[1]
    assert kwargs["story_file"] == "story__upload_flow.md"
    assert kwargs["prompts_dir"] is None
    assert kwargs["strength"] == 0.2
    assert kwargs["temperature"] == 0.0
    assert kwargs["time"] == 0.25
    assert kwargs["verbose"] is False


def test_test_story_generation_mode_from_prompt_inputs(runner):
    """Test 'test' command auto-detects story generation for prompt-file inputs."""
    with runner.isolated_filesystem():
        with open("upload_python.prompt", "w") as f:
            f.write("Upload prompt")
        with open("notify_python.prompt", "w") as f:
            f.write("Notify prompt")

        with patch.object(generate_module, "generate_user_story") as mock_generate_story:
            mock_generate_story.return_value = (
                True,
                "Generated story file: user_stories/story__upload_flow.md. Story prompt metadata linked.",
                0.2,
                "gpt-4",
                "user_stories/story__upload_flow.md",
                ["upload_python.prompt"],
            )
            result = runner.invoke(generate_module.test, ["upload_python.prompt", "notify_python.prompt"])

    assert result.exit_code == 0
    mock_generate_story.assert_called_once()
    kwargs = mock_generate_story.call_args[1]
    assert kwargs["prompt_files"] == ["upload_python.prompt", "notify_python.prompt"]
    assert kwargs["output"] is None
    assert kwargs["stories_dir"] is None
    assert kwargs["prompts_dir"] is None
    assert kwargs["strength"] == 0.2
    assert kwargs["temperature"] == 0.0
    assert kwargs["time"] == 0.25
    assert kwargs["verbose"] is False


def test_test_story_mode_links_uses_env_prompts_dir(runner, monkeypatch):
    """Regression for codex finding on pdd/commands/generate.py:469.

    Story-link mode must fall back to ``PDD_PROMPTS_DIR`` when ctx does not
    provide an explicit ``prompts_dir`` override. The CLI does not populate
    that ctx key, so without the env-var fallback story linking scans the
    wrong locations.
    """
    monkeypatch.setenv("PDD_PROMPTS_DIR", "env_prompts")
    with runner.isolated_filesystem():
        with open("story__upload_flow.md", "w") as f:
            f.write("As a user...")

        with patch.object(generate_module, "cache_story_prompt_links") as mock_link:
            mock_link.return_value = (
                True, "Story prompt metadata linked.", 0.0, "gpt-4", []
            )
            result = runner.invoke(generate_module.test, ["story__upload_flow.md"])

    assert result.exit_code == 0, result.output
    mock_link.assert_called_once()
    assert mock_link.call_args[1]["prompts_dir"] == "env_prompts"


def test_test_story_generation_uses_env_dirs(runner, monkeypatch):
    """Regression for codex finding on pdd/commands/generate.py:469.

    Story-generation mode must fall back to ``PDD_PROMPTS_DIR`` and
    ``PDD_USER_STORIES_DIR`` when ctx lacks explicit overrides.
    """
    monkeypatch.setenv("PDD_PROMPTS_DIR", "env_prompts")
    monkeypatch.setenv("PDD_USER_STORIES_DIR", "env_stories")
    with runner.isolated_filesystem():
        with open("upload_python.prompt", "w") as f:
            f.write("Upload prompt")

        with patch.object(generate_module, "generate_user_story") as mock_gen:
            mock_gen.return_value = (
                True, "ok", 0.0, "gpt-4",
                "env_stories/story__upload_flow.md", ["upload_python.prompt"],
            )
            result = runner.invoke(generate_module.test, ["upload_python.prompt"])

    assert result.exit_code == 0, result.output
    mock_gen.assert_called_once()
    kwargs = mock_gen.call_args[1]
    assert kwargs["prompts_dir"] == "env_prompts"
    assert kwargs["stories_dir"] == "env_stories"


def test_test_markdown_input_not_story_mode(runner):
    """Test non-story markdown input no longer triggers story generation mode."""
    with runner.isolated_filesystem():
        with open("upload_flow.md", "w") as f:
            f.write("As a user...")

        with patch.object(generate_module, "generate_user_story") as mock_generate_story:
            result = runner.invoke(generate_module.test, ["upload_flow.md"])

    assert result.exit_code != 0
    assert "Manual mode requires exactly two arguments" in result.output
    mock_generate_story.assert_not_called()


def test_test_missing_args(runner):
    """Test 'test' command with no arguments."""
    result = runner.invoke(generate_module.test, [])
    assert result.exit_code != 0
    assert "Missing arguments" in result.output

def test_test_agentic_mode_agentic_failure(runner, mock_agentic_test):
    """Test 'test' command Agentic mode failure exit code (issue #593).
    When the command raises Exit(1), CliRunner leaves result.output empty, so we only assert exit_code.
    """
    url = "https://github.com/user/repo/issues/1"
    mock_agentic_test.return_value = (False, "Workflow failed", 0.0, "gpt-4", [])
    
    result = runner.invoke(generate_module.test, [url])
    
    assert result.exit_code == 1
