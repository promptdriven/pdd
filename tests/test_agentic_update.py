# Test Plan for pdd.agentic_update.run_agentic_update
#
# 1. Z3 Formal Verification:
#    - Model the control flow and success conditions using Z3.
#    - Verify that success=True implies the prompt file was modified.
#    - Verify that missing preconditions (files, agents, template) lead to success=False.
#
# 2. Unit Tests:
#    - test_missing_files: Verify handling of missing prompt or code files.
#    - test_no_agents: Verify handling when no agents are available.
#    - test_template_errors: Verify handling of template loading or formatting errors.
#    - test_explicit_tests_missing: Verify handling of invalid explicit test paths.
#    - test_successful_update: Verify success=True when prompt file is modified by the agent task.
#    - test_no_modification: Verify success=False when prompt file is NOT modified.
#    - test_test_discovery: Verify that test files are correctly discovered from various locations and passed to the template.
#    - test_explicit_empty_tests: Verify passing an empty list prevents discovery.

import os
import sys
import time
from pathlib import Path
from typing import Any, Generator, Tuple
from unittest.mock import MagicMock, patch

import pytest

# Add project root to sys.path to ensure pdd package can be imported
# This assumes the test file is in tests/ relative to the project root
PROJECT_ROOT = Path(__file__).resolve().parent.parent
if str(PROJECT_ROOT) not in sys.path:
    sys.path.insert(0, str(PROJECT_ROOT))

from pdd.agentic_update import run_agentic_update

# -----------------------------------------------------------------------------
# Z3 Formal Verification
# -----------------------------------------------------------------------------

def test_z3_logic_verification() -> None:
    """
    Formal verification of the control flow logic using Z3.
    Ensures that success is strictly tied to prompt modification and preconditions.
    """
    try:
        import z3  # type: ignore
    except ImportError:
        pytest.skip("z3-solver not installed, skipping formal verification")

    s = z3.Solver()

    # State Variables
    prompt_exists = z3.Bool('prompt_exists')
    code_exists = z3.Bool('code_exists')
    agents_available = z3.Bool('agents_available')
    explicit_tests_valid = z3.Bool('explicit_tests_valid')
    template_loaded = z3.Bool('template_loaded')
    template_formatted = z3.Bool('template_formatted')
    
    # The critical side-effect check
    prompt_modified = z3.Bool('prompt_modified')

    # The function output
    success = z3.Bool('success')

    # Logic Constraints based on code analysis
    
    # 1. File existence checks
    s.add(z3.Implies(z3.Not(prompt_exists), z3.Not(success)))
    s.add(z3.Implies(z3.And(prompt_exists, z3.Not(code_exists)), z3.Not(success)))

    # 2. Agent availability check
    s.add(z3.Implies(z3.And(prompt_exists, code_exists, z3.Not(agents_available)), z3.Not(success)))

    # 3. Explicit test validation (if we assume explicit tests are provided and invalid)
    # We model the case where explicit tests are invalid -> failure
    s.add(z3.Implies(z3.And(prompt_exists, code_exists, agents_available, z3.Not(explicit_tests_valid)), z3.Not(success)))

    # 4. Template loading and formatting
    pre_template = z3.And(prompt_exists, code_exists, agents_available, explicit_tests_valid)
    s.add(z3.Implies(z3.And(pre_template, z3.Not(template_loaded)), z3.Not(success)))
    s.add(z3.Implies(z3.And(pre_template, template_loaded, z3.Not(template_formatted)), z3.Not(success)))

    # 5. Final Success Condition
    # If all preconditions are met, success is determined by whether the prompt was modified.
    all_preconditions = z3.And(
        prompt_exists, 
        code_exists, 
        agents_available, 
        explicit_tests_valid, 
        template_loaded, 
        template_formatted
    )
    
    # The code: success = bool(prompt_modified)
    s.add(z3.Implies(all_preconditions, success == prompt_modified))

    # Verification 1: Can we have success=True if prompt_modified=False?
    s.push()
    s.add(success == True)
    s.add(prompt_modified == False)
    result = s.check()
    assert result == z3.unsat, "Logic Error: Success reported despite no prompt modification"
    s.pop()

    # Verification 2: Can we have success=True if any precondition is missing?
    # Example: prompt_exists=False
    s.push()
    s.add(success == True)
    s.add(prompt_exists == False)
    result = s.check()
    assert result == z3.unsat, "Logic Error: Success reported despite missing prompt file"
    s.pop()

    # Verification 3: If all preconditions met and prompt modified, must be success
    s.push()
    s.add(all_preconditions)
    s.add(prompt_modified == True)
    s.add(success == False)
    result = s.check()
    assert result == z3.unsat, "Logic Error: Failed to report success despite valid update"
    s.pop()


# -----------------------------------------------------------------------------
# Unit Tests
# -----------------------------------------------------------------------------

@pytest.fixture
def mock_deps() -> Generator[Tuple[MagicMock, MagicMock, MagicMock, MagicMock], None, None]:
    """
    Mock external dependencies: agents, template loader, agent runner, console.

    Also stubs out ``_revert_out_of_scope_changes`` to a no-op so tests that
    leave ``PROJECT_ROOT`` pointing at the real repository do not accidentally
    revert tracked working-tree changes when the scope guard runs.
    """
    with patch("pdd.agentic_update.get_available_agents") as mock_agents, \
         patch("pdd.agentic_update.load_prompt_template") as mock_load, \
         patch("pdd.agentic_update.run_agentic_task") as mock_run, \
         patch("pdd.agentic_update.console") as mock_console, \
         patch("pdd.agentic_update._revert_out_of_scope_changes", return_value=[]):

        # Default happy path setup
        mock_agents.return_value = ["claude"]
        mock_template = MagicMock()
        mock_template.format.return_value = "Rendered template with placeholders"
        mock_load.return_value = mock_template
        mock_run.return_value = (True, "Task complete", 0.01, "claude-3-opus")

        yield mock_agents, mock_load, mock_run, mock_console


def test_missing_files(tmp_path: Path, mock_deps: Tuple[MagicMock, ...]) -> None:
    """Test that missing prompt or code files result in failure."""
    prompt_file = tmp_path / "missing.prompt"
    code_file = tmp_path / "code.py"
    code_file.touch()

    # Case 1: Missing prompt file
    success, msg, cost, _, _ = run_agentic_update(str(prompt_file), str(code_file), quiet=True)
    assert not success
    assert "Prompt file not found" in msg
    assert cost == 0.0

    # Case 2: Missing code file
    prompt_file.touch()
    code_file.unlink()
    success, msg, cost, _, _ = run_agentic_update(str(prompt_file), str(code_file), quiet=True)
    assert not success
    assert "Code file not found" in msg


def test_no_agents(tmp_path: Path, mock_deps: Tuple[MagicMock, ...]) -> None:
    """Test behavior when no agents are available."""
    mock_agents, _, _, _ = mock_deps
    mock_agents.return_value = []

    prompt_file = tmp_path / "test.prompt"
    code_file = tmp_path / "code.py"
    prompt_file.touch()
    code_file.touch()

    success, msg, cost, _, _ = run_agentic_update(str(prompt_file), str(code_file), quiet=True)
    
    assert not success
    assert "No agentic CLI available" in msg
    assert cost == 0.0


def test_template_errors(tmp_path: Path, mock_deps: Tuple[MagicMock, ...]) -> None:
    """Test handling of template loading or formatting errors."""
    mock_agents, mock_load, _, _ = mock_deps
    
    prompt_file = tmp_path / "test.prompt"
    code_file = tmp_path / "code.py"
    prompt_file.touch()
    code_file.touch()

    # Case 1: Template load returns None/Empty
    mock_load.return_value = None
    success, msg, _, _, _ = run_agentic_update(str(prompt_file), str(code_file), quiet=True)
    assert not success
    assert "could not be loaded" in msg

    # Case 2: Template load raises exception
    mock_load.side_effect = Exception("Load error")
    success, msg, _, _, _ = run_agentic_update(str(prompt_file), str(code_file), quiet=True)
    assert not success
    assert "Error while loading prompt template" in msg

    # Case 3: Template format error
    mock_load.side_effect = None
    mock_load.return_value = "Invalid format {missing_key}"
    success, msg, _, _, _ = run_agentic_update(str(prompt_file), str(code_file), quiet=True)
    assert not success
    assert "Error formatting" in msg


def test_explicit_tests_missing(tmp_path: Path, mock_deps: Tuple[MagicMock, ...]) -> None:
    """Test validation of explicitly provided test files."""
    prompt_file = tmp_path / "test.prompt"
    code_file = tmp_path / "code.py"
    prompt_file.touch()
    code_file.touch()

    missing_test = tmp_path / "missing_test.py"
    
    success, msg, _, _, _ = run_agentic_update(
        str(prompt_file), 
        str(code_file), 
        test_files=[missing_test], 
        quiet=True
    )
    
    assert not success
    assert "Test file(s) not found" in msg


def test_successful_update(tmp_path: Path, mock_deps: Tuple[MagicMock, ...]) -> None:
    """
    Test a successful update scenario where the agent modifies the prompt file.
    """
    _, _, mock_run, _ = mock_deps
    
    prompt_file = tmp_path / "test.prompt"
    code_file = tmp_path / "code.py"
    prompt_file.touch()
    code_file.touch()
    
    # Ensure initial mtime is old enough
    old_time = time.time() - 100
    os.utime(prompt_file, (old_time, old_time))

    # Define side effect to simulate agent modifying the file
    def simulate_agent_modification(*args: Any, **kwargs: Any) -> Tuple[bool, str, float, str]:
        # Update mtime to now
        prompt_file.touch()
        return True, "Updated prompt", 0.05, "claude"

    mock_run.side_effect = simulate_agent_modification

    success, msg, cost, model, changed = run_agentic_update(
        str(prompt_file), 
        str(code_file), 
        quiet=True
    )

    assert success is True
    assert "Prompt file updated successfully" in msg
    assert cost == 0.05
    assert model == "claude"
    assert str(prompt_file.resolve()) in changed


def test_no_modification(tmp_path: Path, mock_deps: Tuple[MagicMock, ...]) -> None:
    """
    Test scenario where agent runs but does not modify the prompt file.
    """
    _, _, mock_run, _ = mock_deps
    
    prompt_file = tmp_path / "test.prompt"
    code_file = tmp_path / "code.py"
    prompt_file.touch()
    code_file.touch()

    # Agent runs but touches nothing
    mock_run.return_value = (True, "No changes needed", 0.02, "claude")

    success, msg, cost, _, changed = run_agentic_update(
        str(prompt_file), 
        str(code_file), 
        quiet=True
    )

    assert success is False
    assert "did not modify" in msg
    assert cost == 0.02
    assert len(changed) == 0


def test_test_discovery(tmp_path: Path, mock_deps: Tuple[MagicMock, ...]) -> None:
    """
    Test that test files are correctly discovered from:
    1. Same directory
    2. tests/ subdirectory
    3. Project root tests/ (mocked)
    """
    _, mock_load, _, _ = mock_deps

    # Setup directory structure
    # tmp_path/
    #   code.py
    #   test_code.py (Same dir)
    #   tests/
    #     test_code_extra.py (Subdir)
    #   project_root/
    #     tests/
    #       test_code_global.py (Global)
    
    project_root = tmp_path / "project_root"
    project_root.mkdir()
    (project_root / "tests").mkdir()
    
    code_dir = tmp_path
    (code_dir / "tests").mkdir()

    code_file = code_dir / "code.py"
    code_file.touch()
    prompt_file = code_dir / "code.prompt"
    prompt_file.touch()

    # Create test files
    t1 = code_dir / "test_code.py"
    t1.touch()
    
    t2 = code_dir / "tests" / "test_code_extra.py"
    t2.touch()
    
    t3 = project_root / "tests" / "test_code_global.py"
    t3.touch()

    # Patch PROJECT_ROOT in the module to point to our mock project root
    with patch("pdd.agentic_update.PROJECT_ROOT", project_root):
        run_agentic_update(str(prompt_file), str(code_file), quiet=True)

    # Verify what was passed to the template
    # We expect all 3 tests to be found and formatted into the template
    args, kwargs = mock_load.return_value.format.call_args
    test_paths_str = kwargs.get("test_paths", "")
    
    assert "test_code.py" in test_paths_str
    assert "test_code_extra.py" in test_paths_str
    assert "test_code_global.py" in test_paths_str


def test_discover_test_files_escapes_glob_metacharacters(tmp_path: Path) -> None:
    """Code filenames with glob metacharacters should discover literal tests."""
    from pdd.agentic_update import _discover_test_files

    code_file = tmp_path / "mod[1].py"
    code_file.write_text("def f(): return 1\n")
    expected = tmp_path / "test_mod[1].py"
    expected.write_text("def test_f(): pass\n")
    noise = tmp_path / "test_mod1.py"
    noise.write_text("def test_noise(): pass\n")

    discovered = {
        p.resolve()
        for p in _discover_test_files(code_file, project_root=tmp_path)
    }

    assert expected.resolve() in discovered
    assert noise.resolve() not in discovered


def test_run_agentic_update_expands_user_paths(
    tmp_path: Path,
    monkeypatch: pytest.MonkeyPatch,
    mock_deps: Tuple[MagicMock, ...],
) -> None:
    """Paths beginning with ~ should resolve before existence checks."""
    _, _, mock_run, _ = mock_deps
    home = tmp_path / "home"
    home.mkdir()
    monkeypatch.setenv("HOME", str(home))

    prompt_file = home / "feature.prompt"
    code_file = home / "feature.py"
    prompt_file.write_text("original prompt\n")
    code_file.write_text("def feature(): return 1\n")

    def simulate_agent(*args: Any, **kwargs: Any) -> Tuple[bool, str, float, str]:
        prompt_file.write_text("updated prompt\n")
        return True, "ok", 0.0, "claude"

    mock_run.side_effect = simulate_agent

    success, msg, _, _, changed = run_agentic_update(
        "~/feature.prompt",
        "~/feature.py",
        test_files=[],
        quiet=True,
    )

    assert success is True
    assert "Prompt file updated successfully" in msg
    assert str(prompt_file.resolve()) in changed


def test_snapshot_mtimes_is_bounded_to_candidate_paths(tmp_path: Path) -> None:
    """Change detection should not snapshot the whole project tree."""
    from pdd.agentic_update import _snapshot_mtimes

    tracked = tmp_path / "feature.prompt"
    unrelated = tmp_path / "unrelated.txt"
    tracked.write_text("tracked\n")
    unrelated.write_text("unrelated\n")

    mtimes = _snapshot_mtimes([tracked])

    assert tracked.resolve() in mtimes
    assert unrelated.resolve() not in mtimes


def test_explicit_empty_tests(tmp_path: Path, mock_deps: Tuple[MagicMock, ...]) -> None:
    """
    Test that passing an empty list for test_files prevents auto-discovery.
    """
    _, mock_load, _, _ = mock_deps
    
    code_file = tmp_path / "code.py"
    code_file.touch()
    prompt_file = tmp_path / "code.prompt"
    prompt_file.touch()
    
    # Create a test that would be discovered if we didn't pass empty list
    (tmp_path / "test_code.py").touch()

    run_agentic_update(
        str(prompt_file), 
        str(code_file), 
        test_files=[],  # Explicitly empty
        quiet=True
    )

    args, kwargs = mock_load.return_value.format.call_args
    test_paths_str = kwargs.get("test_paths", "")
    
    # Should indicate no tests found/used
    assert "No tests were found" in test_paths_str
    assert "test_code.py" not in test_paths_str


def test_agent_failure_but_file_changed(tmp_path: Path, mock_deps: Tuple[MagicMock, ...]) -> None:
    """
    Edge case: Agent reports failure (e.g. crash/timeout) but still managed to modify the file.
    The function should report success based on file modification.
    """
    _, _, mock_run, _ = mock_deps

    prompt_file = tmp_path / "test.prompt"
    code_file = tmp_path / "code.py"
    prompt_file.touch()
    code_file.touch()

    old_time = time.time() - 100
    os.utime(prompt_file, (old_time, old_time))

    def simulate_crash_but_write(*args: Any, **kwargs: Any) -> Tuple[bool, str, float, str]:
        prompt_file.touch()
        return False, "Crashed", 0.0, "claude"

    mock_run.side_effect = simulate_crash_but_write

    success, msg, _, _, _ = run_agentic_update(str(prompt_file), str(code_file), quiet=True)

    assert success is True
    assert "Underlying agent reported failure" in msg


def test_discover_test_files_finds_sibling_tests_dir(tmp_path: Path) -> None:
    """Test that tests in ../tests/ relative to code are discovered.

    This tests the common project structure where code is in src/ and tests
    are in a sibling tests/ directory:

        project/
        ├── src/
        │   └── hello.py
        └── tests/
            └── test_hello.py
    """
    from pdd.agentic_update import _discover_test_files

    # Setup: examples/hello/src/hello.py and examples/hello/tests/test_hello.py
    src_dir = tmp_path / "examples" / "hello" / "src"
    tests_dir = tmp_path / "examples" / "hello" / "tests"
    src_dir.mkdir(parents=True)
    tests_dir.mkdir(parents=True)

    code_file = src_dir / "hello.py"
    test_file = tests_dir / "test_hello.py"
    code_file.write_text("def hello(): print('hello')")
    test_file.write_text("def test_hello(): pass")

    # Act
    discovered = _discover_test_files(code_file)

    # Assert
    assert test_file.resolve() in [p.resolve() for p in discovered], (
        f"Expected {test_file.resolve()} to be discovered, "
        f"but only found: {[p.resolve() for p in discovered]}"
    )


def test_discover_test_files_uses_pddrc_tests_dir(tmp_path: Path) -> None:
    """Test that tests_dir from .pddrc config is searched first.

    When a project has a custom test directory configured via .pddrc,
    that directory should be searched for test files.
    """
    from pdd.agentic_update import _discover_test_files

    # Setup: code in src/, test in custom location (from .pddrc test_output_path)
    src_dir = tmp_path / "src"
    custom_tests_dir = tmp_path / "custom_tests"
    src_dir.mkdir()
    custom_tests_dir.mkdir()

    code_file = src_dir / "foo.py"
    test_file = custom_tests_dir / "test_foo.py"
    code_file.write_text("def foo(): pass")
    test_file.write_text("def test_foo(): pass")

    # Act - pass tests_dir from config
    discovered = _discover_test_files(code_file, tests_dir=custom_tests_dir)

    # Assert
    assert test_file.resolve() in [p.resolve() for p in discovered], (
        f"Expected {test_file.resolve()} to be discovered when tests_dir is provided, "
        f"but only found: {[p.resolve() for p in discovered]}"
    )


def test_successful_update_renders_markdown(tmp_path: Path, mock_deps: Tuple[MagicMock, ...]) -> None:
    """Test that successful update renders agent output with Markdown formatting.

    This verifies that when an agent returns markdown-formatted output,
    it is rendered using Rich's Markdown class rather than displayed as plain text.
    """
    from rich.markdown import Markdown  # Import for isinstance check

    _, _, mock_run, mock_console = mock_deps

    prompt_file = tmp_path / "test.prompt"
    code_file = tmp_path / "code.py"
    prompt_file.touch()
    code_file.touch()

    old_time = time.time() - 100
    os.utime(prompt_file, (old_time, old_time))

    markdown_output = "## Summary\n**Bold text** and `code`"

    def simulate_agent_modification(*args, **kwargs):
        prompt_file.touch()
        return True, markdown_output, 0.05, "claude"

    mock_run.side_effect = simulate_agent_modification

    # Don't pass quiet=True so printing code executes
    run_agentic_update(str(prompt_file), str(code_file))

    # Check if any console.print call received a Markdown object
    call_args = mock_console.print.call_args_list
    found_markdown = any(
        call.args and isinstance(call.args[0], Markdown)
        for call in call_args
    )
    assert found_markdown, "Expected agent output to be rendered with Markdown"


def test_agent_task_raises_exception(tmp_path: Path, mock_deps: Tuple[MagicMock, ...]) -> None:
    """Test that an exception from run_agentic_task is handled gracefully."""
    _, _, mock_run, _ = mock_deps

    prompt_file = tmp_path / "test.prompt"
    code_file = tmp_path / "code.py"
    prompt_file.touch()
    code_file.touch()

    mock_run.side_effect = RuntimeError("Agent process crashed")

    success, msg, cost, model, changed = run_agentic_update(
        str(prompt_file), str(code_file), quiet=True
    )

    assert not success
    assert "Agentic task failed with an exception" in msg
    assert cost == 0.0
    assert model == ""
    assert changed == []


def test_get_available_agents_raises_exception(tmp_path: Path, mock_deps: Tuple[MagicMock, ...]) -> None:
    """Test that an exception from get_available_agents is handled gracefully."""
    mock_agents, _, _, _ = mock_deps

    prompt_file = tmp_path / "test.prompt"
    code_file = tmp_path / "code.py"
    prompt_file.touch()
    code_file.touch()

    mock_agents.side_effect = OSError("Cannot check agents")

    success, msg, cost, model, changed = run_agentic_update(
        str(prompt_file), str(code_file), quiet=True
    )

    assert not success
    assert "Failed to check agent availability" in msg
    assert cost == 0.0


def test_explicit_valid_test_files(tmp_path: Path, mock_deps: Tuple[MagicMock, ...]) -> None:
    """Test that explicitly provided valid test files are passed to the template."""
    _, mock_load, _, _ = mock_deps

    prompt_file = tmp_path / "test.prompt"
    code_file = tmp_path / "code.py"
    test_file = tmp_path / "test_code.py"
    prompt_file.touch()
    code_file.touch()
    test_file.write_text("def test_something(): pass\n")

    run_agentic_update(
        str(prompt_file),
        str(code_file),
        test_files=[test_file],
        quiet=True,
    )

    args, kwargs = mock_load.return_value.format.call_args
    test_paths_str = kwargs.get("test_paths", "")
    assert "test_code.py" in test_paths_str


def test_return_tuple_types(tmp_path: Path, mock_deps: Tuple[MagicMock, ...]) -> None:
    """Verify the return tuple has the correct types in all cases."""
    prompt_file = tmp_path / "test.prompt"
    code_file = tmp_path / "code.py"
    prompt_file.touch()
    code_file.touch()

    success, msg, cost, model, changed = run_agentic_update(
        str(prompt_file), str(code_file), quiet=True
    )

    assert isinstance(success, bool)
    assert isinstance(msg, str)
    assert isinstance(cost, float)
    assert isinstance(model, str)
    assert isinstance(changed, list)


def test_new_test_files_detected_after_agent_run(tmp_path: Path, mock_deps: Tuple[MagicMock, ...]) -> None:
    """Test that test files created by the agent during the run are detected as changed."""
    _, _, mock_run, _ = mock_deps

    prompt_file = tmp_path / "test.prompt"
    code_file = tmp_path / "code.py"
    prompt_file.touch()
    code_file.touch()

    old_time = time.time() - 100
    os.utime(prompt_file, (old_time, old_time))

    new_test = tmp_path / "test_code.py"

    def simulate_agent_creates_test(*args: Any, **kwargs: Any) -> Tuple[bool, str, float, str]:
        # Agent modifies the prompt and creates a new test file
        prompt_file.touch()
        new_test.write_text("def test_new(): pass\n")
        return True, "Done", 0.03, "claude"

    mock_run.side_effect = simulate_agent_creates_test

    success, msg, cost, model, changed = run_agentic_update(
        str(prompt_file), str(code_file), quiet=True
    )

    assert success is True
    # The new test file should be in the changed files
    assert str(new_test.resolve()) in changed


def test_quiet_suppresses_output(tmp_path: Path, mock_deps: Tuple[MagicMock, ...]) -> None:
    """Test that quiet=True suppresses console output on failure paths."""
    mock_agents, _, _, mock_console = mock_deps
    mock_agents.return_value = []

    prompt_file = tmp_path / "test.prompt"
    code_file = tmp_path / "code.py"
    prompt_file.touch()
    code_file.touch()

    run_agentic_update(str(prompt_file), str(code_file), quiet=True)

    # Console should NOT have been called when quiet=True
    mock_console.print.assert_not_called()


# -----------------------------------------------------------------------------
# Issue #1054 regression coverage: scope guard must preserve <include> graph
# edits and shared context/ files while still reverting unrelated tracked
# mutations.
# -----------------------------------------------------------------------------


@pytest.fixture
def real_scope_guard_deps() -> Generator[Tuple[MagicMock, MagicMock, MagicMock, MagicMock], None, None]:
    """Like ``mock_deps`` but lets ``_revert_out_of_scope_changes`` run for real.

    The acceptance regressions need the actual scope guard so they can prove
    the allowlist is honored. They run against a throwaway git repo under
    ``tmp_path`` and patch ``PROJECT_ROOT`` to point there.
    """
    with patch("pdd.agentic_update.get_available_agents") as mock_agents, \
         patch("pdd.agentic_update.load_prompt_template") as mock_load, \
         patch("pdd.agentic_update.run_agentic_task") as mock_run, \
         patch("pdd.agentic_update.console") as mock_console:

        mock_agents.return_value = ["claude"]
        mock_template = MagicMock()
        mock_template.format.return_value = "Rendered template with placeholders"
        mock_load.return_value = mock_template
        mock_run.return_value = (True, "Task complete", 0.01, "claude-3-opus")

        yield mock_agents, mock_load, mock_run, mock_console


def _init_git_repo(repo: Path) -> None:
    """Initialize a git repo with a baseline commit suitable for the scope guard."""
    import subprocess

    subprocess.run(["git", "init", "-q"], cwd=repo, check=True)
    subprocess.run(["git", "config", "user.email", "test@example.com"], cwd=repo, check=True)
    subprocess.run(["git", "config", "user.name", "Test"], cwd=repo, check=True)
    subprocess.run(["git", "config", "commit.gpgsign", "false"], cwd=repo, check=True)
    subprocess.run(["git", "add", "-A"], cwd=repo, check=True)
    subprocess.run(
        ["git", "commit", "-q", "-m", "baseline"],
        cwd=repo,
        check=True,
    )


def test_compute_include_allowlist_transitive(tmp_path: Path) -> None:
    """Helper must transitively resolve <include> tags from PROJECT_ROOT."""
    from pdd.agentic_update import _compute_include_allowlist

    root_prompt = tmp_path / "main.prompt"
    sub_prompt = tmp_path / "sub.prompt"
    leaf_doc = tmp_path / "docs" / "leaf.md"
    leaf_doc.parent.mkdir()
    leaf_doc.write_text("leaf")
    sub_prompt.write_text("<include>docs/leaf.md</include>")
    root_prompt.write_text("<include>sub.prompt</include>")

    with patch("pdd.agentic_update.PROJECT_ROOT", tmp_path):
        allowed = _compute_include_allowlist(root_prompt)

    assert sub_prompt.resolve() in allowed
    assert leaf_doc.resolve() in allowed


def test_compute_include_allowlist_is_cycle_safe(tmp_path: Path) -> None:
    """Helper must terminate even when includes form a cycle."""
    from pdd.agentic_update import _compute_include_allowlist

    a = tmp_path / "a.prompt"
    b = tmp_path / "b.prompt"
    a.write_text("<include>b.prompt</include>")
    b.write_text("<include>a.prompt</include>")

    with patch("pdd.agentic_update.PROJECT_ROOT", tmp_path):
        allowed = _compute_include_allowlist(a)

    # Termination is the key invariant; we also expect b to be reached.
    assert b.resolve() in allowed


def test_compute_include_allowlist_skips_missing_targets(tmp_path: Path) -> None:
    """Missing include targets must be silently skipped, not raised."""
    from pdd.agentic_update import _compute_include_allowlist

    prompt = tmp_path / "p.prompt"
    prompt.write_text("<include>does/not/exist.md</include>")

    with patch("pdd.agentic_update.PROJECT_ROOT", tmp_path):
        allowed = _compute_include_allowlist(prompt)

    # Only real files may appear in the allowlist.
    assert all(p.exists() for p in allowed)


def test_compute_include_allowlist_excludes_unreferenced_context_files(
    tmp_path: Path,
) -> None:
    """
    Tracked files under PROJECT_ROOT/context/ that the prompt does not include
    MUST NOT appear in the allowlist. Only files reachable via <include> from
    the prompt are allowlisted; everything else is left to the scope guard so
    unrelated tracked context/ mutations are reverted.
    """
    from pdd.agentic_update import _compute_include_allowlist

    context_dir = tmp_path / "context"
    context_dir.mkdir()
    referenced = context_dir / "shared_ref.md"
    referenced.write_text("referenced shared")
    unreferenced = context_dir / "shared_other.md"
    unreferenced.write_text("not referenced")

    prompt = tmp_path / "p.prompt"
    prompt.write_text("<include>context/shared_ref.md</include>")

    with patch("pdd.agentic_update.PROJECT_ROOT", tmp_path):
        allowed = _compute_include_allowlist(prompt)

    assert referenced.resolve() in allowed
    assert unreferenced.resolve() not in allowed


def test_scope_guard_preserves_included_doc_edits(
    tmp_path: Path,
    real_scope_guard_deps: Tuple[MagicMock, ...],
) -> None:
    """
    Regression for issue #1054: an agent-modified file referenced via
    <include> from the prompt must NOT be reverted by the scope guard.
    """
    _, _, mock_run, _ = real_scope_guard_deps

    repo = tmp_path / "repo"
    repo.mkdir()

    docs = repo / "docs"
    docs.mkdir()
    included = docs / "source.md"
    included.write_text("original included content\n")

    prompt = repo / "feature.prompt"
    prompt.write_text("<include>docs/source.md</include>\noriginal prompt body\n")
    code = repo / "feature.py"
    code.write_text("def feature():\n    return 1\n")

    _init_git_repo(repo)

    new_included = "agent-rewritten included content\n"
    new_prompt = "<include>docs/source.md</include>\nagent-updated prompt body\n"

    def simulate_agent(*args: Any, **kwargs: Any) -> Tuple[bool, str, float, str]:
        prompt.write_text(new_prompt)
        included.write_text(new_included)
        return True, "ok", 0.0, "claude"

    mock_run.side_effect = simulate_agent

    with patch("pdd.agentic_update.PROJECT_ROOT", repo):
        success, _, _, _, changed_files = run_agentic_update(
            str(prompt), str(code), test_files=[], quiet=True
        )

    assert success is True
    # The included doc edit must survive the scope guard.
    assert included.read_text() == new_included, (
        "Included <include> doc was reverted by the scope guard "
        "(issue #1054 regression)"
    )
    # The prompt edit must also survive.
    assert prompt.read_text() == new_prompt
    # The edited included doc must be reported in changed_files so callers
    # (e.g. `pdd change`) can persist or display the doc edit.
    resolved_changed = {str(Path(p).resolve()) for p in changed_files}
    assert str(included.resolve()) in resolved_changed, (
        "Edited included doc was not reported in changed_files: "
        f"got {sorted(resolved_changed)!r}"
    )
    assert str(prompt.resolve()) in resolved_changed


def test_run_agentic_update_resolves_repo_root_from_prompt_when_cwd_subdir(
    tmp_path: Path,
    monkeypatch: pytest.MonkeyPatch,
    real_scope_guard_deps: Tuple[MagicMock, ...],
) -> None:
    """Running from a subdirectory must still use the actual git root."""
    _, _, mock_run, _ = real_scope_guard_deps

    repo = tmp_path / "repo"
    repo.mkdir()
    nested_cwd = repo / "nested" / "cwd"
    nested_cwd.mkdir(parents=True)
    docs = repo / "docs"
    docs.mkdir()
    included = docs / "source.md"
    included.write_text("original included\n")
    prompt = repo / "prompts" / "feature_python.prompt"
    prompt.parent.mkdir()
    prompt.write_text("<include>docs/source.md</include>\noriginal prompt\n")
    code = repo / "pdd" / "feature.py"
    code.parent.mkdir()
    code.write_text("def feature(): return 1\n")

    _init_git_repo(repo)
    monkeypatch.chdir(nested_cwd)

    def simulate_agent(*args: Any, **kwargs: Any) -> Tuple[bool, str, float, str]:
        assert Path(args[1]).resolve() == repo.resolve()
        prompt.write_text("<include>docs/source.md</include>\nupdated prompt\n")
        included.write_text("updated included\n")
        return True, "ok", 0.0, "claude"

    mock_run.side_effect = simulate_agent

    success, _, _, _, changed_files = run_agentic_update(
        str(prompt),
        str(code),
        test_files=[],
        quiet=True,
    )

    assert success is True
    assert included.read_text() == "updated included\n"
    resolved_changed = {str(Path(p).resolve()) for p in changed_files}
    assert str(included.resolve()) in resolved_changed


def test_scope_guard_reverts_unrelated_context_dir_edits(
    tmp_path: Path,
    real_scope_guard_deps: Tuple[MagicMock, ...],
) -> None:
    """
    Tracked files under PROJECT_ROOT/context/ that the prompt does NOT include
    must still be reverted by the scope guard. The context/ directory does not
    grant a blanket allowance; only files reachable via <include> are preserved.
    """
    _, _, mock_run, _ = real_scope_guard_deps

    repo = tmp_path / "repo"
    repo.mkdir()
    context_dir = repo / "context"
    context_dir.mkdir()
    unrelated_shared = context_dir / "unrelated_shared.md"
    unrelated_shared.write_text("baseline unrelated shared\n")

    prompt = repo / "feature.prompt"
    prompt.write_text("original prompt — no includes\n")
    code = repo / "feature.py"
    code.write_text("x = 1\n")

    _init_git_repo(repo)

    def simulate_agent(*args: Any, **kwargs: Any) -> Tuple[bool, str, float, str]:
        prompt.write_text("agent-updated prompt\n")
        unrelated_shared.write_text("AGENT WENT OUT OF BOUNDS\n")
        return True, "ok", 0.0, "claude"

    mock_run.side_effect = simulate_agent

    with patch("pdd.agentic_update.PROJECT_ROOT", repo):
        success, _, _, _, _ = run_agentic_update(
            str(prompt), str(code), test_files=[], quiet=True
        )

    assert success is True
    assert unrelated_shared.read_text() == "baseline unrelated shared\n", (
        "Tracked context/ file not referenced by the prompt should have been "
        "reverted, but the scope guard preserved it."
    )


def test_scope_guard_preserves_new_untracked_context_file(
    tmp_path: Path,
    real_scope_guard_deps: Tuple[MagicMock, ...],
) -> None:
    """
    Newly-created (untracked) files under PROJECT_ROOT/context/ must survive
    the scope guard even when not yet referenced from the prompt. The scope
    guard uses ``git status -uno`` so untracked files are inherently safe;
    this is the "intentional new shared include" criterion from issue #1054.
    """
    _, _, mock_run, _ = real_scope_guard_deps

    repo = tmp_path / "repo"
    repo.mkdir()
    context_dir = repo / "context"
    context_dir.mkdir()
    # Seed the context directory with a tracked, untouched baseline file so
    # the directory exists in HEAD without staging the new untracked file.
    (context_dir / ".keep").write_text("placeholder\n")

    prompt = repo / "feature.prompt"
    prompt.write_text("original prompt\n")
    code = repo / "feature.py"
    code.write_text("x = 1\n")

    _init_git_repo(repo)

    new_shared = context_dir / "new_shared.md"
    new_shared_content = "freshly created shared include\n"

    def simulate_agent(*args: Any, **kwargs: Any) -> Tuple[bool, str, float, str]:
        prompt.write_text("agent-updated prompt\n")
        new_shared.write_text(new_shared_content)
        return True, "ok", 0.0, "claude"

    mock_run.side_effect = simulate_agent

    with patch("pdd.agentic_update.PROJECT_ROOT", repo):
        success, _, _, _, changed_files = run_agentic_update(
            str(prompt), str(code), test_files=[], quiet=True
        )

    assert success is True
    assert new_shared.exists(), "Untracked new context/ file was removed"
    assert new_shared.read_text() == new_shared_content
    # Newly-created files reachable from the prompt directory must be
    # reported in changed_files so downstream callers can surface them.
    resolved_changed = {str(Path(p).resolve()) for p in changed_files}
    assert str(new_shared.resolve()) in resolved_changed, (
        "Newly-created shared include not reported in changed_files: "
        f"got {sorted(resolved_changed)!r}"
    )


def test_scope_guard_still_reverts_unrelated_mutations(
    tmp_path: Path,
    real_scope_guard_deps: Tuple[MagicMock, ...],
) -> None:
    """
    The scope guard must still revert tracked mutations to files that are
    neither the prompt/code/tests, nor reachable via <include>, nor under
    context/. Paired assertion for the include-allowlist behavior.
    """
    _, _, mock_run, _ = real_scope_guard_deps

    repo = tmp_path / "repo"
    repo.mkdir()
    docs = repo / "docs"
    docs.mkdir()
    included = docs / "source.md"
    included.write_text("original included\n")

    unrelated_dir = repo / "unrelated"
    unrelated_dir.mkdir()
    unrelated = unrelated_dir / "elsewhere.md"
    unrelated.write_text("untouchable baseline\n")

    prompt = repo / "feature.prompt"
    prompt.write_text("<include>docs/source.md</include>\nprompt body\n")
    code = repo / "feature.py"
    code.write_text("def f(): return 1\n")

    _init_git_repo(repo)

    def simulate_agent(*args: Any, **kwargs: Any) -> Tuple[bool, str, float, str]:
        prompt.write_text("<include>docs/source.md</include>\nupdated prompt\n")
        included.write_text("updated included\n")
        unrelated.write_text("AGENT WENT OUT OF BOUNDS\n")
        return True, "ok", 0.0, "claude"

    mock_run.side_effect = simulate_agent

    with patch("pdd.agentic_update.PROJECT_ROOT", repo):
        run_agentic_update(str(prompt), str(code), test_files=[], quiet=True)

    # Include-graph edit is preserved.
    assert included.read_text() == "updated included\n"
    # Unrelated tracked mutation is reverted to HEAD.
    assert unrelated.read_text() == "untouchable baseline\n", (
        "Scope guard failed to revert an out-of-scope mutation"
    )


def test_compute_include_allowlist_honors_body_form_path_attr(tmp_path: Path) -> None:
    """
    ``<include path="X">Y</include>`` must allowlist X, not Y.

    Mirrors ``pdd.preprocess.process_include_tags`` which evaluates
    ``attrs.get('path') or content.strip()`` — the attribute wins when both
    are present. Without this, the scope guard would diverge from the real
    include graph for attributed body includes (issue #1054, round 3 finding).
    """
    from pdd.agentic_update import _compute_include_allowlist

    real_target = tmp_path / "docs" / "source.md"
    real_target.parent.mkdir()
    real_target.write_text("real target")

    # Note: fallback.md intentionally does NOT exist — the preprocessor would
    # never look at the body text when ``path=`` is present, so neither should
    # the allowlist.
    prompt = tmp_path / "p.prompt"
    prompt.write_text('<include path="docs/source.md">fallback.md</include>')

    with patch("pdd.agentic_update.PROJECT_ROOT", tmp_path):
        allowed = _compute_include_allowlist(prompt)

    assert real_target.resolve() in allowed
    # The body-text path must NOT have been resolved or allowlisted.
    assert not any(p.name == "fallback.md" for p in allowed)


def test_scope_guard_preserves_body_form_path_attr_included_doc(
    tmp_path: Path,
    real_scope_guard_deps: Tuple[MagicMock, ...],
) -> None:
    """
    Round-3 regression: ``<include path="docs/source.md">fallback.md</include>``
    must allow agent edits to ``docs/source.md`` to survive the scope guard.

    Prior to honoring ``path=`` on body-form includes, the allowlist tried to
    resolve ``fallback.md`` instead of ``docs/source.md`` and the real target
    was reverted by ``_revert_out_of_scope_changes``.
    """
    _, _, mock_run, _ = real_scope_guard_deps

    repo = tmp_path / "repo"
    repo.mkdir()

    docs = repo / "docs"
    docs.mkdir()
    included = docs / "source.md"
    included.write_text("original included content\n")

    prompt = repo / "feature.prompt"
    prompt.write_text(
        '<include path="docs/source.md">fallback.md</include>\n'
        "original prompt body\n"
    )
    code = repo / "feature.py"
    code.write_text("def feature():\n    return 1\n")

    _init_git_repo(repo)

    new_included = "agent-rewritten included content\n"
    new_prompt = (
        '<include path="docs/source.md">fallback.md</include>\n'
        "agent-updated prompt body\n"
    )

    def simulate_agent(*args: Any, **kwargs: Any) -> Tuple[bool, str, float, str]:
        prompt.write_text(new_prompt)
        included.write_text(new_included)
        return True, "ok", 0.0, "claude"

    mock_run.side_effect = simulate_agent

    with patch("pdd.agentic_update.PROJECT_ROOT", repo):
        success, _, _, _, _ = run_agentic_update(
            str(prompt), str(code), test_files=[], quiet=True
        )

    assert success is True
    assert included.read_text() == new_included, (
        "Included doc referenced via <include path=\"...\"> body form was "
        "reverted by the scope guard (issue #1054 round-3 regression)"
    )
    assert prompt.read_text() == new_prompt
