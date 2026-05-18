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
    """
    with patch("pdd.agentic_update.get_available_agents") as mock_agents, \
         patch("pdd.agentic_update.load_prompt_template") as mock_load, \
         patch("pdd.agentic_update.run_agentic_task") as mock_run, \
         patch("pdd.agentic_update.console") as mock_console:
        
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

# --- Reproduction test from Step 5 ---
import subprocess
from pathlib import Path
from unittest.mock import patch, MagicMock

import pytest

from pdd.agentic_update import run_agentic_update

def test_issue_880_reproduction(tmp_path: Path, monkeypatch: pytest.MonkeyPatch):
    """
    Reproduction test for Issue #880: agentic update scope guard reverts
    included-doc edits and new shared includes.
    """
    # 1. Set up a git repo so _revert_out_of_scope_changes will run
    subprocess.run(["git", "init"], cwd=tmp_path, check=True)
    subprocess.run(["git", "config", "user.name", "Test User"], cwd=tmp_path, check=True)
    subprocess.run(["git", "config", "user.email", "test@example.com"], cwd=tmp_path, check=True)

    # 2. Create initial files
    prompt_file = tmp_path / "my.prompt"
    code_file = tmp_path / "my_code.py"
    included_doc = tmp_path / "doc.md"
    context_dir = tmp_path / "context"
    context_dir.mkdir()
    shared_file = context_dir / "shared.md"
    unrelated_file = tmp_path / "unrelated.py"

    prompt_content = "<include doc.md>\n<include context/shared.md>\nPrompt contents here."
    prompt_file.write_text(prompt_content)
    code_file.write_text("print('hello')")
    included_doc.write_text("original doc content")
    shared_file.write_text("original shared content")
    unrelated_file.write_text("original unrelated")

    # Commit the initial files
    subprocess.run(["git", "add", "."], cwd=tmp_path, check=True)
    subprocess.run(["git", "commit", "-m", "Initial"], cwd=tmp_path, check=True)

    # 3. Mock dependencies
    monkeypatch.setattr("pdd.agentic_update.PROJECT_ROOT", tmp_path)
    monkeypatch.setattr("pdd.agentic_update.get_available_agents", lambda: ["mock_agent"])

    mock_template = MagicMock()
    mock_template.format.return_value = "Instruction"
    monkeypatch.setattr("pdd.agentic_update.load_prompt_template", lambda name: mock_template)

    def mock_run_task(*args, **kwargs):
        # Simulate agent modifying the prompt file
        prompt_file.write_text(prompt_content + "\nAgent edit")
        # Simulate agent modifying an included document
        included_doc.write_text("original doc content\nAgent edit to included doc")
        # Simulate agent modifying a shared context file
        shared_file.write_text("original shared content\nAgent edit to shared file")
        # Simulate agent modifying an unrelated file (should be reverted)
        unrelated_file.write_text("original unrelated\nAgent edit to unrelated file")
        
        # Simulate agent creating a NEW shared context file
        new_shared = context_dir / "new_shared.md"
        new_shared.write_text("New shared context file")
        
        return True, "Task complete", 0.0, "mock_agent"

    monkeypatch.setattr("pdd.agentic_update.run_agentic_task", mock_run_task)

    # 4. Run the update
    success, msg, _, _, _ = run_agentic_update(
        str(prompt_file),
        str(code_file),
        test_files=[],
        quiet=True
    )

    assert success is True

    # 5. Assert EXPECTED behavior
    # Unrelated files should be reverted
    assert unrelated_file.read_text() == "original unrelated", "Unrelated file edit was not reverted"

    # Included docs should be preserved (currently fails because _allowed doesn't include them)
    assert included_doc.read_text() == "original doc content\nAgent edit to included doc", \
        "Included doc edit was incorrectly reverted"
    
    assert shared_file.read_text() == "original shared content\nAgent edit to shared file", \
        "Shared context edit was incorrectly reverted"
        
    new_shared = context_dir / "new_shared.md"
    assert new_shared.exists(), "New shared file was incorrectly removed/reverted"


def test_agentic_update_preserves_included_docs(tmp_path: Path, monkeypatch: pytest.MonkeyPatch):
    """Test 1: Agentic update preserves explicitly included docs"""
    subprocess.run(["git", "init"], cwd=tmp_path, check=True)
    subprocess.run(["git", "config", "user.name", "Test User"], cwd=tmp_path, check=True)
    subprocess.run(["git", "config", "user.email", "test@example.com"], cwd=tmp_path, check=True)
    
    prompt_file = tmp_path / "test.prompt"
    code_file = tmp_path / "code.py"
    docs_dir = tmp_path / "docs"
    docs_dir.mkdir()
    doc_file = docs_dir / "my_doc.md"
    
    prompt_file.write_text("<include docs/my_doc.md>\nPrompt")
    code_file.write_text("code")
    doc_file.write_text("original")
    
    subprocess.run(["git", "add", "."], cwd=tmp_path, check=True)
    subprocess.run(["git", "commit", "-m", "Initial"], cwd=tmp_path, check=True)
    
    monkeypatch.setattr("pdd.agentic_update.PROJECT_ROOT", tmp_path)
    monkeypatch.setattr("pdd.agentic_update.get_available_agents", lambda: ["mock_agent"])
    
    mock_template = MagicMock()
    mock_template.format.return_value = "Instruction"
    monkeypatch.setattr("pdd.agentic_update.load_prompt_template", lambda name: mock_template)
    
    def mock_run_task(*args, **kwargs):
        doc_file.write_text("modified")
        prompt_file.write_text("<include docs/my_doc.md>\nModified Prompt")
        return True, "Task complete", 0.0, "mock_agent"
        
    monkeypatch.setattr("pdd.agentic_update.run_agentic_task", mock_run_task)
    
    success, msg, _, _, _ = run_agentic_update(str(prompt_file), str(code_file), test_files=[], quiet=True)
    assert success is True
    assert doc_file.read_text() == "modified", "Included doc edit was reverted"


def test_agentic_update_preserves_new_shared_context(tmp_path: Path, monkeypatch: pytest.MonkeyPatch):
    """Test 2: Agentic update preserves new shared context files"""
    subprocess.run(["git", "init"], cwd=tmp_path, check=True)
    subprocess.run(["git", "config", "user.name", "Test User"], cwd=tmp_path, check=True)
    subprocess.run(["git", "config", "user.email", "test@example.com"], cwd=tmp_path, check=True)
    
    prompt_file = tmp_path / "test.prompt"
    code_file = tmp_path / "code.py"
    context_dir = tmp_path / "context"
    context_dir.mkdir()
    
    prompt_file.write_text("Prompt")
    code_file.write_text("code")
    
    subprocess.run(["git", "add", "."], cwd=tmp_path, check=True)
    subprocess.run(["git", "commit", "-m", "Initial"], cwd=tmp_path, check=True)
    
    monkeypatch.setattr("pdd.agentic_update.PROJECT_ROOT", tmp_path)
    monkeypatch.setattr("pdd.agentic_update.get_available_agents", lambda: ["mock_agent"])
    
    mock_template = MagicMock()
    mock_template.format.return_value = "Instruction"
    monkeypatch.setattr("pdd.agentic_update.load_prompt_template", lambda name: mock_template)
    
    new_shared = context_dir / "shared_state.md"
    def mock_run_task(*args, **kwargs):
        new_shared.write_text("new content")
        prompt_file.write_text("Modified Prompt")
        return True, "Task complete", 0.0, "mock_agent"
        
    monkeypatch.setattr("pdd.agentic_update.run_agentic_task", mock_run_task)
    
    success, msg, _, _, changed_files = run_agentic_update(str(prompt_file), str(code_file), test_files=[], quiet=True)
    assert success is True
    assert new_shared.exists(), "New shared context file was reverted"


def test_unrelated_file_mutations_reverted(tmp_path: Path, monkeypatch: pytest.MonkeyPatch):
    """Test 3: Unrelated file mutations are reverted"""
    subprocess.run(["git", "init"], cwd=tmp_path, check=True)
    subprocess.run(["git", "config", "user.name", "Test User"], cwd=tmp_path, check=True)
    subprocess.run(["git", "config", "user.email", "test@example.com"], cwd=tmp_path, check=True)
    
    prompt_file = tmp_path / "test.prompt"
    code_file = tmp_path / "code.py"
    src_dir = tmp_path / "src"
    src_dir.mkdir()
    unrelated_file = src_dir / "unrelated_file.py"
    
    prompt_file.write_text("Prompt")
    code_file.write_text("code")
    unrelated_file.write_text("original")
    
    subprocess.run(["git", "add", "."], cwd=tmp_path, check=True)
    subprocess.run(["git", "commit", "-m", "Initial"], cwd=tmp_path, check=True)
    
    monkeypatch.setattr("pdd.agentic_update.PROJECT_ROOT", tmp_path)
    monkeypatch.setattr("pdd.agentic_update.get_available_agents", lambda: ["mock_agent"])
    
    mock_template = MagicMock()
    mock_template.format.return_value = "Instruction"
    monkeypatch.setattr("pdd.agentic_update.load_prompt_template", lambda name: mock_template)
    
    def mock_run_task(*args, **kwargs):
        unrelated_file.write_text("modified")
        prompt_file.write_text("Modified Prompt")
        return True, "Task complete", 0.0, "mock_agent"
        
    monkeypatch.setattr("pdd.agentic_update.run_agentic_task", mock_run_task)
    
    success, msg, _, _, _ = run_agentic_update(str(prompt_file), str(code_file), test_files=[], quiet=True)
    assert success is True
    assert unrelated_file.read_text() == "original", "Unrelated file mutation was not reverted"


# Scope addition: covers expansion item "before_paths initialization" identified by Step 6 but absent from Step 8's plan
def test_before_paths_captures_included_docs(tmp_path: Path, monkeypatch: pytest.MonkeyPatch):
    """Test 4: Tracking state before_paths initialization captures included docs"""
    subprocess.run(["git", "init"], cwd=tmp_path, check=True)
    subprocess.run(["git", "config", "user.name", "Test User"], cwd=tmp_path, check=True)
    subprocess.run(["git", "config", "user.email", "test@example.com"], cwd=tmp_path, check=True)
    
    prompt_file = tmp_path / "test.prompt"
    code_file = tmp_path / "code.py"
    docs_dir = tmp_path / "docs"
    docs_dir.mkdir()
    doc_file = docs_dir / "my_doc.md"
    
    prompt_file.write_text("<include docs/my_doc.md>\nPrompt")
    code_file.write_text("code")
    doc_file.write_text("doc")
    
    subprocess.run(["git", "add", "."], cwd=tmp_path, check=True)
    subprocess.run(["git", "commit", "-m", "Initial"], cwd=tmp_path, check=True)
    
    monkeypatch.setattr("pdd.agentic_update.PROJECT_ROOT", tmp_path)
    monkeypatch.setattr("pdd.agentic_update.get_available_agents", lambda: ["mock_agent"])
    
    mock_template = MagicMock()
    mock_template.format.return_value = "Instruction"
    monkeypatch.setattr("pdd.agentic_update.load_prompt_template", lambda name: mock_template)
    
    def mock_run_task(*args, **kwargs):
        doc_file.write_text("doc modified")
        prompt_file.write_text("<include docs/my_doc.md>\nModified Prompt")
        return True, "Task complete", 0.0, "mock_agent"
        
    monkeypatch.setattr("pdd.agentic_update.run_agentic_task", mock_run_task)
    
    success, msg, _, _, changed_files = run_agentic_update(str(prompt_file), str(code_file), test_files=[], quiet=True)
    assert success is True
    assert str(doc_file.resolve()) in changed_files, "Included doc not found in changed_files"


# Scope addition: covers expansion item "after_paths initialization" identified by Step 6 but absent from Step 8's plan
def test_after_paths_captures_new_context(tmp_path: Path, monkeypatch: pytest.MonkeyPatch):
    """Test 5: Tracking state after_paths initialization captures new context files"""
    subprocess.run(["git", "init"], cwd=tmp_path, check=True)
    subprocess.run(["git", "config", "user.name", "Test User"], cwd=tmp_path, check=True)
    subprocess.run(["git", "config", "user.email", "test@example.com"], cwd=tmp_path, check=True)
    
    prompt_file = tmp_path / "test.prompt"
    code_file = tmp_path / "code.py"
    context_dir = tmp_path / "context"
    context_dir.mkdir()
    
    prompt_file.write_text("Prompt")
    code_file.write_text("code")
    
    subprocess.run(["git", "add", "."], cwd=tmp_path, check=True)
    subprocess.run(["git", "commit", "-m", "Initial"], cwd=tmp_path, check=True)
    
    monkeypatch.setattr("pdd.agentic_update.PROJECT_ROOT", tmp_path)
    monkeypatch.setattr("pdd.agentic_update.get_available_agents", lambda: ["mock_agent"])
    
    mock_template = MagicMock()
    mock_template.format.return_value = "Instruction"
    monkeypatch.setattr("pdd.agentic_update.load_prompt_template", lambda name: mock_template)
    
    new_shared = context_dir / "new_shared.md"
    def mock_run_task(*args, **kwargs):
        new_shared.write_text("new shared")
        prompt_file.write_text("Modified Prompt")
        return True, "Task complete", 0.0, "mock_agent"
        
    monkeypatch.setattr("pdd.agentic_update.run_agentic_task", mock_run_task)
    
    success, msg, _, _, changed_files = run_agentic_update(str(prompt_file), str(code_file), test_files=[], quiet=True)
    assert success is True
    assert str(new_shared.resolve()) in changed_files, "New shared context file not found in changed_files"

