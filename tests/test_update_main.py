import pytest
import sys
import os
from unittest.mock import patch, MagicMock, mock_open
import click
from click.testing import CliRunner

# Import the function under test from the pdd package (module named the same as the function).
from pdd.update_main import update_main

@pytest.fixture
def mock_ctx():
    """
    Provides a mock Click context with default parameters.
    You can override these params or obj items in individual tests as needed.
    """
    runner = CliRunner()
    with runner.isolated_filesystem():
        # Create a mock ctx with default params
        ctx = click.Context(click.Command("update"))
        ctx.params = {
            "force": False,
            "quiet": False
        }
        ctx.obj = {
            "strength": 0.5,
            "temperature": 0.0,
            "verbose": False
        }
        yield ctx

@pytest.fixture
def minimal_input_files():
    """
    Returns a minimal/valid set of input file paths for the function.
    """
    return {
        "input_prompt_file": "some_prompt_file.prompt",
        "modified_code_file": "modified_code.py",
        "input_code_file": "original_code.py",
    }

@pytest.fixture
def mock_construct_paths():
    """
    Provides a patch of the construct_paths function used in update_main.
    """
    with patch("pdd.update_main.construct_paths") as mock_cp:
        # Mock the return value: (input_strings, output_file_paths, language)
        mock_cp.return_value = (
            {},  # resolved_config
            {
                "input_prompt_file": "prompt content",
                "modified_code_file": "def modified_code(): pass",
                "input_code_file": "def original_code(): pass",
            },
            {"output": "updated_prompt.prompt"},
            None
        )
        yield mock_cp

@pytest.fixture
def mock_open_file():
    """
    Patches the built-in open function so no real file I/O happens.
    """
    with patch("builtins.open", mock_open()) as mock_file:
        yield mock_file

@pytest.fixture
def mock_update_prompt():
    """
    Patches the update_prompt function so it doesn't invoke external logic.
    """
    with patch("pdd.update_main.update_prompt") as mock_up:
        mock_up.return_value = ("updated prompt text", 0.123456, "test-model")
        yield mock_up

@pytest.fixture
def mock_git_update():
    """
    Patches the git_update function so it doesn't invoke Git or external logic.
    """
    with patch("pdd.update_main.git_update") as mock_gu:
        mock_gu.return_value = ("updated prompt from git", 0.654321, "git-model")
        yield mock_gu

@pytest.fixture
def mock_get_available_agents():
    """
    Patches get_available_agents to return an empty list, disabling agentic routing.
    """
    with patch("pdd.update_main.get_available_agents") as mock_ga:
        mock_ga.return_value = []
        yield mock_ga

def test_update_main_with_input_code_and_no_git(
    mock_ctx,
    minimal_input_files,
    mock_construct_paths,
    mock_update_prompt,
    mock_git_update,
    mock_open_file,
    mock_get_available_agents
):
    """
    Test that update_main correctly calls update_prompt() if git=False
    and an input code file is provided.
    """
    # Arrange
    # Ensure git=False and an input_code_file is set
    mock_ctx.params["quiet"] = False
    git = False
    output = "custom_output.prompt"

    # Act
    result = update_main(
        ctx=mock_ctx,
        input_prompt_file=minimal_input_files["input_prompt_file"],
        modified_code_file=minimal_input_files["modified_code_file"],
        input_code_file=minimal_input_files["input_code_file"],
        output=output,
        use_git=git
    )

    # Assert
    mock_construct_paths.assert_called_once()
    mock_update_prompt.assert_called_once_with(
        input_prompt="prompt content",
        input_code="def original_code(): pass",
        modified_code="def modified_code(): pass",
        strength=0.5,
        temperature=0.0,
        verbose=False,
        time=0.25
    )
    # git_update should NOT be called
    mock_git_update.assert_not_called()

    # The return value should match the mock_update_prompt return value
    assert result == ("updated prompt text", 0.123456, "test-model")

    # The open function should be called to write the updated prompt
    mock_open_file.assert_called_once_with("updated_prompt.prompt", "w")

def test_update_main_with_git_no_input_code(
    mock_ctx,
    minimal_input_files,
    mock_construct_paths,
    mock_update_prompt,
    mock_git_update,
    mock_open_file,
    mock_get_available_agents
):
    """
    Test that update_main correctly calls git_update() if git=True
    and no input_code_file is provided.
    """
    # Arrange
    # Remove input_code_file from the construct_paths dictionary to simulate using --git
    mock_construct_paths.return_value = (
        {},  # resolved_config
        {
            "input_prompt_file": "prompt content",
            "modified_code_file": "def git_modified_code(): pass",
        },
        {"output": "updated_prompt_git.prompt"},
        None
    )

    mock_ctx.params["quiet"] = False
    git = True
    output = "git_output.prompt"

    # Act
    result = update_main(
        ctx=mock_ctx,
        input_prompt_file="some_prompt_file.prompt",
        modified_code_file="modified_code.py",
        input_code_file=None,  # Not provided,
        output=output,
        use_git=git
    )

    # Assert
    mock_construct_paths.assert_called_once()
    mock_git_update.assert_called_once_with(
        input_prompt="prompt content",
        modified_code_file="modified_code.py",
        strength=0.5,
        temperature=0.0,
        verbose=False,
        time=0.25,
        simple=False,  # Agentic was not tried (no agents available)
        quiet=False,
        prompt_file="some_prompt_file.prompt",
    )
    mock_update_prompt.assert_not_called()  # update_prompt should NOT be called

    assert result == ("updated prompt from git", 0.654321, "git-model")
    mock_open_file.assert_called_once_with("updated_prompt_git.prompt", "w")

def test_update_main_with_both_git_and_input_code_returns_none(
    mock_ctx,
    minimal_input_files,
    mock_construct_paths,
    mock_update_prompt,
    mock_git_update,
    mock_get_available_agents
):
    """
    Test that providing both --git and an input_code_file returns None.
    Per the spec, errors return None instead of sys.exit(1) to allow
    orchestrating code (TUI apps, sync commands) to handle errors gracefully.
    """
    # Arrange
    mock_ctx.params["quiet"] = True  # so no output from rprint
    git = True  # also specifying input_code_file

    # Act
    result = update_main(
        ctx=mock_ctx,
        input_prompt_file=minimal_input_files["input_prompt_file"],
        modified_code_file=minimal_input_files["modified_code_file"],
        input_code_file=minimal_input_files["input_code_file"],  # This triggers the error
        output=None,
        use_git=git
    )

    # Assert
    # The function returns None on ValueError to allow orchestrator to handle gracefully
    assert result is None

@patch('pdd.update_main.resolve_prompt_code_pair')
def test_update_main_regeneration_mode(
    mock_resolve_pair,
    mock_ctx,
    mock_update_prompt,
    mock_git_update,
    mock_construct_paths,
    mock_open_file,
    mock_get_available_agents,
    monkeypatch
):
    """
    Test that providing only a modified_code_file correctly triggers
    the regeneration workflow.
    """
    # Arrange
    mock_ctx.obj["quiet"] = False
    mock_resolve_pair.return_value = ("modified_code_python.prompt", "modified_code.py")
    
    # Act
    result = update_main(
        ctx=mock_ctx,
        input_prompt_file=None,
        modified_code_file="modified_code.py",
        input_code_file=None,
        output=None,
        use_git=False
    )

    # Assert
    # 1. It should resolve the pair to find/create the prompt file
    mock_resolve_pair.assert_called_once_with("modified_code.py", False)

    # 2. It should NOT call the complex pathing logic
    mock_construct_paths.assert_not_called()

    # 3. It should call update_prompt directly in "generation" mode
    mock_update_prompt.assert_called_once()
    # We can check the args if needed, but the call itself is the main thing
    args, kwargs = mock_update_prompt.call_args
    assert kwargs['input_prompt'] == "no prompt exists yet, create a new one"
    assert kwargs['input_code'] == ""

    # 4. It should not call git_update
    mock_git_update.assert_not_called()

    # 5. It should write to the derived prompt file
    mock_open_file.assert_any_call("modified_code_python.prompt", "w")

    # 6. The result should be correct
    assert result == ("updated prompt text", 0.123456, "test-model")

def test_update_main_handles_unexpected_exception_gracefully(
    mock_ctx,
    minimal_input_files,
    mock_construct_paths,
    mock_open_file,
    mock_get_available_agents
):
    """
    Test that an unexpected exception returns None and prints an error message.
    Per the spec, errors return None instead of sys.exit(1) to allow
    orchestrating code (TUI apps, sync commands) to handle errors gracefully.
    """
    mock_ctx.params["quiet"] = True

    # Force an unexpected exception in construct_paths or subsequent code
    mock_construct_paths.side_effect = Exception("Something went wrong")

    # Act
    result = update_main(
        ctx=mock_ctx,
        input_prompt_file=minimal_input_files["input_prompt_file"],
        modified_code_file=minimal_input_files["modified_code_file"],
        input_code_file=minimal_input_files["input_code_file"],
        output=None,
        use_git=False
    )

    # Assert - function returns None on errors to allow orchestrator to handle gracefully
    assert result is None

    # The open should never be called because we failed early
    mock_open_file.assert_not_called()

# --- Tests for --repo functionality ---

import os
from pathlib import Path
import git
from pdd.update_main import find_and_resolve_all_pairs

@pytest.fixture
def mock_get_language_for_repo(monkeypatch):
    """Mocks get_language to return predictable results for repo tests."""
    def mock_func(file_path):
        if str(file_path).endswith(".py"):
            return "python"
        if str(file_path).endswith(".js"):
            return "javascript"
        return None
    monkeypatch.setattr('pdd.update_main.get_language', mock_func)

@pytest.fixture
def temp_git_repo(tmp_path, mock_get_language_for_repo):
    """Creates a temporary Git repository with a file structure for testing."""
    repo_path = tmp_path / "test_repo"
    repo_path.mkdir()
    repo = git.Repo.init(repo_path)

    (repo_path / "src").mkdir()
    (repo_path / "src" / "module1.py").write_text("def func1(): pass")
    (repo_path / "src" / "module2.js").write_text("function func2() {}")
    (repo_path / "src" / "existing_module.py").write_text("def existing(): pass")

    # Create prompts directory with existing prompt file
    (repo_path / "prompts").mkdir()
    (repo_path / "prompts" / "existing_module_python.prompt").write_text("Existing prompt.")

    # Add all files to be tracked by git
    repo.index.add([
        str(repo_path / "src" / "module1.py"),
        str(repo_path / "src" / "module2.js"),
        str(repo_path / "src" / "existing_module.py"),
        str(repo_path / "prompts" / "existing_module_python.prompt")
    ])
    repo.index.commit("Initial commit")

    # Change directory into the repo for the test
    original_cwd = os.getcwd()
    os.chdir(repo_path)
    yield repo_path
    os.chdir(original_cwd)

def test_create_and_find_prompt_code_pairs(temp_git_repo):
    """
    Test that the helper function correctly finds code files and creates missing prompts.
    With structure preservation, prompts mirror the source directory structure.
    """
    repo_path_str = str(temp_git_repo)

    # With structure preservation, prompts for files in src/ go to prompts/src/
    module1_prompt_path = temp_git_repo / "prompts" / "src" / "module1_python.prompt"
    module2_prompt_path = temp_git_repo / "prompts" / "src" / "module2_javascript.prompt"
    existing_prompt_path_nested = temp_git_repo / "prompts" / "src" / "existing_module_python.prompt"

    # Run the function
    pairs = find_and_resolve_all_pairs(repo_path_str)

    # Assert that prompts were created in the prompts/src directory
    assert module1_prompt_path.exists()
    assert module1_prompt_path.read_text() == ""
    assert module2_prompt_path.exists()
    assert module2_prompt_path.read_text() == ""
    assert existing_prompt_path_nested.exists()
    assert existing_prompt_path_nested.read_text() == ""

    # Assert that the returned pairs are correct
    expected_pairs = [
        (str(existing_prompt_path_nested), str(temp_git_repo / "src" / "existing_module.py")),
        (str(module1_prompt_path), str(temp_git_repo / "src" / "module1.py")),
        (str(module2_prompt_path), str(temp_git_repo / "src" / "module2.js")),
    ]
    assert len(pairs) == len(expected_pairs)
    assert sorted(p[1] for p in pairs) == sorted(ep[1] for ep in expected_pairs)

@patch('pdd.architecture_sync.update_architecture_from_prompt', return_value={"success": False, "updated": False, "changes": {}})
@patch('pdd.update_main.is_code_changed', return_value=(True, "no fingerprint, file in git changed set"))
@patch('pdd.update_main.get_git_changed_files', return_value=set())
@patch('pdd.update_main.update_file_pair')
def test_update_main_repo_mode_orchestration(mock_update_file_pair, mock_git_changed, mock_is_changed, mock_arch, temp_git_repo, capsys):
    """
    Test the main orchestration logic of update_main in --repo mode.
    """
    # Use a side_effect to return dynamic values based on input
    def mock_update_logic(prompt_file, code_file, ctx, repo, simple=False):
        return {
            "prompt_file": prompt_file,
            "status": "✅ Success",
            "cost": 0.01,
            "model": "mock_model",
            "error": ""
        }
    mock_update_file_pair.side_effect = mock_update_logic

    ctx = click.Context(click.Command('update'))
    ctx.obj = {"strength": 0.5, "temperature": 0.1, "verbose": False, "time": 0.25, "quiet": False}

    # Run update_main in repo mode
    result = update_main(ctx=ctx, input_prompt_file=None, modified_code_file=None, input_code_file=None, output=None, use_git=False, repo=True)

    # Assert that the update function was called for each pair (all 3 marked as changed)
    assert mock_update_file_pair.call_count == 3

    # Check the console output for the summary table
    captured = capsys.readouterr()
    assert "Repository Update Summary" in captured.out
    # With structure preservation, paths include src/
    assert "prompts/src/module1_python.prompt" in captured.out
    assert "prompts/src/module2_javascript.prompt" in captured.out
    assert "prompts/src/existing_module_python.prompt" in captured.out
    assert "Total Estimated Cost" in captured.out

    assert result is not None
    assert result[0] == "Repository update complete."


# --- Tests for .pddrc prompts_dir configuration (GitHub Issue #86) ---

def test_update_regeneration_mode_respects_pddrc_prompts_dir(tmp_path, monkeypatch):
    """
    Test that pdd update in regeneration mode uses prompts_dir from .pddrc context config.
    This is a regression test for GitHub issue #86.
    """
    from pdd.update_main import update_main

    # Setup: Create a temp directory structure with .pddrc
    repo_path = tmp_path / "test_repo"
    repo_path.mkdir()

    # Create .pddrc with context-specific prompts_dir
    pddrc_content = '''
contexts:
  backend:
    paths:
      - "backend/**"
    defaults:
      prompts_dir: "prompts/backend"
      generate_output_path: "backend"
'''
    (repo_path / ".pddrc").write_text(pddrc_content)

    # Create the backend directory and code file
    backend_dir = repo_path / "backend"
    backend_dir.mkdir()
    code_file = backend_dir / "some_module.py"
    code_file.write_text("def example(): pass")

    # Create prompts/backend directory
    prompts_backend = repo_path / "prompts" / "backend"
    prompts_backend.mkdir(parents=True)

    # Change to repo directory
    monkeypatch.chdir(repo_path)

    # Initialize git repo
    git.Repo.init(repo_path)

    # Mock update_prompt to avoid actual LLM calls
    # Mock get_language to avoid PDD_PATH dependency
    with patch("pdd.update_main.update_prompt") as mock_update_prompt, \
         patch("pdd.update_main.get_available_agents") as mock_agents, \
         patch("pdd.update_main.get_language") as mock_get_language:
        mock_update_prompt.return_value = ("generated prompt", 0.01, "mock-model")
        mock_agents.return_value = []
        mock_get_language.return_value = "python"

        ctx = click.Context(click.Command("update"))
        ctx.obj = {"strength": 0.5, "temperature": 0.0, "verbose": False, "quiet": True}

        # Act: Call update_main in regeneration mode (only code file provided)
        result = update_main(
            ctx=ctx,
            input_prompt_file=None,  # Regeneration mode
            modified_code_file=str(code_file),
            input_code_file=None,
            output=None,
            use_git=False
        )

    # Assert: Prompt should be saved to prompts/backend/, not prompts/
    expected_prompt_path = repo_path / "prompts" / "backend" / "some_module_python.prompt"
    wrong_prompt_path = repo_path / "prompts" / "some_module_python.prompt"

    assert expected_prompt_path.exists(), \
        f"Expected prompt at {expected_prompt_path}, but it was not created there. " \
        f"Wrong path exists: {wrong_prompt_path.exists()}"
    assert not wrong_prompt_path.exists(), \
        f"Prompt was created at wrong path {wrong_prompt_path} instead of {expected_prompt_path}"


def test_update_preserves_subdirectory_structure_issue_254(tmp_path, monkeypatch):
    """
    Test that pdd update preserves subdirectory structure from code file path.
    Regression test for GitHub issue #254.

    When updating pdd/commands/generate.py with generate_output_path="pdd",
    the prompt should be created at: prompts/commands/generate_python.prompt
    (preserving 'commands/' subdirectory, stripping 'pdd/' package root)
    """
    import git
    from pathlib import Path
    from unittest.mock import patch

    # Setup: Create a temp directory structure
    repo_path = tmp_path / "test_repo"
    repo_path.mkdir()

    # Create .pddrc with context that has generate_output_path
    pddrc_content = '''
contexts:
  pdd_cli:
    paths:
      - "pdd/**"
    defaults:
      generate_output_path: "pdd"
'''
    (repo_path / ".pddrc").write_text(pddrc_content)

    # Create pdd/commands/ directory and code file
    pdd_dir = repo_path / "pdd"
    pdd_dir.mkdir()
    commands_dir = pdd_dir / "commands"
    commands_dir.mkdir()
    code_file = commands_dir / "generate.py"
    code_file.write_text("def example(): pass")

    # Change to repo directory
    monkeypatch.chdir(repo_path)

    # Initialize git repo
    git.Repo.init(repo_path)

    # Mock update_prompt to avoid actual LLM calls
    # Mock get_language to avoid PDD_PATH dependency
    with patch("pdd.update_main.update_prompt") as mock_update_prompt, \
         patch("pdd.update_main.get_available_agents") as mock_agents, \
         patch("pdd.update_main.get_language") as mock_get_language:
        mock_update_prompt.return_value = ("generated prompt", 0.01, "mock-model")
        mock_agents.return_value = []
        mock_get_language.return_value = "python"

        ctx = click.Context(click.Command("update"))
        ctx.obj = {"strength": 0.5, "temperature": 0.0, "verbose": False, "quiet": True}

        # Act: Call update_main in regeneration mode (only code file provided)
        result = update_main(
            ctx=ctx,
            input_prompt_file=None,  # Regeneration mode
            modified_code_file=str(code_file),
            input_code_file=None,
            output=None,
            use_git=False
        )

    # Assert: Prompt should preserve subdirectory structure (stripping package root)
    # Expected: prompts/commands/generate_python.prompt (NOT prompts/pdd/commands/)
    expected_prompt_path = repo_path / "prompts" / "commands" / "generate_python.prompt"
    wrong_prompt_path = repo_path / "prompts" / "generate_python.prompt"

    assert expected_prompt_path.exists(), \
        f"Expected prompt at {expected_prompt_path}, but it was not created there. " \
        f"Wrong path exists: {wrong_prompt_path.exists()}"
    assert not wrong_prompt_path.exists(), \
        f"Prompt was created at wrong path {wrong_prompt_path} instead of {expected_prompt_path}"


# --- Tests for agentic update source-file mutation bug ---

def test_agentic_update_does_not_modify_source_when_output_specified(tmp_path):
    """
    When --output is specified, the agentic update path must NOT modify the
    source prompt file. Only the output path should contain the updated content.
    Regression test for: agentic update overwrites source in-place ignoring --output.
    """
    source_prompt = tmp_path / "source.prompt"
    output_prompt = tmp_path / "output.prompt"
    code_file = tmp_path / "modified_code.py"
    original_code = tmp_path / "original_code.py"

    original_content = "original prompt content\n"
    source_prompt.write_text(original_content)
    code_file.write_text("def foo(): return 42\n")
    original_code.write_text("def foo(): pass\n")

    ctx = click.Context(click.Command("update"))
    ctx.obj = {
        "strength": 0.5,
        "temperature": 0.0,
        "verbose": False,
        "time": 0.25,
        "force": False,
        "quiet": False,
    }

    with patch("pdd.update_main.get_available_agents", return_value=["anthropic"]), \
         patch("pdd.update_main.get_tests_dir_from_config", return_value=None), \
         patch("pdd.update_main.run_agentic_update") as mock_agentic:

        def agentic_side_effect(prompt_file, **kwargs):
            """Simulate agentic update modifying the prompt_file in-place."""
            Path(prompt_file).write_text("agentic modified content\n")
            return (True, "ok", 0.01, "claude", [str(prompt_file)])

        mock_agentic.side_effect = agentic_side_effect

        result = update_main(
            ctx=ctx,
            input_prompt_file=str(source_prompt),
            modified_code_file=str(code_file),
            input_code_file=str(original_code),
            output=str(output_prompt),
            use_git=False,
            simple=False,
        )

    # Source must remain unchanged
    assert source_prompt.read_text() == original_content, \
        "Source prompt file was modified by agentic update despite --output being specified"
    # Output should have the updated content
    assert output_prompt.exists(), "Output file was not created"
    assert output_prompt.read_text() == "agentic modified content\n"
    # Function should return success
    assert result is not None
    assert result[0] == "agentic modified content\n"


def test_agentic_update_failure_does_not_corrupt_source(tmp_path):
    """
    When agentic update fails after partially modifying a file, the source
    prompt must remain unchanged if --output is specified.
    """
    source_prompt = tmp_path / "source.prompt"
    output_prompt = tmp_path / "output.prompt"
    code_file = tmp_path / "modified_code.py"
    original_code = tmp_path / "original_code.py"

    original_content = "original prompt content\n"
    source_prompt.write_text(original_content)
    code_file.write_text("def foo(): return 42\n")
    original_code.write_text("def foo(): pass\n")

    ctx = click.Context(click.Command("update"))
    ctx.obj = {
        "strength": 0.5,
        "temperature": 0.0,
        "verbose": False,
        "time": 0.25,
        "force": False,
        "quiet": True,
    }

    with patch("pdd.update_main.get_available_agents", return_value=["anthropic"]), \
         patch("pdd.update_main.get_tests_dir_from_config", return_value=None), \
         patch("pdd.update_main.run_agentic_update") as mock_agentic, \
         patch("pdd.update_main.construct_paths") as mock_cp, \
         patch("pdd.update_main.update_prompt") as mock_up:

        def agentic_side_effect(prompt_file, **kwargs):
            """Simulate agentic update that modifies file then fails."""
            Path(prompt_file).write_text("partially corrupted\n")
            return (False, "agentic failed", 0.0, "claude", [])

        mock_agentic.side_effect = agentic_side_effect

        # Set up legacy fallback mocks
        mock_cp.return_value = (
            {},
            {
                "input_prompt_file": original_content,
                "modified_code_file": "def foo(): return 42\n",
                "input_code_file": "def foo(): pass\n",
            },
            {"output": str(output_prompt)},
            None
        )
        mock_up.return_value = ("legacy updated content\n", 0.02, "gpt-4")

        result = update_main(
            ctx=ctx,
            input_prompt_file=str(source_prompt),
            modified_code_file=str(code_file),
            input_code_file=str(original_code),
            output=str(output_prompt),
            use_git=False,
            simple=False,
        )

    # Source must remain unchanged even after agentic failure
    assert source_prompt.read_text() == original_content, \
        "Source prompt was corrupted by failed agentic update"


# --- Tests for issue #493: NameError when using --output with subdirectory code file ---

from pdd.update_main import resolve_prompt_code_pair


def test_resolve_prompt_code_pair_output_dir_with_subdirectory_code_file(tmp_path, monkeypatch):
    """
    Regression test for GitHub issue #493.
    resolve_prompt_code_pair() crashes with UnboundLocalError when --output is provided
    and the code file is in a subdirectory (rel_dir != "."), because context_config
    is only defined in the else branch but used unconditionally when computing code_root.
    """
    # Setup: git repo with code file in a subdirectory
    repo_path = tmp_path / "test_repo"
    repo_path.mkdir()
    sub_dir = repo_path / "backend" / "src"
    sub_dir.mkdir(parents=True)
    code_file = sub_dir / "module.py"
    code_file.write_text("def hello(): return 'world'")

    output_dir = tmp_path / "output"
    output_dir.mkdir()

    monkeypatch.chdir(repo_path)
    git.Repo.init(repo_path)

    with patch("pdd.update_main.get_language") as mock_lang:
        mock_lang.return_value = "python"

        # This should NOT raise NameError for context_config
        prompt_path, code_path = resolve_prompt_code_pair(
            str(code_file), quiet=True, output_dir=str(output_dir)
        )

    # The prompt file should be created under the output directory
    assert os.path.exists(prompt_path)
    assert Path(prompt_path).is_relative_to(output_dir)
    assert prompt_path.endswith("module_python.prompt")


def test_resolve_prompt_code_pair_output_dir_with_root_level_code_file(tmp_path, monkeypatch):
    """
    Edge case for issue #493: code file at repo root with --output should work
    (this path doesn't hit the bug since rel_dir == "." skips the code_root logic).
    """
    repo_path = tmp_path / "test_repo"
    repo_path.mkdir()
    code_file = repo_path / "module.py"
    code_file.write_text("def hello(): return 'world'")

    output_dir = tmp_path / "output"
    output_dir.mkdir()

    monkeypatch.chdir(repo_path)
    git.Repo.init(repo_path)

    with patch("pdd.update_main.get_language") as mock_lang:
        mock_lang.return_value = "python"

        prompt_path, code_path = resolve_prompt_code_pair(
            str(code_file), quiet=True, output_dir=str(output_dir)
        )

    assert os.path.exists(prompt_path)
    assert prompt_path.endswith("module_python.prompt")


def test_resolve_prompt_code_pair_no_output_dir_subdirectory_still_works(tmp_path, monkeypatch):
    """
    No-regression test for issue #493: without --output, subdirectory code files
    should still work as before (context_config is defined in else branch).
    """
    repo_path = tmp_path / "test_repo"
    repo_path.mkdir()
    sub_dir = repo_path / "backend"
    sub_dir.mkdir()
    code_file = sub_dir / "module.py"
    code_file.write_text("def hello(): return 'world'")

    monkeypatch.chdir(repo_path)
    git.Repo.init(repo_path)

    with patch("pdd.update_main.get_language") as mock_lang:
        mock_lang.return_value = "python"

        prompt_path, code_path = resolve_prompt_code_pair(
            str(code_file), quiet=True
        )

    assert os.path.exists(prompt_path)
    assert prompt_path.endswith("module_python.prompt")


# --- Tests for _extract_template_vars ---

from pdd.update_main import _extract_template_vars


class TestExtractTemplateVars:
    """Tests for reverse-matching concrete paths against templates."""

    def test_simple_name_extraction(self):
        """Extract {name} from a simple template."""
        result = _extract_template_vars(
            "frontend/src/Button.tsx",
            "frontend/src/{name}.tsx"
        )
        assert result == {"name": "Button"}

    def test_name_and_category_extraction(self):
        """Extract both {name} and {category} from a template."""
        result = _extract_template_vars(
            "frontend/src/components/billing/AutoBuy.tsx",
            "frontend/src/components/{category}/{name}.tsx"
        )
        assert result == {"category": "billing", "name": "AutoBuy"}

    def test_repeated_name_backreference(self):
        """Templates with repeated {name} should use backreferences."""
        result = _extract_template_vars(
            "frontend/src/components/billing/AutoBuy/AutoBuy.tsx",
            "frontend/src/components/{category}/{name}/{name}.tsx"
        )
        assert result == {"category": "billing", "name": "AutoBuy"}

    def test_repeated_name_mismatch_returns_none(self):
        """If repeated {name} segments differ, should not match."""
        result = _extract_template_vars(
            "frontend/src/components/billing/AutoBuy/SomethingElse.tsx",
            "frontend/src/components/{category}/{name}/{name}.tsx"
        )
        assert result is None

    def test_no_match_returns_none(self):
        """Non-matching path returns None."""
        result = _extract_template_vars(
            "backend/utils/helper.py",
            "frontend/src/{name}.tsx"
        )
        assert result is None

    def test_exact_path_no_vars(self):
        """Template without variables should match exact path."""
        result = _extract_template_vars(
            "app/api/project/route.ts",
            "app/api/project/route.ts"
        )
        assert result == {}

    def test_exact_path_no_vars_mismatch(self):
        """Template without variables should not match different path."""
        result = _extract_template_vars(
            "app/api/other/route.ts",
            "app/api/project/route.ts"
        )
        assert result is None


# --- Tests for _resolve_prompt_from_pddrc ---

from pdd.update_main import _resolve_prompt_from_pddrc


class TestResolvePromptFromPddrc:
    """Tests for template-based prompt path resolution."""

    def test_returns_none_without_pddrc(self, tmp_path, monkeypatch):
        """Should return None when no .pddrc exists."""
        repo_path = tmp_path / "repo"
        repo_path.mkdir()
        monkeypatch.chdir(repo_path)
        result = _resolve_prompt_from_pddrc(
            str(repo_path / "src" / "module.py"), str(repo_path), "python"
        )
        assert result is None

    def test_returns_none_without_outputs_config(self, tmp_path, monkeypatch):
        """Should return None when .pddrc exists but has no outputs templates."""
        repo_path = tmp_path / "repo"
        repo_path.mkdir()
        pddrc = repo_path / ".pddrc"
        pddrc.write_text("""
contexts:
  backend:
    paths:
      - "backend/**"
    defaults:
      prompts_dir: "prompts/backend"
""")
        (repo_path / "backend").mkdir()
        code_file = repo_path / "backend" / "module.py"
        code_file.write_text("def foo(): pass")
        monkeypatch.chdir(repo_path)
        result = _resolve_prompt_from_pddrc(str(code_file), str(repo_path), "python")
        assert result is None

    def test_resolves_prompt_from_template(self, tmp_path, monkeypatch):
        """Should resolve prompt path using outputs.prompt.path template."""
        repo_path = tmp_path / "repo"
        repo_path.mkdir()
        pddrc = repo_path / ".pddrc"
        pddrc.write_text("""
contexts:
  frontend:
    paths:
      - "frontend/**"
    defaults:
      outputs:
        prompt:
          path: "prompts/frontend/{category}/{name}_{language}.prompt"
        code:
          path: "frontend/src/{category}/{name}/{name}.tsx"
""")
        # Create the code file
        code_dir = repo_path / "frontend" / "src" / "billing" / "AutoBuy"
        code_dir.mkdir(parents=True)
        code_file = code_dir / "AutoBuy.tsx"
        code_file.write_text("export default function AutoBuy() {}")

        monkeypatch.chdir(repo_path)
        git.Repo.init(repo_path)

        result = _resolve_prompt_from_pddrc(
            str(code_file), str(repo_path), "TypescriptReact"
        )
        assert result is not None
        expected = str(repo_path / "prompts" / "frontend" / "billing" / "AutoBuy_TypescriptReact.prompt")
        assert result == expected

    def test_resolves_prompt_without_code_template(self, tmp_path, monkeypatch):
        """Should still resolve when outputs.code.path is missing (uses filename as name)."""
        repo_path = tmp_path / "repo"
        repo_path.mkdir()
        pddrc = repo_path / ".pddrc"
        pddrc.write_text("""
contexts:
  backend:
    paths:
      - "backend/**"
    defaults:
      outputs:
        prompt:
          path: "prompts/backend/{name}_{language}.prompt"
""")
        code_dir = repo_path / "backend"
        code_dir.mkdir()
        code_file = code_dir / "module.py"
        code_file.write_text("def foo(): pass")

        monkeypatch.chdir(repo_path)
        git.Repo.init(repo_path)

        result = _resolve_prompt_from_pddrc(
            str(code_file), str(repo_path), "python"
        )
        assert result is not None
        expected = str(repo_path / "prompts" / "backend" / "module_python.prompt")
        assert result == expected


# --- Tests for resolve_prompt_code_pair with template resolution ---

class TestResolvePromptCodePairWithTemplates:
    """Tests for resolve_prompt_code_pair using .pddrc template paths."""

    def test_uses_template_path_when_pddrc_has_outputs(self, tmp_path, monkeypatch):
        """resolve_prompt_code_pair should use .pddrc template paths when available."""
        repo_path = tmp_path / "repo"
        repo_path.mkdir()
        pddrc = repo_path / ".pddrc"
        pddrc.write_text("""
contexts:
  frontend:
    paths:
      - "frontend/**"
    defaults:
      outputs:
        prompt:
          path: "prompts/frontend/{name}_{language}.prompt"
        code:
          path: "frontend/src/app/{name}/{name}.tsx"
""")
        # Create code file at the template code path
        code_dir = repo_path / "frontend" / "src" / "app" / "billing"
        code_dir.mkdir(parents=True)
        code_file = code_dir / "billing.tsx"
        code_file.write_text("export default function Billing() {}")

        monkeypatch.chdir(repo_path)
        git.Repo.init(repo_path)

        with patch("pdd.update_main.get_language") as mock_lang:
            mock_lang.return_value = "TypescriptReact"
            prompt_path, code_path = resolve_prompt_code_pair(
                str(code_file), quiet=True
            )

        # Should use template path, NOT path-mirroring
        expected_prompt = str(repo_path / "prompts" / "frontend" / "billing_TypescriptReact.prompt")
        assert prompt_path == expected_prompt
        assert os.path.exists(prompt_path)


# --- Tests for language casing preservation ---

class TestLanguageCasingPreservation:
    """Tests for Bug 2 fix: language suffix should preserve original casing."""

    def test_resolve_prompt_code_pair_preserves_language_case(self, tmp_path, monkeypatch):
        """Language suffix should use original casing (e.g., TypescriptReact, not typescriptreact)."""
        repo_path = tmp_path / "repo"
        repo_path.mkdir()
        code_file = repo_path / "page.tsx"
        code_file.write_text("export default function Page() {}")

        monkeypatch.chdir(repo_path)
        git.Repo.init(repo_path)

        with patch("pdd.update_main.get_language") as mock_lang:
            mock_lang.return_value = "TypescriptReact"
            prompt_path, _ = resolve_prompt_code_pair(str(code_file), quiet=True)

        assert prompt_path.endswith("page_TypescriptReact.prompt")

    def test_resolve_prompt_code_pair_unknown_language_fallback(self, tmp_path, monkeypatch):
        """Unknown extension should fall back to 'unknown' language suffix."""
        repo_path = tmp_path / "repo"
        repo_path.mkdir()
        code_file = repo_path / "file.xyz"
        code_file.write_text("content")

        monkeypatch.chdir(repo_path)
        git.Repo.init(repo_path)

        with patch("pdd.update_main.get_language") as mock_lang:
            mock_lang.return_value = ""
            prompt_path, _ = resolve_prompt_code_pair(str(code_file), quiet=True)

        assert prompt_path.endswith("file_unknown.prompt")


# --- Tests for config/data file exclusion ---

class TestConfigFileExclusion:
    """Tests for Bug 3 fix: config/data files should not get prompts in repo scan."""

    def test_find_and_resolve_excludes_json_files(self, tmp_path, monkeypatch):
        """JSON files should be excluded from repo scan."""
        repo_path = tmp_path / "repo"
        repo_path.mkdir()
        git.Repo.init(repo_path)

        (repo_path / "module.py").write_text("def foo(): pass")
        (repo_path / "package.json").write_text("{}")
        (repo_path / "tsconfig.json").write_text("{}")

        monkeypatch.chdir(repo_path)

        with patch("pdd.update_main.get_language") as mock_lang:
            def lang_for_ext(ext):
                if ext == ".py":
                    return "python"
                if ext == ".json":
                    return "json"
                return None
            mock_lang.side_effect = lang_for_ext

            pairs = find_and_resolve_all_pairs(str(repo_path), quiet=True)

        code_files = [p[1] for p in pairs]
        assert any("module.py" in f for f in code_files)
        assert not any("package.json" in f for f in code_files)
        assert not any("tsconfig.json" in f for f in code_files)

    def test_find_and_resolve_excludes_css_and_html(self, tmp_path, monkeypatch):
        """CSS and HTML files should be excluded from repo scan."""
        repo_path = tmp_path / "repo"
        repo_path.mkdir()
        git.Repo.init(repo_path)

        (repo_path / "app.ts").write_text("const x = 1;")
        (repo_path / "styles.css").write_text("body {}")
        (repo_path / "index.html").write_text("<html></html>")

        monkeypatch.chdir(repo_path)

        with patch("pdd.update_main.get_language") as mock_lang:
            def lang_for_ext(ext):
                if ext == ".ts":
                    return "typescript"
                if ext == ".css":
                    return "css"
                if ext == ".html":
                    return "html"
                return None
            mock_lang.side_effect = lang_for_ext

            pairs = find_and_resolve_all_pairs(str(repo_path), quiet=True)

        code_files = [p[1] for p in pairs]
        assert any("app.ts" in f for f in code_files)
        assert not any("styles.css" in f for f in code_files)
        assert not any("index.html" in f for f in code_files)

    def test_find_and_resolve_excludes_markdown_and_yaml(self, tmp_path, monkeypatch):
        """Markdown and YAML files should be excluded from repo scan."""
        repo_path = tmp_path / "repo"
        repo_path.mkdir()
        git.Repo.init(repo_path)

        (repo_path / "app.py").write_text("pass")
        (repo_path / "README.md").write_text("# README")
        (repo_path / "config.yaml").write_text("key: value")

        monkeypatch.chdir(repo_path)

        with patch("pdd.update_main.get_language") as mock_lang:
            def lang_for_ext(ext):
                if ext == ".py":
                    return "python"
                if ext == ".md":
                    return "markdown"
                if ext == ".yaml":
                    return "yaml"
                return None
            mock_lang.side_effect = lang_for_ext

            pairs = find_and_resolve_all_pairs(str(repo_path), quiet=True)

        code_files = [p[1] for p in pairs]
        assert any("app.py" in f for f in code_files)
        assert not any("README.md" in f for f in code_files)
        assert not any("config.yaml" in f for f in code_files)

    def test_find_and_resolve_excludes_skip_filenames(self, tmp_path, monkeypatch):
        """Specific filenames like .prettierrc should be excluded."""
        repo_path = tmp_path / "repo"
        repo_path.mkdir()
        git.Repo.init(repo_path)

        (repo_path / "app.js").write_text("const x = 1;")
        (repo_path / ".prettierrc").write_text("{}")
        (repo_path / ".eslintrc").write_text("{}")
        (repo_path / ".gitignore").write_text("node_modules/")
        (repo_path / "next-env.d.ts").write_text("/// <reference />")

        monkeypatch.chdir(repo_path)

        with patch("pdd.update_main.get_language") as mock_lang:
            # get_language receives extensions, not full paths
            def lang_for_ext(ext):
                if ext == ".js":
                    return "javascript"
                if ext == ".ts":
                    return "typescript"
                return "unknown"  # Return something for all
            mock_lang.side_effect = lang_for_ext

            pairs = find_and_resolve_all_pairs(str(repo_path), quiet=True)

        code_files = [os.path.basename(p[1]) for p in pairs]
        assert "app.js" in code_files
        assert ".prettierrc" not in code_files
        assert ".eslintrc" not in code_files
        assert ".gitignore" not in code_files
        assert "next-env.d.ts" not in code_files


# --- Tests for hardened scanning filters (.stories, .test, .spec, .config, .pddignore) ---

from pdd.update_main import _has_skip_suffix, _has_meaningful_code, _is_pddignored, _load_pddignore


class TestHasSkipSuffix:
    """Unit tests for _has_skip_suffix helper."""

    def test_stories_suffix(self):
        assert _has_skip_suffix("Button.stories.tsx") is True

    def test_story_suffix(self):
        assert _has_skip_suffix("Button.story.tsx") is True

    def test_test_suffix(self):
        assert _has_skip_suffix("auth.test.ts") is True

    def test_spec_suffix(self):
        assert _has_skip_suffix("auth.spec.ts") is True

    def test_config_suffix(self):
        assert _has_skip_suffix("jest.config.ts") is True

    def test_setup_suffix(self):
        assert _has_skip_suffix("jest.setup.ts") is True

    def test_e2e_test_suffix(self):
        assert _has_skip_suffix("login.e2e.test.ts") is True

    def test_e2e_spec_suffix(self):
        assert _has_skip_suffix("login.e2e.spec.ts") is True

    def test_d_ts_suffix(self):
        assert _has_skip_suffix("firebase.d.ts") is True

    def test_normal_file_not_skipped(self):
        assert _has_skip_suffix("Button.tsx") is False

    def test_normal_py_file_not_skipped(self):
        assert _has_skip_suffix("main.py") is False

    def test_path_with_directories(self):
        assert _has_skip_suffix("src/components/Button.stories.tsx") is True


class TestHasMeaningfulCode:
    """Unit tests for _has_meaningful_code helper."""

    def test_empty_file(self, tmp_path):
        f = tmp_path / "empty.py"
        f.write_text("")
        assert _has_meaningful_code(str(f)) is False

    def test_comment_only(self, tmp_path):
        f = tmp_path / "comments.py"
        f.write_text("# just a comment\n# another comment\n")
        assert _has_meaningful_code(str(f)) is False

    def test_blank_lines_and_comments(self, tmp_path):
        f = tmp_path / "blank.py"
        f.write_text("\n\n# comment\n\n")
        assert _has_meaningful_code(str(f)) is False

    def test_real_code(self, tmp_path):
        f = tmp_path / "real.py"
        f.write_text("# header\nfrom .core import main\n")
        assert _has_meaningful_code(str(f)) is True

    def test_nonexistent_file(self):
        assert _has_meaningful_code("/nonexistent/file.py") is False


class TestSkipStoriesFiles:
    """Tests that Storybook story files are excluded from repo scan."""

    def test_skip_stories_files(self, tmp_path, monkeypatch):
        repo_path = tmp_path / "repo"
        repo_path.mkdir()
        git.Repo.init(repo_path)

        (repo_path / "Button.tsx").write_text("export function Button() {}")
        (repo_path / "Button.stories.tsx").write_text("export default { title: 'Button' }")
        (repo_path / "Card.story.tsx").write_text("export default { title: 'Card' }")

        monkeypatch.chdir(repo_path)

        with patch("pdd.update_main.get_language") as mock_lang:
            def lang_for_ext(ext):
                if ext == ".tsx":
                    return "TypescriptReact"
                return None
            mock_lang.side_effect = lang_for_ext

            pairs = find_and_resolve_all_pairs(str(repo_path), quiet=True)

        basenames = [os.path.basename(p[1]) for p in pairs]
        assert "Button.tsx" in basenames
        assert "Button.stories.tsx" not in basenames
        assert "Card.story.tsx" not in basenames


class TestSkipTestAndSpecFiles:
    """Tests that test and spec files are excluded from repo scan."""

    def test_skip_test_and_spec_files(self, tmp_path, monkeypatch):
        repo_path = tmp_path / "repo"
        repo_path.mkdir()
        git.Repo.init(repo_path)

        (repo_path / "auth.ts").write_text("export function auth() {}")
        (repo_path / "auth.test.ts").write_text("describe('auth', () => {})")
        (repo_path / "auth.spec.ts").write_text("describe('auth', () => {})")
        (repo_path / "login.e2e.test.ts").write_text("test('login', () => {})")

        monkeypatch.chdir(repo_path)

        with patch("pdd.update_main.get_language") as mock_lang:
            def lang_for_ext(ext):
                if ext == ".ts":
                    return "typescript"
                return None
            mock_lang.side_effect = lang_for_ext

            pairs = find_and_resolve_all_pairs(str(repo_path), quiet=True)

        basenames = [os.path.basename(p[1]) for p in pairs]
        assert "auth.ts" in basenames
        assert "auth.test.ts" not in basenames
        assert "auth.spec.ts" not in basenames
        assert "login.e2e.test.ts" not in basenames


class TestSkipConfigFiles:
    """Tests that config files are excluded from repo scan."""

    def test_skip_config_files(self, tmp_path, monkeypatch):
        repo_path = tmp_path / "repo"
        repo_path.mkdir()
        git.Repo.init(repo_path)

        (repo_path / "app.ts").write_text("const x = 1;")
        (repo_path / "jest.config.ts").write_text("module.exports = {}")
        (repo_path / "tailwind.config.js").write_text("module.exports = {}")
        (repo_path / "vitest.config.ts").write_text("export default {}")
        (repo_path / "mockServiceWorker.js").write_text("self.addEventListener()")

        monkeypatch.chdir(repo_path)

        with patch("pdd.update_main.get_language") as mock_lang:
            def lang_for_ext(ext):
                if ext in (".ts", ".js"):
                    return "typescript" if ext == ".ts" else "javascript"
                return None
            mock_lang.side_effect = lang_for_ext

            pairs = find_and_resolve_all_pairs(str(repo_path), quiet=True)

        basenames = [os.path.basename(p[1]) for p in pairs]
        assert "app.ts" in basenames
        assert "jest.config.ts" not in basenames
        assert "tailwind.config.js" not in basenames
        assert "vitest.config.ts" not in basenames
        assert "mockServiceWorker.js" not in basenames


class TestPddignore:
    """Tests for .pddignore support."""

    def test_pddignore_excludes_patterns(self, tmp_path, monkeypatch):
        repo_path = tmp_path / "repo"
        repo_path.mkdir()
        git.Repo.init(repo_path)

        # Create .pddignore
        (repo_path / ".pddignore").write_text(
            "# Skip UI primitives\n"
            "frontend/src/components/ui/*\n"
            "*.generated.ts\n"
        )

        # Create files
        ui_dir = repo_path / "frontend" / "src" / "components" / "ui"
        ui_dir.mkdir(parents=True)
        (ui_dir / "button.tsx").write_text("export function Button() {}")
        (repo_path / "app.ts").write_text("const x = 1;")
        (repo_path / "schema.generated.ts").write_text("export type Schema = {}")

        monkeypatch.chdir(repo_path)

        with patch("pdd.update_main.get_language") as mock_lang:
            def lang_for_ext(ext):
                if ext in (".ts", ".tsx"):
                    return "typescript"
                return None
            mock_lang.side_effect = lang_for_ext

            pairs = find_and_resolve_all_pairs(str(repo_path), quiet=True)

        basenames = [os.path.basename(p[1]) for p in pairs]
        assert "app.ts" in basenames
        assert "button.tsx" not in basenames
        assert "schema.generated.ts" not in basenames

    def test_pddignore_directory_prefix(self, tmp_path, monkeypatch):
        repo_path = tmp_path / "repo"
        repo_path.mkdir()
        git.Repo.init(repo_path)

        # Create .pddignore with directory prefix pattern
        (repo_path / ".pddignore").write_text("vendor/\n")

        vendor_dir = repo_path / "lib" / "vendor"
        vendor_dir.mkdir(parents=True)
        (vendor_dir / "dep.ts").write_text("export const dep = 1;")
        (repo_path / "app.ts").write_text("const x = 1;")

        monkeypatch.chdir(repo_path)

        with patch("pdd.update_main.get_language") as mock_lang:
            def lang_for_ext(ext):
                if ext == ".ts":
                    return "typescript"
                return None
            mock_lang.side_effect = lang_for_ext

            pairs = find_and_resolve_all_pairs(str(repo_path), quiet=True)

        basenames = [os.path.basename(p[1]) for p in pairs]
        assert "app.ts" in basenames
        assert "dep.ts" not in basenames

    def test_pddignore_missing_is_noop(self, tmp_path, monkeypatch):
        repo_path = tmp_path / "repo"
        repo_path.mkdir()
        git.Repo.init(repo_path)

        (repo_path / "app.ts").write_text("const x = 1;")
        (repo_path / "module.ts").write_text("export const y = 2;")

        monkeypatch.chdir(repo_path)

        with patch("pdd.update_main.get_language") as mock_lang:
            mock_lang.return_value = "typescript"

            pairs = find_and_resolve_all_pairs(str(repo_path), quiet=True)

        basenames = [os.path.basename(p[1]) for p in pairs]
        assert "app.ts" in basenames
        assert "module.ts" in basenames

    def test_skip_empty_files(self, tmp_path, monkeypatch):
        """Empty files and comment-only files are excluded from repo scan."""
        repo_path = tmp_path / "repo"
        repo_path.mkdir()
        git.Repo.init(repo_path)

        pkg_dir = repo_path / "mypackage"
        pkg_dir.mkdir()
        (pkg_dir / "__init__.py").write_text("")
        (pkg_dir / "comment_only.py").write_text("# just a comment\n# nothing else\n")
        (pkg_dir / "core.py").write_text("def main(): pass")

        monkeypatch.chdir(repo_path)

        with patch("pdd.update_main.get_language") as mock_lang:
            mock_lang.return_value = "python"
            pairs = find_and_resolve_all_pairs(str(repo_path), quiet=True)

        basenames = [os.path.basename(p[1]) for p in pairs]
        assert "core.py" in basenames
        assert "__init__.py" not in basenames
        assert "comment_only.py" not in basenames

    def test_keep_init_py_with_real_code(self, tmp_path, monkeypatch):
        """__init__.py with real code IS included in repo scan."""
        repo_path = tmp_path / "repo"
        repo_path.mkdir()
        git.Repo.init(repo_path)

        pkg_dir = repo_path / "mypackage"
        pkg_dir.mkdir()
        (pkg_dir / "__init__.py").write_text(
            "from .core import main\n\n__all__ = ['main']\n"
        )

        monkeypatch.chdir(repo_path)

        with patch("pdd.update_main.get_language") as mock_lang:
            mock_lang.return_value = "python"
            pairs = find_and_resolve_all_pairs(str(repo_path), quiet=True)

        basenames = [os.path.basename(p[1]) for p in pairs]
        assert "__init__.py" in basenames

    def test_pddignore_found_in_parent_when_scanning_subdirectory(self, tmp_path, monkeypatch):
        """When scanning a subdirectory, .pddignore in parent repo root is found."""
        repo_path = tmp_path / "repo"
        repo_path.mkdir()
        git.Repo.init(repo_path)

        # .pddignore at repo root with pattern relative to repo root
        (repo_path / ".pddignore").write_text(
            "frontend/src/components/ui/*\n"
        )

        # Create files inside frontend/ subdirectory
        ui_dir = repo_path / "frontend" / "src" / "components" / "ui"
        ui_dir.mkdir(parents=True)
        (ui_dir / "button.tsx").write_text("export function Button() {}")
        app_dir = repo_path / "frontend" / "src"
        (app_dir / "app.tsx").write_text("export default function App() {}")

        monkeypatch.chdir(repo_path)

        with patch("pdd.update_main.get_language") as mock_lang:
            def lang_for_ext(ext):
                if ext == ".tsx":
                    return "typescriptreact"
                return None
            mock_lang.side_effect = lang_for_ext

            # Scan from frontend/ subdirectory (simulates --directory frontend)
            pairs = find_and_resolve_all_pairs(str(repo_path / "frontend"), quiet=True)

        basenames = [os.path.basename(p[1]) for p in pairs]
        assert "app.tsx" in basenames
        assert "button.tsx" not in basenames


# --- Tests for fingerprint collision fix ---

from pdd.update_main import derive_basename_and_language


class TestFingerprintCollisionAvoidance:
    """Tests that same-named files in different dirs get distinct fingerprint keys."""

    def test_same_name_different_dirs_distinct_basenames(self):
        """Two page.tsx files in different directories must produce different basenames."""
        with patch("pdd.update_main.get_language", return_value="TypescriptReact"):
            b1, l1 = derive_basename_and_language(
                "/repo/frontend/src/app/settings/page.tsx", "/repo"
            )
            b2, l2 = derive_basename_and_language(
                "/repo/frontend/src/app/dashboard/page.tsx", "/repo"
            )
            b3, l3 = derive_basename_and_language(
                "/repo/frontend/src/app/login/page.tsx", "/repo"
            )

        # All basenames must be unique
        assert len({b1, b2, b3}) == 3
        assert b1 == "frontend/src/app/settings/page"
        assert b2 == "frontend/src/app/dashboard/page"
        assert b3 == "frontend/src/app/login/page"

    def test_fingerprint_paths_are_distinct(self):
        """Distinct basenames produce distinct fingerprint file paths via _safe_basename."""
        from pdd.operation_log import get_fingerprint_path, _safe_basename

        b1 = "frontend/src/app/settings/page"
        b2 = "frontend/src/app/dashboard/page"
        lang = "typescriptreact"

        # _safe_basename converts slashes to underscores
        assert _safe_basename(b1) != _safe_basename(b2)
        assert _safe_basename(b1) == "frontend_src_app_settings_page"
        assert _safe_basename(b2) == "frontend_src_app_dashboard_page"


class TestDataFileExclusion:
    """Tests that .csv and .txt data files are excluded from repo scan."""

    def test_csv_files_excluded(self, tmp_path, monkeypatch):
        """CSV files should be excluded from repo scan."""
        repo_path = tmp_path / "repo"
        repo_path.mkdir()
        git.Repo.init(repo_path)

        (repo_path / "module.py").write_text("def foo(): pass")
        (repo_path / "golden_results.csv").write_text("col1,col2\nval1,val2")
        (repo_path / "llm_model.csv").write_text("model,cost\ngpt-4,0.01")

        monkeypatch.chdir(repo_path)

        with patch("pdd.update_main.get_language") as mock_lang:
            def lang_for_ext(ext):
                if ext == ".py":
                    return "python"
                if ext == ".csv":
                    return "CSV"
                return None
            mock_lang.side_effect = lang_for_ext

            pairs = find_and_resolve_all_pairs(str(repo_path), quiet=True)

        code_files = [p[1] for p in pairs]
        assert any("module.py" in f for f in code_files)
        assert not any(".csv" in f for f in code_files)

    def test_txt_files_excluded(self, tmp_path, monkeypatch):
        """Text files should be excluded from repo scan."""
        repo_path = tmp_path / "repo"
        repo_path.mkdir()
        git.Repo.init(repo_path)

        (repo_path / "module.py").write_text("def foo(): pass")
        (repo_path / "requirements.txt").write_text("flask==2.0\n")
        (repo_path / "notes.txt").write_text("some notes")

        monkeypatch.chdir(repo_path)

        with patch("pdd.update_main.get_language") as mock_lang:
            def lang_for_ext(ext):
                if ext == ".py":
                    return "python"
                if ext == ".txt":
                    return "Text"
                return None
            mock_lang.side_effect = lang_for_ext

            pairs = find_and_resolve_all_pairs(str(repo_path), quiet=True)

        code_files = [p[1] for p in pairs]
        assert any("module.py" in f for f in code_files)
        assert not any(".txt" in f for f in code_files)
