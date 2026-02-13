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

@patch('pdd.update_main.update_file_pair')
def test_update_main_repo_mode_orchestration(mock_update_file_pair, temp_git_repo, capsys):
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

    # Assert that the update function was called for each pair
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
