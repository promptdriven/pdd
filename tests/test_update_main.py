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

def test_update_main_with_input_code_and_no_git(
    mock_ctx,
    minimal_input_files,
    mock_construct_paths,
    mock_update_prompt,
    mock_git_update,
    mock_open_file
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
    mock_open_file
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
        input_code_file=None,  # Not provided
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
        time=0.25
    )
    mock_update_prompt.assert_not_called()  # update_prompt should NOT be called

    assert result == ("updated prompt from git", 0.654321, "git-model")
    mock_open_file.assert_called_once_with("updated_prompt_git.prompt", "w")

def test_update_main_with_both_git_and_input_code_raises_valueerror(
    mock_ctx,
    minimal_input_files,
    mock_construct_paths,
    mock_update_prompt,
    mock_git_update
):
    """
    Test that providing both --git and an input_code_file raises ValueError.
    """
    # Arrange
    mock_ctx.params["quiet"] = True  # so no output from rprint
    git = True  # also specifying input_code_file
    with pytest.raises(SystemExit) as e:
        # Act
        update_main(
            ctx=mock_ctx,
            input_prompt_file=minimal_input_files["input_prompt_file"],
            modified_code_file=minimal_input_files["modified_code_file"],
            input_code_file=minimal_input_files["input_code_file"],  # This triggers the error
            output=None,
            use_git=git
        )

    # Assert
    # The function calls sys.exit(1) on ValueError, so we catch SystemExit
    assert e.type == SystemExit
    assert e.value.code == 1  # usage error

def test_update_main_no_git_no_input_code_raises_valueerror(
    mock_ctx,
    mock_construct_paths,
    mock_update_prompt,
    mock_git_update
):
    """
    Test that not specifying --git and leaving input_code_file=None raises ValueError.
    """
    # Arrange
    mock_ctx.params["quiet"] = True
    git = False

    with pytest.raises(SystemExit) as exit_info:
        update_main(
            ctx=mock_ctx,
            input_prompt_file="some_prompt_file.prompt",
            modified_code_file="modified_code.py",
            input_code_file=None,
            output=None,
            use_git=git
        )

    # Assert
    assert exit_info.type == SystemExit
    assert exit_info.value.code == 1

def test_update_main_handles_unexpected_exception_gracefully(
    mock_ctx,
    minimal_input_files,
    mock_construct_paths,
    mock_open_file
):
    """
    Test that an unexpected exception triggers sys.exit(1) and prints an error message.
    """
    mock_ctx.params["quiet"] = True

    # Force an unexpected exception in construct_paths or subsequent code
    mock_construct_paths.side_effect = Exception("Something went wrong")

    with pytest.raises(SystemExit) as exit_info:
        update_main(
            ctx=mock_ctx,
            input_prompt_file=minimal_input_files["input_prompt_file"],
            modified_code_file=minimal_input_files["modified_code_file"],
            input_code_file=minimal_input_files["input_code_file"],
            output=None,
            use_git=False
        )

    assert exit_info.type == SystemExit
    assert exit_info.value.code == 1

    # The open should never be called because we failed early
    mock_open_file.assert_not_called()

# --- Tests for --repo functionality ---

import os
from pathlib import Path
import git
from pdd.update_main import create_and_find_prompt_code_pairs

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
    (repo_path / "src" / "existing_module_python.prompt").write_text("Existing prompt.")
    
    # Add all files to be tracked by git
    repo.index.add([
        str(repo_path / "src" / "module1.py"),
        str(repo_path / "src" / "module2.js"),
        str(repo_path / "src" / "existing_module.py"),
        str(repo_path / "src" / "existing_module_python.prompt")
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
    """
    repo_path_str = str(temp_git_repo)
    
    # Prompts for module1 and module2 should not exist yet
    module1_prompt_path = temp_git_repo / "src" / "module1_python.prompt"
    module2_prompt_path = temp_git_repo / "src" / "module2_javascript.prompt"
    assert not module1_prompt_path.exists()
    assert not module2_prompt_path.exists()

    # Run the function
    pairs = create_and_find_prompt_code_pairs(repo_path_str)

    # Assert that missing prompts were created
    assert module1_prompt_path.exists()
    assert module1_prompt_path.read_text() == ""
    assert module2_prompt_path.exists()
    assert module2_prompt_path.read_text() == ""

    # Assert that the returned pairs are correct
    expected_pairs = [
        (str(temp_git_repo / "src" / "existing_module_python.prompt"), str(temp_git_repo / "src" / "existing_module.py")),
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
    def mock_update_logic(prompt_file, code_file, ctx):
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
    assert "src/module1_python.prompt" in captured.out
    assert "src/module2_javascript.prompt" in captured.out
    assert "src/existing_module_python.prompt" in captured.out
    assert "Total Estimated Cost" in captured.out
    
    assert result is not None
    assert result[0] == "Repository update complete."