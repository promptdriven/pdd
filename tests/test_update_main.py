import pytest
import sys
import os
from pathlib import Path
from unittest.mock import patch, MagicMock, mock_open
import click
from click.testing import CliRunner
import git

from pdd import DEFAULT_STRENGTH
from pdd.update_main import (
    _included_docs_for_drift_report,
    find_and_resolve_all_pairs,
    update_main,
)

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


def test_update_main_without_cli_strength_uses_default_strength_for_direct_update(
    mock_ctx,
    minimal_input_files,
    mock_construct_paths,
    mock_update_prompt,
    mock_git_update,
    mock_open_file,
    mock_get_available_agents,
):
    """Fallback should use DEFAULT_STRENGTH when global --strength was omitted."""
    mock_ctx.obj.pop("strength", None)
    mock_ctx.params["quiet"] = False

    result = update_main(
        ctx=mock_ctx,
        input_prompt_file=minimal_input_files["input_prompt_file"],
        modified_code_file=minimal_input_files["modified_code_file"],
        input_code_file=minimal_input_files["input_code_file"],
        output="custom_output.prompt",
        use_git=False,
    )

    kwargs = mock_update_prompt.call_args.kwargs
    assert kwargs["strength"] == DEFAULT_STRENGTH
    assert result == ("updated prompt text", 0.123456, "test-model")
    mock_git_update.assert_not_called()


def test_update_main_without_cli_strength_uses_default_strength_for_git_update(
    mock_ctx,
    mock_construct_paths,
    mock_update_prompt,
    mock_git_update,
    mock_open_file,
    mock_get_available_agents,
):
    """Git-backed updates should share the same DEFAULT_STRENGTH fallback."""
    mock_ctx.obj.pop("strength", None)
    mock_ctx.params["quiet"] = False
    mock_construct_paths.return_value = (
        {},
        {
            "input_prompt_file": "prompt content",
            "modified_code_file": "def git_modified_code(): pass",
        },
        {"output": "updated_prompt_git.prompt"},
        None,
    )

    result = update_main(
        ctx=mock_ctx,
        input_prompt_file="some_prompt_file.prompt",
        modified_code_file="modified_code.py",
        input_code_file=None,
        output="git_output.prompt",
        use_git=True,
    )

    kwargs = mock_git_update.call_args.kwargs
    assert kwargs["strength"] == DEFAULT_STRENGTH
    assert result == ("updated prompt from git", 0.654321, "git-model")
    mock_update_prompt.assert_not_called()

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


def test_included_docs_for_drift_report_counts_all_prompts_referencing_doc(tmp_path, monkeypatch):
    """Doc rows show how many scan-wide prompts include each doc, not only drifted count."""
    monkeypatch.chdir(tmp_path)
    (tmp_path / "README.md").write_text("# hi\n", encoding="utf-8")
    (tmp_path / "docs").mkdir()
    (tmp_path / "docs" / "api.md").write_text("api", encoding="utf-8")
    (tmp_path / "prompts").mkdir()
    p = tmp_path / "prompts" / "m_python.prompt"
    p.write_text(
        "<include>../README.md</include>\n<include>../docs/api.md</include>\n",
        encoding="utf-8",
    )
    p2 = tmp_path / "prompts" / "n_python.prompt"
    p2.write_text("<include>../README.md</include>\n", encoding="utf-8")
    all_prompts = [str(p), str(p2)]
    # Only m_python is drifted; README is still included by 2 prompts in the scan.
    agg = _included_docs_for_drift_report(str(tmp_path), all_prompts, [str(p)])
    by_name = {rel: c for rel, c in agg}
    assert by_name.get("README.md") == 2
    assert by_name.get("docs/api.md") == 1


def test_estimate_dry_run_cost_range_is_flat_per_pair(tmp_path, monkeypatch):
    """Dry-run estimate is a flat $0.50–$1.00 per drifted pair."""
    from pdd.update_main import _estimate_dry_run_cost_range

    repo = git.Repo.init(tmp_path)
    (tmp_path / "small.py").write_text("a")
    (tmp_path / "prompts").mkdir()
    sp = tmp_path / "prompts" / "small_python.prompt"
    sp.write_text("prompt")
    repo.index.add([str(tmp_path / "small.py"), str(sp)])
    repo.index.commit("init")
    monkeypatch.chdir(tmp_path)

    ctx = click.Context(click.Command("update"))
    ctx.obj = {}
    small_items = [(str(sp), str(tmp_path / "small.py"), "r")]

    lo_s, hi_s = _estimate_dry_run_cost_range(ctx, repo, True, small_items)
    assert lo_s == 0.5
    assert hi_s == 1.0

    lo_0, hi_0 = _estimate_dry_run_cost_range(ctx, repo, True, [])
    assert lo_0 == 0.0
    assert hi_0 == 0.0


@pytest.fixture
def mock_get_language_for_repo(monkeypatch):
    """Mocks get_language to return predictable results for repo tests."""
    def mock_func(file_path):
        if str(file_path).endswith(".py"):
            return "python"
        if str(file_path).endswith(".js"):
            return "javascript"
        return None
    _update_main_mod = sys.modules['pdd.update_main']
    monkeypatch.setattr(_update_main_mod, 'get_language', mock_func)

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
    Test that the helper function correctly finds code files and resolves prompt paths.
    With structure preservation, prompts mirror the source directory structure.
    Scanning must NOT create empty prompt files on disk (side-effect-free).
    """
    repo_path_str = str(temp_git_repo)

    # With structure preservation, prompts for files in src/ go to prompts/src/
    module1_prompt_path = temp_git_repo / "prompts" / "src" / "module1_python.prompt"
    module2_prompt_path = temp_git_repo / "prompts" / "src" / "module2_javascript.prompt"
    existing_prompt_path_nested = temp_git_repo / "prompts" / "src" / "existing_module_python.prompt"

    # Run the function
    pairs = find_and_resolve_all_pairs(repo_path_str)

    # Scanning should NOT create empty prompt files on disk
    assert not module1_prompt_path.exists(), "Scan should not create empty prompt files"
    assert not module2_prompt_path.exists(), "Scan should not create empty prompt files"

    # Assert that the returned pairs are correct
    expected_pairs = [
        (str(existing_prompt_path_nested), str(temp_git_repo / "src" / "existing_module.py")),
        (str(module1_prompt_path), str(temp_git_repo / "src" / "module1.py")),
        (str(module2_prompt_path), str(temp_git_repo / "src" / "module2.js")),
    ]
    assert len(pairs) == len(expected_pairs)
    assert sorted(p[1] for p in pairs) == sorted(ep[1] for ep in expected_pairs)

def test_find_and_resolve_pairs_scans_only_scan_dir(tmp_path, mock_get_language_for_repo):
    """
    Bug repro: when scan_dir is a subdirectory of the git root,
    find_and_resolve_all_pairs should only return code files under
    scan_dir, not files from the parent repo.
    """
    # Create a git repo with a subdirectory project
    repo_path = tmp_path / "repo"
    repo_path.mkdir()
    repo = git.Repo.init(repo_path)

    # Parent repo files (should NOT be scanned)
    (repo_path / "pdd").mkdir()
    (repo_path / "pdd" / "cli.py").write_text("def main(): pass")

    # Subdirectory project files (should be scanned)
    subdir = repo_path / "video_editor"
    subdir.mkdir()
    (subdir / "lib").mkdir()
    (subdir / "lib" / "db.py").write_text("def query(): pass")
    (subdir / "app").mkdir()
    (subdir / "app" / "main.py").write_text("def run(): pass")

    repo.index.add([
        str(repo_path / "pdd" / "cli.py"),
        str(subdir / "lib" / "db.py"),
        str(subdir / "app" / "main.py"),
    ])
    repo.index.commit("Initial commit")

    original_cwd = os.getcwd()
    os.chdir(subdir)
    try:
        pairs = find_and_resolve_all_pairs(str(subdir), quiet=True)

        # Only files under video_editor/ should be found
        code_files = sorted(p[1] for p in pairs)
        for f in code_files:
            assert f.startswith(str(subdir)), \
                f"File '{f}' is outside scan_dir '{subdir}'. " \
                f"find_and_resolve_all_pairs should only scan within scan_dir."

        # Should find the 2 subdir files, NOT the parent's pdd/cli.py
        assert len(pairs) == 2, \
            f"Expected 2 files under video_editor/ but got {len(pairs)}: {code_files}"
    finally:
        os.chdir(original_cwd)


def test_update_main_repo_mode_uses_cwd_pddrc_as_scan_dir(tmp_path, mock_get_language_for_repo):
    """
    Bug repro: when CWD is a subdirectory with its own .pddrc,
    update_main in repo-wide mode (0 args) should scope the scan
    to CWD, not the entire git root.
    """
    from pdd.update_main import update_main

    # Create a git repo
    repo_path = tmp_path / "repo"
    repo_path.mkdir()
    repo = git.Repo.init(repo_path)

    # Parent repo .pddrc and files
    (repo_path / ".pddrc").write_text('version: "1.0"\ncontexts:\n  default:\n    defaults:\n      generate_output_path: "./"\n')
    (repo_path / "pdd").mkdir()
    (repo_path / "pdd" / "cli.py").write_text("def main(): pass")

    # Subdirectory with its own .pddrc
    subdir = repo_path / "video_editor"
    subdir.mkdir()
    (subdir / ".pddrc").write_text('version: "1.0"\ncontexts:\n  default:\n    defaults:\n      prompts_dir: "prompts/"\n')
    (subdir / "lib").mkdir()
    (subdir / "lib" / "db.py").write_text("def query(): pass")
    (subdir / "prompts").mkdir()

    repo.index.add([
        str(repo_path / ".pddrc"),
        str(repo_path / "pdd" / "cli.py"),
        str(subdir / ".pddrc"),
        str(subdir / "lib" / "db.py"),
    ])
    repo.index.commit("Initial commit")

    # Simulate running from the subdirectory (0 args → repo mode)
    original_cwd = os.getcwd()
    os.chdir(subdir)
    try:
        ctx = click.Context(click.Command("update"))
        ctx.params = {"force": False, "quiet": True}
        ctx.obj = {"strength": 0.5, "temperature": 0.0, "verbose": False}

        with patch('pdd.update_main.update_file_pair') as mock_update, \
             patch('pdd.update_main.is_code_changed', return_value=(True, "changed")), \
             patch('pdd.update_main.get_git_changed_files', return_value={str(subdir / "lib" / "db.py")}), \
             patch('pdd.architecture_sync.update_architecture_from_prompt', return_value={"success": False, "updated": False, "changes": {}}):

            mock_update.return_value = {
                "prompt_file": "test.prompt", "status": "ok",
                "cost": 0.0, "model": "mock", "error": ""
            }

            result = update_main(
                ctx=ctx,
                input_prompt_file=None,
                modified_code_file=None,
                input_code_file=None,
                output=None,
                use_git=False,
                repo=True,
                extensions=None,
                directory=None,  # No --directory flag, should detect from CWD
                simple=True,
            )

        # Verify that only subdir files were processed, not parent repo files
        if mock_update.called:
            for call in mock_update.call_args_list:
                code_file = call[0][1] if len(call[0]) > 1 else call[1].get('code_file', '')
                assert 'pdd/cli.py' not in str(code_file), \
                    f"Parent repo file was processed: {code_file}. " \
                    f"update_main should scope scan to CWD when it has a .pddrc."
    finally:
        os.chdir(original_cwd)


@patch('pdd.architecture_sync.update_architecture_from_prompt', return_value={"success": False, "updated": False, "changes": {}})
@patch('pdd.update_main.is_code_changed', return_value=(True, "no fingerprint, file in git changed set"))
@patch('pdd.update_main.get_git_changed_files', return_value=set())
@patch('pdd.update_main.update_file_pair')
@patch('pdd.pddrc_initializer.ensure_pddrc_for_scan')
def test_update_main_repo_mode_orchestration(mock_pddrc, mock_update_file_pair, mock_git_changed, mock_is_changed, mock_arch, temp_git_repo, capsys):
    """
    Test the main orchestration logic of update_main in --repo mode.
    """
    # Use a side_effect to return dynamic values based on input
    def mock_update_logic(
        prompt_file,
        code_file,
        ctx,
        repo,
        simple=False,
        strength=None,
        temperature=None,
    ):
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


@patch('pdd.architecture_sync.update_architecture_from_prompt', return_value={"success": False, "updated": False, "changes": {}})
@patch('pdd.update_main.is_code_changed', return_value=(True, "no fingerprint, file in git changed set"))
@patch('pdd.update_main.get_git_changed_files', return_value=set())
@patch('pdd.update_main.update_file_pair')
def test_update_main_repo_mode_honors_budget_cap(mock_update_file_pair, mock_git_changed, mock_is_changed, mock_arch, temp_git_repo, capsys):
    """Repo mode should stop processing new files once budget cap is reached."""
    costs = iter([0.60, 0.60, 0.60])  # 3 changed pairs in fixture

    def mock_update_logic(
        prompt_file,
        code_file,
        ctx,
        repo,
        simple=False,
        strength=None,
        temperature=None,
    ):
        return {
            "prompt_file": prompt_file,
            "status": "✅ Success",
            "cost": next(costs),
            "model": "mock_model",
            "error": "",
        }

    mock_update_file_pair.side_effect = mock_update_logic

    ctx = click.Context(click.Command('update'))
    ctx.obj = {"strength": 0.5, "temperature": 0.1, "verbose": False, "time": 0.25, "quiet": False}

    result = update_main(
        ctx=ctx,
        input_prompt_file=None,
        modified_code_file=None,
        input_code_file=None,
        output=None,
        use_git=False,
        repo=True,
        budget=1.0,
    )

    # First two updates run (0.6 + 0.6), then cap is reached and third is skipped.
    assert mock_update_file_pair.call_count == 2
    captured = capsys.readouterr()
    assert "budget cap reached" in captured.out.lower()
    assert result is not None
    assert result[1] == pytest.approx(1.2)


@patch("pdd.architecture_sync.update_architecture_from_prompt", return_value={"success": False, "updated": False, "changes": {}})
@patch("pdd.update_main.is_code_changed", return_value=(True, "no fingerprint, file in git changed set"))
@patch("pdd.update_main.get_git_changed_files", return_value=set())
@patch("pdd.update_main.update_file_pair")
@patch("pdd.pddrc_initializer.ensure_pddrc_for_scan")
def test_update_main_repo_mode_dry_run_skips_work(
    mock_ensure_pddrc,
    mock_update_file_pair,
    mock_git_changed,
    mock_is_changed,
    mock_arch,
    temp_git_repo,
    capsys,
):
    """Repository-wide dry run must not call update_file_pair or ensure_pddrc_for_scan."""
    ctx = click.Context(click.Command("update"))
    ctx.obj = {"strength": 0.5, "temperature": 0.1, "verbose": False, "time": 0.25, "quiet": False}

    result = update_main(
        ctx=ctx,
        input_prompt_file=None,
        modified_code_file=None,
        input_code_file=None,
        output=None,
        use_git=False,
        repo=True,
        dry_run=True,
    )

    mock_update_file_pair.assert_not_called()
    mock_ensure_pddrc.assert_not_called()
    captured = capsys.readouterr()
    assert "Repository drift report" in captured.out
    assert "Changed files:" in captured.out
    assert "Estimated cost:" in captured.out
    assert "Drifted modules:" in captured.out
    assert "Included docs that may need updating:" in captured.out
    assert "Repository Update Summary" not in captured.out
    assert result is not None
    assert result[1] == 0.0
    assert "would be updated" in result[0].lower()
    assert result[2] == "N/A"


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

    def test_resolve_prompt_code_pair_lowercases_language(self, tmp_path, monkeypatch):
        """Language suffix should be lowercased (e.g., typescriptreact, not TypescriptReact)."""
        repo_path = tmp_path / "repo"
        repo_path.mkdir()
        code_file = repo_path / "page.tsx"
        code_file.write_text("export default function Page() {}")

        monkeypatch.chdir(repo_path)
        git.Repo.init(repo_path)

        with patch("pdd.update_main.get_language") as mock_lang:
            mock_lang.return_value = "TypescriptReact"
            prompt_path, _ = resolve_prompt_code_pair(str(code_file), quiet=True)

        assert prompt_path.endswith("page_typescriptreact.prompt")

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


# --- Tests for get_git_changed_files ---

from pdd.update_main import get_git_changed_files


class TestGetGitChangedFiles:
    """Tests for get_git_changed_files."""

    def test_combines_committed_uncommitted_and_untracked(self, tmp_path, monkeypatch):
        """Should combine all three sources of changed files."""
        repo_path = tmp_path / "repo"
        repo_path.mkdir()
        repo = git.Repo.init(repo_path)

        # Create and commit initial file
        (repo_path / "init.py").write_text("# init\n")
        repo.index.add(["init.py"])
        repo.index.commit("init")
        # Rename default branch
        repo.git.branch("-M", "main")

        # Create untracked file
        (repo_path / "new_file.py").write_text("def new(): pass\n")

        changed = get_git_changed_files(str(repo_path), base_branch="main")
        # Should at least find the untracked file
        assert any("new_file.py" in f for f in changed)

    def test_empty_repo_returns_empty_set(self, tmp_path):
        """Should handle repos with no commits gracefully."""
        repo_path = tmp_path / "repo"
        repo_path.mkdir()
        git.Repo.init(repo_path)

        changed = get_git_changed_files(str(repo_path), base_branch="main")
        assert isinstance(changed, set)

    def test_returns_absolute_paths(self, tmp_path, monkeypatch):
        """All returned paths should be absolute."""
        repo_path = tmp_path / "repo"
        repo_path.mkdir()
        repo = git.Repo.init(repo_path)

        (repo_path / "init.py").write_text("pass\n")
        repo.index.add(["init.py"])
        repo.index.commit("init")
        repo.git.branch("-M", "main")

        (repo_path / "new.py").write_text("pass\n")

        changed = get_git_changed_files(str(repo_path), base_branch="main")
        for f in changed:
            assert os.path.isabs(f), f"Path is not absolute: {f}"


# --- Tests for is_code_changed ---

from pdd.update_main import is_code_changed


class TestIsCodeChanged:
    """Tests for is_code_changed with fingerprint and git fallback."""

    @pytest.fixture(autouse=True)
    def mock_get_language(self):
        """Mock get_language to avoid PDD_PATH dependency."""
        with patch("pdd.update_main.get_language", return_value="python"):
            yield

    def test_no_fingerprint_in_git_changed(self, tmp_path):
        """No fingerprint + file in git changed set -> changed=True."""
        code_file = tmp_path / "module.py"
        code_file.write_text("def foo(): pass\n")

        with patch("pdd.update_main.read_fingerprint", return_value=None):
            changed, reason = is_code_changed(
                str(code_file), str(tmp_path), {str(code_file)}
            )
        assert changed is True
        assert "git changed set" in reason

    def test_no_fingerprint_not_in_git_changed(self, tmp_path):
        """No fingerprint + file NOT in git changed set -> changed=False."""
        code_file = tmp_path / "module.py"
        code_file.write_text("def foo(): pass\n")

        with patch("pdd.update_main.read_fingerprint", return_value=None):
            changed, reason = is_code_changed(
                str(code_file), str(tmp_path), set()
            )
        assert changed is False

    def test_fingerprint_code_hash_matches(self, tmp_path):
        """Fingerprint with matching code hash -> changed=False."""
        from pdd.sync_determine_operation import calculate_sha256

        code_file = tmp_path / "module.py"
        code_file.write_text("def foo(): pass\n")
        current_hash = calculate_sha256(code_file)

        mock_fp = MagicMock()
        mock_fp.code_hash = current_hash
        mock_fp.include_deps = {}

        with patch("pdd.update_main.read_fingerprint", return_value=mock_fp):
            changed, reason = is_code_changed(
                str(code_file), str(tmp_path), set()
            )
        assert changed is False
        assert "matches" in reason

    def test_fingerprint_code_hash_differs(self, tmp_path):
        """Fingerprint with different code hash -> changed=True."""
        code_file = tmp_path / "module.py"
        code_file.write_text("def foo(): pass\n")

        mock_fp = MagicMock()
        mock_fp.code_hash = "old_hash_that_differs"
        mock_fp.include_deps = {}

        with patch("pdd.update_main.read_fingerprint", return_value=mock_fp):
            changed, reason = is_code_changed(
                str(code_file), str(tmp_path), set()
            )
        assert changed is True
        assert "differs" in reason

    def test_fingerprint_include_deps_changed(self, tmp_path):
        """Include dependency changed on disk -> changed=True."""
        from pdd.sync_determine_operation import calculate_sha256

        code_file = tmp_path / "module.py"
        code_file.write_text("def foo(): pass\n")
        current_hash = calculate_sha256(code_file)

        dep_file = tmp_path / "preamble.md"
        dep_file.write_text("updated preamble content\n")

        mock_fp = MagicMock()
        mock_fp.code_hash = current_hash
        mock_fp.include_deps = {str(dep_file): "old_hash_of_preamble"}

        with patch("pdd.update_main.read_fingerprint", return_value=mock_fp):
            changed, reason = is_code_changed(
                str(code_file), str(tmp_path), set()
            )
        assert changed is True
        assert "include dependency changed" in reason

    def test_uses_prompt_file_path_for_identity(self, tmp_path):
        """When prompt_file_path is provided, uses infer_module_identity."""
        code_file = tmp_path / "module.py"
        code_file.write_text("def foo(): pass\n")

        with patch("pdd.update_main.read_fingerprint", return_value=None) as mock_rf, \
             patch("pdd.operation_log.infer_module_identity", return_value=("module", "python")) as mock_imi:
            changed, reason = is_code_changed(
                str(code_file), str(tmp_path), set(),
                prompt_file_path="prompts/module_python.prompt"
            )
            mock_imi.assert_called_once_with("prompts/module_python.prompt")


# --- Tests for _find_prd_file ---

from pdd.update_main import _find_prd_file


class TestFindPrdFile:
    """Tests for _find_prd_file convention-based PRD discovery."""

    def test_finds_prd_md(self, tmp_path):
        (tmp_path / "PRD.md").write_text("# PRD")
        result = _find_prd_file(tmp_path)
        assert result is not None
        assert result.name == "PRD.md"

    def test_finds_lowercase_prd(self, tmp_path):
        (tmp_path / "prd.md").write_text("# prd")
        result = _find_prd_file(tmp_path)
        assert result is not None
        assert result.name == "prd.md"

    def test_finds_prefixed_prd(self, tmp_path):
        (tmp_path / "myproject_prd.md").write_text("# PRD")
        result = _find_prd_file(tmp_path)
        assert result is not None
        assert "prd" in result.name.lower()

    def test_returns_none_when_no_prd(self, tmp_path):
        (tmp_path / "README.md").write_text("# README")
        result = _find_prd_file(tmp_path)
        assert result is None


# --- Tests for strength/temperature resolution ---


class TestStrengthTemperatureResolution:
    """Tests for strength/temperature parameter resolution."""

    def test_explicit_params_override_ctx(self):
        """Explicit strength/temperature should override ctx.obj values."""
        ctx = click.Context(click.Command("update"))
        ctx.obj = {
            "strength": 0.5,
            "temperature": 0.0,
            "verbose": False,
            "quiet": True,
            "time": 0.25,
            "force": True,
            "context": None,
            "confirm_callback": None,
        }

        with patch("pdd.update_main.get_available_agents", return_value=[]), \
             patch("pdd.update_main.update_prompt", return_value=("prompt", 0.01, "model")) as mock_up, \
             patch("pdd.update_main.resolve_prompt_code_pair", return_value=("/tmp/test.prompt", "/tmp/test.py")), \
             patch("builtins.open", mock_open(read_data="def foo(): pass\n")):
            update_main(
                ctx=ctx,
                input_prompt_file=None,
                modified_code_file="/tmp/test.py",
                input_code_file=None,
                output=None,
                strength=0.9,
                temperature=0.5,
                simple=True,
            )

        kwargs = mock_up.call_args.kwargs
        assert kwargs["strength"] == 0.9
        assert kwargs["temperature"] == 0.5
        # Explicit params should not poison ctx.obj for later per-target resolution.
        assert ctx.obj["strength"] == 0.5
        assert ctx.obj["temperature"] == 0.0

    def test_ctx_values_used_when_params_none(self):
        """When strength/temperature are None, ctx.obj values should be used."""
        ctx = click.Context(click.Command("update"))
        ctx.obj = {
            "strength": 0.7,
            "temperature": 0.3,
            "verbose": False,
            "quiet": True,
            "time": 0.25,
            "force": True,
            "context": None,
            "confirm_callback": None,
        }

        with patch("pdd.update_main.get_available_agents", return_value=[]), \
             patch("pdd.update_main.update_prompt", return_value=("prompt", 0.01, "model")) as mock_up, \
             patch("pdd.update_main.resolve_prompt_code_pair", return_value=("/tmp/test.prompt", "/tmp/test.py")), \
             patch("builtins.open", mock_open(read_data="def foo(): pass\n")):
            update_main(
                ctx=ctx,
                input_prompt_file=None,
                modified_code_file="/tmp/test.py",
                input_code_file=None,
                output=None,
                strength=None,
                temperature=None,
                simple=True,
            )

        assert ctx.obj["strength"] == 0.7
        assert ctx.obj["temperature"] == 0.3


# --- Tests for empty prompt validation ---


class TestEmptyPromptValidation:
    """Tests for defense-in-depth empty prompt validation."""

    def test_empty_prompt_from_llm_returns_none(self):
        """If LLM returns empty prompt, update_main should return None."""
        ctx = click.Context(click.Command("update"))
        ctx.obj = {
            "strength": 0.5,
            "temperature": 0.0,
            "verbose": False,
            "quiet": True,
            "time": 0.25,
            "force": True,
            "context": None,
            "confirm_callback": None,
        }

        with patch("pdd.update_main.get_available_agents", return_value=[]), \
             patch("pdd.update_main.construct_paths") as mock_cp, \
             patch("pdd.update_main.git_update", return_value=("", 0.01, "model")):
            mock_cp.return_value = (
                {},
                {"input_prompt_file": "existing prompt", "modified_code_file": "def foo(): pass"},
                {"output": "/tmp/output.prompt"},
                "python",
            )

            result = update_main(
                ctx=ctx,
                input_prompt_file="/tmp/test.prompt",
                modified_code_file="/tmp/test.py",
                input_code_file=None,
                output=None,
                use_git=True,
                simple=True,
            )

        assert result is None


# --- Tests for update_file_pair ---


class TestUpdateFilePair:
    """Tests for update_file_pair wrapper."""

    def test_agentic_success(self, tmp_path):
        """Agentic path succeeds -> returns success result."""
        from pdd.update_main import update_file_pair

        prompt_file = tmp_path / "test.prompt"
        prompt_file.write_text("updated by agent\n")
        code_file = tmp_path / "test.py"
        code_file.write_text("def foo(): pass\n")

        ctx = click.Context(click.Command("update"))
        ctx.obj = {
            "strength": 0.5,
            "temperature": 0.0,
            "verbose": False,
            "quiet": True,
            "time": 0.25,
        }

        mock_repo = MagicMock()
        mock_repo.working_tree_dir = str(tmp_path)

        with patch("pdd.update_main.get_available_agents", return_value=["anthropic"]), \
             patch("pdd.update_main.get_tests_dir_from_config", return_value=None), \
             patch("pdd.update_main.run_agentic_update", return_value=(True, "ok", 0.05, "claude", [])):
            result = update_file_pair(str(prompt_file), str(code_file), ctx, mock_repo, simple=False)

        assert "Success" in result["status"]
        assert "agentic" in result["status"]
        assert result["cost"] == 0.05

    def test_legacy_git_update_path(self, tmp_path):
        """Legacy path for tracked files with existing prompt."""
        from pdd.update_main import update_file_pair

        prompt_file = tmp_path / "test.prompt"
        prompt_file.write_text("existing prompt content\n")
        code_file = tmp_path / "test.py"
        code_file.write_text("def foo(): pass\n")

        ctx = click.Context(click.Command("update"))
        ctx.obj = {
            "strength": 0.5,
            "temperature": 0.0,
            "verbose": False,
            "quiet": True,
            "time": 0.25,
        }

        mock_repo = MagicMock()
        mock_repo.working_tree_dir = str(tmp_path)
        mock_repo.untracked_files = []

        with patch("pdd.update_main.get_available_agents", return_value=[]), \
             patch("pdd.update_main.git_update", return_value=("updated prompt", 0.02, "gemini")):
            result = update_file_pair(str(prompt_file), str(code_file), ctx, mock_repo, simple=True)

        assert "Success" in result["status"]
        assert result["cost"] == 0.02
        # Verify the prompt was written
        assert prompt_file.read_text() == "updated prompt"

    def test_exception_returns_error_result(self, tmp_path):
        """Exceptions should be caught and returned as error results."""
        from pdd.update_main import update_file_pair

        prompt_file = tmp_path / "test.prompt"
        prompt_file.write_text("prompt\n")
        code_file = tmp_path / "test.py"
        code_file.write_text("def foo(): pass\n")

        ctx = click.Context(click.Command("update"))
        ctx.obj = {
            "strength": 0.5,
            "temperature": 0.0,
            "verbose": False,
            "quiet": True,
            "time": 0.25,
        }

        mock_repo = MagicMock()
        mock_repo.working_tree_dir = str(tmp_path)
        mock_repo.untracked_files = []

        with patch("pdd.update_main.get_available_agents", return_value=[]), \
             patch("pdd.update_main.git_update", side_effect=RuntimeError("LLM error")):
            result = update_file_pair(str(prompt_file), str(code_file), ctx, mock_repo, simple=True)

        assert "Failed" in result["status"]
        assert "LLM error" in result["error"]

    def test_click_abort_reraised(self, tmp_path):
        """click.Abort should be re-raised, not caught."""
        from pdd.update_main import update_file_pair

        prompt_file = tmp_path / "test.prompt"
        prompt_file.write_text("prompt\n")
        code_file = tmp_path / "test.py"
        code_file.write_text("def foo(): pass\n")

        ctx = click.Context(click.Command("update"))
        ctx.obj = {
            "strength": 0.5,
            "temperature": 0.0,
            "verbose": False,
            "quiet": True,
            "time": 0.25,
        }

        mock_repo = MagicMock()
        mock_repo.working_tree_dir = str(tmp_path)
        mock_repo.untracked_files = []

        with patch("pdd.update_main.get_available_agents", return_value=[]), \
             patch("pdd.update_main.git_update", side_effect=click.Abort()):
            with pytest.raises(click.Abort):
                update_file_pair(str(prompt_file), str(code_file), ctx, mock_repo, simple=True)


# --- Tests for repo mode: empty prompts always included ---


class TestRepoModeEmptyPrompts:
    """Tests that empty (0-byte) prompt files trigger updates regardless of code changes."""

    def test_empty_prompt_included_regardless_of_code_changes(self, tmp_path, monkeypatch):
        """Empty prompt files should always be included in changed pairs."""
        repo_path = tmp_path / "repo"
        repo_path.mkdir()
        repo = git.Repo.init(repo_path)

        # Create code and empty prompt
        (repo_path / "module.py").write_text("def foo(): pass\n")
        (repo_path / "prompts").mkdir()
        (repo_path / "prompts" / "module_python.prompt").write_text("")  # empty

        repo.index.add(["module.py", "prompts/module_python.prompt"])
        repo.index.commit("init")
        repo.git.branch("-M", "main")

        monkeypatch.chdir(repo_path)

        ctx = click.Context(click.Command("update"))
        ctx.obj = {
            "strength": 0.5,
            "temperature": 0.0,
            "verbose": False,
            "quiet": True,
            "time": 0.25,
            "force": True,
            "context": None,
            "confirm_callback": None,
        }

        mock_result = {
            "prompt_file": str(repo_path / "prompts" / "module_python.prompt"),
            "status": "Success",
            "cost": 0.01,
            "model": "mock",
            "error": "",
        }

        with patch("pdd.update_main.get_language", return_value="python"), \
             patch("pdd.update_main.update_file_pair", return_value=mock_result) as mock_ufp, \
             patch("pdd.update_main.is_code_changed", return_value=(False, "matches fingerprint")), \
             patch("pdd.update_main.get_git_changed_files", return_value=set()), \
             patch("pdd.architecture_registry.find_architecture_for_project", return_value=[]), \
             patch("pdd.operation_log.save_fingerprint"), \
             patch("pdd.operation_log.infer_module_identity", return_value=("module", "python")):
            result = update_main(
                ctx=ctx,
                input_prompt_file=None,
                modified_code_file=None,
                input_code_file=None,
                output=None,
                repo=True,
                simple=True,
            )

        # Should have been called even though is_code_changed returned False
        assert mock_ufp.called


class TestFindAndResolveAllPairsNoTouch:
    """find_and_resolve_all_pairs must NOT create empty prompt files on disk."""

    def test_scan_does_not_create_prompt_files(self, tmp_path, monkeypatch):
        """Scanning a repo should resolve paths without creating empty .prompt files."""
        repo = tmp_path / "repo"
        repo.mkdir()
        (repo / "src").mkdir()
        (repo / "src" / "module.py").write_text("def main(): pass\n")
        (repo / "src" / "helper.py").write_text("def help(): pass\n")

        # Init git so git ls-files works
        import subprocess
        env = {**os.environ, "GIT_AUTHOR_NAME": "T", "GIT_AUTHOR_EMAIL": "t@t",
               "GIT_COMMITTER_NAME": "T", "GIT_COMMITTER_EMAIL": "t@t"}
        subprocess.run(["git", "init", str(repo)], check=True, capture_output=True, env=env)
        subprocess.run(["git", "-C", str(repo), "add", "-A"], check=True, capture_output=True, env=env)
        subprocess.run(["git", "-C", str(repo), "commit", "-m", "init"], check=True, capture_output=True, env=env)

        monkeypatch.chdir(repo)

        with patch("pdd.update_main.get_language", side_effect=lambda ext: "python" if ext == ".py" else None):
            pairs = find_and_resolve_all_pairs(str(repo), quiet=True)

        # Should find the code files
        assert len(pairs) >= 2

        # The prompt paths should be resolved but NOT created on disk
        for prompt_path, code_path in pairs:
            assert not Path(prompt_path).exists(), (
                f"Scanning should not create prompt files, but {prompt_path} exists on disk"
            )


# --- Regression tests for gltanaka/pdd#1220 ---
# Legacy regeneration path must read the existing prompt from disk rather
# than hardcoding "no prompt exists yet, create a new one", which caused the
# autoheal destructive-rewrite class of bugs in PR #1187 and 5 other
# commits. See the issue for the full empirical matrix.


def _setup_regeneration_repo(tmp_path, monkeypatch, prompt_content=None):
    """Helper: lay out a minimal repo for legacy-regeneration tests.

    Returns (code_file_path, prompt_file_path). Creates the prompt file
    only when prompt_content is not None.
    """
    repo_path = tmp_path / "repo"
    repo_path.mkdir()
    prompts_dir = repo_path / "prompts"
    prompts_dir.mkdir()

    code_file = repo_path / "sample.py"
    code_file.write_text("def sample():\n    return 1\n")

    prompt_file = prompts_dir / "sample_python.prompt"
    if prompt_content is not None:
        prompt_file.write_text(prompt_content)

    monkeypatch.chdir(repo_path)
    git.Repo.init(repo_path)
    return code_file, prompt_file


def test_regeneration_mode_passes_existing_prompt_when_file_exists(tmp_path, monkeypatch):
    """When a prompt already exists on disk, the legacy path must hand its
    full content to update_prompt so the LLM can preserve structure."""
    from pdd.update_main import update_main

    existing_prompt = (
        "<include>context/preamble.prompt</include>\n"
        "% Goal\n"
        "do the thing\n"
        "<pdd.helper>\n"
        "helper text\n"
    )
    code_file, prompt_file = _setup_regeneration_repo(
        tmp_path, monkeypatch, prompt_content=existing_prompt
    )

    with patch("pdd.update_main.update_prompt") as mock_update_prompt, \
         patch("pdd.update_main.get_available_agents") as mock_agents, \
         patch("pdd.update_main.get_language") as mock_get_language:
        mock_update_prompt.return_value = (
            "<include>context/preamble.prompt</include>\n% Goal\nupdated\n<pdd.helper>\n",
            0.01,
            "mock-model",
        )
        mock_agents.return_value = []  # force legacy path
        mock_get_language.return_value = "python"

        ctx = click.Context(click.Command("update"))
        ctx.obj = {"strength": 0.5, "temperature": 0.0, "verbose": False, "quiet": True}

        update_main(
            ctx=ctx,
            input_prompt_file=None,
            modified_code_file=str(code_file),
            input_code_file=None,
            output=None,
            use_git=False,
        )

    assert mock_update_prompt.called
    kwargs = mock_update_prompt.call_args.kwargs
    assert kwargs["input_prompt"] == existing_prompt, (
        "Legacy regeneration path must pass the existing prompt content "
        "to update_prompt; got the first-time sentinel or wrong content."
    )
    assert "<pdd.helper>" in kwargs["input_prompt"]


def test_regeneration_mode_uses_sentinel_when_prompt_file_missing(tmp_path, monkeypatch):
    """When no prompt file exists, the legacy path falls back to the
    first-time-generation sentinel — preserves original semantics."""
    from pdd.update_main import update_main

    code_file, _ = _setup_regeneration_repo(
        tmp_path, monkeypatch, prompt_content=None
    )

    with patch("pdd.update_main.update_prompt") as mock_update_prompt, \
         patch("pdd.update_main.get_available_agents") as mock_agents, \
         patch("pdd.update_main.get_language") as mock_get_language:
        mock_update_prompt.return_value = ("fresh prompt", 0.01, "mock-model")
        mock_agents.return_value = []
        mock_get_language.return_value = "python"

        ctx = click.Context(click.Command("update"))
        ctx.obj = {"strength": 0.5, "temperature": 0.0, "verbose": False, "quiet": True}

        update_main(
            ctx=ctx,
            input_prompt_file=None,
            modified_code_file=str(code_file),
            input_code_file=None,
            output=None,
            use_git=False,
        )

    assert mock_update_prompt.called
    kwargs = mock_update_prompt.call_args.kwargs
    assert kwargs["input_prompt"] == "no prompt exists yet, create a new one"


def test_regeneration_mode_degrades_gracefully_on_unicode_error(tmp_path, monkeypatch):
    """Corrupt / non-UTF8 prompt file must not crash the pipeline — the
    legacy path should fall back to the sentinel so pdd update still runs
    instead of bubbling UnicodeDecodeError up through the heal pipeline."""
    from pdd.update_main import update_main

    code_file, prompt_file = _setup_regeneration_repo(
        tmp_path, monkeypatch, prompt_content=""
    )
    # Write invalid UTF-8 bytes directly so Path.read_text() would raise
    prompt_file.write_bytes(b"\xff\xfe<bad utf-8 \x80\x81\x82>\n")

    with patch("pdd.update_main.update_prompt") as mock_update_prompt, \
         patch("pdd.update_main.get_available_agents") as mock_agents, \
         patch("pdd.update_main.get_language") as mock_get_language:
        mock_update_prompt.return_value = ("fresh prompt", 0.01, "mock-model")
        mock_agents.return_value = []
        mock_get_language.return_value = "python"

        ctx = click.Context(click.Command("update"))
        ctx.obj = {"strength": 0.5, "temperature": 0.0, "verbose": False, "quiet": True}

        # Should not raise UnicodeDecodeError
        update_main(
            ctx=ctx,
            input_prompt_file=None,
            modified_code_file=str(code_file),
            input_code_file=None,
            output=None,
            use_git=False,
        )

    assert mock_update_prompt.called
    kwargs = mock_update_prompt.call_args.kwargs
    assert kwargs["input_prompt"] == "no prompt exists yet, create a new one"


def test_regeneration_mode_uses_sentinel_when_prompt_file_empty(tmp_path, monkeypatch):
    """Empty / whitespace-only prompt file is treated as first-time
    generation — the sentinel is passed through instead of an empty string."""
    from pdd.update_main import update_main

    code_file, _ = _setup_regeneration_repo(
        tmp_path, monkeypatch, prompt_content="   \n\t\n"
    )

    with patch("pdd.update_main.update_prompt") as mock_update_prompt, \
         patch("pdd.update_main.get_available_agents") as mock_agents, \
         patch("pdd.update_main.get_language") as mock_get_language:
        mock_update_prompt.return_value = ("fresh prompt", 0.01, "mock-model")
        mock_agents.return_value = []
        mock_get_language.return_value = "python"

        ctx = click.Context(click.Command("update"))
        ctx.obj = {"strength": 0.5, "temperature": 0.0, "verbose": False, "quiet": True}

        update_main(
            ctx=ctx,
            input_prompt_file=None,
            modified_code_file=str(code_file),
            input_code_file=None,
            output=None,
            use_git=False,
        )

    assert mock_update_prompt.called
    kwargs = mock_update_prompt.call_args.kwargs
    assert kwargs["input_prompt"] == "no prompt exists yet, create a new one"
