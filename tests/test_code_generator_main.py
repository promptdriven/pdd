# Test Plan:
#
# I. Setup and Basic Cases:
# 1.  Test Unreadable/Missing Prompt File:
#     - Input: `prompt_file` path that `construct_paths` indicates as problematic.
#     - Mock: `construct_paths` to return `None` for `current_prompt_content`.
#     - Expected: Error message printed, returns `("", False, 0.0, "")`.
# 2.  Test Unknown Language:
#     - Input: `prompt_file` for which `construct_paths` cannot determine language.
#     - Mock: `construct_paths` to return `None` for `lang`.
#     - Expected: Error message printed, returns `("", False, 0.0, "")`.
# 3.  Test Successful Full Generation (Local Mode, Output to File):
#     - Input: Valid `prompt_file`, `output` path, `ctx` with `local=True`.
#     - Mock: `construct_paths`, `code_generator`, `Path.write_text`.
#     - Expected: `code_generator` called, code written to `output`, correct tuple returned.
# 4.  Test Successful Full Generation (Local Mode, Output to Console if no output path):
#     - Input: Valid `prompt_file`, `ctx` with `local=True`. `construct_paths` returns no `output_code_file`.
#     - Mock: `construct_paths` (to return no output path for "output_code_file"), `code_generator`, `console.print` (for Syntax).
#     - Expected: `code_generator` called, code printed to console, `Path.write_text` not called.
#
# II. Incremental Generation Scenarios:
# 5.  Test Incremental: Output Exists, `original_prompt` Provided (CLI arg):
#     - Input: `prompt_file`, `output` (existing), `original_prompt` (existing).
#     - Mock: `construct_paths`, `Path.exists`, `Path.read_text`, `incremental_code_generator` (success), `_get_git_root` (no git).
#     - Expected: `incremental_code_generator` called, `is_incremental_operation=True`.
# 6.  Test Incremental: Output Exists, Git History for Original Prompt:
#     - Input: `prompt_file`, `output` (existing).
#     - Mock: `construct_paths`, `Path.exists`, `Path.read_text`, `_get_git_root` (returns path), `_run_git_command` (for `git show` and staging), `incremental_code_generator` (success).
#     - Expected: Git commands for original prompt and staging, `incremental_code_generator` called.
# 7.  Test Incremental: Fallback to Full (No Original Prompt, Not in Git):
#     - Input: `prompt_file`, `output` (existing).
#     - Mock: `construct_paths`, `Path.exists`, `Path.read_text`, `_get_git_root` (None or `git show` fails), `code_generator`.
#     - Expected: Fallback to `code_generator`, `is_incremental_operation=False`.
# 8.  Test Incremental: `--incremental` Flag, Output Does Not Exist (Warns & Full Gen):
#     - Input: `prompt_file`, `output` (non-existing), `incremental=True` (CLI flag).
#     - Mock: `construct_paths`, `Path.exists` (False), `code_generator`, `console.print` (for warning).
#     - Expected: Warning, `code_generator` called, `is_incremental_operation=False`.
# 9.  Test Incremental: `incremental_code_generator` Returns `is_incremental=False` (Fallback):
#     - Input: Conditions for incremental met.
#     - Mock: Setup for incremental, `incremental_code_generator` (returns `is_incremental=False`), `code_generator`.
#     - Expected: `incremental_code_generator` called, then `code_generator` called.
# 10. Test Incremental: `incremental_code_generator` Raises Exception (Fallback):
#     - Input: Conditions for incremental met.
#     - Mock: Setup for incremental, `incremental_code_generator` (raises Exception), `code_generator`, `console.print`.
#     - Expected: Error printed, `code_generator` called.
# 11. Test Incremental: Git Staging Logic (via `_stage_file_if_needed` effects):
#     - Verify `_run_git_command` is called for `git add` when a file is untracked or modified.
#     - Mock: `_get_git_root`, `_run_git_command` (to control `git status` output).
#
# III. Cloud vs. Local Execution:
# 12. Test Cloud Execution Success:
#     - Input: Valid `prompt_file`, `output`, `ctx` with `local=False`.
#     - Mock: `construct_paths`, `preprocess`, `os.environ.get` (for keys), `asyncio.run` (for `get_jwt_token`), `requests.post` (success).
#     - Expected: `requests.post` called, cloud result used, local `code_generator` not called.
# 13. Test Cloud Execution: Fallback on `requests.RequestException`:
#     - Input: As above.
#     - Mock: Setup for cloud, `requests.post` (raises `RequestException`), local `code_generator`.
#     - Expected: `requests.post` called, then local `code_generator` called.
# 14. Test Cloud Execution: Fallback on `AuthError` from `get_jwt_token`:
#     - Input: As above.
#     - Mock: Setup for cloud, `asyncio.run` (for `get_jwt_token` raises `AuthError`), local `code_generator`.
#     - Expected: `get_jwt_token` attempted, then local `code_generator` called.
# 15. Test Cloud Execution: Fallback on Missing Firebase API Key:
#     - Input: As above.
#     - Mock: `os.environ.get` (for Firebase key returns `None`), local `code_generator`.
#     - Expected: `requests.post` not called, local `code_generator` called.
# 16. Test Explicit Local Mode (`--local` flag):
#     - Input: `ctx` with `local=True`.
#     - Mock: `construct_paths`, local `code_generator`.
#     - Expected: `requests.post` (cloud) not attempted, local `code_generator` called.
#
# IV. Parameter Handling and Other Edge Cases:
# 17. Test `time`, `strength`, `temperature`, `verbose` Propagation:
#     - Input: `ctx` with specific values.
#     - Mock: `code_generator` and `incremental_code_generator`.
#     - Expected: Mocks called with correct values.
# 18. Test Error During `construct_paths`:
#     - Mock: `construct_paths` (raises Exception).
#     - Expected: Main try-except catches, error printed, returns `("", False, 0.0, "")`.
# 19. Test Error Saving Output File:
#     - Input: Valid generation.
#     - Mock: Successful generation, `Path.write_text` (raises `IOError`), `console.print`.
#     - Expected: Error on save, returns generated code but indicates save failure.
# 20. Test Main Exception Handler:
#     - Mock an internal call (e.g., `preprocess`) to raise an unexpected `RuntimeError`.
#     - Expected: `code_generator_main` catches it, prints error, returns default empty tuple.

import pytest
from unittest.mock import patch, MagicMock, mock_open, ANY, call
import click
import os
import asyncio # For mocking asyncio.run
from pathlib import Path
import json # For cloud response
import shlex # Added for test_incremental_git_history_original_prompt
import requests # Added for test_cloud_execution_fallback_on_request_exception

# Assuming the tests are in tests/ and the module is in pdd/
from pdd.code_generator_main import code_generator_main, CLOUD_FUNCTION_URL
from pdd.get_jwt_token import AuthError #, NetworkError, TokenError, RateLimitError, UserCancelledError (Removed unused imports)
from pdd import DEFAULT_STRENGTH # Import for default value check

# Helper to create a mock Click context
def create_mock_context(verbose: bool = False, force: bool = False, strength: float = DEFAULT_STRENGTH, temperature: float = 0.0, local: bool = False, quiet: bool = False) -> click.Context:
    ctx = click.Context(click.Command("generate"))
    ctx.obj = {
        "verbose": verbose,
        "force": force,
        "strength": strength,
        "temperature": temperature,
        "local": local,
        "quiet": quiet,
    }
    return ctx

@pytest.fixture
def mock_paths_and_files(tmp_path: Path) -> dict[str, str | Path]:
    prompt_file = tmp_path / "test.prompt"
    prompt_file.write_text("A simple prompt")
    output_dir = tmp_path / "output"
    output_dir.mkdir()
    output_file = output_dir / "test.py"
    original_prompt_file = tmp_path / "original.prompt"
    original_prompt_file.write_text("Original prompt")
    return {
        "prompt_file": str(prompt_file),
        "output_file": str(output_file),
        "original_prompt_file": str(original_prompt_file),
        "tmp_path": tmp_path,
    }

# --- Test Cases ---

# I. Setup and Basic Cases
@patch('pdd.code_generator_main.construct_paths')
def test_unreadable_missing_prompt_file(mock_construct: MagicMock, capsys: pytest.CaptureFixture) -> None:
    mock_construct.return_value = ({"prompt_file": None}, {}, "python") # No prompt content
    ctx = create_mock_context()
    result = code_generator_main(ctx, "dummy.prompt", None, None, False, 0.25)
    assert result == ("", False, 0.0, "")
    assert "Error: Could not read prompt file" in capsys.readouterr().out

@patch('pdd.code_generator_main.construct_paths')
def test_unknown_language(mock_construct: MagicMock, capsys: pytest.CaptureFixture) -> None:
    mock_construct.return_value = ({"prompt_file": "content"}, {}, None) # No language
    ctx = create_mock_context()
    result = code_generator_main(ctx, "dummy.prompt", None, None, False, 0.25)
    assert result == ("", False, 0.0, "")
    assert "Error: Could not determine language" in capsys.readouterr().out

@patch('pdd.code_generator_main.Path.write_text')
@patch('pdd.code_generator_main.code_generator')
@patch('pdd.code_generator_main.construct_paths')
def test_successful_full_generation_local_output_to_file(mock_construct: MagicMock, mock_cg: MagicMock, mock_write: MagicMock, mock_paths_and_files: dict[str, str | Path]) -> None:
    mock_construct.return_value = (
        {"prompt_file": "prompt content"},
        {"output_code_file": mock_paths_and_files["output_file"]},
        "python"
    )
    mock_cg.return_value = ("generated code", 0.01, "gpt-local")
    ctx = create_mock_context(local=True, verbose=True)

    code, is_inc, cost, model = code_generator_main(
        ctx, str(mock_paths_and_files["prompt_file"]), str(mock_paths_and_files["output_file"]), None, False, 0.25
    )

    assert code == "generated code"
    assert not is_inc
    assert cost == 0.01
    assert model == "gpt-local"
    mock_cg.assert_called_once_with(
        prompt="prompt content", language="python", strength=DEFAULT_STRENGTH, temperature=0.0, time=0.25, verbose=True
    )
    mock_write.assert_called_once_with("generated code", encoding="utf-8")

@patch('pdd.code_generator_main.console.print')
@patch('pdd.code_generator_main.Path.write_text') # To ensure it's NOT called
@patch('pdd.code_generator_main.code_generator')
@patch('pdd.code_generator_main.construct_paths')
def test_successful_full_generation_local_output_to_console(mock_construct: MagicMock, mock_cg: MagicMock, mock_write: MagicMock, mock_console_print: MagicMock, mock_paths_and_files: dict[str, str | Path]) -> None:
    # Simulate construct_paths returning None for output_code_file path
    mock_construct.return_value = (
        {"prompt_file": "prompt content"},
        {"output_code_file": None}, # Key for output path is None
        "python"
    )
    mock_cg.return_value = ("generated code for console", 0.02, "gpt-local-console")
    ctx = create_mock_context(local=True)

    code, is_inc, cost, model = code_generator_main(
        ctx, str(mock_paths_and_files["prompt_file"]), None, None, False, 0.25 # output=None
    )

    assert code == "generated code for console"
    assert not is_inc
    assert cost == 0.02
    assert model == "gpt-local-console"
    mock_cg.assert_called_once()
    mock_write.assert_not_called()
    # Check if console.print was called with Syntax object (or at least with the code)
    syntax_call_found = any("generated code for console" in c.args[0].code for c in mock_console_print.call_args_list if hasattr(c.args[0], 'code'))
    assert syntax_call_found or any("generated code for console" in str(c.args) for c in mock_console_print.call_args_list)


# II. Incremental Generation
@patch('pdd.code_generator_main.Path')
@patch('pdd.code_generator_main._get_git_root', return_value=None) # No git
@patch('pdd.code_generator_main.incremental_code_generator')
@patch('pdd.code_generator_main.construct_paths')
def test_incremental_output_exists_original_prompt_provided(mock_construct: MagicMock, mock_inc_cg: MagicMock, mock_git_root: MagicMock, MockPathCls: MagicMock, mock_paths_and_files: dict[str, str | Path]) -> None:
    # Setup MockPathCls and instances
    mock_output_path_obj = MagicMock(spec=Path)
    mock_output_path_obj.exists.return_value = True
    mock_output_path_obj.read_text.return_value = "existing code"
    mock_output_path_obj.__str__.return_value = str(mock_paths_and_files["output_file"])
    
    # When Path(str_path) is called, return our mock object
    def path_side_effect(path_arg: str | Path) -> Path | MagicMock:
        if str(path_arg) == mock_paths_and_files["output_file"]:
            return mock_output_path_obj
        elif str(path_arg) == mock_paths_and_files["prompt_file"]: # For .resolve() in _stage_file_if_needed
            m = MagicMock(spec=Path)
            m.resolve.return_value = m 
            m.__str__.return_value = str(path_arg)
            return m
        return Path(path_arg) # Real Path for other cases if any
    MockPathCls.side_effect = path_side_effect


    mock_construct.return_value = (
        {"prompt_file": "new prompt", "original_prompt_file": "original prompt"},
        {"output_code_file": mock_paths_and_files["output_file"]},
        "python"
    )
    mock_inc_cg.return_value = ("updated code", True, 0.03, "gpt-inc")
    ctx = create_mock_context(verbose=True)

    code, is_inc, cost, model = code_generator_main(
        ctx, str(mock_paths_and_files["prompt_file"]), str(mock_paths_and_files["output_file"]), str(mock_paths_and_files["original_prompt_file"]), False, 0.25
    )

    assert code == "updated code"
    assert is_inc
    assert cost == 0.03
    assert model == "gpt-inc"
    mock_inc_cg.assert_called_once_with(
        original_prompt="original prompt", new_prompt="new prompt", existing_code="existing code",
        language="python", strength=DEFAULT_STRENGTH, temperature=0.0, time=0.25,
        force_incremental=False, verbose=True, preprocess_prompt=True
    )
    mock_output_path_obj.write_text.assert_called_once_with("updated code", encoding="utf-8")


@patch('pdd.code_generator_main.Path')
@patch('pdd.code_generator_main._run_git_command')
@patch('pdd.code_generator_main._get_git_root')
@patch('pdd.code_generator_main.incremental_code_generator')
@patch('pdd.code_generator_main.construct_paths')
def test_incremental_git_history_original_prompt(mock_construct: MagicMock, mock_inc_cg: MagicMock, mock_get_git_root: MagicMock, mock_run_git: MagicMock, MockPathCls: MagicMock, mock_paths_and_files: dict[str, str | Path], tmp_path: Path) -> None:
    git_root_path = str(tmp_path / "git_repo")
    Path(git_root_path).mkdir()
    
    # Mock Path objects
    mock_output_path_obj = MagicMock(spec=Path)
    mock_output_path_obj.exists.return_value = True
    mock_output_path_obj.read_text.return_value = "existing code from git version"
    mock_output_path_obj.__str__.return_value = str(mock_paths_and_files["output_file"])
    mock_output_path_obj.resolve.return_value = mock_output_path_obj # for relpath

    mock_prompt_path_obj = MagicMock(spec=Path)
    mock_prompt_path_obj.__str__.return_value = str(mock_paths_and_files["prompt_file"])
    mock_prompt_path_obj.resolve.return_value = mock_prompt_path_obj # for relpath
    mock_prompt_path_obj.is_file.return_value = True
    mock_prompt_path_obj.parent = Path(git_root_path) # Ensure prompt is under git root for _get_git_root

    def path_side_effect(path_arg: str | Path) -> Path | MagicMock:
        path_str = str(path_arg)
        if path_str == mock_paths_and_files["output_file"]:
            return mock_output_path_obj
        if path_str == mock_paths_and_files["prompt_file"]:
            return mock_prompt_path_obj
        
        if path_str == git_root_path:
             p = MagicMock(spec=Path)
             p.__str__.return_value = path_str
             p.is_file.return_value = False 
             return p
        
        p_real = Path(path_str)
        m_real = MagicMock(spec=Path)
        m_real.__str__.return_value = path_str
        m_real.parent = MagicMock(spec=Path)
        m_real.parent.mkdir = MagicMock()
        m_real.exists.return_value = p_real.exists() 
        m_real.is_file.return_value = p_real.is_file()
        m_real.resolve.return_value = m_real 
        return m_real

    MockPathCls.side_effect = path_side_effect
    
    mock_get_git_root.return_value = git_root_path

    def git_command_side_effect(command: list[str], cwd: str | None = None) -> tuple[bool, str]:
        cmd_str = " ".join(command)
        if "git show HEAD:" in cmd_str:
            return True, "original prompt from git"
        if "git status --porcelain" in cmd_str:
            rel_path_prompt = os.path.relpath(str(mock_prompt_path_obj.resolve()), git_root_path)
            rel_path_output = os.path.relpath(str(mock_output_path_obj.resolve()), git_root_path)
            if rel_path_prompt in cmd_str:
                 return True, f"?? {rel_path_prompt}"
            if rel_path_output in cmd_str:
                 return True, f" M {rel_path_output}" 
        if "git add" in cmd_str:
            return True, "added"
        return False, "git command failed"
    mock_run_git.side_effect = git_command_side_effect

    mock_construct.return_value = (
        {"prompt_file": "new prompt content"},
        {"output_code_file": mock_paths_and_files["output_file"]},
        "python"
    )
    mock_inc_cg.return_value = ("git updated code", True, 0.04, "gpt-inc-git")
    ctx = create_mock_context(verbose=True)

    abs_prompt_file_path = Path(git_root_path) / "test.prompt"
    mock_prompt_path_obj.__str__.return_value = str(abs_prompt_file_path)
    mock_prompt_path_obj.resolve.return_value = abs_prompt_file_path

    abs_output_file_path = Path(git_root_path) / "output/test.py"
    mock_output_path_obj.__str__.return_value = str(abs_output_file_path)
    mock_output_path_obj.resolve.return_value = abs_output_file_path
    (Path(git_root_path) / "output").mkdir(exist_ok=True)


    code, is_inc, cost, model = code_generator_main(
        ctx, str(abs_prompt_file_path), str(abs_output_file_path), None, False, 0.25
    )

    assert code == "git updated code"
    assert is_inc
    mock_inc_cg.assert_called_once()
    
    # Check git show call (command is a list of strings)
    # Example: ['git', 'show', 'HEAD:test.prompt']
    show_call_found = False
    for call_args in mock_run_git.call_args_list:
        cmd_list = call_args.args[0]
        if cmd_list[0] == 'git' and cmd_list[1] == 'show' and f"HEAD:{shlex.quote(os.path.relpath(str(abs_prompt_file_path), git_root_path))}" in cmd_list[2]:
            show_call_found = True
            break
    assert show_call_found
    
    add_calls = [c for c in mock_run_git.call_args_list if "add" in c.args[0]]
    assert len(add_calls) == 2 


@patch('pdd.code_generator_main.code_generator')
@patch('pdd.code_generator_main.Path')
@patch('pdd.code_generator_main._get_git_root', return_value=None) # No git
@patch('pdd.code_generator_main.construct_paths')
def test_incremental_fallback_no_original_prompt_not_in_git(mock_construct: MagicMock, mock_git_root: MagicMock, MockPathCls: MagicMock, mock_cg: MagicMock, mock_paths_and_files: dict[str, str | Path], capsys: pytest.CaptureFixture) -> None:
    mock_output_path_obj = MagicMock(spec=Path)
    mock_output_path_obj.exists.return_value = True # Output file exists
    mock_output_path_obj.read_text.return_value = "existing code"
    MockPathCls.side_effect = lambda p: mock_output_path_obj if str(p) == mock_paths_and_files["output_file"] else Path(p)

    mock_construct.return_value = (
        {"prompt_file": "new prompt", "original_prompt_file": None}, # No original_prompt provided
        {"output_code_file": mock_paths_and_files["output_file"]},
        "python"
    )
    mock_cg.return_value = ("full gen code", 0.01, "gpt-fallback")
    ctx = create_mock_context(verbose=True) # verbose to check logs

    code, is_inc, cost, model = code_generator_main(
        ctx, str(mock_paths_and_files["prompt_file"]), str(mock_paths_and_files["output_file"]), None, False, 0.25
    )
    
    assert not is_inc
    assert code == "full gen code"
    mock_cg.assert_called_once()
    captured = capsys.readouterr().out
    assert "Proceeding with Full Code Generation" in captured


@patch('pdd.code_generator_main.code_generator')
@patch('pdd.code_generator_main.Path')
@patch('pdd.code_generator_main.construct_paths')
def test_incremental_flag_output_does_not_exist(mock_construct: MagicMock, MockPathCls: MagicMock, mock_cg: MagicMock, mock_paths_and_files: dict[str, str | Path], capsys: pytest.CaptureFixture) -> None:
    mock_output_path_obj = MagicMock(spec=Path)
    mock_output_path_obj.exists.return_value = False # Output file does NOT exist
    MockPathCls.side_effect = lambda p: mock_output_path_obj if str(p) == mock_paths_and_files["output_file"] else Path(p)

    mock_construct.return_value = (
        {"prompt_file": "new prompt"},
        {"output_code_file": mock_paths_and_files["output_file"]},
        "python"
    )
    mock_cg.return_value = ("full gen code for missing output", 0.01, "gpt-full")
    ctx = create_mock_context()

    # Call with incremental=True (CLI flag)
    code, is_inc, cost, model = code_generator_main(
        ctx, str(mock_paths_and_files["prompt_file"]), str(mock_paths_and_files["output_file"]), None, True, 0.25
    )

    assert not is_inc
    assert code == "full gen code for missing output"
    mock_cg.assert_called_once()
    captured_out = capsys.readouterr().out
    assert "Warning: --incremental flag was set, but output file" in captured_out
    assert "does not exist. Performing full generation." in captured_out


@patch('pdd.code_generator_main.code_generator')
@patch('pdd.code_generator_main.incremental_code_generator')
@patch('pdd.code_generator_main.Path')
@patch('pdd.code_generator_main._get_git_root', return_value=None)
@patch('pdd.code_generator_main.construct_paths')
def test_incremental_returns_is_incremental_false(mock_construct: MagicMock, mock_git_root: MagicMock, MockPathCls: MagicMock, mock_inc_cg: MagicMock, mock_cg: MagicMock, mock_paths_and_files: dict[str, str | Path], capsys: pytest.CaptureFixture) -> None:
    mock_output_path_obj = MagicMock(spec=Path)
    mock_output_path_obj.exists.return_value = True
    mock_output_path_obj.read_text.return_value = "existing code"
    MockPathCls.side_effect = lambda p: mock_output_path_obj if str(p) == mock_paths_and_files["output_file"] else Path(p)
    
    mock_construct.return_value = (
        {"prompt_file": "new prompt", "original_prompt_file": "original prompt"},
        {"output_code_file": mock_paths_and_files["output_file"]},
        "python"
    )
    # Incremental generator decides full regeneration is better
    mock_inc_cg.return_value = ("code from inc but full needed", False, 0.005, "gpt-inc-fallback")
    mock_cg.return_value = ("final full code", 0.01, "gpt-full")
    ctx = create_mock_context(verbose=True)

    code, is_inc, cost, model = code_generator_main(
        ctx, str(mock_paths_and_files["prompt_file"]), str(mock_paths_and_files["output_file"]), str(mock_paths_and_files["original_prompt_file"]), False, 0.25
    )

    assert not is_inc # Overall operation is full
    assert code == "final full code" # Code from full generator
    assert cost == 0.01 # Cost from full generator
    assert model == "gpt-full" # Model from full generator
    mock_inc_cg.assert_called_once()
    mock_cg.assert_called_once()
    assert "Incremental generator suggested full regeneration" in capsys.readouterr().out


# III. Cloud vs. Local
@patch('pdd.code_generator_main.Path.write_text')
@patch('pdd.code_generator_main.requests.post')
@patch('pdd.code_generator_main.asyncio.run')
@patch.dict(os.environ, {"REACT_APP_FIREBASE_API_KEY": "fake_fb_key", "GITHUB_CLIENT_ID": "fake_gh_id"})
@patch('pdd.code_generator_main.preprocess')
@patch('pdd.code_generator_main.construct_paths')
def test_cloud_execution_success(mock_construct: MagicMock, mock_preprocess: MagicMock, mock_asyncio_run: MagicMock, mock_requests_post: MagicMock, mock_write: MagicMock, mock_paths_and_files: dict[str, str | Path]) -> None:
    mock_construct.return_value = (
        {"prompt_file": "cloud prompt"},
        {"output_code_file": mock_paths_and_files["output_file"]},
        "python"
    )
    mock_preprocess.return_value = "processed cloud prompt"
    mock_asyncio_run.return_value = "mock_jwt_token" # For get_jwt_token
    
    mock_response = MagicMock()
    mock_response.json.return_value = {"code": "cloud generated code", "cost": 0.05, "model_name": "gpt-cloud"}
    mock_response.raise_for_status = MagicMock()
    mock_requests_post.return_value = mock_response
    
    ctx = create_mock_context(local=False, verbose=True) # Default is local=False

    code, is_inc, cost, model = code_generator_main(
        ctx, str(mock_paths_and_files["prompt_file"]), str(mock_paths_and_files["output_file"]), None, False, 0.25
    )

    assert code == "cloud generated code"
    assert not is_inc
    assert cost == 0.05
    assert model == "gpt-cloud"
    mock_preprocess.assert_called_once_with("cloud prompt", recursive=True, double_curly_brackets=True, exclude_keys=[])
    mock_asyncio_run.assert_called_once() # With get_jwt_token
    mock_requests_post.assert_called_once_with(
        CLOUD_FUNCTION_URL,
        json={
            "promptContent": "processed cloud prompt", "language": "python",
            "strength": DEFAULT_STRENGTH, "temperature": 0.0, "time": 0.25, "verbose": True,
        },
        headers={"Authorization": "Bearer mock_jwt_token", "Content-Type": "application/json"},
        timeout=ANY # Check that timeout is present
    )
    mock_write.assert_called_once_with("cloud generated code", encoding="utf-8")


@patch('pdd.code_generator_main.code_generator') # Local fallback
@patch('pdd.code_generator_main.requests.post')
@patch('pdd.code_generator_main.asyncio.run', return_value="mock_jwt_token")
@patch.dict(os.environ, {"REACT_APP_FIREBASE_API_KEY": "fake_fb_key", "GITHUB_CLIENT_ID": "fake_gh_id"})
@patch('pdd.code_generator_main.preprocess', return_value="processed_prompt")
@patch('pdd.code_generator_main.construct_paths')
def test_cloud_execution_fallback_on_request_exception(mock_construct: MagicMock, mock_preprocess: MagicMock, mock_async_run: MagicMock, mock_requests_post: MagicMock, mock_local_cg: MagicMock, mock_paths_and_files: dict[str, str | Path], capsys: pytest.CaptureFixture) -> None:
    mock_construct.return_value = ({"prompt_file": "prompt"}, {"output_code_file": mock_paths_and_files["output_file"]}, "python")
    mock_requests_post.side_effect = requests.exceptions.RequestException("Network error")
    mock_local_cg.return_value = ("local fallback code", 0.001, "gpt-local-fallback")
    ctx = create_mock_context(local=False)

    code, is_inc, cost, model = code_generator_main(
        ctx, str(mock_paths_and_files["prompt_file"]), str(mock_paths_and_files["output_file"]), None, False, 0.25
    )

    assert code == "local fallback code"
    assert cost == 0.001
    assert model == "gpt-local-fallback"
    mock_requests_post.assert_called_once()
    mock_local_cg.assert_called_once()
    captured_out = capsys.readouterr().out
    assert "Cloud execution failed: Network error." in captured_out
    assert "Falling back to local execution." in captured_out


@patch('pdd.code_generator_main.code_generator') # Local fallback
@patch('pdd.code_generator_main.asyncio.run')
@patch.dict(os.environ, {"REACT_APP_FIREBASE_API_KEY": "fake_fb_key", "GITHUB_CLIENT_ID": "fake_gh_id"})
@patch('pdd.code_generator_main.preprocess', return_value="processed_prompt")
@patch('pdd.code_generator_main.construct_paths')
def test_cloud_execution_fallback_on_auth_error(mock_construct: MagicMock, mock_preprocess: MagicMock, mock_async_run: MagicMock, mock_local_cg: MagicMock, mock_paths_and_files: dict[str, str | Path], capsys: pytest.CaptureFixture) -> None:
    mock_construct.return_value = ({"prompt_file": "prompt"}, {"output_code_file": mock_paths_and_files["output_file"]}, "python")
    mock_async_run.side_effect = AuthError("Auth failed") # Mock get_jwt_token raising AuthError
    mock_local_cg.return_value = ("local fallback auth error", 0.002, "gpt-local-auth-fallback")
    ctx = create_mock_context(local=False)

    code, is_inc, cost, model = code_generator_main(
        ctx, str(mock_paths_and_files["prompt_file"]), str(mock_paths_and_files["output_file"]), None, False, 0.25
    )
    
    assert code == "local fallback auth error"
    mock_async_run.assert_called_once()
    mock_local_cg.assert_called_once()
    assert "Cloud authentication/token error: Auth failed" in capsys.readouterr().out


@patch('pdd.code_generator_main.code_generator') # Local fallback
@patch('pdd.code_generator_main.requests.post') # To ensure it's NOT called
@patch.dict(os.environ, {"GITHUB_CLIENT_ID": "fake_gh_id"}) # Firebase key missing
@patch('pdd.code_generator_main.preprocess')
@patch('pdd.code_generator_main.construct_paths')
def test_cloud_fallback_missing_firebase_key(mock_construct: MagicMock, mock_preprocess: MagicMock, mock_requests_post: MagicMock, mock_local_cg: MagicMock, mock_paths_and_files: dict[str, str | Path], capsys: pytest.CaptureFixture, monkeypatch: pytest.MonkeyPatch) -> None:
    # Ensure REACT_APP_FIREBASE_API_KEY is not set for this test
    monkeypatch.delenv("REACT_APP_FIREBASE_API_KEY", raising=False)

    mock_construct.return_value = ({"prompt_file": "prompt"}, {"output_code_file": mock_paths_and_files["output_file"]}, "python")
    mock_local_cg.return_value = ("local fallback no key", 0.003, "gpt-local-no-key")
    ctx = create_mock_context(local=False)

    code, is_inc, cost, model = code_generator_main(
        ctx, str(mock_paths_and_files["prompt_file"]), str(mock_paths_and_files["output_file"]), None, False, 0.25
    )

    assert code == "local fallback no key"
    mock_requests_post.assert_not_called() # Cloud should not be attempted
    mock_local_cg.assert_called_once()
    assert "REACT_APP_FIREBASE_API_KEY not found" in capsys.readouterr().out


# IV. Parameter Handling and Other Edge Cases
@patch('pdd.code_generator_main.code_generator')
@patch('pdd.code_generator_main.construct_paths')
def test_parameter_propagation_to_local_generator(mock_construct: MagicMock, mock_cg: MagicMock, mock_paths_and_files: dict[str, str | Path]) -> None:
    mock_construct.return_value = ({"prompt_file": "prompt"}, {"output_code_file": mock_paths_and_files["output_file"]}, "python")
    mock_cg.return_value = ("code", 0.1, "model")
    
    ctx = create_mock_context(local=True, verbose=True, strength=0.8, temperature=0.5)
    time_val = 0.75

    code_generator_main(ctx, str(mock_paths_and_files["prompt_file"]), str(mock_paths_and_files["output_file"]), None, False, time_val)

    mock_cg.assert_called_once_with(
        prompt="prompt", language="python", strength=0.8, temperature=0.5, time=time_val, verbose=True
    )

@patch('pdd.code_generator_main.construct_paths', side_effect=Exception("Construct paths failed"))
def test_error_during_construct_paths(mock_construct_fail: MagicMock, capsys: pytest.CaptureFixture) -> None:
    ctx = create_mock_context()
    result = code_generator_main(ctx, "dummy.prompt", None, None, False, 0.25)
    assert result == ("", False, 0.0, "")
    assert "An unexpected error occurred in code_generator_main: Construct paths failed" in capsys.readouterr().out

@patch('pdd.code_generator_main.Path.write_text', side_effect=IOError("Cannot write"))
@patch('pdd.code_generator_main.code_generator')
@patch('pdd.code_generator_main.construct_paths')
def test_error_saving_output_file(mock_construct: MagicMock, mock_cg: MagicMock, mock_write_fail: MagicMock, mock_paths_and_files: dict[str, str | Path], capsys: pytest.CaptureFixture) -> None:
    mock_construct.return_value = ({"prompt_file": "prompt"}, {"output_code_file": mock_paths_and_files["output_file"]}, "python")
    mock_cg.return_value = ("generated code to save", 0.01, "model")
    ctx = create_mock_context(local=True)

    code, is_inc, cost, model = code_generator_main(
        ctx, str(mock_paths_and_files["prompt_file"]), str(mock_paths_and_files["output_file"]), None, False, 0.25
    )
    
    assert code == "generated code to save" # Code was generated
    captured_out = capsys.readouterr().out
    assert "Error saving generated code" in captured_out
    assert "Cannot write" in captured_out

@patch('pdd.code_generator_main.construct_paths')
@patch('pdd.code_generator_main.preprocess', side_effect=RuntimeError("Unexpected preprocess error"))
def test_main_exception_handler(mock_preprocess_fail: MagicMock, mock_construct: MagicMock, capsys: pytest.CaptureFixture, mock_paths_and_files: dict[str, str | Path], monkeypatch: pytest.MonkeyPatch) -> None:
    # Force cloud path by providing env vars
    monkeypatch.setenv("REACT_APP_FIREBASE_API_KEY", "fake_fb_key")
    monkeypatch.setenv("GITHUB_CLIENT_ID", "fake_gh_id")

    mock_construct.return_value = ({"prompt_file": "prompt"}, {"output_code_file": mock_paths_and_files["output_file"]}, "python")
    ctx = create_mock_context(local=False, verbose=True) # Trigger cloud path where preprocess is called

    result = code_generator_main(ctx, str(mock_paths_and_files["prompt_file"]), str(mock_paths_and_files["output_file"]), None, False, 0.25)
    
    assert result == ("", False, 0.0, "")
    captured = capsys.readouterr().out
    assert "An unexpected error occurred in code_generator_main: Unexpected preprocess error" in captured