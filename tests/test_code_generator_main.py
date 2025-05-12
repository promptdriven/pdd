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
        prompt="prompt content", language="python", strength=DEFAULT_STRENGTH, temperature=0.0, verbose=True # No time
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
    mock_cg.assert_called_once() # Will check specific args in test_parameter_propagation
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

    abs_prompt_file_path = Path(git_root_path) / "test.prompt"
    abs_output_file_path = Path(git_root_path) / "output" / "test.py"
    (Path(git_root_path) / "output").mkdir(exist_ok=True)

    mock_output_path_obj = MagicMock(spec=Path)
    mock_output_path_obj.exists.return_value = True
    mock_output_path_obj.read_text.return_value = "existing code from git version"
    mock_output_path_obj.__str__.return_value = str(abs_output_file_path)
    mock_output_path_obj.resolve.return_value = abs_output_file_path
    mock_output_path_obj.parent = abs_output_file_path.parent

    mock_prompt_path_obj = MagicMock(spec=Path)
    mock_prompt_path_obj.__str__.return_value = str(abs_prompt_file_path)
    mock_prompt_path_obj.resolve.return_value = abs_prompt_file_path
    mock_prompt_path_obj.is_file.return_value = True
    mock_prompt_path_obj.parent = abs_prompt_file_path.parent

    def path_side_effect(path_arg: str | Path) -> Path | MagicMock:
        path_str = str(path_arg)
        if path_str == str(abs_output_file_path):
            return mock_output_path_obj
        if path_str == str(abs_prompt_file_path):
            return mock_prompt_path_obj
        if path_str == git_root_path:
             p_git_root = MagicMock(spec=Path)
             p_git_root.__str__.return_value = path_str
             p_git_root.is_file.return_value = False
             p_git_root.resolve.return_value = p_git_root
             return p_git_root
        p_real = Path(path_str)
        m_real = MagicMock(spec=Path)
        m_real.__str__.return_value = path_str
        m_real.parent = MagicMock(spec=Path, __str__=lambda:str(p_real.parent))
        m_real.parent.mkdir = MagicMock()
        m_real.exists.return_value = p_real.exists()
        m_real.is_file.return_value = p_real.is_file()
        m_real.resolve.return_value = m_real
        m_real.read_text = lambda encoding: p_real.read_text(encoding=encoding) if p_real.exists() else ""
        return m_real

    MockPathCls.side_effect = path_side_effect
    mock_get_git_root.return_value = git_root_path

    def git_command_side_effect(command_str: str, cwd: str | None = None) -> tuple[bool, str]: # Corrected signature
        command_list = shlex.split(command_str) # Added shlex.split

        expected_raw_rel_prompt_path = os.path.relpath(str(abs_prompt_file_path), git_root_path)
        expected_quoted_rel_prompt_path_for_show = shlex.quote(expected_raw_rel_prompt_path)
        if command_list[0] == 'git' and command_list[1] == 'show' and \
           command_list[2] == f"HEAD:{expected_quoted_rel_prompt_path_for_show}":
            return True, "original prompt from git"

        if command_list[0] == 'git' and command_list[1] == 'status' and \
           command_list[2] == '--porcelain' and command_list[3] == '--':
            path_in_cmd_arg = command_list[4]
            unquoted_rel_prompt = os.path.relpath(str(abs_prompt_file_path), git_root_path)
            unquoted_rel_output = os.path.relpath(str(abs_output_file_path), git_root_path)
            if path_in_cmd_arg == shlex.quote(unquoted_rel_prompt):
                 return True, f"?? {unquoted_rel_prompt}"
            if path_in_cmd_arg == shlex.quote(unquoted_rel_output):
                 return True, f" M {unquoted_rel_output}" # Note the leading space for modified
        
        if command_list[0] == 'git' and command_list[1] == 'add' and command_list[2] == '--':
            return True, "added"
            
        return False, f"git command failed (unmocked in test for command: {command_str})" # Use command_str
    mock_run_git.side_effect = git_command_side_effect

    mock_construct.return_value = (
        {"prompt_file": "new prompt content"},
        {"output_code_file": str(abs_output_file_path)},
        "python"
    )
    mock_inc_cg.return_value = ("git updated code", True, 0.04, "gpt-inc-git")
    ctx = create_mock_context(verbose=True)

    code, is_inc, cost, model = code_generator_main(
        ctx, str(abs_prompt_file_path), str(abs_output_file_path), None, False, 0.25
    )

    assert code == "git updated code"
    assert is_inc
    assert cost == 0.04
    assert model == "gpt-inc-git"
    mock_inc_cg.assert_called_once()
    
    show_call_found = False
    expected_show_cmd_str_part = f"git show HEAD:{shlex.quote(os.path.relpath(str(abs_prompt_file_path), git_root_path))}"
    for call_args in mock_run_git.call_args_list:
        cmd_str_arg = call_args.args[0] 
        if cmd_str_arg.startswith("git show") and expected_show_cmd_str_part in cmd_str_arg :
            show_call_found = True
            break
    assert show_call_found, f"Git show call not found or incorrect. Expected part: {expected_show_cmd_str_part}. Calls: {mock_run_git.call_args_list}"
    
    add_calls = [c for c in mock_run_git.call_args_list if c.args[0].startswith("git add")]
    assert len(add_calls) == 2, f"Expected 2 git add calls, got {len(add_calls)}. Calls: {mock_run_git.call_args_list}"


@patch('pdd.code_generator_main.code_generator')
@patch('pdd.code_generator_main.Path')
@patch('pdd.code_generator_main._get_git_root', return_value=None)  # No git
@patch('pdd.code_generator_main.construct_paths')
def test_incremental_fallback_no_original_prompt_not_in_git(
    mock_construct: MagicMock,
    mock_git_root: MagicMock,
    MockPathCls: MagicMock,
    mock_cg: MagicMock,
    mock_paths_and_files: dict[str, str | Path],
    capsys: pytest.CaptureFixture
) -> None:
    mock_output_path_obj = MagicMock(spec=Path)
    mock_output_path_obj.exists.return_value = True
    mock_output_path_obj.read_text.return_value = "existing code"
    mock_output_path_obj.__str__.return_value = "output/test.py"  # Use short path for test

    def path_side_effect(path_arg: str | Path) -> Path | MagicMock:
        if str(path_arg) == mock_paths_and_files["output_file"]:
            return mock_output_path_obj
        if str(path_arg) == mock_paths_and_files["prompt_file"]:
            mp = MagicMock(spec=Path)
            mp.__str__.return_value = str(path_arg)
            mp.resolve.return_value = mp
            mp.is_file.return_value = True
            mp.parent = MagicMock(spec=Path)
            return mp
        return Path(path_arg)

    MockPathCls.side_effect = path_side_effect

    mock_construct.return_value = (
        {"prompt_file": "new prompt", "original_prompt_file": None},
        {"output_code_file": mock_paths_and_files["output_file"]},
        "python"
    )
    mock_cg.return_value = ("full gen code", 0.01, "gpt-fallback")
    ctx = create_mock_context(verbose=True)

    code, is_inc, cost, model = code_generator_main(
        ctx,
        str(mock_paths_and_files["prompt_file"]),
        str(mock_paths_and_files["output_file"]),
        None,
        False,
        0.25
    )

    assert not is_inc
    assert code == "full gen code"
    mock_cg.assert_called_once()

    captured = capsys.readouterr().out

    # Check for key parts of the message separately
    assert "Output file" in captured
    assert "exists" in captured
    assert "original prompt" in captured
    assert "checked CLI arg" in captured
    assert "Proceeding with Full Code Generation" in captured  # Updated to match actual output


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


@pytest.mark.filterwarnings("ignore:coroutine 'get_jwt_token' was never awaited:RuntimeWarning")
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


@pytest.mark.filterwarnings("ignore:coroutine 'get_jwt_token' was never awaited:RuntimeWarning")
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

    ctx = create_mock_context(local=True, verbose=True, strength=0.9, temperature=0.5)
    time_val = 0.75 # This time_val is passed to code_generator_main

    code_generator_main(ctx, str(mock_paths_and_files["prompt_file"]), str(mock_paths_and_files["output_file"]), None, False, time_val)

    mock_cg.assert_called_once_with(
        prompt="prompt", language="python", strength=0.9, temperature=0.5, verbose=True # No time
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
