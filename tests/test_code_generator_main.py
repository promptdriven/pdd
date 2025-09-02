import asyncio
import json
import os
import pathlib
import shlex
import subprocess
import pytest
from unittest.mock import MagicMock, patch, mock_open, AsyncMock

import click
import requests
from rich.panel import Panel
from rich.text import Text # ADDED THIS IMPORT

# Import the function to be tested using an absolute path
from pdd.code_generator_main import code_generator_main, CLOUD_GENERATE_URL, CLOUD_REQUEST_TIMEOUT
from pdd.get_jwt_token import AuthError, NetworkError, TokenError, UserCancelledError, RateLimitError
from pdd import DEFAULT_TIME # Ensure DEFAULT_TIME is available if mock_ctx doesn't always set 'time'

# Constants for mocking
DEFAULT_MOCK_GENERATED_CODE = "def hello():\n  print('Hello, world!')"
DEFAULT_MOCK_COST = 0.001
DEFAULT_MOCK_MODEL_NAME = "mock_model_v1"
DEFAULT_MOCK_LANGUAGE = "python"

# Test Plan
#
# I. Setup and Mocking (Fixtures)
#    1.  `mock_ctx`: Pytest fixture for `click.Context`.
#    2.  `temp_dir_setup`: Pytest fixture to create temporary directories for prompts, output. Manages cleanup.
#    3.  `git_repo_setup`: Pytest fixture to initialize a temporary git repository, commit files, and provide paths.
#    4.  `mock_env_vars`: Pytest fixture using `monkeypatch` to set/unset environment variables.
#    5.  `mock_construct_paths_fixture`: Autouse fixture to mock `pdd.construct_paths.construct_paths`.
#    6.  `mock_pdd_preprocess_fixture`: Autouse fixture to mock `pdd.preprocess.preprocess`.
#    7.  `mock_local_generator_fixture`: Autouse fixture to mock `pdd.code_generator.local_code_generator_func`.
#    8.  `mock_incremental_generator_fixture`: Autouse fixture to mock `pdd.incremental_code_generator.incremental_code_generator_func`.
#    9.  `mock_get_jwt_token_fixture`: Autouse fixture to mock `pdd.get_jwt_token.get_jwt_token`.
#   10.  `mock_requests_post_fixture`: Autouse fixture to mock `requests.post`.
#   11.  `mock_subprocess_run_fixture`: Autouse fixture to mock `subprocess.run`.
#   12.  `mock_rich_console_fixture`: Autouse fixture to mock `Console.print`.
#
# II. Core Functionality Tests
#
#    A. Full Generation - Local Execution
#        1.  `test_full_gen_local_no_output_file`: Prompt exists, no output file yet. `--local` is True.
#        2.  `test_full_gen_local_output_exists_no_incremental_possible`: Prompt exists, output file exists, but no original prompt source. `--local` is True.
#        3.  `test_full_gen_local_output_to_console`: Prompt exists, no output path specified. `--local` is True, `quiet=False`.
#
#    B. Full Generation - Cloud Execution
#        1.  `test_full_gen_cloud_success`: Prompt exists, no output file. `--local` is False. `get_jwt_token` and `requests.post` succeed.
#        2.  `test_full_gen_cloud_auth_failure_fallback_to_local`: `--local` is False. `get_jwt_token` raises `AuthError`.
#        3.  `test_full_gen_cloud_network_timeout_fallback_to_local`: `--local` is False. `requests.post` raises `requests.exceptions.Timeout`.
#        4.  `test_full_gen_cloud_http_error_fallback_to_local`: `--local` is False. `requests.post` raises `requests.exceptions.HTTPError`.
#        5.  `test_full_gen_cloud_json_error_fallback_to_local`: `--local` is False. `requests.post` returns non-JSON response.
#        6.  `test_full_gen_cloud_no_code_returned_fallback_to_local`: `--local` is False. `requests.post` succeeds but JSON response has no `generatedCode`.
#        7.  `test_full_gen_cloud_missing_env_vars_fallback_to_local`: `--local` is False. Firebase/GitHub env vars not set.
#
#    C. Incremental Generation
#        1.  `test_incremental_gen_with_original_prompt_file`: Prompt, output, and original_prompt_file exist. `incremental_code_generator_func` returns `is_incremental=True`.
#        2.  `test_incremental_gen_with_git_committed_prompt`: Prompt in git, modified. Output file exists. `incremental_code_generator_func` returns `is_incremental=True`.
#        3.  `test_incremental_gen_git_staging_untracked_files`: Prompt is untracked, output file exists. Incremental attempt. `git_add_files` called.
#        4.  `test_incremental_gen_git_staging_modified_files`: Prompt is committed and modified, output file exists. Incremental attempt. `git_add_files` called.
#        5.  `test_incremental_gen_fallback_to_full_on_generator_suggestion`: Conditions for incremental met. `incremental_code_generator_func` returns `is_incremental=False`.
#        6.  `test_incremental_gen_force_incremental_flag_success`: Conditions for incremental met. `force_incremental_flag=True`.
#        7.  `test_incremental_gen_force_incremental_flag_but_no_output_file`: `force_incremental_flag=True`, but no output file. Warns, does full.
#        8.  `test_incremental_gen_force_incremental_flag_but_no_original_prompt`: `force_incremental_flag=True`, output file exists, but no original prompt source. Warns, does full.
#        9.  `test_incremental_gen_no_git_repo_fallback_to_full_if_git_needed`: Output file exists, prompt not in git, no `original_prompt_file` specified. Full generation.
#
#    D. File and Path Handling
#        1.  `test_error_prompt_file_not_found`: `prompt_file` path is invalid.
#        2.  `test_error_original_prompt_file_not_found`: `original_prompt_file_path` is invalid.
#        3.  `test_output_file_creation_and_overwrite`: Test with and without `force=True` when output file exists.
#
#    E. Error and Edge Cases
#        1.  `test_code_generation_fails_no_code_produced`: Generator returns `None` for code.
#        2.  `test_unexpected_exception_during_generation`: Generator raises a generic `Exception`.
#
# III. Git Helper Function Tests (Simplified for brevity, focusing on `code_generator_main`'s usage)
#    *   Git helper tests are implicitly covered by the incremental generation tests that rely on mocked `subprocess.run`.
#       Dedicated tests for git helpers would mock `subprocess.run` and assert behavior of `is_git_repository`,
#       `get_git_committed_content`, `get_file_git_status`, `git_add_files`.
#       For this test suite, we focus on `code_generator_main`'s integration of these.

@pytest.fixture
def mock_ctx(monkeypatch):
    ctx = MagicMock(spec=click.Context)
    ctx.obj = {
        'local': False,
        'strength': 0.5,
        'temperature': 0.0,
        'time': 0.25,
        'verbose': False,
        'force': False,
        'quiet': False,
    }
    return ctx

@pytest.fixture
def temp_dir_setup(tmp_path, monkeypatch):
    output_dir = tmp_path / "output"
    output_dir.mkdir(exist_ok=True)
    
    prompts_dir = tmp_path / "prompts"
    prompts_dir.mkdir(exist_ok=True)

    # Create a dummy PDD_PATH/data for construct_paths if it relies on it
    pdd_path_data = tmp_path / "pdd_root" / "data"
    pdd_path_data.mkdir(parents=True, exist_ok=True)
    (pdd_path_data / "llm_model.csv").write_text("model,cost\nmock,0.01") # Dummy content
    monkeypatch.setenv("PDD_PATH", str(tmp_path / "pdd_root"))

    return {"output_dir": output_dir, "prompts_dir": prompts_dir, "tmp_path": tmp_path}

@pytest.fixture
def git_repo_setup(temp_dir_setup, monkeypatch):
    git_dir = temp_dir_setup["tmp_path"] / "git_repo"
    git_dir.mkdir()
    
    original_subprocess_run = subprocess.run
    
    def mock_git_run_for_setup(*args, **kwargs):
        cmd = args[0]
        cwd_resolved = pathlib.Path(kwargs.get("cwd", str(git_dir))).resolve()
        git_dir_resolved = git_dir.resolve()

        if cmd[0] == "git":
            if cmd[1] == "rev-parse" and "--is-inside-work-tree" in cmd:
                if (git_dir_resolved / ".git").exists() and \
                   (cwd_resolved == git_dir_resolved or str(git_dir_resolved) in str(cwd_resolved)):
                    return subprocess.CompletedProcess(args, 0, stdout="true", stderr="")
                return subprocess.CompletedProcess(args, 0, stdout="false", stderr="")
            if cmd[1] == "rev-parse" and "--show-toplevel" in cmd:
                if (git_dir_resolved / ".git").exists() and \
                   (cwd_resolved == git_dir_resolved or str(git_dir_resolved) in str(cwd_resolved)):
                    return subprocess.CompletedProcess(args, 0, stdout=str(git_dir_resolved), stderr="")
                return subprocess.CompletedProcess(args, 128, stdout="", stderr="Not a git repository")

        return original_subprocess_run(*args, **kwargs)


    monkeypatch.setattr(subprocess, 'run', mock_git_run_for_setup)
    
    (git_dir / ".git").mkdir() 
    
    return git_dir


# --- Start Mocks for PDD internal functions ---
@pytest.fixture
def mock_construct_paths_fixture(monkeypatch):
    mock = MagicMock()
    monkeypatch.setattr("pdd.code_generator_main.construct_paths", mock)
    mock.return_value = (
        {},  # resolved_config
        {"prompt_file": "Test prompt content"}, 
        {"output": "output/test_output.py"}, 
        DEFAULT_MOCK_LANGUAGE
    )
    return mock

@pytest.fixture
def mock_pdd_preprocess_fixture(monkeypatch):
    mock = MagicMock(return_value="Preprocessed prompt content")
    monkeypatch.setattr("pdd.code_generator_main.pdd_preprocess", mock)
    return mock

@pytest.fixture
def mock_local_generator_fixture(monkeypatch):
    mock = MagicMock(return_value=(DEFAULT_MOCK_GENERATED_CODE, DEFAULT_MOCK_COST, DEFAULT_MOCK_MODEL_NAME))
    monkeypatch.setattr("pdd.code_generator_main.local_code_generator_func", mock)
    return mock

@pytest.fixture
def mock_incremental_generator_fixture(monkeypatch):
    mock = MagicMock(return_value=(DEFAULT_MOCK_GENERATED_CODE, True, DEFAULT_MOCK_COST, DEFAULT_MOCK_MODEL_NAME)) 
    monkeypatch.setattr("pdd.code_generator_main.incremental_code_generator_func", mock)
    return mock
# --- End Mocks for PDD internal functions ---

# --- Start Mocks for External Dependencies ---
@pytest.fixture(autouse=True) 
def mock_get_jwt_token_fixture(monkeypatch):
    mock = AsyncMock(return_value="test_jwt_token")
    monkeypatch.setattr("pdd.code_generator_main.get_jwt_token", mock)
    return mock

@pytest.fixture(autouse=True) 
def mock_requests_post_fixture(monkeypatch):
    mock = MagicMock()
    mock_response = MagicMock(spec=requests.Response)
    mock_response.json.return_value = {"generatedCode": DEFAULT_MOCK_GENERATED_CODE, "totalCost": DEFAULT_MOCK_COST, "modelName": "cloud_model"}
    mock_response.status_code = 200
    mock_response.raise_for_status = MagicMock()
    mock.return_value = mock_response
    monkeypatch.setattr("pdd.code_generator_main.requests.post", mock)
    return mock

@pytest.fixture(autouse=True) 
def mock_subprocess_run_fixture(monkeypatch):
    mock = MagicMock(return_value=subprocess.CompletedProcess(args=[], returncode=0, stdout="", stderr=""))
    monkeypatch.setattr("pdd.code_generator_main.subprocess.run", mock) 
    monkeypatch.setattr(subprocess, "run", mock) 
    return mock


@pytest.fixture(autouse=True) 
def mock_rich_console_fixture(monkeypatch):
    mock_console_print = MagicMock()
    monkeypatch.setattr("pdd.code_generator_main.console.print", mock_console_print)
    return mock_console_print

@pytest.fixture
def mock_env_vars(monkeypatch):
    monkeypatch.setenv("NEXT_PUBLIC_FIREBASE_API_KEY", "test_firebase_key")
    monkeypatch.setenv("GITHUB_CLIENT_ID", "test_github_id")

# --- Helper to create files ---
def create_file(path, content=""):
    pathlib.Path(path).parent.mkdir(parents=True, exist_ok=True)
    pathlib.Path(path).write_text(content, encoding="utf-8")

# === Test Cases ===

# A. Full Generation - Local Execution
def test_full_gen_local_no_output_file(
    mock_ctx, temp_dir_setup, mock_construct_paths_fixture, mock_local_generator_fixture, mock_env_vars
):
    mock_ctx.obj['local'] = True
    prompt_file_path = temp_dir_setup["prompts_dir"] / "test_prompt_python.prompt"
    create_file(prompt_file_path, "Local test prompt")
    
    output_file_name = "local_output.py"
    output_file_path_str = str(temp_dir_setup["output_dir"] / output_file_name)

    mock_construct_paths_fixture.return_value = (
        {},  # resolved_config
        {"prompt_file": "Local test prompt"},
        {"output": output_file_path_str}, 
        "python"
    )

    code, incremental, cost, model = code_generator_main(
        mock_ctx, str(prompt_file_path), output_file_path_str, None, False
    )

    assert code == DEFAULT_MOCK_GENERATED_CODE
    assert not incremental
    assert cost == DEFAULT_MOCK_COST
    assert model == DEFAULT_MOCK_MODEL_NAME
    mock_local_generator_fixture.assert_called_once_with(
        prompt="Local test prompt",
        language="python",
        strength=mock_ctx.obj['strength'],
        temperature=mock_ctx.obj['temperature'],
        time=mock_ctx.obj['time'],
        verbose=mock_ctx.obj['verbose'],
        preprocess_prompt=True
    )
    assert (temp_dir_setup["output_dir"] / output_file_name).exists()
    assert (temp_dir_setup["output_dir"] / output_file_name).read_text() == DEFAULT_MOCK_GENERATED_CODE

def test_full_gen_local_output_exists_no_incremental_possible(
    mock_ctx, temp_dir_setup, mock_construct_paths_fixture, mock_local_generator_fixture, mock_subprocess_run_fixture, mock_env_vars
):
    mock_ctx.obj['local'] = True
    prompt_file_path = temp_dir_setup["prompts_dir"] / "test_prompt_python.prompt"
    create_file(prompt_file_path, "Local test prompt")
    
    output_file_name = "existing_local_output.py"
    output_file_path = temp_dir_setup["output_dir"] / output_file_name
    create_file(output_file_path, "Old code")

    mock_construct_paths_fixture.return_value = (
        {},  # resolved_config
        {"prompt_file": "Local test prompt"},
        {"output": str(output_file_path)}, 
        "python"
    )
    
    with patch("pdd.code_generator_main.is_git_repository", return_value=False):
        code, _, _, _ = code_generator_main(
            mock_ctx, str(prompt_file_path), str(output_file_path), None, False
        )

    assert code == DEFAULT_MOCK_GENERATED_CODE
    mock_local_generator_fixture.assert_called_once_with(
        prompt="Local test prompt", language="python", strength=mock_ctx.obj['strength'], temperature=mock_ctx.obj['temperature'], time=mock_ctx.obj['time'], verbose=mock_ctx.obj['verbose'], preprocess_prompt=True
    )
    assert output_file_path.read_text() == DEFAULT_MOCK_GENERATED_CODE


def test_full_gen_local_output_to_console(
    mock_ctx, temp_dir_setup, mock_construct_paths_fixture, mock_local_generator_fixture, mock_rich_console_fixture, mock_env_vars
):
    mock_ctx.obj['local'] = True
    mock_ctx.obj['quiet'] = False 
    prompt_file_path = temp_dir_setup["prompts_dir"] / "test_prompt_python.prompt"
    create_file(prompt_file_path, "Console test prompt")

    mock_construct_paths_fixture.return_value = (
        {},  # resolved_config
        {"prompt_file": "Console test prompt"},
        {"output": None}, 
        "python"
    )

    code, _, _, _ = code_generator_main(
        mock_ctx, str(prompt_file_path), None, None, False
    )

    assert code == DEFAULT_MOCK_GENERATED_CODE
    mock_local_generator_fixture.assert_called_once_with(
        prompt="Console test prompt", language="python", strength=mock_ctx.obj['strength'], temperature=mock_ctx.obj['temperature'], time=mock_ctx.obj['time'], verbose=mock_ctx.obj['verbose'], preprocess_prompt=True
    )
    printed_to_console = False
    for call_args in mock_rich_console_fixture.call_args_list:
        args, _ = call_args
        if args and isinstance(args[0], Panel):
            panel_obj = args[0]
            if hasattr(panel_obj, 'renderable') and isinstance(panel_obj.renderable, Text):
                if DEFAULT_MOCK_GENERATED_CODE in panel_obj.renderable.plain:
                    printed_to_console = True
                    break
    assert printed_to_console


# B. Full Generation - Cloud Execution
def test_full_gen_cloud_success(
    mock_ctx, temp_dir_setup, mock_construct_paths_fixture, mock_pdd_preprocess_fixture,
    mock_get_jwt_token_fixture, mock_requests_post_fixture, mock_env_vars 
):
    mock_ctx.obj['local'] = False
    prompt_file_path = temp_dir_setup["prompts_dir"] / "cloud_prompt_python.prompt"
    create_file(prompt_file_path, "Cloud test prompt")
    
    output_file_name = "cloud_output.py"
    output_file_path_str = str(temp_dir_setup["output_dir"] / output_file_name)

    mock_construct_paths_fixture.return_value = (
        {},  # resolved_config
        {"prompt_file": "Cloud test prompt"},
        {"output": output_file_path_str}, 
        "python"
    )
    mock_pdd_preprocess_fixture.return_value = "Preprocessed cloud prompt"

    code, incremental, cost, model = code_generator_main(
        mock_ctx, str(prompt_file_path), output_file_path_str, None, False
    )

    assert code == DEFAULT_MOCK_GENERATED_CODE
    assert not incremental
    assert cost == DEFAULT_MOCK_COST
    assert model == "cloud_model"
    
    mock_pdd_preprocess_fixture.assert_called_once_with("Cloud test prompt", recursive=True, double_curly_brackets=True, exclude_keys=[])
    mock_get_jwt_token_fixture.assert_called_once() 
    
    mock_requests_post_fixture.assert_called_once_with(
        CLOUD_GENERATE_URL,
        json={
            "promptContent": mock_pdd_preprocess_fixture.return_value,
            "language": "python",
            "strength": mock_ctx.obj['strength'],
            "temperature": mock_ctx.obj['temperature'],
            "verbose": mock_ctx.obj['verbose']
        },
        headers={"Authorization": "Bearer test_jwt_token", "Content-Type": "application/json"},
        timeout=CLOUD_REQUEST_TIMEOUT
    )
    assert (temp_dir_setup["output_dir"] / output_file_name).exists()


@pytest.mark.parametrize("cloud_error, local_fallback_expected", [
    (AuthError("Auth failed"), True),
    (requests.exceptions.Timeout("Timeout"), True),
    (requests.exceptions.HTTPError(response=MagicMock(status_code=500, text="Server Error")), True),
    (json.JSONDecodeError("msg", "doc", 0), True), 
    ("NO_CODE_RETURNED", True), 
])
def test_full_gen_cloud_fallback_scenarios(
    cloud_error, local_fallback_expected, mock_ctx, temp_dir_setup, mock_construct_paths_fixture,
    mock_pdd_preprocess_fixture, mock_get_jwt_token_fixture, mock_requests_post_fixture,
    mock_local_generator_fixture, mock_rich_console_fixture, mock_env_vars 
):
    mock_ctx.obj['local'] = False
    prompt_file_path = temp_dir_setup["prompts_dir"] / "fallback_prompt_python.prompt"
    create_file(prompt_file_path, "Fallback test prompt")
    output_file_path_str = str(temp_dir_setup["output_dir"] / "fallback_output.py")

    mock_construct_paths_fixture.return_value = (
        {},  # resolved_config
        {"prompt_file": "Fallback test prompt"},
        {"output": output_file_path_str}, 
        "python" 
    )
    mock_pdd_preprocess_fixture.return_value = "Preprocessed fallback prompt"

    if isinstance(cloud_error, AuthError):
        mock_get_jwt_token_fixture.side_effect = cloud_error
    elif cloud_error == "NO_CODE_RETURNED":
        mock_response = MagicMock(spec=requests.Response)
        mock_response.json.return_value = {"totalCost": 0.01, "modelName": "cloud_model_no_code"} 
        mock_response.status_code = 200
        mock_response.raise_for_status = MagicMock()
        mock_requests_post_fixture.return_value = mock_response
        mock_requests_post_fixture.side_effect = None 
    elif isinstance(cloud_error, json.JSONDecodeError):
         mock_response = MagicMock(spec=requests.Response)
         mock_response.json.side_effect = cloud_error
         mock_response.status_code = 200
         mock_response.raise_for_status = MagicMock()
         mock_requests_post_fixture.return_value = mock_response
         mock_requests_post_fixture.side_effect = None 
    else: 
        mock_requests_post_fixture.side_effect = cloud_error
        mock_requests_post_fixture.return_value = None 
        if isinstance(cloud_error, requests.exceptions.HTTPError): 
             mock_requests_post_fixture.side_effect.response = cloud_error.response


    code, _, _, _ = code_generator_main(
        mock_ctx, str(prompt_file_path), output_file_path_str, None, False
    )

    if local_fallback_expected:
        mock_local_generator_fixture.assert_called_once_with(
            prompt="Fallback test prompt",
            language="python",
            strength=mock_ctx.obj['strength'],
            temperature=mock_ctx.obj['temperature'],
            time=mock_ctx.obj['time'],
            verbose=mock_ctx.obj['verbose'],
            preprocess_prompt=True
        )
        assert code == DEFAULT_MOCK_GENERATED_CODE
        assert any("falling back to local" in str(call_args[0][0]).lower() for call_args in mock_rich_console_fixture.call_args_list if call_args[0])
    else: 
        mock_local_generator_fixture.assert_not_called()
    
    mock_get_jwt_token_fixture.side_effect = None 
    mock_get_jwt_token_fixture.return_value = "test_jwt_token" 
    mock_requests_post_fixture.side_effect = None
    default_mock_response = MagicMock(spec=requests.Response)
    default_mock_response.json.return_value = {"generatedCode": DEFAULT_MOCK_GENERATED_CODE, "totalCost": DEFAULT_MOCK_COST, "modelName": "cloud_model"}
    default_mock_response.status_code = 200
    default_mock_response.raise_for_status = MagicMock()
    mock_requests_post_fixture.return_value = default_mock_response


def test_full_gen_cloud_missing_env_vars_fallback_to_local(
    mock_ctx, temp_dir_setup, mock_construct_paths_fixture, 
    mock_pdd_preprocess_fixture,
    mock_local_generator_fixture, mock_rich_console_fixture, monkeypatch 
):
    mock_ctx.obj['local'] = False
    prompt_file_path = temp_dir_setup["prompts_dir"] / "env_var_prompt_python.prompt"
    create_file(prompt_file_path, "Env var test prompt")
    output_file_path_str = str(temp_dir_setup["output_dir"] / "env_var_output.py")

    mock_construct_paths_fixture.return_value = (
        {},  # resolved_config
        {"prompt_file": "Env var test prompt"},
        {"output": output_file_path_str}, 
        "python" 
    )
    
    monkeypatch.delenv("NEXT_PUBLIC_FIREBASE_API_KEY", raising=False)
    
    async def mock_get_jwt_token_with_check_for_this_test(firebase_api_key, **kwargs):
        if not os.environ.get("NEXT_PUBLIC_FIREBASE_API_KEY"): 
            raise AuthError("Firebase API key not set.")
        return "test_jwt_token" 
    
    code_generator_main(mock_ctx, str(prompt_file_path), output_file_path_str, None, False)

    mock_local_generator_fixture.assert_called_once_with(
        prompt="Env var test prompt",
        language="python",
        strength=mock_ctx.obj['strength'],
        temperature=mock_ctx.obj['temperature'],
        time=mock_ctx.obj['time'],
        verbose=mock_ctx.obj['verbose'],
        preprocess_prompt=True
    )
    assert any("falling back to local" in str(call_args[0][0]).lower() for call_args in mock_rich_console_fixture.call_args_list if call_args[0])


# C. Incremental Generation
def test_incremental_gen_with_original_prompt_file(
    mock_ctx, temp_dir_setup, mock_construct_paths_fixture, mock_incremental_generator_fixture, mock_env_vars
):
    prompt_file_path = temp_dir_setup["prompts_dir"] / "inc_prompt_python.prompt"
    create_file(prompt_file_path, "New prompt content")
    
    output_file_name = "inc_output.py"
    output_file_path = temp_dir_setup["output_dir"] / output_file_name
    create_file(output_file_path, "Existing code content")

    original_prompt_file_path = temp_dir_setup["prompts_dir"] / "inc_original_python.prompt"
    create_file(original_prompt_file_path, "Original prompt content")

    mock_construct_paths_fixture.return_value = (
        {},  # resolved_config
        {
            "prompt_file": "New prompt content",
            "original_prompt_file": "Original prompt content" 
        },
        {"output": str(output_file_path)}, 
        "python"
    )
    mock_incremental_generator_fixture.return_value = ("Updated code", True, 0.002, "inc_model")

    code, incremental, cost, model = code_generator_main(
        mock_ctx, str(prompt_file_path), str(output_file_path), str(original_prompt_file_path), False
    )

    assert code == "Updated code"
    assert incremental
    assert cost == 0.002
    assert model == "inc_model"
    mock_incremental_generator_fixture.assert_called_once_with(
        original_prompt="Original prompt content",
        new_prompt="New prompt content",
        existing_code="Existing code content",
        language="python",
        strength=0.5, temperature=0.0, time=0.25,
        force_incremental=False, verbose=False, preprocess_prompt=True
    )
    assert output_file_path.read_text() == "Updated code"


def test_incremental_gen_with_git_committed_prompt(
    mock_ctx, temp_dir_setup, git_repo_setup, mock_construct_paths_fixture, 
    mock_incremental_generator_fixture, mock_subprocess_run_fixture, mock_env_vars 
):
    prompt_filename = "git_prompt_python.prompt"
    prompt_file_path_in_git = git_repo_setup / prompt_filename
    original_git_content = "Original git prompt from HEAD"
    create_file(prompt_file_path_in_git, original_git_content) 

    def git_command_side_effect(*args, **kwargs):
        cmd = args[0]
        
        if "git" in cmd and "show" in cmd and f"HEAD:{prompt_filename}" in cmd[2]: 
            if pathlib.Path(kwargs.get("cwd", ".")).resolve() == git_repo_setup.resolve():
                return subprocess.CompletedProcess(cmd, 0, stdout=original_git_content, stderr="")
        if "git" in cmd and "rev-parse" in cmd and "--is-inside-work-tree" in cmd:
            if (git_repo_setup / ".git").exists() and \
               (pathlib.Path(kwargs.get("cwd")).resolve() == git_repo_setup.resolve() or \
                str(git_repo_setup.resolve()) in str(pathlib.Path(kwargs.get("cwd")).resolve())):
                return subprocess.CompletedProcess(cmd, 0, stdout="true", stderr="")
            return subprocess.CompletedProcess(cmd, 0, stdout="false", stderr="")
        if "git" in cmd and "rev-parse" in cmd and "--show-toplevel" in cmd:
            if (git_repo_setup / ".git").exists():
                 return subprocess.CompletedProcess(cmd, 0, stdout=str(git_repo_setup.resolve()), stderr="")
            return subprocess.CompletedProcess(cmd, 128, stdout="", stderr="Not a git repo")
        if "git" in cmd and "status" in cmd and "--porcelain" in cmd and str(prompt_file_path_in_git.resolve()) in cmd:
            return subprocess.CompletedProcess(cmd, 0, stdout=f" M {prompt_filename}", stderr="") 
        if "git" in cmd and "diff" in cmd and "--quiet" in cmd and "HEAD" in cmd and str(prompt_file_path_in_git.resolve()) in cmd:
            return subprocess.CompletedProcess(cmd, 1, stdout="", stderr="") 
        if "git" in cmd and "add" in cmd:
            return subprocess.CompletedProcess(cmd, 0, stdout="", stderr="")
        return subprocess.CompletedProcess(cmd, 0, stdout="default mock stdout", stderr="default mock stderr")

    mock_subprocess_run_fixture.side_effect = git_command_side_effect
    
    new_prompt_content_on_disk = "New git prompt content on disk"
    create_file(prompt_file_path_in_git, new_prompt_content_on_disk) 

    output_file_name = "git_output.py"
    output_file_path = temp_dir_setup["output_dir"] / output_file_name 
    create_file(output_file_path, "Existing code for git test")

    mock_construct_paths_fixture.return_value = (
        {},  # resolved_config
        {"prompt_file": new_prompt_content_on_disk}, 
        {"output": str(output_file_path)}, 
        "python"
    )
    mock_incremental_generator_fixture.return_value = ("Git updated code", True, 0.003, "git_inc_model")

    code, incremental, _, _ = code_generator_main(
        mock_ctx, str(prompt_file_path_in_git), str(output_file_path), None, False
    )

    assert code == "Git updated code"
    assert incremental
    mock_incremental_generator_fixture.assert_called_once_with(
        original_prompt=original_git_content, 
        new_prompt=new_prompt_content_on_disk,
        existing_code="Existing code for git test",
        language="python",
        strength=0.5, temperature=0.0, time=0.25,
        force_incremental=False, verbose=False, preprocess_prompt=True
    )
    add_called_for_prompt = False
    for call in mock_subprocess_run_fixture.call_args_list:
        args_list = call[0][0] 
        if "git" in args_list and "add" in args_list and str(prompt_file_path_in_git.resolve()) in args_list:
            add_called_for_prompt = True
            break
    assert add_called_for_prompt
    mock_subprocess_run_fixture.side_effect = None 


def test_incremental_gen_fallback_to_full_on_generator_suggestion(
    mock_ctx, temp_dir_setup, mock_construct_paths_fixture, 
    mock_pdd_preprocess_fixture,
    mock_incremental_generator_fixture, mock_local_generator_fixture, mock_env_vars
):
    mock_ctx.obj['local'] = True 
    prompt_file_path = temp_dir_setup["prompts_dir"] / "inc_fallback_prompt.prompt"
    create_file(prompt_file_path, "New prompt")
    output_file_path = temp_dir_setup["output_dir"] / "inc_fallback_output.py"
    create_file(output_file_path, "Existing code")
    original_prompt_file_path = temp_dir_setup["prompts_dir"] / "inc_fallback_original.prompt"
    create_file(original_prompt_file_path, "Original prompt")

    mock_construct_paths_fixture.return_value = (
        {},  # resolved_config
        {"prompt_file": "New prompt", "original_prompt_file": "Original prompt"},
        {"output": str(output_file_path)}, 
        "python" 
    )
    mock_incremental_generator_fixture.return_value = (None, False, 0.001, "inc_model_suggests_full")

    code_generator_main(
        mock_ctx, str(prompt_file_path), str(output_file_path), str(original_prompt_file_path), False
    )

    mock_incremental_generator_fixture.assert_called_once_with(
        original_prompt="Original prompt",
        new_prompt="New prompt",
        existing_code="Existing code",
        language="python",
        strength=mock_ctx.obj['strength'],
        temperature=mock_ctx.obj['temperature'],
        time=mock_ctx.obj['time'],
        force_incremental=False,
        verbose=mock_ctx.obj['verbose'],
        preprocess_prompt=True
    )
    mock_local_generator_fixture.assert_called_once_with(
        prompt="New prompt",
        language="python",
        strength=mock_ctx.obj['strength'],
        temperature=mock_ctx.obj['temperature'],
        time=mock_ctx.obj['time'],
        verbose=mock_ctx.obj['verbose'],
        preprocess_prompt=True
    )

def test_incremental_gen_force_incremental_flag_but_no_output_file(
    mock_ctx, temp_dir_setup, mock_construct_paths_fixture, 
    mock_local_generator_fixture, mock_rich_console_fixture, mock_env_vars 
):
    mock_ctx.obj['local'] = True
    prompt_file_path = temp_dir_setup["prompts_dir"] / "force_inc_no_out.prompt"
    create_file(prompt_file_path, "Prompt content")
    output_path_str = str(temp_dir_setup["output_dir"] / "force_inc_no_out.py") 

    mock_construct_paths_fixture.return_value = (
        {},  # resolved_config
        {"prompt_file": "Prompt content"},
        {"output": output_path_str}, 
        "python"
    )
    
    code_generator_main(
        mock_ctx, str(prompt_file_path), output_path_str, None, True 
    )

    mock_local_generator_fixture.assert_called_once() 
    assert any("output file does not exist" in str(call_args[0][0]).lower() for call_args in mock_rich_console_fixture.call_args_list if call_args[0])


# D. File and Path Handling
def test_error_prompt_file_not_found(mock_ctx, mock_construct_paths_fixture, mock_env_vars):
    mock_construct_paths_fixture.side_effect = FileNotFoundError("Prompt file missing")
    
    prompt_file = "non_existent_prompt.prompt"
    
    code, incremental, cost, model = code_generator_main(mock_ctx, prompt_file, None, None, False)

    assert code == ""
    assert not incremental
    assert cost == 0.0
    assert model == "error"
    mock_construct_paths_fixture.side_effect = None 

# E. Error and Edge Cases
def test_code_generation_fails_no_code_produced(
    mock_ctx, temp_dir_setup, mock_construct_paths_fixture, mock_local_generator_fixture, mock_rich_console_fixture, mock_env_vars 
):
    mock_ctx.obj['local'] = True
    prompt_file_path = temp_dir_setup["prompts_dir"] / "no_code_prompt.prompt"
    create_file(prompt_file_path, "Prompt for no code")
    output_path_str = str(temp_dir_setup["output_dir"] / "no_code_output.py")

    mock_construct_paths_fixture.return_value = (
        {},  # resolved_config
        {"prompt_file": "Prompt for no code"},
        {"output": output_path_str}, 
        "python" 
    )
    mock_local_generator_fixture.return_value = (None, 0.0, "model_failed") 

    code, _, _, _ = code_generator_main(mock_ctx, str(prompt_file_path), output_path_str, None, False)
    
    assert code == "" 
    assert any("code generation failed" in str(call_args[0][0]).lower() for call_args in mock_rich_console_fixture.call_args_list if call_args[0])


def test_unexpected_exception_during_generation(
    mock_ctx, temp_dir_setup, mock_construct_paths_fixture, mock_local_generator_fixture, mock_rich_console_fixture, mock_env_vars 
):
    mock_ctx.obj['local'] = True
    mock_ctx.obj['verbose'] = True 
    prompt_file_path = temp_dir_setup["prompts_dir"] / "exception_prompt.prompt"
    create_file(prompt_file_path, "Prompt for exception")
    output_path_str = str(temp_dir_setup["output_dir"] / "exception_output.py")

    mock_construct_paths_fixture.return_value = (
        {},  # resolved_config
        {"prompt_file": "Prompt for exception"},
        {"output": output_path_str}, 
        "python" 
    )
    mock_local_generator_fixture.side_effect = Exception("Unexpected LLM error")

    code, incremental, cost, model = code_generator_main(mock_ctx, str(prompt_file_path), output_path_str, None, False)

    assert code == ""
    assert not incremental 
    assert model == "error"
    
    printed_error = False
    printed_traceback = False
    for call_args in mock_rich_console_fixture.call_args_list:
        args, _ = call_args
        if args:
            arg_str = str(args[0])
            if "unexpected error occurred: unexpected llm error" in arg_str.lower():
                printed_error = True
            if "traceback (most recent call last)" in arg_str.lower():
                printed_traceback = True
    assert printed_error
    assert printed_traceback
    mock_local_generator_fixture.side_effect = None 


# Regression: output provided as directory should not be treated as file
def test_generate_with_output_directory_path_uses_resolved_file_and_succeeds(
    mock_ctx, temp_dir_setup, mock_construct_paths_fixture, mock_local_generator_fixture, mock_env_vars
):
    """
    Intended behavior: when --output is a directory, use the resolved file path
    from construct_paths and write successfully.
    """
    mock_ctx.obj['local'] = True

    prompt_file_path = temp_dir_setup["prompts_dir"] / "dir_output_prompt_python.prompt"
    create_file(prompt_file_path, "Prompt content for dir output")

    resolved_output_file = temp_dir_setup["output_dir"] / "dir_output.py"
    mock_construct_paths_fixture.return_value = (
        {},
        {"prompt_file": "Prompt content for dir output"},
        {"output": str(resolved_output_file)},
        "python",
    )

    # Pass the directory as --output; command main should use resolved file
    raw_output_arg_dir = str(temp_dir_setup["output_dir"])  # directory path
    code, incremental, cost, model = code_generator_main(
        mock_ctx, str(prompt_file_path), raw_output_arg_dir, None, False
    )

    # Expect success and file written to resolved_output_file
    assert code == DEFAULT_MOCK_GENERATED_CODE
    assert model != "error"
    assert not incremental
    assert resolved_output_file.exists()
    assert resolved_output_file.read_text() == DEFAULT_MOCK_GENERATED_CODE
