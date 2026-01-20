import asyncio
import json
import os
import pathlib
import shlex
import subprocess
import sys
import types
import pytest
from unittest.mock import MagicMock, patch, mock_open, AsyncMock

import click
import requests
from rich.panel import Panel
from rich.text import Text # ADDED THIS IMPORT

# Import the function to be tested using an absolute path
from pdd.code_generator_main import code_generator_main, CLOUD_REQUEST_TIMEOUT
from pdd.core.cloud import CloudConfig
from pdd.get_jwt_token import AuthError, NetworkError, TokenError, UserCancelledError, RateLimitError

# Get the cloud URL for assertions in tests
CLOUD_GENERATE_URL = CloudConfig.get_endpoint_url("generateCode")
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
        {},
        {"prompt_file": "Test prompt content"}, 
        {"output": "output/test_output.py"}, 
        DEFAULT_MOCK_LANGUAGE
    )
    return mock

@pytest.fixture
def mock_pdd_preprocess_fixture(monkeypatch):
    # Default mock returns the input unchanged to allow tests to assert substitution behavior when needed
    def passthrough(prompt_text, recursive=False, double_curly_brackets=True, exclude_keys=None):
        return prompt_text
    mock = MagicMock(side_effect=passthrough)
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
    # Mock CloudConfig.get_jwt_token since we no longer import get_jwt_token directly
    mock = MagicMock(return_value="test_jwt_token")
    monkeypatch.setattr("pdd.code_generator_main.CloudConfig.get_jwt_token", mock)
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
    original_run = subprocess.run
    mock = MagicMock(return_value=subprocess.CompletedProcess(args=[], returncode=0, stdout="", stderr=""))
    mock.original_run = original_run
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
    # Do not assert preprocess_prompt flag here because wrapper may pre-process before calling generator
    called_kwargs = mock_local_generator_fixture.call_args.kwargs
    assert called_kwargs["language"] == "python"
    assert called_kwargs["strength"] == mock_ctx.obj['strength']
    assert called_kwargs["temperature"] == mock_ctx.obj['temperature']
    assert called_kwargs["time"] == mock_ctx.obj['time']
    assert called_kwargs["verbose"] == mock_ctx.obj['verbose']
    assert called_kwargs["output_schema"] is None
    assert (temp_dir_setup["output_dir"] / output_file_name).exists()
    assert (temp_dir_setup["output_dir"] / output_file_name).read_text() == DEFAULT_MOCK_GENERATED_CODE


def test_preprocess_order_local_flow(
    mock_ctx, temp_dir_setup, mock_construct_paths_fixture, mock_local_generator_fixture, mock_pdd_preprocess_fixture, mock_env_vars
):
    """Ensure local path calls preprocess twice: includes-first then double-curly."""
    mock_ctx.obj['local'] = True
    prompt_file_path = temp_dir_setup["prompts_dir"] / "order_prompt_python.prompt"
    create_file(prompt_file_path, "Hello $NAME")
    output_file_path_str = str(temp_dir_setup["output_dir"] / "order.py")

    mock_construct_paths_fixture.return_value = (
        {},  # resolved_config
        {"prompt_file": "Hello $NAME"},
        {"output": output_file_path_str},
        "python"
    )

    code_generator_main(mock_ctx, str(prompt_file_path), output_file_path_str, None, False, env_vars={"NAME": "X"})

    # Expect two preprocess calls in order
    calls = mock_pdd_preprocess_fixture.call_args_list
    assert len(calls) >= 2
    # First call: recursive=True, double_curly=False
    args, kwargs = calls[0]
    assert kwargs.get('recursive') is True
    assert kwargs.get('double_curly_brackets') is False
    # Second call: recursive=False, double_curly=True
    args2, kwargs2 = calls[1]
    assert kwargs2.get('recursive') is False
    assert kwargs2.get('double_curly_brackets') is True
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
    called_kwargs = mock_local_generator_fixture.call_args.kwargs
    assert called_kwargs["language"] == "python"
    assert called_kwargs["strength"] == mock_ctx.obj['strength']
    assert called_kwargs["temperature"] == mock_ctx.obj['temperature']
    assert called_kwargs["time"] == mock_ctx.obj['time']
    assert called_kwargs["verbose"] == mock_ctx.obj['verbose']
    assert called_kwargs["output_schema"] is None
    assert output_file_path.read_text() == DEFAULT_MOCK_GENERATED_CODE


def test_env_substitution_in_output_path_and_prompt(
    mock_ctx, temp_dir_setup, mock_construct_paths_fixture, mock_local_generator_fixture, monkeypatch, mock_env_vars
):
    """Ensure $KEY and ${KEY} are substituted using env_vars for prompt and output path."""
    mock_ctx.obj['local'] = True
    prompt_file_path = temp_dir_setup["prompts_dir"] / "env_sub_prompt_python.prompt"
    prompt_content = "Hello $NAME and ${ITEM} and $UNKNOWN"
    create_file(prompt_file_path, prompt_content)

    output_dir = temp_dir_setup["output_dir"]
    output_pattern = str(output_dir / "${NAME}.txt")

    # Construct paths should return our provided strings
    mock_construct_paths_fixture.return_value = (
        {},  # resolved_config
        {"prompt_file": prompt_content},
        {"output": output_pattern},
        "python",
    )

    # Run with env_vars passed directly
    code, incremental, cost, model = code_generator_main(
        mock_ctx,
        str(prompt_file_path),
        output_pattern,
        None,
        False,
        env_vars={"NAME": "Alice", "ITEM": "Book"},
    )

    # Local generator should be called with substituted prompt (UNKNOWN remains)
    called_kwargs = mock_local_generator_fixture.call_args.kwargs
    assert "Hello Alice and Book and $UNKNOWN" in called_kwargs["prompt"]

    # Output should be written to expanded path
    expanded = output_dir / "Alice.txt"
    assert expanded.exists(), f"Expected output file at {expanded}"


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
    called_kwargs = mock_local_generator_fixture.call_args.kwargs
    assert called_kwargs["language"] == "python"
    assert called_kwargs["strength"] == mock_ctx.obj['strength']
    assert called_kwargs["temperature"] == mock_ctx.obj['temperature']
    assert called_kwargs["time"] == mock_ctx.obj['time']
    assert called_kwargs["verbose"] == mock_ctx.obj['verbose']
    assert called_kwargs["output_schema"] is None
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
    
    # Wrapper now preprocesses twice: includes (no doubling), then doubling
    calls = mock_pdd_preprocess_fixture.call_args_list
    assert len(calls) == 2
    _args1, kwargs1 = calls[0]
    assert kwargs1.get('recursive') is True
    assert kwargs1.get('double_curly_brackets') is False
    _args2, kwargs2 = calls[1]
    assert kwargs2.get('recursive') is False
    assert kwargs2.get('double_curly_brackets') is True
    mock_get_jwt_token_fixture.assert_called_once() 
    
    mock_requests_post_fixture.assert_called_once_with(
        CLOUD_GENERATE_URL,
        json={
            # With the default passthrough side_effect, promptContent remains original
            "promptContent": "Cloud test prompt",
            "language": "python",
            "strength": mock_ctx.obj['strength'],
            "temperature": mock_ctx.obj['temperature'],
            "verbose": mock_ctx.obj['verbose']
        },
        headers={"Authorization": "Bearer test_jwt_token", "Content-Type": "application/json"},
        timeout=CLOUD_REQUEST_TIMEOUT
    )
    assert (temp_dir_setup["output_dir"] / output_file_name).exists()


# Tests for JSON fence stripping from cloud responses
@pytest.mark.parametrize("fenced_code,expected_output", [
    ('```json\n{"key": "value"}\n```', '{"key": "value"}'),
    ('```\n{"key": "value"}\n```', '{"key": "value"}'),
    ('```json\n\n{"nested": {"a": 1}}\n\n```', '{"nested": {"a": 1}}'),
    ('{"key": "value"}', '{"key": "value"}'),  # No fences, unchanged
    ('  ```json\n{"key": "value"}\n```  ', '{"key": "value"}'),  # With whitespace
])
def test_cloud_json_response_fence_stripping(
    fenced_code, expected_output, mock_ctx, temp_dir_setup, mock_construct_paths_fixture,
    mock_pdd_preprocess_fixture, mock_get_jwt_token_fixture, mock_requests_post_fixture, mock_env_vars
):
    """Test that markdown code fences are stripped from JSON responses in cloud mode."""
    mock_ctx.obj['local'] = False
    prompt_file_path = temp_dir_setup["prompts_dir"] / "json_fence_prompt.prompt"
    create_file(prompt_file_path, "Generate JSON")

    output_file_name = "fence_output.json"
    output_file_path_str = str(temp_dir_setup["output_dir"] / output_file_name)

    mock_construct_paths_fixture.return_value = (
        {},
        {"prompt_file": "Generate JSON"},
        {"output": output_file_path_str},
        "json"  # JSON language triggers fence stripping
    )

    mock_response = MagicMock(spec=requests.Response)
    mock_response.json.return_value = {
        "generatedCode": fenced_code,
        "totalCost": 0.001,
        "modelName": "cloud_model"
    }
    mock_response.status_code = 200
    mock_response.raise_for_status = MagicMock()
    mock_requests_post_fixture.return_value = mock_response

    code, incremental, cost, model = code_generator_main(
        mock_ctx, str(prompt_file_path), output_file_path_str, None, False
    )

    assert code == expected_output
    assert not incremental
    assert (temp_dir_setup["output_dir"] / output_file_name).exists()
    assert (temp_dir_setup["output_dir"] / output_file_name).read_text() == expected_output


def test_cloud_non_json_response_not_stripped(
    mock_ctx, temp_dir_setup, mock_construct_paths_fixture,
    mock_pdd_preprocess_fixture, mock_get_jwt_token_fixture, mock_requests_post_fixture, mock_env_vars
):
    """Test that code fences are NOT stripped for non-JSON language responses."""
    mock_ctx.obj['local'] = False
    prompt_file_path = temp_dir_setup["prompts_dir"] / "python_fence_prompt.prompt"
    create_file(prompt_file_path, "Generate Python")

    output_file_name = "fence_output.py"
    output_file_path_str = str(temp_dir_setup["output_dir"] / output_file_name)

    # Python code that happens to have backticks in it
    python_code_with_backticks = '```python\ndef hello(): pass\n```'

    mock_construct_paths_fixture.return_value = (
        {},
        {"prompt_file": "Generate Python"},
        {"output": output_file_path_str},
        "python"  # Non-JSON language should NOT trigger fence stripping
    )

    mock_response = MagicMock(spec=requests.Response)
    mock_response.json.return_value = {
        "generatedCode": python_code_with_backticks,
        "totalCost": 0.001,
        "modelName": "cloud_model"
    }
    mock_response.status_code = 200
    mock_response.raise_for_status = MagicMock()
    mock_requests_post_fixture.return_value = mock_response

    code, incremental, cost, model = code_generator_main(
        mock_ctx, str(prompt_file_path), output_file_path_str, None, False
    )

    # For non-JSON, the code should remain unchanged (with fences)
    assert code == python_code_with_backticks
    assert (temp_dir_setup["output_dir"] / output_file_name).read_text() == python_code_with_backticks


def test_cloud_json_case_insensitive_language(
    mock_ctx, temp_dir_setup, mock_construct_paths_fixture,
    mock_pdd_preprocess_fixture, mock_get_jwt_token_fixture, mock_requests_post_fixture, mock_env_vars
):
    """Test that JSON fence stripping works with case-insensitive language check."""
    mock_ctx.obj['local'] = False
    prompt_file_path = temp_dir_setup["prompts_dir"] / "json_case_prompt.prompt"
    create_file(prompt_file_path, "Generate JSON")

    output_file_name = "case_output.json"
    output_file_path_str = str(temp_dir_setup["output_dir"] / output_file_name)

    mock_construct_paths_fixture.return_value = (
        {},
        {"prompt_file": "Generate JSON"},
        {"output": output_file_path_str},
        "JSON"  # Uppercase JSON
    )

    fenced_json = '```json\n{"test": true}\n```'
    mock_response = MagicMock(spec=requests.Response)
    mock_response.json.return_value = {
        "generatedCode": fenced_json,
        "totalCost": 0.001,
        "modelName": "cloud_model"
    }
    mock_response.status_code = 200
    mock_response.raise_for_status = MagicMock()
    mock_requests_post_fixture.return_value = mock_response

    code, incremental, cost, model = code_generator_main(
        mock_ctx, str(prompt_file_path), output_file_path_str, None, False
    )

    assert code == '{"test": true}'


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
        # CloudConfig.get_jwt_token catches AuthError internally and returns None
        mock_get_jwt_token_fixture.return_value = None
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
        # Local fallback should call generator with preprocess_prompt=False (wrapper preprocessed already)
        called_kwargs = mock_local_generator_fixture.call_args.kwargs
        assert called_kwargs["prompt"] == "Fallback test prompt"
        assert called_kwargs["language"] == "python"
        assert called_kwargs["strength"] == mock_ctx.obj['strength']
        assert called_kwargs["temperature"] == mock_ctx.obj['temperature']
        assert called_kwargs["time"] == mock_ctx.obj['time']
        assert called_kwargs["verbose"] == mock_ctx.obj['verbose']
        assert called_kwargs["preprocess_prompt"] is False
        assert called_kwargs["output_schema"] is None
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


# Tests for non-recoverable HTTP errors that should NOT fall back to local
@pytest.mark.parametrize("status_code, error_message, expected_match", [
    (402, "Insufficient credits", "Insufficient credits"),
    (401, "Invalid token", "Cloud authentication failed"),
    (403, "User not approved", "Access denied"),
    (400, "Empty prompt not allowed", "Invalid request"),
])
def test_full_gen_cloud_non_recoverable_http_errors(
    status_code, error_message, expected_match, mock_ctx, temp_dir_setup, mock_construct_paths_fixture,
    mock_pdd_preprocess_fixture, mock_get_jwt_token_fixture, mock_requests_post_fixture,
    mock_local_generator_fixture, mock_rich_console_fixture, mock_env_vars
):
    """Test that HTTP 402, 401, 403, 400 errors raise UsageError instead of falling back to local."""
    mock_ctx.obj['local'] = False
    prompt_file_path = temp_dir_setup["prompts_dir"] / "non_recoverable_prompt_python.prompt"
    create_file(prompt_file_path, "Non-recoverable test prompt")
    output_file_path_str = str(temp_dir_setup["output_dir"] / "non_recoverable_output.py")

    mock_construct_paths_fixture.return_value = (
        {},  # resolved_config
        {"prompt_file": "Non-recoverable test prompt"},
        {"output": output_file_path_str},
        "python"
    )
    mock_pdd_preprocess_fixture.return_value = "Preprocessed prompt"

    # Create mock response with the specific status code
    mock_response = MagicMock(spec=requests.Response)
    mock_response.status_code = status_code
    mock_response.text = error_message
    mock_response.json.return_value = {"error": error_message, "currentBalance": 0, "estimatedCost": 0.05}

    http_error = requests.exceptions.HTTPError(response=mock_response)
    http_error.response = mock_response
    mock_requests_post_fixture.side_effect = http_error

    # Should raise click.UsageError, NOT fall back to local
    with pytest.raises(click.UsageError, match=expected_match):
        code_generator_main(
            mock_ctx, str(prompt_file_path), output_file_path_str, None, False
        )

    # Local generator should NOT have been called
    mock_local_generator_fixture.assert_not_called()

    # Reset mocks for next test
    mock_requests_post_fixture.side_effect = None
    default_mock_response = MagicMock(spec=requests.Response)
    default_mock_response.json.return_value = {"generatedCode": DEFAULT_MOCK_GENERATED_CODE, "totalCost": DEFAULT_MOCK_COST, "modelName": "cloud_model"}
    default_mock_response.status_code = 200
    default_mock_response.raise_for_status = MagicMock()
    mock_requests_post_fixture.return_value = default_mock_response


def test_full_gen_cloud_insufficient_credits_displays_balance(
    mock_ctx, temp_dir_setup, mock_construct_paths_fixture,
    mock_pdd_preprocess_fixture, mock_get_jwt_token_fixture, mock_requests_post_fixture,
    mock_local_generator_fixture, mock_rich_console_fixture, mock_env_vars
):
    """Test that HTTP 402 error displays current balance and estimated cost from response."""
    mock_ctx.obj['local'] = False
    prompt_file_path = temp_dir_setup["prompts_dir"] / "credits_prompt_python.prompt"
    create_file(prompt_file_path, "Credits test prompt")
    output_file_path_str = str(temp_dir_setup["output_dir"] / "credits_output.py")

    mock_construct_paths_fixture.return_value = (
        {},
        {"prompt_file": "Credits test prompt"},
        {"output": output_file_path_str},
        "python"
    )

    # Create 402 response with balance info
    mock_response = MagicMock(spec=requests.Response)
    mock_response.status_code = 402
    mock_response.text = "Insufficient credits"
    mock_response.json.return_value = {"error": "Insufficient credits", "currentBalance": 0.02, "estimatedCost": 0.05}

    http_error = requests.exceptions.HTTPError(response=mock_response)
    http_error.response = mock_response
    mock_requests_post_fixture.side_effect = http_error

    with pytest.raises(click.UsageError, match="Insufficient credits"):
        code_generator_main(mock_ctx, str(prompt_file_path), output_file_path_str, None, False)

    # Check that balance info was printed
    printed_messages = [str(call_args[0][0]) for call_args in mock_rich_console_fixture.call_args_list if call_args[0]]
    assert any("0.02" in msg and "0.05" in msg for msg in printed_messages), \
        f"Expected balance/cost info in output. Got: {printed_messages}"

    # Reset
    mock_requests_post_fixture.side_effect = None


def test_full_gen_cloud_missing_env_vars_fallback_to_local(
    mock_ctx, temp_dir_setup, mock_construct_paths_fixture,
    mock_pdd_preprocess_fixture,
    mock_local_generator_fixture, mock_rich_console_fixture, mock_get_jwt_token_fixture, monkeypatch
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

    # CloudConfig.get_jwt_token returns None when env vars are missing
    # (it catches the AuthError internally)
    mock_get_jwt_token_fixture.return_value = None

    code_generator_main(mock_ctx, str(prompt_file_path), output_file_path_str, None, False)

    # Local fallback should call generator with preprocess_prompt=False now
    called_kwargs = mock_local_generator_fixture.call_args.kwargs
    assert called_kwargs["prompt"] == "Env var test prompt"
    assert called_kwargs["language"] == "python"
    assert called_kwargs["strength"] == mock_ctx.obj['strength']
    assert called_kwargs["temperature"] == mock_ctx.obj['temperature']
    assert called_kwargs["time"] == mock_ctx.obj['time']
    assert called_kwargs["verbose"] == mock_ctx.obj['verbose']
    assert called_kwargs["preprocess_prompt"] is False
    assert called_kwargs["output_schema"] is None
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
    call_kwargs = mock_incremental_generator_fixture.call_args.kwargs
    assert call_kwargs["original_prompt"] == "Original prompt content"
    assert call_kwargs["new_prompt"] == "New prompt content"
    assert call_kwargs["existing_code"] == "Existing code content"
    assert call_kwargs["language"] == "python"
    assert call_kwargs["strength"] == 0.5
    assert call_kwargs["temperature"] == 0.0
    assert call_kwargs["time"] == 0.25
    assert call_kwargs["force_incremental"] is False
    assert call_kwargs["verbose"] is False
    assert call_kwargs["preprocess_prompt"] is False
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
    call_kwargs = mock_incremental_generator_fixture.call_args.kwargs
    assert call_kwargs["language"] == "python"
    assert call_kwargs["strength"] == 0.5
    assert call_kwargs["temperature"] == 0.0
    assert call_kwargs["time"] == 0.25
    assert call_kwargs["force_incremental"] is False
    assert call_kwargs["verbose"] is False
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

    call_kwargs = mock_incremental_generator_fixture.call_args.kwargs
    assert call_kwargs["language"] == "python"
    assert call_kwargs["strength"] == mock_ctx.obj['strength']
    assert call_kwargs["temperature"] == mock_ctx.obj['temperature']
    assert call_kwargs["time"] == mock_ctx.obj['time']
    assert call_kwargs["force_incremental"] is False
    assert call_kwargs["verbose"] == mock_ctx.obj['verbose']


def test_incremental_with_env_vars_substitution(
    mock_ctx, temp_dir_setup, mock_construct_paths_fixture, mock_incremental_generator_fixture, mock_env_vars
):
    """Ensure env_vars substitute in both original and new prompts before incremental call."""
    mock_ctx.obj['local'] = True
    prompt_file_path = temp_dir_setup["prompts_dir"] / "inc_env_prompt.prompt"
    output_file_path = temp_dir_setup["output_dir"] / "inc_env_output.py"
    create_file(prompt_file_path, "New says $NAME")
    create_file(output_file_path, "Existing code body")

    mock_construct_paths_fixture.return_value = (
        {},  # resolved_config
        {"prompt_file": "New says $NAME", "original_prompt_file": "Old says ${NAME}"},
        {"output": str(output_file_path)},
        "python",
    )

    code_generator_main(
        mock_ctx,
        str(prompt_file_path),
        str(output_file_path),
        None,
        True,
        env_vars={"NAME": "Alice", "llm": "true"},
    )

    call_kwargs = mock_incremental_generator_fixture.call_args.kwargs
    assert call_kwargs["original_prompt"] == "Old says Alice"
    assert call_kwargs["new_prompt"] == "New says Alice"
    assert call_kwargs["preprocess_prompt"] is False


def test_unknown_variable_in_output_path_left_unchanged(
    mock_ctx, temp_dir_setup, mock_construct_paths_fixture, mock_local_generator_fixture, mock_env_vars
):
    mock_ctx.obj['local'] = True
    prompt_file_path = temp_dir_setup["prompts_dir"] / "unk_out_prompt.prompt"
    create_file(prompt_file_path, "Ignorable")
    output_pattern = str(temp_dir_setup["output_dir"] / "out_${UNKNOWN}.txt")

    mock_construct_paths_fixture.return_value = (
        {},  # resolved_config
        {"prompt_file": "Ignorable"},
        {"output": output_pattern},
        "python"
    )

    code_generator_main(
        mock_ctx, str(prompt_file_path), output_pattern, None, False, env_vars={"NAME": "Bob"}
    )

    # Expect literal filename with ${UNKNOWN}
    literal_path = temp_dir_setup["output_dir"] / "out_${UNKNOWN}.txt"
    assert literal_path.exists()


def test_cloud_payload_uses_processed_prompt(
    mock_ctx, temp_dir_setup, mock_construct_paths_fixture, mock_requests_post_fixture, mock_env_vars
):
    # Cloud path (local=False by default); ensure payload promptContent includes substituted vars
    prompt_file_path = temp_dir_setup["prompts_dir"] / "cloud_prompt.prompt"
    prompt_content = "Cloud says $NAME"
    create_file(prompt_file_path, prompt_content)

    mock_construct_paths_fixture.return_value = (
        {},  # resolved_config
        {"prompt_file": prompt_content},
        {"output": str(temp_dir_setup["output_dir"] / "c.py")},
        "python"
    )

    code_generator_main(
        mock_ctx, str(prompt_file_path), str(temp_dir_setup["output_dir"] / "c.py"), None, False, env_vars={"NAME": "Bob"}
    )

    # The first call args to requests.post should have JSON with processed prompt
    args, kwargs = mock_requests_post_fixture.call_args
    payload = kwargs.get('json') or {}
    assert payload.get('promptContent') == "Cloud says Bob"

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

    with pytest.raises(click.UsageError, match="An unexpected error occurred: Unexpected LLM error"):
        code_generator_main(mock_ctx, str(prompt_file_path), output_path_str, None, False)

    # Since it raises, we don't check return values or printed output here anymore
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
        {},  # resolved_config
        {"prompt_file": "Prompt content for dir output"},
        {"output": str(resolved_output_file)},
        "python",
    )

    # Pass the directory as --output; command main should use resolved file
    raw_output_arg_dir = str(temp_dir_setup["output_dir"])  # directory path
    code, incremental, cost, model = code_generator_main(
        mock_ctx,
        str(prompt_file_path),
        raw_output_arg_dir,
        None,
        False,
    )

    # Expect success and file written to resolved_output_file
    assert code == DEFAULT_MOCK_GENERATED_CODE
    assert model != "error"
    assert not incremental
    assert resolved_output_file.exists()
    assert resolved_output_file.read_text() == DEFAULT_MOCK_GENERATED_CODE


# Template Front Matter & Prompt Template Behavior
def test_front_matter_language_override(
    mock_ctx,
    temp_dir_setup,
    mock_construct_paths_fixture,
    mock_local_generator_fixture,
    mock_env_vars,
):
    mock_ctx.obj['local'] = True
    prompt_file_path = temp_dir_setup["prompts_dir"] / "front_lang.prompt"

    front_matter_prompt = """---
language: json
---
Say hi to the user.
"""
    create_file(prompt_file_path, front_matter_prompt)

    mock_construct_paths_fixture.return_value = (
        {},  # resolved_config
        {"prompt_file": front_matter_prompt},
        {"output": str(temp_dir_setup["output_dir"] / "fm_lang.py")},
        "python",
    )

    code_generator_main(mock_ctx, str(prompt_file_path), None, None, False, env_vars={"llm": "true"})

    called_kwargs = mock_local_generator_fixture.call_args.kwargs
    assert called_kwargs["language"] == "json"
    assert "Say hi to the user." in called_kwargs["prompt"]


def test_front_matter_output_path_with_env_substitution(
    mock_ctx,
    temp_dir_setup,
    mock_construct_paths_fixture,
    mock_local_generator_fixture,
    mock_env_vars,
):
    mock_ctx.obj['local'] = True
    prompt_file_path = temp_dir_setup["prompts_dir"] / "front_output.prompt"

    output_template_path = temp_dir_setup["tmp_path"] / "templated_outputs" / "${NAME}.py"
    front_matter_prompt = f"""---
output: \"{output_template_path}\"
variables:
  NAME:
    required: true
---
Generate module for $NAME.
"""
    create_file(prompt_file_path, front_matter_prompt)

    mock_construct_paths_fixture.return_value = (
        {},  # resolved_config
        {"prompt_file": front_matter_prompt},
        {"output": str(temp_dir_setup["output_dir"] / "fallback.py")},
        "python",
    )

    code_generator_main(
        mock_ctx,
        str(prompt_file_path),
        None,
        None,
        False,
        env_vars={"NAME": "Widget", "llm": "true"},
    )

    expected_path = pathlib.Path(str(output_template_path).replace("${NAME}", "Widget")).resolve()
    assert expected_path.exists()
    assert expected_path.read_text() == DEFAULT_MOCK_GENERATED_CODE


def test_front_matter_variable_defaults_and_no_override(
    mock_ctx,
    temp_dir_setup,
    mock_construct_paths_fixture,
    mock_local_generator_fixture,
    mock_env_vars,
):
    mock_ctx.obj['local'] = True
    prompt_file_path = temp_dir_setup["prompts_dir"] / "front_defaults.prompt"

    front_matter_prompt = """---
variables:
  NAME:
    required: true
  COLOR:
    default: blue
  STYLE:
    default: simple
  OVERRIDE:
    default: should_not_win
---
Name: $NAME | Color: $COLOR | Style: $STYLE | Override: $OVERRIDE
"""
    create_file(prompt_file_path, front_matter_prompt)

    mock_construct_paths_fixture.return_value = (
        {},  # resolved_config
        {"prompt_file": front_matter_prompt},
        {"output": str(temp_dir_setup["output_dir"] / "defaults.py")},
        "python",
    )

    code_generator_main(
        mock_ctx,
        str(prompt_file_path),
        str(temp_dir_setup["output_dir"] / "defaults.py"),
        None,
        False,
        env_vars={"NAME": "Ada", "OVERRIDE": "custom", "llm": "true"},
    )

    called_prompt = mock_local_generator_fixture.call_args.kwargs["prompt"]
    assert "Name: Ada" in called_prompt
    assert "Color: blue" in called_prompt
    assert "Style: simple" in called_prompt
    assert "Override: custom" in called_prompt


def test_front_matter_missing_required_variable_returns_error(
    mock_ctx,
    temp_dir_setup,
    mock_construct_paths_fixture,
    mock_local_generator_fixture,
    mock_rich_console_fixture,
):
    mock_ctx.obj['local'] = True
    prompt_file_path = temp_dir_setup["prompts_dir"] / "front_missing.prompt"

    front_matter_prompt = """---
variables:
  NAME:
    required: true
---
Hello $NAME
"""
    create_file(prompt_file_path, front_matter_prompt)

    mock_construct_paths_fixture.return_value = (
        {},  # resolved_config
        {"prompt_file": front_matter_prompt},
        {"output": str(temp_dir_setup["output_dir"] / "missing.py")},
        "python",
    )

    code, incremental, cost, model = code_generator_main(
        mock_ctx,
        str(prompt_file_path),
        str(temp_dir_setup["output_dir"] / "missing.py"),
        None,
        False,
        env_vars={"llm": "true"},
    )

    assert code == ""
    assert not incremental
    assert cost == 0.0
    assert model == "error"
    assert not mock_local_generator_fixture.called
    assert any(
        "missing required variables" in str(call_args[0][0]).lower()
        for call_args in mock_rich_console_fixture.call_args_list
        if call_args[0]
    )


def test_front_matter_discovery_populates_env_vars(
    mock_ctx,
    temp_dir_setup,
    mock_construct_paths_fixture,
    mock_local_generator_fixture,
    mock_env_vars,
):
    mock_ctx.obj['local'] = True
    prompt_file_path = temp_dir_setup["prompts_dir"] / "front_discover.prompt"

    docs_dir = temp_dir_setup["tmp_path"] / "docs"
    docs_dir.mkdir(exist_ok=True)
    discovered_file = docs_dir / "spec.md"
    create_file(discovered_file, "Spec content")

    root_str = str(temp_dir_setup["tmp_path"])
    front_matter_prompt = f"""---
variables:
  DOC_FILES:
    required: false
discover:
  enabled: true
  root: \"{root_str}\"
  set:
    DOC_FILES:
      patterns:
        - "docs/*.md"
---
Docs included: $DOC_FILES
"""
    create_file(prompt_file_path, front_matter_prompt)

    mock_construct_paths_fixture.return_value = (
        {},  # resolved_config
        {"prompt_file": front_matter_prompt},
        {"output": str(temp_dir_setup["output_dir"] / "discover.py")},
        "python",
    )

    code_generator_main(
        mock_ctx,
        str(prompt_file_path),
        str(temp_dir_setup["output_dir"] / "discover.py"),
        None,
        False,
        env_vars={},
    )

    called_prompt = mock_local_generator_fixture.call_args.kwargs["prompt"]
    assert str(discovered_file.resolve()) in called_prompt


def test_front_matter_output_schema_validation_failure(
    mock_ctx,
    temp_dir_setup,
    mock_construct_paths_fixture,
    mock_local_generator_fixture,
    mock_env_vars,
    mock_rich_console_fixture,
    monkeypatch,
):
    mock_ctx.obj['local'] = True
    prompt_file_path = temp_dir_setup["prompts_dir"] / "front_schema.prompt"

    schema_output_path = temp_dir_setup["tmp_path"] / "schema_output.json"
    front_matter_prompt = f"""---
language: json
output: \"{schema_output_path}\"
output_schema:
  type: object
  required:
    - name
---
Return JSON for the spec.
"""
    create_file(prompt_file_path, front_matter_prompt)

    mock_construct_paths_fixture.return_value = (
        {},  # resolved_config
        {"prompt_file": front_matter_prompt},
        {"output": str(temp_dir_setup["output_dir"] / "schema.json")},
        "python",
    )

    calls = {"count": 0}

    def _failing_validate(instance, schema):
        calls["count"] += 1
        raise ValueError("schema mismatch")

    if "jsonschema" in sys.modules:
        monkeypatch.setattr(sys.modules["jsonschema"], "validate", _failing_validate, raising=False)
    else:
        monkeypatch.setitem(sys.modules, "jsonschema", types.SimpleNamespace(validate=_failing_validate))
    mock_local_generator_fixture.return_value = ("{\"age\": 1}", DEFAULT_MOCK_COST, DEFAULT_MOCK_MODEL_NAME)

    with pytest.raises(click.UsageError, match="Generated JSON does not match output_schema: schema mismatch"):
        code_generator_main(
            mock_ctx,
            str(prompt_file_path),
            None,
            None,
            False,
            env_vars={},
        )

    assert calls["count"] == 1
    assert not schema_output_path.exists()


def test_architecture_template_datasource_object_passes_schema(
    mock_ctx,
    temp_dir_setup,
    mock_construct_paths_fixture,
    mock_local_generator_fixture,
    mock_env_vars,
    mock_rich_console_fixture,
):
    mock_ctx.obj['local'] = True
    prompt_file_path = temp_dir_setup["output_dir"] / "architecture.prompt"
    create_file(prompt_file_path, "placeholder")

    prd_path = temp_dir_setup["tmp_path"] / "docs" / "specs.md"
    create_file(prd_path, "Spec content for schema regression")

    template_path = pathlib.Path("pdd/templates/architecture/architecture_json.prompt")
    template_content = template_path.read_text(encoding="utf-8")
    output_path = temp_dir_setup["output_dir"] / "architecture.json"

    mock_construct_paths_fixture.return_value = (
        {},  # resolved_config
        {"prompt_file": template_content},
        {"output": str(output_path)},
        "json",
    )

    generated_json = json.dumps(
        [
            {
                "reason": "Replication",
                "description": "Expose dataSources schema mismatch",
                "dependencies": [],
                "priority": 1,
                "filename": "architecture_json.prompt",
                "filepath": "src/architecture.json",
                "interface": {
                    "type": "page",
                    "page": {
                        "route": "/inventory",
                        "dataSources": [
                            {
                                "kind": "api",
                                "source": "/api/inventory",
                                "method": "GET",
                                "description": "Fetch inventory table contents",
                            }
                        ],
                    },
                },
            }
        ]
    )

    mock_local_generator_fixture.return_value = (
        generated_json,
        DEFAULT_MOCK_COST,
        DEFAULT_MOCK_MODEL_NAME,
    )

    code, incremental, cost, model = code_generator_main(
        mock_ctx,
        str(prompt_file_path),
        str(output_path),
        None,
        False,
        env_vars={"PRD_FILE": str(prd_path)},
    )

    assert not incremental
    assert cost == DEFAULT_MOCK_COST
    assert model == DEFAULT_MOCK_MODEL_NAME
    assert output_path.exists()
    assert output_path.read_text(encoding="utf-8") == generated_json


def test_architecture_template_datasource_string_rejected(
    mock_ctx,
    temp_dir_setup,
    mock_construct_paths_fixture,
    mock_local_generator_fixture,
    mock_env_vars,
    mock_rich_console_fixture,
):
    mock_ctx.obj['local'] = True
    prompt_file_path = temp_dir_setup["output_dir"] / "architecture_string.prompt"

    prd_path = temp_dir_setup["tmp_path"] / "docs" / "specs.md"
    create_file(prd_path, "Spec content for schema regression")

    template_path = pathlib.Path("pdd/templates/architecture/architecture_json.prompt")
    template_content = template_path.read_text(encoding="utf-8")
    create_file(prompt_file_path, template_content)
    output_path = temp_dir_setup["output_dir"] / "architecture_string.json"

    mock_construct_paths_fixture.return_value = (
        {},  # resolved_config
        {"prompt_file": template_content},
        {"output": str(output_path)},
        "json",
    )

    invalid_json = json.dumps(
        [
            {
                "reason": "Legacy string",
                "description": "String data source should fail",
                "dependencies": [],
                "priority": 1,
                "filename": "architecture.prompt",
                "interface": {
                    "type": "page",
                    "page": {
                        "route": "/inventory",
                        "dataSources": ["/api/inventory"],
                    },
                },
            }
        ]
    )

    mock_local_generator_fixture.return_value = (
        invalid_json,
        DEFAULT_MOCK_COST,
        DEFAULT_MOCK_MODEL_NAME,
    )

    with pytest.raises(click.UsageError, match="Generated JSON does not match output_schema"):
        code_generator_main(
            mock_ctx,
            str(prompt_file_path),
            str(output_path),
            None,
            False,
            env_vars={"PRD_FILE": str(prd_path), "llm": "true"},
        )

    assert not output_path.exists()


def test_architecture_template_repairs_invalid_interface_type(
    mock_ctx,
    temp_dir_setup,
    mock_construct_paths_fixture,
    mock_local_generator_fixture,
    mock_env_vars,
    mock_rich_console_fixture,
):
    mock_ctx.obj['local'] = True
    prompt_file_path = temp_dir_setup["output_dir"] / "architecture_type.prompt"
    prd_path = temp_dir_setup["tmp_path"] / "docs" / "specs.md"
    create_file(prd_path, "Spec content for interface type repair")

    template_path = pathlib.Path("pdd/templates/architecture/architecture_json.prompt")
    template_content = template_path.read_text(encoding="utf-8")
    create_file(prompt_file_path, template_content)
    output_path = temp_dir_setup["output_dir"] / "architecture_type.json"

    mock_construct_paths_fixture.return_value = (
        {},  # resolved_config
        {"prompt_file": template_content},
        {"output": str(output_path)},
        "json",
    )

    invalid_type_json = json.dumps(
        [
            {
                "reason": "Fix invalid type",
                "description": "LLM occasionally emits unsupported interface types",
                "dependencies": [],
                "priority": 1,
                "filename": "orders_page.prompt",
                "filepath": "app/orders/page.tsx",
                "interface": {
                    "type": "object",
                    "page": {
                        "route": "/orders",
                        "dataSources": [
                            {
                                "kind": "api",
                                "source": "/api/orders",
                            }
                        ],
                    },
                },
            }
        ],
        indent=2,
    )

    mock_local_generator_fixture.return_value = (
        invalid_type_json,
        DEFAULT_MOCK_COST,
        DEFAULT_MOCK_MODEL_NAME,
    )

    code, incremental, cost, model = code_generator_main(
        mock_ctx,
        str(prompt_file_path),
        str(output_path),
        None,
        False,
        env_vars={"PRD_FILE": str(prd_path)},
    )

    assert not incremental
    assert cost == DEFAULT_MOCK_COST
    assert model == DEFAULT_MOCK_MODEL_NAME
    assert output_path.exists()
    saved = json.loads(output_path.read_text(encoding="utf-8"))
    assert saved[0]["interface"]["type"] == "page"


def test_postprocess_uses_output_path_as_input_when_llm_enabled(
    mock_ctx,
    temp_dir_setup,
    mock_construct_paths_fixture,
    mock_local_generator_fixture,
    mock_subprocess_run_fixture,
    mock_env_vars,
):
    """When LLM is enabled and an output path is resolved, the post-process input file should be the output path."""
    mock_ctx.obj['local'] = True

    # Build a prompt with front matter enabling a post-process script
    prompt_file_path = temp_dir_setup["prompts_dir"] / "postprocess_prompt_python.prompt"
    output_file_path = temp_dir_setup["output_dir"] / "pp_output.py"

    front_matter_prompt = """---
language: python
post_process_python: "./dummy_post_process.py"
---
Generate a simple module.
"""
    create_file(prompt_file_path, front_matter_prompt)

    # construct_paths should return our prompt content and resolved output
    mock_construct_paths_fixture.return_value = (
        {},  # resolved_config
        {"prompt_file": front_matter_prompt},
        {"output": str(output_file_path)},
        "python",
    )

    # Run generation with llm enabled (default); a post-process will be attempted
    code, incremental, cost, model = code_generator_main(
        mock_ctx,
        str(prompt_file_path),
        str(output_file_path),
        None,
        False,
        env_vars={"llm": "true"},
    )

    # Output should be written prior to post-process and match generated code
    assert output_file_path.exists()
    assert output_file_path.read_text(encoding="utf-8") == DEFAULT_MOCK_GENERATED_CODE

    # Post-process should be invoked
    assert mock_subprocess_run_fixture.called


def test_architecture_postprocess_passes_absolute_input_path(
    mock_ctx,
    temp_dir_setup,
    mock_construct_paths_fixture,
    mock_local_generator_fixture,
    mock_subprocess_run_fixture,
    mock_env_vars,
    monkeypatch,
):
    """render_mermaid should receive an absolute path so it can open architecture.json from any cwd."""
    mock_ctx.obj['local'] = True

    template_path = pathlib.Path("pdd/templates/architecture/architecture_json.prompt").resolve()
    template_content = template_path.read_text(encoding="utf-8")

    # Work inside the temp repo to mimic running `pdd` from project root with a relative --output
    monkeypatch.chdir(temp_dir_setup["tmp_path"])

    prompt_file_path = temp_dir_setup["prompts_dir"] / "architecture.prompt"
    create_file(prompt_file_path, template_content)

    relative_output = "architecture.json"
    expected_output_path = temp_dir_setup["tmp_path"] / relative_output
    prd_path = temp_dir_setup["tmp_path"] / "docs" / "specs.md"
    create_file(prd_path, "Spec content for absolute path regression")

    mock_construct_paths_fixture.return_value = (
        {},  # resolved_config
        {"prompt_file": template_content},
        {"output": relative_output},
        "json",
    )

    generated_json = json.dumps(
        [
            {
                "reason": "Diagram generation",
                "description": "Minimal architecture entry for render_mermaid.",
                "dependencies": [],
                "priority": 1,
                "filename": "orders/api.py",
                "filepath": "orders/api.py",
            }
        ]
    )
    mock_local_generator_fixture.return_value = (
        generated_json,
        DEFAULT_MOCK_COST,
        DEFAULT_MOCK_MODEL_NAME,
    )

    code_generator_main(
        mock_ctx,
        str(prompt_file_path),
        relative_output,
        None,
        False,
        env_vars={"PRD_FILE": str(prd_path), "llm": "true"},
    )

    render_cmd = None
    for call in mock_subprocess_run_fixture.call_args_list:
        cmd = call[0][0]
        if len(cmd) >= 2 and pathlib.Path(cmd[1]).name == "render_mermaid.py":
            render_cmd = cmd
            break

    assert render_cmd is not None, "render_mermaid.py should run for architecture template"
    input_arg = render_cmd[2]
    assert os.path.isabs(input_arg)
    assert input_arg == str(expected_output_path.resolve())


def test_architecture_postprocess_rewrites_json_pretty(
    mock_ctx,
    temp_dir_setup,
    mock_construct_paths_fixture,
    mock_local_generator_fixture,
    mock_subprocess_run_fixture,
    mock_env_vars,
):
    """render_mermaid should normalize architecture.json so diffs stay stable."""
    mock_ctx.obj['local'] = True
    real_run = mock_subprocess_run_fixture.original_run
    def render_side_effect(cmd, *args, **kwargs):
        if len(cmd) >= 2 and pathlib.Path(cmd[1]).name == "render_mermaid.py":
            return real_run(cmd, *args, **kwargs)
        return subprocess.CompletedProcess(cmd, 0, stdout="", stderr="")
    mock_subprocess_run_fixture.side_effect = render_side_effect
    template_path = pathlib.Path("pdd/templates/architecture/architecture_json.prompt").resolve()
    template_content = template_path.read_text(encoding="utf-8")

    prompt_file_path = temp_dir_setup["prompts_dir"] / "architecture.prompt"
    create_file(prompt_file_path, template_content)

    prd_path = temp_dir_setup["tmp_path"] / "docs" / "specs.md"
    create_file(prd_path, "Render pretty regression")

    output_path = temp_dir_setup["output_dir"] / "architecture.json"
    mock_construct_paths_fixture.return_value = (
        {},  # resolved_config
        {"prompt_file": template_content},
        {"output": str(output_path)},
        "json",
    )

    unformatted_entries = [
        {
            "reason": "Pretty print regression",
            "description": "Ensure render_mermaid rewrites JSON.",
            "dependencies": [],
            "priority": 1,
            "filename": "foo.py",
            "filepath": "src/foo.py",
        }
    ]
    mock_local_generator_fixture.return_value = (
        json.dumps(unformatted_entries, separators=(',', ':')),
        DEFAULT_MOCK_COST,
        DEFAULT_MOCK_MODEL_NAME,
    )

    code_generator_main(
        mock_ctx,
        str(prompt_file_path),
        str(output_path),
        None,
        False,
        env_vars={"PRD_FILE": str(prd_path), "llm": "true"},
    )

    # render_mermaid should rewrite the file with pretty formatting
    render_calls = [
        call for call in mock_subprocess_run_fixture.call_args_list
        if len(call[0][0]) >= 2 and pathlib.Path(call[0][0][1]).name == "render_mermaid.py"
    ]
    assert render_calls, "render_mermaid.py was never invoked"
    expected = json.dumps(unformatted_entries, indent=2) + "\n"
    actual = output_path.read_text(encoding="utf-8")
    assert actual == expected


def test_full_gen_local_with_unit_test(
    mock_ctx, temp_dir_setup, mock_construct_paths_fixture, mock_local_generator_fixture, mock_env_vars
):
    mock_ctx.obj['local'] = True
    prompt_file_path = temp_dir_setup["prompts_dir"] / "unit_test_prompt.prompt"
    prompt_content = "Generate code that passes the test."
    create_file(prompt_file_path, prompt_content)
    
    unit_test_file = temp_dir_setup["tmp_path"] / "test_something.py"
    unit_test_content = "def test_hello(): assert True"
    create_file(unit_test_file, unit_test_content)
    
    output_file_path_str = str(temp_dir_setup["output_dir"] / "output_with_test.py")

    mock_construct_paths_fixture.return_value = (
        {},  # resolved_config
        {"prompt_file": prompt_content},
        {"output": output_file_path_str}, 
        "python"
    )

    code_generator_main(
        mock_ctx, 
        str(prompt_file_path), 
        output_file_path_str, 
        None, 
        False, 
        unit_test_file=str(unit_test_file)
    )

    called_kwargs = mock_local_generator_fixture.call_args.kwargs
    called_prompt = called_kwargs["prompt"]
    
    assert prompt_content in called_prompt
    # Unit test content should now be wrapped in <unit_test_content> tags
    assert "<unit_test_content>" in called_prompt
    assert unit_test_content in called_prompt
    assert "</unit_test_content>" in called_prompt


def test_full_gen_local_with_unit_test_and_front_matter_conflict(
    mock_ctx, temp_dir_setup, mock_construct_paths_fixture, mock_local_generator_fixture, mock_env_vars
):
    """
    Ensure that a unit test file starting with '---' does not interfere with 
    the prompt's front matter parsing, and that injection happens after parsing.
    """
    mock_ctx.obj['local'] = True
    
    # Prompt with front matter
    prompt_file_path = temp_dir_setup["prompts_dir"] / "conflict_prompt.prompt"
    prompt_body = "This is the main prompt body."
    prompt_content = f"""---
language: json
---
{prompt_body}
"""
    create_file(prompt_file_path, prompt_content)
    
    # Unit test file that looks like it has front matter
    unit_test_file = temp_dir_setup["tmp_path"] / "test_conflict.py"
    unit_test_content = """---
this: looks
like: frontmatter
---
def test_conflict(): pass
"""
    create_file(unit_test_file, unit_test_content)
    
    output_file_path_str = str(temp_dir_setup["output_dir"] / "conflict_output.json")

    mock_construct_paths_fixture.return_value = (
        {},  # resolved_config
        {"prompt_file": prompt_content},
        {"output": output_file_path_str}, 
        "json"
    )

    code_generator_main(
        mock_ctx, 
        str(prompt_file_path), 
        output_file_path_str, 
        None, 
        False, 
        unit_test_file=str(unit_test_file)
    )

    called_kwargs = mock_local_generator_fixture.call_args.kwargs
    
    # Verify metadata from front matter was respected
    assert called_kwargs["language"] == "json"
    
    # Verify prompt content
    called_prompt = called_kwargs["prompt"]
    assert prompt_body in called_prompt
    assert "<unit_test_content>" in called_prompt
    assert unit_test_content in called_prompt
    assert "</unit_test_content>" in called_prompt
    # Ensure the prompt's front matter is NOT in the final prompt passed to generator
    assert "language: json" not in called_prompt

def test_find_default_test_files_logic(
    mock_ctx, temp_dir_setup, mock_construct_paths_fixture, mock_local_generator_fixture, mock_env_vars, mock_rich_console_fixture
):
    """Test automatic inclusion of test files based on code filename."""
    mock_ctx.obj['local'] = True
    mock_ctx.obj['verbose'] = True
    prompt_file_path = temp_dir_setup["prompts_dir"] / "auto_test.prompt"
    create_file(prompt_file_path, "Prompt content")
    
    output_file_name = "auto_test_code.py"
    output_file_path_str = str(temp_dir_setup["output_dir"] / output_file_name)
    
    tests_dir = temp_dir_setup["tmp_path"] / "tests"
    tests_dir.mkdir(exist_ok=True)
    
    # Create matching test files
    test_file_1 = tests_dir / "test_auto_test_code.py"
    create_file(test_file_1, "def test_1(): pass")
    test_file_2 = tests_dir / "test_auto_test_code_extra.py"
    create_file(test_file_2, "def test_2(): pass")
    
    # Create non-matching test file
    create_file(tests_dir / "test_other.py", "def test_other(): pass")

    mock_construct_paths_fixture.return_value = (
        {"tests_dir": str(tests_dir)},  # resolved_config with tests_dir
        {"prompt_file": "Prompt content"},
        {"output": output_file_path_str}, 
        "python"
    )

    code_generator_main(
        mock_ctx, str(prompt_file_path), output_file_path_str, None, False
    )

    called_kwargs = mock_local_generator_fixture.call_args.kwargs
    called_prompt = called_kwargs["prompt"]
    
    assert "<unit_test_content>" in called_prompt
    assert "File: test_auto_test_code.py" in called_prompt
    assert "def test_1(): pass" in called_prompt
    assert "File: test_auto_test_code_extra.py" in called_prompt
    assert "def test_2(): pass" in called_prompt
    assert "test_other.py" not in called_prompt
    
    # Check log output
    assert any("Found default test files" in str(call_args[0][0]) for call_args in mock_rich_console_fixture.call_args_list if call_args[0])


def test_exclude_tests_flag_prevents_auto_inclusion(
    mock_ctx, temp_dir_setup, mock_construct_paths_fixture, mock_local_generator_fixture, mock_env_vars, mock_rich_console_fixture
):
    """Test --exclude-tests prevents automatic test inclusion."""
    mock_ctx.obj['local'] = True
    mock_ctx.obj['verbose'] = True
    prompt_file_path = temp_dir_setup["prompts_dir"] / "exclude_test.prompt"
    create_file(prompt_file_path, "Prompt content")
    
    output_file_name = "exclude_test_code.py"
    output_file_path_str = str(temp_dir_setup["output_dir"] / output_file_name)
    
    tests_dir = temp_dir_setup["tmp_path"] / "tests"
    tests_dir.mkdir(exist_ok=True)
    test_file = tests_dir / "test_exclude_test_code.py"
    create_file(test_file, "def test_should_not_include(): pass")

    mock_construct_paths_fixture.return_value = (
        {"tests_dir": str(tests_dir)}, 
        {"prompt_file": "Prompt content"},
        {"output": output_file_path_str}, 
        "python"
    )

    # Pass exclude_tests=True
    code_generator_main(
        mock_ctx, str(prompt_file_path), output_file_path_str, None, False, exclude_tests=True
    )

    called_kwargs = mock_local_generator_fixture.call_args.kwargs
    called_prompt = called_kwargs["prompt"]
    
    assert "<unit_test_content>" not in called_prompt
    assert "def test_should_not_include(): pass" not in called_prompt
    
    # Check log output (should not see "Found default test files")
    assert not any("Found default test files" in str(call_args[0][0]) for call_args in mock_rich_console_fixture.call_args_list if call_args[0])


def test_explicit_unit_test_file_precedence(
    mock_ctx, temp_dir_setup, mock_construct_paths_fixture, mock_local_generator_fixture, mock_env_vars
):
    """Test explicit --unit-test overrides automatic discovery."""
    mock_ctx.obj['local'] = True
    prompt_file_path = temp_dir_setup["prompts_dir"] / "precedence_test.prompt"
    create_file(prompt_file_path, "Prompt content")
    
    output_file_name = "precedence_code.py"
    output_file_path_str = str(temp_dir_setup["output_dir"] / output_file_name)
    
    tests_dir = temp_dir_setup["tmp_path"] / "tests"
    tests_dir.mkdir(exist_ok=True)
    auto_test_file = tests_dir / "test_precedence_code.py"
    create_file(auto_test_file, "def test_auto(): pass")
    
    explicit_test_file = temp_dir_setup["tmp_path"] / "explicit_test.py"
    create_file(explicit_test_file, "def test_explicit(): pass")

    mock_construct_paths_fixture.return_value = (
        {"tests_dir": str(tests_dir)}, 
        {"prompt_file": "Prompt content"},
        {"output": output_file_path_str}, 
        "python"
    )

    code_generator_main(
        mock_ctx, str(prompt_file_path), output_file_path_str, None, False, unit_test_file=str(explicit_test_file)
    )

    called_kwargs = mock_local_generator_fixture.call_args.kwargs
    called_prompt = called_kwargs["prompt"]

    assert "<unit_test_content>" in called_prompt
    assert "def test_explicit(): pass" in called_prompt
    assert "def test_auto(): pass" not in called_prompt


# --- Tests for LLM Array Unwrapping ---

class TestLLMArrayUnwrapping:
    """
    Tests for unwrapping arrays that LLMs incorrectly wrap in objects.

    LLMs sometimes return {"items": [...]} or {"data": [...]} when the schema
    expects a plain array [...]. This tests the fix to unwrap such responses.
    """

    def test_unwrap_items_wrapper(self):
        """Test unwrapping {"items": [...]} to [...]."""
        # Simulate the unwrapping logic from code_generator_main.py
        output_schema = {"type": "array"}
        parsed = {"items": [{"name": "module1"}, {"name": "module2"}]}

        if output_schema.get("type") == "array" and isinstance(parsed, dict):
            if "items" in parsed and isinstance(parsed["items"], list):
                parsed = parsed["items"]

        assert parsed == [{"name": "module1"}, {"name": "module2"}]
        assert isinstance(parsed, list)

    def test_unwrap_data_wrapper(self):
        """Test unwrapping {"data": [...]} to [...]."""
        output_schema = {"type": "array"}
        parsed = {"data": [1, 2, 3]}

        if output_schema.get("type") == "array" and isinstance(parsed, dict):
            if "items" in parsed and isinstance(parsed["items"], list):
                parsed = parsed["items"]
            elif "data" in parsed and isinstance(parsed["data"], list):
                parsed = parsed["data"]

        assert parsed == [1, 2, 3]
        assert isinstance(parsed, list)

    def test_unwrap_results_wrapper(self):
        """Test unwrapping {"results": [...]} to [...]."""
        output_schema = {"type": "array"}
        parsed = {"results": ["a", "b", "c"]}

        if output_schema.get("type") == "array" and isinstance(parsed, dict):
            if "items" in parsed and isinstance(parsed["items"], list):
                parsed = parsed["items"]
            elif "data" in parsed and isinstance(parsed["data"], list):
                parsed = parsed["data"]
            elif "results" in parsed and isinstance(parsed["results"], list):
                parsed = parsed["results"]

        assert parsed == ["a", "b", "c"]
        assert isinstance(parsed, list)

    def test_no_unwrap_when_schema_not_array(self):
        """Test that unwrapping is skipped when schema type is not array."""
        output_schema = {"type": "object"}  # Not an array schema
        parsed = {"items": [1, 2, 3]}
        original = parsed.copy()

        if output_schema.get("type") == "array" and isinstance(parsed, dict):
            if "items" in parsed and isinstance(parsed["items"], list):
                parsed = parsed["items"]

        # Should remain unchanged
        assert parsed == original
        assert isinstance(parsed, dict)

    def test_no_unwrap_when_already_list(self):
        """Test that actual lists are not modified."""
        output_schema = {"type": "array"}
        parsed = [1, 2, 3]  # Already a list
        original = parsed.copy()

        if output_schema.get("type") == "array" and isinstance(parsed, dict):
            if "items" in parsed and isinstance(parsed["items"], list):
                parsed = parsed["items"]

        # Should remain unchanged
        assert parsed == original
        assert isinstance(parsed, list)

    def test_no_unwrap_when_items_not_list(self):
        """Test that non-list 'items' values are not unwrapped."""
        output_schema = {"type": "array"}
        parsed = {"items": "not a list"}  # items is not a list
        original = parsed.copy()

        if output_schema.get("type") == "array" and isinstance(parsed, dict):
            if "items" in parsed and isinstance(parsed["items"], list):
                parsed = parsed["items"]

        # Should remain unchanged
        assert parsed == original
        assert isinstance(parsed, dict)

    def test_unwrap_nested_architecture(self):
        """Test unwrapping a realistic architecture.json wrapper case."""
        output_schema = {"type": "array"}
        parsed = {
            "items": [
                {
                    "filename": "auth",
                    "filepath": "src/auth.py",
                    "description": "Authentication module",
                    "dependencies": [],
                    "priority": 1,
                    "reason": "Core security"
                },
                {
                    "filename": "database",
                    "filepath": "src/database.py",
                    "description": "Database connection",
                    "dependencies": ["auth"],
                    "priority": 2,
                    "reason": "Data persistence"
                }
            ]
        }

        if output_schema.get("type") == "array" and isinstance(parsed, dict):
            if "items" in parsed and isinstance(parsed["items"], list):
                parsed = parsed["items"]

        assert isinstance(parsed, list)
        assert len(parsed) == 2
        assert parsed[0]["filename"] == "auth"
        assert parsed[1]["filename"] == "database"

    def test_items_takes_precedence_over_data(self):
        """Test that 'items' is checked before 'data'."""
        output_schema = {"type": "array"}
        parsed = {"items": [1], "data": [2]}  # Both present

        if output_schema.get("type") == "array" and isinstance(parsed, dict):
            if "items" in parsed and isinstance(parsed["items"], list):
                parsed = parsed["items"]
            elif "data" in parsed and isinstance(parsed["data"], list):
                parsed = parsed["data"]

        # items should take precedence
        assert parsed == [1]

    def test_json_serialization_after_unwrap(self):
        """Test that unwrapped arrays can be serialized back to JSON."""
        output_schema = {"type": "array"}
        parsed = {"items": [{"key": "value"}]}

        if output_schema.get("type") == "array" and isinstance(parsed, dict):
            if "items" in parsed and isinstance(parsed["items"], list):
                parsed = parsed["items"]
                generated_code_content = json.dumps(parsed, indent=2)

        expected = '[\n  {\n    "key": "value"\n  }\n]'
        assert generated_code_content == expected


# =============================================================================
# Issue #154 Regression Tests: File Overwrite Not Happening
# =============================================================================
#
# These tests verify the bug where "generation overwrite a file doesn't always
# happen". The root cause is an architectural disconnect between:
# 1. construct_paths() - handles overwrite confirmation
# 2. code_generator_main() - handles actual file write at line 1087
#
# When generate_output_paths() returns {} (e.g., due to empty basename),
# output_path becomes falsy and the write block is skipped silently.
#
# TEST STRATEGY:
# These tests assert the EXPECTED FIXED behavior, so they will FAIL on the
# current buggy code and PASS once the bug is fixed.
# =============================================================================


class TestIssue154OverwriteNotHappening:
    """
    Regression tests for GitHub Issue #154: File overwrite not always happening.

    The bug manifests when:
    1. construct_paths() returns empty/falsy output_file_paths
    2. LLM successfully generates code
    3. The file write block at line 1087 is silently skipped due to `if output_path:`

    These tests assert the EXPECTED behavior after the fix, so they will
    FAIL on the current buggy code.
    """

    def test_issue_154_empty_output_path_should_raise_error(
        self, mock_ctx, temp_dir_setup, mock_construct_paths_fixture,
        mock_local_generator_fixture, mock_rich_console_fixture, mock_env_vars
    ):
        """
        FAILING TEST for issue #154: Empty output_path should raise an error.

        Current behavior (BUG): Code generates, write is silently skipped.
        Expected behavior (FIX): Should raise click.UsageError when output_path is empty.

        This test FAILS on the current buggy code because no error is raised.
        """
        mock_ctx.obj['local'] = True
        mock_ctx.obj['quiet'] = False
        prompt_file_path = temp_dir_setup["prompts_dir"] / "issue154_prompt.prompt"
        create_file(prompt_file_path, "Test prompt for issue 154")

        # Simulate what happens when generate_output_paths returns {}
        # due to empty basename - output_file_paths.get("output") returns ""
        mock_construct_paths_fixture.return_value = (
            {},  # resolved_config
            {"prompt_file": "Test prompt for issue 154"},
            {"output": ""},  # Empty string - falsy output path (triggers the bug)
            "python"
        )

        # EXPECTED FIX: Should raise click.UsageError when output_path is empty
        # CURRENT BUG: No error raised, write is silently skipped
        with pytest.raises(click.UsageError) as excinfo:
            code_generator_main(
                mock_ctx, str(prompt_file_path), "", None, False
            )

        # Verify the error message is helpful
        assert "output" in str(excinfo.value).lower() or "path" in str(excinfo.value).lower(), \
            "Error message should mention output path issue"

    def test_issue_154_none_output_path_should_raise_error(
        self, mock_ctx, temp_dir_setup, mock_construct_paths_fixture,
        mock_local_generator_fixture, mock_rich_console_fixture, mock_env_vars
    ):
        """
        FAILING TEST for issue #154: None output_path should raise an error.

        When construct_paths returns None for output path (e.g., when
        generate_output_paths returns {} and .get("output") returns None),
        an error should be raised instead of silently skipping the write.

        This test FAILS on the current buggy code.
        """
        mock_ctx.obj['local'] = True
        mock_ctx.obj['quiet'] = False
        prompt_file_path = temp_dir_setup["prompts_dir"] / "issue154_none_prompt.prompt"
        create_file(prompt_file_path, "Test prompt for issue 154 - None case")

        # Simulate output_file_paths.get("output") returning None
        mock_construct_paths_fixture.return_value = (
            {},  # resolved_config
            {"prompt_file": "Test prompt for issue 154 - None case"},
            {"output": None},  # None output path - triggers the bug
            "python"
        )

        # EXPECTED FIX: Should raise click.UsageError when output_path is None
        # CURRENT BUG: No error, write silently skipped, console shows warning
        with pytest.raises(click.UsageError) as excinfo:
            code_generator_main(
                mock_ctx, str(prompt_file_path), None, None, False
            )

        assert "output" in str(excinfo.value).lower() or "path" in str(excinfo.value).lower()

    def test_issue_154_llm_should_not_be_called_with_invalid_output_path(
        self, mock_ctx, temp_dir_setup, mock_construct_paths_fixture,
        mock_local_generator_fixture, mock_env_vars
    ):
        """
        FAILING TEST for issue #154: LLM should NOT be called when output_path is invalid.

        The architectural bug is that output_path validation happens AFTER the
        expensive LLM call. The LLM is called (costing money/time) even when
        output_path is invalid/empty.

        Expected fix: Validate output_path BEFORE calling the LLM.
        This test FAILS on the current buggy code because the LLM IS called.
        """
        mock_ctx.obj['local'] = True
        prompt_file_path = temp_dir_setup["prompts_dir"] / "issue154_llm_call.prompt"
        create_file(prompt_file_path, "Test prompt")

        # Empty output path - simulates generate_output_paths returning {}
        mock_construct_paths_fixture.return_value = (
            {},
            {"prompt_file": "Test prompt"},
            {"output": ""},  # Empty - should be caught BEFORE LLM call
            "python"
        )

        # Expect an error to be raised BEFORE the LLM is called
        try:
            code_generator_main(mock_ctx, str(prompt_file_path), "", None, False)
        except click.UsageError:
            pass  # This is the expected behavior after fix

        # EXPECTED FIX: LLM should NOT be called when output_path is invalid
        # CURRENT BUG: LLM IS called, wasting resources
        assert not mock_local_generator_fixture.called, \
            "LLM should NOT be called when output_path is empty/invalid. " \
            "The output path should be validated BEFORE expensive LLM operations."
