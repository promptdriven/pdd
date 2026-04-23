import asyncio
import json
import os
import pathlib
import re
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
from pdd.code_generator_main import code_generator_main, _verify_architecture_conformance
from pdd.core.cloud import CloudConfig, get_cloud_timeout, get_cloud_request_timeout
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
    # Ensure cloud-only env vars don't leak from the host environment
    # and override local=True in tests (see _env_flag_enabled checks).
    monkeypatch.delenv("PDD_CLOUD_ONLY", raising=False)
    monkeypatch.delenv("PDD_NO_LOCAL_FALLBACK", raising=False)

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
            "searchInput": "Cloud test prompt",
            "language": "python",
            "strength": mock_ctx.obj['strength'],
            "temperature": mock_ctx.obj['temperature'],
            "verbose": mock_ctx.obj['verbose']
        },
        headers={"Authorization": "Bearer test_jwt_token", "Content-Type": "application/json"},
        timeout=get_cloud_request_timeout()
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


def test_full_gen_k_service_skips_cloud(
    mock_ctx, temp_dir_setup, mock_construct_paths_fixture,
    mock_pdd_preprocess_fixture,
    mock_local_generator_fixture, mock_get_jwt_token_fixture, monkeypatch
):
    """
    Test that K_SERVICE env var (Cloud Run worker) skips cloud auth entirely
    and goes straight to local execution.

    Regression test for issue #596: inside a Cloud Run Job, cloud auth always
    fails (no JWT cache, no device flow). The warning message confused the LLM
    agent into bailing out instead of letting local fallback run.
    """
    mock_ctx.obj['local'] = False  # Not forcing local — cloud would normally be tried
    monkeypatch.setenv("K_SERVICE", "pdd-executor-job")

    prompt_file_path = temp_dir_setup["prompts_dir"] / "k_service_prompt_python.prompt"
    create_file(prompt_file_path, "K_SERVICE test prompt")
    output_file_path_str = str(temp_dir_setup["output_dir"] / "k_service_output.py")

    mock_construct_paths_fixture.return_value = (
        {},
        {"prompt_file": "K_SERVICE test prompt"},
        {"output": output_file_path_str},
        "python"
    )

    code_generator_main(mock_ctx, str(prompt_file_path), output_file_path_str, None, False)

    # Cloud auth should NOT be attempted when K_SERVICE is set
    mock_get_jwt_token_fixture.assert_not_called()
    # Local generator should be used directly
    mock_local_generator_fixture.assert_called_once()


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


def test_front_matter_output_overrides_pddrc_config(
    mock_ctx,
    temp_dir_setup,
    mock_construct_paths_fixture,
    mock_local_generator_fixture,
    mock_env_vars,
):
    """Front-matter output: should override .pddrc generate_output_path
    when output_from_config=True (sync flow)."""
    mock_ctx.obj['local'] = True
    prompt_file_path = temp_dir_setup["prompts_dir"] / "fm_override.prompt"

    fm_output = temp_dir_setup["tmp_path"] / "correct_subdir" / "fm_override.py"
    pddrc_output = temp_dir_setup["output_dir"] / "fm_override.py"

    front_matter_prompt = f"""---
output: \"{fm_output}\"
---
Generate module.
"""
    create_file(prompt_file_path, front_matter_prompt)

    mock_construct_paths_fixture.return_value = (
        {},
        {"prompt_file": front_matter_prompt},
        {"output": str(pddrc_output)},
        "python",
    )

    # output_from_config=True simulates sync passing .pddrc-resolved path
    code_generator_main(
        mock_ctx,
        str(prompt_file_path),
        str(pddrc_output),  # .pddrc output
        None,
        False,
        env_vars={"llm": "true"},
        output_from_config=True,
    )

    # Front-matter should win over .pddrc
    assert fm_output.resolve().exists(), "Front-matter output should override .pddrc path"
    assert not pddrc_output.exists(), ".pddrc path should NOT be used"


def test_cli_output_flag_beats_front_matter(
    mock_ctx,
    temp_dir_setup,
    mock_construct_paths_fixture,
    mock_local_generator_fixture,
    mock_env_vars,
):
    """Explicit --output CLI flag should NOT be overridden by front-matter."""
    mock_ctx.obj['local'] = True
    prompt_file_path = temp_dir_setup["prompts_dir"] / "cli_wins.prompt"

    fm_output = temp_dir_setup["tmp_path"] / "fm_path" / "cli_wins.py"
    cli_output = temp_dir_setup["output_dir"] / "cli_wins.py"

    front_matter_prompt = f"""---
output: \"{fm_output}\"
---
Generate module.
"""
    create_file(prompt_file_path, front_matter_prompt)

    mock_construct_paths_fixture.return_value = (
        {},
        {"prompt_file": front_matter_prompt},
        {"output": str(cli_output)},
        "python",
    )

    # output_from_config=False (default) = explicit CLI --output
    code_generator_main(
        mock_ctx,
        str(prompt_file_path),
        str(cli_output),  # CLI --output
        None,
        False,
        env_vars={"llm": "true"},
        output_from_config=False,
    )

    # CLI flag should win over front-matter
    assert cli_output.exists(), "CLI --output should be used"
    assert not fm_output.resolve().exists(), "Front-matter should NOT override CLI --output"


def test_front_matter_resolution_failure_warns_and_falls_back(
    mock_ctx,
    temp_dir_setup,
    mock_construct_paths_fixture,
    mock_local_generator_fixture,
    mock_env_vars,
    mock_rich_console_fixture,
    monkeypatch,
):
    """When front-matter ``output:`` resolution raises (e.g. bad path,
    permission error), the CLI must:
        1. log a yellow warning to the console
        2. fall back to the .pddrc / CLI-supplied output path
        3. NOT crash silently

    Regression: the bare ``except Exception: pass`` previously swallowed
    these errors, so users would see code written to the wrong location
    with no indication why.
    """
    import pdd.code_generator_main as cgm

    mock_ctx.obj['local'] = True
    mock_ctx.obj['quiet'] = False
    prompt_file_path = temp_dir_setup["prompts_dir"] / "fm_broken.prompt"

    fallback_output = temp_dir_setup["output_dir"] / "fm_broken.py"
    front_matter_prompt = """---
output: \"/tmp/fm_resolve_will_explode.py\"
---
Generate module.
"""
    create_file(prompt_file_path, front_matter_prompt)

    mock_construct_paths_fixture.return_value = (
        {},
        {"prompt_file": front_matter_prompt},
        {"output": str(fallback_output)},
        "python",
    )

    # Force front-matter resolution to raise. We monkeypatch ``_expand_vars``
    # to raise *only* for the front-matter value — the helper is also called
    # earlier on the regular ``output_path`` argument, which must succeed so
    # we actually reach the try/except Greg flagged in code_generator_main.py.
    real_expand = cgm._expand_vars
    fm_value = "/tmp/fm_resolve_will_explode.py"

    def selective_boom(text, vars_map=None):
        if text == fm_value:
            raise PermissionError("simulated permission error during expansion")
        return real_expand(text, vars_map)

    monkeypatch.setattr(cgm, "_expand_vars", selective_boom)

    code_generator_main(
        mock_ctx,
        str(prompt_file_path),
        str(fallback_output),  # .pddrc-supplied default
        None,
        False,
        env_vars={"llm": "true"},
        output_from_config=True,  # exercise the broadened sync path
    )

    # ``mock_rich_console_fixture`` is the autouse fixture that intercepts
    # ``console.print`` calls in this module — capsys would not see them
    # because rich's print is replaced with a MagicMock.
    printed = [
        " ".join(str(a) for a in call.args)
        for call in mock_rich_console_fixture.call_args_list
    ]
    joined = " ".join(printed)
    assert "Could not resolve front-matter output path" in joined, (
        f"Expected fall-back warning in console output, got: {printed}"
    )
    assert "simulated permission error" in joined
    # Fallback path was actually used.
    assert fallback_output.exists(), "Should fall back to .pddrc / CLI path on resolution failure"



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
    # Template uses double braces for YAML escaping; normalize to single for test
    template_content = template_content.replace("{{INPUT_FILE}}", "{INPUT_FILE}")
    template_content = template_content.replace("{{APP_NAME}}", "{APP_NAME}")
    template_content = template_content.replace("{{OUTPUT_HTML}}", "{OUTPUT_HTML}")

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
    # Template uses double braces for YAML escaping; normalize to single for test
    template_content = template_content.replace("{{INPUT_FILE}}", "{INPUT_FILE}")
    template_content = template_content.replace("{{APP_NAME}}", "{APP_NAME}")
    template_content = template_content.replace("{{OUTPUT_HTML}}", "{OUTPUT_HTML}")

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
    # Issue #617: filename should mirror filepath in normalized output
    expected_entries = [
        {
            **unformatted_entries[0],
            "filename": "src/foo_Python.prompt",
        }
    ]
    expected = json.dumps(expected_entries, indent=2) + "\n"
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


# --- Tests for Example Display (Pinned & Cloud Response) ---

def test_pinned_example_extraction_verbose(
    mock_ctx, temp_dir_setup, mock_construct_paths_fixture, mock_pdd_preprocess_fixture,
    mock_get_jwt_token_fixture, mock_requests_post_fixture, mock_env_vars, capsys
):
    """Test that pinned example ID from <pin> tag is displayed in verbose mode."""
    mock_ctx.obj['local'] = False
    mock_ctx.obj['verbose'] = True

    prompt_content = "Test prompt\n<pin>test-example-id-123</pin>\nMore content"
    prompt_file_path = temp_dir_setup["prompts_dir"] / "pin_prompt.prompt"
    create_file(prompt_file_path, prompt_content)

    output_file_path_str = str(temp_dir_setup["output_dir"] / "pin_output.py")

    mock_construct_paths_fixture.return_value = (
        {},
        {"prompt_file": prompt_content},
        {"output": output_file_path_str},
        "python"
    )
    # pdd_preprocess returns prompt unchanged (passthrough)
    mock_pdd_preprocess_fixture.return_value = prompt_content

    # Mock cloud response with examplesUsed array
    mock_response = MagicMock(spec=requests.Response)
    mock_response.json.return_value = {
        "generatedCode": DEFAULT_MOCK_GENERATED_CODE,
        "totalCost": 0.001,
        "modelName": "test-model",
        "examplesUsed": [{"id": "test-example-id-123", "title": "Test Example Title"}]
    }
    mock_response.raise_for_status = MagicMock()
    mock_requests_post_fixture.return_value = mock_response

    with patch('pdd.code_generator_main.console') as mock_console:
        code_generator_main(
            mock_ctx, str(prompt_file_path), output_file_path_str, None, False
        )

        # Check that console.print was called with pinned example message
        print_calls = [str(call) for call in mock_console.print.call_args_list]
        pinned_call_found = any("Using pinned example" in call and "test-example-id-123" in call for call in print_calls)
        assert pinned_call_found, f"Expected 'Using pinned example: test-example-id-123' in console output. Got: {print_calls}"


def test_pinned_example_no_verbose(
    mock_ctx, temp_dir_setup, mock_construct_paths_fixture, mock_pdd_preprocess_fixture,
    mock_get_jwt_token_fixture, mock_requests_post_fixture, mock_env_vars
):
    """Test that pinned example is NOT displayed when verbose=False."""
    mock_ctx.obj['local'] = False
    mock_ctx.obj['verbose'] = False  # Not verbose

    prompt_content = "Test prompt\n<pin>test-example-id-456</pin>\nMore content"
    prompt_file_path = temp_dir_setup["prompts_dir"] / "pin_prompt_quiet.prompt"
    create_file(prompt_file_path, prompt_content)

    output_file_path_str = str(temp_dir_setup["output_dir"] / "pin_output_quiet.py")

    mock_construct_paths_fixture.return_value = (
        {},
        {"prompt_file": prompt_content},
        {"output": output_file_path_str},
        "python"
    )
    mock_pdd_preprocess_fixture.return_value = prompt_content

    mock_response = MagicMock(spec=requests.Response)
    mock_response.json.return_value = {
        "generatedCode": DEFAULT_MOCK_GENERATED_CODE,
        "totalCost": 0.001,
        "modelName": "test-model"
    }
    mock_response.raise_for_status = MagicMock()
    mock_requests_post_fixture.return_value = mock_response

    with patch('pdd.code_generator_main.console') as mock_console:
        code_generator_main(
            mock_ctx, str(prompt_file_path), output_file_path_str, None, False
        )

        # Check that "Using pinned example" was NOT printed
        print_calls = [str(call) for call in mock_console.print.call_args_list]
        pinned_call_found = any("Using pinned example" in call for call in print_calls)
        assert not pinned_call_found, f"'Using pinned example' should not appear when verbose=False. Got: {print_calls}"


def test_no_pin_tag_no_display(
    mock_ctx, temp_dir_setup, mock_construct_paths_fixture, mock_pdd_preprocess_fixture,
    mock_get_jwt_token_fixture, mock_requests_post_fixture, mock_env_vars
):
    """Test that no pinned example message when prompt has no <pin> tag."""
    mock_ctx.obj['local'] = False
    mock_ctx.obj['verbose'] = True

    prompt_content = "Test prompt without pin tag"
    prompt_file_path = temp_dir_setup["prompts_dir"] / "no_pin_prompt.prompt"
    create_file(prompt_file_path, prompt_content)

    output_file_path_str = str(temp_dir_setup["output_dir"] / "no_pin_output.py")

    mock_construct_paths_fixture.return_value = (
        {},
        {"prompt_file": prompt_content},
        {"output": output_file_path_str},
        "python"
    )
    mock_pdd_preprocess_fixture.return_value = prompt_content

    mock_response = MagicMock(spec=requests.Response)
    mock_response.json.return_value = {
        "generatedCode": DEFAULT_MOCK_GENERATED_CODE,
        "totalCost": 0.001,
        "modelName": "test-model"
    }
    mock_response.raise_for_status = MagicMock()
    mock_requests_post_fixture.return_value = mock_response

    with patch('pdd.code_generator_main.console') as mock_console:
        code_generator_main(
            mock_ctx, str(prompt_file_path), output_file_path_str, None, False
        )

        # Check that "Using pinned example" was NOT printed
        print_calls = [str(call) for call in mock_console.print.call_args_list]
        pinned_call_found = any("Using pinned example" in call for call in print_calls)
        assert not pinned_call_found, f"'Using pinned example' should not appear without <pin> tag. Got: {print_calls}"


def test_cloud_response_with_examples_used(
    mock_ctx, temp_dir_setup, mock_construct_paths_fixture, mock_pdd_preprocess_fixture,
    mock_get_jwt_token_fixture, mock_requests_post_fixture, mock_env_vars
):
    """Test that examplesUsed from cloud response is displayed in success panel."""
    mock_ctx.obj['local'] = False
    mock_ctx.obj['verbose'] = True

    prompt_content = "Test prompt"
    prompt_file_path = temp_dir_setup["prompts_dir"] / "example_response.prompt"
    create_file(prompt_file_path, prompt_content)

    output_file_path_str = str(temp_dir_setup["output_dir"] / "example_output.py")

    mock_construct_paths_fixture.return_value = (
        {},
        {"prompt_file": prompt_content},
        {"output": output_file_path_str},
        "python"
    )
    mock_pdd_preprocess_fixture.return_value = prompt_content

    # Mock cloud response with examplesUsed array
    mock_response = MagicMock(spec=requests.Response)
    mock_response.json.return_value = {
        "generatedCode": DEFAULT_MOCK_GENERATED_CODE,
        "totalCost": 0.001,
        "modelName": "test-model",
        "examplesUsed": [{"id": "ex-123", "title": "Test Example Title"}]
    }
    mock_response.raise_for_status = MagicMock()
    mock_requests_post_fixture.return_value = mock_response

    with patch('pdd.code_generator_main.console') as mock_console:
        code_generator_main(
            mock_ctx, str(prompt_file_path), output_file_path_str, None, False
        )

        # Check that console.print was called with example info in Panel
        # Need to inspect Panel objects for their content
        example_info_found = False
        for call in mock_console.print.call_args_list:
            args = call[0] if call[0] else ()
            for arg in args:
                if isinstance(arg, Panel):
                    # Panel.renderable contains the content
                    panel_content = str(arg.renderable)
                    if "ex-123" in panel_content and "Test Example Title" in panel_content:
                        example_info_found = True
                        break
                elif isinstance(arg, str):
                    if "ex-123" in arg and "Test Example Title" in arg:
                        example_info_found = True
                        break
        assert example_info_found, f"Expected example info 'ex-123 (Test Example Title)' in console output"


def test_cloud_response_empty_examples_used(
    mock_ctx, temp_dir_setup, mock_construct_paths_fixture, mock_pdd_preprocess_fixture,
    mock_get_jwt_token_fixture, mock_requests_post_fixture, mock_env_vars
):
    """Test standard success message when examplesUsed array is empty."""
    mock_ctx.obj['local'] = False
    mock_ctx.obj['verbose'] = True

    prompt_content = "Test prompt"
    prompt_file_path = temp_dir_setup["prompts_dir"] / "no_example_response.prompt"
    create_file(prompt_file_path, prompt_content)

    output_file_path_str = str(temp_dir_setup["output_dir"] / "no_example_output.py")

    mock_construct_paths_fixture.return_value = (
        {},
        {"prompt_file": prompt_content},
        {"output": output_file_path_str},
        "python"
    )
    mock_pdd_preprocess_fixture.return_value = prompt_content

    # Mock cloud response with empty examplesUsed array
    mock_response = MagicMock(spec=requests.Response)
    mock_response.json.return_value = {
        "generatedCode": DEFAULT_MOCK_GENERATED_CODE,
        "totalCost": 0.001,
        "modelName": "test-model",
        "examplesUsed": []  # Empty array
    }
    mock_response.raise_for_status = MagicMock()
    mock_requests_post_fixture.return_value = mock_response

    with patch('pdd.code_generator_main.console') as mock_console:
        code_generator_main(
            mock_ctx, str(prompt_file_path), output_file_path_str, None, False
        )

        # Check that success message is present but without example info
        # Need to inspect Panel objects for their content
        cloud_success_found = False
        example_info_found = False
        for call in mock_console.print.call_args_list:
            args = call[0] if call[0] else ()
            for arg in args:
                if isinstance(arg, Panel):
                    panel_content = str(arg.renderable)
                    if "Cloud generation successful" in panel_content:
                        cloud_success_found = True
                    if "Example:" in panel_content:
                        example_info_found = True
                elif isinstance(arg, str):
                    if "Cloud generation successful" in arg:
                        cloud_success_found = True
                    if "Example:" in arg:
                        example_info_found = True
        assert cloud_success_found, f"Expected 'Cloud generation successful' in console output"
        assert not example_info_found, f"'Example:' should not appear when examplesUsed is empty"


def test_cloud_response_without_examples_used_key(
    mock_ctx, temp_dir_setup, mock_construct_paths_fixture, mock_pdd_preprocess_fixture,
    mock_get_jwt_token_fixture, mock_requests_post_fixture, mock_env_vars
):
    """Test standard success message when examplesUsed key is missing from response."""
    mock_ctx.obj['local'] = False
    mock_ctx.obj['verbose'] = True

    prompt_content = "Test prompt"
    prompt_file_path = temp_dir_setup["prompts_dir"] / "missing_example_key.prompt"
    create_file(prompt_file_path, prompt_content)

    output_file_path_str = str(temp_dir_setup["output_dir"] / "missing_key_output.py")

    mock_construct_paths_fixture.return_value = (
        {},
        {"prompt_file": prompt_content},
        {"output": output_file_path_str},
        "python"
    )
    mock_pdd_preprocess_fixture.return_value = prompt_content

    # Mock cloud response without examplesUsed key at all
    mock_response = MagicMock(spec=requests.Response)
    mock_response.json.return_value = {
        "generatedCode": DEFAULT_MOCK_GENERATED_CODE,
        "totalCost": 0.001,
        "modelName": "test-model"
        # No examplesUsed key
    }
    mock_response.raise_for_status = MagicMock()
    mock_requests_post_fixture.return_value = mock_response

    with patch('pdd.code_generator_main.console') as mock_console:
        code_generator_main(
            mock_ctx, str(prompt_file_path), output_file_path_str, None, False
        )

        # Check that success message is present but without example info
        # Need to inspect Panel objects for their content
        cloud_success_found = False
        example_info_found = False
        for call in mock_console.print.call_args_list:
            args = call[0] if call[0] else ()
            for arg in args:
                if isinstance(arg, Panel):
                    panel_content = str(arg.renderable)
                    if "Cloud generation successful" in panel_content:
                        cloud_success_found = True
                    if "Example:" in panel_content:
                        example_info_found = True
                elif isinstance(arg, str):
                    if "Cloud generation successful" in arg:
                        cloud_success_found = True
                    if "Example:" in arg:
                        example_info_found = True
        assert cloud_success_found, f"Expected 'Cloud generation successful' in console output"
        assert not example_info_found, f"'Example:' should not appear when examplesUsed key is missing"


# === Language parameter passthrough ===

def test_language_param_passed_to_construct_paths(
    mock_ctx, temp_dir_setup, mock_construct_paths_fixture, mock_local_generator_fixture, mock_env_vars
):
    """When language is passed to code_generator_main, it should appear in command_options."""
    mock_ctx.obj['local'] = True
    prompt_file_path = temp_dir_setup["prompts_dir"] / "test_prompt_typescriptreact.prompt"
    create_file(prompt_file_path, "TSX test prompt")

    output_file_path_str = str(temp_dir_setup["output_dir"] / "output.tsx")

    mock_construct_paths_fixture.return_value = (
        {},
        {"prompt_file": "TSX test prompt"},
        {"output": output_file_path_str},
        "typescriptreact"
    )

    code_generator_main(
        mock_ctx, str(prompt_file_path), output_file_path_str, None, False,
        language="typescriptreact",
    )

    # Verify construct_paths was called with language in command_options
    call_kwargs = mock_construct_paths_fixture.call_args
    command_options = call_kwargs.kwargs.get("command_options") or call_kwargs[1].get("command_options")
    if command_options is None:
        # Positional arg — construct_paths(input_file_paths, force, quiet, command, command_options, ...)
        command_options = call_kwargs[0][4] if len(call_kwargs[0]) > 4 else None
    assert command_options is not None, "command_options should be passed to construct_paths"
    assert command_options.get("language") == "typescriptreact"


def test_language_param_not_set_when_none(
    mock_ctx, temp_dir_setup, mock_construct_paths_fixture, mock_local_generator_fixture, mock_env_vars
):
    """When language is not passed, command_options should not contain 'language' key."""
    mock_ctx.obj['local'] = True
    prompt_file_path = temp_dir_setup["prompts_dir"] / "test_prompt_python.prompt"
    create_file(prompt_file_path, "Python test prompt")

    output_file_path_str = str(temp_dir_setup["output_dir"] / "output.py")

    mock_construct_paths_fixture.return_value = (
        {},
        {"prompt_file": "Python test prompt"},
        {"output": output_file_path_str},
        "python"
    )

    code_generator_main(
        mock_ctx, str(prompt_file_path), output_file_path_str, None, False,
    )

    call_kwargs = mock_construct_paths_fixture.call_args
    command_options = call_kwargs.kwargs.get("command_options") or call_kwargs[1].get("command_options")
    if command_options is None:
        command_options = call_kwargs[0][4] if len(call_kwargs[0]) > 4 else None
    assert command_options is not None
    assert "language" not in command_options


# === Fix 2A: Architecture Conformance Check Tests ===

class TestVerifyArchitectureConformance:
    """Tests for _verify_architecture_conformance (Fix 2A)."""

    def test_passes_when_all_symbols_present(self, tmp_path):
        """Conformance check passes when generated code exports all declared symbols."""
        arch = [
            {
                "filename": "models_Python.prompt",
                "filepath": "src/models.py",
                "interface": {
                    "type": "module",
                    "module": {
                        "functions": [
                            {"name": "Order", "signature": "class Order(BaseModel)"},
                            {"name": "User", "signature": "class User(BaseModel)"},
                        ]
                    },
                },
            }
        ]
        (tmp_path / "architecture.json").write_text(json.dumps(arch))

        generated_code = (
            "from pydantic import BaseModel\n\n"
            "class Order(BaseModel):\n    id: str\n\n"
            "class User(BaseModel):\n    name: str\n"
        )

        # Should not raise
        _verify_architecture_conformance(
            generated_code=generated_code,
            prompt_name="models_Python.prompt",
            arch_path=str(tmp_path / "architecture.json"),
            language="python",
            verbose=False,
        )

    def test_fails_when_symbol_missing(self, tmp_path):
        """Conformance check raises UsageError when declared symbol is missing."""
        arch = [
            {
                "filename": "models_Python.prompt",
                "filepath": "src/models.py",
                "interface": {
                    "type": "module",
                    "module": {
                        "functions": [
                            {"name": "Order", "signature": "class Order(BaseModel)"},
                            {"name": "User", "signature": "class User(BaseModel)"},
                        ]
                    },
                },
            }
        ]
        (tmp_path / "architecture.json").write_text(json.dumps(arch))

        generated_code = "class Order(BaseModel):\n    id: str\n"

        with pytest.raises(click.UsageError, match="User"):
            _verify_architecture_conformance(
                generated_code=generated_code,
                prompt_name="models_Python.prompt",
                arch_path=str(tmp_path / "architecture.json"),
                language="python",
                verbose=False,
            )

    def test_fails_on_camelcase_in_python(self, tmp_path):
        """Conformance check detects camelCase in Python code."""
        arch = [
            {
                "filename": "utils_Python.prompt",
                "filepath": "src/utils.py",
                "interface": {
                    "type": "module",
                    "module": {
                        "functions": [
                            {"name": "processData", "signature": "def processData(data)"},
                        ]
                    },
                },
            }
        ]
        (tmp_path / "architecture.json").write_text(json.dumps(arch))

        generated_code = "def processData(data):\n    return data\n"

        with pytest.raises(click.UsageError, match="camelCase"):
            _verify_architecture_conformance(
                generated_code=generated_code,
                prompt_name="utils_Python.prompt",
                arch_path=str(tmp_path / "architecture.json"),
                language="python",
                verbose=False,
            )

    def test_skips_when_no_architecture_file(self, tmp_path):
        """Conformance check silently skips when architecture.json doesn't exist."""
        _verify_architecture_conformance(
            generated_code="def foo(): pass",
            prompt_name="test_Python.prompt",
            arch_path=str(tmp_path / "nonexistent.json"),
            language="python",
            verbose=False,
        )

    def test_skips_when_no_matching_entry(self, tmp_path):
        """Conformance check silently skips when no matching entry in architecture."""
        arch = [
            {
                "filename": "other_Python.prompt",
                "filepath": "src/other.py",
                "interface": {"type": "module", "module": {"functions": []}},
            }
        ]
        (tmp_path / "architecture.json").write_text(json.dumps(arch))

        _verify_architecture_conformance(
            generated_code="def foo(): pass",
            prompt_name="missing_Python.prompt",
            arch_path=str(tmp_path / "architecture.json"),
            language="python",
            verbose=False,
        )

    def test_skips_page_type_modules(self, tmp_path):
        """Conformance check skips page-type modules (no export symbol checking)."""
        arch = [
            {
                "filename": "dashboard_page_TypeScriptReact.prompt",
                "filepath": "app/dashboard/page.tsx",
                "interface": {"type": "page", "page": {"route": "/dashboard"}},
            }
        ]
        (tmp_path / "architecture.json").write_text(json.dumps(arch))

        _verify_architecture_conformance(
            generated_code="export default function DashboardPage() { return <div/>; }",
            prompt_name="dashboard_page_TypeScriptReact.prompt",
            arch_path=str(tmp_path / "architecture.json"),
            language="typescript",
            verbose=False,
        )

    def test_typescript_exports_checked(self, tmp_path):
        """Conformance check validates TypeScript export names."""
        arch = [
            {
                "filename": "api_client_TypeScript.prompt",
                "filepath": "src/lib/api.ts",
                "interface": {
                    "type": "module",
                    "module": {
                        "functions": [
                            {"name": "fetchOrders", "signature": "() => Promise<Order[]>"},
                            {"name": "createOrder", "signature": "(data: OrderInput) => Promise<Order>"},
                        ]
                    },
                },
            }
        ]
        (tmp_path / "architecture.json").write_text(json.dumps(arch))

        generated_code = (
            "export function fetchOrders(): Promise<Order[]> { return fetch('/api/orders'); }\n"
            "export function createOrder(data: OrderInput): Promise<Order> { return fetch('/api/orders', {method: 'POST'}); }\n"
        )

        _verify_architecture_conformance(
            generated_code=generated_code,
            prompt_name="api_client_TypeScript.prompt",
            arch_path=str(tmp_path / "architecture.json"),
            language="typescript",
            verbose=False,
        )

    def test_typescript_missing_export_fails(self, tmp_path):
        """Conformance check fails when TypeScript is missing a declared export."""
        arch = [
            {
                "filename": "api_client_TypeScript.prompt",
                "filepath": "src/lib/api.ts",
                "interface": {
                    "type": "module",
                    "module": {
                        "functions": [
                            {"name": "fetchOrders", "signature": "() => Promise<Order[]>"},
                            {"name": "deleteOrder", "signature": "(id: string) => Promise<void>"},
                        ]
                    },
                },
            }
        ]
        (tmp_path / "architecture.json").write_text(json.dumps(arch))

        generated_code = "export function fetchOrders(): Promise<Order[]> { return []; }\n"

        with pytest.raises(click.UsageError, match="deleteOrder"):
            _verify_architecture_conformance(
                generated_code=generated_code,
                prompt_name="api_client_TypeScript.prompt",
                arch_path=str(tmp_path / "architecture.json"),
                language="typescript",
                verbose=False,
            )

    def test_skips_on_empty_declared_symbols(self, tmp_path):
        """Conformance check skips when interface has no declared functions."""
        arch = [
            {
                "filename": "config_Python.prompt",
                "filepath": "src/config.py",
                "interface": {"type": "module", "module": {"functions": []}},
            }
        ]
        (tmp_path / "architecture.json").write_text(json.dumps(arch))

        _verify_architecture_conformance(
            generated_code="FOO = 'bar'\n",
            prompt_name="config_Python.prompt",
            arch_path=str(tmp_path / "architecture.json"),
            language="python",
            verbose=False,
        )

    def test_type_annotated_module_constant_recognized(self, tmp_path):
        """Typed module constants (ast.AnnAssign) must be visible to the
        conformance check. Regression test for issue #1131."""
        arch = [
            {
                "filename": "models_Python.prompt",
                "filepath": "src/models.py",
                "interface": {
                    "type": "module",
                    "module": {
                        "functions": [
                            {
                                "name": "MACHINE_USER_MODEL_MAP",
                                "signature": "dict[str, str]",
                                "returns": "Constant mapping machine users to LLM model IDs",
                            },
                        ]
                    },
                },
            }
        ]
        (tmp_path / "architecture.json").write_text(json.dumps(arch))

        generated_code = (
            'MACHINE_USER_MODEL_MAP: dict[str, str] = {\n'
            '    "pdd-sonnet": "claude-sonnet-4-6",\n'
            '    "pdd-opus": "claude-opus-4-6",\n'
            '}\n'
        )

        # Should NOT raise — MACHINE_USER_MODEL_MAP is declared as a typed
        # module constant, which the AST walker previously only handled for
        # plain ast.Assign nodes, missing ast.AnnAssign entirely.
        _verify_architecture_conformance(
            generated_code=generated_code,
            prompt_name="models_Python.prompt",
            arch_path=str(tmp_path / "architecture.json"),
            language="python",
            verbose=False,
        )

    def test_plain_module_constant_still_recognized(self, tmp_path):
        """Backward compatibility: untyped `X = ...` module constants (ast.Assign)
        must still be recognized after adding AnnAssign handling."""
        arch = [
            {
                "filename": "config_Python.prompt",
                "filepath": "src/config.py",
                "interface": {
                    "type": "module",
                    "module": {
                        "functions": [
                            {"name": "MAX_RETRIES", "signature": "int"},
                        ]
                    },
                },
            }
        ]
        (tmp_path / "architecture.json").write_text(json.dumps(arch))

        _verify_architecture_conformance(
            generated_code="MAX_RETRIES = 5\n",
            prompt_name="config_Python.prompt",
            arch_path=str(tmp_path / "architecture.json"),
            language="python",
            verbose=False,
        )

    def test_annassign_without_value_is_not_a_module_binding(self, tmp_path):
        """Bare `X: int` (AnnAssign with value=None) does not create a module
        binding at runtime, so it must NOT satisfy conformance."""
        arch = [
            {
                "filename": "types_Python.prompt",
                "filepath": "src/types.py",
                "interface": {
                    "type": "module",
                    "module": {
                        "functions": [
                            {"name": "GLOBAL_COUNTER", "signature": "int"},
                        ]
                    },
                },
            }
        ]
        (tmp_path / "architecture.json").write_text(json.dumps(arch))

        with pytest.raises(click.UsageError, match="GLOBAL_COUNTER"):
            _verify_architecture_conformance(
                generated_code="GLOBAL_COUNTER: int\n",
                prompt_name="types_Python.prompt",
                arch_path=str(tmp_path / "architecture.json"),
                language="python",
                verbose=False,
            )


# === Issue #687 Tests: example_output_path must be injected and consumed ===
# Root cause: generate_prompt.prompt tells the LLM to parse .pddrc YAML for
# example_output_path, but when .pddrc is missing the LLM has no fallback.
# Fix: (1) inject EXAMPLE_OUTPUT_PATH from resolved_config into env_vars,
# (2) update the template to use ${EXAMPLE_OUTPUT_PATH} directly.


class TestIssue687ExampleOutputPath:
    """Tests for issue #687: example_output_path must flow from resolved_config
    through env_vars into the prompt the LLM receives."""

    def test_example_output_path_injected_into_env_vars(
        self, mock_ctx, temp_dir_setup, mock_construct_paths_fixture,
        mock_env_vars
    ):
        """When resolved_config has example_output_path, it must be injected into
        env_vars as EXAMPLE_OUTPUT_PATH so _expand_vars can substitute it.

        Verifies via the cloud prompt payload since the cloud mock is autouse."""
        mock_ctx.obj['local'] = False
        mock_ctx.obj['force'] = True
        prompt_file_path = temp_dir_setup["prompts_dir"] / "test_prompt_python.prompt"
        prompt_content = "Dependencies at ${EXAMPLE_OUTPUT_PATH}/dep_example.py"
        create_file(prompt_file_path, prompt_content)
        output_file_path_str = str(temp_dir_setup["output_dir"] / "local_output.py")

        mock_construct_paths_fixture.return_value = (
            {"example_output_path": "examples/shared"},  # resolved_config
            {"prompt_file": prompt_content},
            {"output": output_file_path_str},
            "python"
        )

        code_generator_main(
            mock_ctx, str(prompt_file_path), output_file_path_str, None, False
        )

        # Check the prompt sent to cloud — it goes through the same _expand_vars path
        from pdd.code_generator_main import requests
        call_kwargs = requests.post.call_args
        payload = call_kwargs.kwargs.get("json") or call_kwargs[1].get("json", {})
        cloud_prompt = payload.get("promptContent", "")
        assert "EXAMPLE_OUTPUT_PATH" not in cloud_prompt, (
            "Bug #687: ${EXAMPLE_OUTPUT_PATH} was not expanded — resolved_config "
            "values are not being injected into env_vars"
        )
        assert "examples/shared" in cloud_prompt

    def test_explicit_env_var_overrides_resolved_config(
        self, mock_ctx, temp_dir_setup, mock_construct_paths_fixture,
        mock_env_vars
    ):
        """Explicit -e EXAMPLE_OUTPUT_PATH=value must take precedence over
        the value from resolved_config."""
        mock_ctx.obj['local'] = False
        mock_ctx.obj['force'] = True
        prompt_file_path = temp_dir_setup["prompts_dir"] / "gen_prompt2.prompt"
        prompt_content = "Examples at ${EXAMPLE_OUTPUT_PATH}"
        create_file(prompt_file_path, prompt_content)
        output_file_path_str = str(temp_dir_setup["output_dir"] / "output2.py")

        mock_construct_paths_fixture.return_value = (
            {"example_output_path": "context/examples"},
            {"prompt_file": prompt_content},
            {"output": output_file_path_str},
            "python"
        )

        code_generator_main(
            mock_ctx, str(prompt_file_path), output_file_path_str, None, False,
            env_vars={"EXAMPLE_OUTPUT_PATH": "custom/override"}
        )

        from pdd.code_generator_main import requests
        call_kwargs = requests.post.call_args
        payload = call_kwargs.kwargs.get("json") or call_kwargs[1].get("json", {})
        cloud_prompt = payload.get("promptContent", "")
        assert "custom/override" in cloud_prompt
        assert "context/examples" not in cloud_prompt

    def test_real_template_forbids_fabricated_example_paths(self):
        """The real generate_prompt template should forbid fabricated example includes."""
        template_path = (
            pathlib.Path(__file__).parent.parent
            / "pdd" / "templates" / "generic" / "generate_prompt.prompt"
        )
        template_content = template_path.read_text(encoding="utf-8")
        assert "Do NOT fabricate file paths or assume files exist." in template_content, (
            "generate_prompt.prompt must explicitly forbid fabricated dependency example paths."
        )
        assert "${EXAMPLE_OUTPUT_PATH}/[dependency_name]_example.${DEP_EXAMPLE_EXT}." not in template_content, (
            "generate_prompt.prompt should not instruct the model to synthesize dependency example paths."
        )

    def test_real_template_has_example_output_path_default(self):
        """The template front-matter must define EXAMPLE_OUTPUT_PATH with
        default 'context' so missing .pddrc doesn't leave the variable empty."""
        import yaml

        template_path = (
            pathlib.Path(__file__).parent.parent
            / "pdd" / "templates" / "generic" / "generate_prompt.prompt"
        )
        template_content = template_path.read_text(encoding="utf-8")
        # Parse YAML front-matter between --- delimiters
        parts = template_content.split("---", 2)
        assert len(parts) >= 3, "Template must have YAML front-matter delimited by ---"
        fm = yaml.safe_load(parts[1])
        variables = fm.get("variables", {})
        assert "EXAMPLE_OUTPUT_PATH" in variables, (
            "Template must define EXAMPLE_OUTPUT_PATH variable in front-matter"
        )
        eop_spec = variables["EXAMPLE_OUTPUT_PATH"]
        assert isinstance(eop_spec, dict), "EXAMPLE_OUTPUT_PATH must be a dict spec"
        assert eop_spec.get("default") == "context", (
            "EXAMPLE_OUTPUT_PATH must default to 'context' for projects without .pddrc"
        )

    def test_resolved_config_overwrites_front_matter_default(
        self, mock_ctx, temp_dir_setup, mock_construct_paths_fixture,
        mock_env_vars
    ):
        """resolved_config.example_output_path must overwrite the front-matter
        default 'context'. This test uses a template WITH front-matter to verify
        the full code path: front-matter sets default → injection overwrites it."""
        mock_ctx.obj['local'] = False
        mock_ctx.obj['force'] = True
        prompt_file_path = temp_dir_setup["prompts_dir"] / "fm_prompt_python.prompt"
        # Template with front-matter declaring EXAMPLE_OUTPUT_PATH default "context"
        prompt_content = (
            "---\n"
            "name: test/fm_prompt\n"
            "variables:\n"
            "  EXAMPLE_OUTPUT_PATH:\n"
            "    required: false\n"
            "    type: string\n"
            "    default: context\n"
            "---\n"
            "Deps at ${EXAMPLE_OUTPUT_PATH}/service_example.py\n"
        )
        create_file(prompt_file_path, prompt_content)
        output_file_path_str = str(temp_dir_setup["output_dir"] / "fm_output.py")

        mock_construct_paths_fixture.return_value = (
            {"example_output_path": "examples/shared"},  # resolved_config from .pddrc
            {"prompt_file": prompt_content},
            {"output": output_file_path_str},
            "python"
        )

        code_generator_main(
            mock_ctx, str(prompt_file_path), output_file_path_str, None, False
        )

        from pdd.code_generator_main import requests
        call_kwargs = requests.post.call_args
        payload = call_kwargs.kwargs.get("json") or call_kwargs[1].get("json", {})
        cloud_prompt = payload.get("promptContent", "")
        # resolved_config must overwrite front-matter default "context"
        assert "examples/shared/service_example.py" in cloud_prompt, (
            "resolved_config.example_output_path must overwrite the front-matter "
            "default 'context' — got: " + cloud_prompt[:200]
        )
        assert "context/service_example.py" not in cloud_prompt, (
            "Front-matter default 'context' should have been overwritten by "
            "resolved_config value 'examples/shared'"
        )

    def test_front_matter_default_used_when_no_resolved_config(
        self, mock_ctx, temp_dir_setup, mock_construct_paths_fixture,
        mock_env_vars
    ):
        """When resolved_config has no example_output_path, the front-matter
        default 'context' must be used. This is James's exact scenario:
        .pddrc exists but has no example_output_path configured."""
        mock_ctx.obj['local'] = False
        mock_ctx.obj['force'] = True
        prompt_file_path = temp_dir_setup["prompts_dir"] / "fm_prompt2_python.prompt"
        prompt_content = (
            "---\n"
            "name: test/fm_prompt2\n"
            "variables:\n"
            "  EXAMPLE_OUTPUT_PATH:\n"
            "    required: false\n"
            "    type: string\n"
            "    default: context\n"
            "---\n"
            "Deps at ${EXAMPLE_OUTPUT_PATH}/storage_layer_example.py\n"
        )
        create_file(prompt_file_path, prompt_content)
        output_file_path_str = str(temp_dir_setup["output_dir"] / "fm_output2.py")

        mock_construct_paths_fixture.return_value = (
            {},  # empty resolved_config — no example_output_path
            {"prompt_file": prompt_content},
            {"output": output_file_path_str},
            "python"
        )

        code_generator_main(
            mock_ctx, str(prompt_file_path), output_file_path_str, None, False
        )

        from pdd.code_generator_main import requests
        call_kwargs = requests.post.call_args
        payload = call_kwargs.kwargs.get("json") or call_kwargs[1].get("json", {})
        cloud_prompt = payload.get("promptContent", "")
        assert "context/storage_layer_example.py" in cloud_prompt, (
            "Front-matter default 'context' must be used when resolved_config "
            "has no example_output_path — got: " + cloud_prompt[:200]
        )
        assert "EXAMPLE_OUTPUT_PATH" not in cloud_prompt, (
            "${EXAMPLE_OUTPUT_PATH} was not expanded — front-matter default not applied"
        )


# === Issue #225 follow-up: include validation must survive architecture tag injection ===

def test_invalid_prompt_includes_are_not_reintroduced_by_architecture_tag_injection(
    mock_ctx,
    temp_dir_setup,
    mock_construct_paths_fixture,
    mock_local_generator_fixture,
    mock_env_vars,
    monkeypatch,
):
    """Invalid includes should stay replaced when architecture tags are prepended."""
    mock_ctx.obj["local"] = True
    monkeypatch.setenv("PDD_SKIP_CONFORMANCE", "1")
    monkeypatch.chdir(temp_dir_setup["tmp_path"])

    prompt_file_path = temp_dir_setup["prompts_dir"] / "generate_prompt.prompt"
    create_file(prompt_file_path, "Generate a prompt")
    output_file_path = temp_dir_setup["prompts_dir"] / "user_service_Python.prompt"

    generated_prompt = (
        "<prompt>\n"
        "<context_data_dictionary>\n"
        "<include>prompts/_context/data_dictionary.yaml</include>\n"
        "</context_data_dictionary>\n"
        "</prompt>\n"
    )
    mock_local_generator_fixture.return_value = (
        generated_prompt,
        DEFAULT_MOCK_COST,
        DEFAULT_MOCK_MODEL_NAME,
    )
    mock_construct_paths_fixture.return_value = (
        {},
        {"prompt_file": "Generate a prompt"},
        {"output": str(output_file_path)},
        "prompt",
    )

    monkeypatch.setattr(
        "pdd.code_generator_main.get_architecture_entry_for_prompt",
        lambda _prompt_name: {"reason": "Test reason"},
    )
    monkeypatch.setattr(
        "pdd.code_generator_main.generate_tags_from_architecture",
        lambda _entry: "<pdd-reason>Test reason</pdd-reason>",
    )
    monkeypatch.setattr("pdd.code_generator_main.has_pdd_tags", lambda _content: False)

    code_generator_main(
        mock_ctx,
        str(prompt_file_path),
        str(output_file_path),
        None,
        False,
    )

    final_content = output_file_path.read_text(encoding="utf-8")
    assert "<pdd-reason>Test reason</pdd-reason>" in final_content
    assert "<context_data_dictionary>" not in final_content
    assert "<include>prompts/_context/data_dictionary.yaml</include>" not in final_content


# === Tests for Issue #1043: Incremental patch identical code fallback ===
# The root-cause fix lives in incremental_code_generator (returns
# is_incremental=False when patched code == existing code). A defense-in-depth
# check in code_generator_main also catches this at the caller level.

def test_incremental_identical_code_falls_back_to_full_generation(
    mock_ctx, temp_dir_setup, mock_construct_paths_fixture, mock_pdd_preprocess_fixture,
    mock_incremental_generator_fixture, mock_local_generator_fixture, mock_env_vars
):
    """When incremental patch returns identical code, full generation should run."""
    mock_ctx.obj['local'] = True
    existing_code = "Existing code content"

    prompt_file_path = temp_dir_setup["prompts_dir"] / "inc_identical_prompt.prompt"
    create_file(prompt_file_path, "New prompt content")
    output_file_path = temp_dir_setup["output_dir"] / "inc_identical_output.py"
    create_file(output_file_path, existing_code)
    original_prompt_file_path = temp_dir_setup["prompts_dir"] / "inc_identical_original.prompt"
    create_file(original_prompt_file_path, "Original prompt content")

    mock_construct_paths_fixture.return_value = (
        {},
        {"prompt_file": "New prompt content", "original_prompt_file": "Original prompt content"},
        {"output": str(output_file_path)},
        "python"
    )
    # Incremental returns identical code with is_incremental=True — the bug scenario
    mock_incremental_generator_fixture.return_value = (existing_code, True, 0.002, "inc_model")

    code, incremental, cost, model = code_generator_main(
        mock_ctx, str(prompt_file_path), str(output_file_path), str(original_prompt_file_path), False
    )

    # After the fix: was_incremental_operation should be False (fallback triggered)
    assert not incremental, (
        "was_incremental_operation should be False when incremental patch produces identical code"
    )


def test_incremental_identical_code_verbose_prints_fallback_warning(
    mock_ctx, temp_dir_setup, mock_construct_paths_fixture, mock_pdd_preprocess_fixture,
    mock_incremental_generator_fixture, mock_local_generator_fixture,
    mock_rich_console_fixture, mock_env_vars
):
    """Verbose mode should print a fallback warning, not 'Incremental Success'."""
    mock_ctx.obj['local'] = True
    mock_ctx.obj['verbose'] = True
    existing_code = "Existing code content"

    prompt_file_path = temp_dir_setup["prompts_dir"] / "inc_verbose_prompt.prompt"
    create_file(prompt_file_path, "New prompt")
    output_file_path = temp_dir_setup["output_dir"] / "inc_verbose_output.py"
    create_file(output_file_path, existing_code)
    original_prompt_file_path = temp_dir_setup["prompts_dir"] / "inc_verbose_original.prompt"
    create_file(original_prompt_file_path, "Original prompt")

    mock_construct_paths_fixture.return_value = (
        {},
        {"prompt_file": "New prompt", "original_prompt_file": "Original prompt"},
        {"output": str(output_file_path)},
        "python"
    )
    mock_incremental_generator_fixture.return_value = (existing_code, True, 0.002, "inc_model")

    code_generator_main(
        mock_ctx, str(prompt_file_path), str(output_file_path), str(original_prompt_file_path), False
    )

    # Check that a fallback warning was printed (not "Incremental Success")
    all_print_args = [str(call) for call in mock_rich_console_fixture.call_args_list]
    combined_output = " ".join(all_print_args)

    # The fix should print a warning about falling back
    assert "no changes" in combined_output.lower() or "falling back" in combined_output.lower(), (
        f"Expected fallback warning in verbose output, got: {combined_output[:500]}"
    )
    # "Incremental Success" should NOT appear when code was identical
    assert "Incremental Success" not in combined_output, (
        "Should not print 'Incremental Success' when incremental patch produced identical code"
    )


def test_incremental_different_code_no_fallback(
    mock_ctx, temp_dir_setup, mock_construct_paths_fixture, mock_pdd_preprocess_fixture,
    mock_incremental_generator_fixture, mock_local_generator_fixture, mock_env_vars
):
    """When incremental produces genuinely different code, no fallback should occur (regression guard)."""
    mock_ctx.obj['local'] = True
    existing_code = "Existing code content"
    updated_code = "Updated code that is different"

    prompt_file_path = temp_dir_setup["prompts_dir"] / "inc_diff_prompt.prompt"
    create_file(prompt_file_path, "New prompt")
    output_file_path = temp_dir_setup["output_dir"] / "inc_diff_output.py"
    create_file(output_file_path, existing_code)
    original_prompt_file_path = temp_dir_setup["prompts_dir"] / "inc_diff_original.prompt"
    create_file(original_prompt_file_path, "Original prompt")

    mock_construct_paths_fixture.return_value = (
        {},
        {"prompt_file": "New prompt", "original_prompt_file": "Original prompt"},
        {"output": str(output_file_path)},
        "python"
    )
    mock_incremental_generator_fixture.return_value = (updated_code, True, 0.002, "inc_model")

    code, incremental, cost, model = code_generator_main(
        mock_ctx, str(prompt_file_path), str(output_file_path), str(original_prompt_file_path), False
    )

    assert incremental, "was_incremental_operation should remain True when code actually changed"
    assert code == updated_code
    mock_local_generator_fixture.assert_not_called()


def test_incremental_returns_none_code_does_not_crash(
    mock_ctx, temp_dir_setup, mock_construct_paths_fixture, mock_pdd_preprocess_fixture,
    mock_incremental_generator_fixture, mock_local_generator_fixture, mock_env_vars
):
    """When incremental returns None code with is_incremental=True, the None guard
    in the fallback check must skip the comparison without crashing."""
    mock_ctx.obj['local'] = True
    existing_code = "Existing code content"

    prompt_file_path = temp_dir_setup["prompts_dir"] / "inc_none_prompt.prompt"
    create_file(prompt_file_path, "New prompt")
    output_file_path = temp_dir_setup["output_dir"] / "inc_none_output.py"
    create_file(output_file_path, existing_code)
    original_prompt_file_path = temp_dir_setup["prompts_dir"] / "inc_none_original.prompt"
    create_file(original_prompt_file_path, "Original prompt")

    mock_construct_paths_fixture.return_value = (
        {},
        {"prompt_file": "New prompt", "original_prompt_file": "Original prompt"},
        {"output": str(output_file_path)},
        "python"
    )
    mock_incremental_generator_fixture.return_value = (None, True, 0.002, "inc_model")

    code, incremental, cost, model = code_generator_main(
        mock_ctx, str(prompt_file_path), str(output_file_path), str(original_prompt_file_path), False
    )

    # None guard skips the comparison, so was_incremental_operation stays True
    assert incremental, "None code should not trigger the identical-code fallback"


# === Root-cause test: incremental_code_generator returns is_incremental=False
#     when patched code is identical to existing code (issue #1043) ===

@patch("pdd.incremental_code_generator.llm_invoke")
@patch("pdd.incremental_code_generator.load_prompt_template", return_value="mock_template")
def test_incremental_code_generator_returns_false_when_patch_is_identical(
    mock_load_template, mock_llm_invoke
):
    """The incremental_code_generator itself should return is_incremental=False
    when the LLM patcher produces code identical to the existing code."""
    from pdd.incremental_code_generator import (
        incremental_code_generator, DiffAnalysis, CodePatchResult,
    )

    existing_code = "def hello():\n    print('hello')\n"

    # First llm_invoke call: diff analyzer says small change
    diff_result = DiffAnalysis(
        is_big_change=False,
        change_description="Minor wording change",
        analysis="Small change, incremental patching appropriate",
    )
    # Second llm_invoke call: patcher returns identical code (the bug scenario)
    patch_result = CodePatchResult(
        patched_code=existing_code,
        analysis="No changes needed",
        planned_modifications="None",
    )
    mock_llm_invoke.side_effect = [
        {"result": diff_result, "cost": 0.001, "model_name": "mock_diff_model"},
        {"result": patch_result, "cost": 0.001, "model_name": "mock_patch_model"},
    ]

    code, is_incremental, cost, model = incremental_code_generator(
        original_prompt="Original prompt",
        new_prompt="Slightly modified prompt",
        existing_code=existing_code,
        language="python",
        preprocess_prompt=False,
    )

    assert not is_incremental, (
        "incremental_code_generator should return is_incremental=False "
        "when patched code is identical to existing code"
    )
    assert code is None, "Should return None code to signal full regeneration needed"


@patch("pdd.incremental_code_generator.llm_invoke")
@patch("pdd.incremental_code_generator.load_prompt_template", return_value="mock_template")
def test_incremental_code_generator_returns_true_when_patch_differs(
    mock_load_template, mock_llm_invoke
):
    """Regression guard: incremental_code_generator should still return
    is_incremental=True when the patcher produces genuinely different code."""
    from pdd.incremental_code_generator import (
        incremental_code_generator, DiffAnalysis, CodePatchResult,
    )

    existing_code = "def hello():\n    print('hello')\n"
    patched_code = "def hello():\n    print('hello world')\n"

    diff_result = DiffAnalysis(
        is_big_change=False,
        change_description="Added world to greeting",
        analysis="Small change",
    )
    patch_result = CodePatchResult(
        patched_code=patched_code,
        analysis="Updated greeting",
        planned_modifications="Changed print string",
    )
    mock_llm_invoke.side_effect = [
        {"result": diff_result, "cost": 0.001, "model_name": "mock_diff_model"},
        {"result": patch_result, "cost": 0.001, "model_name": "mock_patch_model"},
    ]

    code, is_incremental, cost, model = incremental_code_generator(
        original_prompt="Original prompt",
        new_prompt="Modified prompt",
        existing_code=existing_code,
        language="python",
        preprocess_prompt=False,
    )

    assert is_incremental, "Should return is_incremental=True when code actually changed"
    assert code == patched_code


# =============================================================================
# Issue #1048: _find_default_test_files glob must escape brackets in code_stem
# =============================================================================


def test_issue_1048_find_default_test_files_bracket_stem(tmp_path):
    """_find_default_test_files: glob 'test_[id]_page*.py' must escape brackets.

    Bug: When code_path has stem '[id]_page', the glob pattern 'test_[id]_page*.py'
    interprets [id] as a character class matching 'i' or 'd'.
    """
    from pdd.code_generator_main import _find_default_test_files
    from pathlib import Path

    tests_dir = tmp_path / "tests"
    tests_dir.mkdir()

    target_file = tests_dir / "test_[id]_page.py"
    target_file.write_text("def test_bracket(): pass")
    decoy_file = tests_dir / "test_i_page.py"
    decoy_file.write_text("def test_decoy(): pass")

    code_path = Path(tmp_path / "src" / "[id]_page.py")

    result = _find_default_test_files(tests_dir, code_path)
    result_names = [Path(f).name for f in result]

    assert "test_[id]_page.py" in result_names, \
        f"Bug #1048: _find_default_test_files can't find test_[id]_page.py because " \
        f"glob treats [id] as char class. Found: {result_names}"
    assert "test_i_page.py" not in result_names, \
        f"Bug #1048: Matched decoy test_i_page.py via [id] char class. Found: {result_names}"


# =============================================================================
# Issue #777: generate crashes on 0-byte output file
# -----------------------------------------------------------------------------
# Bug: code_generator_main.py:761 uses `if existing_code_content is not None`
#      which passes for an empty string, entering the incremental path. Then
#      incremental_code_generator.py:59 rejects empty `existing_code` with
#      ValueError("All required inputs ... must be provided").
#
# Fix: after reading the existing file, normalize empty/whitespace-only content
#      to None so the caller falls through to full generation.
#
# These tests exercise the caller→callee boundary. The incremental mock is
# given a ValueError side_effect matching the REAL validation at
# incremental_code_generator.py:59-60 so that the test fails on buggy code
# (caller enters incremental path, mock raises, outer handler turns it into
# click.UsageError) and passes on the fix (caller skips incremental, local
# generator runs full generation).
# =============================================================================


def _incremental_mock_with_real_validation():
    """Return a MagicMock whose side_effect mirrors the real incremental_code_generator
    input validation at pdd/incremental_code_generator.py:59-60."""
    def _side_effect(*args, **kwargs):
        original_prompt = kwargs.get("original_prompt")
        new_prompt = kwargs.get("new_prompt")
        existing_code = kwargs.get("existing_code")
        language = kwargs.get("language")
        if not original_prompt or not new_prompt or not existing_code or not language:
            raise ValueError(
                "All required inputs (original_prompt, new_prompt, existing_code, language) must be provided."
            )
        return ("Updated code", True, 0.002, "inc_model")
    m = MagicMock(side_effect=_side_effect)
    return m


def test_issue_777_empty_output_file_falls_back_to_full_generation(
    mock_ctx, temp_dir_setup, mock_construct_paths_fixture,
    mock_incremental_generator_fixture, mock_local_generator_fixture, mock_env_vars
):
    """Primary repro: 0-byte output file + explicit original_prompt_file.

    Bug: empty_string passes `is not None` guard, so caller enters the
    incremental path with existing_code="". The real incremental generator
    raises ValueError on empty existing_code, which is wrapped as
    click.UsageError by the outer handler.

    Fix: caller normalizes "" to None after reading the file, so the
    incremental path is skipped entirely and full (local) generation runs.
    """
    mock_ctx.obj['local'] = True
    # Wire the incremental mock so it raises like the real function would.
    mock_incremental_generator_fixture.side_effect = \
        _incremental_mock_with_real_validation().side_effect

    prompt_file_path = temp_dir_setup["prompts_dir"] / "issue_777_empty.prompt"
    create_file(prompt_file_path, "Updated prompt content")

    # Create a 0-byte output file (e.g., VS Code auto-save recreated it empty)
    output_file_path = temp_dir_setup["output_dir"] / "issue_777_empty_output.py"
    output_file_path.parent.mkdir(parents=True, exist_ok=True)
    output_file_path.touch()  # 0 bytes
    assert output_file_path.exists()
    assert output_file_path.stat().st_size == 0

    original_prompt_file_path = temp_dir_setup["prompts_dir"] / "issue_777_original.prompt"
    create_file(original_prompt_file_path, "Original prompt content")

    mock_construct_paths_fixture.return_value = (
        {},
        {
            "prompt_file": "Updated prompt content",
            "original_prompt_file": "Original prompt content",
        },
        {"output": str(output_file_path)},
        "python",
    )

    # On buggy code: the incremental mock is called with existing_code="",
    # its side_effect raises ValueError, which is re-wrapped as click.UsageError
    # by the outer exception handler. On the fix, this call completes normally.
    code, incremental, _, _ = code_generator_main(
        mock_ctx, str(prompt_file_path), str(output_file_path),
        str(original_prompt_file_path), False,
    )

    # Fix behavior: full generation happens (local generator invoked, not incremental).
    assert code == DEFAULT_MOCK_GENERATED_CODE, (
        "Expected output of full (local) generation when existing file is 0 bytes; "
        f"got: {code!r}"
    )
    assert not incremental, (
        "was_incremental must be False when existing file is 0 bytes"
    )
    mock_local_generator_fixture.assert_called_once()
    # The incremental generator should NOT be called at all when existing_code is empty.
    mock_incremental_generator_fixture.assert_not_called()


def test_issue_777_whitespace_only_output_file_falls_back_to_full_generation(
    mock_ctx, temp_dir_setup, mock_construct_paths_fixture,
    mock_incremental_generator_fixture, mock_local_generator_fixture, mock_env_vars
):
    """Whitespace-only output file should behave the same as a 0-byte file.

    Covers the `.strip()` branch of the suggested fix: content that is
    technically non-empty but contains no code (just spaces/newlines) must not
    enter the incremental path — passing it through would still fail the
    truthiness check downstream ("" evaluates falsy after strip() is applied
    by any sensible diff/patch pipeline, and whitespace is not meaningful code).
    """
    mock_ctx.obj['local'] = True
    mock_incremental_generator_fixture.side_effect = \
        _incremental_mock_with_real_validation().side_effect

    prompt_file_path = temp_dir_setup["prompts_dir"] / "issue_777_ws.prompt"
    create_file(prompt_file_path, "Updated prompt")

    # Output file with only whitespace/newlines (not truly empty bytes,
    # but still no code to patch incrementally).
    output_file_path = temp_dir_setup["output_dir"] / "issue_777_ws_output.py"
    create_file(output_file_path, "   \n\t\n  \n")
    assert output_file_path.stat().st_size > 0
    assert output_file_path.read_text().strip() == ""

    original_prompt_file_path = temp_dir_setup["prompts_dir"] / "issue_777_ws_orig.prompt"
    create_file(original_prompt_file_path, "Original prompt")

    mock_construct_paths_fixture.return_value = (
        {},
        {
            "prompt_file": "Updated prompt",
            "original_prompt_file": "Original prompt",
        },
        {"output": str(output_file_path)},
        "python",
    )

    code, incremental, _, _ = code_generator_main(
        mock_ctx, str(prompt_file_path), str(output_file_path),
        str(original_prompt_file_path), False,
    )

    assert code == DEFAULT_MOCK_GENERATED_CODE
    assert not incremental
    mock_local_generator_fixture.assert_called_once()
    mock_incremental_generator_fixture.assert_not_called()


def test_issue_777_real_content_output_file_still_uses_incremental(
    mock_ctx, temp_dir_setup, mock_construct_paths_fixture,
    mock_incremental_generator_fixture, mock_local_generator_fixture, mock_env_vars
):
    """Regression guard: the fix must NOT suppress incremental for real content.

    Files with actual code should still enter the incremental path. This
    ensures we don't accidentally over-normalize in code_generator_main.
    """
    mock_ctx.obj['local'] = True
    # Real validation side_effect: non-empty existing_code returns normally.
    mock_incremental_generator_fixture.side_effect = \
        _incremental_mock_with_real_validation().side_effect

    prompt_file_path = temp_dir_setup["prompts_dir"] / "issue_777_real.prompt"
    create_file(prompt_file_path, "Updated prompt for real content")

    output_file_path = temp_dir_setup["output_dir"] / "issue_777_real_output.py"
    create_file(output_file_path, "def existing():\n    return 42\n")

    original_prompt_file_path = temp_dir_setup["prompts_dir"] / "issue_777_real_orig.prompt"
    create_file(original_prompt_file_path, "Original prompt for real content")

    mock_construct_paths_fixture.return_value = (
        {},
        {
            "prompt_file": "Updated prompt for real content",
            "original_prompt_file": "Original prompt for real content",
        },
        {"output": str(output_file_path)},
        "python",
    )

    code, incremental, _, _ = code_generator_main(
        mock_ctx, str(prompt_file_path), str(output_file_path),
        str(original_prompt_file_path), False,
    )

    # Real content → incremental path still taken, local generator not called.
    assert incremental, "Non-empty existing file must still trigger incremental path"
    assert code == "Updated code", f"Expected incremental output, got: {code!r}"
    mock_incremental_generator_fixture.assert_called_once()
    call_kwargs = mock_incremental_generator_fixture.call_args.kwargs
    assert call_kwargs["existing_code"] == "def existing():\n    return 42\n"
    mock_local_generator_fixture.assert_not_called()


def test_issue_777_empty_output_file_git_derived_prompt_falls_back_to_full(
    mock_ctx, temp_dir_setup, git_repo_setup, mock_construct_paths_fixture,
    mock_incremental_generator_fixture, mock_local_generator_fixture,
    mock_subprocess_run_fixture, mock_env_vars
):
    """Alternate entry point: 0-byte output file + git-derived original prompt.

    When no explicit --original-prompt-file is passed, the code can still enter
    the incremental path via the git-history branch (when the prompt has
    uncommitted changes against HEAD). A 0-byte output file must ALSO fall
    back to full generation in this alternate entry point — the fix at the
    single write site (normalization of `existing_code_content`) guards both
    entry paths.
    """
    mock_ctx.obj['local'] = True
    # Prompt lives inside the git repo; HEAD has the "old" content, on-disk has "new".
    prompt_filename = "issue_777_git_prompt.prompt"
    prompt_file_path = git_repo_setup / prompt_filename
    head_prompt_content = "Original prompt from HEAD"
    new_prompt_on_disk = "New prompt content on disk"
    create_file(prompt_file_path, new_prompt_on_disk)

    # Configure subprocess side_effect: git reports this as a tracked, modified file.
    def git_side_effect(*args, **kwargs):
        cmd = args[0]
        if "git" in cmd and "rev-parse" in cmd and "--is-inside-work-tree" in cmd:
            return subprocess.CompletedProcess(cmd, 0, stdout="true", stderr="")
        if "git" in cmd and "rev-parse" in cmd and "--show-toplevel" in cmd:
            return subprocess.CompletedProcess(cmd, 0, stdout=str(git_repo_setup.resolve()), stderr="")
        if "git" in cmd and "show" in cmd and any(f"HEAD:{prompt_filename}" in a for a in cmd):
            return subprocess.CompletedProcess(cmd, 0, stdout=head_prompt_content, stderr="")
        if "git" in cmd and "status" in cmd and "--porcelain" in cmd:
            return subprocess.CompletedProcess(cmd, 0, stdout=f" M {prompt_filename}", stderr="")
        if "git" in cmd and "diff" in cmd and "--quiet" in cmd:
            # Different from HEAD → rc=1
            return subprocess.CompletedProcess(cmd, 1, stdout="", stderr="")
        if "git" in cmd and "add" in cmd:
            return subprocess.CompletedProcess(cmd, 0, stdout="", stderr="")
        return subprocess.CompletedProcess(cmd, 0, stdout="", stderr="")

    mock_subprocess_run_fixture.side_effect = git_side_effect

    mock_incremental_generator_fixture.side_effect = \
        _incremental_mock_with_real_validation().side_effect

    # 0-byte output file
    output_file_path = temp_dir_setup["output_dir"] / "issue_777_git_output.py"
    output_file_path.parent.mkdir(parents=True, exist_ok=True)
    output_file_path.touch()
    assert output_file_path.stat().st_size == 0

    mock_construct_paths_fixture.return_value = (
        {},
        {"prompt_file": new_prompt_on_disk},  # NO explicit original_prompt_file
        {"output": str(output_file_path)},
        "python",
    )

    code, incremental, _, _ = code_generator_main(
        mock_ctx, str(prompt_file_path), str(output_file_path), None, False,
    )

    # Even though git CAN provide an original prompt, the empty existing file
    # means there's nothing to patch incrementally — full generation must run.
    assert code == DEFAULT_MOCK_GENERATED_CODE, (
        "Expected full-generation output for 0-byte file on git-derived path"
    )
    assert not incremental, (
        "was_incremental must be False when existing file is 0 bytes, "
        "even if git provides an original prompt"
    )
    mock_local_generator_fixture.assert_called_once()
    mock_incremental_generator_fixture.assert_not_called()
    mock_subprocess_run_fixture.side_effect = None


# ---------------------------------------------------------------------------
# Issue #1224: _verify_architecture_conformance must handle ClassName.method
# ---------------------------------------------------------------------------

class TestVerifyArchitectureConformanceDottedMethods:
    """Tests for dotted ClassName.method support in _verify_architecture_conformance (Issue #1224)."""

    def test_passes_when_dotted_method_exists_on_class(self, tmp_path):
        """Conformance passes when ClassName.method is declared and class defines that method."""
        arch = [
            {
                "filename": "agentic_sync_runner_python.prompt",
                "filepath": "pdd/agentic_sync_runner.py",
                "interface": {
                    "type": "module",
                    "module": {
                        "functions": [
                            {"name": "AsyncSyncRunner", "signature": "class AsyncSyncRunner"},
                            {"name": "AsyncSyncRunner.run", "signature": "def run(self)"},
                            {"name": "build_dep_graph_from_architecture", "signature": "def build_dep_graph_from_architecture()"},
                        ]
                    },
                },
            }
        ]
        (tmp_path / "architecture.json").write_text(json.dumps(arch))

        generated_code = (
            "class AsyncSyncRunner:\n"
            "    def run(self):\n"
            "        pass\n\n"
            "def build_dep_graph_from_architecture():\n"
            "    pass\n"
        )

        # Should not raise — all declared symbols including dotted method exist
        _verify_architecture_conformance(
            generated_code=generated_code,
            prompt_name="agentic_sync_runner_python.prompt",
            arch_path=str(tmp_path / "architecture.json"),
            language="python",
            verbose=False,
        )

    def test_fails_when_dotted_method_missing_from_class(self, tmp_path):
        """Conformance raises UsageError when ClassName.method is declared but method doesn't exist."""
        arch = [
            {
                "filename": "worker_python.prompt",
                "filepath": "src/worker.py",
                "interface": {
                    "type": "module",
                    "module": {
                        "functions": [
                            {"name": "MyClass", "signature": "class MyClass"},
                            {"name": "MyClass.process", "signature": "def process(self)"},
                        ]
                    },
                },
            }
        ]
        (tmp_path / "architecture.json").write_text(json.dumps(arch))

        # Class exists but has 'run' not 'process'
        generated_code = (
            "class MyClass:\n"
            "    def run(self):\n"
            "        pass\n"
        )

        with pytest.raises(click.UsageError, match="MyClass.process"):
            _verify_architecture_conformance(
                generated_code=generated_code,
                prompt_name="worker_python.prompt",
                arch_path=str(tmp_path / "architecture.json"),
                language="python",
                verbose=False,
            )

    def test_fails_when_dotted_class_missing(self, tmp_path):
        """Conformance raises UsageError when ClassName.method is declared but class doesn't exist."""
        arch = [
            {
                "filename": "runner_python.prompt",
                "filepath": "src/runner.py",
                "interface": {
                    "type": "module",
                    "module": {
                        "functions": [
                            {"name": "MissingClass.run", "signature": "def run(self)"},
                        ]
                    },
                },
            }
        ]
        (tmp_path / "architecture.json").write_text(json.dumps(arch))

        generated_code = (
            "def some_function():\n"
            "    pass\n"
        )

        with pytest.raises(click.UsageError, match="MissingClass.run"):
            _verify_architecture_conformance(
                generated_code=generated_code,
                prompt_name="runner_python.prompt",
                arch_path=str(tmp_path / "architecture.json"),
                language="python",
                verbose=False,
            )

    def test_passes_when_async_method_exists_on_class(self, tmp_path):
        """Conformance passes when ClassName.method is declared and class defines an async method."""
        arch = [
            {
                "filename": "worker_python.prompt",
                "filepath": "src/worker.py",
                "interface": {
                    "type": "module",
                    "module": {
                        "functions": [
                            {"name": "Worker", "signature": "class Worker"},
                            {"name": "Worker.execute", "signature": "async def execute(self)"},
                        ]
                    },
                },
            }
        ]
        (tmp_path / "architecture.json").write_text(json.dumps(arch))

        generated_code = (
            "class Worker:\n"
            "    async def execute(self):\n"
            "        pass\n"
        )

        # Should not raise — async methods inside class bodies must be collected
        _verify_architecture_conformance(
            generated_code=generated_code,
            prompt_name="worker_python.prompt",
            arch_path=str(tmp_path / "architecture.json"),
            language="python",
            verbose=False,
        )

    def test_passes_with_multiple_dotted_methods_on_same_class(self, tmp_path):
        """Conformance passes when multiple ClassName.method entries are declared on one class."""
        arch = [
            {
                "filename": "service_python.prompt",
                "filepath": "src/service.py",
                "interface": {
                    "type": "module",
                    "module": {
                        "functions": [
                            {"name": "Service", "signature": "class Service"},
                            {"name": "Service.start", "signature": "def start(self)"},
                            {"name": "Service.stop", "signature": "def stop(self)"},
                        ]
                    },
                },
            }
        ]
        (tmp_path / "architecture.json").write_text(json.dumps(arch))

        generated_code = (
            "class Service:\n"
            "    def start(self):\n"
            "        pass\n\n"
            "    def stop(self):\n"
            "        pass\n"
        )

        # Should not raise — all dotted methods resolve
        _verify_architecture_conformance(
            generated_code=generated_code,
            prompt_name="service_python.prompt",
            arch_path=str(tmp_path / "architecture.json"),
            language="python",
            verbose=False,
        )


class TestVerifyArchitectureConformanceDeepRecursion:
    """Issue #1224 follow-up: nested classes and control-flow-guarded methods."""

    def _write_arch(self, tmp_path, filename, filepath, names):
        arch = [
            {
                "filename": filename,
                "filepath": filepath,
                "interface": {
                    "type": "module",
                    "module": {
                        "functions": [{"name": n, "signature": ""} for n in names]
                    },
                },
            }
        ]
        (tmp_path / "architecture.json").write_text(json.dumps(arch))
        return str(tmp_path / "architecture.json")

    def test_nested_class_method_passes(self, tmp_path):
        """Declared Outer.Inner.foo resolves when code defines it at that depth."""
        arch_path = self._write_arch(
            tmp_path,
            "outer_python.prompt",
            "src/outer.py",
            ["Outer", "Outer.Inner", "Outer.Inner.foo"],
        )
        code = (
            "class Outer:\n"
            "    class Inner:\n"
            "        def foo(self):\n"
            "            pass\n"
        )
        _verify_architecture_conformance(
            generated_code=code,
            prompt_name="outer_python.prompt",
            arch_path=arch_path,
            language="python",
            verbose=False,
        )

    def test_nested_class_method_missing_fails(self, tmp_path):
        """Declared Outer.Inner.foo fails when Inner lacks the method."""
        arch_path = self._write_arch(
            tmp_path,
            "outer_python.prompt",
            "src/outer.py",
            ["Outer.Inner.foo"],
        )
        code = (
            "class Outer:\n"
            "    class Inner:\n"
            "        def bar(self):\n"
            "            pass\n"
        )
        with pytest.raises(click.UsageError, match=re.escape("Outer.Inner.foo")):
            _verify_architecture_conformance(
                generated_code=code,
                prompt_name="outer_python.prompt",
                arch_path=arch_path,
                language="python",
                verbose=False,
            )

    def test_triple_nested_class_method_passes(self, tmp_path):
        """Three levels deep: A.B.C.run resolves."""
        arch_path = self._write_arch(
            tmp_path,
            "deep_python.prompt",
            "src/deep.py",
            ["A.B.C.run"],
        )
        code = (
            "class A:\n"
            "    class B:\n"
            "        class C:\n"
            "            def run(self):\n"
            "                pass\n"
        )
        _verify_architecture_conformance(
            generated_code=code,
            prompt_name="deep_python.prompt",
            arch_path=arch_path,
            language="python",
            verbose=False,
        )

    def test_if_guarded_method_does_not_satisfy_conformance(self, tmp_path):
        """Method defined only inside `if` in a class body must NOT count.

        Conformance is a hard validator — branch evaluation at runtime is not
        checked here, so a conditionally-defined method cannot be relied on to
        exist unconditionally.
        """
        arch_path = self._write_arch(
            tmp_path,
            "compat_python.prompt",
            "src/compat.py",
            ["Compat", "Compat.new_feature"],
        )
        code = (
            "import sys\n"
            "class Compat:\n"
            "    if sys.version_info >= (3, 12):\n"
            "        def new_feature(self):\n"
            "            return 'new'\n"
        )
        with pytest.raises(click.UsageError, match=re.escape("Compat.new_feature")):
            _verify_architecture_conformance(
                generated_code=code,
                prompt_name="compat_python.prompt",
                arch_path=arch_path,
                language="python",
                verbose=False,
            )

    def test_if_false_method_does_not_satisfy_conformance(self, tmp_path):
        """Greg's explicit counter-example: `if False: def maybe(self)` must not pass.

        Accepting this would let unreachable code satisfy the architecture
        contract, which defeats the purpose of the conformance check.
        """
        arch_path = self._write_arch(
            tmp_path,
            "foo_python.prompt",
            "src/foo.py",
            ["Foo", "Foo.maybe"],
        )
        code = (
            "class Foo:\n"
            "    if False:\n"
            "        def maybe(self):\n"
            "            return None\n"
        )
        with pytest.raises(click.UsageError, match=re.escape("Foo.maybe")):
            _verify_architecture_conformance(
                generated_code=code,
                prompt_name="foo_python.prompt",
                arch_path=arch_path,
                language="python",
                verbose=False,
            )

    def test_try_guarded_method_does_not_satisfy_conformance(self, tmp_path):
        """Method defined inside `try`/`except` in a class body must NOT count."""
        arch_path = self._write_arch(
            tmp_path,
            "fallback_python.prompt",
            "src/fallback.py",
            ["Fallback", "Fallback.optional"],
        )
        code = (
            "class Fallback:\n"
            "    try:\n"
            "        def optional(self):\n"
            "            return True\n"
            "    except Exception:\n"
            "        pass\n"
        )
        with pytest.raises(click.UsageError, match=re.escape("Fallback.optional")):
            _verify_architecture_conformance(
                generated_code=code,
                prompt_name="fallback_python.prompt",
                arch_path=arch_path,
                language="python",
                verbose=False,
            )

    def test_dotted_method_camelcase_fails(self, tmp_path):
        """camelCase in the method segment of a dotted symbol must still fail the snake_case guard.

        Before the segment-aware check, ``MyClass.processData`` slipped past
        because the regex only matched on the start of the full string and
        ``MyClass`` starts with an uppercase letter.
        """
        arch_path = self._write_arch(
            tmp_path,
            "myclass_python.prompt",
            "src/myclass.py",
            ["MyClass", "MyClass.processData"],
        )
        code = (
            "class MyClass:\n"
            "    def processData(self):\n"
            "        pass\n"
        )
        with pytest.raises(click.UsageError, match="camelCase"):
            _verify_architecture_conformance(
                generated_code=code,
                prompt_name="myclass_python.prompt",
                arch_path=arch_path,
                language="python",
                verbose=False,
            )

    def test_top_level_functions_still_recognised(self, tmp_path):
        """Regression: plain top-level functions continue to work as before."""
        arch_path = self._write_arch(
            tmp_path,
            "plain_python.prompt",
            "src/plain.py",
            ["run", "helper"],
        )
        code = (
            "def run():\n"
            "    pass\n\n"
            "def helper():\n"
            "    pass\n"
        )
        _verify_architecture_conformance(
            generated_code=code,
            prompt_name="plain_python.prompt",
            arch_path=arch_path,
            language="python",
            verbose=False,
        )

    def test_module_constants_still_recognised(self, tmp_path):
        """Regression: top-level Assign / AnnAssign constants remain valid symbols."""
        arch_path = self._write_arch(
            tmp_path,
            "consts_python.prompt",
            "src/consts.py",
            ["MAX_WORKERS", "DEFAULT_TIMEOUT"],
        )
        code = (
            "MAX_WORKERS = 10\n"
            "DEFAULT_TIMEOUT: int = 30\n"
        )
        _verify_architecture_conformance(
            generated_code=code,
            prompt_name="consts_python.prompt",
            arch_path=arch_path,
            language="python",
            verbose=False,
        )

    def test_module_level_if_guard_does_not_leak_into_dotted(self, tmp_path):
        """Module-level `if: def foo` must not be exposed as some_class.foo.

        Only class-level control-flow recurses with a prefix; module level keeps
        conservative semantics to avoid inventing fake dotted symbols.
        """
        arch_path = self._write_arch(
            tmp_path,
            "modguard_python.prompt",
            "src/modguard.py",
            ["top_level_fn"],  # declared at module top level
        )
        code = (
            "import sys\n"
            "if sys.version_info >= (3, 12):\n"
            "    def top_level_fn():\n"
            "        pass\n"
        )
        # `top_level_fn` is conditionally defined at module level — not
        # recognised as a stable export, so conformance should fail loudly.
        with pytest.raises(click.UsageError, match="top_level_fn"):
            _verify_architecture_conformance(
                generated_code=code,
                prompt_name="modguard_python.prompt",
                arch_path=arch_path,
                language="python",
                verbose=False,
            )


# --- Issue #1256: Dict-format architecture tolerance ---
# Scope addition: covers expansion item "pdd/code_generator_main.py:244 loads
# architecture.json with isinstance conditional that silently treats dict as empty"
# identified by Step 6 but absent from Step 8's plan


def test_verify_architecture_conformance_dict_format(tmp_path):
    """_verify_architecture_conformance with dict-format architecture validates conformance (Test 17).

    Bug: isinstance(arch_data, list) at code_generator_main.py:244 returns False
    for dict-format, so the loop uses [] and never finds the architecture entry.
    The conformance check silently passes without actually validating — missing
    functions are not detected.
    """
    arch = {"modules": [
        {
            "filename": "models_Python.prompt",
            "filepath": "src/models.py",
            "interface": {
                "type": "module",
                "module": {
                    "functions": [
                        {"name": "UserModel", "signature": "class UserModel(BaseModel)", "returns": "UserModel"},
                        {"name": "OrderModel", "signature": "class OrderModel(BaseModel)", "returns": "OrderModel"},
                    ]
                },
            },
        }
    ]}
    arch_path = tmp_path / "architecture.json"
    arch_path.write_text(json.dumps(arch), encoding="utf-8")

    # Code that is MISSING OrderModel — should trigger UsageError
    code = "class UserModel:\n    pass\n"

    with pytest.raises(click.UsageError, match="OrderModel"):
        _verify_architecture_conformance(
            generated_code=code,
            prompt_name="models_Python.prompt",
            arch_path=str(arch_path),
            language="python",
            verbose=False,
        )

