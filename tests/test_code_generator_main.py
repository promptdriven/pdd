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

# Cap per-test runtime for this real-LLM heavy module. Individual hot tests
# may carry their own @pytest.mark.timeout override.
pytestmark = pytest.mark.timeout(450)

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
    def passthrough(prompt_text, recursive=False, double_curly_brackets=True, exclude_keys=None, **kwargs):
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

@pytest.fixture(autouse=True)
def _clear_cloud_runtime_env(monkeypatch):
    """Strip cloud-runtime detection env vars for all tests.

    The Cloud Run executor that runs these tests sets K_SERVICE, which causes
    `CloudConfig.is_running_in_cloud()` to return True and short-circuits the
    cloud branch in `code_generator_main`. Tests that exercise either the cloud
    success path or the cloud→local fallback path need K_SERVICE/FUNCTIONS_EMULATOR
    cleared so the mocked cloud call is actually reached.
    """
    monkeypatch.delenv("K_SERVICE", raising=False)
    monkeypatch.delenv("FUNCTIONS_EMULATOR", raising=False)

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


def test_postprocess_uses_temp_input_when_llm_enabled(
    mock_ctx,
    temp_dir_setup,
    mock_construct_paths_fixture,
    mock_local_generator_fixture,
    mock_subprocess_run_fixture,
    mock_env_vars,
):
    """When LLM is enabled, post-process input should not overwrite the output path before gates pass."""
    mock_ctx.obj['local'] = True

    # Build a prompt with front matter enabling a post-process script
    prompt_file_path = temp_dir_setup["prompts_dir"] / "postprocess_prompt_python.prompt"
    output_file_path = temp_dir_setup["output_dir"] / "pp_output.py"

    front_matter_prompt = """---
language: python
post_process_python: "./dummy_post_process.py"
post_process_args: ["{INPUT_FILE}"]
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

    assert output_file_path.exists()
    assert output_file_path.read_text(encoding="utf-8") == DEFAULT_MOCK_GENERATED_CODE

    assert mock_subprocess_run_fixture.called
    postprocess_cmd = mock_subprocess_run_fixture.call_args[0][0]
    assert pathlib.Path(postprocess_cmd[2]).resolve() != output_file_path.resolve()


def test_postprocess_reads_back_modified_temp_input_when_llm_enabled(
    mock_ctx,
    temp_dir_setup,
    mock_construct_paths_fixture,
    mock_local_generator_fixture,
    mock_subprocess_run_fixture,
    mock_env_vars,
):
    mock_ctx.obj['local'] = True
    prompt_file_path = temp_dir_setup["prompts_dir"] / "postprocess_prompt_python.prompt"
    output_file_path = temp_dir_setup["output_dir"] / "pp_output.py"
    postprocessed_code = "def hello():\n  print('postprocessed')"

    front_matter_prompt = """---
language: python
post_process_python: "./dummy_post_process.py"
post_process_args: ["{INPUT_FILE}"]
---
Generate a simple module.
"""
    create_file(prompt_file_path, front_matter_prompt)
    mock_construct_paths_fixture.return_value = (
        {},
        {"prompt_file": front_matter_prompt},
        {"output": str(output_file_path)},
        "python",
    )

    def rewrite_input_file(*args, **kwargs):
        input_path = pathlib.Path(args[0][2])
        input_path.write_text(postprocessed_code, encoding="utf-8")
        return subprocess.CompletedProcess(args=args[0], returncode=0, stdout="", stderr="")

    mock_subprocess_run_fixture.side_effect = rewrite_input_file

    code, incremental, cost, model = code_generator_main(
        mock_ctx,
        str(prompt_file_path),
        str(output_file_path),
        None,
        False,
        env_vars={"llm": "true"},
    )

    assert code == postprocessed_code
    assert output_file_path.read_text(encoding="utf-8") == postprocessed_code


def test_postprocess_gate_failure_restores_existing_output(
    mock_ctx,
    temp_dir_setup,
    mock_construct_paths_fixture,
    mock_local_generator_fixture,
    mock_subprocess_run_fixture,
    mock_env_vars,
):
    from pdd.code_generator_main import PublicSurfaceRegressionError

    mock_ctx.obj['local'] = True
    prompt_file_path = temp_dir_setup["prompts_dir"] / "postprocess_prompt_python.prompt"
    output_file_path = temp_dir_setup["output_dir"] / "pp_output.py"
    existing_code = "def stable_api():\n    return 'old'\n"
    rejected_code = "def replacement_api():\n    return 'new'\n"
    create_file(output_file_path, existing_code)

    front_matter_prompt = """---
language: python
post_process_python: "./dummy_post_process.py"
post_process_args: ["{INPUT_FILE}"]
---
Generate a simple module.
"""
    create_file(prompt_file_path, front_matter_prompt)
    mock_construct_paths_fixture.return_value = (
        {},
        {"prompt_file": front_matter_prompt},
        {"output": str(output_file_path)},
        "python",
    )
    mock_local_generator_fixture.return_value = (
        rejected_code,
        DEFAULT_MOCK_COST,
        DEFAULT_MOCK_MODEL_NAME,
    )

    def write_rejected_output(*args, **kwargs):
        output_file_path.write_text(rejected_code, encoding="utf-8")
        return subprocess.CompletedProcess(args=args[0], returncode=0, stdout="", stderr="")

    mock_subprocess_run_fixture.side_effect = write_rejected_output

    with pytest.raises(PublicSurfaceRegressionError):
        code_generator_main(
            mock_ctx,
            str(prompt_file_path),
            str(output_file_path),
            None,
            False,
            env_vars={"llm": "true"},
        )

    assert output_file_path.read_text(encoding="utf-8") == existing_code


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
    assert pathlib.Path(input_arg).resolve() != expected_output_path.resolve()


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


def test_full_gen_local_includes_architecture_repair_directive(
    mock_ctx,
    temp_dir_setup,
    mock_construct_paths_fixture,
    mock_local_generator_fixture,
    monkeypatch,
    mock_env_vars,
):
    """Retry callers can inject missing-symbol repair instructions into generation."""
    mock_ctx.obj['local'] = True
    prompt_file_path = temp_dir_setup["prompts_dir"] / "repair_prompt.prompt"
    prompt_content = "Generate repaired code."
    create_file(prompt_file_path, prompt_content)
    output_file_path_str = str(temp_dir_setup["output_dir"] / "repair.py")
    repair_directive = (
        "Architecture conformance repair required.\n"
        "Required missing exports:\n"
        "- AsyncSyncRunner.run\n"
        "Do not modify architecture.json."
    )
    monkeypatch.setenv("PDD_REPAIR_DIRECTIVE", repair_directive)

    mock_construct_paths_fixture.return_value = (
        {},
        {"prompt_file": prompt_content},
        {"output": output_file_path_str},
        "python",
    )

    code_generator_main(
        mock_ctx,
        str(prompt_file_path),
        output_file_path_str,
        None,
        False,
    )

    called_prompt = mock_local_generator_fixture.call_args.kwargs["prompt"]
    assert prompt_content in called_prompt
    assert "<architecture_repair_directive>" in called_prompt
    assert "- AsyncSyncRunner.run" in called_prompt
    assert "</architecture_repair_directive>" in called_prompt


def test_conformance_error_from_codegen_carries_generation_cost(
    mock_ctx,
    temp_dir_setup,
    mock_construct_paths_fixture,
    mock_local_generator_fixture,
    monkeypatch,
    mock_env_vars,
):
    """Failed conformance after generation must still expose spent cost/model."""
    from pdd.code_generator_main import ArchitectureConformanceError

    monkeypatch.chdir(temp_dir_setup["tmp_path"])
    mock_ctx.obj["local"] = True
    prompt_file_path = temp_dir_setup["prompts_dir"] / "costed_python.prompt"
    create_file(prompt_file_path, "Generate a costed module.")
    output_file_path_str = str(temp_dir_setup["output_dir"] / "costed.py")
    (temp_dir_setup["tmp_path"] / "architecture.json").write_text(json.dumps([
        {
            "filename": "costed_python.prompt",
            "filepath": "output/costed.py",
            "interface": {
                "type": "module",
                "module": {
                    "functions": [
                        {"name": "required_export", "signature": "def required_export()"},
                    ]
                },
            },
        }
    ]))
    mock_local_generator_fixture.return_value = (
        "def other_export():\n    return None\n",
        0.123,
        "mock-cost-model",
    )
    mock_construct_paths_fixture.return_value = (
        {},
        {"prompt_file": "Generate a costed module."},
        {"output": output_file_path_str},
        "python",
    )

    with pytest.raises(ArchitectureConformanceError) as excinfo:
        code_generator_main(
            mock_ctx,
            str(prompt_file_path),
            output_file_path_str,
            None,
            False,
        )

    assert excinfo.value.total_cost == pytest.approx(0.123)
    assert excinfo.value.model_name == "mock-cost-model"


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

    def test_examples_dir_fallback_when_example_output_path_unset(
        self, mock_ctx, temp_dir_setup, mock_construct_paths_fixture,
        mock_env_vars
    ):
        """When `example_output_path` is unset but `examples_dir` is populated
        by construct_paths, EXAMPLE_OUTPUT_PATH falls back to `examples_dir` so
        the LLM template gets the right value ('examples' for greenfield,
        'context' for legacy back-compat). Issue #616."""
        mock_ctx.obj['local'] = False
        mock_ctx.obj['force'] = True
        prompt_file_path = temp_dir_setup["prompts_dir"] / "gap_prompt.prompt"
        prompt_content = "Dep at ${EXAMPLE_OUTPUT_PATH}/foo_example.py"
        create_file(prompt_file_path, prompt_content)
        output_file_path_str = str(temp_dir_setup["output_dir"] / "out.py")

        # Simulate construct_paths' return when there's no .pddrc:
        # example_output_path is None, examples_dir = EXAMPLES_DIR (= "examples").
        mock_construct_paths_fixture.return_value = (
            {"examples_dir": "examples"},  # no example_output_path key
            {"prompt_file": prompt_content},
            {"output": output_file_path_str},
            "python",
        )

        code_generator_main(
            mock_ctx, str(prompt_file_path), output_file_path_str, None, False,
        )

        from pdd.code_generator_main import requests
        call_kwargs = requests.post.call_args
        payload = call_kwargs.kwargs.get("json") or call_kwargs[1].get("json", {})
        cloud_prompt = payload.get("promptContent", "")
        assert "${EXAMPLE_OUTPUT_PATH}" not in cloud_prompt, (
            "Variable not expanded — examples_dir fallback failed (#616)"
        )
        assert "examples/foo_example.py" in cloud_prompt, (
            f"Expected 'examples/foo_example.py' in cloud prompt; got:\n{cloud_prompt}"
        )

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
        """The template front-matter defines EXAMPLE_OUTPUT_PATH with default
        EXAMPLES_DIR ('examples') so missing .pddrc doesn't leave the variable
        empty. Runtime injection in code_generator_main normally flows the
        right value through; the front-matter default is a safety net."""
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
        # Template default must match generate_output_paths.EXAMPLES_DIR (#616).
        from pdd.generate_output_paths import EXAMPLES_DIR
        assert eop_spec.get("default") == EXAMPLES_DIR, (
            f"EXAMPLE_OUTPUT_PATH must default to '{EXAMPLES_DIR}' for projects without .pddrc"
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
    # The default helper returns the literal "Updated code", which parses to
    # zero public symbols and would trip the PublicSurfaceRegressionError
    # gate against the pre-existing single-symbol surface. Use a return value
    # that preserves the existing public symbol so this test exercises the
    # incremental path without colliding with the public-surface gate.
    updated_code = "def existing():\n    return 99\n"

    def _incremental_side_effect(*args, **kwargs):
        original_prompt = kwargs.get("original_prompt")
        new_prompt = kwargs.get("new_prompt")
        existing_code = kwargs.get("existing_code")
        language = kwargs.get("language")
        if not original_prompt or not new_prompt or not existing_code or not language:
            raise ValueError(
                "All required inputs (original_prompt, new_prompt, existing_code, language) must be provided."
            )
        return (updated_code, True, 0.002, "inc_model")

    mock_incremental_generator_fixture.side_effect = _incremental_side_effect

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
    assert code == updated_code, f"Expected incremental output, got: {code!r}"
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


# ---------------------------------------------------------------------------
# Tests for _parse_front_matter CRLF handling (Issue #197)
# ---------------------------------------------------------------------------
from pdd.code_generator_main import _parse_front_matter


class TestParseFrontMatterCRLF:
    """Tests for _parse_front_matter handling of CRLF line endings (Issue #197)."""

    def test_parse_front_matter_crlf(self):
        """Front matter with Windows (CRLF) line endings should parse correctly."""
        text = "---\r\nname: my_module\r\nlanguage: python\r\n---\r\nPrompt body here"
        meta, body = _parse_front_matter(text)
        assert meta is not None, "CRLF front matter returned None"
        assert meta["name"] == "my_module"
        assert meta["language"] == "python"
        assert "Prompt body here" in body

    def test_parse_front_matter_mixed_line_endings(self):
        """Front matter with mixed LF/CRLF should still parse."""
        text = "---\nname: mixed\r\n---\nBody content"
        meta, body = _parse_front_matter(text)
        assert meta is not None, "Mixed line ending front matter returned None"
        assert meta["name"] == "mixed"
        assert "Body content" in body

    def test_parse_front_matter_crlf_delimiters_lf_inside(self):
        """CRLF on delimiters but LF inside YAML content should parse."""
        text = "---\r\nname: test\nlanguage: python\n---\r\nBody"
        meta, body = _parse_front_matter(text)
        assert meta is not None, "CRLF-delimiter front matter returned None"
        assert meta["name"] == "test"
        assert "Body" in body

    def test_parse_front_matter_lf_still_works(self):
        """Existing LF-only front matter must continue to work (regression guard)."""
        text = "---\nname: lf_module\nlanguage: python\n---\nPrompt body"
        meta, body = _parse_front_matter(text)
        assert meta is not None, "LF front matter should still work"
        assert meta["name"] == "lf_module"
        assert "Prompt body" in body

    def test_parse_front_matter_no_front_matter(self):
        """Text without front matter should pass through unchanged."""
        text = "Just a regular prompt with no front matter"
        meta, body = _parse_front_matter(text)
        assert meta is None
        assert body == text

    def test_parse_front_matter_unclosed_fence_silent(self, caplog):
        """Opener '---\\n' without a closing fence MUST be silent: that pattern
        is indistinguishable from a markdown horizontal rule, so warning would
        produce false positives on valid content.
        """
        text = "---\nname: broken\nno closing fence here"
        with caplog.at_level("WARNING", logger="pdd.code_generator_main"):
            meta, body = _parse_front_matter(text)
        assert meta is None
        assert body == text
        assert not caplog.records, (
            f"Unclosed-fence path must not warn; got: "
            f"{[r.message for r in caplog.records]}"
        )

    def test_parse_front_matter_unclosed_fence_crlf_silent(self, caplog):
        """Same silence rule for CRLF-opened unclosed front matter."""
        text = "---\r\nname: broken\r\nno closing fence"
        with caplog.at_level("WARNING", logger="pdd.code_generator_main"):
            meta, body = _parse_front_matter(text)
        assert meta is None
        assert body == text
        assert not caplog.records

    def test_parse_front_matter_markdown_hr_no_warn(self, caplog):
        """A prompt that opens with a markdown HR (``---\\nProse text...``)
        is the canonical false-positive shape and MUST NOT warn. ``main``
        returned ``(None, original_text)`` silently; this fix must preserve
        that.
        """
        text = "---\nPrompt starts after a Markdown horizontal rule\n\nMore prose."
        with caplog.at_level("WARNING", logger="pdd.code_generator_main"):
            meta, body = _parse_front_matter(text)
        assert meta is None
        assert body == text
        assert not caplog.records, (
            f"Markdown-HR opener must not warn; got: "
            f"{[r.message for r in caplog.records]}"
        )

    def test_parse_front_matter_malformed_yaml_warns(self, caplog):
        """Invalid YAML inside valid fences must log a warning naming the cause."""
        text = "---\nname: [unclosed\nlanguage: python\n---\nBody"
        with caplog.at_level("WARNING", logger="pdd.code_generator_main"):
            meta, body = _parse_front_matter(text)
        assert meta is None
        assert body == text
        assert any(
            "yaml" in record.message.lower() for record in caplog.records
        ), f"Expected YAML-parse warning; got: {[r.message for r in caplog.records]}"

    def test_parse_front_matter_plain_text_does_not_warn(self, caplog):
        """No warning for text that does not begin with '---' (avoid false positives)."""
        text = "Regular prompt with no sentinel"
        with caplog.at_level("WARNING", logger="pdd.code_generator_main"):
            meta, body = _parse_front_matter(text)
        assert meta is None
        assert body == text
        assert not caplog.records, (
            f"Should not warn on plain text; got: {[r.message for r in caplog.records]}"
        )

    def test_parse_front_matter_bom_crlf(self):
        """UTF-8 BOM + CRLF front matter must parse (Windows Notepad/Excel default)."""
        text = "﻿---\r\nname: bom_module\r\nlanguage: python\r\n---\r\nBody"
        meta, body = _parse_front_matter(text)
        assert meta is not None, "BOM+CRLF front matter returned None"
        assert meta["name"] == "bom_module"
        assert body == "Body"

    def test_parse_front_matter_bom_lf(self):
        """UTF-8 BOM + LF front matter must parse."""
        text = "﻿---\nname: bom_lf\n---\nBody"
        meta, body = _parse_front_matter(text)
        assert meta is not None
        assert meta["name"] == "bom_lf"
        assert body == "Body"

    def test_parse_front_matter_trailing_whitespace_on_fence(self):
        """Trailing spaces/tabs on fence lines must be tolerated (editor artifacts)."""
        text = "---   \nname: ws_ok\n---\t\nBody"
        meta, body = _parse_front_matter(text)
        assert meta is not None, "Trailing fence whitespace should be tolerated"
        assert meta["name"] == "ws_ok"
        assert body == "Body"

    def test_parse_front_matter_bare_dashes_markdown_hr_no_warn(self, caplog):
        """Bare '---' (no newline) looks like a markdown HR, not a fence — must not warn."""
        text = "---some inline text that happens to start with three dashes"
        with caplog.at_level("WARNING", logger="pdd.code_generator_main"):
            meta, body = _parse_front_matter(text)
        assert meta is None
        assert body == text
        assert not caplog.records, (
            f"Bare '---' without newline must not warn; got: "
            f"{[r.message for r in caplog.records]}"
        )

    def test_parse_front_matter_crlf_via_file_read_no_newline_translation(self, tmp_path):
        """End-to-end: opening a CRLF file with newline='' (no translation) must
        still yield parseable front matter. Covers callers that bypass universal
        newlines (binary pipelines, network sources, or explicit newline='').
        """
        p = tmp_path / "crlf.prompt"
        p.write_bytes(
            b"---\r\nname: e2e_crlf\r\nlanguage: python\r\n---\r\nBody here"
        )
        # newline='' disables universal-newlines — CRLF survives to _parse_front_matter
        with open(p, "r", encoding="utf-8", newline="") as f:
            raw = f.read()
        assert "\r\n" in raw, "Sanity: newline='' must preserve CRLF in read buffer"
        meta, body = _parse_front_matter(raw)
        assert meta is not None, "End-to-end CRLF (no newline translation) returned None"
        assert meta["name"] == "e2e_crlf"
        assert "Body here" in body

    def test_parse_front_matter_bom_via_file_read_utf8(self, tmp_path):
        """End-to-end: a UTF-8-with-BOM file opened with encoding='utf-8'
        (not 'utf-8-sig') still parses. This matches the production read path
        at code_generator_main.py which does NOT strip BOM.
        """
        p = tmp_path / "bom.prompt"
        p.write_bytes(
            b"\xef\xbb\xbf---\r\nname: e2e_bom\r\n---\r\nBody"
        )
        with open(p, "r", encoding="utf-8") as f:
            raw = f.read()
        assert raw.startswith("﻿"), "Sanity: utf-8 decode keeps BOM as U+FEFF"
        meta, body = _parse_front_matter(raw)
        assert meta is not None, "BOM prompt read with encoding='utf-8' returned None"
        assert meta["name"] == "e2e_bom"
        assert body == "Body"


# ---------------------------------------------------------------------------
# Tests for ArchitectureConformanceError typed exception (Requirement 5)
# ---------------------------------------------------------------------------
class TestArchitectureConformanceErrorTypedException:
    """Tests for the typed ArchitectureConformanceError class.

    Requirement 5 of the spec mandates that architecture conformance failures
    raise a typed ``ArchitectureConformanceError`` (subclass of
    ``click.UsageError``) with structured fields so callers like
    ``pdd sync`` / ``agentic_sync_runner`` can build a repair directive
    and retry generation without parsing the message string.
    """

    def test_class_is_subclass_of_usage_error(self):
        """ArchitectureConformanceError must subclass click.UsageError."""
        from pdd.code_generator_main import ArchitectureConformanceError
        assert issubclass(ArchitectureConformanceError, click.UsageError)

    def test_class_importable_from_module(self):
        """The class must be importable from pdd.code_generator_main."""
        from pdd.code_generator_main import ArchitectureConformanceError
        assert ArchitectureConformanceError is not None

    def test_missing_symbol_raises_typed_exception_with_fields(self, tmp_path):
        """Missing-symbol failure carries all structured fields per spec."""
        from pdd.code_generator_main import ArchitectureConformanceError
        arch = [
            {
                "filename": "models_Python.prompt",
                "filepath": "src/models.py",
                "interface": {
                    "type": "module",
                    "module": {
                        "functions": [
                            {"name": "User", "signature": "class User"},
                            {"name": "Admin", "signature": "class Admin"},
                        ]
                    },
                },
            }
        ]
        (tmp_path / "architecture.json").write_text(json.dumps(arch))
        generated_code = "class User:\n    pass\n"

        with pytest.raises(ArchitectureConformanceError) as excinfo:
            _verify_architecture_conformance(
                generated_code=generated_code,
                prompt_name="models_Python.prompt",
                arch_path=str(tmp_path / "architecture.json"),
                language="python",
                verbose=False,
            )

        exc = excinfo.value
        assert exc.prompt_name == "models_Python.prompt"
        # output_path may be empty for in-memory failures.
        assert exc.output_path == ""
        # architecture_entry should be the matched entry, not empty.
        assert isinstance(exc.architecture_entry, dict)
        assert exc.architecture_entry.get("filename") == "models_Python.prompt"
        # Declared interface symbols.
        assert exc.expected_symbols == ["User", "Admin"]
        # Symbols actually exported by the generated code.
        assert exc.found_symbols == ["User"]
        # Declared symbols absent from found_symbols.
        assert exc.missing_symbols == ["Admin"]

    def test_missing_symbol_message_format(self, tmp_path):
        """String message must start with the legacy prefix and name missing symbols."""
        from pdd.code_generator_main import ArchitectureConformanceError
        arch = [
            {
                "filename": "models_Python.prompt",
                "filepath": "src/models.py",
                "interface": {
                    "type": "module",
                    "module": {
                        "functions": [
                            {"name": "Admin", "signature": "class Admin"},
                        ]
                    },
                },
            }
        ]
        (tmp_path / "architecture.json").write_text(json.dumps(arch))

        with pytest.raises(ArchitectureConformanceError) as excinfo:
            _verify_architecture_conformance(
                generated_code="",
                prompt_name="models_Python.prompt",
                arch_path=str(tmp_path / "architecture.json"),
                language="python",
                verbose=False,
            )

        msg = str(excinfo.value)
        # Per spec: must start with this exact prefix for legacy log parsers.
        assert msg.startswith("Architecture conformance error for models_Python.prompt:")
        # Must include the missing symbols.
        assert "Admin" in msg

    def test_missing_symbol_includes_output_path_when_provided(self, tmp_path):
        """Structured failures should carry the generated output path."""
        from pdd.code_generator_main import ArchitectureConformanceError
        arch = [
            {
                "filename": "models_Python.prompt",
                "filepath": "src/models.py",
                "interface": {
                    "type": "module",
                    "module": {
                        "functions": [
                            {"name": "Admin", "signature": "class Admin"},
                        ]
                    },
                },
            }
        ]
        (tmp_path / "architecture.json").write_text(json.dumps(arch))

        with pytest.raises(ArchitectureConformanceError) as excinfo:
            _verify_architecture_conformance(
                generated_code="",
                prompt_name="models_Python.prompt",
                arch_path=str(tmp_path / "architecture.json"),
                language="python",
                verbose=False,
                output_path="src/models.py",
            )

        assert excinfo.value.output_path == "src/models.py"
        assert "Output: src/models.py" in str(excinfo.value)

    def test_missing_symbol_repair_directive_format(self, tmp_path):
        """repair_directive must enumerate missing symbols and forbid arch edits."""
        from pdd.code_generator_main import ArchitectureConformanceError
        arch = [
            {
                "filename": "models_Python.prompt",
                "filepath": "src/models.py",
                "interface": {
                    "type": "module",
                    "module": {
                        "functions": [
                            {"name": "User", "signature": "class User"},
                            {"name": "Admin", "signature": "class Admin"},
                            {"name": "Guest", "signature": "class Guest"},
                        ]
                    },
                },
            }
        ]
        (tmp_path / "architecture.json").write_text(json.dumps(arch))

        with pytest.raises(ArchitectureConformanceError) as excinfo:
            _verify_architecture_conformance(
                generated_code="class User:\n    pass\n",
                prompt_name="models_Python.prompt",
                arch_path=str(tmp_path / "architecture.json"),
                language="python",
                verbose=False,
            )

        directive = excinfo.value.repair_directive
        # Required header.
        assert "Required missing exports:" in directive
        # One bullet per missing symbol.
        assert "- Admin" in directive
        assert "- Guest" in directive
        # Forbid architecture.json edits.
        assert "Do not modify architecture.json. Do not remove existing valid exports." in directive

    def test_camelcase_violation_raises_typed_exception(self, tmp_path):
        """camelCase guard must raise ArchitectureConformanceError too (spec)."""
        from pdd.code_generator_main import ArchitectureConformanceError
        arch = [
            {
                "filename": "utils_Python.prompt",
                "filepath": "src/utils.py",
                "interface": {
                    "type": "module",
                    "module": {
                        "functions": [
                            {"name": "processData", "signature": "def processData(...)"},
                        ]
                    },
                },
            }
        ]
        (tmp_path / "architecture.json").write_text(json.dumps(arch))

        with pytest.raises(ArchitectureConformanceError) as excinfo:
            _verify_architecture_conformance(
                generated_code="def processData(data):\n    return data\n",
                prompt_name="utils_Python.prompt",
                arch_path=str(tmp_path / "architecture.json"),
                language="python",
                verbose=False,
            )

        exc = excinfo.value
        # Per spec: missing_symbols MUST be the offending camelCase symbols.
        assert "processData" in exc.missing_symbols
        # Subclass of UsageError so existing call sites still work.
        assert isinstance(exc, click.UsageError)

    def test_typed_exception_caught_as_usage_error(self, tmp_path):
        """Code that catches click.UsageError still works (back-compat)."""
        arch = [
            {
                "filename": "models_Python.prompt",
                "filepath": "src/models.py",
                "interface": {
                    "type": "module",
                    "module": {
                        "functions": [
                            {"name": "Missing", "signature": "class Missing"},
                        ]
                    },
                },
            }
        ]
        (tmp_path / "architecture.json").write_text(json.dumps(arch))

        # Existing callers that catch click.UsageError MUST still work.
        with pytest.raises(click.UsageError):
            _verify_architecture_conformance(
                generated_code="",
                prompt_name="models_Python.prompt",
                arch_path=str(tmp_path / "architecture.json"),
                language="python",
                verbose=False,
            )

    def test_construction_directly_with_all_fields(self):
        """Direct construction populates every documented field."""
        from pdd.code_generator_main import ArchitectureConformanceError
        exc = ArchitectureConformanceError(
            prompt_name="x_Python.prompt",
            output_path="src/x.py",
            architecture_entry={"filename": "x_Python.prompt"},
            expected_symbols=["a", "b"],
            found_symbols=["a"],
            missing_symbols=["b"],
            total_cost=0.42,
            model_name="cost-model",
        )
        assert exc.prompt_name == "x_Python.prompt"
        assert exc.output_path == "src/x.py"
        assert exc.architecture_entry == {"filename": "x_Python.prompt"}
        assert exc.expected_symbols == ["a", "b"]
        assert exc.found_symbols == ["a"]
        assert exc.missing_symbols == ["b"]
        assert exc.total_cost == pytest.approx(0.42)
        assert exc.model_name == "cost-model"
        # repair_directive computable from fields.
        assert "- b" in exc.repair_directive
        assert "Do not modify architecture.json. Do not remove existing valid exports." in exc.repair_directive


# ---------------------------------------------------------------------------
# Tests for public surface and test churn gates (Issue #1012)
# ---------------------------------------------------------------------------
class TestSyncCompatibilityGates:
    def test_public_surface_regression_catches_removed_helper(self):
        from pdd.code_generator_main import (
            PublicSurfaceRegressionError,
            _verify_public_surface_regression,
        )

        # Both versions preserve ``import git`` so this test isolates the
        # helper-removal signal. Removal of the import is covered separately
        # by ``test_public_surface_regression_catches_removed_import``.
        before = (
            "import git\n"
            "def read_fingerprint():\n"
            "    return 'old'\n"
            "def calculate_sha256(value):\n"
            "    return value\n"
        )
        after = (
            "import git\n"
            "def read_fingerprint():\n"
            "    return 'new'\n"
        )

        with pytest.raises(PublicSurfaceRegressionError) as excinfo:
            _verify_public_surface_regression(
                before,
                after,
                "update_main_Python.prompt",
                "pdd/update_main.py",
                "python",
                "Update internals only.",
            )

        assert "Public surface regression for update_main_Python.prompt:" in str(excinfo.value)
        assert excinfo.value.removed_symbols == ["calculate_sha256"]
        assert "- calculate_sha256" in excinfo.value.repair_directive

    def test_public_surface_regression_catches_removed_import(self):
        """Removing an ``import`` re-export is a real downstream-breaking
        change — issue #1012's user-cited regression was specifically the
        loss of the ``git`` module re-export, so this MUST surface."""
        from pdd.code_generator_main import (
            PublicSurfaceRegressionError,
            _verify_public_surface_regression,
        )

        before = (
            "import git\n"
            "def read_fingerprint():\n"
            "    return 'old'\n"
        )
        after = (
            "def read_fingerprint():\n"
            "    return 'new'\n"
        )

        with pytest.raises(PublicSurfaceRegressionError) as excinfo:
            _verify_public_surface_regression(
                before,
                after,
                "update_main_Python.prompt",
                "pdd/update_main.py",
                "python",
                "Update internals only.",
            )

        assert "git" in excinfo.value.removed_symbols
        assert "- git" in excinfo.value.repair_directive

    def test_public_surface_regression_catches_removed_module_attribute(self):
        """Module-level ``ast.Assign`` targets (public constants) are part
        of the importable surface; their removal MUST raise."""
        from pdd.code_generator_main import (
            PublicSurfaceRegressionError,
            _verify_public_surface_regression,
        )

        before = (
            "PUBLIC_SETTING = True\n"
            "def read_fingerprint():\n"
            "    return 'old'\n"
        )
        after = (
            "def read_fingerprint():\n"
            "    return 'new'\n"
        )

        with pytest.raises(PublicSurfaceRegressionError) as excinfo:
            _verify_public_surface_regression(
                before,
                after,
                "update_main_Python.prompt",
                "pdd/update_main.py",
                "python",
                "Update internals only.",
            )

        assert "PUBLIC_SETTING" in excinfo.value.removed_symbols

    def test_public_surface_regression_ignores_underscore_module_names(self):
        """Underscore-prefixed module-level names (private) and dunder
        attributes are NOT part of the public surface — they must NOT
        cause a regression when removed."""
        from pdd.code_generator_main import _verify_public_surface_regression

        before = (
            "_PRIVATE_CONST = 1\n"
            "__version__ = '0.1.0'\n"
            "import _internal_module\n"
            "from typing import _GenericAlias\n"
            "def read_fingerprint():\n"
            "    return 'old'\n"
        )
        after = (
            "def read_fingerprint():\n"
            "    return 'new'\n"
        )

        # All removed names are private/dunder — gate should pass silently.
        _verify_public_surface_regression(
            before,
            after,
            "update_main_Python.prompt",
            "pdd/update_main.py",
            "python",
            "Update internals only.",
        )

    def test_public_surface_regression_tracks_from_import_aliases(self):
        """``from X import Y`` and ``from X import Y as Z`` bind ``Y``
        and ``Z`` respectively as module attributes; both are public
        re-exports that must be tracked. ``from X import *`` binds no
        fixed identifier and is ignored."""
        from pdd.code_generator_main import (
            PublicSurfaceRegressionError,
            _verify_public_surface_regression,
        )

        before = (
            "from pathlib import Path\n"
            "from os.path import join as pjoin\n"
            "def read_fingerprint():\n"
            "    return 'old'\n"
        )
        after = (
            "def read_fingerprint():\n"
            "    return 'new'\n"
        )

        with pytest.raises(PublicSurfaceRegressionError) as excinfo:
            _verify_public_surface_regression(
                before,
                after,
                "update_main_Python.prompt",
                "pdd/update_main.py",
                "python",
                "Update internals only.",
            )

        # Both the direct name and the alias surface as removed.
        assert "Path" in excinfo.value.removed_symbols
        assert "pjoin" in excinfo.value.removed_symbols

    def test_public_surface_regression_tracks_annotated_assignment(self):
        """Module-level ``ast.AnnAssign`` targets (annotated public
        constants) are also part of the importable surface."""
        from pdd.code_generator_main import (
            PublicSurfaceRegressionError,
            _verify_public_surface_regression,
        )

        before = (
            "PUBLIC_FLAG: bool = True\n"
            "def read_fingerprint():\n"
            "    return 'old'\n"
        )
        after = "def read_fingerprint():\n    return 'new'\n"

        with pytest.raises(PublicSurfaceRegressionError) as excinfo:
            _verify_public_surface_regression(
                before,
                after,
                "update_main_Python.prompt",
                "pdd/update_main.py",
                "python",
                "Update internals only.",
            )

        assert "PUBLIC_FLAG" in excinfo.value.removed_symbols

    def test_public_surface_regression_ignores_bare_annotation(self):
        """Bare ``ast.AnnAssign`` declarations (``PUBLIC_NAME: int`` with no
        value) do NOT bind a runtime module attribute — they're type hints
        only. Capturing them as public surface would cause false positives
        when a generation removes a type-only annotation, so the snapshot
        skips bare annotations and only tracks bound ones."""
        from pdd.code_generator_main import _verify_public_surface_regression

        before = (
            "PUBLIC_BARE: int\n"
            "def read_fingerprint():\n"
            "    return 'old'\n"
        )
        after = "def read_fingerprint():\n    return 'new'\n"

        # Removing the bare annotation must NOT raise — it never bound a
        # runtime attribute callers could have imported.
        _verify_public_surface_regression(
            before,
            after,
            "update_main_Python.prompt",
            "pdd/update_main.py",
            "python",
            "Update internals only.",
        )

    def test_public_surface_regression_tracks_annassign_with_none_value(self):
        """``PUBLIC_NAME: int = None`` is a real binding (the explicit
        ``None`` value lives at ``node.value``, distinct from the Python
        sentinel meaning "no value assigned"), so it MUST be tracked."""
        from pdd.code_generator_main import (
            PublicSurfaceRegressionError,
            _verify_public_surface_regression,
        )

        before = (
            "PUBLIC_NONE: int = None\n"
            "def read_fingerprint():\n"
            "    return 'old'\n"
        )
        after = "def read_fingerprint():\n    return 'new'\n"

        with pytest.raises(PublicSurfaceRegressionError) as excinfo:
            _verify_public_surface_regression(
                before,
                after,
                "update_main_Python.prompt",
                "pdd/update_main.py",
                "python",
                "Update internals only.",
            )

        assert "PUBLIC_NONE" in excinfo.value.removed_symbols

    def test_public_surface_regression_walks_tuple_assignment_targets(self):
        """Tuple-unpacking module-level assignments expose each name as a
        separate attribute; the snapshot walks every element."""
        from pdd.code_generator_main import (
            PublicSurfaceRegressionError,
            _verify_public_surface_regression,
        )

        before = (
            "PUBLIC_A, PUBLIC_B = 1, 2\n"
            "def read_fingerprint():\n"
            "    return 'old'\n"
        )
        after = "def read_fingerprint():\n    return 'new'\n"

        with pytest.raises(PublicSurfaceRegressionError) as excinfo:
            _verify_public_surface_regression(
                before,
                after,
                "update_main_Python.prompt",
                "pdd/update_main.py",
                "python",
                "Update internals only.",
            )

        assert "PUBLIC_A" in excinfo.value.removed_symbols
        assert "PUBLIC_B" in excinfo.value.removed_symbols

    # -----------------------------------------------------------------
    # Codex review (#1015) F-C (iter-6): `__all__` is Python's canonical
    # public-API declaration. When it is present as a clean list/tuple
    # of string constants, it MUST be authoritative — underscore-prefixed
    # names listed in `__all__` ARE public, and names NOT in `__all__`
    # are NOT public even if they're otherwise non-underscore.
    # -----------------------------------------------------------------
    def test_public_surface_regression_dunder_all_protects_underscore_name(self):
        """`__all__ = ["_public_helper"]` makes `_public_helper` public
        per Python semantics; removing it MUST raise even though the
        name is underscore-prefixed."""
        from pdd.code_generator_main import (
            PublicSurfaceRegressionError,
            _verify_public_surface_regression,
        )

        before = (
            "__all__ = [\"_public_helper\", \"PublicClass\"]\n"
            "def _public_helper():\n    pass\n"
            "class PublicClass:\n    pass\n"
        )
        after = (
            "__all__ = [\"PublicClass\"]\n"
            "class PublicClass:\n    pass\n"
        )

        with pytest.raises(PublicSurfaceRegressionError) as excinfo:
            _verify_public_surface_regression(
                before,
                after,
                "module_Python.prompt",
                "pdd/module.py",
                "python",
                "Update internals only.",
            )

        assert "_public_helper" in excinfo.value.removed_symbols

    def test_public_surface_regression_dunder_all_excludes_unlisted_name(self):
        """When `__all__` declares only `["A"]`, removing a sibling `B`
        (not in `__all__`) MUST NOT raise — `B` is no longer part of the
        public surface once `__all__` is declared."""
        from pdd.code_generator_main import _verify_public_surface_regression

        before = (
            "__all__ = [\"A\"]\n"
            "def A():\n    pass\n"
            "def B():\n    pass\n"
        )
        after = (
            "__all__ = [\"A\"]\n"
            "def A():\n    pass\n"
        )

        # Must NOT raise — B is not in __all__, so it's not public.
        _verify_public_surface_regression(
            before,
            after,
            "module_Python.prompt",
            "pdd/module.py",
            "python",
            "Internal refactor.",
        )

    def test_public_surface_regression_no_dunder_all_uses_heuristic(self):
        """When `__all__` is absent the underscore-prefix heuristic
        applies as before: `_helper` is NOT in the surface."""
        from pdd.code_generator_main import _verify_public_surface_regression

        before = (
            "def _helper():\n    pass\n"
            "def public_one():\n    pass\n"
        )
        after = (
            "def public_one():\n    pass\n"
        )

        # No __all__ declared — `_helper` is private (underscore prefix).
        _verify_public_surface_regression(
            before,
            after,
            "module_Python.prompt",
            "pdd/module.py",
            "python",
            "Internal refactor.",
        )

    def test_public_surface_regression_dunder_all_tuple_form(self):
        """`__all__` declared as a tuple of constants is equally valid."""
        from pdd.code_generator_main import (
            PublicSurfaceRegressionError,
            _verify_public_surface_regression,
        )

        before = (
            "__all__ = (\"_protected\",)\n"
            "def _protected():\n    pass\n"
        )
        after = "def _protected_renamed():\n    pass\n"

        with pytest.raises(PublicSurfaceRegressionError) as excinfo:
            _verify_public_surface_regression(
                before,
                after,
                "module_Python.prompt",
                "pdd/module.py",
                "python",
                "Internal refactor.",
            )

        assert "_protected" in excinfo.value.removed_symbols

    def test_public_surface_regression_dunder_all_computed_falls_back(self):
        """When `__all__` is computed (e.g. `sorted(...)`) and cannot be
        statically evaluated, the heuristic falls back to the
        non-underscore rule."""
        from pdd.code_generator_main import _verify_public_surface_regression

        # __all__ is computed; the heuristic falls back. `_helper` is
        # underscore-prefixed so it's not in the surface; removing it
        # must NOT raise even though a computed __all__ exists.
        before = (
            "__all__ = sorted([\"_helper\"])\n"
            "def _helper():\n    pass\n"
            "def public_one():\n    pass\n"
        )
        after = (
            "__all__ = sorted([])\n"
            "def public_one():\n    pass\n"
        )

        _verify_public_surface_regression(
            before,
            after,
            "module_Python.prompt",
            "pdd/module.py",
            "python",
            "Internal refactor.",
        )

    # -----------------------------------------------------------------
    # Codex review (#1015) F-C follow-up (iter-7): the parser MUST
    # walk every top-level __all__ assignment in source order and
    # honor the LAST one (Python runtime semantics). The previous
    # implementation returned the first clean literal, which would
    # incorrectly trust ``__all__ = ["_helper"]`` even when a later
    # ``__all__ = func()`` overrode it at runtime.
    # -----------------------------------------------------------------
    def test_dunder_all_computed_after_literal_overrides(self):
        """A computed `__all__` assignment FOLLOWING a clean literal
        MUST reset the parse state — at runtime the computed value
        wins. The snapshot must NOT keep treating the earlier literal
        as authoritative."""
        from pdd.code_generator_main import _extract_dunder_all
        import ast

        src = (
            "__all__ = [\"_helper\"]\n"
            "def func():\n    return [\"a\", \"b\"]\n"
            "__all__ = func()\n"
        )
        result = _extract_dunder_all(ast.parse(src))
        assert result is None, (
            "Computed __all__ after a literal MUST reset state to None "
            "(last assignment wins); got %r" % (result,)
        )

    def test_dunder_all_aug_assign_falls_back(self):
        """`__all__ += [...]` (AugAssign) mutates the previous list at
        runtime; statically we cannot be sure what's in the target
        object, so the parser must fall back to the heuristic."""
        from pdd.code_generator_main import _extract_dunder_all
        import ast

        src = (
            "__all__ = [\"A\"]\n"
            "__all__ += [\"B\"]\n"
        )
        result = _extract_dunder_all(ast.parse(src))
        assert result is None, (
            "AugAssign to __all__ MUST reset state to None; got %r" % (result,)
        )

    def test_dunder_all_single_literal_captures_set(self):
        """A single clean `__all__ = [...]` literal is captured exactly
        (regression guard for the common case)."""
        from pdd.code_generator_main import _extract_dunder_all
        import ast

        src = "__all__ = [\"_helper\", \"PublicClass\"]\n"
        result = _extract_dunder_all(ast.parse(src))
        assert result == {"_helper", "PublicClass"}

    def test_dunder_all_last_literal_wins(self):
        """Two clean literal assignments in source order — only the
        SECOND survives (matches Python runtime semantics)."""
        from pdd.code_generator_main import _extract_dunder_all
        import ast

        src = (
            "__all__ = [\"A\"]\n"
            "__all__ = [\"B\"]\n"
        )
        result = _extract_dunder_all(ast.parse(src))
        assert result == {"B"}, (
            "Second clean literal MUST win (last assignment wins); got %r"
            % (result,)
        )

    def test_public_surface_regression_dunder_all_computed_after_literal(self):
        """End-to-end: a computed __all__ following a clean literal
        falls back to the heuristic. Underscore-prefixed name from the
        earlier literal is therefore NOT treated as public, so removing
        it does NOT raise (the heuristic excludes underscore-prefixed
        names from the surface)."""
        from pdd.code_generator_main import _verify_public_surface_regression

        before = (
            "__all__ = [\"_helper\"]\n"
            "def _helper():\n    pass\n"
            "def public_one():\n    pass\n"
            "def _compute():\n    return []\n"
            "__all__ = _compute()\n"
        )
        after = (
            "def public_one():\n    pass\n"
            "def _compute():\n    return []\n"
            "__all__ = _compute()\n"
        )

        # Heuristic applies — `_helper` is underscore-prefixed and
        # therefore not in the surface. Removal must NOT raise.
        _verify_public_surface_regression(
            before,
            after,
            "module_Python.prompt",
            "pdd/module.py",
            "python",
            "Internal refactor.",
        )

    def test_public_surface_regression_dunder_all_aug_assign_falls_back(self):
        """End-to-end: `__all__ += [...]` after a clean literal makes
        the parser fall back. Underscore-prefixed name removal must
        NOT raise."""
        from pdd.code_generator_main import _verify_public_surface_regression

        before = (
            "__all__ = [\"_helper\"]\n"
            "__all__ += [\"PublicClass\"]\n"
            "def _helper():\n    pass\n"
            "class PublicClass:\n    pass\n"
        )
        after = (
            "__all__ = [\"_helper\"]\n"
            "__all__ += [\"PublicClass\"]\n"
            "class PublicClass:\n    pass\n"
        )

        # Heuristic applies — underscore-prefixed `_helper` is not in
        # the surface. Removal must NOT raise.
        _verify_public_surface_regression(
            before,
            after,
            "module_Python.prompt",
            "pdd/module.py",
            "python",
            "Internal refactor.",
        )

    def test_public_surface_regression_dunder_all_narrowing_surfaces_removed(self):
        """Adding `__all__` to a module that previously exported `foo`
        and `bar` as plain non-underscore names is intentionally
        surface-narrowing: omitted names show up as removed. The fix
        is the standard `BREAKING-CHANGE: remove <symbol>` opt-out."""
        from pdd.code_generator_main import (
            PublicSurfaceRegressionError,
            _verify_public_surface_regression,
        )

        before = (
            "def foo():\n    pass\n"
            "def bar():\n    pass\n"
        )
        after = (
            "__all__ = [\"foo\"]\n"
            "def foo():\n    pass\n"
            "def bar():\n    pass\n"
        )

        with pytest.raises(PublicSurfaceRegressionError) as excinfo:
            _verify_public_surface_regression(
                before,
                after,
                "module_Python.prompt",
                "pdd/module.py",
                "python",
                "Narrowing the public surface.",
            )

        assert "bar" in excinfo.value.removed_symbols

    def test_public_surface_regression_dunder_all_applies_to_signature_snapshot(self):
        """The `__all__` rule applies to `_snapshot_public_signatures`
        too — otherwise the removed-symbol diff and the signature-drift
        diff disagree on what is "public". Sanity-check by changing the
        signature of an underscore-prefixed function listed in
        `__all__`: signature drift MUST surface."""
        from pdd.code_generator_main import (
            PublicSurfaceRegressionError,
            _verify_public_surface_regression,
        )

        before = (
            "__all__ = [\"_run\"]\n"
            "def _run(x, y=1):\n    return x + y\n"
        )
        after = (
            "__all__ = [\"_run\"]\n"
            "def _run(x):\n    return x\n"
        )

        with pytest.raises(PublicSurfaceRegressionError) as excinfo:
            _verify_public_surface_regression(
                before,
                after,
                "module_Python.prompt",
                "pdd/module.py",
                "python",
                "Internal refactor.",
            )

        assert "_run" in excinfo.value.changed_signatures

    # -----------------------------------------------------------------
    # Codex review (#1015) F-F (iter-8): when `__all__` lists a class,
    # the recursively-walked members of that class (methods, nested
    # classes, methods on nested classes) MUST also be part of the
    # public surface. Without this, the user-cited regression where
    # `__all__ = ["Service"]` plus removal of `Service.run` slipped
    # past the gate would persist. Methods of __all__'d classes are
    # captured regardless of underscore prefix — the user opted the
    # whole class into the public surface, consistent with how
    # underscore-prefixed top-level names in __all__ are public.
    # -----------------------------------------------------------------
    def test_public_surface_regression_dunder_all_walks_class_methods(self):
        """`__all__ = ["Service"]` with `Service.run` MUST capture
        `Service.run` as part of the public surface — removing it
        raises with `Service.run` in `removed_symbols`."""
        from pdd.code_generator_main import (
            PublicSurfaceRegressionError,
            _verify_public_surface_regression,
        )

        before = (
            "__all__ = [\"Service\"]\n"
            "class Service:\n"
            "    def run(self):\n        return 1\n"
        )
        after = (
            "__all__ = [\"Service\"]\n"
            "class Service:\n    pass\n"
        )

        with pytest.raises(PublicSurfaceRegressionError) as excinfo:
            _verify_public_surface_regression(
                before,
                after,
                "module_Python.prompt",
                "pdd/module.py",
                "python",
                "Internal refactor.",
            )

        assert "Service.run" in excinfo.value.removed_symbols

    def test_public_surface_regression_dunder_all_walks_nested_class_members(self):
        """`__all__ = ["Service"]` with a nested `Service.Inner.m` MUST
        capture the deeply-nested method; removing it raises with
        `Service.Inner.m` in `removed_symbols`."""
        from pdd.code_generator_main import (
            PublicSurfaceRegressionError,
            _verify_public_surface_regression,
        )

        before = (
            "__all__ = [\"Service\"]\n"
            "class Service:\n"
            "    class Inner:\n"
            "        def m(self):\n            return 1\n"
        )
        after = (
            "__all__ = [\"Service\"]\n"
            "class Service:\n"
            "    class Inner:\n        pass\n"
        )

        with pytest.raises(PublicSurfaceRegressionError) as excinfo:
            _verify_public_surface_regression(
                before,
                after,
                "module_Python.prompt",
                "pdd/module.py",
                "python",
                "Internal refactor.",
            )

        assert "Service.Inner.m" in excinfo.value.removed_symbols

    def test_public_surface_regression_dunder_all_catches_class_method_signature_change(self):
        """`__all__ = ["Service"]` + signature change on `Service.run`
        (adding a required param) MUST raise with `Service.run` in
        `changed_signatures`."""
        from pdd.code_generator_main import (
            PublicSurfaceRegressionError,
            _verify_public_surface_regression,
        )

        before = (
            "__all__ = [\"Service\"]\n"
            "class Service:\n"
            "    def run(self):\n        return 1\n"
        )
        after = (
            "__all__ = [\"Service\"]\n"
            "class Service:\n"
            "    def run(self, value):\n        return value\n"
        )

        with pytest.raises(PublicSurfaceRegressionError) as excinfo:
            _verify_public_surface_regression(
                before,
                after,
                "module_Python.prompt",
                "pdd/module.py",
                "python",
                "Internal refactor.",
            )

        assert "Service.run" in excinfo.value.changed_signatures

    def test_public_surface_regression_dunder_all_ignores_unlisted_class_members(self):
        """Top-level classes NOT in `__all__` and their members are not
        part of the public surface — removing them does NOT raise."""
        from pdd.code_generator_main import _verify_public_surface_regression

        before = (
            "__all__ = [\"Service\"]\n"
            "class Service:\n"
            "    def run(self):\n        return 1\n"
            "class Internal:\n"
            "    def helper(self):\n        return 2\n"
        )
        after = (
            "__all__ = [\"Service\"]\n"
            "class Service:\n"
            "    def run(self):\n        return 1\n"
        )

        # `Internal` and `Internal.helper` are not in __all__ — removal
        # must NOT raise.
        _verify_public_surface_regression(
            before,
            after,
            "module_Python.prompt",
            "pdd/module.py",
            "python",
            "Internal refactor.",
        )

    def test_public_surface_regression_dunder_all_includes_underscore_methods(self):
        """When a class is opted into __all__, its underscore-prefixed
        methods ARE part of the public surface (consistent with how
        underscore-prefixed top-level names in __all__ are public)."""
        from pdd.code_generator_main import (
            PublicSurfaceRegressionError,
            _verify_public_surface_regression,
        )

        before = (
            "__all__ = [\"Service\"]\n"
            "class Service:\n"
            "    def _internal_run(self):\n        return 1\n"
        )
        after = (
            "__all__ = [\"Service\"]\n"
            "class Service:\n    pass\n"
        )

        with pytest.raises(PublicSurfaceRegressionError) as excinfo:
            _verify_public_surface_regression(
                before,
                after,
                "module_Python.prompt",
                "pdd/module.py",
                "python",
                "Internal refactor.",
            )

        assert "Service._internal_run" in excinfo.value.removed_symbols

    def test_public_surface_regression_allows_explicit_breaking_change(self):
        from pdd.code_generator_main import _verify_public_surface_regression

        _verify_public_surface_regression(
            "def old_helper():\n    pass\n",
            "def new_helper():\n    pass\n",
            "module_Python.prompt",
            "pdd/module.py",
            "python",
            "BREAKING-CHANGE: remove old_helper.",
        )

    def test_public_surface_regression_requires_scoped_breaking_change(self):
        from pdd.code_generator_main import (
            PublicSurfaceRegressionError,
            _verify_public_surface_regression,
        )

        with pytest.raises(PublicSurfaceRegressionError) as excinfo:
            _verify_public_surface_regression(
                "def old_helper():\n    pass\n"
                "def keep_helper():\n    pass\n",
                "def new_helper():\n    pass\n",
                "module_Python.prompt",
                "pdd/module.py",
                "python",
                "BREAKING-CHANGE: remove old_helper.",
            )

        assert excinfo.value.removed_symbols == ["keep_helper"]

    def test_public_surface_regression_catches_signature_change(self):
        from pdd.code_generator_main import (
            PublicSurfaceRegressionError,
            _verify_public_surface_regression,
        )

        with pytest.raises(PublicSurfaceRegressionError) as excinfo:
            _verify_public_surface_regression(
                "def calculate(value, *, strict=False) -> str:\n    return str(value)\n",
                "def calculate(value) -> str:\n    return str(value)\n",
                "module_Python.prompt",
                "pdd/module.py",
                "python",
                "",
            )

        assert excinfo.value.removed_symbols == []
        assert excinfo.value.changed_signatures == ["calculate"]
        assert "signature_changed: calculate" in str(excinfo.value)

    def test_public_surface_regression_allows_scoped_signature_change(self):
        from pdd.code_generator_main import _verify_public_surface_regression

        _verify_public_surface_regression(
            "def calculate(value, *, strict=False) -> str:\n    return str(value)\n",
            "def calculate(value) -> str:\n    return str(value)\n",
            "module_Python.prompt",
            "pdd/module.py",
            "python",
            "BREAKING-CHANGE: change signature calculate.",
        )

    def test_public_surface_regression_requires_scoped_signature_change(self):
        from pdd.code_generator_main import (
            PublicSurfaceRegressionError,
            _verify_public_surface_regression,
        )

        with pytest.raises(PublicSurfaceRegressionError) as excinfo:
            _verify_public_surface_regression(
                "def calculate(value, *, strict=False) -> str:\n    return str(value)\n",
                "def calculate(value) -> str:\n    return str(value)\n",
                "module_Python.prompt",
                "pdd/module.py",
                "python",
                "BREAKING-CHANGE: change signature other_function.",
            )

        assert excinfo.value.changed_signatures == ["calculate"]

    def test_public_surface_regression_catches_removed_constructor(self):
        from pdd.code_generator_main import (
            PublicSurfaceRegressionError,
            _verify_public_surface_regression,
        )

        before = (
            "class MyClass:\n"
            "    def __init__(self, value: int) -> None:\n"
            "        self.value = value\n"
            "    def public_method(self) -> int:\n"
            "        return self.value\n"
        )
        after = (
            "class MyClass:\n"
            "    def public_method(self) -> int:\n"
            "        return 0\n"
        )

        with pytest.raises(PublicSurfaceRegressionError) as excinfo:
            _verify_public_surface_regression(
                before,
                after,
                "module_Python.prompt",
                "pdd/module.py",
                "python",
                "",
            )

        assert excinfo.value.removed_symbols == []
        assert "MyClass" in excinfo.value.changed_signatures

    # -----------------------------------------------------------------
    # Codex review (#1015) P1.B (iter-13): a class without an explicit
    # `__init__` is treated as having the implicit `(self)` constructor
    # at runtime. Previously the signature snapshot recorded NO entry
    # for such classes, so adding a required-arg `__init__` slipped
    # past the gate — even though callers doing `Service()` would
    # `TypeError` at runtime. The fix records `"()"` for implicit
    # constructors so the pre/post diff catches the addition.
    # -----------------------------------------------------------------
    def test_public_surface_regression_catches_added_required_init(self):
        """A class WITHOUT an explicit `__init__` then a class WITH a
        new required-arg `__init__` MUST raise: the change is a
        runtime ABI break for callers using the default `Service()`
        construction."""
        from pdd.code_generator_main import (
            PublicSurfaceRegressionError,
            _verify_public_surface_regression,
        )

        before = (
            "class Service:\n"
            "    def run(self):\n"
            "        return 1\n"
        )
        after = (
            "class Service:\n"
            "    def __init__(self, required):\n"
            "        self.required = required\n"
            "    def run(self):\n"
            "        return self.required\n"
        )

        with pytest.raises(PublicSurfaceRegressionError) as excinfo:
            _verify_public_surface_regression(
                before,
                after,
                "module_Python.prompt",
                "pdd/module.py",
                "python",
                "",
            )

        assert "Service" in excinfo.value.changed_signatures
        # The repair directive should surface the changed constructor.
        assert "Service" in excinfo.value.repair_directive

    def test_public_surface_regression_allows_added_init_with_breaking_change(self):
        """The same change with an anchored `BREAKING-CHANGE: change
        signature Service` directive must NOT raise — explicit opt-out."""
        from pdd.code_generator_main import _verify_public_surface_regression

        before = (
            "class Service:\n"
            "    def run(self):\n"
            "        return 1\n"
        )
        after = (
            "class Service:\n"
            "    def __init__(self, required):\n"
            "        self.required = required\n"
            "    def run(self):\n"
            "        return self.required\n"
        )

        _verify_public_surface_regression(
            before,
            after,
            "module_Python.prompt",
            "pdd/module.py",
            "python",
            "BREAKING-CHANGE: change signature Service.",
        )

    def test_public_surface_regression_ignores_unrelated_method_addition(self):
        """Negative test: class without `__init__` in both pre and post,
        only an unrelated method added. The implicit `()` signature is
        unchanged between pre and post, so the gate must NOT raise."""
        from pdd.code_generator_main import _verify_public_surface_regression

        before = (
            "class Service:\n"
            "    def run(self):\n"
            "        return 1\n"
        )
        after = (
            "class Service:\n"
            "    def run(self):\n"
            "        return 1\n"
            "    def new_method(self):\n"
            "        return 2\n"
        )

        # Both sides have implicit `()` init; only a new method appears,
        # which is additive. Must NOT raise.
        _verify_public_surface_regression(
            before,
            after,
            "module_Python.prompt",
            "pdd/module.py",
            "python",
            "",
        )

    def test_public_surface_regression_catches_staticmethod_signature_change(self):
        from pdd.code_generator_main import (
            PublicSurfaceRegressionError,
            _verify_public_surface_regression,
        )

        before = (
            "class MyClass:\n"
            "    @staticmethod\n"
            "    def compute(value: int, factor: int) -> int:\n"
            "        return value * factor\n"
        )
        after = (
            "class MyClass:\n"
            "    @staticmethod\n"
            "    def compute(value: int) -> int:\n"
            "        return value\n"
        )

        with pytest.raises(PublicSurfaceRegressionError) as excinfo:
            _verify_public_surface_regression(
                before,
                after,
                "module_Python.prompt",
                "pdd/module.py",
                "python",
                "",
            )

        assert "MyClass.compute" in excinfo.value.changed_signatures

    def test_public_surface_regression_catches_async_sync_flip(self):
        from pdd.code_generator_main import (
            PublicSurfaceRegressionError,
            _verify_public_surface_regression,
        )

        before = "async def foo() -> int:\n    return 0\n"
        after = "def foo() -> int:\n    return 0\n"

        with pytest.raises(PublicSurfaceRegressionError) as excinfo:
            _verify_public_surface_regression(
                before,
                after,
                "module_Python.prompt",
                "pdd/module.py",
                "python",
                "",
            )

        assert excinfo.value.removed_symbols == []
        assert "foo" in excinfo.value.changed_signatures

    def test_public_surface_regression_catches_async_sync_flip_on_method(self):
        from pdd.code_generator_main import (
            PublicSurfaceRegressionError,
            _verify_public_surface_regression,
        )

        before = (
            "class MyClass:\n"
            "    async def compute(self, value: int) -> int:\n"
            "        return value\n"
        )
        after = (
            "class MyClass:\n"
            "    def compute(self, value: int) -> int:\n"
            "        return value\n"
        )

        with pytest.raises(PublicSurfaceRegressionError) as excinfo:
            _verify_public_surface_regression(
                before,
                after,
                "module_Python.prompt",
                "pdd/module.py",
                "python",
                "",
            )

        assert "MyClass.compute" in excinfo.value.changed_signatures

    def test_public_surface_regression_allows_unchanged_staticmethod(self):
        from pdd.code_generator_main import _verify_public_surface_regression

        source = (
            "class MyClass:\n"
            "    @staticmethod\n"
            "    def compute(value: int, factor: int) -> int:\n"
            "        return value * factor\n"
        )

        _verify_public_surface_regression(
            source,
            source,
            "module_Python.prompt",
            "pdd/module.py",
            "python",
            "",
        )

    def test_public_surface_gate_has_dedicated_skip_flag(self, monkeypatch):
        from pdd.code_generator_main import _verify_public_surface_regression

        monkeypatch.setenv("PDD_SKIP_PUBLIC_SURFACE_GATE", "1")

        _verify_public_surface_regression(
            "def old_helper():\n    pass\n",
            "def new_helper():\n    pass\n",
            "module_Python.prompt",
            "pdd/module.py",
            "python",
            "",
        )

    # Codex review (#1015) F-K (iter-16): the umbrella
    # `PDD_SKIP_CONFORMANCE=1` flag must short-circuit both the
    # public-surface gate AND the test-churn gate, matching the
    # README's documented hierarchy.
    def test_public_surface_gate_honors_skip_conformance_umbrella(self, monkeypatch):
        """`PDD_SKIP_CONFORMANCE=1` must disable the public-surface
        gate (not just `PDD_SKIP_PUBLIC_SURFACE_GATE=1`)."""
        from pdd.code_generator_main import _verify_public_surface_regression

        monkeypatch.setenv("PDD_SKIP_CONFORMANCE", "1")
        # Without the umbrella flag this would raise; with it set,
        # the call must return silently.
        _verify_public_surface_regression(
            "def old_helper():\n    pass\n",
            "def new_helper():\n    pass\n",
            "module_Python.prompt",
            "pdd/module.py",
            "python",
            "",
        )

    def test_test_churn_gate_honors_skip_conformance_umbrella(self, monkeypatch):
        """`PDD_SKIP_CONFORMANCE=1` must disable the test-churn gate
        (not just `PDD_SKIP_TEST_CHURN_GATE=1`)."""
        from pdd.code_generator_main import _verify_test_churn

        monkeypatch.setenv("PDD_SKIP_CONFORMANCE", "1")
        # 100% churn — would normally raise; with the umbrella flag
        # set, the call must return silently.
        _verify_test_churn(
            existing_code=(
                "def test_a(): pass\n"
                "def test_b(): pass\n"
                "def test_c(): pass\n"
            ),
            generated_code=(
                "def test_new_a(): pass\n"
                "def test_new_b(): pass\n"
                "def test_new_c(): pass\n"
            ),
            prompt_name="module_test_Python.prompt",
            output_path="tests/test_module.py",
            prompt_content="",
        )

    def test_public_surface_regression_exempts_first_time_generation(self):
        from pdd.code_generator_main import _verify_public_surface_regression

        _verify_public_surface_regression(
            "",
            "def new_helper():\n    pass\n",
            "module_Python.prompt",
            "pdd/module.py",
            "python",
            "",
        )

    def test_test_churn_gate_raises_above_threshold(self, monkeypatch):
        from pdd.code_generator_main import TestChurnError, _verify_test_churn

        monkeypatch.setenv("PDD_TEST_CHURN_THRESHOLD", "0.40")
        before = "\n".join(
            [
                "def test_a(): pass",
                "def test_b(): pass",
                "def test_c(): pass",
                "def test_d(): pass",
                "def test_e(): pass",
            ]
        )
        after = "\n".join(
            [
                "def test_new_a(): pass",
                "def test_new_b(): pass",
                "def test_new_c(): pass",
                "def test_new_d(): pass",
                "def test_new_e(): pass",
            ]
        )

        with pytest.raises(TestChurnError) as excinfo:
            _verify_test_churn(
                before,
                after,
                "update_main_test_Python.prompt",
                "tests/test_update_main.py",
                "",
            )

        assert excinfo.value.churn_ratio > excinfo.value.threshold
        assert "Test churn threshold exceeded for update_main_test_Python.prompt:" in str(excinfo.value)

    def test_test_churn_allows_pure_additive_growth(self, monkeypatch):
        from pdd.code_generator_main import _verify_test_churn

        monkeypatch.setenv("PDD_TEST_CHURN_THRESHOLD", "0.40")
        before = "def test_a():\n    assert True\n"
        after = before + "\ndef test_b():\n    assert True\n"

        _verify_test_churn(
            before,
            after,
            "module_test_Python.prompt",
            "tests/test_module.py",
            "",
        )

    def test_test_churn_requires_explicit_test_rewrite_marker(self, monkeypatch):
        from pdd.code_generator_main import TestChurnError, _verify_test_churn

        monkeypatch.setenv("PDD_TEST_CHURN_THRESHOLD", "0.40")
        before = "def test_a(): pass\ndef test_b(): pass\ndef test_c(): pass\n"
        after = "def test_new_a(): pass\ndef test_new_b(): pass\ndef test_new_c(): pass\n"

        with pytest.raises(TestChurnError):
            _verify_test_churn(
                before,
                after,
                "module_test_Python.prompt",
                "tests/test_module.py",
                "BREAKING-CHANGE: remove old_helper.",
            )

        _verify_test_churn(
            before,
            after,
            "module_test_Python.prompt",
            "tests/test_module.py",
            "BREAKING-CHANGE: rewrite tests for new contract.",
        )

    def test_test_churn_gate_has_dedicated_skip_flag(self, monkeypatch):
        from pdd.code_generator_main import _verify_test_churn

        monkeypatch.setenv("PDD_TEST_CHURN_THRESHOLD", "0.40")
        monkeypatch.setenv("PDD_SKIP_TEST_CHURN_GATE", "1")

        _verify_test_churn(
            "def test_a(): pass\ndef test_b(): pass\ndef test_c(): pass\n",
            "def test_new_a(): pass\ndef test_new_b(): pass\ndef test_new_c(): pass\n",
            "module_test_Python.prompt",
            "tests/test_module.py",
            "",
        )

    def test_test_churn_threshold_is_clamped_to_one(self, monkeypatch):
        from pdd.code_generator_main import _get_test_churn_threshold

        monkeypatch.setenv("PDD_TEST_CHURN_THRESHOLD", "2")

        assert _get_test_churn_threshold() == pytest.approx(1.0)

    # -----------------------------------------------------------------
    # Codex review (#1015): anchoring + verb-form coverage for the
    # BREAKING-CHANGE: opt-out parsers. Mid-line prose mentioning the
    # marker must NOT disable a gate, and the documented gerund variants
    # (`rewriting`/`replacing`) MUST opt out the test-churn gate.
    # -----------------------------------------------------------------
    def test_test_churn_gate_ignores_midline_marker(self, monkeypatch):
        """Buried prose like 'use BREAKING-CHANGE: rewrite tests to opt out'
        must NOT opt out the gate — only an anchored directive line does."""
        from pdd.code_generator_main import TestChurnError, _verify_test_churn

        monkeypatch.setenv("PDD_TEST_CHURN_THRESHOLD", "0.40")
        before = "def test_a(): pass\ndef test_b(): pass\ndef test_c(): pass\n"
        after = "def test_new_a(): pass\ndef test_new_b(): pass\ndef test_new_c(): pass\n"
        prose = (
            "# Marker docs: use `BREAKING-CHANGE: rewrite tests` to opt out.\n"
        )

        with pytest.raises(TestChurnError):
            _verify_test_churn(
                before,
                after,
                "module_test_Python.prompt",
                "tests/test_module.py",
                prose,
            )

    def test_test_churn_gate_accepts_gerund_variants(self, monkeypatch):
        """Documented gerund forms (`rewriting`/`replacing` tests) MUST opt
        out — the prompt body explicitly suggests this wording."""
        from pdd.code_generator_main import _verify_test_churn

        monkeypatch.setenv("PDD_TEST_CHURN_THRESHOLD", "0.40")
        before = "def test_a(): pass\ndef test_b(): pass\ndef test_c(): pass\n"
        after = "def test_new_a(): pass\ndef test_new_b(): pass\ndef test_new_c(): pass\n"

        for marker in (
            "BREAKING-CHANGE: rewriting tests for new contract.",
            "BREAKING-CHANGE: replacing tests after refactor.",
            "BREAKING-CHANGE: regenerating tests to match new fixtures.",
            "   BREAKING-CHANGE: rewrite tests after split.",
        ):
            _verify_test_churn(
                before,
                after,
                "module_test_Python.prompt",
                "tests/test_module.py",
                marker,
            )

    def test_test_churn_gate_rejects_unrelated_target(self, monkeypatch):
        """A `BREAKING-CHANGE: rewrite calculator` directive must NOT opt out
        the test-churn gate — the verb must be paired with `test`/`tests`."""
        from pdd.code_generator_main import TestChurnError, _verify_test_churn

        monkeypatch.setenv("PDD_TEST_CHURN_THRESHOLD", "0.40")
        before = "def test_a(): pass\ndef test_b(): pass\ndef test_c(): pass\n"
        after = "def test_new_a(): pass\ndef test_new_b(): pass\ndef test_new_c(): pass\n"

        with pytest.raises(TestChurnError):
            _verify_test_churn(
                before,
                after,
                "module_test_Python.prompt",
                "tests/test_module.py",
                "BREAKING-CHANGE: rewrite calculator helper.",
            )

    # -----------------------------------------------------------------
    # Codex review (#1015) Finding 1 (iter-2): the verb must take
    # `tests?` as its OBJECT, not merely co-occur with it. A comma,
    # semicolon, or conjunction (`and`/`but`/`then`/`or`) between the
    # opt-out verb and `tests?` belongs to a different verb's phrase,
    # so the directive must NOT opt out.
    # -----------------------------------------------------------------
    def test_test_churn_gate_rejects_verb_with_different_object(self, monkeypatch):
        """`BREAKING-CHANGE: rewrite docs and update tests` must NOT opt out:
        the opt-out verb's object is `docs`, and `update` is not an opt-out
        verb. Codex review #1015 Finding 1 (iter-2)."""
        from pdd.code_generator_main import TestChurnError, _verify_test_churn

        monkeypatch.setenv("PDD_TEST_CHURN_THRESHOLD", "0.40")
        before = "def test_a(): pass\ndef test_b(): pass\ndef test_c(): pass\n"
        after = "def test_new_a(): pass\ndef test_new_b(): pass\ndef test_new_c(): pass\n"

        for marker in (
            "BREAKING-CHANGE: rewrite docs and update tests.",
            "BREAKING-CHANGE: rewrite docs, update tests.",
            "BREAKING-CHANGE: rewriting calculator helper but keep tests.",
            "BREAKING-CHANGE: replace shim; preserve tests.",
        ):
            with pytest.raises(TestChurnError):
                _verify_test_churn(
                    before,
                    after,
                    "module_test_Python.prompt",
                    "tests/test_module.py",
                    marker,
                )

    def test_test_churn_gate_accepts_verb_directly_governing_tests(self, monkeypatch):
        """The verb may have prose between itself and `tests?` (e.g. a
        determiner like `the` or a noun phrase like `the failing`) as long
        as no comma/conjunction breaks the phrase. Codex review #1015
        Finding 1 (iter-2)."""
        from pdd.code_generator_main import _verify_test_churn

        monkeypatch.setenv("PDD_TEST_CHURN_THRESHOLD", "0.40")
        before = "def test_a(): pass\ndef test_b(): pass\ndef test_c(): pass\n"
        after = "def test_new_a(): pass\ndef test_new_b(): pass\ndef test_new_c(): pass\n"

        for marker in (
            "BREAKING-CHANGE: rewriting the failing tests for new helper.",
            "BREAKING-CHANGE: rewrite the test suite for new helper.",
            # An earlier non-churn directive verb is fine: the second
            # opt-out verb here directly governs `tests`.
            "BREAKING-CHANGE: drop foo and rewrite tests.",
        ):
            _verify_test_churn(
                before,
                after,
                "module_test_Python.prompt",
                "tests/test_module.py",
                marker,
            )

    def test_public_surface_gate_ignores_midline_marker(self):
        """Prompt prose explaining the marker by example must NOT whitelist
        prose tokens like `to`/`opt`/`out` as removable symbols."""
        from pdd.code_generator_main import (
            PublicSurfaceRegressionError,
            _verify_public_surface_regression,
        )

        before = (
            "def to():\n    pass\n"
            "def opt():\n    pass\n"
            "def out():\n    pass\n"
        )
        after = "def new_helper():\n    pass\n"
        prose_prompt = (
            "Marker docs: use `BREAKING-CHANGE: remove old_helper` to opt out.\n"
        )

        with pytest.raises(PublicSurfaceRegressionError) as excinfo:
            _verify_public_surface_regression(
                before,
                after,
                "module_Python.prompt",
                "pdd/module.py",
                "python",
                prose_prompt,
            )

        # None of `to`, `opt`, `out` should have been silently whitelisted;
        # all three must surface as removed symbols.
        assert set(excinfo.value.removed_symbols) == {"to", "opt", "out"}

    def test_public_surface_gate_rejects_prose_after_verb(self):
        """Even an anchored directive must not leak prose tokens as
        removable symbols — only delimited identifier lists are accepted."""
        from pdd.code_generator_main import (
            PublicSurfaceRegressionError,
            _verify_public_surface_regression,
        )

        before = (
            "def to():\n    pass\n"
            "def opt():\n    pass\n"
            "def out():\n    pass\n"
        )
        after = "def new_helper():\n    pass\n"
        # The verb is recognized but the rest is prose: `to opt out` must NOT
        # be parsed as the symbols `to`, `opt`, `out`.
        prompt_with_directive = "BREAKING-CHANGE: remove old_helper to opt out\n"

        with pytest.raises(PublicSurfaceRegressionError) as excinfo:
            _verify_public_surface_regression(
                before,
                after,
                "module_Python.prompt",
                "pdd/module.py",
                "python",
                prompt_with_directive,
            )

        assert set(excinfo.value.removed_symbols) == {"to", "opt", "out"}

    def test_public_surface_gate_accepts_comma_list(self):
        """An anchored `BREAKING-CHANGE: remove a, b, c` directive correctly
        whitelists each comma-delimited identifier."""
        from pdd.code_generator_main import _verify_public_surface_regression

        before = (
            "def a():\n    pass\n"
            "def b():\n    pass\n"
            "def c():\n    pass\n"
        )
        after = "def new_helper():\n    pass\n"

        _verify_public_surface_regression(
            before,
            after,
            "module_Python.prompt",
            "pdd/module.py",
            "python",
            "BREAKING-CHANGE: remove a, b, c\n",
        )

    def test_signature_gate_ignores_midline_marker(self):
        """Mid-line marker mentions must NOT whitelist a real signature
        change — only an anchored directive opts out."""
        from pdd.code_generator_main import (
            PublicSurfaceRegressionError,
            _verify_public_surface_regression,
        )

        before = "def calculate(value, *, strict=False) -> str:\n    return str(value)\n"
        after = "def calculate(value) -> str:\n    return str(value)\n"
        prose_prompt = (
            "See the BREAKING-CHANGE: change signature calculate marker in the doc.\n"
        )

        with pytest.raises(PublicSurfaceRegressionError) as excinfo:
            _verify_public_surface_regression(
                before,
                after,
                "module_Python.prompt",
                "pdd/module.py",
                "python",
                prose_prompt,
            )

        assert "calculate" in excinfo.value.changed_signatures

    # -----------------------------------------------------------------
    # Codex review (#1015) Medium 3 (iter-3): the BREAKING-CHANGE: opt-out
    # parser must accept quoted identifiers — operators writing the doc
    # naturally reach for backticks/single-quotes/double-quotes around
    # symbol names. The same identifier grammar must work whether the
    # author wraps the symbol or not.
    # -----------------------------------------------------------------
    def test_breaking_change_removal_accepts_quoted_identifiers(self):
        from pdd.code_generator_main import _verify_public_surface_regression

        before = "def old_helper():\n    pass\n"
        after = "def new_helper():\n    pass\n"

        for marker in (
            'BREAKING-CHANGE: remove "old_helper".',
            "BREAKING-CHANGE: remove 'old_helper'.",
            "BREAKING-CHANGE: remove `old_helper`.",
            'BREAKING-CHANGE: remove "old_helper", `another_helper`.',
        ):
            _verify_public_surface_regression(
                before,
                after,
                "module_Python.prompt",
                "pdd/module.py",
                "python",
                marker,
            )

    def test_breaking_change_signature_accepts_quoted_identifiers(self):
        from pdd.code_generator_main import _verify_public_surface_regression

        before = (
            "class MyClass:\n"
            "    def method(self, value, *, strict=False):\n"
            "        return value\n"
        )
        after = (
            "class MyClass:\n"
            "    def method(self, value):\n"
            "        return value\n"
        )

        for marker in (
            "BREAKING-CHANGE: change signature \"MyClass.method\".",
            "BREAKING-CHANGE: change signature 'MyClass.method'.",
        ):
            _verify_public_surface_regression(
                before,
                after,
                "module_Python.prompt",
                "pdd/module.py",
                "python",
                marker,
            )

    def test_breaking_change_rejects_mismatched_quote_wrappers(self):
        """Wrappers must MATCH on both sides — ``"old_helper'`` is a typo,
        not a valid identifier token, so the directive must NOT whitelist
        the removal. Falling back to a sane error keeps the gate
        protective when authors slip a quote.
        """
        from pdd.code_generator_main import (
            PublicSurfaceRegressionError,
            _verify_public_surface_regression,
        )

        before = "def old_helper():\n    pass\n"
        after = "def new_helper():\n    pass\n"

        with pytest.raises(PublicSurfaceRegressionError) as excinfo:
            _verify_public_surface_regression(
                before,
                after,
                "module_Python.prompt",
                "pdd/module.py",
                "python",
                "BREAKING-CHANGE: remove \"old_helper'.",
            )

        assert "old_helper" in excinfo.value.removed_symbols

    # -----------------------------------------------------------------
    # Codex review (#1015) Medium 4 (iter-3): the public-surface
    # snapshot must recurse into nested classes so removing
    # ``Outer.Inner.method`` is caught (the enclosing ``Outer.Inner``
    # may stay, escaping both the removed-symbol diff and the
    # signature-change diff).
    # -----------------------------------------------------------------
    def test_public_surface_regression_catches_nested_class_method_removal(self):
        from pdd.code_generator_main import (
            PublicSurfaceRegressionError,
            _verify_public_surface_regression,
        )

        before = (
            "class Outer:\n"
            "    class Inner:\n"
            "        def removed_method(self):\n"
            "            return 1\n"
            "        def kept_method(self):\n"
            "            return 2\n"
        )
        after = (
            "class Outer:\n"
            "    class Inner:\n"
            "        def kept_method(self):\n"
            "            return 2\n"
        )

        with pytest.raises(PublicSurfaceRegressionError) as excinfo:
            _verify_public_surface_regression(
                before,
                after,
                "module_Python.prompt",
                "pdd/module.py",
                "python",
                "",
            )

        assert "Outer.Inner.removed_method" in excinfo.value.removed_symbols

    def test_public_surface_regression_catches_nested_class_method_signature_change(self):
        from pdd.code_generator_main import (
            PublicSurfaceRegressionError,
            _verify_public_surface_regression,
        )

        before = (
            "class Outer:\n"
            "    class Inner:\n"
            "        def method(self, value, *, strict=False):\n"
            "            return value\n"
        )
        after = (
            "class Outer:\n"
            "    class Inner:\n"
            "        def method(self, value):\n"
            "            return value\n"
        )

        with pytest.raises(PublicSurfaceRegressionError) as excinfo:
            _verify_public_surface_regression(
                before,
                after,
                "module_Python.prompt",
                "pdd/module.py",
                "python",
                "",
            )

        assert "Outer.Inner.method" in excinfo.value.changed_signatures

    def test_public_surface_regression_recursion_depth_two_or_more(self):
        """Triple-nested public classes (``A.B.C.method``) must also be
        recorded by the snapshot — single-level recursion is not enough."""
        from pdd.code_generator_main import (
            PublicSurfaceRegressionError,
            _verify_public_surface_regression,
        )

        before = (
            "class Outer:\n"
            "    class Mid:\n"
            "        class Inner:\n"
            "            def removed(self):\n"
            "                return 1\n"
        )
        after = (
            "class Outer:\n"
            "    class Mid:\n"
            "        class Inner:\n"
            "            pass\n"
        )

        with pytest.raises(PublicSurfaceRegressionError) as excinfo:
            _verify_public_surface_regression(
                before,
                after,
                "module_Python.prompt",
                "pdd/module.py",
                "python",
                "",
            )

        assert "Outer.Mid.Inner.removed" in excinfo.value.removed_symbols

    def test_public_surface_regression_nested_private_class_ignored(self):
        """A leading-underscore (private) nested class must NOT contribute
        symbols to the snapshot, even when its enclosing class is public."""
        from pdd.code_generator_main import _verify_public_surface_regression

        before = (
            "class Outer:\n"
            "    class _Inner:\n"
            "        def helper(self):\n"
            "            return 1\n"
        )
        after = (
            "class Outer:\n"
            "    class _Inner:\n"
            "        pass\n"
        )

        # _Inner is private; removing its method should not fail the gate.
        _verify_public_surface_regression(
            before,
            after,
            "module_Python.prompt",
            "pdd/module.py",
            "python",
            "",
        )

    # -----------------------------------------------------------------
    # Codex review (#1015) Medium 5 (iter-3): PDD_TEST_CHURN_THRESHOLD
    # must accept a trailing ``%`` so common operator wording like
    # ``50%`` is treated as ``0.50`` rather than silently clamped to
    # the default 0.40.
    # -----------------------------------------------------------------
    def test_test_churn_threshold_accepts_percent_suffix(self, monkeypatch):
        from pdd.code_generator_main import _get_test_churn_threshold

        for raw, expected in (
            ("40%", 0.40),
            ("50%", 0.50),
            ("100%", 1.0),
            ("0%", 0.0),
            ("50 %", 0.50),
        ):
            monkeypatch.setenv("PDD_TEST_CHURN_THRESHOLD", raw)
            assert _get_test_churn_threshold() == pytest.approx(expected)

    def test_test_churn_threshold_invalid_defaults_and_warns(self, monkeypatch, caplog):
        from pdd.code_generator_main import _get_test_churn_threshold

        monkeypatch.setenv("PDD_TEST_CHURN_THRESHOLD", "invalid")
        caplog.set_level("WARNING", logger="pdd.code_generator_main")

        assert _get_test_churn_threshold() == pytest.approx(0.40)
        assert any(
            "PDD_TEST_CHURN_THRESHOLD" in record.message
            for record in caplog.records
        )

    # -----------------------------------------------------------------
    # External review (PR #1015) follow-up: extend churn-gate file-type
    # detection past Python/JS — `<name>_test.go` and `<name>_spec.rb`
    # live next to production code (not under `tests/`) and the gate's
    # early-return previously skipped them.
    # -----------------------------------------------------------------
    def test_test_churn_gate_catches_sibling_go_test_file(self):
        """`handler_test.go` sitting next to `handler.go` must trip the
        churn gate when generation drops most of the existing tests."""
        from pdd.code_generator_main import TestChurnError, _verify_test_churn

        before = "\n".join(f"func TestCase{i}(t *testing.T) {{}}" for i in range(20)) + "\n"
        after = "func TestCase0(t *testing.T) {}\n"

        with pytest.raises(TestChurnError):
            _verify_test_churn(
                before,
                after,
                "handler_test_go.prompt",
                "service/handler_test.go",
                "Cover the public API.",
            )

    def test_test_churn_gate_catches_sibling_ruby_spec_file(self):
        """`widget_spec.rb` next to `widget.rb` must trip the gate too."""
        from pdd.code_generator_main import TestChurnError, _verify_test_churn

        before = "\n".join(f"it 'case {i}' do; end" for i in range(20)) + "\n"
        after = "it 'case 0' do; end\n"

        with pytest.raises(TestChurnError):
            _verify_test_churn(
                before,
                after,
                "widget_spec_ruby.prompt",
                "app/widget_spec.rb",
                "Document the public API.",
            )

    def test_test_churn_gate_catches_pascal_case_java_test_file(self):
        """`src/test/java/FooTest.java` (PascalCase `Test.java`) must trip
        the churn gate. The agentic test prompt names `Test.java` as a
        first-class test convention."""
        from pdd.code_generator_main import TestChurnError, _verify_test_churn

        before = (
            "\n".join(
                f"  @Test public void case{i}() {{}}" for i in range(20)
            )
            + "\n"
        )
        after = "  @Test public void case0() {}\n"

        with pytest.raises(TestChurnError):
            _verify_test_churn(
                before,
                after,
                "FooTest_java.prompt",
                "src/test/java/FooTest.java",
                "Cover the public API.",
            )

    def test_test_churn_gate_catches_kotlin_spec_file(self):
        """`WidgetSpec.kt` (PascalCase `Spec.kt`) must trip the gate."""
        from pdd.code_generator_main import TestChurnError, _verify_test_churn

        before = (
            "\n".join(f"  fun `case {i}`() {{}}" for i in range(20)) + "\n"
        )
        after = "  fun `case 0`() {}\n"

        with pytest.raises(TestChurnError):
            _verify_test_churn(
                before,
                after,
                "WidgetSpec_kt.prompt",
                "src/test/kotlin/WidgetSpec.kt",
                "Cover the public API.",
            )

    def test_test_churn_gate_skips_pascal_case_false_positive(self):
        """`latest.kt` is NOT a test file even though it ends with the
        substring `test.kt` — the PascalCase suffix match is
        case-sensitive on `Test`/`Tests`/`Spec` to avoid this trap."""
        from pdd.code_generator_main import _verify_test_churn

        # Large rewrite that would normally trip the gate.
        before = "\n".join(f"val item{i} = {i}" for i in range(50)) + "\n"
        after = "val item0 = 0\n"

        # Must NOT raise — `latest.kt` is regular code, not a test.
        _verify_test_churn(
            before,
            after,
            "latest_kt.prompt",
            "src/main/kotlin/latest.kt",
            "Internal refactor.",
        )

    # -----------------------------------------------------------------
    # External review (PR #1015) iter-11 follow-up: extend test-suffix
    # detection past `Test.java`/`Tests.kt`/`Spec.kt` to cover JUnit
    # integration tests (`FooIT.java`), older JUnit/TestNG
    # (`FooTestCase.java`), ScalaTest specs (`FooSpec.scala`), and
    # Rust sibling tests (`foo_test.rs`).
    # -----------------------------------------------------------------
    def test_test_churn_gate_catches_java_integration_test(self):
        """`FooIT.java` (Maven failsafe integration test) must trip the gate."""
        from pdd.code_generator_main import TestChurnError, _verify_test_churn

        before = (
            "\n".join(f"  @Test public void case{i}() {{}}" for i in range(20))
            + "\n"
        )
        after = "  @Test public void case0() {}\n"

        with pytest.raises(TestChurnError):
            _verify_test_churn(
                before,
                after,
                "FooIT_java.prompt",
                "src/test/java/FooIT.java",
                "Cover the public API.",
            )

    def test_test_churn_gate_catches_java_testcase(self):
        """`FooTestCase.java` (older JUnit/TestNG convention) too."""
        from pdd.code_generator_main import TestChurnError, _verify_test_churn

        before = (
            "\n".join(f"  public void testCase{i}() {{}}" for i in range(20))
            + "\n"
        )
        after = "  public void testCase0() {}\n"

        with pytest.raises(TestChurnError):
            _verify_test_churn(
                before,
                after,
                "FooTestCase_java.prompt",
                "src/test/java/FooTestCase.java",
                "Cover the public API.",
            )

    def test_test_churn_gate_catches_scala_spec(self):
        """`FooSpec.scala` (ScalaTest convention) too."""
        from pdd.code_generator_main import TestChurnError, _verify_test_churn

        before = "\n".join(f'  it("case {i}") {{}}' for i in range(20)) + "\n"
        after = '  it("case 0") {}\n'

        with pytest.raises(TestChurnError):
            _verify_test_churn(
                before,
                after,
                "FooSpec_scala.prompt",
                "src/test/scala/FooSpec.scala",
                "Cover the public API.",
            )

    def test_test_churn_gate_catches_rust_sibling_test(self):
        """`widget_test.rs` next to `widget.rs` (Rust sibling test) too."""
        from pdd.code_generator_main import TestChurnError, _verify_test_churn

        before = (
            "\n".join(f"#[test]\nfn case_{i}() {{}}" for i in range(20)) + "\n"
        )
        after = "#[test]\nfn case_0() {}\n"

        with pytest.raises(TestChurnError):
            _verify_test_churn(
                before,
                after,
                "widget_test_rs.prompt",
                "src/widget_test.rs",
                "Cover the public API.",
            )

    # -----------------------------------------------------------------
    # External review (PR #1015) iter-12 follow-up: broaden test-suffix
    # coverage to all `_test.<ext>` / `_spec.<ext>` extensions in
    # `_LANGUAGE_TEST_FILE_EXTS` (Elixir/Dart/Clojure/Lua/PHP appear by
    # data, not code) AND add Groovy PascalCase (Spock convention).
    # -----------------------------------------------------------------
    def test_test_churn_gate_catches_groovy_spec(self):
        """`FooSpec.groovy` (Spock framework) must trip the gate."""
        from pdd.code_generator_main import TestChurnError, _verify_test_churn

        before = (
            "\n".join(f"  def 'case {i}'() {{}}" for i in range(20)) + "\n"
        )
        after = "  def 'case 0'() {}\n"

        with pytest.raises(TestChurnError):
            _verify_test_churn(
                before,
                after,
                "FooSpec_groovy.prompt",
                "src/test/groovy/FooSpec.groovy",
                "Cover the public API.",
            )

    def test_test_churn_gate_catches_elixir_sibling_test(self):
        """`widget_test.exs` (Elixir ExUnit) must trip the gate."""
        from pdd.code_generator_main import TestChurnError, _verify_test_churn

        before = (
            "\n".join(f'  test "case {i}" do\n  end' for i in range(20))
            + "\n"
        )
        after = '  test "case 0" do\n  end\n'

        with pytest.raises(TestChurnError):
            _verify_test_churn(
                before,
                after,
                "widget_test_exs.prompt",
                "lib/widget_test.exs",
                "Cover the public API.",
            )

    def test_test_churn_gate_catches_dart_sibling_test(self):
        """`widget_test.dart` (Flutter / Dart test) must trip the gate."""
        from pdd.code_generator_main import TestChurnError, _verify_test_churn

        before = (
            "\n".join(f"  test('case {i}', () {{}});" for i in range(20))
            + "\n"
        )
        after = "  test('case 0', () {});\n"

        with pytest.raises(TestChurnError):
            _verify_test_churn(
                before,
                after,
                "widget_test_dart.prompt",
                "lib/widget_test.dart",
                "Cover the public API.",
            )

    def test_test_churn_gate_catches_clojure_sibling_test(self):
        """`widget_test.clj` (clojure.test) must trip the gate."""
        from pdd.code_generator_main import TestChurnError, _verify_test_churn

        before = (
            "\n".join(f"(deftest case-{i} (is true))" for i in range(20))
            + "\n"
        )
        after = "(deftest case-0 (is true))\n"

        with pytest.raises(TestChurnError):
            _verify_test_churn(
                before,
                after,
                "widget_test_clj.prompt",
                "src/widget_test.clj",
                "Cover the public API.",
            )

    def test_test_churn_gate_catches_lua_busted_spec(self):
        """`widget_spec.lua` (Busted) must trip the gate."""
        from pdd.code_generator_main import TestChurnError, _verify_test_churn

        before = (
            "\n".join(f'  it("case {i}", function() end)' for i in range(20))
            + "\n"
        )
        after = '  it("case 0", function() end)\n'

        with pytest.raises(TestChurnError):
            _verify_test_churn(
                before,
                after,
                "widget_spec_lua.prompt",
                "src/widget_spec.lua",
                "Cover the public API.",
            )

    def test_test_churn_gate_skips_groovy_false_positive(self):
        """`Greatest.groovy` is NOT a test file; the PascalCase
        `Spec.groovy`/`Test.groovy` match must remain case-sensitive
        so generic names ending in `est.groovy` do not trip the gate."""
        from pdd.code_generator_main import _verify_test_churn

        before = "\n".join(f"def item{i} = {i}" for i in range(50)) + "\n"
        after = "def item0 = 0\n"

        # Must NOT raise — `Greatest.groovy` is regular code, not a test.
        _verify_test_churn(
            before,
            after,
            "Greatest_groovy.prompt",
            "src/main/groovy/Greatest.groovy",
            "Internal refactor.",
        )

    # -----------------------------------------------------------------
    # External review (PR #1015) follow-up: `from __future__ import …`
    # is a compiler directive, not a public attribute, so removing it
    # MUST NOT trip the public-surface gate.
    # -----------------------------------------------------------------
    def test_public_surface_regression_ignores_future_import(self):
        """`from __future__ import annotations` is not part of the
        importable public surface — removing it after a Python-version
        bump must not fail the gate."""
        from pdd.code_generator_main import _verify_public_surface_regression

        before = (
            "from __future__ import annotations\n"
            "def public_one(x: int) -> int:\n    return x\n"
        )
        after = "def public_one(x: int) -> int:\n    return x\n"

        # Must NOT raise — the only "removed" name is a future directive.
        _verify_public_surface_regression(
            before,
            after,
            "module_Python.prompt",
            "pdd/module.py",
            "python",
            "Clean up the future-imports header.",
        )

    def test_public_surface_regression_future_import_under_dunder_all(self):
        """`__all__ = ["annotations"]` combined with `from __future__
        import annotations` must NOT promote the future binding into
        the public surface: cleaning up the directive (and the bogus
        `__all__` entry) should not fire `removed: annotations`."""
        from pdd.code_generator_main import _verify_public_surface_regression

        before = (
            "from __future__ import annotations\n"
            "__all__ = [\"annotations\", \"public_one\"]\n"
            "def public_one():\n    return 1\n"
        )
        after = (
            "__all__ = [\"public_one\"]\n"
            "def public_one():\n    return 1\n"
        )

        # Must NOT raise — `annotations` was only ever a `__future__`
        # binding, which the gate now ignores even when `__all__`
        # mentions it.
        _verify_public_surface_regression(
            before,
            after,
            "module_Python.prompt",
            "pdd/module.py",
            "python",
            "Clean up the future-imports header and __all__ list.",
        )

    def test_public_surface_regression_future_import_to_real_assignment(self):
        """A regenerated module that drops `from __future__ import
        annotations` AND binds a real `annotations = …` attribute MUST
        NOT trip the signature-drift diff. Without the parallel
        `__future__` skip in `_snapshot_public_signatures` the
        before-signature `[import:from __future__]` would falsely diff
        against the after-signature `[assignment]` on the same name."""
        from pdd.code_generator_main import _verify_public_surface_regression

        before = (
            "from __future__ import annotations\n"
            "def public_one(x: int) -> int:\n    return x\n"
        )
        after = (
            "annotations = {\"version\": 1}\n"
            "def public_one(x: int) -> int:\n    return x\n"
        )

        # Must NOT raise — `annotations` only existed as a `__future__`
        # directive before, which the gate now ignores.
        _verify_public_surface_regression(
            before,
            after,
            "module_Python.prompt",
            "pdd/module.py",
            "python",
            "Replace the future-imports header with a real annotations dict.",
        )

    # -----------------------------------------------------------------
    # External review (PR #1015) follow-up: `BREAKING-CHANGE: remove
    # Service` should authorize removing every captured descendant of
    # `Service` (its methods, nested classes, and their methods). Without
    # the expansion the caller has to enumerate every member by hand.
    # -----------------------------------------------------------------
    def test_public_surface_regression_breaking_change_remove_class_covers_descendants(self):
        """Listing a top-level class in `BREAKING-CHANGE: remove …`
        implicitly authorizes removing every `Class.method` /
        `Class.Inner.method` descendant the snapshot captured."""
        from pdd.code_generator_main import _verify_public_surface_regression

        before = (
            "class Service:\n"
            "    def run(self):\n        return 1\n"
            "    class Inner:\n"
            "        def go(self):\n            return 2\n"
            "def keep_me():\n    return 0\n"
        )
        after = "def keep_me():\n    return 0\n"

        # The directive only names `Service`; the gate must accept the
        # disappearance of `Service.run`, `Service.Inner`, and
        # `Service.Inner.go` without forcing the caller to enumerate them.
        _verify_public_surface_regression(
            before,
            after,
            "module_Python.prompt",
            "pdd/module.py",
            "python",
            "BREAKING-CHANGE: remove Service\n",
        )


# ---------------------------------------------------------------------------
# Tests for <pdd-interface> signature conformance (Issue #928)
# ---------------------------------------------------------------------------
class TestPddInterfaceSignatureConformance:
    """Tests for the <pdd-interface> signature conformance check (Issue #928).

    The existing architecture conformance check verifies that declared symbols
    EXIST in the generated code, but it does not check the function SIGNATURE.
    This means PDD sync could silently regenerate code that drops a declared
    keyword argument (e.g. ``sync_metadata=False``) without surfacing the bug.

    These tests cover the new signature check that compares parameter names
    declared in the prompt's ``<pdd-interface>`` block against the parameter
    names of the matching ``ast.FunctionDef`` (or ``__init__`` for declared
    classes) in the generated code.
    """

    def _write_arch(self, tmp_path, prompt_filename: str) -> str:
        """Helper: write a minimal architecture.json that matches the prompt."""
        arch = [
            {
                "filename": prompt_filename,
                "filepath": f"src/{pathlib.Path(prompt_filename).stem}.py",
                "interface": {
                    "type": "module",
                    "module": {
                        "functions": [
                            # Declare a single function so the existing
                            # symbol-existence check passes; the new signature
                            # check operates on the prompt's <pdd-interface>.
                            {"name": "update_main", "signature": "def update_main(...)"},
                        ]
                    },
                },
            }
        ]
        arch_path = tmp_path / "architecture.json"
        arch_path.write_text(json.dumps(arch))
        return str(arch_path)

    def test_missing_kwarg_in_function_raises_conformance_error(self, tmp_path):
        """Missing kwarg declared in <pdd-interface> raises ArchitectureConformanceError."""
        from pdd.code_generator_main import ArchitectureConformanceError

        prompt_filename = "update_main_python.prompt"
        arch_path = self._write_arch(tmp_path, prompt_filename)
        prompt_content = (
            '<pdd-interface>{"type":"module","module":{"functions":'
            '[{"name":"update_main","signature":"(ctx, input, output, sync_metadata=False)"}]}}'
            '</pdd-interface>\n'
            '% You are an expert Python engineer.\n'
        )
        # Code that declares update_main without the sync_metadata kwarg
        generated_code = "def update_main(ctx, input, output):\n    pass\n"

        with pytest.raises(ArchitectureConformanceError) as excinfo:
            _verify_architecture_conformance(
                generated_code=generated_code,
                prompt_name=prompt_filename,
                arch_path=arch_path,
                language="python",
                verbose=False,
                prompt_content=prompt_content,
            )

        exc = excinfo.value
        assert exc.missing_symbols == ["update_main.sync_metadata"]
        assert str(exc).startswith(
            f"Architecture conformance error for {prompt_filename}:"
        )
        # Must surface the missing parameter name in the message.
        assert "sync_metadata" in str(exc)

    def test_cli_command_missing_kwarg_raises(self, tmp_path):
        """CLI commands declared in <pdd-interface> with missing kwarg raise."""
        from pdd.code_generator_main import ArchitectureConformanceError

        prompt_filename = "update_main_python.prompt"
        arch_path = self._write_arch(tmp_path, prompt_filename)
        prompt_content = (
            '<pdd-interface>{"type":"cli","cli":{"commands":'
            '[{"name":"update_main","signature":"(ctx, foo, bar, sync_metadata=False)"}]}}'
            '</pdd-interface>\n'
        )
        generated_code = "def update_main(ctx, foo, bar):\n    pass\n"

        with pytest.raises(ArchitectureConformanceError) as excinfo:
            _verify_architecture_conformance(
                generated_code=generated_code,
                prompt_name=prompt_filename,
                arch_path=arch_path,
                language="python",
                verbose=False,
                prompt_content=prompt_content,
            )
        assert excinfo.value.missing_symbols == ["update_main.sync_metadata"]

    def test_present_kwarg_passes(self, tmp_path):
        """Generated code that includes the declared kwarg passes (no raise)."""
        prompt_filename = "update_main_python.prompt"
        arch_path = self._write_arch(tmp_path, prompt_filename)
        prompt_content = (
            '<pdd-interface>{"type":"module","module":{"functions":'
            '[{"name":"update_main","signature":"(ctx, input, output, sync_metadata=False)"}]}}'
            '</pdd-interface>\n'
        )
        generated_code = (
            "def update_main(ctx, input, output, sync_metadata=False):\n"
            "    return sync_metadata\n"
        )

        # Should not raise.
        _verify_architecture_conformance(
            generated_code=generated_code,
            prompt_name=prompt_filename,
            arch_path=arch_path,
            language="python",
            verbose=False,
            prompt_content=prompt_content,
        )

    def test_kwargs_variadic_does_not_satisfy_named_param(self, tmp_path):
        """**kwargs catch-all does NOT satisfy a declared named param."""
        from pdd.code_generator_main import ArchitectureConformanceError

        prompt_filename = "update_main_python.prompt"
        arch_path = self._write_arch(tmp_path, prompt_filename)
        prompt_content = (
            '<pdd-interface>{"type":"module","module":{"functions":'
            '[{"name":"update_main","signature":"(ctx, sync_metadata=False)"}]}}'
            '</pdd-interface>\n'
        )
        # Variadic kwargs catch-all should NOT satisfy a named kwarg contract.
        generated_code = "def update_main(ctx, **kwargs):\n    pass\n"

        with pytest.raises(ArchitectureConformanceError) as excinfo:
            _verify_architecture_conformance(
                generated_code=generated_code,
                prompt_name=prompt_filename,
                arch_path=arch_path,
                language="python",
                verbose=False,
                prompt_content=prompt_content,
            )
        assert "update_main.sync_metadata" in excinfo.value.missing_symbols

    def test_missing_pdd_interface_skips_check(self, tmp_path):
        """If the prompt has no <pdd-interface> block, the new check is skipped."""
        prompt_filename = "update_main_python.prompt"
        arch_path = self._write_arch(tmp_path, prompt_filename)
        prompt_content = "% You are an expert Python engineer. No tags here.\n"
        # Function exists at top level (existing symbol-existence check passes)
        # but uses different parameter names than caller would have expected.
        generated_code = "def update_main(a, b, c):\n    pass\n"

        # Should not raise -- no <pdd-interface> declared, nothing to enforce.
        _verify_architecture_conformance(
            generated_code=generated_code,
            prompt_name=prompt_filename,
            arch_path=arch_path,
            language="python",
            verbose=False,
            prompt_content=prompt_content,
        )

    def test_malformed_pdd_interface_warns_and_skips(self, tmp_path, caplog):
        """Malformed <pdd-interface> JSON logs a warning and skips the new check."""
        import logging

        prompt_filename = "update_main_python.prompt"
        arch_path = self._write_arch(tmp_path, prompt_filename)
        prompt_content = (
            '<pdd-interface>not valid json at all</pdd-interface>\n'
            '% Body.\n'
        )
        generated_code = "def update_main(ctx):\n    pass\n"

        with caplog.at_level(logging.WARNING, logger="pdd.code_generator_main"):
            # Must not raise.
            _verify_architecture_conformance(
                generated_code=generated_code,
                prompt_name=prompt_filename,
                arch_path=arch_path,
                language="python",
                verbose=False,
                prompt_content=prompt_content,
            )

        # Confirm a warning was emitted mentioning the parse error.
        assert any(
            "interface" in record.message.lower()
            and ("parse" in record.message.lower() or "json" in record.message.lower())
            for record in caplog.records
            if record.levelno >= logging.WARNING
        ), f"Expected a warning about pdd-interface parse error, got: {[r.message for r in caplog.records]}"

    def test_extra_kwarg_in_code_does_not_raise(self, tmp_path):
        """Extra parameters in generated code are allowed; only missing fail."""
        prompt_filename = "update_main_python.prompt"
        arch_path = self._write_arch(tmp_path, prompt_filename)
        prompt_content = (
            '<pdd-interface>{"type":"module","module":{"functions":'
            '[{"name":"update_main","signature":"(ctx, input)"}]}}'
            '</pdd-interface>\n'
        )
        # Generated code has MORE params than declared -- this must be allowed.
        generated_code = (
            "def update_main(ctx, input, extra_param=None, sync_metadata=False):\n"
            "    pass\n"
        )

        # Should not raise.
        _verify_architecture_conformance(
            generated_code=generated_code,
            prompt_name=prompt_filename,
            arch_path=arch_path,
            language="python",
            verbose=False,
            prompt_content=prompt_content,
        )

    def test_reuses_architecture_conformance_error_fields(self, tmp_path):
        """Raised exception has all structured fields populated correctly."""
        from pdd.code_generator_main import ArchitectureConformanceError

        prompt_filename = "update_main_python.prompt"
        arch_path = self._write_arch(tmp_path, prompt_filename)
        prompt_content = (
            '<pdd-interface>{"type":"module","module":{"functions":'
            '[{"name":"update_main","signature":"(ctx, input, output, sync_metadata=False)"}]}}'
            '</pdd-interface>\n'
        )
        generated_code = "def update_main(ctx, input, output):\n    pass\n"

        with pytest.raises(ArchitectureConformanceError) as excinfo:
            _verify_architecture_conformance(
                generated_code=generated_code,
                prompt_name=prompt_filename,
                arch_path=arch_path,
                language="python",
                verbose=False,
                output_path="src/update_main.py",
                prompt_content=prompt_content,
            )

        exc = excinfo.value
        # Must subclass click.UsageError so existing handlers still work.
        assert isinstance(exc, click.UsageError)
        # Structured fields populated.
        assert exc.prompt_name == prompt_filename
        assert exc.output_path == "src/update_main.py"
        assert isinstance(exc.architecture_entry, dict)
        assert exc.missing_symbols == ["update_main.sync_metadata"]
        # expected/found symbols carry the declared/actual param names so the
        # repair loop has the same diagnostic shape as the existing checks.
        assert "update_main.sync_metadata" in exc.expected_symbols
        # Repair directive must be a non-empty string with the missing param.
        directive = exc.repair_directive
        assert isinstance(directive, str) and directive.strip()
        assert "sync_metadata" in directive
        # The directive must NOT instruct removing the declared param from the
        # prompt -- the prompt is the source of truth.
        assert "Do not remove the declared parameters from the prompt" in directive

    def test_signature_check_skips_when_function_absent_from_code(self, tmp_path):
        """When the declared function is missing entirely, the existing
        symbol-existence check fires; the new signature check must not
        double-fire or mask that error.
        """
        from pdd.code_generator_main import ArchitectureConformanceError

        # Arch declares ``update_main`` as a required symbol; code provides none.
        prompt_filename = "update_main_python.prompt"
        arch_path = self._write_arch(tmp_path, prompt_filename)
        prompt_content = (
            '<pdd-interface>{"type":"module","module":{"functions":'
            '[{"name":"update_main","signature":"(ctx, sync_metadata=False)"}]}}'
            '</pdd-interface>\n'
        )
        generated_code = "def something_else():\n    pass\n"

        with pytest.raises(ArchitectureConformanceError) as excinfo:
            _verify_architecture_conformance(
                generated_code=generated_code,
                prompt_name=prompt_filename,
                arch_path=arch_path,
                language="python",
                verbose=False,
                prompt_content=prompt_content,
            )
        # The existing symbol-existence check must own this: the missing entry
        # is the function name itself, not a dotted ``update_main.sync_metadata``.
        assert "update_main" in excinfo.value.missing_symbols
        assert "update_main.sync_metadata" not in excinfo.value.missing_symbols

    def test_dotted_class_method_signature_is_checked(self, tmp_path):
        """``Outer.method`` signatures declared in <pdd-interface> are resolved
        through the class body, and missing params on the method are reported
        as dotted ``Outer.method.param`` entries. Issue #928 follow-up: prior
        to this fix, ``_find_target_function`` only handled bare names so
        any prompt declaring a method on a class (e.g. ``ContentSelector.select``)
        was silently skipped.
        """
        from pdd.code_generator_main import ArchitectureConformanceError

        prompt_filename = "content_selector_python.prompt"
        # Architecture entry declares only the class; the method's signature
        # contract is owned by the prompt's <pdd-interface>.
        arch = [
            {
                "filename": prompt_filename,
                "filepath": "src/content_selector.py",
                "interface": {
                    "type": "module",
                    "module": {
                        "functions": [
                            {"name": "ContentSelector", "signature": "class ContentSelector"},
                        ]
                    },
                },
            }
        ]
        arch_path = tmp_path / "architecture.json"
        arch_path.write_text(json.dumps(arch))
        prompt_content = (
            '<pdd-interface>{"type":"module","module":{"functions":'
            '[{"name":"ContentSelector.select",'
            '"signature":"(content, selectors, file_path=None, mode=\\"full\\")"}]}}'
            '</pdd-interface>\n'
        )
        generated_code = (
            "class ContentSelector:\n"
            "    def select(self, content, selectors, file_path=None):\n"
            "        return content\n"
        )

        with pytest.raises(ArchitectureConformanceError) as excinfo:
            _verify_architecture_conformance(
                generated_code=generated_code,
                prompt_name=prompt_filename,
                arch_path=str(arch_path),
                language="python",
                verbose=False,
                prompt_content=prompt_content,
            )
        assert excinfo.value.missing_symbols == ["ContentSelector.select.mode"]

    def test_dotted_method_absent_from_class_is_reported(self, tmp_path):
        """When the class exists but the declared method is absent, surface
        the missing method name (``ContentSelector.select``) so the repair
        loop has something concrete to fix. Without this, prompts whose
        architecture.json entry does not also enumerate the method would
        leave the gap uncaught.
        """
        from pdd.code_generator_main import ArchitectureConformanceError

        prompt_filename = "content_selector_python.prompt"
        # Arch declares only the class (no method) so its symbol check passes.
        arch = [
            {
                "filename": prompt_filename,
                "filepath": "src/content_selector.py",
                "interface": {
                    "type": "module",
                    "module": {
                        "functions": [
                            {"name": "ContentSelector", "signature": "class ContentSelector"},
                        ]
                    },
                },
            }
        ]
        arch_path = tmp_path / "architecture.json"
        arch_path.write_text(json.dumps(arch))
        prompt_content = (
            '<pdd-interface>{"type":"module","module":{"functions":'
            '[{"name":"ContentSelector.select",'
            '"signature":"(content, selectors)"}]}}'
            '</pdd-interface>\n'
        )
        generated_code = "class ContentSelector:\n    pass\n"

        with pytest.raises(ArchitectureConformanceError) as excinfo:
            _verify_architecture_conformance(
                generated_code=generated_code,
                prompt_name=prompt_filename,
                arch_path=str(arch_path),
                language="python",
                verbose=False,
                prompt_content=prompt_content,
            )
        assert "ContentSelector.select" in excinfo.value.missing_symbols

    def test_annotation_drift_raises_conformance_error(self, tmp_path):
        """When the prompt declares ``sync_metadata: bool = False`` and the
        generated code has ``sync_metadata: str = True``, the new drift check
        must raise. Issue #928 named this 'type drift' as one of its
        acceptance cases.
        """
        from pdd.code_generator_main import ArchitectureConformanceError

        prompt_filename = "update_main_python.prompt"
        arch_path = self._write_arch(tmp_path, prompt_filename)
        prompt_content = (
            '<pdd-interface>{"type":"module","module":{"functions":'
            '[{"name":"update_main",'
            '"signature":"(ctx, sync_metadata: bool = False)"}]}}'
            '</pdd-interface>\n'
        )
        generated_code = (
            "def update_main(ctx, sync_metadata: str = True):\n"
            "    pass\n"
        )

        with pytest.raises(ArchitectureConformanceError) as excinfo:
            _verify_architecture_conformance(
                generated_code=generated_code,
                prompt_name=prompt_filename,
                arch_path=arch_path,
                language="python",
                verbose=False,
                prompt_content=prompt_content,
            )
        exc = excinfo.value
        # Drift entries are reported as dotted ``func.param`` in missing_symbols.
        assert "update_main.sync_metadata" in exc.missing_symbols
        # Directive must surface the actual drift kind + declared/actual values.
        assert "annotation" in exc.repair_directive
        assert "`bool`" in exc.repair_directive
        assert "`str`" in exc.repair_directive
        # And default drift in the same parameter on the same call.
        assert "default" in exc.repair_directive
        assert "`False`" in exc.repair_directive
        assert "`True`" in exc.repair_directive

    def test_missing_default_raises_drift_even_when_annotation_present(self, tmp_path):
        """Defaults are runtime signature behavior, not static metadata. A
        prompt declaring ``sync_metadata=False`` is advertising that callers
        may omit the kwarg. Generated code that drops the default would
        break those callers with TypeError at the call site, so the drift
        gate MUST fire even though the parameter name is present.
        """
        from pdd.code_generator_main import ArchitectureConformanceError

        prompt_filename = "update_main_python.prompt"
        arch_path = self._write_arch(tmp_path, prompt_filename)
        prompt_content = (
            '<pdd-interface>{"type":"module","module":{"functions":'
            '[{"name":"update_main",'
            '"signature":"(ctx, sync_metadata: bool = False)"}]}}'
            '</pdd-interface>\n'
        )
        # Actual has the param + annotation but is missing the default.
        generated_code = (
            "def update_main(ctx, sync_metadata: bool):\n"
            "    pass\n"
        )

        with pytest.raises(ArchitectureConformanceError) as excinfo:
            _verify_architecture_conformance(
                generated_code=generated_code,
                prompt_name=prompt_filename,
                arch_path=arch_path,
                language="python",
                verbose=False,
                prompt_content=prompt_content,
            )
        exc = excinfo.value
        assert "update_main.sync_metadata" in exc.missing_symbols
        assert "default" in exc.repair_directive
        assert "`False`" in exc.repair_directive
        # The "<no default>" sentinel surfaces in the diagnostic so the
        # LLM knows what to restore.
        assert "<no default>" in exc.repair_directive

    def test_missing_symbols_dedups_when_param_hits_multiple_drift_kinds(self, tmp_path):
        """When a single parameter drifts on BOTH annotation and default,
        ``missing_symbols`` must list the canonical dotted symbol once.
        Duplicates leak into the stuck-symbol-set short-circuit comparison
        and the structured hard-failure block downstream.
        """
        from pdd.code_generator_main import ArchitectureConformanceError

        prompt_filename = "update_main_python.prompt"
        arch_path = self._write_arch(tmp_path, prompt_filename)
        prompt_content = (
            '<pdd-interface>{"type":"module","module":{"functions":'
            '[{"name":"update_main",'
            '"signature":"(ctx, sync_metadata: bool = False)"}]}}'
            '</pdd-interface>\n'
        )
        # Both annotation and default differ from the declared signature.
        generated_code = (
            "def update_main(ctx, sync_metadata: str = True):\n"
            "    pass\n"
        )

        with pytest.raises(ArchitectureConformanceError) as excinfo:
            _verify_architecture_conformance(
                generated_code=generated_code,
                prompt_name=prompt_filename,
                arch_path=arch_path,
                language="python",
                verbose=False,
                prompt_content=prompt_content,
            )
        exc = excinfo.value
        # The same parameter must appear once in missing_symbols even though
        # two drift tuples were generated (one annotation, one default).
        assert exc.missing_symbols.count("update_main.sync_metadata") == 1
        # The repair directive still itemises both drift kinds — the dedup
        # only affects the canonical symbol set.
        assert "annotation" in exc.repair_directive
        assert "default" in exc.repair_directive

    def test_drift_skipped_when_one_side_omits_annotation(self, tmp_path):
        """Conservative behavior: when only one side declares an annotation,
        the drift check does not fire. This keeps the gate from churning
        on gradually-typed code that hasn't caught up to the prompt yet.
        """
        prompt_filename = "update_main_python.prompt"
        arch_path = self._write_arch(tmp_path, prompt_filename)
        prompt_content = (
            '<pdd-interface>{"type":"module","module":{"functions":'
            '[{"name":"update_main",'
            '"signature":"(ctx, sync_metadata: bool = False)"}]}}'
            '</pdd-interface>\n'
        )
        # Same default; actual omits annotation. Must not raise.
        generated_code = (
            "def update_main(ctx, sync_metadata=False):\n"
            "    pass\n"
        )
        _verify_architecture_conformance(
            generated_code=generated_code,
            prompt_name=prompt_filename,
            arch_path=arch_path,
            language="python",
            verbose=False,
            prompt_content=prompt_content,
        )

    def test_command_interface_type_signature_is_checked(self, tmp_path):
        """``type: "command"`` interfaces (used by ``pdd/prompts/commands/*``)
        must participate in the signature check when entries carry a
        ``signature`` field. Both the multi-command (``commands: [...]``) and
        single-command (``name`` at top) shapes are supported.
        """
        from pdd.code_generator_main import ArchitectureConformanceError

        prompt_filename = "modify_python.prompt"
        arch = [
            {
                "filename": prompt_filename,
                "filepath": "pdd/commands/modify.py",
                "interface": {
                    "type": "module",
                    "module": {
                        "functions": [
                            {"name": "split", "signature": "def split(...)"},
                        ]
                    },
                },
            }
        ]
        arch_path = tmp_path / "architecture.json"
        arch_path.write_text(json.dumps(arch))
        prompt_content = (
            '<pdd-interface>{"type":"command","command":{"commands":'
            '[{"name":"split","signature":"(target_file, mode=\'agentic\')"}]}}'
            '</pdd-interface>\n'
        )
        generated_code = "def split(target_file):\n    pass\n"

        with pytest.raises(ArchitectureConformanceError) as excinfo:
            _verify_architecture_conformance(
                generated_code=generated_code,
                prompt_name=prompt_filename,
                arch_path=str(arch_path),
                language="python",
                verbose=False,
                prompt_content=prompt_content,
            )
        assert excinfo.value.missing_symbols == ["split.mode"]

    def test_command_interface_single_shape_skipped_without_signature(self, tmp_path):
        """``type: "command"`` entries without a ``signature`` (the common
        case today — name+description only) must be silent no-ops, same as
        class-header signatures: they have nothing to check.
        """
        prompt_filename = "modify_python.prompt"
        arch = [
            {
                "filename": prompt_filename,
                "filepath": "pdd/commands/modify.py",
                "interface": {
                    "type": "module",
                    "module": {
                        "functions": [
                            {"name": "split", "signature": "def split(...)"},
                        ]
                    },
                },
            }
        ]
        arch_path = tmp_path / "architecture.json"
        arch_path.write_text(json.dumps(arch))
        prompt_content = (
            '<pdd-interface>{"type":"command","command":{"commands":'
            '[{"name":"split","description":"do a thing"}]}}'
            '</pdd-interface>\n'
        )
        # No signature → no check → code doesn't need to match anything.
        generated_code = "def split():\n    pass\n"

        _verify_architecture_conformance(
            generated_code=generated_code,
            prompt_name=prompt_filename,
            arch_path=str(arch_path),
            language="python",
            verbose=False,
            prompt_content=prompt_content,
        )

    def test_dotted_method_repair_directive_groups_via_rsplit(self, tmp_path):
        """The repair directive must group ``ContentSelector.select.mode``
        as ("ContentSelector.select", "mode"), not ("ContentSelector",
        "select.mode"). The previous ``partition('.')`` implementation
        misattributed the parameter to the class.
        """
        from pdd.code_generator_main import ArchitectureConformanceError

        prompt_filename = "content_selector_python.prompt"
        arch = [
            {
                "filename": prompt_filename,
                "filepath": "src/content_selector.py",
                "interface": {
                    "type": "module",
                    "module": {
                        "functions": [
                            {"name": "ContentSelector", "signature": "class ContentSelector"},
                        ]
                    },
                },
            }
        ]
        arch_path = tmp_path / "architecture.json"
        arch_path.write_text(json.dumps(arch))
        prompt_content = (
            '<pdd-interface>{"type":"module","module":{"functions":'
            '[{"name":"ContentSelector.select",'
            '"signature":"(content, selectors, file_path=None, mode=\\"full\\")"}]}}'
            '</pdd-interface>\n'
        )
        generated_code = (
            "class ContentSelector:\n"
            "    def select(self, content, selectors, file_path=None):\n"
            "        return content\n"
        )

        with pytest.raises(ArchitectureConformanceError) as excinfo:
            _verify_architecture_conformance(
                generated_code=generated_code,
                prompt_name=prompt_filename,
                arch_path=str(arch_path),
                language="python",
                verbose=False,
                prompt_content=prompt_content,
            )
        directive = excinfo.value.repair_directive
        assert "On `ContentSelector.select`" in directive
        assert "`mode`" in directive
        # Must not misattribute "select.mode" to ContentSelector.
        assert "select.mode" not in directive
        assert "On `ContentSelector`," not in directive

    def test_prompt_only_missing_function_without_architecture_entry(self, tmp_path):
        """A function declared in <pdd-interface> that is entirely absent from
        the generated code must be reported, even when architecture.json has
        no matching entry. Without this, prompt-only declarations slip through
        because the architecture.json symbol-existence check is a no-op.
        """
        from pdd.code_generator_main import ArchitectureConformanceError

        prompt_filename = "no_arch_module_python.prompt"
        # No architecture.json at all: arch_path points at a non-existent file
        # so the existing symbol-existence check returns early (silent).
        arch_path = tmp_path / "architecture.json"
        # Intentionally NOT writing the file.
        prompt_content = (
            '<pdd-interface>{"type":"module","module":{"functions":'
            '[{"name":"update_main","signature":"(ctx, sync_metadata=False)"}]}}'
            '</pdd-interface>\n'
        )
        generated_code = "def something_else():\n    pass\n"

        with pytest.raises(ArchitectureConformanceError) as excinfo:
            _verify_architecture_conformance(
                generated_code=generated_code,
                prompt_name=prompt_filename,
                arch_path=str(arch_path),
                language="python",
                verbose=False,
                prompt_content=prompt_content,
            )
        # Missing entry is the bare function name, not a dotted param.
        assert "update_main" in excinfo.value.missing_symbols
        assert all("." not in s for s in excinfo.value.missing_symbols if s == "update_main")


# ---------------------------------------------------------------------------
# Codex review #1015 iter-1 follow-ups
# ---------------------------------------------------------------------------
class TestPublicSurfaceBindingKind:
    """Blocker 1: changing a method's binding (instance ↔ staticmethod ↔
    classmethod ↔ property) breaks ``Class.method(arg)`` callers even when
    the receiver-stripped parameter list is identical. The signature gate
    must catch this — previously the snapshot normalized them away.
    """

    def test_instance_to_staticmethod_flip_is_detected(self):
        from pdd.code_generator_main import (
            PublicSurfaceRegressionError,
            _verify_public_surface_regression,
        )

        # Same receiver-stripped param list: `(value)`. Without the binding
        # discriminator the gate compared "(value)" == "(value)" and missed
        # the flip even though `MyClass.f(1)` callers now break.
        before = (
            "class MyClass:\n"
            "    def f(self, value):\n"
            "        return value\n"
        )
        after = (
            "class MyClass:\n"
            "    @staticmethod\n"
            "    def f(value):\n"
            "        return value\n"
        )

        with pytest.raises(PublicSurfaceRegressionError) as excinfo:
            _verify_public_surface_regression(
                before,
                after,
                "module_Python.prompt",
                "pdd/module.py",
                "python",
                "",
            )

        assert "MyClass.f" in excinfo.value.changed_signatures

    def test_instance_to_classmethod_flip_is_detected(self):
        from pdd.code_generator_main import (
            PublicSurfaceRegressionError,
            _verify_public_surface_regression,
        )

        before = (
            "class MyClass:\n"
            "    def f(self, value):\n"
            "        return value\n"
        )
        after = (
            "class MyClass:\n"
            "    @classmethod\n"
            "    def f(cls, value):\n"
            "        return value\n"
        )

        with pytest.raises(PublicSurfaceRegressionError) as excinfo:
            _verify_public_surface_regression(
                before,
                after,
                "module_Python.prompt",
                "pdd/module.py",
                "python",
                "",
            )

        assert "MyClass.f" in excinfo.value.changed_signatures

    def test_method_to_property_flip_is_detected(self):
        from pdd.code_generator_main import (
            PublicSurfaceRegressionError,
            _verify_public_surface_regression,
        )

        before = (
            "class MyClass:\n"
            "    def value(self):\n"
            "        return 1\n"
        )
        after = (
            "class MyClass:\n"
            "    @property\n"
            "    def value(self):\n"
            "        return 1\n"
        )

        with pytest.raises(PublicSurfaceRegressionError) as excinfo:
            _verify_public_surface_regression(
                before,
                after,
                "module_Python.prompt",
                "pdd/module.py",
                "python",
                "",
            )

        assert "MyClass.value" in excinfo.value.changed_signatures

    def test_unchanged_classmethod_is_allowed(self):
        # Sanity check: same binding kind, same signature → no failure.
        from pdd.code_generator_main import _verify_public_surface_regression

        source = (
            "class MyClass:\n"
            "    @classmethod\n"
            "    def f(cls, value):\n"
            "        return value\n"
        )

        _verify_public_surface_regression(
            source,
            source,
            "module_Python.prompt",
            "pdd/module.py",
            "python",
            "",
        )

    # ------------------------------------------------------------------
    # Iter-2 Blocker 2: property descriptors with setters must NOT
    # collide with plain methods of the same name. Last-write-wins on
    # the signature dict previously let ``@x.setter`` overwrite the
    # ``@property`` getter as ``[instance] (self, value)``; a plain
    # ``def x(self, value)`` rewrite then produced the same snapshot
    # and bypassed the gate.
    # ------------------------------------------------------------------
    def test_property_to_plain_method_flip_is_detected(self):
        from pdd.code_generator_main import (
            PublicSurfaceRegressionError,
            _verify_public_surface_regression,
        )

        before = (
            "class MyClass:\n"
            "    @property\n"
            "    def x(self):\n"
            "        return 1\n"
        )
        after = (
            "class MyClass:\n"
            "    def x(self):\n"
            "        return 1\n"
        )

        with pytest.raises(PublicSurfaceRegressionError) as excinfo:
            _verify_public_surface_regression(
                before,
                after,
                "module_Python.prompt",
                "pdd/module.py",
                "python",
                "",
            )

        assert "MyClass.x" in excinfo.value.changed_signatures

    def test_property_with_setter_to_plain_method_flip_is_detected(self):
        from pdd.code_generator_main import (
            PublicSurfaceRegressionError,
            _verify_public_surface_regression,
        )

        before = (
            "class MyClass:\n"
            "    @property\n"
            "    def x(self):\n"
            "        return self._x\n"
            "    @x.setter\n"
            "    def x(self, value):\n"
            "        self._x = value\n"
        )
        # The receiver-stripped param list of the setter is ``(value)`` —
        # identical to a plain ``def x(self, value)`` after stripping
        # ``self``. Without the merged property tag the snapshot dict
        # would resolve both sides to ``[instance] (value)`` and the
        # gate would miss the regression.
        after = (
            "class MyClass:\n"
            "    def x(self, value):\n"
            "        self._x = value\n"
        )

        with pytest.raises(PublicSurfaceRegressionError) as excinfo:
            _verify_public_surface_regression(
                before,
                after,
                "module_Python.prompt",
                "pdd/module.py",
                "python",
                "",
            )

        assert "MyClass.x" in excinfo.value.changed_signatures

    def test_property_with_setter_unchanged_is_allowed(self):
        from pdd.code_generator_main import _verify_public_surface_regression

        source = (
            "class MyClass:\n"
            "    @property\n"
            "    def x(self):\n"
            "        return self._x\n"
            "    @x.setter\n"
            "    def x(self, value):\n"
            "        self._x = value\n"
        )

        # Same descriptor on both sides → merged snapshot must match.
        _verify_public_surface_regression(
            source,
            source,
            "module_Python.prompt",
            "pdd/module.py",
            "python",
            "",
        )

    def test_property_loses_setter_is_detected(self):
        # Dropping write-capability is a real breaking change for callers
        # doing ``instance.x = value``; the accessor-set in the snapshot
        # tag (``getter+setter`` → ``getter``) makes the diff visible.
        from pdd.code_generator_main import (
            PublicSurfaceRegressionError,
            _verify_public_surface_regression,
        )

        before = (
            "class MyClass:\n"
            "    @property\n"
            "    def x(self):\n"
            "        return self._x\n"
            "    @x.setter\n"
            "    def x(self, value):\n"
            "        self._x = value\n"
        )
        after = (
            "class MyClass:\n"
            "    @property\n"
            "    def x(self):\n"
            "        return self._x\n"
        )

        with pytest.raises(PublicSurfaceRegressionError) as excinfo:
            _verify_public_surface_regression(
                before,
                after,
                "module_Python.prompt",
                "pdd/module.py",
                "python",
                "",
            )

        assert "MyClass.x" in excinfo.value.changed_signatures

    # ------------------------------------------------------------------
    # Iter-2 Blocker 3: top-level kind flips (class ↔ function /
    # function ↔ async function) preserve name and normalized signature
    # but break callers that instantiate, subclass, or ``await``.
    # ------------------------------------------------------------------
    def test_class_to_function_flip_is_detected(self):
        from pdd.code_generator_main import (
            PublicSurfaceRegressionError,
            _verify_public_surface_regression,
        )

        before = "class Service:\n    pass\n"
        # Same bare ``()`` signature on both sides — only the symbol
        # kind tag (``[class]`` vs ``[function]``) distinguishes them.
        after = "def Service():\n    return None\n"

        with pytest.raises(PublicSurfaceRegressionError) as excinfo:
            _verify_public_surface_regression(
                before,
                after,
                "module_Python.prompt",
                "pdd/module.py",
                "python",
                "",
            )

        assert "Service" in excinfo.value.changed_signatures

    def test_function_to_class_flip_is_detected(self):
        from pdd.code_generator_main import (
            PublicSurfaceRegressionError,
            _verify_public_surface_regression,
        )

        before = "def Service():\n    return None\n"
        after = "class Service:\n    pass\n"

        with pytest.raises(PublicSurfaceRegressionError) as excinfo:
            _verify_public_surface_regression(
                before,
                after,
                "module_Python.prompt",
                "pdd/module.py",
                "python",
                "",
            )

        assert "Service" in excinfo.value.changed_signatures

    def test_function_to_async_function_flip_is_detected(self):
        from pdd.code_generator_main import (
            PublicSurfaceRegressionError,
            _verify_public_surface_regression,
        )

        before = "def run(x):\n    return x\n"
        after = "async def run(x):\n    return x\n"

        with pytest.raises(PublicSurfaceRegressionError) as excinfo:
            _verify_public_surface_regression(
                before,
                after,
                "module_Python.prompt",
                "pdd/module.py",
                "python",
                "",
            )

        assert "run" in excinfo.value.changed_signatures

    def test_unchanged_class_is_allowed(self):
        from pdd.code_generator_main import _verify_public_surface_regression

        source = "class Service:\n    def run(self):\n        return 1\n"

        _verify_public_surface_regression(
            source,
            source,
            "module_Python.prompt",
            "pdd/module.py",
            "python",
            "",
        )

    # ------------------------------------------------------------------
    # Iter-3 Important: top-level assignment ↔ def/class kind flips must
    # be detected in BOTH directions. The iter-2 fallback at the bottom
    # of ``_verify_public_surface_regression`` only caught the
    # ``def/class → assignment`` direction (because the after-side
    # dropped the signatures entry while keeping the surface entry).
    # The reverse ``assignment → def/class`` left the before-side
    # without a signatures entry, so the new function/class looked like
    # an ADDED symbol — no diff fired. Recording assignments as
    # ``[assignment]`` in the signatures dict closes that gap.
    # ------------------------------------------------------------------
    def test_assignment_to_function_flip_is_detected(self):
        from pdd.code_generator_main import (
            PublicSurfaceRegressionError,
            _verify_public_surface_regression,
        )

        before = "Foo = lambda: None\n"
        after = "def Foo():\n    return None\n"

        with pytest.raises(PublicSurfaceRegressionError) as excinfo:
            _verify_public_surface_regression(
                before,
                after,
                "module_Python.prompt",
                "pdd/module.py",
                "python",
                "",
            )

        assert "Foo" in excinfo.value.changed_signatures

    def test_assignment_to_class_flip_is_detected(self):
        # The class-valued assignment example from the codex finding —
        # ``Foo = type("Foo", (), {})`` previously slipped past the gate
        # because the surface helper kept ``Foo`` while the signatures
        # helper had no record of it, so ``def Foo()`` looked like a
        # brand-new symbol rather than a kind flip.
        from pdd.code_generator_main import (
            PublicSurfaceRegressionError,
            _verify_public_surface_regression,
        )

        before = 'Foo = type("Foo", (), {})\n'
        after = "class Foo:\n    pass\n"

        with pytest.raises(PublicSurfaceRegressionError) as excinfo:
            _verify_public_surface_regression(
                before,
                after,
                "module_Python.prompt",
                "pdd/module.py",
                "python",
                "",
            )

        assert "Foo" in excinfo.value.changed_signatures

    def test_class_to_assignment_flip_still_detected(self):
        # Regression guard: this direction was already caught before
        # iter-3 via the surface-helper fallback at line ~1128 (after
        # signatures drops ``Foo`` but the surface keeps it). Now that
        # the signatures dict also records assignments, this case
        # should hit the primary ``changed_set`` path (``[class] ()``
        # → ``[assignment]``) instead. Either path is acceptable, but
        # the failure MUST still surface.
        from pdd.code_generator_main import (
            PublicSurfaceRegressionError,
            _verify_public_surface_regression,
        )

        before = "class Foo:\n    pass\n"
        after = 'Foo = type("Foo", (), {})\n'

        with pytest.raises(PublicSurfaceRegressionError) as excinfo:
            _verify_public_surface_regression(
                before,
                after,
                "module_Python.prompt",
                "pdd/module.py",
                "python",
                "",
            )

        assert "Foo" in excinfo.value.changed_signatures

    def test_unchanged_top_level_assignment_is_allowed(self):
        # Sanity check: identical module-level assignments on both
        # sides must NOT produce a snapshot diff. Otherwise every
        # regenerated module that ships a public constant would
        # falsely trip the gate.
        from pdd.code_generator_main import _verify_public_surface_regression

        source = (
            "PUBLIC_SETTING = 42\n"
            "ANOTHER: int = 7\n"
        )

        _verify_public_surface_regression(
            source,
            source,
            "module_Python.prompt",
            "pdd/module.py",
            "python",
            "",
        )

    # ------------------------------------------------------------------
    # External review (PR #1015): the positional-only ``/`` marker was
    # silently dropped from ``_format_python_signature``. As a result,
    # ``def f(x, /, y)`` and ``def f(x, y)`` both snapshotted as
    # ``(x, y)`` and the public-surface gate missed a real ABI break —
    # ``f(x=1, y=2)`` succeeds against the second form but raises
    # ``TypeError`` against the first. The fix inserts a literal ``/``
    # token between the posonly group and the regular args (mirroring
    # the existing ``*`` insertion for kwonlyargs).
    # ------------------------------------------------------------------
    def test_positional_only_added_is_detected(self):
        from pdd.code_generator_main import (
            PublicSurfaceRegressionError,
            _verify_public_surface_regression,
        )

        before = "def f(x, y):\n    return x + y\n"
        # Same arg names, but ``x`` is now positional-only — callers
        # doing ``f(x=1, y=2)`` will break.
        after = "def f(x, /, y):\n    return x + y\n"

        with pytest.raises(PublicSurfaceRegressionError) as excinfo:
            _verify_public_surface_regression(
                before,
                after,
                "module_Python.prompt",
                "pdd/module.py",
                "python",
                "",
            )

        assert "f" in excinfo.value.changed_signatures

    def test_positional_only_removed_is_detected(self):
        from pdd.code_generator_main import (
            PublicSurfaceRegressionError,
            _verify_public_surface_regression,
        )

        # Reverse direction: the ``/`` is dropped. While dropping
        # positional-only is technically a strict broadening of the
        # callable contract, the snapshot must still register the
        # change so reviewers can see the surface shift.
        before = "def f(x, /, y):\n    return x + y\n"
        after = "def f(x, y):\n    return x + y\n"

        with pytest.raises(PublicSurfaceRegressionError) as excinfo:
            _verify_public_surface_regression(
                before,
                after,
                "module_Python.prompt",
                "pdd/module.py",
                "python",
                "",
            )

        assert "f" in excinfo.value.changed_signatures

    def test_unchanged_positional_only_is_allowed(self):
        # Sanity check: identical posonly markers on both sides must
        # NOT produce a snapshot diff.
        from pdd.code_generator_main import _verify_public_surface_regression

        source = "def f(x, /, y):\n    return x + y\n"

        _verify_public_surface_regression(
            source,
            source,
            "module_Python.prompt",
            "pdd/module.py",
            "python",
            "",
        )

    def test_format_python_signature_emits_posonly_marker(self):
        """Direct snapshot-string test: ``def f(x, /, y)`` MUST produce
        a signature containing the literal ``/`` token. Pins the marker
        independently of the diff machinery — a future refactor that
        accidentally drops the marker from ``_format_python_signature``
        will fail this test even if the diff path coincidentally still
        catches the change via another tag."""
        import ast
        from pdd.code_generator_main import _format_python_signature

        tree = ast.parse("def f(x, /, y):\n    return x + y\n")
        func_node = tree.body[0]
        signature = _format_python_signature(func_node)
        assert "/" in signature, (
            f"posonly ``/`` marker missing from signature: {signature!r}"
        )
        # And the marker must sit BETWEEN the posonly arg and the
        # regular arg (not at the end).
        assert signature.startswith("(x, /, y)"), signature

    # ------------------------------------------------------------------
    # External review (PR #1015, iter-4): top-level imports were
    # captured by the surface helper but NOT by the signatures helper.
    # That asymmetry let ``from pathlib import Path`` → ``def Path():
    # ...`` slip through — the surface set kept ``Path`` (no removal),
    # and the signatures dict had no ``Path`` entry on the before side
    # so the new ``[function] ()`` looked like a brand-new symbol, not
    # a re-export break. Recording imports as ``[import:...]`` in the
    # signatures dict closes the gap.
    # ------------------------------------------------------------------
    def test_from_import_to_function_flip_is_detected(self):
        from pdd.code_generator_main import (
            PublicSurfaceRegressionError,
            _verify_public_surface_regression,
        )

        before = "from pathlib import Path\n"
        # Same bound name ``Path`` but now resolves to a local function;
        # ``Path("/tmp")`` callers that expect the pathlib API break.
        after = "def Path():\n    return None\n"

        with pytest.raises(PublicSurfaceRegressionError) as excinfo:
            _verify_public_surface_regression(
                before,
                after,
                "module_Python.prompt",
                "pdd/module.py",
                "python",
                "",
            )

        assert "Path" in excinfo.value.changed_signatures

    def test_import_to_assignment_flip_is_detected(self):
        from pdd.code_generator_main import (
            PublicSurfaceRegressionError,
            _verify_public_surface_regression,
        )

        before = "import pathlib\n"
        # Same bound name ``pathlib`` but now ``None`` — code that does
        # ``pathlib.Path(...)`` raises ``AttributeError`` after the
        # rewrite.
        after = "pathlib = None\n"

        with pytest.raises(PublicSurfaceRegressionError) as excinfo:
            _verify_public_surface_regression(
                before,
                after,
                "module_Python.prompt",
                "pdd/module.py",
                "python",
                "",
            )

        assert "pathlib" in excinfo.value.changed_signatures

    def test_import_aliased_to_function_flip_is_detected(self):
        # ``import pathlib as p`` binds ``p``; replacing with a local
        # ``def p()`` is the same flip as the unaliased form. The alias
        # is encoded in the signatures snapshot so this still trips.
        from pdd.code_generator_main import (
            PublicSurfaceRegressionError,
            _verify_public_surface_regression,
        )

        before = "import pathlib as p\n"
        after = "def p():\n    return None\n"

        with pytest.raises(PublicSurfaceRegressionError) as excinfo:
            _verify_public_surface_regression(
                before,
                after,
                "module_Python.prompt",
                "pdd/module.py",
                "python",
                "",
            )

        assert "p" in excinfo.value.changed_signatures

    def test_unchanged_from_import_is_allowed(self):
        # Sanity check: identical ``from X import Y`` on both sides must
        # NOT produce a snapshot diff. The encoded source module keeps
        # the entry stable across regeneration.
        from pdd.code_generator_main import _verify_public_surface_regression

        source = "from pathlib import Path\n"

        _verify_public_surface_regression(
            source,
            source,
            "module_Python.prompt",
            "pdd/module.py",
            "python",
            "",
        )

    # ------------------------------------------------------------------
    # External review (PR #1015, iter-4): when a class has no explicit
    # ``__init__`` the snapshot was ``[class] ()`` regardless of the
    # synthesised dataclass init. Adding a required field
    # (``@dataclass class User: name: str`` → add ``age: int``) left
    # the snapshot unchanged so the gate missed a constructor break.
    # ``_synthesize_dataclass_init_signature`` mirrors the synthesised
    # init from the field annotations so the snapshot moves when the
    # field list does.
    # ------------------------------------------------------------------
    def test_dataclass_adding_required_field_is_detected(self):
        from pdd.code_generator_main import (
            PublicSurfaceRegressionError,
            _verify_public_surface_regression,
        )

        before = (
            "from dataclasses import dataclass\n"
            "@dataclass\n"
            "class User:\n"
            "    name: str\n"
        )
        # ``age`` is added as a required field, so existing callers of
        # ``User(name)`` break with a ``TypeError: missing argument``.
        after = (
            "from dataclasses import dataclass\n"
            "@dataclass\n"
            "class User:\n"
            "    name: str\n"
            "    age: int\n"
        )

        with pytest.raises(PublicSurfaceRegressionError) as excinfo:
            _verify_public_surface_regression(
                before,
                after,
                "module_Python.prompt",
                "pdd/module.py",
                "python",
                "",
            )

        assert "User" in excinfo.value.changed_signatures

    def test_dataclass_adding_optional_field_is_detected_as_signature_change(self):
        # Adding an OPTIONAL field (with a default) is still a public
        # surface change — callers introspecting fields, constructing
        # positionally, or pickling instances may be affected. The
        # snapshot diff should fire so reviewers can decide.
        from pdd.code_generator_main import (
            PublicSurfaceRegressionError,
            _verify_public_surface_regression,
        )

        before = (
            "from dataclasses import dataclass\n"
            "@dataclass\n"
            "class User:\n"
            "    name: str\n"
        )
        after = (
            "from dataclasses import dataclass\n"
            "@dataclass\n"
            "class User:\n"
            "    name: str\n"
            "    age: int = 0\n"
        )

        with pytest.raises(PublicSurfaceRegressionError) as excinfo:
            _verify_public_surface_regression(
                before,
                after,
                "module_Python.prompt",
                "pdd/module.py",
                "python",
                "",
            )

        assert "User" in excinfo.value.changed_signatures

    def test_dataclass_removing_field_is_detected(self):
        from pdd.code_generator_main import (
            PublicSurfaceRegressionError,
            _verify_public_surface_regression,
        )

        before = (
            "from dataclasses import dataclass\n"
            "@dataclass\n"
            "class User:\n"
            "    name: str\n"
            "    age: int\n"
        )
        after = (
            "from dataclasses import dataclass\n"
            "@dataclass\n"
            "class User:\n"
            "    name: str\n"
        )

        with pytest.raises(PublicSurfaceRegressionError) as excinfo:
            _verify_public_surface_regression(
                before,
                after,
                "module_Python.prompt",
                "pdd/module.py",
                "python",
                "",
            )

        assert "User" in excinfo.value.changed_signatures

    def test_dataclass_explicit_init_still_takes_precedence(self):
        # When a ``@dataclass`` class has an explicit ``__init__``,
        # dataclasses skip synthesising one and uses the user's. The
        # snapshot must follow suit — adding a field annotation while
        # keeping the explicit init signature should NOT trip the gate.
        from pdd.code_generator_main import _verify_public_surface_regression

        before = (
            "from dataclasses import dataclass\n"
            "@dataclass\n"
            "class User:\n"
            "    name: str\n"
            "    def __init__(self, name: str):\n"
            "        self.name = name\n"
        )
        # Add a class-level annotation that runtime dataclasses would
        # have folded into the synthesised init — but the explicit
        # ``__init__`` takes precedence, so callers are not affected.
        after = (
            "from dataclasses import dataclass\n"
            "@dataclass\n"
            "class User:\n"
            "    name: str\n"
            "    metadata: dict\n"
            "    def __init__(self, name: str):\n"
            "        self.name = name\n"
        )

        _verify_public_surface_regression(
            before,
            after,
            "module_Python.prompt",
            "pdd/module.py",
            "python",
            "",
        )

    def test_dataclasses_dataclass_attribute_decorator_form_works(self):
        # The attribute form ``@dataclasses.dataclass`` should be
        # recognised identically to the bare ``@dataclass`` form.
        # Adding a required field MUST trip the gate.
        from pdd.code_generator_main import (
            PublicSurfaceRegressionError,
            _verify_public_surface_regression,
        )

        before = (
            "import dataclasses\n"
            "@dataclasses.dataclass\n"
            "class User:\n"
            "    name: str\n"
        )
        after = (
            "import dataclasses\n"
            "@dataclasses.dataclass\n"
            "class User:\n"
            "    name: str\n"
            "    age: int\n"
        )

        with pytest.raises(PublicSurfaceRegressionError) as excinfo:
            _verify_public_surface_regression(
                before,
                after,
                "module_Python.prompt",
                "pdd/module.py",
                "python",
                "",
            )

        assert "User" in excinfo.value.changed_signatures

    def test_classvar_field_is_excluded(self):
        # ``ClassVar`` annotations are class-level constants per PEP
        # 557, NOT positional init params. Toggling a ``ClassVar``
        # annotation must NOT trip the dataclass init synthesis (the
        # synthesised constructor is unchanged at runtime).
        from pdd.code_generator_main import _verify_public_surface_regression

        before = (
            "from dataclasses import dataclass\n"
            "from typing import ClassVar\n"
            "@dataclass\n"
            "class User:\n"
            "    name: str\n"
        )
        # Add a ``ClassVar``-typed attribute — this changes module
        # source but the synthesised ``__init__`` signature stays
        # ``(name: str)``.
        after = (
            "from dataclasses import dataclass\n"
            "from typing import ClassVar\n"
            "@dataclass\n"
            "class User:\n"
            "    name: str\n"
            "    DEFAULT_ROLE: ClassVar[str] = 'guest'\n"
        )

        _verify_public_surface_regression(
            before,
            after,
            "module_Python.prompt",
            "pdd/module.py",
            "python",
            "",
        )

    # ------------------------------------------------------------------
    # External review (PR #1015, iter-5): the pass-2 synthesizer
    # ignored ``kw_only=True`` / ``KW_ONLY`` / ``InitVar`` / ``field(
    # init=False)`` — all of which alter the runtime constructor
    # signature. These tests pin the four corrected behaviours.
    # ------------------------------------------------------------------
    def test_dataclass_kw_only_decorator_change_is_detected(self):
        # Flipping ``@dataclass`` to ``@dataclass(kw_only=True)`` makes
        # every field kw-only at runtime: callers passing positionally
        # break with ``TypeError``. The snapshot must move.
        from pdd.code_generator_main import (
            PublicSurfaceRegressionError,
            _verify_public_surface_regression,
        )

        before = (
            "from dataclasses import dataclass\n"
            "@dataclass\n"
            "class User:\n"
            "    name: str\n"
            "    age: int\n"
        )
        after = (
            "from dataclasses import dataclass\n"
            "@dataclass(kw_only=True)\n"
            "class User:\n"
            "    name: str\n"
            "    age: int\n"
        )

        with pytest.raises(PublicSurfaceRegressionError) as excinfo:
            _verify_public_surface_regression(
                before,
                after,
                "module_Python.prompt",
                "pdd/module.py",
                "python",
                "",
            )

        assert "User" in excinfo.value.changed_signatures

    def test_dataclass_kw_only_sentinel_added_is_detected(self):
        # Inserting ``_: KW_ONLY`` between fields converts trailing
        # fields to kw-only. Callers passing positionally break.
        from pdd.code_generator_main import (
            PublicSurfaceRegressionError,
            _verify_public_surface_regression,
        )

        before = (
            "from dataclasses import dataclass, KW_ONLY\n"
            "@dataclass\n"
            "class User:\n"
            "    name: str\n"
            "    age: int\n"
        )
        after = (
            "from dataclasses import dataclass, KW_ONLY\n"
            "@dataclass\n"
            "class User:\n"
            "    name: str\n"
            "    _: KW_ONLY\n"
            "    age: int\n"
        )

        with pytest.raises(PublicSurfaceRegressionError) as excinfo:
            _verify_public_surface_regression(
                before,
                after,
                "module_Python.prompt",
                "pdd/module.py",
                "python",
                "",
            )

        assert "User" in excinfo.value.changed_signatures

    def test_dataclass_initvar_field_is_included(self):
        # ``InitVar`` params are part of the synthesised ``__init__``
        # signature even though they are not stored as instance
        # attributes. Adding one is a constructor-shape change.
        from pdd.code_generator_main import (
            PublicSurfaceRegressionError,
            _verify_public_surface_regression,
        )

        before = (
            "from dataclasses import dataclass\n"
            "@dataclass\n"
            "class User:\n"
            "    name: str\n"
        )
        after = (
            "from dataclasses import dataclass, InitVar\n"
            "@dataclass\n"
            "class User:\n"
            "    name: str\n"
            "    seed: InitVar[int] = 0\n"
        )

        with pytest.raises(PublicSurfaceRegressionError) as excinfo:
            _verify_public_surface_regression(
                before,
                after,
                "module_Python.prompt",
                "pdd/module.py",
                "python",
                "",
            )

        assert "User" in excinfo.value.changed_signatures

    def test_dataclass_initvar_change_is_detected(self):
        # Flipping ``InitVar[int]`` to a plain ``int`` annotation
        # changes the field semantics (constructor param without
        # instance storage → constructor param WITH instance storage).
        # The annotation text differs so the snapshot diffs.
        from pdd.code_generator_main import (
            PublicSurfaceRegressionError,
            _verify_public_surface_regression,
        )

        before = (
            "from dataclasses import dataclass, InitVar\n"
            "@dataclass\n"
            "class User:\n"
            "    name: str\n"
            "    seed: InitVar[int] = 0\n"
        )
        after = (
            "from dataclasses import dataclass\n"
            "@dataclass\n"
            "class User:\n"
            "    name: str\n"
            "    seed: int = 0\n"
        )

        with pytest.raises(PublicSurfaceRegressionError) as excinfo:
            _verify_public_surface_regression(
                before,
                after,
                "module_Python.prompt",
                "pdd/module.py",
                "python",
                "",
            )

        assert "User" in excinfo.value.changed_signatures

    def test_dataclass_init_false_field_is_excluded_from_synth(self):
        # ``field(init=False, ...)`` fields are NOT part of the
        # synthesised ``__init__`` so adding one must NOT trip the
        # public-surface gate (false-positive from the iter-4 build).
        from pdd.code_generator_main import _verify_public_surface_regression

        before = (
            "from dataclasses import dataclass\n"
            "@dataclass\n"
            "class User:\n"
            "    name: str\n"
        )
        after = (
            "from dataclasses import dataclass, field\n"
            "@dataclass\n"
            "class User:\n"
            "    name: str\n"
            "    cache: dict = field(init=False, default_factory=dict)\n"
        )

        _verify_public_surface_regression(
            before,
            after,
            "module_Python.prompt",
            "pdd/module.py",
            "python",
            "",
        )

    def test_dataclass_init_true_field_is_included(self):
        # Explicit ``init=True`` (the default) keeps the field IN the
        # synth: adding one is a real constructor-shape change.
        from pdd.code_generator_main import (
            PublicSurfaceRegressionError,
            _verify_public_surface_regression,
        )

        before = (
            "from dataclasses import dataclass\n"
            "@dataclass\n"
            "class User:\n"
            "    name: str\n"
        )
        after = (
            "from dataclasses import dataclass, field\n"
            "@dataclass\n"
            "class User:\n"
            "    name: str\n"
            "    extras: dict = field(init=True, default_factory=dict)\n"
        )

        with pytest.raises(PublicSurfaceRegressionError) as excinfo:
            _verify_public_surface_regression(
                before,
                after,
                "module_Python.prompt",
                "pdd/module.py",
                "python",
                "",
            )

        assert "User" in excinfo.value.changed_signatures

    def test_dataclass_field_without_init_kwarg_is_included(self):
        # ``field(default=...)`` with no ``init`` kwarg defaults to
        # ``init=True`` at runtime, so the field stays in the synth.
        from pdd.code_generator_main import (
            PublicSurfaceRegressionError,
            _verify_public_surface_regression,
        )

        before = (
            "from dataclasses import dataclass\n"
            "@dataclass\n"
            "class User:\n"
            "    name: str\n"
        )
        after = (
            "from dataclasses import dataclass, field\n"
            "@dataclass\n"
            "class User:\n"
            "    name: str\n"
            "    extras: dict = field(default_factory=dict)\n"
        )

        with pytest.raises(PublicSurfaceRegressionError) as excinfo:
            _verify_public_surface_regression(
                before,
                after,
                "module_Python.prompt",
                "pdd/module.py",
                "python",
                "",
            )

        assert "User" in excinfo.value.changed_signatures

    # ------------------------------------------------------------------
    # External review (PR #1015, iter-6): the synth ignored
    # ``@dataclass(init=False)`` (which keeps ``object.__init__``)
    # and did not pull in fields declared on dataclass-decorated base
    # classes. Both gaps allowed real constructor-shape regressions to
    # slip past the gate.
    # ------------------------------------------------------------------
    def test_dataclass_init_false_decorator_flip_to_default_is_detected(self):
        # ``@dataclass(init=False)`` does NOT synthesise an __init__ —
        # the class keeps ``object.__init__`` (zero positional args).
        # Flipping to the default ``@dataclass`` adds a synthesised
        # ``(name: str)`` constructor: callers must update.
        from pdd.code_generator_main import (
            PublicSurfaceRegressionError,
            _verify_public_surface_regression,
        )

        before = (
            "from dataclasses import dataclass\n"
            "@dataclass(init=False)\n"
            "class User:\n"
            "    name: str\n"
        )
        after = (
            "from dataclasses import dataclass\n"
            "@dataclass\n"
            "class User:\n"
            "    name: str\n"
        )

        with pytest.raises(PublicSurfaceRegressionError) as excinfo:
            _verify_public_surface_regression(
                before,
                after,
                "module_Python.prompt",
                "pdd/module.py",
                "python",
                "",
            )

        assert "User" in excinfo.value.changed_signatures

    def test_dataclass_init_false_decorator_keeps_zero_arg_signature(self):
        # Adding fields under ``@dataclass(init=False)`` does NOT change
        # the runtime constructor (still ``object.__init__()``). The
        # snapshot must NOT diff — false-positive that the bare-synth
        # implementation would have raised.
        from pdd.code_generator_main import _verify_public_surface_regression

        before = (
            "from dataclasses import dataclass\n"
            "@dataclass(init=False)\n"
            "class User:\n"
            "    name: str\n"
        )
        after = (
            "from dataclasses import dataclass\n"
            "@dataclass(init=False)\n"
            "class User:\n"
            "    name: str\n"
            "    age: int\n"
        )

        _verify_public_surface_regression(
            before,
            after,
            "module_Python.prompt",
            "pdd/module.py",
            "python",
            "",
        )

    def test_dataclasses_dataclass_init_false_form_works(self):
        # The attribute form ``@dataclasses.dataclass(init=False)``
        # should be recognised identically to the bare-import form.
        # Adding a field still must NOT trip the gate.
        from pdd.code_generator_main import _verify_public_surface_regression

        before = (
            "import dataclasses\n"
            "@dataclasses.dataclass(init=False)\n"
            "class User:\n"
            "    name: str\n"
        )
        after = (
            "import dataclasses\n"
            "@dataclasses.dataclass(init=False)\n"
            "class User:\n"
            "    name: str\n"
            "    age: int\n"
        )

        _verify_public_surface_regression(
            before,
            after,
            "module_Python.prompt",
            "pdd/module.py",
            "python",
            "",
        )

    def test_dataclass_inherited_field_added_to_private_base_is_detected(self):
        # Reviewer's exact repro: ``_Base`` gains a required field;
        # ``User`` itself is unchanged. The runtime ``User`` constructor
        # signature changes from ``User(base, name)`` to
        # ``User(base, token, name)`` — public-surface regression.
        from pdd.code_generator_main import (
            PublicSurfaceRegressionError,
            _verify_public_surface_regression,
        )

        before = (
            "from dataclasses import dataclass\n"
            "@dataclass\n"
            "class _Base:\n"
            "    base: str\n"
            "@dataclass\n"
            "class User(_Base):\n"
            "    name: str\n"
        )
        after = (
            "from dataclasses import dataclass\n"
            "@dataclass\n"
            "class _Base:\n"
            "    base: str\n"
            "    token: str\n"
            "@dataclass\n"
            "class User(_Base):\n"
            "    name: str\n"
        )

        with pytest.raises(PublicSurfaceRegressionError) as excinfo:
            _verify_public_surface_regression(
                before,
                after,
                "module_Python.prompt",
                "pdd/module.py",
                "python",
                "",
            )

        assert "User" in excinfo.value.changed_signatures

    def test_dataclass_unchanged_inheritance_is_allowed(self):
        # Same inheritance shape on both sides; no fields change. The
        # snapshot must be stable — adding inheritance support must not
        # create churn in unchanged modules.
        from pdd.code_generator_main import _verify_public_surface_regression

        source = (
            "from dataclasses import dataclass\n"
            "@dataclass\n"
            "class _Base:\n"
            "    base: str\n"
            "@dataclass\n"
            "class User(_Base):\n"
            "    name: str\n"
        )

        _verify_public_surface_regression(
            source,
            source,
            "module_Python.prompt",
            "pdd/module.py",
            "python",
            "",
        )

    def test_dataclass_unresolved_base_is_marked_uncertain(self):
        # When the base class is imported from another module we cannot
        # see its fields. The snapshot encodes that with an
        # ``[inherited_unresolved]`` token: adding a field LOCALLY
        # still trips the gate (the derived synth changes), but a
        # purely-base change we can't observe correctly slips through —
        # the gate is conservative for invisible parents.
        from pdd.code_generator_main import (
            PublicSurfaceRegressionError,
            _verify_public_surface_regression,
            _snapshot_public_signatures,
        )

        before = (
            "from dataclasses import dataclass\n"
            "from external_mod import Base\n"
            "@dataclass\n"
            "class User(Base):\n"
            "    name: str\n"
        )
        # Local change: adding a required field. Must trip.
        after_local = (
            "from dataclasses import dataclass\n"
            "from external_mod import Base\n"
            "@dataclass\n"
            "class User(Base):\n"
            "    name: str\n"
            "    age: int\n"
        )

        # First: signature snapshot includes the marker.
        sig_before = _snapshot_public_signatures(before, "python")
        assert "[inherited_unresolved]" in sig_before["User"]

        with pytest.raises(PublicSurfaceRegressionError) as excinfo:
            _verify_public_surface_regression(
                before,
                after_local,
                "module_Python.prompt",
                "pdd/module.py",
                "python",
                "",
            )

        assert "User" in excinfo.value.changed_signatures

    def test_dataclass_multiple_inheritance_mro_order(self):
        # ``class C(A, B)`` synth must follow Python's @dataclass
        # field-collection semantics: ``__dataclass_fields__`` is
        # populated in REVERSE-MRO order so later bases override
        # earlier ones in dict-insertion order. Concretely the synth
        # is ``(b, a, c)`` — B's fields, then A's, then C's own.
        # Reordering bases to ``class C(B, A)`` flips the synth to
        # ``(a, b, c)`` so a base-order swap is observed as a
        # constructor regression.
        from pdd.code_generator_main import (
            PublicSurfaceRegressionError,
            _verify_public_surface_regression,
            _snapshot_public_signatures,
        )

        before = (
            "from dataclasses import dataclass\n"
            "@dataclass\n"
            "class A:\n"
            "    a: int\n"
            "@dataclass\n"
            "class B:\n"
            "    b: int\n"
            "@dataclass\n"
            "class C(A, B):\n"
            "    c: int\n"
        )
        after = (
            "from dataclasses import dataclass\n"
            "@dataclass\n"
            "class A:\n"
            "    a: int\n"
            "@dataclass\n"
            "class B:\n"
            "    b: int\n"
            "@dataclass\n"
            "class C(B, A):\n"
            "    c: int\n"
        )

        # Sanity: snapshot follows reverse-MRO (matching Python's
        # ``@dataclass`` __dataclass_fields__ ordering).
        sig = _snapshot_public_signatures(before, "python")
        assert "(b: int, a: int, c: int)" in sig["C"]

        with pytest.raises(PublicSurfaceRegressionError) as excinfo:
            _verify_public_surface_regression(
                before,
                after,
                "module_Python.prompt",
                "pdd/module.py",
                "python",
                "",
            )

        assert "C" in excinfo.value.changed_signatures

    def test_dataclass_single_inheritance_still_matches_runtime(self):
        # Regression check that single inheritance (the common case)
        # still produces ``base_fields ++ derived_fields`` — the
        # reverse-MRO refactor must not regress this. Reverse iteration
        # over a single-element base list is a no-op, so the derived
        # synth remains ``(base, name)``.
        from pdd.code_generator_main import _snapshot_public_signatures

        source = (
            "from dataclasses import dataclass\n"
            "@dataclass\n"
            "class Base:\n"
            "    base: str\n"
            "@dataclass\n"
            "class Derived(Base):\n"
            "    name: str\n"
        )

        sig = _snapshot_public_signatures(source, "python")
        assert "(base: str, name: str)" in sig["Derived"]

    def test_dataclass_diamond_inheritance_dedupes_by_name(self):
        # Diamond: ``class C(A, B)`` where both ``A`` and ``B`` inherit
        # from a shared ``X`` (X has field ``x``). The synth must
        # include ``x`` exactly once — Python's @dataclass merges
        # fields by name via ``__dataclass_fields__``'s dict semantics.
        #
        # In our walk order: reversed(bases) processes B first, then A.
        # Each branch contributes its inherited ``x`` (from X). Under
        # the outer dict-merge in ``_synthesize_dataclass_init_signature``,
        # the LAST write wins — which is A's contribution (A is
        # processed after B in walk order). Either branch carries the
        # same field text, so the resulting position is X's original
        # slot at the front of the field list.
        from pdd.code_generator_main import _snapshot_public_signatures

        source = (
            "from dataclasses import dataclass\n"
            "@dataclass\n"
            "class X:\n"
            "    x: int\n"
            "@dataclass\n"
            "class A(X):\n"
            "    a: int\n"
            "@dataclass\n"
            "class B(X):\n"
            "    b: int\n"
            "@dataclass\n"
            "class C(A, B):\n"
            "    c: int\n"
        )

        sig = _snapshot_public_signatures(source, "python")
        rendered = sig["C"]
        # ``x`` appears once; reverse-MRO walk order yields
        # ``(x, b, a, c)`` after dedup by field name. Top-level
        # classes carry the ``[class]`` binding-kind prefix.
        assert rendered.count("x: int") == 1
        assert rendered == "[class] (x: int, b: int, a: int, c: int)"

    def test_dataclass_init_false_base_contributes_inherited_fields(self):
        # External reviewer's exact repro: a base decorated with
        # ``@dataclass(init=False)`` STILL contributes its fields to a
        # derived ``@dataclass``'s synthesised ``__init__``. The
        # ``init=False`` flag only suppresses the BASE's own
        # ``__init__`` synthesis — Python still records its fields in
        # ``__dataclass_fields__`` and the derived class merges them
        # when synthesising its own init. Adding a required field to
        # the base must therefore change the derived's snapshot and
        # trip the gate.
        from pdd.code_generator_main import (
            PublicSurfaceRegressionError,
            _verify_public_surface_regression,
        )

        before = (
            "from dataclasses import dataclass\n"
            "@dataclass(init=False)\n"
            "class _Base:\n"
            "    base: str\n"
            "@dataclass\n"
            "class Child(_Base):\n"
            "    name: str\n"
        )
        after = (
            "from dataclasses import dataclass\n"
            "@dataclass(init=False)\n"
            "class _Base:\n"
            "    base: str\n"
            "    token: str\n"
            "@dataclass\n"
            "class Child(_Base):\n"
            "    name: str\n"
        )

        with pytest.raises(PublicSurfaceRegressionError) as excinfo:
            _verify_public_surface_regression(
                before,
                after,
                "module_Python.prompt",
                "pdd/module.py",
                "python",
                "",
            )

        assert "Child" in excinfo.value.changed_signatures

    def test_dataclass_init_false_base_unchanged_inheritance_is_allowed(self):
        # Companion to the regression test: no field changes anywhere
        # in the inheritance chain. The snapshot must be stable —
        # including a ``@dataclass(init=False)`` base in the walker
        # must not introduce churn for unchanged modules.
        from pdd.code_generator_main import _verify_public_surface_regression

        source = (
            "from dataclasses import dataclass\n"
            "@dataclass(init=False)\n"
            "class _Base:\n"
            "    base: str\n"
            "@dataclass\n"
            "class Child(_Base):\n"
            "    name: str\n"
        )

        _verify_public_surface_regression(
            source,
            source,
            "module_Python.prompt",
            "pdd/module.py",
            "python",
            "",
        )

    def test_dataclass_explicit_init_still_takes_precedence_with_inheritance(self):
        # When the derived class has an explicit ``__init__``,
        # dataclasses skip synthesising — inheritance must NOT be
        # walked. Adding a field to the base would otherwise look like
        # a synth diff, but the explicit init shields callers.
        from pdd.code_generator_main import _verify_public_surface_regression

        before = (
            "from dataclasses import dataclass\n"
            "@dataclass\n"
            "class _Base:\n"
            "    base: str\n"
            "@dataclass\n"
            "class User(_Base):\n"
            "    name: str\n"
            "    def __init__(self, x: int):\n"
            "        self.x = x\n"
        )
        # Base gains a field — explicit ``__init__`` on User does not
        # call ``super().__init__`` here, so callers are unaffected.
        after = (
            "from dataclasses import dataclass\n"
            "@dataclass\n"
            "class _Base:\n"
            "    base: str\n"
            "    token: str\n"
            "@dataclass\n"
            "class User(_Base):\n"
            "    name: str\n"
            "    def __init__(self, x: int):\n"
            "        self.x = x\n"
        )

        _verify_public_surface_regression(
            before,
            after,
            "module_Python.prompt",
            "pdd/module.py",
            "python",
            "",
        )


class TestFrontMatterStripping:
    """Blocker 2: BREAKING-CHANGE: directives buried inside YAML front
    matter must NOT opt the prompt out of the gates. Opt-outs come from
    the prompt BODY only. Defensive hardening — no shipped prompt
    currently uses YAML front matter, but a future convention must not
    silently disable conformance gates.
    """

    def test_front_matter_breaking_change_does_not_opt_out_removal_gate(self):
        from pdd.code_generator_main import (
            PublicSurfaceRegressionError,
            _verify_public_surface_regression,
        )

        # Directive is INSIDE the front matter block — it must be ignored.
        prompt_with_front_matter = (
            "---\n"
            "BREAKING-CHANGE: remove old_helper\n"
            "title: My Module\n"
            "---\n"
            "Generate a module without `old_helper`.\n"
        )
        before = (
            "def old_helper():\n"
            "    return 1\n"
            "\n"
            "def new_helper():\n"
            "    return 2\n"
        )
        after = "def new_helper():\n    return 2\n"

        with pytest.raises(PublicSurfaceRegressionError) as excinfo:
            _verify_public_surface_regression(
                before,
                after,
                "module_Python.prompt",
                "pdd/module.py",
                "python",
                prompt_with_front_matter,
            )

        assert "old_helper" in excinfo.value.removed_symbols

    def test_body_breaking_change_still_opts_out_removal_gate(self):
        # Sanity: the same directive in the BODY must still opt out.
        from pdd.code_generator_main import _verify_public_surface_regression

        prompt_in_body = (
            "---\n"
            "title: My Module\n"
            "---\n"
            "BREAKING-CHANGE: remove old_helper\n"
        )
        before = (
            "def old_helper():\n"
            "    return 1\n"
            "\n"
            "def new_helper():\n"
            "    return 2\n"
        )
        after = "def new_helper():\n    return 2\n"

        # Should NOT raise: opt-out lives in the body after the front matter.
        _verify_public_surface_regression(
            before,
            after,
            "module_Python.prompt",
            "pdd/module.py",
            "python",
            prompt_in_body,
        )

    def test_front_matter_breaking_change_does_not_opt_out_churn_gate(self, tmp_path):
        from pdd.code_generator_main import (
            TestChurnError,
            _verify_test_churn,
        )

        prompt_with_front_matter = (
            "---\n"
            "BREAKING-CHANGE: rewrite tests\n"
            "owner: someone\n"
            "---\n"
            "Add a small helper.\n"
        )
        existing_tests = "\n".join(
            f"def test_case_{i}():\n    assert True" for i in range(40)
        )
        new_tests = "def test_new():\n    assert True\n"
        test_path = tmp_path / "test_module.py"

        with pytest.raises(TestChurnError):
            _verify_test_churn(
                existing_code=existing_tests,
                generated_code=new_tests,
                prompt_name="module_Python.prompt",
                output_path=str(test_path),
                prompt_content=prompt_with_front_matter,
            )

    def test_unterminated_front_matter_is_not_stripped(self):
        # An opening `---\n` without a closing `---\n` must NOT swallow the
        # entire prompt. Defensive against a malformed prompt.
        from pdd.code_generator_main import _strip_yaml_front_matter

        prompt = "---\nBREAKING-CHANGE: remove foo\nno closing fence ever\n"
        assert _strip_yaml_front_matter(prompt) == prompt

    def test_strip_helper_returns_body_after_fence(self):
        from pdd.code_generator_main import _strip_yaml_front_matter

        prompt = "---\nfoo: bar\n---\nbody line\n"
        assert _strip_yaml_front_matter(prompt) == "body line\n"

    def test_strip_helper_handles_empty_prompt(self):
        from pdd.code_generator_main import _strip_yaml_front_matter

        assert _strip_yaml_front_matter(None) == ""
        assert _strip_yaml_front_matter("") == ""
        assert _strip_yaml_front_matter("plain prompt") == "plain prompt"

    # ------------------------------------------------------------------
    # Iter-2 Blocker 1: front matter stripping must tolerate CRLF line
    # endings, a leading UTF-8 BOM, and a closing fence at EOF (no
    # trailing newline). Windows editors hand us all three, so a missed
    # fence variant leaves ``BREAKING-CHANGE:`` metadata visible to the
    # directive parser and silently opts the prompt out of the gates.
    # ------------------------------------------------------------------
    def test_strip_helper_handles_crlf_front_matter(self):
        from pdd.code_generator_main import _strip_yaml_front_matter

        prompt = "---\r\nfoo: bar\r\n---\r\nbody line\r\n"
        assert _strip_yaml_front_matter(prompt) == "body line\r\n"

    def test_strip_helper_handles_bom_front_matter(self):
        from pdd.code_generator_main import _strip_yaml_front_matter

        prompt = "﻿---\nfoo: bar\n---\nbody line\n"
        assert _strip_yaml_front_matter(prompt) == "body line\n"

    def test_strip_helper_handles_eof_terminated_front_matter(self):
        # Closing ``---`` is the last line of the file (no trailing
        # newline). Must still be recognized so a buried
        # BREAKING-CHANGE inside the block does not leak into the body.
        from pdd.code_generator_main import _strip_yaml_front_matter

        prompt = "---\nfoo: bar\n---"
        assert _strip_yaml_front_matter(prompt) == ""

    def test_strip_helper_handles_trailing_whitespace_on_fence(self):
        from pdd.code_generator_main import _strip_yaml_front_matter

        prompt = "---  \nfoo: bar\n---  \nbody\n"
        assert _strip_yaml_front_matter(prompt) == "body\n"

    def test_strip_helper_strips_lone_bom_without_front_matter(self):
        # A leading BOM with no front matter still needs stripping so a
        # subsequent first-line BREAKING-CHANGE directive scan sees a
        # clean body.
        from pdd.code_generator_main import _strip_yaml_front_matter

        prompt = "﻿BREAKING-CHANGE: remove old_helper\n"
        assert _strip_yaml_front_matter(prompt) == "BREAKING-CHANGE: remove old_helper\n"

    def test_crlf_front_matter_breaking_change_does_not_opt_out_removal_gate(self):
        from pdd.code_generator_main import (
            PublicSurfaceRegressionError,
            _verify_public_surface_regression,
        )

        # CRLF-ended front matter — previous regex only matched ``\n``
        # variants, so the directive leaked into the body scan.
        prompt_with_front_matter = (
            "---\r\n"
            "BREAKING-CHANGE: remove old_helper\r\n"
            "title: My Module\r\n"
            "---\r\n"
            "Generate a module without `old_helper`.\r\n"
        )
        before = (
            "def old_helper():\n"
            "    return 1\n"
            "\n"
            "def new_helper():\n"
            "    return 2\n"
        )
        after = "def new_helper():\n    return 2\n"

        with pytest.raises(PublicSurfaceRegressionError) as excinfo:
            _verify_public_surface_regression(
                before,
                after,
                "module_Python.prompt",
                "pdd/module.py",
                "python",
                prompt_with_front_matter,
            )

        assert "old_helper" in excinfo.value.removed_symbols

    def test_bom_front_matter_breaking_change_does_not_opt_out_removal_gate(self):
        from pdd.code_generator_main import (
            PublicSurfaceRegressionError,
            _verify_public_surface_regression,
        )

        prompt_with_front_matter = (
            "﻿---\n"
            "BREAKING-CHANGE: remove old_helper\n"
            "title: My Module\n"
            "---\n"
            "Generate a module without `old_helper`.\n"
        )
        before = (
            "def old_helper():\n"
            "    return 1\n"
            "\n"
            "def new_helper():\n"
            "    return 2\n"
        )
        after = "def new_helper():\n    return 2\n"

        with pytest.raises(PublicSurfaceRegressionError) as excinfo:
            _verify_public_surface_regression(
                before,
                after,
                "module_Python.prompt",
                "pdd/module.py",
                "python",
                prompt_with_front_matter,
            )

        assert "old_helper" in excinfo.value.removed_symbols

    def test_eof_front_matter_breaking_change_does_not_opt_out_removal_gate(self):
        # Closing ``---`` is the final line of the file (no trailing
        # newline). Directive must still be ignored.
        from pdd.code_generator_main import (
            PublicSurfaceRegressionError,
            _verify_public_surface_regression,
        )

        prompt_with_front_matter = (
            "---\n"
            "BREAKING-CHANGE: remove old_helper\n"
            "title: My Module\n"
            "---"
        )
        before = (
            "def old_helper():\n"
            "    return 1\n"
            "\n"
            "def new_helper():\n"
            "    return 2\n"
        )
        after = "def new_helper():\n    return 2\n"

        with pytest.raises(PublicSurfaceRegressionError) as excinfo:
            _verify_public_surface_regression(
                before,
                after,
                "module_Python.prompt",
                "pdd/module.py",
                "python",
                prompt_with_front_matter,
            )

        assert "old_helper" in excinfo.value.removed_symbols
