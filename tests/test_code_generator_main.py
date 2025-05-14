# Test Plan:
#
# I. Setup and Basic File Operations
#    - test_successful_invocation_with_minimal_params: Basic happy path for full generation (local).
#    - test_prompt_file_not_found: Prompt file path is invalid, expecting early exit.
#    - test_language_detection_error: Prompt file has an unidentifiable extension (via construct_paths).
#    - test_output_file_write_error: Output file cannot be written due to permissions (mock Path.write_text).
#    - test_construct_paths_key_error: Mock construct_paths to return a dict missing a required key.

# II. Incremental Generation Logic
#    A. Original Prompt Source & Output File
#        - test_incremental_with_explicit_original_prompt_success: --original-prompt provided, file exists, output exists, incremental_code_generator succeeds.
#        - test_incremental_with_explicit_original_prompt_file_not_found: --original-prompt provided, but file doesn't exist. Fallback to full.
#        - test_incremental_git_original_prompt_success: No --original-prompt, git provides original, output exists, incremental_code_generator succeeds.
#        - test_incremental_git_original_prompt_not_in_repo: Not a git repo. Fallback to full.
#        - test_incremental_output_file_does_not_exist: Output file for incremental update is missing. Fallback to full.
#    B. Incremental Flag (--incremental)
#        - test_force_incremental_flag_with_success: --incremental set, conditions met, incremental_code_generator respects force_incremental.
#        - test_force_incremental_flag_warns_if_output_missing: --incremental set, output missing. Warns, fallback to full.
#    C. incremental_code_generator Behavior
#        - test_incremental_generator_returns_is_incremental_false: incremental_code_generator suggests full regen. Fallback to full.
#        - test_incremental_generator_raises_exception: incremental_code_generator fails. Fallback to full.
#    D. Git Add Behavior
#        - test_incremental_success_git_add_called: Successful incremental, verify git add attempts.

# III. Full Generation Logic (Cloud and Local)
#    A. Cloud Path (--local is False)
#        - test_full_gen_cloud_success: All cloud steps succeed.
#        - test_full_gen_cloud_env_vars_missing: Firebase/GitHub env vars missing. Fallback to local.
#        - test_full_gen_cloud_auth_fails: get_jwt_token raises AuthError. Fallback to local.
#        - test_full_gen_cloud_requests_post_timeout: requests.post times out. Fallback to local.
#        - test_full_gen_cloud_requests_post_http_error: requests.post raises HTTPError. Fallback to local.
#    B. Local Path
#        - test_full_gen_local_success_forced: --local is True, code_generator succeeds.
#        - test_full_gen_local_success_after_cloud_fallback: Cloud fails, then local code_generator succeeds.
#        - test_full_gen_local_code_generator_fails: local code_generator raises Exception. Returns error state.

# IV. Output and Return Values
#    - test_return_tuple_on_success_full_gen: Correct tuple for successful full generation.
#    - test_return_tuple_on_success_incremental_gen: Correct tuple for successful incremental generation.
#    - test_return_tuple_on_setup_error: Correct tuple if construct_paths fails.
#    - test_no_code_generated_message_if_all_fails: Verify warning if no code produced (and not quiet).

# V. Context and Global Options
#    - test_global_options_passed_to_generators: strength, temperature, time, verbose passed correctly.
#    - test_quiet_option_suppresses_prints: Check a key print message is suppressed with --quiet.

import pytest
import click
import subprocess
import os
from pathlib import Path
from unittest.mock import MagicMock, patch, mock_open, ANY

# Assuming the code under test is in pdd.commands.generate
from pdd.commands.generate import code_generator_main
from pdd.construct_paths import PathConstructionError, LanguageDetectionError
from pdd.get_jwt_token import AuthError

# Mock constants if direct import from `pdd` is problematic in test environment
# For a robust setup, ensure `pdd` is in PYTHONPATH or installed.
try:
    from pdd import DEFAULT_STRENGTH, DEFAULT_TIME
except ImportError:
    DEFAULT_STRENGTH = 0.5
    DEFAULT_TIME = 0.25


@pytest.fixture
def mock_ctx(mocker):
    ctx = MagicMock(spec=click.Context)
    ctx.obj = {
        "verbose": False,
        "quiet": False,
        "force": False,
        "local": False,
        "strength": DEFAULT_STRENGTH,
        "temperature": 0.0,
        "time": DEFAULT_TIME,
    }
    return ctx

@pytest.fixture
def mock_console(mocker):
    return mocker.patch("pdd.commands.generate.Console").return_value

@pytest.fixture
def mock_construct_paths(mocker):
    mock = mocker.patch("pdd.commands.generate.construct_paths")
    # Default successful return
    mock.return_value = (
        {"prompt_file": "def main():\n  print('Hello')"}, # input_strings
        {"output_file": "output/generated_code.py"},     # output_file_paths
        "python"                                         # language
    )
    return mock

@pytest.fixture
def mock_code_generator(mocker):
    mock = mocker.patch("pdd.commands.generate.code_generator")
    mock.return_value = ("# Generated by local full", 0.01, "local_model_gpt4")
    return mock

@pytest.fixture
def mock_incremental_code_generator(mocker):
    mock = mocker.patch("pdd.commands.generate.incremental_code_generator")
    mock.return_value = ("# Generated by incremental", True, 0.005, "inc_model_gpt3")
    return mock

@pytest.fixture
def mock_preprocess(mocker):
    mock = mocker.patch("pdd.commands.generate.preprocess")
    mock.side_effect = lambda prompt, **kwargs: f"processed: {prompt}"
    return mock

@pytest.fixture
def mock_get_jwt_token(mocker):
    # Patch asyncio.run to return a mock that returns the token
    mock_async_run = mocker.patch("asyncio.run")
    mock_async_run.return_value = "test_jwt_token"
    # The actual get_jwt_token function is not directly patched here,
    # but its invocation via asyncio.run is.
    return mock_async_run


@pytest.fixture
def mock_requests_post(mocker):
    mock = mocker.patch("requests.post")
    mock_response = MagicMock()
    mock_response.json.return_value = {
        "generatedCode": "# Generated by cloud",
        "cost": 0.02,
        "modelName": "cloud_model_claude",
    }
    mock_response.raise_for_status.return_value = None
    mock.return_value = mock_response
    return mock

@pytest.fixture
def mock_subprocess_run(mocker):
    return mocker.patch("subprocess.run")

@pytest.fixture
def temp_prompt_file(tmp_path):
    file_path = tmp_path / "test_prompt.py.prompt"
    file_path.write_text("Create a Python hello world function.")
    return str(file_path)

@pytest.fixture
def temp_output_dir(tmp_path):
    output_dir = tmp_path / "output"
    # Don't create it here, let the function do it or construct_paths handle it
    return str(output_dir)


# I. Setup and Basic File Operations

def test_successful_invocation_with_minimal_params_local_forced(
    mock_ctx, temp_prompt_file, temp_output_dir, mock_construct_paths, mock_code_generator, mock_console
):
    mock_ctx.obj["local"] = True
    output_file_path = Path(temp_output_dir) / "generated.py"
    mock_construct_paths.return_value = (
        {"prompt_file": "prompt content"},
        {"output_file": str(output_file_path)},
        "python"
    )

    code, is_inc, cost, model = code_generator_main(
        mock_ctx, temp_prompt_file, str(output_file_path), None, False
    )

    assert code == "# Generated by local full"
    assert not is_inc
    assert cost == 0.01
    assert model == "local_model_gpt4"
    mock_code_generator.assert_called_once()
    assert output_file_path.exists()
    assert output_file_path.read_text() == "# Generated by local full"
    mock_console.print.assert_any_call(f"Generated code saved to: '{output_file_path.resolve()}'")

def test_prompt_file_not_found(mock_ctx, mock_construct_paths, mock_console):
    mock_construct_paths.side_effect = FileNotFoundError("Prompt file does not exist")
    
    code, is_inc, cost, model = code_generator_main(
        mock_ctx, "non_existent.prompt", "output.py", None, False
    )

    assert code == ""
    assert not is_inc
    assert cost == 0.0
    assert model == "error"
    mock_console.print.assert_any_call("[bold red]Error during setup:[/bold red] Prompt file does not exist")

def test_language_detection_error(mock_ctx, temp_prompt_file, mock_construct_paths, mock_console):
    mock_construct_paths.side_effect = LanguageDetectionError("Cannot detect language")

    code, is_inc, cost, model = code_generator_main(
        mock_ctx, temp_prompt_file, "output.py", None, False
    )
    assert model == "error"
    mock_console.print.assert_any_call("[bold red]Error during setup:[/bold red] Cannot detect language")

@patch("pathlib.Path.write_text", side_effect=IOError("Permission denied"))
def test_output_file_write_error(
    mock_write_text, mock_ctx, temp_prompt_file, temp_output_dir, mock_construct_paths, mock_code_generator, mock_console
):
    mock_ctx.obj["local"] = True # Force local to simplify
    output_file_path = Path(temp_output_dir) / "generated.py"
    mock_construct_paths.return_value = (
        {"prompt_file": "prompt content"},
        {"output_file": str(output_file_path)},
        "python"
    )
    
    code, is_inc, cost, model = code_generator_main(
        mock_ctx, temp_prompt_file, str(output_file_path), None, False
    )

    assert code == "# Generated by local full" # Generation happens
    mock_console.print.assert_any_call(f"[bold red]Error writing output file '{output_file_path}':[/bold red] Permission denied")
    # The return tuple still reflects the successful generation attempt

def test_construct_paths_key_error(mock_ctx, temp_prompt_file, mock_construct_paths, mock_console):
    mock_construct_paths.return_value = ({"prompt_file": "content"}, {}, "python") # Missing "output_file"

    code, is_inc, cost, model = code_generator_main(
        mock_ctx, temp_prompt_file, "output.py", None, False
    )
    assert model == "error"
    mock_console.print.assert_any_call("[bold red]Error accessing file paths or content after construct_paths:[/bold red] Missing key 'output_file'")


# II. Incremental Generation Logic

def test_incremental_with_explicit_original_prompt_success(
    mock_ctx, temp_prompt_file, tmp_path, mock_construct_paths, mock_incremental_code_generator, mock_subprocess_run
):
    original_prompt_content = "original prompt"
    original_prompt_file = tmp_path / "original.py.prompt"
    original_prompt_file.write_text(original_prompt_content)

    existing_code_content = "existing code"
    output_file = tmp_path / "output" / "existing_code.py"
    output_file.parent.mkdir(exist_ok=True)
    output_file.write_text(existing_code_content)

    mock_construct_paths.return_value = (
        {"prompt_file": "new prompt content"},
        {"output_file": str(output_file)},
        "python"
    )
    # Simulate being in a git repo for git add
    mock_subprocess_run.side_effect = [
        MagicMock(returncode=0, stdout=str(tmp_path)), # git rev-parse
        MagicMock(returncode=0), # git add prompt
        MagicMock(returncode=0), # git add output
    ]


    code, is_inc, cost, model = code_generator_main(
        mock_ctx, temp_prompt_file, str(output_file), str(original_prompt_file), False
    )

    assert code == "# Generated by incremental"
    assert is_inc
    mock_incremental_code_generator.assert_called_once_with(
        original_prompt=original_prompt_content,
        new_prompt="new prompt content",
        existing_code=existing_code_content,
        language="python",
        strength=ANY, temperature=ANY, time=ANY,
        force_incremental=False,
        verbose=False,
        preprocess_prompt=True
    )
    assert output_file.read_text() == "# Generated by incremental"
    # Check git add calls
    assert mock_subprocess_run.call_count >= 3 # rev-parse + 2 adds
    
    # More specific check for git add calls if needed
    # calls = [
    #     call(['git', 'add', str(Path(temp_prompt_file).resolve())], cwd=tmp_path, check=False),
    #     call(['git', 'add', str(output_file.resolve())], cwd=tmp_path, check=False)
    # ]
    # mock_subprocess_run.assert_has_calls(calls, any_order=True)


def test_incremental_with_explicit_original_prompt_file_not_found(
    mock_ctx, temp_prompt_file, tmp_path, mock_construct_paths, mock_code_generator, mock_console
):
    mock_ctx.obj["local"] = True # Ensure fallback goes to local
    output_file = tmp_path / "output" / "existing_code.py"
    output_file.parent.mkdir(exist_ok=True)
    output_file.write_text("existing code")

    mock_construct_paths.return_value = (
        {"prompt_file": "new prompt content"},
        {"output_file": str(output_file)},
        "python"
    )

    code_generator_main(
        mock_ctx, temp_prompt_file, str(output_file), "non_existent_original.prompt", False
    )
    mock_console.print.assert_any_call("[yellow]Warning: Could not read specified original prompt 'non_existent_original.prompt': [Errno 2] No such file or directory: 'non_existent_original.prompt'. Will perform full generation.[/yellow]")
    mock_code_generator.assert_called_once() # Fallback to full

def test_incremental_git_original_prompt_success(
    mock_ctx, temp_prompt_file, tmp_path, mock_construct_paths, mock_incremental_code_generator, mock_subprocess_run
):
    output_file = tmp_path / "output" / "existing_code.py"
    output_file.parent.mkdir(exist_ok=True)
    output_file.write_text("existing code")

    mock_construct_paths.return_value = (
        {"prompt_file": "new prompt content"},
        {"output_file": str(output_file)},
        "python"
    )
    
    # Simulate git environment
    git_root = tmp_path
    abs_prompt_file = Path(temp_prompt_file).resolve() # Ensure it's resolvable
    
    mock_subprocess_run.side_effect = [
        MagicMock(returncode=0, stdout=str(git_root) + "\n"),  # git rev-parse --show-toplevel
        MagicMock(returncode=0),                             # git ls-files
        MagicMock(returncode=0, stdout="original git prompt"), # git show HEAD:rel_path
        MagicMock(returncode=0, stdout=str(git_root)), # git rev-parse for git add
        MagicMock(returncode=0), # git add prompt
        MagicMock(returncode=0), # git add output
    ]

    code, is_inc, _, _ = code_generator_main(
        mock_ctx, temp_prompt_file, str(output_file), None, False # No explicit original_prompt
    )
    assert is_inc
    mock_incremental_code_generator.assert_called_once()
    assert mock_incremental_code_generator.call_args[1]['original_prompt'] == "original git prompt"


def test_incremental_generator_returns_is_incremental_false(
    mock_ctx, temp_prompt_file, tmp_path, mock_construct_paths, mock_incremental_code_generator, mock_code_generator, mock_console
):
    mock_ctx.obj["local"] = True # Ensure fallback goes to local
    original_prompt_file = tmp_path / "original.py.prompt"
    original_prompt_file.write_text("original")
    output_file = tmp_path / "output" / "existing.py"
    output_file.parent.mkdir(exist_ok=True)
    output_file.write_text("existing")

    mock_construct_paths.return_value = (
        {"prompt_file": "new"}, {"output_file": str(output_file)}, "python"
    )
    mock_incremental_code_generator.return_value = ("# Full regen suggested", False, 0.0, "inc_model_fallback")

    code_generator_main(mock_ctx, temp_prompt_file, str(output_file), str(original_prompt_file), False)
    
    mock_incremental_code_generator.assert_called_once()
    mock_code_generator.assert_called_once() # Fallback to full
    mock_console.print.assert_any_call("[blue]Incremental analysis suggests full regeneration. Proceeding with full generation.[/blue]")


# III. Full Generation Logic

@patch.dict(os.environ, {"REACT_APP_FIREBASE_API_KEY": "test_fb_key", "GITHUB_CLIENT_ID": "test_gh_id"})
def test_full_gen_cloud_success(
    mock_ctx, temp_prompt_file, temp_output_dir, mock_construct_paths, 
    mock_preprocess, mock_get_jwt_token, mock_requests_post, mock_console
):
    output_file_path = Path(temp_output_dir) / "generated_cloud.py"
    mock_construct_paths.return_value = (
        {"prompt_file": "cloud prompt"},
        {"output_file": str(output_file_path)},
        "python"
    )

    code, is_inc, cost, model = code_generator_main(
        mock_ctx, temp_prompt_file, str(output_file_path), None, False
    )

    assert code == "# Generated by cloud"
    assert not is_inc
    assert cost == 0.02
    assert model == "cloud_model_claude"
    mock_preprocess.assert_called_once_with("cloud prompt", recursive=True, double_curly_brackets=True, exclude_keys=[])
    mock_get_jwt_token.assert_called_once() # Checks asyncio.run was called
    mock_requests_post.assert_called_once()
    assert output_file_path.read_text() == "# Generated by cloud"
    mock_console.print.assert_any_call("[green]Cloud code generation successful.[/green]")

@patch.dict(os.environ, {"REACT_APP_FIREBASE_API_KEY": "", "GITHUB_CLIENT_ID": ""}) # Missing keys
def test_full_gen_cloud_env_vars_missing_falls_back_to_local(
    mock_ctx, temp_prompt_file, temp_output_dir, mock_construct_paths, 
    mock_code_generator, mock_console
):
    output_file_path = Path(temp_output_dir) / "generated_local_fallback.py"
    mock_construct_paths.return_value = (
        {"prompt_file": "prompt"}, {"output_file": str(output_file_path)}, "python"
    )

    code_generator_main(mock_ctx, temp_prompt_file, str(output_file_path), None, False)
    
    mock_console.print.assert_any_call("[yellow]Warning: Firebase API key or GitHub Client ID not found in environment. Skipping cloud generation.[/yellow]")
    mock_console.print.assert_any_call("[dim]Falling back to local code generation...[/dim]")
    mock_code_generator.assert_called_once()


@patch.dict(os.environ, {"REACT_APP_FIREBASE_API_KEY": "test_fb_key", "GITHUB_CLIENT_ID": "test_gh_id"})
def test_full_gen_cloud_auth_fails_falls_back_to_local(
    mock_ctx, temp_prompt_file, temp_output_dir, mock_construct_paths, 
    mock_get_jwt_token, mock_code_generator, mock_console
):
    output_file_path = Path(temp_output_dir) / "generated_local_fallback.py"
    mock_construct_paths.return_value = (
        {"prompt_file": "prompt"}, {"output_file": str(output_file_path)}, "python"
    )
    mock_get_jwt_token.side_effect = AuthError("Auth failed") # Mock asyncio.run raising AuthError

    code_generator_main(mock_ctx, temp_prompt_file, str(output_file_path), None, False)
    
    mock_console.print.assert_any_call("[yellow]Cloud authentication failed: Auth failed. Falling back to local generation.[/yellow]")
    mock_code_generator.assert_called_once()

@patch.dict(os.environ, {"REACT_APP_FIREBASE_API_KEY": "test_fb_key", "GITHUB_CLIENT_ID": "test_gh_id"})
def test_full_gen_cloud_requests_post_http_error_falls_back_to_local(
    mock_ctx, temp_prompt_file, temp_output_dir, mock_construct_paths, 
    mock_get_jwt_token, mock_requests_post, mock_code_generator, mock_console
):
    output_file_path = Path(temp_output_dir) / "generated_local_fallback.py"
    mock_construct_paths.return_value = (
        {"prompt_file": "prompt"}, {"output_file": str(output_file_path)}, "python"
    )
    
    http_error_response = MagicMock()
    http_error_response.status_code = 500
    http_error_response.text = "Internal Server Error"
    mock_requests_post.side_effect = requests.exceptions.HTTPError(response=http_error_response)

    code_generator_main(mock_ctx, temp_prompt_file, str(output_file_path), None, False)
    
    mock_console.print.assert_any_call("[yellow]Cloud API error (500): Internal Server Error. Falling back to local generation.[/yellow]")
    mock_code_generator.assert_called_once()


def test_full_gen_local_code_generator_fails(
    mock_ctx, temp_prompt_file, temp_output_dir, mock_construct_paths, mock_code_generator, mock_console
):
    mock_ctx.obj["local"] = True
    output_file_path = Path(temp_output_dir) / "generated_failed.py"
    mock_construct_paths.return_value = (
        {"prompt_file": "prompt"}, {"output_file": str(output_file_path)}, "python"
    )
    mock_code_generator.side_effect = Exception("Local LLM exploded")

    code, is_inc, cost, model = code_generator_main(
        mock_ctx, temp_prompt_file, str(output_file_path), None, False
    )

    assert code == ""
    assert not is_inc
    # Cost might be 0 or some partial cost depending on where exception occurs in real code_generator
    assert model == "local_error"
    mock_console.print.assert_any_call("[bold red]Error during local code generation:[/bold red] Local LLM exploded")
    mock_console.print.assert_any_call("[bold red]Code generation failed. No code was produced.[/bold red]")
    assert not output_file_path.exists() # Should not write if generation fails and content is empty


# IV. Output and Return Values

def test_return_tuple_on_success_full_gen(
    mock_ctx, temp_prompt_file, temp_output_dir, mock_construct_paths, mock_code_generator
):
    mock_ctx.obj["local"] = True
    output_file_path = Path(temp_output_dir) / "generated.py"
    mock_construct_paths.return_value = (
        {"prompt_file": "prompt"}, {"output_file": str(output_file_path)}, "python"
    )
    mock_code_generator.return_value = ("local code", 0.1, "local_m")

    code, is_inc, cost, model_name = code_generator_main(
        mock_ctx, temp_prompt_file, str(output_file_path), None, False
    )
    assert code == "local code"
    assert not is_inc
    assert cost == 0.1
    assert model_name == "local_m"

def test_return_tuple_on_setup_error(mock_ctx, mock_construct_paths):
    mock_construct_paths.side_effect = PathConstructionError("Setup failed")
    code, is_inc, cost, model_name = code_generator_main(
        mock_ctx, "p.prompt", "o.py", None, False
    )
    assert code == ""
    assert not is_inc
    assert cost == 0.0
    assert model_name == "error"


# V. Context and Global Options

def test_global_options_passed_to_generators(
    mock_ctx, temp_prompt_file, temp_output_dir, mock_construct_paths, mock_code_generator
):
    mock_ctx.obj["local"] = True
    mock_ctx.obj["strength"] = 0.8
    mock_ctx.obj["temperature"] = 0.5
    mock_ctx.obj["time"] = 0.7
    mock_ctx.obj["verbose"] = True

    output_file_path = Path(temp_output_dir) / "generated.py"
    mock_construct_paths.return_value = (
        {"prompt_file": "prompt"}, {"output_file": str(output_file_path)}, "python"
    )
    
    code_generator_main(mock_ctx, temp_prompt_file, str(output_file_path), None, False)

    mock_code_generator.assert_called_once_with(
        prompt="prompt",
        language="python",
        strength=0.8,
        temperature=0.5,
        verbose=True # Time param is not directly used by code_generator, but by incremental
    )

def test_quiet_option_suppresses_prints(
    mock_ctx, temp_prompt_file, temp_output_dir, mock_construct_paths, mock_code_generator, mock_console
):
    mock_ctx.obj["local"] = True
    mock_ctx.obj["quiet"] = True
    output_file_path = Path(temp_output_dir) / "generated.py"
    mock_construct_paths.return_value = (
        {"prompt_file": "prompt"}, {"output_file": str(output_file_path)}, "python"
    )

    code_generator_main(mock_ctx, temp_prompt_file, str(output_file_path), None, False)
    
    # Check that a specific normally printed message was NOT printed
    # For example, the "Generated code saved to..." message
    for call_args in mock_console.print.call_args_list:
        assert "Generated code saved to" not in call_args[0][0]
        assert "Performing local code generation" not in call_args[0][0] # This is a [dim] message
