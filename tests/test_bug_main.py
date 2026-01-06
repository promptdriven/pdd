"""
Tests for the `bug_main` function, which handles CLI commands for bug test generation.
"""
import json
import os
import sys
import pytest
from unittest.mock import patch, MagicMock, mock_open
import click
import requests
from click import Context
from rich.console import Console
from pdd import DEFAULT_STRENGTH
from pdd.bug_main import bug_main, CLOUD_REQUEST_TIMEOUT
from pdd.core.cloud import CloudConfig


def _has_cloud_credentials() -> bool:
    """Check if cloud credentials are available for E2E testing."""
    return bool(
        os.environ.get("NEXT_PUBLIC_FIREBASE_API_KEY") and
        os.environ.get("GITHUB_CLIENT_ID")
    )


# Pytest marker for tests that require cloud credentials (but not E2E execution)
requires_cloud = pytest.mark.skipif(
    not _has_cloud_credentials(),
    reason="Cloud credentials not available"
)

# Get the cloud URL for assertions in tests
CLOUD_GENERATE_BUG_TEST_URL = CloudConfig.get_endpoint_url("generateBugTest")

# Constants for mocking
DEFAULT_MOCK_GENERATED_TEST = "def test_bug_fix():\n    assert True"
DEFAULT_MOCK_COST = 0.01
DEFAULT_MOCK_MODEL_NAME = "cloud_model"

@pytest.fixture
def mock_ctx():
    """Fixture to create a mock context object.
    Forces local execution to ensure tests verify local behavior regardless of cloud credentials.
    """
    ctx = MagicMock(spec=Context)
    ctx.obj = {
        'force': False,
        'quiet': False,
        'verbose': False,
        'strength': DEFAULT_STRENGTH,
        'temperature': 0,
        'local': True,  # Force local execution for unit tests
    }
    # Note: 'time' is not in ctx.obj, so bug_main will use DEFAULT_TIME for time_budget
    return ctx

@pytest.fixture
def mock_input_files(tmpdir):
    """Fixture to create temporary input files for testing."""
    prompt_file = tmpdir.join("prompt.prompt")
    code_file = tmpdir.join("code.py")
    program_file = tmpdir.join("program.py")
    current_output = tmpdir.join("current_output.txt")
    desired_output = tmpdir.join("desired_output.txt")

    prompt_file.write("Prompt content")
    code_file.write("Code content")
    program_file.write("Program content")
    current_output.write("Current output content")
    desired_output.write("Desired output content")

    return {
        "prompt_file": str(prompt_file),
        "code_file": str(code_file),
        "program_file": str(program_file),
        "current_output": str(current_output),
        "desired_output": str(desired_output)
    }

def test_bug_main_success(mock_ctx, mock_input_files, tmpdir):
    """Test case for successful execution of bug_main."""
    output_file = str(tmpdir.join("output_test.py"))
    
    with patch('pdd.bug_main.construct_paths') as mock_construct_paths, \
         patch('pdd.bug_main.bug_to_unit_test') as mock_bug_to_unit_test:
        
        # Mock construct_paths
        mock_construct_paths.return_value = (
            {},  # resolved_config
            {
                "prompt_file": "Prompt content",
                "code_file": "Code content",
                "program_file": "Program content",
                "current_output": "Current output content",
                "desired_output": "Desired output content"
            },
            {"output": output_file},
            None # detected_language, not used in this test path as language is provided
        )
        
        # Mock bug_to_unit_test
        mock_bug_to_unit_test.return_value = ("Generated unit test", 0.001, "gpt-4")
        
        # Call the function
        result = bug_main(
            mock_ctx,
            mock_input_files["prompt_file"],
            mock_input_files["code_file"],
            mock_input_files["program_file"],
            mock_input_files["current_output"],
            mock_input_files["desired_output"],
            output=output_file
            # language defaults to "Python" in bug_main
        )
        
        # Assertions
        assert result == ("Generated unit test", 0.001, "gpt-4")
        assert os.path.exists(output_file)
        with open(output_file, 'r') as f:
            assert f.read() == "Generated unit test"

def test_bug_main_no_output(mock_ctx, mock_input_files):
    """Test case for bug_main when no output file is specified."""
    with patch('pdd.bug_main.construct_paths') as mock_construct_paths, \
         patch('pdd.bug_main.bug_to_unit_test') as mock_bug_to_unit_test:
        
        # Mock construct_paths
        mock_construct_paths.return_value = (
            {},  # resolved_config
            {
                "prompt_file": "Prompt content",
                "code_file": "Code content",
                "program_file": "Program content",
                "current_output": "Current output content",
                "desired_output": "Desired output content"
            },
            {"output": None}, # No output file path
            None # detected_language
        )
        
        # Mock bug_to_unit_test
        mock_bug_to_unit_test.return_value = ("Generated unit test", 0.001, "gpt-4")
        
        # Call the function
        result = bug_main(
            mock_ctx,
            mock_input_files["prompt_file"],
            mock_input_files["code_file"],
            mock_input_files["program_file"],
            mock_input_files["current_output"],
            mock_input_files["desired_output"]
            # output is None by default
            # language defaults to "Python"
        )
        
        # Assertions
        assert result == ("Generated unit test", 0.001, "gpt-4")

def test_bug_main_error_handling(mock_ctx, mock_input_files):
    """Test case for error handling in bug_main."""
    with patch('pdd.bug_main.construct_paths') as mock_construct_paths:
        # Mock construct_paths to raise an exception
        mock_construct_paths.side_effect = Exception("Test error")

        # Call the function - now returns error tuple instead of sys.exit(1)
        result = bug_main(
            mock_ctx,
            mock_input_files["prompt_file"],
            mock_input_files["code_file"],
            mock_input_files["program_file"],
            mock_input_files["current_output"],
            mock_input_files["desired_output"]
        )

        # Verify error result tuple is returned
        assert result[0] == ""
        assert result[1] == 0.0
        assert "Error:" in result[2]
        assert "Test error" in result[2]

def test_bug_main_quiet_mode(mock_ctx, mock_input_files):
    """Test case for bug_main in quiet mode."""
    mock_ctx.obj['quiet'] = True
    
    with patch('pdd.bug_main.construct_paths') as mock_construct_paths, \
         patch('pdd.bug_main.bug_to_unit_test') as mock_bug_to_unit_test:
        
        # Mock construct_paths
        mock_construct_paths.return_value = (
            {},  # resolved_config
            {
                "prompt_file": "Prompt content",
                "code_file": "Code content",
                "program_file": "Program content",
                "current_output": "Current output content",
                "desired_output": "Desired output content"
            },
            {"output": None},
            None
        )
        
        # Mock bug_to_unit_test
        mock_bug_to_unit_test.return_value = ("Generated unit test", 0.001, "gpt-4")
        
        # Call the function
        result = bug_main(
            mock_ctx,
            mock_input_files["prompt_file"],
            mock_input_files["code_file"],
            mock_input_files["program_file"],
            mock_input_files["current_output"],
            mock_input_files["desired_output"]
        )
        
        # Assertions
        assert result == ("Generated unit test", 0.001, "gpt-4")

def test_bug_main_different_language(mock_ctx, mock_input_files):
    """Test case for bug_main with a different programming language."""
    with patch('pdd.bug_main.construct_paths') as mock_construct_paths, \
         patch('pdd.bug_main.bug_to_unit_test') as mock_bug_to_unit_test:
        
        # Mock construct_paths
        mock_construct_paths.return_value = (
            {},  # resolved_config
            {
                "prompt_file": "Prompt content",
                "code_file": "Code content",
                "program_file": "Program content",
                "current_output": "Current output content",
                "desired_output": "Desired output content"
            },
            {"output": None},
            "JavaScript" # detected_language from construct_paths if it were to detect
        )
        
        # Mock bug_to_unit_test
        mock_bug_to_unit_test.return_value = ("Generated unit test", 0.001, "gpt-4")
        
        # Call the function
        result = bug_main(
            mock_ctx,
            mock_input_files["prompt_file"],
            mock_input_files["code_file"],
            mock_input_files["program_file"],
            mock_input_files["current_output"],
            mock_input_files["desired_output"],
            language="JavaScript" # Explicitly passing "JavaScript"
        )
        
        # Assertions
        assert result == ("Generated unit test", 0.001, "gpt-4")
        # Verify bug_to_unit_test was called with "JavaScript"
        mock_bug_to_unit_test.assert_called_once()
        args, kwargs = mock_bug_to_unit_test.call_args
        assert args[8] == "JavaScript" # language is the 9th argument (index 8)

def test_bug_main_language_from_construct_paths(mock_ctx, mock_input_files):
    """Test case for bug_main using the language detected by construct_paths when language is None."""
    with patch('pdd.bug_main.construct_paths') as mock_construct_paths, \
         patch('pdd.bug_main.bug_to_unit_test') as mock_bug_to_unit_test:
        
        # Mock construct_paths to return "python" as detected language
        mock_construct_paths.return_value = (
            {},  # resolved_config
            {
                "prompt_file": "Prompt content",
                "code_file": "Code content",
                "program_file": "Program content",
                "current_output": "Current output content",
                "desired_output": "Desired output content"
            },
            {"output": None},
            "python"  # Detected language
        )
        
        # Mock bug_to_unit_test
        mock_bug_to_unit_test.return_value = ("Generated unit test", 0.001, "gpt-4")
        
        # Call the function with language=None
        result = bug_main(
            mock_ctx,
            mock_input_files["prompt_file"],
            mock_input_files["code_file"],
            mock_input_files["program_file"],
            mock_input_files["current_output"],
            mock_input_files["desired_output"],
            language=None  # Explicitly passing None to test this logic
        )
        
        # Verify bug_to_unit_test was called with the language from construct_paths
        mock_bug_to_unit_test.assert_called_once()
        args, kwargs = mock_bug_to_unit_test.call_args
        # Corrected assertion: language is the 9th argument (index 8)
        assert args[8] == "python", "The language parameter should be 'python' from construct_paths, not None"

        # Assertions on the result
        assert result == ("Generated unit test", 0.001, "gpt-4")


# -----------------------------------------------------------------------------
# Cloud Support Tests
# -----------------------------------------------------------------------------

@pytest.fixture
def mock_cloud_ctx():
    """Create a mock Click context configured for cloud execution."""
    ctx = MagicMock(spec=Context)
    ctx.obj = {
        "verbose": False,
        "force": False,
        "quiet": False,
        "local": False,  # Cloud mode
        "time": 0.25,
    }
    return ctx


@pytest.fixture
def mock_get_jwt_token_fixture(monkeypatch):
    """Mock CloudConfig.get_jwt_token for cloud auth."""
    mock = MagicMock(return_value="test_jwt_token")
    monkeypatch.setattr("pdd.bug_main.CloudConfig.get_jwt_token", mock)
    return mock


@pytest.fixture
def mock_requests_post_fixture(monkeypatch):
    """Mock requests.post for cloud API calls."""
    mock = MagicMock()
    mock_response = MagicMock(spec=requests.Response)
    mock_response.json.return_value = {
        "generatedTest": DEFAULT_MOCK_GENERATED_TEST,
        "totalCost": DEFAULT_MOCK_COST,
        "modelName": DEFAULT_MOCK_MODEL_NAME
    }
    mock_response.status_code = 200
    mock_response.raise_for_status = MagicMock()
    mock.return_value = mock_response
    monkeypatch.setattr("pdd.bug_main.requests.post", mock)
    return mock


@pytest.fixture
def mock_rich_console_fixture(monkeypatch):
    """Mock console.print for testing Rich output."""
    mock_console_print = MagicMock()
    monkeypatch.setattr("pdd.bug_main.console.print", mock_console_print)
    return mock_console_print


@pytest.fixture
def mock_cloud_env_vars(monkeypatch):
    """Set required environment variables for cloud authentication."""
    monkeypatch.setenv("NEXT_PUBLIC_FIREBASE_API_KEY", "test_firebase_key")
    monkeypatch.setenv("GITHUB_CLIENT_ID", "test_github_id")


# B. Cloud Execution Tests

def test_bug_main_cloud_success(
    mock_cloud_ctx, mock_get_jwt_token_fixture, mock_requests_post_fixture,
    mock_rich_console_fixture, mock_cloud_env_vars, mock_input_files
):
    """Test successful cloud bug test generation."""
    with patch("pdd.bug_main.construct_paths") as mock_construct_paths:

        mock_construct_paths.return_value = (
            {},  # resolved_config
            {
                "prompt_file": "Prompt content",
                "code_file": "Code content",
                "program_file": "Program content",
                "current_output": "Current output",
                "desired_output": "Desired output"
            },
            {"output": None},
            "python"
        )

        result = bug_main(
            ctx=mock_cloud_ctx,
            prompt_file=mock_input_files["prompt_file"],
            code_file=mock_input_files["code_file"],
            program_file=mock_input_files["program_file"],
            current_output=mock_input_files["current_output"],
            desired_output=mock_input_files["desired_output"],
            output=None,
            language="python"
        )

        assert result[0] == DEFAULT_MOCK_GENERATED_TEST
        assert result[1] == DEFAULT_MOCK_COST
        assert result[2] == DEFAULT_MOCK_MODEL_NAME

        # Verify cloud request was made with correct payload
        mock_get_jwt_token_fixture.assert_called_once()
        mock_requests_post_fixture.assert_called_once()
        call_kwargs = mock_requests_post_fixture.call_args
        assert call_kwargs[0][0] == CLOUD_GENERATE_BUG_TEST_URL
        payload = call_kwargs[1]["json"]
        assert payload["promptContent"] == "Prompt content"
        assert payload["codeContent"] == "Code content"
        assert payload["programContent"] == "Program content"
        assert payload["currentOutput"] == "Current output"
        assert payload["desiredOutput"] == "Desired output"
        assert payload["language"] == "python"


def test_bug_main_cloud_fallback_auth_failure(
    mock_cloud_ctx, mock_get_jwt_token_fixture, mock_requests_post_fixture,
    mock_rich_console_fixture, mock_cloud_env_vars, mock_input_files
):
    """Test fallback to local when cloud auth fails."""
    mock_get_jwt_token_fixture.return_value = None  # Auth failed

    with patch("pdd.bug_main.construct_paths") as mock_construct_paths, \
         patch("pdd.bug_main.bug_to_unit_test") as mock_local_generate:

        mock_construct_paths.return_value = (
            {},
            {
                "prompt_file": "Prompt content",
                "code_file": "Code content",
                "program_file": "Program content",
                "current_output": "Current output",
                "desired_output": "Desired output"
            },
            {"output": None},
            "python"
        )
        mock_local_generate.return_value = ("local_test_code", 0.05, "local_model")

        result = bug_main(
            ctx=mock_cloud_ctx,
            prompt_file=mock_input_files["prompt_file"],
            code_file=mock_input_files["code_file"],
            program_file=mock_input_files["program_file"],
            current_output=mock_input_files["current_output"],
            desired_output=mock_input_files["desired_output"],
            output=None,
            language="python"
        )

        # Should have fallen back to local
        mock_local_generate.assert_called_once()
        mock_requests_post_fixture.assert_not_called()
        assert result[0] == "local_test_code"
        # Check fallback message was printed
        assert any("falling back" in str(call_args[0][0]).lower()
                   for call_args in mock_rich_console_fixture.call_args_list if call_args[0])


def test_bug_main_cloud_fallback_timeout(
    mock_cloud_ctx, mock_get_jwt_token_fixture, mock_requests_post_fixture,
    mock_rich_console_fixture, mock_cloud_env_vars, mock_input_files
):
    """Test fallback to local when cloud request times out."""
    mock_requests_post_fixture.side_effect = requests.exceptions.Timeout("Request timed out")

    with patch("pdd.bug_main.construct_paths") as mock_construct_paths, \
         patch("pdd.bug_main.bug_to_unit_test") as mock_local_generate:

        mock_construct_paths.return_value = (
            {},
            {
                "prompt_file": "Prompt content",
                "code_file": "Code content",
                "program_file": "Program content",
                "current_output": "Current output",
                "desired_output": "Desired output"
            },
            {"output": None},
            "python"
        )
        mock_local_generate.return_value = ("local_test_code", 0.05, "local_model")

        result = bug_main(
            ctx=mock_cloud_ctx,
            prompt_file=mock_input_files["prompt_file"],
            code_file=mock_input_files["code_file"],
            program_file=mock_input_files["program_file"],
            current_output=mock_input_files["current_output"],
            desired_output=mock_input_files["desired_output"],
            output=None,
            language="python"
        )

        mock_local_generate.assert_called_once()
        assert result[0] == "local_test_code"
        assert any("timed out" in str(call_args[0][0]).lower()
                   for call_args in mock_rich_console_fixture.call_args_list if call_args[0])


def test_bug_main_cloud_fallback_5xx_error(
    mock_cloud_ctx, mock_get_jwt_token_fixture, mock_requests_post_fixture,
    mock_rich_console_fixture, mock_cloud_env_vars, mock_input_files
):
    """Test fallback to local on 5xx server error."""
    mock_response = MagicMock(spec=requests.Response)
    mock_response.status_code = 500
    mock_response.text = "Internal Server Error"
    http_error = requests.exceptions.HTTPError(response=mock_response)
    http_error.response = mock_response
    mock_requests_post_fixture.side_effect = http_error

    with patch("pdd.bug_main.construct_paths") as mock_construct_paths, \
         patch("pdd.bug_main.bug_to_unit_test") as mock_local_generate:

        mock_construct_paths.return_value = (
            {},
            {
                "prompt_file": "Prompt content",
                "code_file": "Code content",
                "program_file": "Program content",
                "current_output": "Current output",
                "desired_output": "Desired output"
            },
            {"output": None},
            "python"
        )
        mock_local_generate.return_value = ("local_test_code", 0.05, "local_model")

        result = bug_main(
            ctx=mock_cloud_ctx,
            prompt_file=mock_input_files["prompt_file"],
            code_file=mock_input_files["code_file"],
            program_file=mock_input_files["program_file"],
            current_output=mock_input_files["current_output"],
            desired_output=mock_input_files["desired_output"],
            output=None,
            language="python"
        )

        mock_local_generate.assert_called_once()
        assert result[0] == "local_test_code"


def test_bug_main_cloud_fallback_json_decode_error(
    mock_cloud_ctx, mock_get_jwt_token_fixture, mock_requests_post_fixture,
    mock_rich_console_fixture, mock_cloud_env_vars, mock_input_files
):
    """Test fallback to local when cloud returns invalid JSON."""
    mock_response = MagicMock(spec=requests.Response)
    mock_response.json.side_effect = json.JSONDecodeError("msg", "doc", 0)
    mock_response.status_code = 200
    mock_response.raise_for_status = MagicMock()
    mock_requests_post_fixture.return_value = mock_response
    mock_requests_post_fixture.side_effect = None

    with patch("pdd.bug_main.construct_paths") as mock_construct_paths, \
         patch("pdd.bug_main.bug_to_unit_test") as mock_local_generate:

        mock_construct_paths.return_value = (
            {},
            {
                "prompt_file": "Prompt content",
                "code_file": "Code content",
                "program_file": "Program content",
                "current_output": "Current output",
                "desired_output": "Desired output"
            },
            {"output": None},
            "python"
        )
        mock_local_generate.return_value = ("local_test_code", 0.05, "local_model")

        result = bug_main(
            ctx=mock_cloud_ctx,
            prompt_file=mock_input_files["prompt_file"],
            code_file=mock_input_files["code_file"],
            program_file=mock_input_files["program_file"],
            current_output=mock_input_files["current_output"],
            desired_output=mock_input_files["desired_output"],
            output=None,
            language="python"
        )

        mock_local_generate.assert_called_once()
        assert result[0] == "local_test_code"
        assert any("invalid json" in str(call_args[0][0]).lower()
                   for call_args in mock_rich_console_fixture.call_args_list if call_args[0])


def test_bug_main_cloud_fallback_no_test_returned(
    mock_cloud_ctx, mock_get_jwt_token_fixture, mock_requests_post_fixture,
    mock_rich_console_fixture, mock_cloud_env_vars, mock_input_files
):
    """Test fallback to local when cloud returns no test code."""
    mock_response = MagicMock(spec=requests.Response)
    mock_response.json.return_value = {"totalCost": 0.01, "modelName": "cloud_model"}  # No generatedTest
    mock_response.status_code = 200
    mock_response.raise_for_status = MagicMock()
    mock_requests_post_fixture.return_value = mock_response
    mock_requests_post_fixture.side_effect = None

    with patch("pdd.bug_main.construct_paths") as mock_construct_paths, \
         patch("pdd.bug_main.bug_to_unit_test") as mock_local_generate:

        mock_construct_paths.return_value = (
            {},
            {
                "prompt_file": "Prompt content",
                "code_file": "Code content",
                "program_file": "Program content",
                "current_output": "Current output",
                "desired_output": "Desired output"
            },
            {"output": None},
            "python"
        )
        mock_local_generate.return_value = ("local_test_code", 0.05, "local_model")

        result = bug_main(
            ctx=mock_cloud_ctx,
            prompt_file=mock_input_files["prompt_file"],
            code_file=mock_input_files["code_file"],
            program_file=mock_input_files["program_file"],
            current_output=mock_input_files["current_output"],
            desired_output=mock_input_files["desired_output"],
            output=None,
            language="python"
        )

        mock_local_generate.assert_called_once()
        assert result[0] == "local_test_code"


# C. Non-Recoverable HTTP Error Tests

@pytest.mark.parametrize("status_code, error_message, expected_match", [
    (402, "Insufficient credits", "Insufficient credits"),
    (401, "Invalid token", "Cloud authentication failed"),
    (403, "User not approved", "Access denied"),
    (400, "Invalid request", "Invalid request"),
])
def test_bug_main_cloud_non_recoverable_http_errors(
    status_code, error_message, expected_match,
    mock_cloud_ctx, mock_get_jwt_token_fixture, mock_requests_post_fixture,
    mock_rich_console_fixture, mock_cloud_env_vars, mock_input_files
):
    """Test that HTTP 402, 401, 403, 400 errors raise UsageError instead of falling back."""
    mock_response = MagicMock(spec=requests.Response)
    mock_response.status_code = status_code
    mock_response.text = error_message
    mock_response.json.return_value = {"error": error_message, "currentBalance": 0, "estimatedCost": 0.05}
    http_error = requests.exceptions.HTTPError(response=mock_response)
    http_error.response = mock_response
    mock_requests_post_fixture.side_effect = http_error

    with patch("pdd.bug_main.construct_paths") as mock_construct_paths, \
         patch("pdd.bug_main.bug_to_unit_test") as mock_local_generate:

        mock_construct_paths.return_value = (
            {},
            {
                "prompt_file": "Prompt content",
                "code_file": "Code content",
                "program_file": "Program content",
                "current_output": "Current output",
                "desired_output": "Desired output"
            },
            {"output": None},
            "python"
        )

        with pytest.raises(click.UsageError, match=expected_match):
            bug_main(
                ctx=mock_cloud_ctx,
                prompt_file=mock_input_files["prompt_file"],
                code_file=mock_input_files["code_file"],
                program_file=mock_input_files["program_file"],
                current_output=mock_input_files["current_output"],
                desired_output=mock_input_files["desired_output"],
                output=None,
                language="python"
            )

        # Local generator should NOT have been called
        mock_local_generate.assert_not_called()


def test_bug_main_cloud_insufficient_credits_displays_balance(
    mock_cloud_ctx, mock_get_jwt_token_fixture, mock_requests_post_fixture,
    mock_rich_console_fixture, mock_cloud_env_vars, mock_input_files
):
    """Test that HTTP 402 displays current balance and estimated cost."""
    mock_response = MagicMock(spec=requests.Response)
    mock_response.status_code = 402
    mock_response.text = "Insufficient credits"
    mock_response.json.return_value = {"error": "Insufficient credits", "currentBalance": 0.02, "estimatedCost": 0.05}
    http_error = requests.exceptions.HTTPError(response=mock_response)
    http_error.response = mock_response
    mock_requests_post_fixture.side_effect = http_error

    with patch("pdd.bug_main.construct_paths") as mock_construct_paths:

        mock_construct_paths.return_value = (
            {},
            {
                "prompt_file": "Prompt content",
                "code_file": "Code content",
                "program_file": "Program content",
                "current_output": "Current output",
                "desired_output": "Desired output"
            },
            {"output": None},
            "python"
        )

        with pytest.raises(click.UsageError, match="Insufficient credits"):
            bug_main(
                ctx=mock_cloud_ctx,
                prompt_file=mock_input_files["prompt_file"],
                code_file=mock_input_files["code_file"],
                program_file=mock_input_files["program_file"],
                current_output=mock_input_files["current_output"],
                desired_output=mock_input_files["desired_output"],
                output=None,
                language="python"
            )

        # Check balance info was printed
        printed_messages = [str(call_args[0][0]) for call_args in mock_rich_console_fixture.call_args_list if call_args[0]]
        assert any("0.02" in msg and "0.05" in msg for msg in printed_messages), \
            f"Expected balance/cost info in output. Got: {printed_messages}"


# D. Cloud-Only Mode and Local Mode Tests

def test_bug_main_cloud_only_mode_prevents_fallback(
    mock_cloud_ctx, mock_get_jwt_token_fixture, mock_requests_post_fixture,
    mock_rich_console_fixture, mock_cloud_env_vars, mock_input_files, monkeypatch
):
    """Test that PDD_CLOUD_ONLY=1 prevents fallback to local."""
    monkeypatch.setenv("PDD_CLOUD_ONLY", "1")
    mock_requests_post_fixture.side_effect = requests.exceptions.Timeout("Request timed out")

    with patch("pdd.bug_main.construct_paths") as mock_construct_paths, \
         patch("pdd.bug_main.bug_to_unit_test") as mock_local_generate:

        mock_construct_paths.return_value = (
            {},
            {
                "prompt_file": "Prompt content",
                "code_file": "Code content",
                "program_file": "Program content",
                "current_output": "Current output",
                "desired_output": "Desired output"
            },
            {"output": None},
            "python"
        )

        with pytest.raises(click.UsageError, match="timed out"):
            bug_main(
                ctx=mock_cloud_ctx,
                prompt_file=mock_input_files["prompt_file"],
                code_file=mock_input_files["code_file"],
                program_file=mock_input_files["program_file"],
                current_output=mock_input_files["current_output"],
                desired_output=mock_input_files["desired_output"],
                output=None,
                language="python"
            )

        # Local generator should NOT have been called
        mock_local_generate.assert_not_called()


def test_bug_main_local_mode_skips_cloud(
    mock_cloud_ctx, mock_get_jwt_token_fixture, mock_requests_post_fixture,
    mock_rich_console_fixture, mock_cloud_env_vars, mock_input_files
):
    """Test that local mode skips cloud entirely."""
    mock_cloud_ctx.obj['local'] = True  # Local mode

    with patch("pdd.bug_main.construct_paths") as mock_construct_paths, \
         patch("pdd.bug_main.bug_to_unit_test") as mock_local_generate:

        mock_construct_paths.return_value = (
            {},
            {
                "prompt_file": "Prompt content",
                "code_file": "Code content",
                "program_file": "Program content",
                "current_output": "Current output",
                "desired_output": "Desired output"
            },
            {"output": None},
            "python"
        )
        mock_local_generate.return_value = ("local_test_code", 0.05, "local_model")

        result = bug_main(
            ctx=mock_cloud_ctx,
            prompt_file=mock_input_files["prompt_file"],
            code_file=mock_input_files["code_file"],
            program_file=mock_input_files["program_file"],
            current_output=mock_input_files["current_output"],
            desired_output=mock_input_files["desired_output"],
            output=None,
            language="python"
        )

        # Cloud should not have been called
        mock_get_jwt_token_fixture.assert_not_called()
        mock_requests_post_fixture.assert_not_called()
        # Local generator should have been called
        mock_local_generate.assert_called_once()
        assert result[0] == "local_test_code"


def test_bug_main_cloud_payload_contains_all_params(
    mock_cloud_ctx, mock_get_jwt_token_fixture, mock_requests_post_fixture,
    mock_rich_console_fixture, mock_cloud_env_vars, mock_input_files
):
    """Test that cloud payload contains all required parameters."""
    mock_cloud_ctx.obj['verbose'] = True

    with patch("pdd.bug_main.construct_paths") as mock_construct_paths:

        mock_construct_paths.return_value = (
            {"strength": 0.8, "temperature": 0.5, "time": 0.3},  # resolved_config
            {
                "prompt_file": "Prompt content",
                "code_file": "Code content",
                "program_file": "Program content",
                "current_output": "Current output",
                "desired_output": "Desired output"
            },
            {"output": None},
            "python"
        )

        bug_main(
            ctx=mock_cloud_ctx,
            prompt_file=mock_input_files["prompt_file"],
            code_file=mock_input_files["code_file"],
            program_file=mock_input_files["program_file"],
            current_output=mock_input_files["current_output"],
            desired_output=mock_input_files["desired_output"],
            output=None,
            language="javascript"
        )

        call_kwargs = mock_requests_post_fixture.call_args
        payload = call_kwargs[1]["json"]

        # Verify all expected fields are present
        assert "promptContent" in payload
        assert "codeContent" in payload
        assert "programContent" in payload
        assert "currentOutput" in payload
        assert "desiredOutput" in payload
        assert "language" in payload
        assert "strength" in payload
        assert "temperature" in payload
        assert "time" in payload
        assert "verbose" in payload
