"""
Tests for the `cmd_test_main` function, which handles CLI commands for test generation.
"""
import json
import os
from unittest.mock import patch, MagicMock, mock_open
import pytest
import click
import requests
from click import Context
from pdd.cmd_test_main import cmd_test_main, CLOUD_REQUEST_TIMEOUT
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
CLOUD_GENERATE_TEST_URL = CloudConfig.get_endpoint_url("generateTest")

# Constants for mocking
DEFAULT_MOCK_GENERATED_TEST = "def test_sample():\n    assert True"
DEFAULT_MOCK_COST = 0.01
DEFAULT_MOCK_MODEL_NAME = "cloud_model"


@pytest.fixture
def mock_ctx_fixture():
    """
    Create a mock Click context with default settings for verbosity, strength, etc.
    Forces local execution to ensure tests verify local behavior regardless of cloud credentials.
    """
    m_ctx = MagicMock(spec=Context)
    m_ctx.obj = {
        "verbose": False,
        "strength": 0.5,
        "temperature": 0.0,
        "force": False,
        "quiet": False,
        "local": True,  # Force local execution for unit tests
    }
    return m_ctx


@pytest.fixture
def mock_files_fixture():
    """
    Returns default file paths for prompt_file, code_file, etc. for use in tests.
    """
    return {
        "prompt_file": "fake_prompt_file.prompt",
        "code_file": "fake_code_file.py",
        "output": "fake_test_output.py",
        "existing_tests": ["fake_existing_tests.py"],  # Now a list to support multiple test files
        "coverage_report": "fake_coverage_report.xml",
    }


# pylint: disable=redefined-outer-name
@pytest.mark.parametrize("coverage_report, existing_tests, expect_error", [
    (None, None, False),
    ("fake_coverage_report.xml", None, True),
    ("fake_coverage_report.xml", ["fake_existing_tests.py"], False),  # Now a list
])
def test_cmd_test_main_coverage_handling(
    mock_ctx_fixture,
    mock_files_fixture,
    coverage_report,
    existing_tests,
    expect_error
):
    """
    Tests behavior when coverage_report is missing or present
    and the presence/absence of existing_tests.
    """
    # Force coverage_report / existing_tests for test
    mock_files_fixture["coverage_report"] = coverage_report
    mock_files_fixture["existing_tests"] = existing_tests

    # Patch dependencies
    with patch("pdd.cmd_test_main.construct_paths") as mock_construct_paths, \
         patch("pdd.cmd_test_main.generate_test") as mock_generate_test, \
         patch("pdd.cmd_test_main.increase_tests") as mock_increase_tests, \
         patch("builtins.open", mock_open()):

        # Mock construct_paths to return some test data
        mock_construct_paths.return_value = (
            {},  # resolved_config
            {
                "prompt_file": "prompt_contents",
                "code_file": "code_contents",
                "coverage_report": "coverage_contents" if coverage_report else None,
                "existing_tests": "existing_tests_contents" if existing_tests else None
            },
            {"output": mock_files_fixture["output"]},
            "python",
        )

        # Mock generate_test and increase_tests
        mock_generate_test.return_value = ("generated_tests_code", 0.05, "test_model")
        mock_increase_tests.return_value = ("enhanced_tests_code", 0.10, "coverage_model")

        result = cmd_test_main(
            ctx=mock_ctx_fixture,
            prompt_file=mock_files_fixture["prompt_file"],
            code_file=mock_files_fixture["code_file"],
            output=mock_files_fixture["output"],
            language=None,
            coverage_report=coverage_report,
            existing_tests=existing_tests,
            target_coverage=95.0,
            merge=False,
        )

        # Check if we expected an error result (tuple with Error in model_name)
        if expect_error:
            assert result[0] == ""
            assert result[1] == 0.0
            assert "Error:" in result[2]
        else:
            # If not an error, we either tested generate_test or increase_tests
            if coverage_report is None:
                # Should have invoked generate_test
                mock_generate_test.assert_called_once()
                mock_increase_tests.assert_not_called()
            else:
                # coverage_report is present, should have invoked increase_tests
                if existing_tests:
                    mock_increase_tests.assert_called_once()
                    mock_generate_test.assert_not_called()


# pylint: disable=unused-argument
def test_cmd_test_main_path_construction_error(mock_ctx_fixture, mock_files_fixture):
    """
    Tests that if construct_paths raises an exception,
    cmd_test_main handles it and returns an error result tuple.
    """
    with patch("pdd.cmd_test_main.construct_paths") as mock_construct_paths:
        mock_construct_paths.side_effect = Exception("construct_paths error")

        result = cmd_test_main(
            ctx=mock_ctx_fixture,
            prompt_file=mock_files_fixture["prompt_file"],
            code_file=mock_files_fixture["code_file"],
            output=mock_files_fixture["output"],
            language=None,
            coverage_report=None,
            existing_tests=None,
            target_coverage=None,
            merge=False,
        )

        # Verify error result tuple is returned
        assert result[0] == ""
        assert result[1] == 0.0
        assert "Error:" in result[2]
        assert "construct_paths error" in result[2]


# pylint: disable=unused-argument
def test_cmd_test_main_generate_test_error(mock_ctx_fixture, mock_files_fixture):
    """
    Tests that if generate_test raises an exception,
    cmd_test_main handles it and returns an error result tuple.
    """
    with patch("pdd.cmd_test_main.construct_paths") as mock_construct_paths, \
         patch("pdd.cmd_test_main.generate_test") as mock_generate_test:

        mock_construct_paths.return_value = (
            {},  # resolved_config
            {"prompt_file": "prompt_contents", "code_file": "code_contents"},
            {"output": mock_files_fixture["output"]},
            "python"
        )
        mock_generate_test.side_effect = Exception("generate_test error")

        result = cmd_test_main(
            ctx=mock_ctx_fixture,
            prompt_file=mock_files_fixture["prompt_file"],
            code_file=mock_files_fixture["code_file"],
            output=mock_files_fixture["output"],
            language=None,
            coverage_report=None,
            existing_tests=None,
            target_coverage=None,
            merge=False,
        )

        # Verify error result tuple is returned
        assert result[0] == ""
        assert result[1] == 0.0
        assert "Error:" in result[2]
        assert "generate_test error" in result[2]


# pylint: disable=unused-argument
def test_cmd_test_main_increase_tests_error(mock_ctx_fixture, mock_files_fixture):
    """
    Tests that if increase_tests raises an exception (when coverage_report is provided),
    cmd_test_main handles it and returns an error result tuple.
    """
    with patch("pdd.cmd_test_main.construct_paths") as mock_construct_paths, \
         patch("pdd.cmd_test_main.increase_tests") as mock_increase_tests, \
         patch("builtins.open", mock_open(read_data="existing test content")) as m_file:

        mock_construct_paths.return_value = (
            {},  # resolved_config
            {
                "prompt_file": "prompt_contents",
                "code_file": "code_contents",
                "coverage_report": "coverage_contents",
                "existing_tests": "existing_tests_contents",
            },
            {"output": mock_files_fixture["output"]},
            "python"
        )
        mock_increase_tests.side_effect = Exception("increase_tests error")

        result = cmd_test_main(
            ctx=mock_ctx_fixture,
            prompt_file=mock_files_fixture["prompt_file"],
            code_file=mock_files_fixture["code_file"],
            output=mock_files_fixture["output"],
            language=None,
            coverage_report=mock_files_fixture["coverage_report"],
            existing_tests=mock_files_fixture["existing_tests"],
            target_coverage=95.0,
            merge=False,
        )

        # Verify error result tuple is returned
        assert result[0] == ""
        assert result[1] == 0.0
        assert "Error:" in result[2]
        assert "increase_tests error" in result[2]


# pylint: disable=redefined-outer-name
def test_cmd_test_main_successful_generate_test_no_coverage(mock_ctx_fixture, mock_files_fixture):
    """
    Tests successful run where no coverage_report is provided
    and generate_test is used.
    """
    with patch("pdd.cmd_test_main.construct_paths") as mock_construct_paths, \
         patch("pdd.cmd_test_main.generate_test") as mock_generate_test, \
         patch("builtins.open", mock_open()) as m_file:

        mock_construct_paths.return_value = (
            {},  # resolved_config
            {"prompt_file": "prompt_contents", "code_file": "code_contents"},
            {"output": mock_files_fixture["output"]},
            "python"
        )
        mock_generate_test.return_value = ("unit_test_code", 0.10, "model_v1")

        result = cmd_test_main(
            ctx=mock_ctx_fixture,
            prompt_file=mock_files_fixture["prompt_file"],
            code_file=mock_files_fixture["code_file"],
            output=mock_files_fixture["output"],
            language=None,
            coverage_report=None,
            existing_tests=None,
            target_coverage=None,
            merge=False,
        )

        # Verify file writing
        m_file.assert_called_once_with(mock_files_fixture["output"], "w", encoding="utf-8")
        handle = m_file()
        handle.write.assert_called_once_with("unit_test_code")

        # Verify the result
        assert result == ("unit_test_code", 0.10, "model_v1")


# pylint: disable=redefined-outer-name
def test_cmd_test_main_successful_increase_test_with_coverage(mock_ctx_fixture, mock_files_fixture):
    """
    Tests a successful run with a coverage report, which should trigger 'increase_tests'.
    """
    with patch("pdd.cmd_test_main.construct_paths") as mock_construct_paths, \
         patch("pdd.cmd_test_main.increase_tests") as mock_increase_tests, \
         patch("builtins.open", mock_open()) as m_file:

        mock_construct_paths.return_value = (
            {},  # resolved_config
            {
                "prompt_file": "prompt_contents",
                "code_file": "code_contents",
                "coverage_report": "coverage_contents",
                "existing_tests": "existing_tests_contents",
            },
            {"output": mock_files_fixture["output"]},
            "python"
        )
        mock_increase_tests.return_value = ("more_tests", 0.20, "model_v2")

        result = cmd_test_main(
            ctx=mock_ctx_fixture,
            prompt_file=mock_files_fixture["prompt_file"],
            code_file=mock_files_fixture["code_file"],
            output=mock_files_fixture["output"],
            language=None,
            coverage_report=mock_files_fixture["coverage_report"],
            existing_tests=mock_files_fixture["existing_tests"],
            target_coverage=95.0,
            merge=False,
        )

        # Verify file writing and result
        m_file.assert_any_call(mock_files_fixture["output"], "w", encoding="utf-8")
        handle = m_file()
        handle.write.assert_called_once_with("more_tests")
        assert result == ("more_tests", 0.20, "model_v2")


# pylint: disable=redefined-outer-name
def test_cmd_test_main_merge_existing_tests(mock_ctx_fixture, mock_files_fixture):
    """
    Tests that when 'merge' is True, the output file is the 'existing_tests' path
    and tests are APPENDED (not overwritten).
    """
    with patch("pdd.cmd_test_main.construct_paths") as mock_construct_paths, \
         patch("pdd.cmd_test_main.generate_test") as mock_generate_test, \
         patch("builtins.open", mock_open()) as m_file:

        # Ensure 'existing_tests' is in the output path from construct_paths
        mock_construct_paths.return_value = (
            {},  # resolved_config
            {"prompt_file": "p", "code_file": "c", "existing_tests": "et"},
            {"output": mock_files_fixture["output"]},
            "python"
        )
        mock_generate_test.return_value = ("merged_code", 0.15, "model_v3")

        cmd_test_main(
            ctx=mock_ctx_fixture,
            prompt_file=mock_files_fixture["prompt_file"],
            code_file=mock_files_fixture["code_file"],
            output=None,
            language=None,
            coverage_report=None,
            existing_tests=mock_files_fixture["existing_tests"],  # Already a list
            target_coverage=None,
            merge=True,
        )

        # When merge=True, file should be opened in APPEND mode, not write mode
        m_file.assert_any_call(mock_files_fixture["existing_tests"][0], "a", encoding="utf-8")
        handle = m_file()
        # Content is prepended with newlines when appending
        handle.write.assert_called_once_with("\n\n" + "merged_code")


def test_cmd_test_main_output_directory_path_uses_resolved_file(mock_ctx_fixture, mock_files_fixture, tmp_path):
    """
    Intended behavior: when output is a directory path, cmd should write to the
    resolved file from construct_paths, not exit.
    """
    out_dir = tmp_path / "tests_out"
    out_dir.mkdir()

    with patch("pdd.cmd_test_main.construct_paths") as mock_construct_paths, \
         patch("pdd.cmd_test_main.generate_test") as mock_generate_test, \
         patch("builtins.open", mock_open()) as m_open:

        resolved_file = out_dir / "unit_test_file.py"
        mock_construct_paths.return_value = (
            {},
            {"prompt_file": "prompt_contents", "code_file": "code_contents"},
            {"output": str(resolved_file)},
            "python",
        )
        mock_generate_test.return_value = ("unit_test_code", 0.10, "model_v1")

        # Pass directory path via output; command should use resolved file
        result = cmd_test_main(
            ctx=mock_ctx_fixture,
            prompt_file=mock_files_fixture["prompt_file"],
            code_file=mock_files_fixture["code_file"],
            output=str(out_dir),
            language=None,
            coverage_report=None,
            existing_tests=None,
            target_coverage=None,
            merge=False,
        )

        assert result == ("unit_test_code", 0.10, "model_v1")
        m_open.assert_called_once_with(str(resolved_file), "w", encoding="utf-8")
        handle = m_open()
        handle.write.assert_called_once_with("unit_test_code")


def test_cmd_test_main_uses_safe_ctx_obj_access():
    """
    Regression: cmd_test_main should not raise KeyError if ctx.obj
    is missing 'strength' or 'temperature' keys.

    Bug: Direct dict access ctx.obj["strength"] raises KeyError,
    but ctx.obj.get("strength", DEFAULT) is safe.
    """
    import inspect

    source = inspect.getsource(cmd_test_main)

    # Should NOT use direct dict access for strength/temperature
    assert 'ctx.obj["strength"]' not in source, \
        "cmd_test_main should use ctx.obj.get('strength', ...) not ctx.obj['strength']"
    assert 'ctx.obj["temperature"]' not in source, \
        "cmd_test_main should use ctx.obj.get('temperature', ...) not ctx.obj['temperature']"


def test_cmd_test_main_uses_pddrc_strength_from_resolved_config():
    """
    REGRESSION TEST: cmd_test_main must use strength from resolved_config (pddrc),
    not just ctx.obj or defaults.

    Bug: strength was resolved BEFORE calling construct_paths, so pddrc values
    from resolved_config were ignored. generate_test received DEFAULT_STRENGTH
    instead of pddrc value.

    BEFORE FIX: generate_test called with strength=0.75 (default)
    AFTER FIX: generate_test called with strength=0.9 (from pddrc via resolved_config)
    """
    mock_ctx = MagicMock(spec=Context)
    mock_ctx.obj = {
        "verbose": False,
        "force": False,
        "quiet": False,
        "local": True,  # Force local execution for unit test
        "time": 0.25,
        # strength/temperature NOT in ctx.obj (simulates CLI not passing --strength)
    }

    with patch("pdd.cmd_test_main.construct_paths") as mock_construct_paths, \
         patch("pdd.cmd_test_main.generate_test") as mock_generate_test, \
         patch("builtins.open", mock_open()):

        # resolved_config contains pddrc strength value
        mock_construct_paths.return_value = (
            {"strength": 0.9, "temperature": 0.5},  # pddrc values in resolved_config
            {"prompt_file": "prompt_contents", "code_file": "code_contents"},
            {"output": "test_output.py"},
            "python"
        )
        mock_generate_test.return_value = ("unit_test_code", 0.10, "model_v1")

        cmd_test_main(
            ctx=mock_ctx,
            prompt_file="test.prompt",
            code_file="test.py",
            output="test_output.py",
            language=None,
            coverage_report=None,
            existing_tests=None,
            target_coverage=None,
            merge=False,
        )

        # Verify generate_test was called with pddrc strength (0.9), not default (0.75)
        mock_generate_test.assert_called_once()
        call_kwargs = mock_generate_test.call_args.kwargs
        assert call_kwargs["strength"] == 0.9, \
            f"Expected pddrc strength 0.9, got {call_kwargs['strength']}"
        assert call_kwargs["temperature"] == 0.5, \
            f"Expected pddrc temperature 0.5, got {call_kwargs['temperature']}"


def test_cmd_test_main_cli_strength_overrides_pddrc():
    """
    Verify that explicit CLI --strength overrides pddrc value.

    When user passes --strength 0.3, that should be used even if pddrc has 0.9.
    """
    mock_ctx = MagicMock(spec=Context)
    mock_ctx.obj = {
        "verbose": False,
        "force": False,
        "quiet": False,
        "local": True,  # Force local execution for unit test
        "time": 0.25,
        "strength": 0.3,  # CLI passed --strength 0.3
        "temperature": 0.1,
    }

    with patch("pdd.cmd_test_main.construct_paths") as mock_construct_paths, \
         patch("pdd.cmd_test_main.generate_test") as mock_generate_test, \
         patch("builtins.open", mock_open()):

        # resolved_config would normally have pddrc value, but CLI should win
        # However, construct_paths merges CLI > pddrc, so resolved_config
        # should already have the CLI value
        mock_construct_paths.return_value = (
            {"strength": 0.3, "temperature": 0.1},  # CLI values propagated
            {"prompt_file": "prompt_contents", "code_file": "code_contents"},
            {"output": "test_output.py"},
            "python"
        )
        mock_generate_test.return_value = ("unit_test_code", 0.10, "model_v1")

        cmd_test_main(
            ctx=mock_ctx,
            prompt_file="test.prompt",
            code_file="test.py",
            output="test_output.py",
            language=None,
            coverage_report=None,
            existing_tests=None,
            target_coverage=None,
            merge=False,
        )

        # Verify CLI strength (0.3) was used
        call_kwargs = mock_generate_test.call_args.kwargs
        assert call_kwargs["strength"] == 0.3, \
            f"Expected CLI strength 0.3, got {call_kwargs['strength']}"


def test_cmd_test_main_multiple_existing_tests_concatenated(tmp_path):
    """
    Test that cmd_test_main correctly concatenates multiple existing test files.

    This tests the new feature where multiple --existing-tests options can be provided
    and their content is concatenated before being passed to the test generation.
    """
    mock_ctx = MagicMock(spec=Context)
    mock_ctx.obj = {
        "verbose": False,
        "force": True,
        "quiet": False,
        "local": True,  # Force local execution for unit test
        "time": 0.25,
        "context": None,
        "confirm_callback": None,
    }

    # Create test files with actual content
    test_file_1 = tmp_path / "test_1.py"
    test_file_1.write_text("# test 1 content\ndef test_one(): pass")
    test_file_2 = tmp_path / "test_2.py"
    test_file_2.write_text("# test 2 content\ndef test_two(): pass")
    output_file = tmp_path / "test_output.py"

    with patch("pdd.cmd_test_main.construct_paths") as mock_construct_paths, \
         patch("pdd.cmd_test_main.generate_test") as mock_generate_test:

        mock_construct_paths.return_value = (
            {},  # resolved_config
            {
                "prompt_file": "prompt_contents",
                "code_file": "code_contents",
                # existing_tests will be populated by cmd_test_main after construct_paths
            },
            {"output": str(output_file)},
            "python"
        )
        mock_generate_test.return_value = ("generated_tests", 0.10, "model_v1")

        result = cmd_test_main(
            ctx=mock_ctx,
            prompt_file="test.prompt",
            code_file="test.py",
            output=str(output_file),
            language=None,
            coverage_report=None,
            existing_tests=[str(test_file_1), str(test_file_2)],
            target_coverage=None,
            merge=False,
        )

        # Verify generate_test was called and received concatenated existing tests
        mock_generate_test.assert_called_once()
        call_kwargs = mock_generate_test.call_args.kwargs

        # BUG FIX: existing_tests MUST be passed to generate_test
        # Previously this was a conditional check that silently passed when missing
        assert "existing_tests" in call_kwargs, \
            "BUG: existing_tests should be passed to generate_test but is missing"

        existing_tests_content = call_kwargs["existing_tests"]
        assert "test 1 content" in existing_tests_content, \
            "Content from test_file_1 should be in existing_tests"
        assert "test 2 content" in existing_tests_content, \
            "Content from test_file_2 should be in existing_tests"


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
    monkeypatch.setattr("pdd.cmd_test_main.CloudConfig.get_jwt_token", mock)
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
    monkeypatch.setattr("pdd.cmd_test_main.requests.post", mock)
    return mock


@pytest.fixture
def mock_rich_console_fixture(monkeypatch):
    """Mock console.print for testing Rich output."""
    mock_console_print = MagicMock()
    monkeypatch.setattr("pdd.cmd_test_main.console.print", mock_console_print)
    return mock_console_print


@pytest.fixture
def mock_cloud_env_vars(monkeypatch):
    """Set required environment variables for cloud authentication."""
    monkeypatch.setenv("NEXT_PUBLIC_FIREBASE_API_KEY", "test_firebase_key")
    monkeypatch.setenv("GITHUB_CLIENT_ID", "test_github_id")


# B. Cloud Execution Tests

def test_cmd_test_main_cloud_success_generate_mode(
    mock_cloud_ctx, mock_get_jwt_token_fixture, mock_requests_post_fixture,
    mock_rich_console_fixture, mock_cloud_env_vars
):
    """Test successful cloud test generation in 'generate' mode."""
    with patch("pdd.cmd_test_main.construct_paths") as mock_construct_paths, \
         patch("builtins.open", mock_open()):

        mock_construct_paths.return_value = (
            {},  # resolved_config
            {"prompt_file": "Cloud test prompt", "code_file": "def func(): pass"},
            {"output": "test_output.py"},
            "python"
        )

        result = cmd_test_main(
            ctx=mock_cloud_ctx,
            prompt_file="test.prompt",
            code_file="test.py",
            output="test_output.py",
            language=None,
            coverage_report=None,
            existing_tests=None,
            target_coverage=None,
            merge=False,
        )

        assert result[0] == DEFAULT_MOCK_GENERATED_TEST
        assert result[1] == DEFAULT_MOCK_COST
        assert result[2] == DEFAULT_MOCK_MODEL_NAME

        # Verify cloud request was made with correct payload
        mock_get_jwt_token_fixture.assert_called_once()
        mock_requests_post_fixture.assert_called_once()
        call_kwargs = mock_requests_post_fixture.call_args
        assert call_kwargs[0][0] == CLOUD_GENERATE_TEST_URL
        payload = call_kwargs[1]["json"]
        assert payload["mode"] == "generate"
        assert payload["promptContent"] == "Cloud test prompt"
        assert payload["codeContent"] == "def func(): pass"
        assert payload["language"] == "python"


def test_cmd_test_main_cloud_success_increase_mode(
    mock_cloud_ctx, mock_get_jwt_token_fixture, mock_requests_post_fixture,
    mock_rich_console_fixture, mock_cloud_env_vars
):
    """Test successful cloud test generation in 'increase' mode."""
    mock_response = MagicMock(spec=requests.Response)
    mock_response.json.return_value = {
        "generatedTest": "def test_new(): assert True",
        "totalCost": 0.015,
        "modelName": "cloud_model"
    }
    mock_response.status_code = 200
    mock_response.raise_for_status = MagicMock()
    mock_requests_post_fixture.return_value = mock_response

    with patch("pdd.cmd_test_main.construct_paths") as mock_construct_paths, \
         patch("builtins.open", mock_open(read_data="existing test content")):

        mock_construct_paths.return_value = (
            {},
            {
                "prompt_file": "Cloud test prompt",
                "code_file": "def func(): pass",
                "coverage_report": "<coverage><line hits='0'/></coverage>",
                "existing_tests": "def test_existing(): pass"
            },
            {"output": "test_output.py"},
            "python"
        )

        result = cmd_test_main(
            ctx=mock_cloud_ctx,
            prompt_file="test.prompt",
            code_file="test.py",
            output="test_output.py",
            language=None,
            coverage_report="coverage.xml",
            existing_tests=["existing_tests.py"],
            target_coverage=None,
            merge=False,
        )

        assert result[0] == "def test_new(): assert True"
        assert result[1] == 0.015

        # Verify cloud request had increase mode fields
        call_kwargs = mock_requests_post_fixture.call_args
        payload = call_kwargs[1]["json"]
        assert payload["mode"] == "increase"
        assert "existingTests" in payload
        assert "coverageReport" in payload


def test_cmd_test_main_cloud_fallback_auth_failure(
    mock_cloud_ctx, mock_get_jwt_token_fixture, mock_requests_post_fixture,
    mock_rich_console_fixture, mock_cloud_env_vars
):
    """Test fallback to local when cloud auth fails."""
    mock_get_jwt_token_fixture.return_value = None  # Auth failed

    with patch("pdd.cmd_test_main.construct_paths") as mock_construct_paths, \
         patch("pdd.cmd_test_main.generate_test") as mock_local_generate, \
         patch("builtins.open", mock_open()):

        mock_construct_paths.return_value = (
            {},
            {"prompt_file": "test prompt", "code_file": "def func(): pass"},
            {"output": "test_output.py"},
            "python"
        )
        mock_local_generate.return_value = ("local_test_code", 0.05, "local_model")

        result = cmd_test_main(
            ctx=mock_cloud_ctx,
            prompt_file="test.prompt",
            code_file="test.py",
            output="test_output.py",
            language=None,
            coverage_report=None,
            existing_tests=None,
            target_coverage=None,
            merge=False,
        )

        # Should have fallen back to local
        mock_local_generate.assert_called_once()
        mock_requests_post_fixture.assert_not_called()
        assert result[0] == "local_test_code"
        # Check fallback message was printed
        assert any("falling back" in str(call_args[0][0]).lower()
                   for call_args in mock_rich_console_fixture.call_args_list if call_args[0])


def test_cmd_test_main_cloud_fallback_timeout(
    mock_cloud_ctx, mock_get_jwt_token_fixture, mock_requests_post_fixture,
    mock_rich_console_fixture, mock_cloud_env_vars
):
    """Test fallback to local when cloud request times out."""
    mock_requests_post_fixture.side_effect = requests.exceptions.Timeout("Request timed out")

    with patch("pdd.cmd_test_main.construct_paths") as mock_construct_paths, \
         patch("pdd.cmd_test_main.generate_test") as mock_local_generate, \
         patch("builtins.open", mock_open()):

        mock_construct_paths.return_value = (
            {},
            {"prompt_file": "test prompt", "code_file": "def func(): pass"},
            {"output": "test_output.py"},
            "python"
        )
        mock_local_generate.return_value = ("local_test_code", 0.05, "local_model")

        result = cmd_test_main(
            ctx=mock_cloud_ctx,
            prompt_file="test.prompt",
            code_file="test.py",
            output="test_output.py",
            language=None,
            coverage_report=None,
            existing_tests=None,
            target_coverage=None,
            merge=False,
        )

        mock_local_generate.assert_called_once()
        assert result[0] == "local_test_code"
        assert any("timed out" in str(call_args[0][0]).lower()
                   for call_args in mock_rich_console_fixture.call_args_list if call_args[0])


def test_cmd_test_main_cloud_fallback_5xx_error(
    mock_cloud_ctx, mock_get_jwt_token_fixture, mock_requests_post_fixture,
    mock_rich_console_fixture, mock_cloud_env_vars
):
    """Test fallback to local on 5xx server error."""
    mock_response = MagicMock(spec=requests.Response)
    mock_response.status_code = 500
    mock_response.text = "Internal Server Error"
    http_error = requests.exceptions.HTTPError(response=mock_response)
    http_error.response = mock_response
    mock_requests_post_fixture.side_effect = http_error

    with patch("pdd.cmd_test_main.construct_paths") as mock_construct_paths, \
         patch("pdd.cmd_test_main.generate_test") as mock_local_generate, \
         patch("builtins.open", mock_open()):

        mock_construct_paths.return_value = (
            {},
            {"prompt_file": "test prompt", "code_file": "def func(): pass"},
            {"output": "test_output.py"},
            "python"
        )
        mock_local_generate.return_value = ("local_test_code", 0.05, "local_model")

        result = cmd_test_main(
            ctx=mock_cloud_ctx,
            prompt_file="test.prompt",
            code_file="test.py",
            output="test_output.py",
            language=None,
            coverage_report=None,
            existing_tests=None,
            target_coverage=None,
            merge=False,
        )

        mock_local_generate.assert_called_once()
        assert result[0] == "local_test_code"


def test_cmd_test_main_cloud_fallback_json_decode_error(
    mock_cloud_ctx, mock_get_jwt_token_fixture, mock_requests_post_fixture,
    mock_rich_console_fixture, mock_cloud_env_vars
):
    """Test fallback to local when cloud returns invalid JSON."""
    mock_response = MagicMock(spec=requests.Response)
    mock_response.json.side_effect = json.JSONDecodeError("msg", "doc", 0)
    mock_response.status_code = 200
    mock_response.raise_for_status = MagicMock()
    mock_requests_post_fixture.return_value = mock_response
    mock_requests_post_fixture.side_effect = None

    with patch("pdd.cmd_test_main.construct_paths") as mock_construct_paths, \
         patch("pdd.cmd_test_main.generate_test") as mock_local_generate, \
         patch("builtins.open", mock_open()):

        mock_construct_paths.return_value = (
            {},
            {"prompt_file": "test prompt", "code_file": "def func(): pass"},
            {"output": "test_output.py"},
            "python"
        )
        mock_local_generate.return_value = ("local_test_code", 0.05, "local_model")

        result = cmd_test_main(
            ctx=mock_cloud_ctx,
            prompt_file="test.prompt",
            code_file="test.py",
            output="test_output.py",
            language=None,
            coverage_report=None,
            existing_tests=None,
            target_coverage=None,
            merge=False,
        )

        mock_local_generate.assert_called_once()
        assert result[0] == "local_test_code"
        assert any("invalid json" in str(call_args[0][0]).lower()
                   for call_args in mock_rich_console_fixture.call_args_list if call_args[0])


def test_cmd_test_main_cloud_fallback_no_test_returned(
    mock_cloud_ctx, mock_get_jwt_token_fixture, mock_requests_post_fixture,
    mock_rich_console_fixture, mock_cloud_env_vars
):
    """Test fallback to local when cloud returns no test code."""
    mock_response = MagicMock(spec=requests.Response)
    mock_response.json.return_value = {"totalCost": 0.01, "modelName": "cloud_model"}  # No generatedTest
    mock_response.status_code = 200
    mock_response.raise_for_status = MagicMock()
    mock_requests_post_fixture.return_value = mock_response
    mock_requests_post_fixture.side_effect = None

    with patch("pdd.cmd_test_main.construct_paths") as mock_construct_paths, \
         patch("pdd.cmd_test_main.generate_test") as mock_local_generate, \
         patch("builtins.open", mock_open()):

        mock_construct_paths.return_value = (
            {},
            {"prompt_file": "test prompt", "code_file": "def func(): pass"},
            {"output": "test_output.py"},
            "python"
        )
        mock_local_generate.return_value = ("local_test_code", 0.05, "local_model")

        result = cmd_test_main(
            ctx=mock_cloud_ctx,
            prompt_file="test.prompt",
            code_file="test.py",
            output="test_output.py",
            language=None,
            coverage_report=None,
            existing_tests=None,
            target_coverage=None,
            merge=False,
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
def test_cmd_test_main_cloud_non_recoverable_http_errors(
    status_code, error_message, expected_match,
    mock_cloud_ctx, mock_get_jwt_token_fixture, mock_requests_post_fixture,
    mock_rich_console_fixture, mock_cloud_env_vars
):
    """Test that HTTP 402, 401, 403, 400 errors raise UsageError instead of falling back."""
    mock_response = MagicMock(spec=requests.Response)
    mock_response.status_code = status_code
    mock_response.text = error_message
    mock_response.json.return_value = {"error": error_message, "currentBalance": 0, "estimatedCost": 0.05}
    http_error = requests.exceptions.HTTPError(response=mock_response)
    http_error.response = mock_response
    mock_requests_post_fixture.side_effect = http_error

    with patch("pdd.cmd_test_main.construct_paths") as mock_construct_paths, \
         patch("pdd.cmd_test_main.generate_test") as mock_local_generate, \
         patch("builtins.open", mock_open()):

        mock_construct_paths.return_value = (
            {},
            {"prompt_file": "test prompt", "code_file": "def func(): pass"},
            {"output": "test_output.py"},
            "python"
        )

        with pytest.raises(click.UsageError, match=expected_match):
            cmd_test_main(
                ctx=mock_cloud_ctx,
                prompt_file="test.prompt",
                code_file="test.py",
                output="test_output.py",
                language=None,
                coverage_report=None,
                existing_tests=None,
                target_coverage=None,
                merge=False,
            )

        # Local generator should NOT have been called
        mock_local_generate.assert_not_called()


def test_cmd_test_main_cloud_insufficient_credits_displays_balance(
    mock_cloud_ctx, mock_get_jwt_token_fixture, mock_requests_post_fixture,
    mock_rich_console_fixture, mock_cloud_env_vars
):
    """Test that HTTP 402 displays current balance and estimated cost."""
    mock_response = MagicMock(spec=requests.Response)
    mock_response.status_code = 402
    mock_response.text = "Insufficient credits"
    mock_response.json.return_value = {"error": "Insufficient credits", "currentBalance": 0.02, "estimatedCost": 0.05}
    http_error = requests.exceptions.HTTPError(response=mock_response)
    http_error.response = mock_response
    mock_requests_post_fixture.side_effect = http_error

    with patch("pdd.cmd_test_main.construct_paths") as mock_construct_paths, \
         patch("builtins.open", mock_open()):

        mock_construct_paths.return_value = (
            {},
            {"prompt_file": "test prompt", "code_file": "def func(): pass"},
            {"output": "test_output.py"},
            "python"
        )

        with pytest.raises(click.UsageError, match="Insufficient credits"):
            cmd_test_main(
                ctx=mock_cloud_ctx,
                prompt_file="test.prompt",
                code_file="test.py",
                output="test_output.py",
                language=None,
                coverage_report=None,
                existing_tests=None,
                target_coverage=None,
                merge=False,
            )

        # Check balance info was printed
        printed_messages = [str(call_args[0][0]) for call_args in mock_rich_console_fixture.call_args_list if call_args[0]]
        assert any("0.02" in msg and "0.05" in msg for msg in printed_messages), \
            f"Expected balance/cost info in output. Got: {printed_messages}"


# D. Cloud-Only Mode and Local Mode Tests

def test_cmd_test_main_cloud_only_mode_prevents_fallback(
    mock_cloud_ctx, mock_get_jwt_token_fixture, mock_requests_post_fixture,
    mock_rich_console_fixture, mock_cloud_env_vars, monkeypatch
):
    """Test that PDD_CLOUD_ONLY=1 prevents fallback to local."""
    monkeypatch.setenv("PDD_CLOUD_ONLY", "1")
    mock_requests_post_fixture.side_effect = requests.exceptions.Timeout("Request timed out")

    with patch("pdd.cmd_test_main.construct_paths") as mock_construct_paths, \
         patch("pdd.cmd_test_main.generate_test") as mock_local_generate, \
         patch("builtins.open", mock_open()):

        mock_construct_paths.return_value = (
            {},
            {"prompt_file": "test prompt", "code_file": "def func(): pass"},
            {"output": "test_output.py"},
            "python"
        )

        with pytest.raises(click.UsageError, match="timed out"):
            cmd_test_main(
                ctx=mock_cloud_ctx,
                prompt_file="test.prompt",
                code_file="test.py",
                output="test_output.py",
                language=None,
                coverage_report=None,
                existing_tests=None,
                target_coverage=None,
                merge=False,
            )

        # Local generator should NOT have been called
        mock_local_generate.assert_not_called()


def test_cmd_test_main_local_mode_skips_cloud(
    mock_cloud_ctx, mock_get_jwt_token_fixture, mock_requests_post_fixture,
    mock_rich_console_fixture, mock_cloud_env_vars
):
    """Test that local mode skips cloud entirely."""
    mock_cloud_ctx.obj['local'] = True  # Local mode

    with patch("pdd.cmd_test_main.construct_paths") as mock_construct_paths, \
         patch("pdd.cmd_test_main.generate_test") as mock_local_generate, \
         patch("builtins.open", mock_open()):

        mock_construct_paths.return_value = (
            {},
            {"prompt_file": "test prompt", "code_file": "def func(): pass"},
            {"output": "test_output.py"},
            "python"
        )
        mock_local_generate.return_value = ("local_test_code", 0.05, "local_model")

        result = cmd_test_main(
            ctx=mock_cloud_ctx,
            prompt_file="test.prompt",
            code_file="test.py",
            output="test_output.py",
            language=None,
            coverage_report=None,
            existing_tests=None,
            target_coverage=None,
            merge=False,
        )

        # Cloud should not have been called
        mock_get_jwt_token_fixture.assert_not_called()
        mock_requests_post_fixture.assert_not_called()
        # Local generator should have been called
        mock_local_generate.assert_called_once()
        assert result[0] == "local_test_code"


def test_cmd_test_main_cloud_payload_contains_all_params(
    mock_cloud_ctx, mock_get_jwt_token_fixture, mock_requests_post_fixture,
    mock_rich_console_fixture, mock_cloud_env_vars
):
    """Test that cloud payload contains all required parameters."""
    mock_cloud_ctx.obj['verbose'] = True

    with patch("pdd.cmd_test_main.construct_paths") as mock_construct_paths, \
         patch("builtins.open", mock_open()):

        mock_construct_paths.return_value = (
            {"strength": 0.8, "temperature": 0.5, "time": 0.3},  # resolved_config
            {"prompt_file": "test prompt", "code_file": "def func(): pass"},
            {"output": "test_output.py"},
            "python"
        )

        cmd_test_main(
            ctx=mock_cloud_ctx,
            prompt_file="test.prompt",
            code_file="test.py",
            output="test_output.py",
            language="javascript",
            coverage_report=None,
            existing_tests=None,
            target_coverage=None,
            merge=False,
            strength=0.8,
            temperature=0.5,
        )

        call_kwargs = mock_requests_post_fixture.call_args
        payload = call_kwargs[1]["json"]

        # Verify all expected fields are present
        assert "promptContent" in payload
        assert "codeContent" in payload
        assert "language" in payload
        assert "strength" in payload
        assert "temperature" in payload
        assert "time" in payload
        assert "verbose" in payload
        assert "sourceFilePath" in payload
        assert "testFilePath" in payload
        assert "moduleName" in payload
        assert "mode" in payload


# -----------------------------------------------------------------------------
# E2E Cloud Tests (run when cloud credentials are available)
# -----------------------------------------------------------------------------

def _has_cloud_jwt_token() -> bool:
    """Check if a JWT token is available (either injected or via stored refresh token)."""
    # First check for env var (fast path)
    if os.environ.get("PDD_JWT_TOKEN"):
        return True
    # Check for stored refresh token (requires keyring)
    try:
        import keyring
        token = keyring.get_password("firebase-auth-PDD Code Generator", "refresh_token")
        return bool(token)
    except Exception:
        return False


def _wait_for_cloud_credentials(max_retries: int = 3, delay: float = 1.0) -> bool:
    """
    Retry checking for cloud credentials with delays.

    pytest-xdist workers may have delayed access to keyring or env vars.
    This gives the system a chance to make credentials available.
    """
    import time
    for attempt in range(max_retries):
        if _has_cloud_credentials() and _has_cloud_jwt_token():
            return True
        if attempt < max_retries - 1:
            time.sleep(delay)
    return False


# Marker for tests that require actual cloud execution with valid token
requires_cloud_e2e = pytest.mark.skipif(
    not (_has_cloud_credentials() and _has_cloud_jwt_token()),
    reason="Cloud E2E tests require credentials (API keys) and auth token (PDD_JWT_TOKEN or stored refresh token)"
)


@requires_cloud_e2e
def test_cmd_test_main_cloud_e2e_generate_mode(tmp_path, monkeypatch, capsys):
    """
    E2E test: Real cloud test generation.

    This test verifies actual cloud execution by:
    1. Setting PDD_CLOUD_ONLY=1 to prevent silent fallback to local
    2. Checking for "Cloud Success" in output

    Requires PDD_JWT_TOKEN to be set (e.g., via infisical).
    """
    # Retry credentials check (pytest-xdist workers may have delayed keyring access)
    if not _wait_for_cloud_credentials(max_retries=3, delay=1.0):
        pytest.skip("Cloud credentials not available in this worker process after retries")

    # Prevent silent fallback to local - cloud must work or test fails
    monkeypatch.setenv("PDD_CLOUD_ONLY", "1")

    # Create minimal test files in tmp_path
    prompt_file = tmp_path / "test.prompt"
    prompt_file.write_text("Generate unit tests for a simple add function.")

    code_file = tmp_path / "simple_math.py"
    code_file.write_text("def add(a, b):\n    return a + b\n")

    output_file = tmp_path / "test_simple_math.py"

    # Create real Click context with local=False
    ctx = MagicMock(spec=Context)
    ctx.obj = {
        "verbose": True,
        "force": True,
        "quiet": False,
        "local": False,  # Use cloud
        "strength": 0.25,  # Use lowest strength for faster cloud response
        "temperature": 0.0,
    }

    result = cmd_test_main(
        ctx=ctx,
        prompt_file=str(prompt_file),
        code_file=str(code_file),
        output=str(output_file),
        language="python",
        coverage_report=None,
        existing_tests=None,
        target_coverage=None,
        merge=False,
    )

    # Capture output to verify cloud execution
    captured = capsys.readouterr()

    # Verify we got valid test code back
    generated_test, cost, model = result
    assert len(generated_test) > 0, "Cloud should return generated test code"
    assert "def test" in generated_test.lower() or "class test" in generated_test.lower(), \
        "Should contain test functions or test class"
    assert cost > 0, "Cloud execution should have a cost"
    assert output_file.exists(), "Output file should be created"
    # Verify cloud was actually used by checking for "Cloud Success" in output
    assert "Cloud Success" in captured.out, \
        f"Expected 'Cloud Success' in output, got: {captured.out[:500]}"
