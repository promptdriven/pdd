# To run this test:
# Option 1: From project root: pytest tests/test_utils.py
# Option 2: From project root: python -m pytest tests/test_utils.py
# Option 3: From tests directory: pytest test_utils.py

"""
Test Plan for edit_file_tool/utils.py

The 'utils' module is foundational, providing core services like logging,
error handling, cost calculation, and validation. Tests must be comprehensive,
covering happy paths, edge cases, and failure modes for each utility.

1. Type Aliases and Constants:
   - Test `get_environment_config` for various scenarios:
     - Variable not set (returns default).
     - Variable set to valid values for int, float, bool, str.
     - Variable set to invalid values (returns default).
     - Variable is an empty string (returns default, except for str type).
     - Boolean casting for 'true', '1', 'yes' (case-insensitive).

2. Exception Classes:
   - Test `EditToolError` and its subclasses.
   - Verify that a message is stored correctly.
   - Verify that context can be added and is included in the string representation.
   - Check the inheritance hierarchy (e.g., `isinstance(FileOperationError(), EditToolError)`).

3. Logging Infrastructure:
   - Test `setup_logger`:
     - Verify logger is created with the correct name and level.
     - Test both standard and structured (JSON) formatters using `caplog`.
     - Test file logging using `tmp_path` to create a temporary log file.
     - Test log rotation setup (conceptually, by checking handler type).
     - Test error handling when the log file path is not writable (mock `Path.mkdir` or `RotatingFileHandler` to raise `PermissionError`).
   - Test `sanitize_for_logging`:
     - Redact sensitive keys (e.g., 'api_key', 'Authorization') in dicts.
     - Test with nested data structures (lists of dicts).
     - Test string truncation for long strings.
     - Ensure non-sensitive data is untouched.
     - Test with various data types (int, float, bool).

4. Performance Decorators:
   - Test `@timed`:
     - For both sync and async functions.
     - Verify it logs a DEBUG message with the execution time using `caplog`.
     - Ensure the original function's return value is preserved.
     - Ensure it still logs time if the decorated function raises an exception.
   - Test `@retry`:
     - For both sync and async functions.
     - Scenario: function succeeds on the first attempt (no retry).
     - Scenario: function fails once, then succeeds (one retry).
     - Scenario: function fails all attempts, then raises the final exception.
     - Scenario: function raises an exception not in the specified list (raises immediately).
     - Mock `time.sleep` and `asyncio.sleep` to avoid actual delays and verify backoff logic.

5. Validation Utilities:
   - Test `validate_file_path`:
     - Happy path: valid, non-existent path with `allow_create=True`.
     - Security: path traversal attempt (`../`) should raise `ValidationError`.
     - `must_exist=True`: test with an existing file (pass) and a non-existing file (raise `FileOperationError`).
     - `must_exist=True`: test with a directory path (raise `FileOperationError`).
     - `allow_create=True`: test with a path whose parent directory does not exist (raise `FileOperationError`).
     - Test with a custom `base_dir`.
     - Test with an empty path string (raise `ValidationError`).
   - Test `check_model_compatibility`:
     - Parametrize with various model/feature combinations.
     - Test a model in the list against an older, equal, and newer feature.
     - Test a model not in the list (should use default).
   - Test `sanitize_input`:
     - String with control characters to be removed.
     - String with allowed whitespace (`\n`, `\t`).
     - String that needs truncation due to `max_length`.
     - Empty string.

6. Cost Management:
   - Test `get_model_prices`:
     - Request a known model.
     - Request an unknown model (verify fallback to `WARNING` log).
   - Test `calculate_cost` and `calculate_cost_breakdown`:
     - Parametrize with different models, token counts, and `cache_status` ('none', 'write', 'read').
     - Verify calculations against manually computed expected values.
     - Test with zero tokens.
   - Test `format_cost`:
     - Test with various float values and precision settings.
     - Verify the '$' prefix and correct number of decimal places.

7. Cache Strategy:
   - Test `calculate_cache_complexity`:
     - Test with empty content (should be 0).
     - Test with simple, low-density content.
     - Test with complex, high-density content.
     - Test with content that exceeds normalization limits.
   - Test `should_use_cache`:
     - File size below the minimum threshold (should be `False`).
     - File size above the maximum threshold (should be `True`).
     - File size in the middle range:
       - Low complexity (should be `False`).
       - High complexity (should be `True`).
     - Use `monkeypatch` to modify thresholds for easier testing.

8. System Integration and Formatting:
   - Test `check_system_compatibility`:
     - Verify it returns a dictionary with the expected keys ('python_version', 'platform', etc.).
   - Test `format_metrics`:
     - Test with an empty dictionary.
     - Test with a mix of data types.
     - Verify that keys with 'cost' are formatted as currency.
     - Verify title-casing and formatting of other keys.
"""

import asyncio
import json
import logging
import sys
from logging.handlers import RotatingFileHandler
from pathlib import Path
from unittest.mock import MagicMock, patch

import pytest

from edit_file_tool import utils
from edit_file_tool.utils import (APIError, EditToolError, FileOperationError,
                                  ModelCompatibilityError, ValidationError)


# --- 1. Type Aliases and Constants Tests ---

@pytest.mark.parametrize(
    "env_var, key, default, cast_to, expected",
    [
        (None, "TEST_VAR", "default_val", str, "default_val"),
        ("hello", "TEST_VAR", "default_val", str, "hello"),
        ("123", "TEST_VAR", 0, int, 123),
        ("not-an-int", "TEST_VAR", 0, int, 0),
        ("3.14", "TEST_VAR", 0.0, float, 3.14),
        ("not-a-float", "TEST_VAR", 0.0, float, 0.0),
        ("true", "TEST_VAR", False, bool, True),
        ("1", "TEST_VAR", False, bool, True),
        ("YES", "TEST_VAR", False, bool, True),
        ("false", "TEST_VAR", True, bool, False),
        ("0", "TEST_VAR", True, bool, False),
        ("no", "TEST_VAR", True, bool, False),
        ("", "TEST_VAR", "default", str, ""),
        ("", "TEST_VAR", 123, int, 123),
    ],
)
def test_get_environment_config(monkeypatch, env_var, key, default, cast_to, expected):
    """Tests get_environment_config with various inputs."""
    if env_var is not None:
        monkeypatch.setenv(key, env_var)
    else:
        monkeypatch.delenv(key, raising=False)

    result = utils.get_environment_config(key, default, cast_to)
    assert result == expected
    assert isinstance(result, type(expected))


# --- 2. Exception Classes Tests ---

def test_edit_tool_error_basic():
    """Tests basic EditToolError instantiation."""
    error = EditToolError("A test error")
    assert error.message == "A test error"
    assert error.context == {}
    assert str(error) == "A test error"


def test_edit_tool_error_with_context():
    """Tests EditToolError with context."""
    context = {"file": "test.txt", "line": 10}
    error = EditToolError("A contextual error", context=context)
    assert error.message == "A contextual error"
    assert error.context == context
    assert "A contextual error" in str(error)
    assert "file=test.txt" in str(error)
    assert "line=10" in str(error)


def test_exception_inheritance():
    """Tests that specific exceptions inherit from EditToolError."""
    assert isinstance(FileOperationError(""), EditToolError)
    assert isinstance(APIError(""), EditToolError)
    assert isinstance(ValidationError(""), EditToolError)
    assert isinstance(ModelCompatibilityError(""), EditToolError)


# --- 3. Logging Infrastructure Tests ---

def test_setup_logger_basic(caplog):
    """Tests basic logger setup with standard formatting."""
    logger = utils.setup_logger("test_logger", level="INFO")
    assert logger.name == "test_logger"
    assert logger.level == logging.INFO
    logger.info("This is an info message.")
    assert "This is an info message." in caplog.text
    assert "test_logger" in caplog.text
    assert "INFO" in caplog.text


def test_setup_logger_structured(caplog):
    """Tests logger setup with JSON structured formatting."""
    logger = utils.setup_logger("json_logger", level="WARNING", structured=True)
    logger.warning("This is a warning.", extra={"data": 123})

    # Find the formatter on one of the logger's handlers
    json_formatter = None
    for handler in logger.handlers:
        if isinstance(handler.formatter, utils.JsonFormatter):
            json_formatter = handler.formatter
            break
    assert json_formatter is not None, "JsonFormatter not found on any handler"

    # Format the captured record using the correct formatter
    last_record = caplog.records[-1]
    formatted_message = json_formatter.format(last_record)
    log_json = json.loads(formatted_message)

    assert log_json["level"] == "WARNING"
    assert log_json["name"] == "json_logger"
    assert log_json["message"] == "This is a warning."
    assert log_json["data"] == 123


def test_setup_logger_file(tmp_path):
    """Tests logger setup with a file handler."""
    log_file = tmp_path / "test.log"
    logger = utils.setup_logger("file_logger", log_file=log_file)
    
    assert any(isinstance(h, RotatingFileHandler) for h in logger.handlers)
    
    logger.error("Error to file.")
    # Force handlers to flush
    logging.shutdown()
    
    log_content = log_file.read_text()
    assert "Error to file." in log_content


def test_setup_logger_file_permission_error(caplog, mocker):
    """Tests that logger setup handles file permission errors gracefully."""
    mocker.patch("pathlib.Path.mkdir", side_effect=PermissionError("Access denied"))
    logger = utils.setup_logger("bad_file_logger", log_file="/restricted/test.log")
    
    assert "Failed to set up log file" in caplog.text
    assert "Access denied" in caplog.text
    # Should still have a console handler
    assert any(isinstance(h, logging.StreamHandler) for h in logger.handlers)


@pytest.mark.parametrize(
    "data, expected",
    [
        ({"api_key": "123", "user": "test"}, {"api_key": "[REDACTED]", "user": "test"}),
        ({"Authorization": "Bearer xyz", "data": "safe"}, {"Authorization": "[REDACTED]", "data": "safe"}),
        ([{"secret": "abc"}, "item2"], [{"secret": "[REDACTED]"}, "item2"]),
        ("a" * 600, "a" * 500 + "..."),
        ("short string", "short string"),
        (123, 123),
        (None, None),
    ],
)
def test_sanitize_for_logging(data, expected):
    """Tests sanitization of various data structures."""
    assert utils.sanitize_for_logging(data) == expected


# --- 4. Performance Decorators Tests ---

@pytest.mark.asyncio
async def test_timed_decorator_async(caplog):
    """Tests @timed decorator on an async function."""
    caplog.set_level(logging.DEBUG)

    @utils.timed()
    async def sample_async_func():
        await asyncio.sleep(0.01)
        return "done"

    result = await sample_async_func()
    assert result == "done"
    assert "'sample_async_func' executed in" in caplog.text
    assert len(caplog.records) == 1
    assert caplog.records[0].levelname == "DEBUG"


def test_timed_decorator_sync(caplog):
    """Tests @timed decorator on a sync function."""
    caplog.set_level(logging.DEBUG)

    @utils.timed()
    def sample_sync_func():
        return "done"

    result = sample_sync_func()
    assert result == "done"
    assert "'sample_sync_func' executed in" in caplog.text


@pytest.mark.asyncio
async def test_timed_decorator_with_exception(caplog):
    """Tests that @timed still logs when the function raises an exception."""
    caplog.set_level(logging.DEBUG)

    @utils.timed()
    async def failing_func():
        raise ValueError("test error")

    with pytest.raises(ValueError):
        await failing_func()
    
    assert "'failing_func' executed in" in caplog.text


@pytest.mark.asyncio
async def test_retry_decorator_async_success_first_try(mocker):
    """Tests @retry on an async function that succeeds immediately."""
    async_sleep_mock = mocker.patch("asyncio.sleep")
    
    @utils.retry(max_attempts=3)
    async def func():
        return "success"

    result = await func()
    assert result == "success"
    async_sleep_mock.assert_not_called()


@pytest.mark.asyncio
async def test_retry_decorator_async_success_on_retry(mocker, caplog):
    """Tests @retry on an async function that succeeds after one failure."""
    async_sleep_mock = mocker.patch("asyncio.sleep")
    
    call_count = 0
    @utils.retry(max_attempts=3, exceptions=(APIError,))
    async def func():
        nonlocal call_count
        call_count += 1
        if call_count == 1:
            raise APIError("First fail")
        return "success"

    result = await func()
    assert result == "success"
    assert call_count == 2
    async_sleep_mock.assert_called_once()
    assert "Attempt 1/3 failed" in caplog.text


@pytest.mark.asyncio
async def test_retry_decorator_async_all_fails(mocker, caplog):
    """Tests @retry on an async function that fails all attempts."""
    async_sleep_mock = mocker.patch("asyncio.sleep")
    
    @utils.retry(max_attempts=3, exceptions=(APIError,))
    async def func():
        raise APIError("Always fail")

    with pytest.raises(APIError, match="Always fail"):
        await func()
    
    assert async_sleep_mock.call_count == 2
    assert caplog.text.count("failed for func") == 2


def test_retry_decorator_sync_all_fails(mocker, caplog):
    """Tests @retry on a sync function that fails all attempts."""
    sleep_mock = mocker.patch("time.sleep")
    
    @utils.retry(max_attempts=3, exceptions=(ValueError,))
    def func():
        raise ValueError("Always fail")

    with pytest.raises(ValueError, match="Always fail"):
        func()
    
    assert sleep_mock.call_count == 2
    assert caplog.text.count("failed for func") == 2


def test_retry_decorator_unhandled_exception(mocker):
    """Tests that @retry does not catch unspecified exceptions."""
    sleep_mock = mocker.patch("time.sleep")
    
    @utils.retry(max_attempts=3, exceptions=(APIError,))
    def func():
        raise ValueError("Unhandled")

    with pytest.raises(ValueError, match="Unhandled"):
        func()
    
    sleep_mock.assert_not_called()


# --- 5. Validation Utilities Tests ---

def test_validate_file_path_success(tmp_path):
    """Tests a valid file path that can be created."""
    path = tmp_path / "new_file.txt"
    validated_path = utils.validate_file_path(path, base_dir=tmp_path)
    assert validated_path == path.resolve()


def test_validate_file_path_must_exist_success(tmp_path):
    """Tests a path that must exist and does."""
    file_path = tmp_path / "existing.txt"
    file_path.touch()
    validated_path = utils.validate_file_path(file_path, must_exist=True, base_dir=tmp_path)
    assert validated_path == file_path.resolve()


def test_validate_file_path_must_exist_fail(tmp_path):
    """Tests a path that must exist but doesn't."""
    with pytest.raises(FileOperationError, match="File does not exist"):
        utils.validate_file_path(tmp_path / "nonexistent.txt", must_exist=True, base_dir=tmp_path)


def test_validate_file_path_is_not_file(tmp_path):
    """Tests a path that exists but is a directory."""
    with pytest.raises(FileOperationError, match="Path is not a file"):
        utils.validate_file_path(tmp_path, must_exist=True, base_dir=tmp_path)


def test_validate_file_path_parent_does_not_exist(tmp_path):
    """Tests a path where the parent directory doesn't exist."""
    path = tmp_path / "new_dir" / "file.txt"
    with pytest.raises(FileOperationError, match="Parent directory does not exist"):
        utils.validate_file_path(path, allow_create=True, base_dir=tmp_path)


def test_validate_file_path_traversal_attack(tmp_path):
    """Tests that directory traversal is blocked."""
    malicious_path = tmp_path / ".." / "some_other_dir"
    with pytest.raises(ValidationError, match="Path is outside the allowed directory"):
        utils.validate_file_path(malicious_path, base_dir=tmp_path)


def test_validate_file_path_empty_path():
    """Tests that an empty path raises a validation error."""
    with pytest.raises(ValidationError, match="File path cannot be empty"):
        utils.validate_file_path("")


@pytest.mark.parametrize(
    "model, feature, expected",
    [
        ("claude-3-5-sonnet-20240620", "text_editor_20250124", True),
        ("claude-3-5-sonnet-20240620", "text_editor_20241022", True),
        ("claude-3-5-sonnet-20240620", "text_editor_20250728", False),
        ("unknown-model", "text_editor_20241022", True), # Falls back to default
        ("unknown-model", "text_editor_20250124", False), # Default is older
    ]
)
def test_check_model_compatibility(model, feature, expected):
    """Tests model feature compatibility checks."""
    assert utils.check_model_compatibility(model, feature) == expected


@pytest.mark.parametrize(
    "input_str, max_len, expected",
    [
        ("hello\x00world", None, "helloworld"),
        ("test\n\t\rstring", None, "test\n\t\rstring"),
        ("1234567890", 5, "12345"),
        ("short", 10, "short"),
        ("", None, ""),
    ]
)
def test_sanitize_input(input_str, max_len, expected):
    """Tests input sanitization."""
    assert utils.sanitize_input(input_str, max_length=max_len) == expected


# --- 6. Cost Management Tests ---

def test_get_model_prices_known_model():
    """Tests retrieving prices for a known model."""
    prices = utils.get_model_prices("claude-3-5-sonnet-20240620")
    assert prices["input"] == 3.00
    assert prices["output"] == 15.00


def test_get_model_prices_unknown_model(caplog):
    """Tests fallback and warning for an unknown model."""
    prices = utils.get_model_prices("claude-x-turbo")
    assert "not found in pricing list" in caplog.text
    assert "Falling back to" in caplog.text
    # Should fall back to the default model's prices
    default_prices = utils.MODEL_PRICES[utils.DEFAULT_MODEL]
    assert prices == default_prices


@pytest.mark.parametrize(
    "model, input_tokens, output_tokens, cache_status, expected_cost",
    [
        ("claude-3-5-sonnet-20240620", 1_000_000, 1_000_000, "none", 3.00 + 15.00),
        ("claude-3-5-sonnet-20240620", 1_000_000, 0, "write", 3.00 * 1.25),
        ("claude-3-5-sonnet-20240620", 1_000_000, 0, "read", 3.00 * 0.10),
        ("claude-3-haiku-20240307", 2_000_000, 500_000, "none", (0.25 * 2) + (1.25 * 0.5)),
        ("claude-3-opus-20240229", 0, 0, "none", 0.0),
    ]
)
def test_calculate_cost(model, input_tokens, output_tokens, cache_status, expected_cost):
    """Tests cost calculation for various scenarios."""
    cost = utils.calculate_cost(model, input_tokens, output_tokens, cache_status)
    assert cost == pytest.approx(expected_cost)


def test_calculate_cost_breakdown():
    """Tests the detailed cost breakdown function."""
    breakdown = utils.calculate_cost_breakdown(
        "claude-3-opus-20240229", 100_000, 20_000, "write"
    )
    assert breakdown["model"] == "claude-3-opus-20240229"
    assert breakdown["cache_status"] == "write"
    assert breakdown["input_tokens"] == 100_000
    assert breakdown["effective_input_rate_per_million"] == 15.00 * 1.25
    assert breakdown["input_cost"] == pytest.approx((100_000 / 1_000_000) * (15.00 * 1.25))
    assert breakdown["output_cost"] == pytest.approx((20_000 / 1_000_000) * 75.00)
    assert breakdown["total_cost"] == pytest.approx(breakdown["input_cost"] + breakdown["output_cost"])


@pytest.mark.parametrize(
    "cost, precision, expected",
    [
        (1.23456, 4, "$1.2346"),
        (0.00012, 5, "$0.00012"),
        (25.0, 2, "$25.00"),
    ]
)
def test_format_cost(cost, precision, expected):
    """Tests cost formatting."""
    assert utils.format_cost(cost, precision) == expected


# --- 7. Cache Strategy Tests ---

@pytest.mark.parametrize(
    "content, expected_score_range",
    [
        ("", (0.0, 0.0)),
        ("one line", (0.0, 0.1)), # Low lines, low density
        ("\n".join(["short"] * 100), (0.1, 0.2)), # High lines, low density
        ("a" * 200, (0.4, 0.41)), # Low lines, high density
        ("\n".join(["a" * 100] * 200), (0.5, 0.7)), # High lines, high density
    ]
)
def test_calculate_cache_complexity(content, expected_score_range):
    """Tests the cache complexity calculation."""
    score = utils.calculate_cache_complexity(content)
    min_score, max_score = expected_score_range
    assert min_score <= score <= max_score


def test_should_use_cache(monkeypatch):
    """Tests the main cache decision logic."""
    monkeypatch.setattr(utils, 'CACHE_SIZE_THRESHOLD_MIN', 100)
    monkeypatch.setattr(utils, 'CACHE_SIZE_THRESHOLD_MAX', 500)
    monkeypatch.setattr(utils, 'CACHE_COMPLEXITY_THRESHOLD', 0.3)

    # Below min threshold
    small_content = "a" * 50
    assert not utils.should_use_cache("small.txt", small_content)

    # Above max threshold
    large_content = "a" * 600
    assert utils.should_use_cache("large.txt", large_content)

    # In-between, low complexity
    mid_low_complexity = "\n" * 200 # 200 bytes, but low density
    assert not utils.should_use_cache("mid_low.txt", mid_low_complexity)

    # In-between, high complexity
    mid_high_complexity = ("a" * 100 + "\n") * 4 # ~400 bytes, high density
    assert utils.should_use_cache("mid_high.txt", mid_high_complexity)


# --- 8. System Integration and Formatting Tests ---

def test_check_system_compatibility():
    """Tests the system compatibility check."""
    compat = utils.check_system_compatibility()
    assert "python_version" in compat
    assert "python_version_ok" in compat
    assert "platform" in compat
    assert compat["python_version_ok"] == (sys.version_info >= (3, 9))


def test_format_metrics():
    """Tests the metrics formatting function."""
    metrics = {
        "total_cost": 0.12345,
        "execution_time": 5.6789,
        "model_used": "claude-3-5-sonnet-20240620",
    }
    formatted = utils.format_metrics(metrics)
    assert "--- Metrics ---" in formatted
    assert "Total Cost: $0.1235" in formatted
    assert "Execution Time: 5.6789" in formatted
    assert "Model Used: claude-3-5-sonnet-20240620" in formatted
