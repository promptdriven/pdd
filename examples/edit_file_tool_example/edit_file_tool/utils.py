# edit_file_tool/utils.py

"""
This module serves as the foundational utility layer for the edit-file tool.

It offers shared functionality such as structured logging, exception formatting,
type-safe helpers, cost calculation, and caching logic. It ensures consistent
behavior and error reporting across the codebase, reducing duplication and
improving maintainability. As the first module to be implemented (priority 1),
it has no dependencies and provides the foundation that all other components
depend on for logging, error propagation, type annotations, and common utilities.
"""

import asyncio
import functools
import json
import logging
import logging.handlers
import os
import re
import sys
import time
import traceback
from pathlib import Path
from typing import (Any, Callable, Dict, List, Literal, Optional, Tuple, Type,
                    TypeVar, Union)

# ==============================================================================
# 1. Type Aliases and Constants
# ==============================================================================

# --- Type Aliases ---
FilePath = Union[str, Path]
ModelName = str
CacheMode = Literal['auto', 'always', 'never']
CacheStatus = Literal['none', 'write', 'read']
EditInstruction = str
LogLevel = Literal['DEBUG', 'INFO', 'WARNING', 'ERROR', 'CRITICAL']
T = TypeVar('T')
F = TypeVar('F', bound=Callable[..., Any])

# --- System Constants ---
def get_environment_config(key: str, default: T, cast_to: Type = str) -> T:
    """Retrieves configuration from environment variables with type conversion."""
    value = os.environ.get(key)
    if value is None:
        return default
    try:
        if cast_to is bool:
            return bool(value.lower() in ('true', '1', 'yes'))
        if value == "" and cast_to is not str:
             return default
        return cast_to(value)
    except (ValueError, TypeError):
        return default

# Cache thresholds
CACHE_SIZE_THRESHOLD_MIN = get_environment_config('CACHE_SIZE_THRESHOLD_MIN', 1024, int)  # 1KB
CACHE_SIZE_THRESHOLD_MAX = get_environment_config('CACHE_SIZE_THRESHOLD_MAX', 4096, int)  # 4KB
CACHE_COMPLEXITY_THRESHOLD = get_environment_config('CACHE_COMPLEXITY_THRESHOLD', 0.4, float)

# Model compatibility mapping
# Maps model name prefixes to their supported text editor tool versions.
# Assumes newer versions are backward compatible or superior.
TEXT_EDITOR_TOOL_VERSIONS = {
    "claude-3-opus-20240229": "text_editor_20250728", # Hypothetical future support
    "claude-3-sonnet-20240229": "text_editor_20250728", # Hypothetical future support
    "claude-3-haiku-20240307": "text_editor_20250124", # Hypothetical future support
    "claude-3-5-sonnet-20240620": "text_editor_20250124", # Sonnet 3.5 supports the newer tool
    "default": "text_editor_20241022", # Fallback for older/unspecified models
}

# Default model for fallback operations
DEFAULT_MODEL = "claude-3-5-sonnet-20240620"

# Model pricing per million tokens (as of late 2024, hypothetical)
# Prices are in USD.
# Cache pricing: write = input * 1.25, read = input * 0.10
_MODEL_PRICES_BASE = {
    "claude-3-opus-20240229": {"input": 15.00, "output": 75.00},
    "claude-3-sonnet-20240229": {"input": 3.00, "output": 15.00},
    "claude-3-haiku-20240307": {"input": 0.25, "output": 1.25},
    "claude-3-5-sonnet-20240620": {"input": 3.00, "output": 15.00},
}

MODEL_PRICES: Dict[str, Dict[str, float]] = {}
for model, prices in _MODEL_PRICES_BASE.items():
    input_price = prices["input"]
    MODEL_PRICES[model] = {
        "input": input_price,
        "output": prices["output"],
        "cache_input_write": input_price * 1.25,
        "cache_input_read": input_price * 0.10,
    }

# --- Security Constants ---
SENSITIVE_KEYS = re.compile(r'api_key|token|secret|authorization', re.IGNORECASE)
MAX_LOG_STR_LENGTH = 500


# ==============================================================================
# 2. Exception Classes
# ==============================================================================

class EditToolError(Exception):
    """Base exception class for all edit-file-tool errors.

    Attributes:
        message (str): A human-readable error message.
        context (Dict[str, Any]): A dictionary containing structured error context
            for debugging.
    """
    def __init__(self, message: str, context: Optional[Dict[str, Any]] = None):
        self.message = message
        self.context = context or {}
        super().__init__(self.message)

    def __str__(self) -> str:
        if self.context:
            ctx_str = ", ".join(f"{k}={v}" for k, v in self.context.items())
            return f"{self.message} (Context: {ctx_str})"
        return self.message

class FileOperationError(EditToolError):
    """Exception for file I/O related errors, e.g., permissions, not found."""
    pass

class APIError(EditToolError):
    """Exception for Claude API communication errors, e.g., network, auth."""
    pass

class ValidationError(EditToolError):
    """Exception for input validation failures, e.g., invalid path, bad config."""
    pass

class ModelCompatibilityError(EditToolError):
    """Exception for unsupported model/feature combinations."""
    pass


# ==============================================================================
# 3. Logging Infrastructure
# ==============================================================================

class JsonFormatter(logging.Formatter):
    """Formats log records as JSON strings."""
    def format(self, record: logging.LogRecord) -> str:
        # Standard attributes of a LogRecord
        reserved_attrs = (
            'args', 'asctime', 'created', 'exc_info', 'exc_text', 'filename',
            'funcName', 'levelname', 'levelno', 'lineno', 'module', 'msecs',
            'message', 'msg', 'name', 'pathname', 'process', 'processName',
            'relativeCreated', 'stack_info', 'thread', 'threadName'
        )
        log_record = {
            "timestamp": self.formatTime(record, self.datefmt),
            "level": record.levelname,
            "name": record.name,
            "message": record.getMessage(),
        }
        # Add any 'extra' fields passed to the logger
        for key, value in record.__dict__.items():
            if key not in reserved_attrs and not key.startswith('_'):
                log_record[key] = value

        if record.exc_info:
            log_record['exc_info'] = self.formatException(record.exc_info)
        return json.dumps(log_record)

def sanitize_for_logging(data: Any) -> Any:
    """Recursively sanitizes data by removing sensitive information for logging.

    Args:
        data: The data to sanitize (e.g., dict, list, str).

    Returns:
        The sanitized data.
    """
    if isinstance(data, dict):
        return {
            k: "[REDACTED]" if SENSITIVE_KEYS.search(k) else sanitize_for_logging(v)
            for k, v in data.items()
        }
    elif isinstance(data, list):
        return [sanitize_for_logging(item) for item in data]
    elif isinstance(data, str):
        return (data[:MAX_LOG_STR_LENGTH] + '...' if len(data) > MAX_LOG_STR_LENGTH else data)
    return data

def setup_logger(
    name: str,
    level: LogLevel = 'INFO',
    structured: bool = False,
    log_file: Optional[FilePath] = None
) -> logging.Logger:
    """Sets up a configurable async-safe logger.

    Args:
        name: The name of the logger.
        level: The minimum logging level.
        structured: If True, output logs in JSON format.
        log_file: Optional path to a file for log output with rotation.

    Returns:
        A configured logger instance.
    """
    logger = logging.getLogger(name)
    if logger.hasHandlers():
        logger.handlers.clear()

    logger.setLevel(level)
    log_format = '%(asctime)s - %(name)s - %(levelname)s - %(message)s'
    formatter = JsonFormatter() if structured else logging.Formatter(log_format)

    # Console handler
    console_handler = logging.StreamHandler(sys.stdout)
    console_handler.setFormatter(formatter)
    logger.addHandler(console_handler)

    # File handler with rotation
    if log_file:
        try:
            file_path = Path(log_file)
            file_path.parent.mkdir(parents=True, exist_ok=True)
            # Rotate logs at 5MB, keep 5 backup files
            file_handler = logging.handlers.RotatingFileHandler(
                file_path, maxBytes=5 * 1024 * 1024, backupCount=5
            )
            file_handler.setFormatter(formatter)
            logger.addHandler(file_handler)
        except (OSError, PermissionError) as e:
            logger.error(f"Failed to set up log file at {log_file}: {e}")

    # logger.propagate = False # This was preventing pytest caplog from capturing logs
    return logger

def get_logger(name: str) -> logging.Logger:
    """Gets or creates a logger instance for the specified module."""
    return logging.getLogger(name)

# ==============================================================================
# 4. Performance Decorators
# ==============================================================================

def retry(
    max_attempts: int = 3,
    backoff_factor: float = 1.5,
    exceptions: Tuple[Type[Exception], ...] = (APIError, asyncio.TimeoutError)
) -> Callable[[F], F]:
    """Decorator for retry logic with exponential backoff.

    Args:
        max_attempts: Maximum number of attempts.
        backoff_factor: Factor to increase delay between retries.
        exceptions: A tuple of exception types to catch and retry on.

    Returns:
        A decorator that wraps the function with retry logic.
    """
    def decorator(func: F) -> F:
        @functools.wraps(func)
        async def async_wrapper(*args, **kwargs):
            last_exception = None
            for attempt in range(max_attempts):
                try:
                    return await func(*args, **kwargs)
                except exceptions as e:
                    last_exception = e
                    if attempt == max_attempts - 1:
                        break  # Don't sleep on the last attempt
                    delay = backoff_factor ** attempt
                    logger = get_logger(func.__module__)
                    logger.warning(
                        f"Attempt {attempt + 1}/{max_attempts} failed for {func.__name__}: {e}. "
                        f"Retrying in {delay:.2f}s..."
                    )
                    await asyncio.sleep(delay)
            raise last_exception or EditToolError(f"{func.__name__} failed after {max_attempts} attempts.")

        @functools.wraps(func)
        def sync_wrapper(*args, **kwargs):
            last_exception = None
            for attempt in range(max_attempts):
                try:
                    return func(*args, **kwargs)
                except exceptions as e:
                    last_exception = e
                    if attempt == max_attempts - 1:
                        break  # Don't sleep on the last attempt
                    delay = backoff_factor ** attempt
                    logger = get_logger(func.__module__)
                    logger.warning(
                        f"Attempt {attempt + 1}/{max_attempts} failed for {func.__name__}: {e}. "
                        f"Retrying in {delay:.2f}s..."
                    )
                    time.sleep(delay)
            raise last_exception or EditToolError(f"{func.__name__} failed after {max_attempts} attempts.")

        if asyncio.iscoroutinefunction(func):
            return async_wrapper
        else:
            return sync_wrapper
    return decorator

def timed(logger: Optional[logging.Logger] = None) -> Callable[[F], F]:
    """Decorator for performance timing measurement.

    Args:
        logger: The logger to use for output. If None, uses the function's module logger.

    Returns:
        A decorator that wraps the function with timing logic.
    """
    def decorator(func: F) -> F:
        log = logger or get_logger(func.__module__)

        @functools.wraps(func)
        async def async_wrapper(*args, **kwargs):
            start_time = time.perf_counter()
            try:
                return await func(*args, **kwargs)
            finally:
                end_time = time.perf_counter()
                log.debug(f"'{func.__name__}' executed in {end_time - start_time:.4f}s")

        @functools.wraps(func)
        def sync_wrapper(*args, **kwargs):
            start_time = time.perf_counter()
            try:
                return func(*args, **kwargs)
            finally:
                end_time = time.perf_counter()
                log.debug(f"'{func.__name__}' executed in {end_time - start_time:.4f}s")

        if asyncio.iscoroutinefunction(func):
            return async_wrapper
        else:
            return sync_wrapper
    return decorator


# ==============================================================================
# 5. Validation Utilities
# ==============================================================================

@timed()
def validate_file_path(
    path: FilePath,
    must_exist: bool = False,
    allow_create: bool = True,
    base_dir: Optional[FilePath] = None
) -> Path:
    """Validates and normalizes file paths with security checks.

    Prevents directory traversal attacks by ensuring the resolved path is within
    a safe base directory (defaults to the current working directory).

    Args:
        path: The file path to validate.
        must_exist: If True, the file must already exist.
        allow_create: If True, the file's parent directory must exist.
        base_dir: The safe root directory. Defaults to os.getcwd().

    Returns:
        A resolved, validated pathlib.Path object.

    Raises:
        ValidationError: If the path is invalid or insecure.
        FileOperationError: If file system checks fail (e.g., not found).
    """
    if not path:
        raise ValidationError("File path cannot be empty.")

    safe_base_dir = Path(base_dir or os.getcwd()).resolve()
    
    try:
        # Resolve the path to make it absolute and normalize it.
        # strict=False allows resolving paths that don't exist yet.
        resolved_path = Path(path).resolve(strict=False)

        # Security Check: Prevent directory traversal
        if not str(resolved_path).startswith(str(safe_base_dir)):
            raise ValidationError(
                "Path is outside the allowed directory.",
                context={"path": str(path), "base_dir": str(safe_base_dir)}
            )
    except Exception as e:
        raise ValidationError(f"Invalid path provided: {path}", context={"error": str(e)})

    if must_exist and not resolved_path.exists():
        raise FileOperationError(f"File does not exist: {resolved_path}", context={"path": str(resolved_path)})

    if must_exist and not resolved_path.is_file():
        raise FileOperationError(f"Path is not a file: {resolved_path}", context={"path": str(resolved_path)})

    if allow_create and not must_exist and not resolved_path.parent.exists():
        raise FileOperationError(
            f"Parent directory does not exist for creation: {resolved_path.parent}",
            context={"path": str(resolved_path)}
        )

    return resolved_path

def check_model_compatibility(model: ModelName, feature: str) -> bool:
    """Checks if a model supports a specific feature.

    Args:
        model: The name of the model.
        feature: The feature to check (e.g., 'text_editor_20250124').

    Returns:
        True if the model supports the feature, False otherwise.
    """
    # Simple check: find the tool version for the given model
    model_tool_version = TEXT_EDITOR_TOOL_VERSIONS.get(model, TEXT_EDITOR_TOOL_VERSIONS["default"])
    
    # Assuming date-based versions, a higher date string means a newer/better version
    return model_tool_version >= feature

def sanitize_input(input_data: str, max_length: Optional[int] = None) -> str:
    """Sanitizes user input by removing control characters and limiting length.

    Args:
        input_data: The string to sanitize.
        max_length: The maximum allowed length of the string.

    Returns:
        The sanitized string.
    """
    # Remove control characters except for common whitespace like \n, \r, \t
    sanitized = re.sub(r'[\x00-\x08\x0b\x0c\x0e-\x1f\x7f]', '', input_data)
    if max_length is not None and len(sanitized) > max_length:
        sanitized = sanitized[:max_length]
    return sanitized


# ==============================================================================
# 6. Cost Management
# ==============================================================================

def get_model_prices(model: ModelName) -> Dict[str, float]:
    """Retrieves pricing information for a given Anthropic model.

    If the model is not found, it logs a warning and falls back to the
    default model's pricing to prevent crashes.

    Args:
        model: The name of the model.

    Returns:
        A dictionary with pricing details.
    """
    if model not in MODEL_PRICES:
        get_logger(__name__).warning(
            f"Model '{model}' not found in pricing list. "
            f"Falling back to '{DEFAULT_MODEL}' pricing."
        )
        return MODEL_PRICES[DEFAULT_MODEL]
    return MODEL_PRICES[model]

def calculate_cost(
    model: ModelName,
    input_tokens: int,
    output_tokens: int,
    cache_status: CacheStatus = "none"
) -> float:
    """Calculates the total cost of an LLM API call in USD.

    Args:
        model: The model used for the API call.
        input_tokens: The number of input tokens.
        output_tokens: The number of output tokens.
        cache_status: The caching status for the input prompt.

    Returns:
        The total calculated cost in USD.
    """
    prices = get_model_prices(model)
    
    input_cost = 0
    if cache_status == "write":
        input_cost = (input_tokens / 1_000_000) * prices["cache_input_write"]
    elif cache_status == "read":
        input_cost = (input_tokens / 1_000_000) * prices["cache_input_read"]
    else: # "none"
        input_cost = (input_tokens / 1_000_000) * prices["input"]
        
    output_cost = (output_tokens / 1_000_000) * prices["output"]
    
    return input_cost + output_cost

def calculate_cost_breakdown(
    model: ModelName,
    input_tokens: int,
    output_tokens: int,
    cache_status: CacheStatus = "none"
) -> Dict[str, Any]:
    """Provides a detailed cost breakdown for analysis.

    Args:
        model: The model used.
        input_tokens: The number of input tokens.
        output_tokens: The number of output tokens.
        cache_status: The caching status.

    Returns:
        A dictionary with a detailed cost breakdown.
    """
    prices = get_model_prices(model)
    
    if cache_status == "write":
        input_rate = prices["cache_input_write"]
    elif cache_status == "read":
        input_rate = prices["cache_input_read"]
    else:
        input_rate = prices["input"]
        
    output_rate = prices["output"]
    
    input_cost = (input_tokens / 1_000_000) * input_rate
    output_cost = (output_tokens / 1_000_000) * output_rate
    total_cost = input_cost + output_cost
    
    return {
        "model": model,
        "cache_status": cache_status,
        "input_tokens": input_tokens,
        "output_tokens": output_tokens,
        "input_cost": input_cost,
        "output_cost": output_cost,
        "total_cost": total_cost,
        "effective_input_rate_per_million": input_rate,
        "output_rate_per_million": output_rate,
    }

def format_cost(cost: float, precision: int = 4) -> str:
    """Formats cost values for consistent display."""
    return f"${cost:.{precision}f}"


# ==============================================================================
# 7. Cache Strategy
# ==============================================================================

def calculate_cache_complexity(content: str) -> float:
    """Calculates a content complexity score for cache decision making.

    The score is based on a weighted average of normalized line count and
    content density (characters per line). A higher score suggests a more
    complex file that would benefit from caching.

    Args:
        content: The string content of the file.

    Returns:
        A complexity score between 0.0 and 1.0.
    """
    lines = content.splitlines()
    num_lines = len(lines)
    if num_lines == 0:
        return 0.0

    content_length = len(content)
    density = content_length / num_lines if num_lines > 0 else 0

    # Normalize metrics to a 0-1 scale
    # Line count: normalized against a typical "complex" file of 500 lines
    line_count_norm = min(1.0, num_lines / 500.0)
    # Density: normalized against a typical dense line length of 120 chars
    density_norm = min(1.0, density / 120.0)

    # Weighted average: give more weight to line count
    complexity_score = (0.6 * line_count_norm) + (0.4 * density_norm)
    return complexity_score

@timed()
def should_use_cache(file_path: FilePath, file_content: str) -> bool:
    """Determines whether to use prompt caching based on file size and complexity.

    The logic is as follows:
    - Disabled for files smaller than CACHE_SIZE_THRESHOLD_MIN (1KB).
    - Enabled for files larger than CACHE_SIZE_THRESHOLD_MAX (4KB).
    - For files in between, the decision is based on a complexity score
      calculated from line count and content density.

    Args:
        file_path: The path to the file (used for logging/context).
        file_content: The content of the file.

    Returns:
        True if caching is recommended, False otherwise.
    """
    try:
        file_size = len(file_content.encode('utf-8'))
    except Exception:
        # Fallback for content that can't be encoded
        file_size = len(file_content)

    if file_size < CACHE_SIZE_THRESHOLD_MIN:
        return False
    if file_size > CACHE_SIZE_THRESHOLD_MAX:
        return True

    # For files between 1KB and 4KB, use complexity analysis
    complexity = calculate_cache_complexity(file_content)
    get_logger(__name__).debug(
        f"Cache complexity for {file_path}: {complexity:.2f} "
        f"(Threshold: {CACHE_COMPLEXITY_THRESHOLD})"
    )
    return complexity >= CACHE_COMPLEXITY_THRESHOLD


# ==============================================================================
# 8. System Integration and Formatting
# ==============================================================================

def check_system_compatibility() -> Dict[str, Any]:
    """Checks system requirements and compatibility."""
    py_version = sys.version_info
    return {
        "python_version": f"{py_version.major}.{py_version.minor}.{py_version.micro}",
        "python_version_ok": py_version >= (3, 9),
        "platform": sys.platform,
    }

def format_metrics(metrics: Dict[str, Any]) -> str:
    """Formats performance and cost metrics for display."""
    lines = ["--- Metrics ---"]
    for key, value in metrics.items():
        if "cost" in key and isinstance(value, (int, float)):
            lines.append(f"{key.replace('_', ' ').title()}: {format_cost(value)}")
        elif isinstance(value, float):
            lines.append(f"{key.replace('_', ' ').title()}: {value:.4f}")
        else:
            lines.append(f"{key.replace('_', ' ').title()}: {value}")
    return "\n".join(lines)
