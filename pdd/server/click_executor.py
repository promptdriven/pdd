"""
Click Command Executor for PDD Server.

This module provides functionality to programmatically execute Click commands with:
- Isolated Click context creation
- Output capture (stdout/stderr)
- Error handling
- Real-time streaming via callback
"""

from __future__ import annotations

import io
import os
import sys
from dataclasses import dataclass, field
from typing import Any, Callable, Dict, Optional
from unittest.mock import MagicMock

import click


def _setup_headless_environment():
    """
    Set up environment variables for headless command execution.

    This ensures commands run in non-interactive mode without TUI,
    which is necessary when running programmatically through the server.

    NOTE: This should only be called when actually executing commands through
    the server, NOT at module import time. Calling at import time would
    affect ALL pdd commands (including CLI usage) because the connect command
    imports this module transitively.
    """
    os.environ['CI'] = '1'  # Triggers headless mode in sync and other commands
    os.environ['PDD_FORCE'] = '1'  # Skip confirmation prompts
    os.environ['TERM'] = 'dumb'  # Disable fancy terminal features


# NOTE: Do NOT call _setup_headless_environment() here at import time!
# It will be called by ClickCommandExecutor when executing commands.


# ============================================================================
# Output Capture
# ============================================================================

@dataclass
class CapturedOutput:
    """Container for captured command output."""
    stdout: str = ""
    stderr: str = ""
    exit_code: int = 0
    exception: Optional[Exception] = None
    cost: float = 0.0


class StreamingWriter:
    """
    Writer that both buffers output and calls a callback for streaming.
    """

    def __init__(
        self,
        buffer: io.StringIO,
        callback: Optional[Callable[[str, str], None]],
        stream_type: str,
    ):
        self._buffer = buffer
        self._callback = callback
        self._stream_type = stream_type

    def write(self, text: str) -> int:
        self._buffer.write(text)
        if self._callback and text:
            self._callback(self._stream_type, text)
        return len(text)

    def flush(self):
        self._buffer.flush()

    def isatty(self) -> bool:
        return False


class OutputCapture:
    """
    Captures stdout and stderr during command execution.

    Usage:
        with OutputCapture() as capture:
            # Execute command
            result = some_function()

        print(capture.stdout)
        print(capture.stderr)
    """

    def __init__(self, callback: Optional[Callable[[str, str], None]] = None):
        """
        Initialize output capture.

        Args:
            callback: Optional callback(stream_type, text) for real-time streaming
        """
        self._callback = callback
        self._stdout_buffer = io.StringIO()
        self._stderr_buffer = io.StringIO()
        self._original_stdout = None
        self._original_stderr = None

    def __enter__(self) -> "OutputCapture":
        self._original_stdout = sys.stdout
        self._original_stderr = sys.stderr

        if self._callback:
            # Use streaming wrappers
            sys.stdout = StreamingWriter(self._stdout_buffer, self._callback, "stdout")
            sys.stderr = StreamingWriter(self._stderr_buffer, self._callback, "stderr")
        else:
            sys.stdout = self._stdout_buffer
            sys.stderr = self._stderr_buffer

        return self

    def __exit__(self, exc_type, exc_val, exc_tb):
        sys.stdout = self._original_stdout
        sys.stderr = self._original_stderr
        return False

    @property
    def stdout(self) -> str:
        return self._stdout_buffer.getvalue()

    @property
    def stderr(self) -> str:
        return self._stderr_buffer.getvalue()


# ============================================================================
# Click Context Factory
# ============================================================================

def create_isolated_context(
    command: click.Command,
    obj: Optional[Dict[str, Any]] = None,
    color: bool = False,
) -> click.Context:
    """
    Create an isolated Click context for programmatic command execution.

    Args:
        command: The Click command to create context for
        obj: Context object (ctx.obj) with shared state
        color: Whether to enable ANSI colors in output

    Returns:
        Configured Click context
    """
    # Create context with the command
    ctx = click.Context(command, color=color)

    # Set context object (shared state between commands)
    ctx.obj = obj or {
        "strength": 0.5,
        "temperature": 0.1,
        "time": 0.25,
        "verbose": False,
        "force": False,
        "quiet": False,
        "output_cost": None,
        "review_examples": False,
        "local": False,
        "context": None,
    }

    # Mock parameter source checking (returns DEFAULT for all)
    mock_source = MagicMock()
    mock_source.name = "DEFAULT"
    ctx.get_parameter_source = MagicMock(return_value=mock_source)

    return ctx


# ============================================================================
# Command Executor
# ============================================================================

# Options that should be integers when passed to Click commands
INTEGER_OPTIONS = {
    'max_attempts', 'target_coverage', 'depth', 'limit',
    'max_tokens', 'timeout', 'retries', 'iterations',
}

# Options that should be floats when passed to Click commands
FLOAT_OPTIONS = {
    'strength', 'temperature', 'time', 'threshold', 'budget',
}

# Options that should be booleans when passed to Click commands
BOOLEAN_OPTIONS = {
    'verbose', 'quiet', 'force', 'loop', 'skip_verify', 'skip_tests',
    'local', 'dry_run', 'auto_submit', 'recursive',
}


def _convert_option_type(key: str, value: Any) -> Any:
    """
    Convert option value to the appropriate type based on the option name.

    Args:
        key: The option name (with underscores, not hyphens)
        value: The value to convert

    Returns:
        The value converted to the appropriate type
    """
    if value is None:
        return None

    normalized_key = key.replace("-", "_")

    # Handle integers
    if normalized_key in INTEGER_OPTIONS:
        if isinstance(value, int):
            return value
        if isinstance(value, str):
            try:
                return int(value)
            except ValueError:
                return value
        return value

    # Handle floats
    if normalized_key in FLOAT_OPTIONS:
        if isinstance(value, (int, float)):
            return float(value)
        if isinstance(value, str):
            try:
                return float(value)
            except ValueError:
                return value
        return value

    # Handle booleans
    if normalized_key in BOOLEAN_OPTIONS:
        if isinstance(value, bool):
            return value
        if isinstance(value, str):
            return value.lower() in ('true', '1', 'yes', 'on')
        return bool(value)

    return value


class ClickCommandExecutor:
    """
    Executes Click commands programmatically with output capture.

    This class provides:
    - Isolated context creation
    - Output capture (stdout/stderr)
    - Error handling
    - Real-time streaming via callback

    Usage:
        executor = ClickCommandExecutor()

        # Execute a command
        result = executor.execute(
            command=sync_command,
            params={"basename": "hello", "max_attempts": 3},
        )

        print(result.stdout)
        print(f"Exit code: {result.exit_code}")
    """

    def __init__(
        self,
        base_context_obj: Optional[Dict[str, Any]] = None,
        output_callback: Optional[Callable[[str, str], None]] = None,
    ):
        """
        Initialize the executor.

        Args:
            base_context_obj: Base context object for all commands
            output_callback: Callback for real-time output streaming
        """
        self._base_context_obj = base_context_obj or {}
        self._output_callback = output_callback

    def execute(
        self,
        command: click.Command,
        args: Optional[Dict[str, Any]] = None,
        options: Optional[Dict[str, Any]] = None,
        capture_output: bool = True,
    ) -> CapturedOutput:
        """
        Execute a Click command with the given parameters.

        Args:
            command: Click command to execute
            args: Positional arguments to pass to the command
            options: Options/flags to pass to the command
            capture_output: If True, capture stdout/stderr. If False, output goes to terminal.

        Returns:
            CapturedOutput with stdout, stderr, exit_code
        """
        # Set up headless environment for server-executed commands
        _setup_headless_environment()

        # Merge context objects
        obj = {**self._base_context_obj, **(options or {})}

        # Merge args and options into params
        # Convert hyphens to underscores in keys (CLI uses hyphens, Python uses underscores)
        # Also convert string values to appropriate types for known options
        params = {}
        if args:
            for key, value in args.items():
                normalized_key = key.replace("-", "_")
                params[normalized_key] = _convert_option_type(normalized_key, value)
        if options:
            for key, value in options.items():
                normalized_key = key.replace("-", "_")
                params[normalized_key] = _convert_option_type(normalized_key, value)

        # Create isolated context
        ctx = create_isolated_context(command, obj)

        if capture_output:
            # Capture output mode
            capture = OutputCapture(callback=self._output_callback)

            try:
                with capture:
                    with ctx:
                        # Invoke the command with parameters
                        result = ctx.invoke(command, **params)

                return CapturedOutput(
                    stdout=capture.stdout,
                    stderr=capture.stderr,
                    exit_code=0,
                )

            except click.Abort:
                return CapturedOutput(
                    stdout=capture.stdout,
                    stderr=capture.stderr,
                    exit_code=1,
                )

            except click.ClickException as e:
                return CapturedOutput(
                    stdout=capture.stdout,
                    stderr=capture.stderr + f"\nError: {e.format_message()}",
                    exit_code=e.exit_code,
                    exception=e,
                )

            except Exception as e:
                return CapturedOutput(
                    stdout=capture.stdout,
                    stderr=capture.stderr + f"\nException: {str(e)}",
                    exit_code=1,
                    exception=e,
                )
        else:
            # Terminal mode - output goes directly to terminal
            try:
                with ctx:
                    result = ctx.invoke(command, **params)
                return CapturedOutput(exit_code=0)

            except click.Abort:
                return CapturedOutput(exit_code=1)

            except click.ClickException as e:
                print(f"Error: {e.format_message()}", file=sys.stderr)
                return CapturedOutput(exit_code=e.exit_code, exception=e)

            except Exception as e:
                print(f"Exception: {str(e)}", file=sys.stderr)
                return CapturedOutput(exit_code=1, exception=e)


# ============================================================================
# PDD Command Registry
# ============================================================================

# Command registry - lazily populated to avoid circular imports
_command_cache: Dict[str, click.Command] = {}


def get_pdd_command(command_name: str) -> Optional[click.Command]:
    """
    Get a PDD Click command by name.

    This function maps command names to their Click command objects.
    Commands are imported lazily to avoid circular imports.

    Args:
        command_name: Name of the command (e.g., "sync", "generate")

    Returns:
        Click command object or None if not found
    """
    # Return from cache if available
    if command_name in _command_cache:
        return _command_cache[command_name]

    # Import commands lazily
    try:
        if command_name == "sync":
            from pdd.commands.maintenance import sync
            _command_cache[command_name] = sync
            return sync

        elif command_name == "update":
            from pdd.commands.modify import update
            _command_cache[command_name] = update
            return update

        elif command_name == "generate":
            from pdd.commands.generate import generate
            _command_cache[command_name] = generate
            return generate

        elif command_name == "test":
            from pdd.commands.generate import test
            _command_cache[command_name] = test
            return test

        elif command_name == "fix":
            from pdd.commands.fix import fix
            _command_cache[command_name] = fix
            return fix

        elif command_name == "example":
            from pdd.commands.generate import example
            _command_cache[command_name] = example
            return example

        elif command_name == "bug":
            from pdd.commands.analysis import bug
            _command_cache[command_name] = bug
            return bug

        elif command_name == "crash":
            from pdd.commands.analysis import crash
            _command_cache[command_name] = crash
            return crash

        elif command_name == "verify":
            from pdd.commands.utility import verify
            _command_cache[command_name] = verify
            return verify

        else:
            return None

    except ImportError as e:
        # Log import error but don't crash
        import logging
        logging.warning(f"Failed to import command '{command_name}': {e}")
        return None
