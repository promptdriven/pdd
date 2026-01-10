from __future__ import annotations

import io
import sys
from dataclasses import dataclass
from typing import Any, Callable, Dict, Optional
from unittest.mock import MagicMock

import click
from rich.console import Console

# Attempt to import global constants, falling back to safe defaults if package structure varies
try:
    from .. import DEFAULT_STRENGTH, DEFAULT_TIME
except ImportError:
    DEFAULT_STRENGTH = 0.5
    DEFAULT_TIME = None


@dataclass
class CapturedOutput:
    """
    Container for captured command output and execution results.
    """
    stdout: str
    stderr: str
    exit_code: int
    exception: Optional[Exception] = None
    result: Optional[Any] = None
    cost: float = 0.0


class StreamingWriter:
    """
    Writer that both buffers output to a StringIO and calls a callback for real-time streaming.
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
        """Write text to buffer and trigger callback."""
        self._buffer.write(text)
        if self._callback and text:
            self._callback(self._stream_type, text)
        return len(text)

    def flush(self) -> None:
        """Flush the underlying buffer."""
        self._buffer.flush()

    def isatty(self) -> bool:
        """Return False to indicate this is not a terminal."""
        return False


class OutputCapture:
    """
    Context manager that captures stdout and stderr during command execution.
    Supports real-time streaming via a callback.
    """

    def __init__(self, callback: Optional[Callable[[str, str], None]] = None):
        """
        Initialize output capture.

        Args:
            callback: Optional callback(stream_type, text) for real-time streaming.
                      stream_type will be "stdout" or "stderr".
        """
        self._callback = callback
        self._stdout_buffer = io.StringIO()
        self._stderr_buffer = io.StringIO()
        self._original_stdout = sys.stdout
        self._original_stderr = sys.stderr

    def __enter__(self) -> "OutputCapture":
        # Redirect streams
        sys.stdout = StreamingWriter(self._stdout_buffer, self._callback, "stdout")  # type: ignore
        sys.stderr = StreamingWriter(self._stderr_buffer, self._callback, "stderr")  # type: ignore
        return self

    def __exit__(self, exc_type: Any, exc_val: Any, exc_tb: Any) -> bool:
        # Restore streams
        sys.stdout = self._original_stdout
        sys.stderr = self._original_stderr
        return False  # Propagate exceptions

    @property
    def stdout(self) -> str:
        """Get captured stdout content."""
        return self._stdout_buffer.getvalue()

    @property
    def stderr(self) -> str:
        """Get captured stderr content."""
        return self._stderr_buffer.getvalue()


def create_isolated_context(
    command: click.Command,
    obj: Optional[Dict[str, Any]] = None,
    color: bool = False,
) -> click.Context:
    """
    Create an isolated Click context for programmatic command execution.

    This sets up the context object (ctx.obj) with PDD global defaults and
    mocks parameter sources to ensure smooth execution outside the CLI loop.

    Args:
        command: The Click command to create context for.
        obj: Optional dictionary to populate ctx.obj (merged with defaults).
        color: Whether to enable ANSI colors in output.

    Returns:
        Configured Click context.
    """
    ctx = click.Context(command, color=color)

    # Default PDD global options
    default_obj = {
        "strength": DEFAULT_STRENGTH,
        "temperature": 0.0,
        "time": DEFAULT_TIME,
        "verbose": False,
        "force": False,
        "quiet": False,
        "output_cost": None,
        "review_examples": False,
        "local": False,
        "context": None,
        "confirm_callback": None,
    }

    # Merge provided obj with defaults
    ctx.obj = {**default_obj, **(obj or {})}

    # Mock parameter source checking to return DEFAULT.
    # This prevents Click from erroring when checking how parameters were supplied.
    mock_source = MagicMock()
    mock_source.name = "DEFAULT"
    ctx.get_parameter_source = MagicMock(return_value=mock_source)

    return ctx


class ClickCommandExecutor:
    """
    Executes Click commands programmatically with output capture and error handling.
    """

    def __init__(
        self,
        base_context_obj: Optional[Dict[str, Any]] = None,
        output_callback: Optional[Callable[[str, str], None]] = None,
    ):
        """
        Initialize the executor.

        Args:
            base_context_obj: Base context object to be merged into every execution.
            output_callback: Callback for real-time output streaming.
        """
        self._base_context_obj = base_context_obj or {}
        self._output_callback = output_callback

    def execute(
        self,
        command: click.Command,
        params: Optional[Dict[str, Any]] = None,
        context_obj: Optional[Dict[str, Any]] = None,
    ) -> CapturedOutput:
        """
        Execute a Click command with the given parameters.

        Args:
            command: Click command to execute.
            params: Parameters to pass to the command (arguments and options).
            context_obj: Optional context object overrides for this specific execution.

        Returns:
            CapturedOutput object containing results and logs.
        """
        # Merge context objects
        obj = {**self._base_context_obj, **(context_obj or {})}

        # Create isolated context
        ctx = create_isolated_context(command, obj)

        # Capture output
        capture = OutputCapture(callback=self._output_callback)

        result_val = None
        cost = 0.0

        try:
            with capture:
                with ctx:
                    # Invoke the command with parameters
                    # Note: standalone_mode=False prevents Click from handling exceptions (sys.exit)
                    # but ctx.invoke doesn't use standalone_mode. It just calls the callback.
                    result_val = ctx.invoke(command, **(params or {}))

            # Attempt to extract cost from result if available
            # PDD commands often return a tuple where the second element is cost,
            # or a dict with a 'cost' key.
            if isinstance(result_val, tuple) and len(result_val) >= 2:
                # Common pattern: (result_str, cost, model_name)
                if isinstance(result_val[1], (int, float)):
                    cost = float(result_val[1])
            elif isinstance(result_val, dict) and "cost" in result_val:
                cost = float(result_val["cost"])
            elif hasattr(result_val, "cost"):
                cost = float(result_val.cost)

            return CapturedOutput(
                stdout=capture.stdout,
                stderr=capture.stderr,
                exit_code=0,
                result=result_val,
                cost=cost,
            )

        except click.Abort:
            return CapturedOutput(
                stdout=capture.stdout,
                stderr=capture.stderr,
                exit_code=1,
                exception=click.Abort(),
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


def get_pdd_command(command_name: str) -> Optional[click.Command]:
    """
    Get a PDD Click command object by name.
    Uses lazy imports to avoid circular dependencies.

    Args:
        command_name: Name of the command (e.g., "sync", "generate").

    Returns:
        The Click command object or None if not found.
    """
    # Lazy imports to avoid circular dependencies with the main CLI module
    try:
        from ..commands.sync import sync
        from ..commands.update import update
        from ..commands.bug import bug
        from ..commands.generate import generate
        from ..commands.test import test
        from ..commands.fix import fix
        from ..commands.example import example
        from ..commands.preprocess import preprocess
        from ..commands.split import split
        from ..commands.change import change
        from ..commands.detect import detect
        from ..commands.conflicts import conflicts
        from ..commands.crash import crash
    except ImportError:
        # Fallback for testing or incomplete environments
        return None

    commands_map = {
        "sync": sync,
        "update": update,
        "bug": bug,
        "generate": generate,
        "test": test,
        "fix": fix,
        "example": example,
        "preprocess": preprocess,
        "split": split,
        "change": change,
        "detect": detect,
        "conflicts": conflicts,
        "crash": crash,
    }

    return commands_map.get(command_name)


def execute_pdd_command(
    command_name: str,
    args: Optional[Dict[str, Any]] = None,
    options: Optional[Dict[str, Any]] = None,
    callback: Optional[Callable[[str, str], None]] = None,
) -> CapturedOutput:
    """
    High-level helper to execute a PDD command by name.

    Args:
        command_name: The name of the command to run (e.g., 'generate').
        args: Dictionary of arguments/options to pass to the command.
        options: Dictionary of global options (ctx.obj overrides).
        callback: Optional callback for output streaming.

    Returns:
        CapturedOutput object.
    """
    command = get_pdd_command(command_name)
    if not command:
        return CapturedOutput(
            stdout="",
            stderr=f"Error: Command '{command_name}' not found.",
            exit_code=1,
            exception=ValueError(f"Unknown command: {command_name}"),
        )

    executor = ClickCommandExecutor(
        base_context_obj=options,
        output_callback=callback,
    )

    return executor.execute(command, params=args)