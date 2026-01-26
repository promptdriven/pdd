"""
Click Command Executor Example for PDD Server.

This example demonstrates how to programmatically execute Click commands with:
- Isolated Click context creation
- Output capture (stdout/stderr)
- Error handling
- Parameter injection

Documentation references:
- Click: https://click.palletsprojects.com/en/8.1.x/
- Click Testing: https://click.palletsprojects.com/en/8.1.x/testing/
- Click Context: https://click.palletsprojects.com/en/8.1.x/api/#click.Context
- io.StringIO: https://docs.python.org/3/library/io.html#io.StringIO
"""

import io
import sys
from contextlib import contextmanager, redirect_stdout, redirect_stderr
from dataclasses import dataclass
from pathlib import Path
from typing import Any, Callable, Dict, List, Optional, Tuple
from unittest.mock import MagicMock

import click


# ============================================================================
# Output Capture
# ============================================================================

@dataclass
class CapturedOutput:
    """Container for captured command output."""
    stdout: str
    stderr: str
    exit_code: int
    exception: Optional[Exception] = None


class OutputCapture:
    """
    Captures stdout and stderr during command execution.

    This is similar to the OutputCapture class in pdd/core/cli.py
    but adapted for use in the server context.

    Usage:
        with OutputCapture() as capture:
            # Execute command
            result = some_function()

        print(capture.stdout)
        print(capture.stderr)
    """

    def __init__(self, callback: Callable[[str, str], None] = None):
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


class StreamingWriter:
    """
    Writer that both buffers output and calls a callback for streaming.
    """

    def __init__(
        self,
        buffer: io.StringIO,
        callback: Callable[[str, str], None],
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


# ============================================================================
# Click Context Factory
# ============================================================================

def create_isolated_context(
    command: click.Command,
    obj: Dict[str, Any] = None,
    color: bool = False,
) -> click.Context:
    """
    Create an isolated Click context for programmatic command execution.

    This mimics the context that Click creates when running commands
    from the CLI, but allows us to control the environment.

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
        base_context_obj: Dict[str, Any] = None,
        output_callback: Callable[[str, str], None] = None,
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
        params: Dict[str, Any] = None,
        context_obj: Dict[str, Any] = None,
    ) -> CapturedOutput:
        """
        Execute a Click command with the given parameters.

        Args:
            command: Click command to execute
            params: Parameters to pass to the command
            context_obj: Optional context object (merged with base)

        Returns:
            CapturedOutput with stdout, stderr, exit_code
        """
        # Merge context objects
        obj = {**self._base_context_obj, **(context_obj or {})}

        # Create isolated context
        ctx = create_isolated_context(command, obj)

        # Capture output
        capture = OutputCapture(callback=self._output_callback)

        try:
            with capture:
                with ctx:
                    # Invoke the command with parameters
                    result = ctx.invoke(command, **(params or {}))

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


# ============================================================================
# PDD Command Mapping
# ============================================================================

def get_pdd_command(command_name: str) -> Optional[click.Command]:
    """
    Get a PDD Click command by name.

    This function maps command names to their Click command objects.
    In real implementation, this would import from pdd.commands.

    Args:
        command_name: Name of the command (e.g., "sync", "generate")

    Returns:
        Click command object or None if not found
    """
    # Import commands lazily to avoid circular imports
    # In real implementation:
    # from pdd.commands import sync, generate, fix, test, update, bug

    # For this example, we create a mock command
    @click.command(command_name)
    @click.argument("basename", required=False)
    @click.option("--max-attempts", type=int, default=3)
    @click.option("--budget", type=float, default=1.0)
    @click.pass_context
    def mock_command(ctx, basename, max_attempts, budget):
        """Mock PDD command for demonstration."""
        print(f"Executing {command_name}...")
        print(f"  basename: {basename}")
        print(f"  max_attempts: {max_attempts}")
        print(f"  budget: ${budget:.2f}")
        print(f"  context.obj: {ctx.obj}")
        return {"success": True, "cost": 0.05}

    return mock_command


# ============================================================================
# Example Usage
# ============================================================================

def main():
    """
    Example demonstrating Click command execution.
    """
    print("Click Command Executor Example")
    print("=" * 40)

    # Create a sample command
    @click.command("sample")
    @click.argument("name")
    @click.option("--greeting", default="Hello")
    @click.option("--count", type=int, default=1)
    @click.pass_context
    def sample_command(ctx, name, greeting, count):
        """Sample command that prints a greeting."""
        for i in range(count):
            print(f"{greeting}, {name}! (iteration {i + 1})")

        if ctx.obj.get("verbose"):
            print(f"Context: {ctx.obj}")

        return {"message": f"Greeted {name} {count} times"}

    # Create executor with streaming callback
    def stream_callback(stream_type: str, text: str):
        prefix = "[OUT]" if stream_type == "stdout" else "[ERR]"
        print(f"{prefix} {text}", end="")

    executor = ClickCommandExecutor(
        base_context_obj={"verbose": True, "force": False},
        output_callback=stream_callback,
    )

    # Execute the command
    print("\n1. Executing with streaming:")
    print("-" * 40)
    result = executor.execute(
        command=sample_command,
        params={"name": "World", "greeting": "Hi", "count": 3},
    )

    print("-" * 40)
    print(f"\nExit code: {result.exit_code}")
    print(f"Full stdout:\n{result.stdout}")

    # Execute with error
    print("\n2. Executing command that raises error:")
    print("-" * 40)

    @click.command("failing")
    def failing_command():
        """Command that fails."""
        raise click.ClickException("Something went wrong!")

    result = executor.execute(command=failing_command, params={})
    print(f"Exit code: {result.exit_code}")
    print(f"Stderr: {result.stderr}")

    # Show how to use with PDD commands
    print("\n3. Mock PDD command execution:")
    print("-" * 40)

    sync_cmd = get_pdd_command("sync")
    result = executor.execute(
        command=sync_cmd,
        params={"basename": "hello", "max_attempts": 5, "budget": 2.0},
    )
    print(f"Exit code: {result.exit_code}")


if __name__ == "__main__":
    main()
