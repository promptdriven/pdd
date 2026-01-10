"""
Example usage of the ClickCommandExecutor module.

This script demonstrates how to:
1. Define simple Click commands for testing.
2. Execute commands programmatically using ClickCommandExecutor.
3. Capture standard output and standard error.
4. Handle real-time output streaming via callbacks.
5. Manage errors and exceptions during command execution.

Prerequisites:
- Ensure 'click' is installed (`pip install click`).
- The `click_executor.py` module should be in the python path.
"""

import sys
import time
import click
from typing import Dict, Any

# Import from the provided module
# Assuming the module is saved as 'click_executor.py' in the same directory
try:
    from click_executor import ClickCommandExecutor, CapturedOutput
except ImportError:
    # Fallback for demonstration if running directly without package structure
    sys.path.append(".")
    try:
        from click_executor import ClickCommandExecutor, CapturedOutput
    except ImportError:
        # If the module is still not found, we define placeholders to avoid linting errors in this example
        class CapturedOutput:
            def __init__(self, stdout, stderr, exit_code, exception):
                self.stdout = stdout
                self.stderr = stderr
                self.exit_code = exit_code
                self.exception = exception
        class ClickCommandExecutor:
            def __init__(self, output_callback=None, base_context_obj=None):
                pass
            def execute(self, command, args=None, options=None):
                return CapturedOutput("", "", 0, None)


# ============================================================================
# 1. Define Sample Click Commands
# ============================================================================

@click.command()
@click.argument("name")
@click.option("--count", default=1, help="Number of greetings.")
@click.option("--loud", is_flag=True, help="Shout the greeting.")
def greet(name: str, count: int, loud: bool):
    """Simple greeting command."""
    greeting = f"Hello, {name}!"
    if loud:
        greeting = greeting.upper()
    
    for _ in range(count):
        click.echo(greeting)
        # Simulate some work for streaming demonstration
        time.sleep(0.1)

@click.command()
def fail_command():
    """A command that fails intentionally."""
    click.echo("Starting risky operation...", nl=True)
    click.echo("Something went wrong!", err=True)
    raise click.ClickException("Critical system failure.")

# ============================================================================
# 2. Demonstration Functions
# ============================================================================

def demo_basic_execution():
    """Demonstrates basic command execution with output capture."""
    print("\n--- Demo: Basic Execution ---")
    
    executor = ClickCommandExecutor()
    
    # Execute the 'greet' command
    # Equivalent to CLI: greet "World" --count 3
    print("Executing: greet 'World' --count 3")
    result: CapturedOutput = executor.execute(
        command=greet,
        args={"name": "World"},
        options={"count": 3}
    )
    
    print(f"Exit Code: {result.exit_code}")
    print("Captured Stdout:")
    print(f"'{result.stdout.strip()}'")


def demo_streaming_execution():
    """Demonstrates real-time output streaming via callback."""
    print("\n--- Demo: Streaming Execution ---")
    
    # Define a callback to handle real-time output
    def stream_callback(stream_type: str, text: str):
        prefix = "[STREAM-OUT]" if stream_type == "stdout" else "[STREAM-ERR]"
        # We use sys.stdout.write directly to avoid double newlines from print
        sys.stdout.write(f"{prefix} {text}")
        sys.stdout.flush()

    executor = ClickCommandExecutor(output_callback=stream_callback)
    
    # Execute the 'greet' command
    # Equivalent to CLI: greet "Streamer" --count 3 --loud
    print("Executing: greet 'Streamer' --count 3 --loud")
    result = executor.execute(
        command=greet,
        args={"name": "Streamer"},
        options={"count": 3, "loud": True}
    )
    
    print(f"\nFinal Exit Code: {result.exit_code}")
    # Note: result.stdout still contains the full captured output even when streaming
    print(f"Total captured length: {len(result.stdout)} chars")


def demo_error_handling():
    """Demonstrates handling of command failures and stderr capture."""
    print("\n--- Demo: Error Handling ---")
    
    executor = ClickCommandExecutor()
    
    print("Executing: fail_command")
    result = executor.execute(command=fail_command)
    
    print(f"Exit Code: {result.exit_code}")
    
    if result.stdout:
        print("Captured Stdout:")
        print(result.stdout.strip())
        
    if result.stderr:
        print("Captured Stderr:")
        print(result.stderr.strip())
        
    if result.exception:
        print(f"Caught Exception Type: {type(result.exception).__name__}")


def demo_context_passing():
    """Demonstrates passing shared context state."""
    print("\n--- Demo: Context Passing ---")
    
    # Define a command that uses ctx.obj
    @click.command()
    @click.pass_context
    def check_config(ctx):
        strength = ctx.obj.get("strength")
        verbose = ctx.obj.get("verbose")
        click.echo(f"Config: strength={strength}, verbose={verbose}")

    # Initialize executor with base context
    base_context = {"strength": 0.9, "verbose": True}
    executor = ClickCommandExecutor(base_context_obj=base_context)
    
    result = executor.execute(command=check_config)
    print(f"Output: {result.stdout.strip()}")


# ============================================================================
# Main Entry Point
# ============================================================================

if __name__ == "__main__":
    try:
        demo_basic_execution()
        demo_streaming_execution()
        demo_error_handling()
        demo_context_passing()
    except Exception as e:
        print(f"An unexpected error occurred in the example script: {e}")