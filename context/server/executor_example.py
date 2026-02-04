import sys
import click
from typing import Dict, Any
from rich.console import Console

# In a real application, you would import from your package structure
# from pdd.server.executor import ClickCommandExecutor, execute_pdd_command, CapturedOutput

# Mocking the module import for this standalone example
try:
    from pdd.server.executor import ClickCommandExecutor, execute_pdd_command, CapturedOutput
except ImportError:
    # Fallback if running outside the package context for demonstration
    sys.path.append(".")  # Adjust path as needed
    try:
        from executor import ClickCommandExecutor, execute_pdd_command, CapturedOutput
    except ImportError:
        # Define stubs if the module is completely missing to ensure the script is parseable
        class CapturedOutput:
            def __init__(self, stdout, stderr, exit_code, result, cost):
                self.stdout = stdout
                self.stderr = stderr
                self.exit_code = exit_code
                self.result = result
                self.cost = cost

        class ClickCommandExecutor:
            def __init__(self, base_context_obj=None, output_callback=None):
                self.base_context_obj = base_context_obj
                self.output_callback = output_callback
            def execute(self, command, params):
                return CapturedOutput("", "", 0, {}, 0.0)

        def execute_pdd_command(*args, **kwargs):
            return CapturedOutput("", "", 0, {}, 0.0)

console = Console()

# ---------------------------------------------------------------------------
# 1. Define a sample Click command to execute
# ---------------------------------------------------------------------------
@click.command("greet")
@click.argument("name")
@click.option("--count", default=1, help="Number of times to greet.")
@click.option("--loud", is_flag=True, help="Shout the greeting.")
@click.pass_context
def greet_command(ctx: click.Context, name: str, count: int, loud: bool) -> Dict[str, Any]:
    """Simple command that prints greetings."""
    greeting = "HELLO" if loud else "Hello"
    
    # Access global context options injected by the executor
    strength = ctx.obj.get("strength", 0.5) if ctx.obj else 0.5
    
    for _ in range(count):
        click.echo(f"{greeting}, {name}! (Strength: {strength})")
        
    # Simulate some "cost" or result data often returned by PDD commands
    return {"status": "success", "cost": 0.002 * count}

# ---------------------------------------------------------------------------
# 2. Define a streaming callback
# ---------------------------------------------------------------------------
def on_output(stream_type: str, text: str) -> None:
    """
    Callback function that receives output in real-time.
    
    Args:
        stream_type: Either "stdout" or "stderr"
        text: The chunk of text being written
    """
    color = "green" if stream_type == "stdout" else "red"
    # We print to the real stdout here, prefixed to show it's streaming
    sys.__stdout__.write(f"[{color} STREAM {stream_type}]: {text}")
    sys.__stdout__.flush()

# ---------------------------------------------------------------------------
# 3. Using ClickCommandExecutor directly
# ---------------------------------------------------------------------------
def demo_executor_class() -> None:
    """Demonstrates using the ClickCommandExecutor class directly."""
    console.print("[bold blue]--- Demo: ClickCommandExecutor Class ---[/bold blue]")
    
    # Initialize executor with global context options and a callback
    executor = ClickCommandExecutor(
        base_context_obj={
            "strength": 0.9,  # Override default strength
            "verbose": True
        },
        output_callback=on_output
    )

    # Parameters for the command
    params = {
        "name": "Developer",
        "count": 3,
        "loud": False
    }

    console.print("Executing 'greet' command...")
    
    # Execute the command
    result: CapturedOutput = executor.execute(
        command=greet_command,
        params=params
    )

    console.print("\n[bold]Execution Finished[/bold]")
    console.print(f"Exit Code: {result.exit_code}")
    console.print(f"Cost: ${result.cost:.4f}")
    console.print(f"Result Object: {result.result}")
    
    # The captured stdout is available in the result object
    console.print(f"[dim]Captured Stdout Length: {len(result.stdout)} chars[/dim]")

# ---------------------------------------------------------------------------
# 4. Using the high-level execute_pdd_command helper
# ---------------------------------------------------------------------------
def demo_high_level_helper() -> None:
    """Demonstrates using the high-level execute_pdd_command helper."""
    console.print("\n[bold blue]--- Demo: execute_pdd_command Helper ---[/bold blue]")
    
    # This helper is designed to look up PDD commands by name string.
    command_name = "generate" # A real PDD command
    
    console.print(f"Attempting to execute PDD command: '{command_name}'")
    
    # We pass arguments just like we would to the function
    args = {"prompt_file": "non_existent.prompt"}
    
    result = execute_pdd_command(
        command_name=command_name,
        args=args,
        options={"quiet": True}, # Global options
        callback=on_output
    )

    if result.exit_code != 0:
        console.print(f"[yellow]Command finished with expected error (exit code {result.exit_code})[/yellow]")
        console.print(f"Stderr: {result.stderr.strip()}")
    else:
        console.print("[green]Command success![/green]")

if __name__ == "__main__":
    demo_executor_class()
    demo_high_level_helper()