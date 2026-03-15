"""
Example usage of the pdd.commands.fix module.

This script demonstrates how to invoke the `fix` command programmatically
in its different modes: Agentic E2E Fix, User Story Fix, and Manual Mode.
Since the function may rely on external dependencies like LLMs and GitHub,
this example uses mocking to simulate successful executions without real API calls.

The script:
1. Adjusts sys.path to import the module (assuming this script is in a directory relative to the project root).
2. Demonstrates each mode with mocked internal functions.
3. Prints the results for each mode.

Note: In a real scenario, remove the mocks and ensure required dependencies are installed.
"""

import sys
from pathlib import Path
from unittest.mock import patch
import click
from rich.console import Console
from typing import Tuple, Dict, Any, Optional

# Adjust sys.path to include the project root (assuming this script is in examples/ or similar)
# This allows importing pdd.commands.fix even if running this script directly.
current_dir = Path(__file__).resolve().parent
project_root = current_dir.parent.parent  # Adjust based on actual structure (e.g., if in context/, go up more)
if str(project_root) not in sys.path:
    sys.path.insert(0, str(project_root))

try:
    from pdd.commands.fix import fix
except ImportError:
    print("Error: Could not import 'pdd.commands.fix'.")
    print("Ensure your PYTHONPATH is set correctly or adjust the sys.path in this script.")
    sys.exit(1)

console = Console()

def mock_run_agentic_e2e_fix(**kwargs) -> Tuple[bool, str, float, str, list]:
    """Mock agentic fix to simulate success."""
    return True, "Agentic fix successful (mocked)", 1.23, "claude-3-5-sonnet", ["fixed_file.py"]

def mock_run_user_story_fix(**kwargs) -> Tuple[bool, str, float, str, list]:
    """Mock user story fix to simulate success."""
    return True, "User story fix successful (mocked)", 0.45, "gpt-4", ["prompt1.prompt", "prompt2.prompt"]

def mock_fix_main(**kwargs) -> Tuple[bool, str, str, int, float, str]:
    """Mock manual fix to simulate success."""
    return True, "fixed_test.py", "fixed_code.py", 2, 0.67, "gemini-pro"

def create_mock_context() -> click.Context:
    """Create a mock Click context with default options."""
    dummy_command = click.Command("fix")
    ctx = click.Context(dummy_command)
    ctx.obj = {
        "verbose": True,
        "quiet": False,
        "strength": 0.5,
        "temperature": 0.0,
        "time": 0.25,
        "force": True,
        "prompts_dir": "prompts/",  # For user story mode
    }
    return ctx

def demonstrate_agentic_mode(ctx: click.Context) -> None:
    """Demonstrate Agentic E2E Fix mode."""
    console.print("[bold blue]Demonstrating Agentic E2E Fix Mode[/bold blue]")
    args = ("https://github.com/example/repo/issues/42",)
    with patch("pdd.commands.fix.run_agentic_e2e_fix", mock_run_agentic_e2e_fix):
        result = fix(
            ctx=ctx,
            args=args,
            manual=False,
            timeout_adder=1.0,
            max_cycles=3,
            resume=True,
            force=True,
            no_github_state=False,
            output_test=None,
            output_code=None,
            output_results=None,
            loop=False,
            verification_program=None,
            max_attempts=3,
            budget=5.0,
            auto_submit=False,
            agentic_fallback=True,
            protect_tests=True,
        )
    if result:
        result_dict, cost, model = result
        console.print(f"[green]Result:[/green] {result_dict}")
        console.print(f"Cost: ${cost:.2f}, Model: {model}")

def demonstrate_user_story_mode(ctx: click.Context) -> None:
    """Demonstrate User Story Fix mode."""
    console.print("\n[bold blue]Demonstrating User Story Fix Mode[/bold blue]")
    # Simulate a story file (in real use, create an actual .md file)
    story_file = "story__example.md"
    args = (story_file,)
    with patch("pdd.commands.fix.run_user_story_fix", mock_run_user_story_fix), \
         patch("pdd.commands.fix.os.path.exists", return_value=True), \
         patch("pdd.commands.fix.os.path.basename", return_value="story__example.md"):
        result = fix(
            ctx=ctx,
            args=args,
            manual=False,
            timeout_adder=0.0,
            max_cycles=5,
            resume=True,
            force=False,
            no_github_state=True,
            output_test=None,
            output_code=None,
            output_results=None,
            loop=False,
            verification_program=None,
            max_attempts=3,
            budget=2.0,
            auto_submit=False,
            agentic_fallback=True,
            protect_tests=False,
        )
    if result:
        result_dict, cost, model = result
        console.print(f"[green]Result:[/green] {result_dict}")
        console.print(f"Cost: ${cost:.2f}, Model: {model}")

def demonstrate_manual_mode(ctx: click.Context) -> None:
    """Demonstrate Manual Mode (non-loop)."""
    console.print("\n[bold blue]Demonstrating Manual Mode (Non-Loop)[/bold blue]")
    # Simulate file paths (in real use, create actual files)
    args = ("prompt.prompt", "code.py", "test.py", "error.log")
    with patch("pdd.commands.fix.fix_main", mock_fix_main):
        result = fix(
            ctx=ctx,
            args=args,
            manual=True,
            timeout_adder=0.0,
            max_cycles=5,
            resume=True,
            force=False,
            no_github_state=False,
            output_test="fixed_test.py",
            output_code="fixed_code.py",
            output_results="results.log",
            loop=False,
            verification_program=None,
            max_attempts=3,
            budget=5.0,
            auto_submit=True,
            agentic_fallback=False,
            protect_tests=True,
        )
    if result:
        result_dict, cost, model = result
        console.print(f"[green]Result:[/green] {result_dict}")
        console.print(f"Cost: ${cost:.2f}, Model: {model}")

if __name__ == "__main__":
    ctx = create_mock_context()
    demonstrate_agentic_mode(ctx)
    demonstrate_user_story_mode(ctx)
    demonstrate_manual_mode(ctx)