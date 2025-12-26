"""
Error handling logic for PDD CLI.
"""
import os
import traceback
from typing import Any, Dict, List
import click
from rich.console import Console
from rich.markup import MarkupError, escape
from rich.theme import Theme

# --- Initialize Rich Console ---
# Define a custom theme for consistent styling
custom_theme = Theme({
    "info": "cyan",
    "warning": "yellow",
    "error": "bold red",
    "success": "green",
    "path": "dim blue",
    "command": "bold magenta",
})
console = Console(theme=custom_theme)

# Buffer to collect errors for optional core dumps
_core_dump_errors: List[Dict[str, Any]] = []

def get_core_dump_errors() -> List[Dict[str, Any]]:
    """Return the list of collected errors."""
    return _core_dump_errors

def clear_core_dump_errors() -> None:
    """Clear the list of collected errors."""
    _core_dump_errors.clear()

def handle_error(exception: Exception, command_name: str, quiet: bool):
    """Prints error messages using Rich console."""
    # Record error details for potential core dump
    _core_dump_errors.append(
        {
            "command": command_name,
            "type": type(exception).__name__,
            "message": str(exception),
            "traceback": "".join(
                traceback.format_exception(type(exception), exception, exception.__traceback__)
            ),
        }
    )

    if not quiet:
        console.print(f"[error]Error during '{command_name}' command:[/error]", style="error")
        if isinstance(exception, FileNotFoundError):
            console.print(f"  [error]File not found:[/error] {exception}", style="error")
        elif isinstance(exception, (ValueError, IOError)):
            console.print(f"  [error]Input/Output Error:[/error] {exception}", style="error")
        elif isinstance(exception, click.UsageError): # Handle Click usage errors explicitly if needed
             console.print(f"  [error]Usage Error:[/error] {exception}", style="error")
             # click.UsageError should typically exit with 2, but we are handling it.
        elif isinstance(exception, MarkupError):
            console.print("  [error]Markup Error:[/error] Invalid Rich markup encountered.", style="error")
            # Print the error message safely escaped
            console.print(escape(str(exception)))
        else:
            console.print(f"  [error]An unexpected error occurred:[/error] {exception}", style="error")
    strict_exit = os.environ.get("PDD_STRICT_EXIT", "").strip().lower() in {"1", "true", "yes", "on"}
    if strict_exit:
        raise SystemExit(1)
    # Do NOT re-raise e here. Let the command function return None.
