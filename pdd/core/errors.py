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

try:
    from pdd.agentic_common import get_and_clear_agentic_interrupt_context
except ImportError:
    # Fallback for environments (e.g. certain tests) where agentic_common is unavailable.
    def get_and_clear_agentic_interrupt_context():  # type: ignore[override]
        return None

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


def _format_interrupt_reason(ctx: Dict[str, Any]) -> str:
    """Build a human-readable reason from agentic interrupt context."""
    step = ctx.get("current_step")
    total = ctx.get("total_steps")
    step_name = ctx.get("step_name", "")
    completed = ctx.get("completed_steps") or []
    workflow = ctx.get("workflow", "")

    parts: List[str] = []
    if step is not None and total is not None:
        parts.append(f"Interrupted at step {step}/{total}")
        if step_name:
            parts.append(f" ({step_name})")
        parts.append(".")
    if completed:
        parts.append(f" Completed steps: {', '.join(str(s) for s in completed)}.")
    if workflow and not parts:
        parts.append(f"Workflow: {workflow}.")

    return "".join(parts) if parts else "Interrupted by user (Ctrl+C)."


def handle_error(exception: Exception, command_name: str, quiet: bool):
    """Prints error messages using Rich console and records core-dump metadata."""
    # Build error record for potential core dump
    error_record: Dict[str, Any] = {
        "command": command_name,
        "type": type(exception).__name__,
        "message": str(exception),
        "traceback": "".join(
            traceback.format_exception(type(exception), exception, exception.__traceback__)
        ),
    }

    # For KeyboardInterrupt, enrich with agentic progress context if available
    if isinstance(exception, KeyboardInterrupt):
        interrupt_ctx = get_and_clear_agentic_interrupt_context()
        if interrupt_ctx:
            error_record["reason"] = _format_interrupt_reason(interrupt_ctx)

    _core_dump_errors.append(error_record)

    if not quiet:
        if isinstance(exception, KeyboardInterrupt):
            console.print(
                f"[warning]You pressed Ctrl+C in your terminal. Interrupted during '{command_name}' command.[/warning]",
                style="warning",
            )
        else:
            console.print(
                f"[error]Error during '{command_name}' command:[/error]",
                style="error",
            )

        if isinstance(exception, FileNotFoundError):
            console.print(
                f"  [error]File not found:[/error] {exception}",
                style="error",
            )
        elif isinstance(exception, (ValueError, IOError)):
            console.print(
                f"  [error]Input/Output Error:[/error] {exception}",
                style="error",
            )
        elif isinstance(exception, click.UsageError):
            console.print(
                f"  [error]Usage Error:[/error] {exception}",
                style="error",
            )
            # click.UsageError should typically exit with 2, so we re-raise it
            raise exception
        elif isinstance(exception, MarkupError):
            console.print(
                "  [error]Markup Error:[/error] Invalid Rich markup encountered.",
                style="error",
            )
            # Print the error message safely escaped
            console.print(escape(str(exception)))
        elif isinstance(exception, KeyboardInterrupt):
            reason = error_record.get("reason")
            if reason:
                console.print(f"  [warning]{reason}[/warning]", style="warning")
            else:
                console.print(
                    "  [warning]Interrupted by user (Ctrl+C).[/warning]",
                    style="warning",
                )
            console.print(
                "  [dim]Re-run the same command to start fresh.[/dim]"
            )
        else:
            console.print(
                f"  [error]An unexpected error occurred:[/error] {exception}",
                style="error",
            )

    strict_exit = os.environ.get("PDD_STRICT_EXIT", "").strip().lower() in {
        "1",
        "true",
        "yes",
        "on",
    }
    if strict_exit:
        raise SystemExit(1)
    # Do NOT re-raise e here. Let the command function return None.
