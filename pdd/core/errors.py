"""
Error handling logic for PDD CLI.
"""
import os
import traceback
from typing import Any, Callable, Dict, List, Optional
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
# Brand color is the single source of truth (EPIC #1540, workstream 1). The
# shared console renders every semantic role from the central palette in
# ``pdd.cli_theme`` so the enhanced color system is the *default* across the
# whole CLI — every existing ``[command]``/``[success]``/``[error]`` markup now
# resolves to the brand palette instead of an ad-hoc per-module theme. The role
# names below are a superset of the historical ones (``info``/``warning``/
# ``error``/``success``/``path``/``command``), so existing call sites keep
# working unchanged.
from ..cli_theme import SEMANTIC_STYLES, apply_global_color_preference

custom_theme = Theme(SEMANTIC_STYLES)
console = Console(theme=custom_theme)


def _set_console_color(con: Console, enabled: bool) -> None:
    """Force or disable color on an already-constructed Rich console.

    Color is cosmetic, so any failure poking Rich internals is swallowed rather
    than allowed to break a command.
    """
    try:
        if enabled:
            con.no_color = False
            con._force_terminal = True  # render color even when piped / non-TTY
            if getattr(con, "_color_system", None) is None:
                from rich.color import ColorSystem
                truecolor = os.environ.get("COLORTERM", "").strip().lower() in (
                    "truecolor",
                    "24bit",
                )
                con._color_system = (
                    ColorSystem.TRUECOLOR if truecolor else ColorSystem.EIGHT_BIT
                )
        else:
            con.no_color = True
    except Exception:  # pragma: no cover - defensive
        pass


def apply_color_preference(preference: Optional[bool]) -> Callable[[], None]:
    """Apply the global ``--color`` / ``--no-color`` preference for this run.

    ``preference`` is ``True`` (force color even when piped), ``False`` (disable
    color everywhere), or ``None`` (auto: color on a TTY, off when piped or when
    ``NO_COLOR`` is set — the default, so omitting the flag changes nothing).

    The choice is wired two ways so it reaches every surface:

    * The ``NO_COLOR`` / ``FORCE_COLOR`` environment variables are set for
      non-Rich surfaces and subprocesses that honor the conventional flags.
    * ``pdd.cli_theme`` translates the active preference into Rich constructor
      arguments and maintains a registry of Rich consoles, so consoles created
      before and after this callback are updated consistently.

    Returns a cleanup callback that restores the pre-invocation environment and
    Rich console state. That keeps ``--color`` / ``--no-color`` scoped to a
    single CLI invocation even when tests, servers, or other callers run the CLI
    repeatedly in one Python process.
    """
    if preference is None:
        return lambda: None

    saved_env = {key: os.environ.get(key) for key in ("NO_COLOR", "FORCE_COLOR")}

    if preference:
        os.environ.pop("NO_COLOR", None)
        os.environ["FORCE_COLOR"] = "1"
    else:
        os.environ.pop("FORCE_COLOR", None)
        os.environ["NO_COLOR"] = "1"

    restore_consoles = apply_global_color_preference(preference)

    def restore() -> None:
        for key, value in saved_env.items():
            if value is None:
                os.environ.pop(key, None)
            else:
                os.environ[key] = value
        restore_consoles()

    return restore

# Buffer to collect errors for optional core dumps
_core_dump_errors: List[Dict[str, Any]] = []

def get_core_dump_errors() -> List[Dict[str, Any]]:
    """Return the list of collected errors."""
    return _core_dump_errors


def clear_core_dump_errors() -> None:
    """Clear the list of collected errors."""
    _core_dump_errors.clear()


def record_core_dump_error(
    *,
    command: str,
    type: str,
    message: str,
    details: Optional[Dict[str, Any]] = None,
    traceback_text: Optional[str] = None,
) -> None:
    """Record a structured error entry for core dumps.

    Use this for non-exception "logical failures" (budget exhaustion, retry limits,
    cycle detection, etc.) so core dumps contain actionable context even when the
    CLI run terminates without raising an exception.
    """
    error_record: Dict[str, Any] = {
        "command": command,
        "type": type,
        "message": message,
    }
    if details:
        error_record["details"] = details
    if traceback_text:
        error_record["traceback"] = traceback_text
    _core_dump_errors.append(error_record)


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
                f"  [error]File not found:[/error] {escape(str(exception))}",
                style="error",
            )
        elif isinstance(exception, (ValueError, IOError)):
            # Issue #1677: escape the message — it can contain paths with Rich-markup
            # metacharacters (e.g. a Next.js dynamic route `src/app/users/[id]/page.tsx`),
            # which would otherwise be swallowed and make the listed choices unreadable.
            console.print(
                f"  [error]Input/Output Error:[/error] {escape(str(exception))}",
                style="error",
            )
        elif isinstance(exception, click.UsageError):
            console.print(
                f"  [error]Usage Error:[/error] {exception}",
                style="error",
            )
            # click.UsageError should typically exit with 2, so we re-raise it
            raise exception
        elif isinstance(exception, click.ClickException):
            # A plain ClickException is a validated, user-facing error raised
            # deliberately by a command (e.g. "Story file not found") — report
            # it as a normal error, not an "unexpected" one.
            console.print(
                f"  [error]Error:[/error] {escape(exception.format_message())}",
                style="error",
            )
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
                f"  [error]An unexpected error occurred:[/error] {escape(str(exception))}",
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
