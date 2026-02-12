"""Global quiet mode support for PDD.

When enabled, patches rich.console.Console.print, click.echo, and click.secho
to suppress non-error output across the entire codebase.

Only errors are passed through.
"""

import click
import rich.console

_quiet = False
_patched = False

# Only error messages pass through in quiet mode
_ERROR_PATTERNS = [
    "[red]Error", "[bold red]Error", "[error]",
    "[red]Insufficient", "[red]Access denied",
    "[red]Authentication failed", "[red]Invalid request",
    "Error:", "error:",
]


def _is_error(msg) -> bool:
    """Check if a message is an error that should always be shown."""
    if not msg:
        return False
    text = str(msg)
    return any(pattern in text for pattern in _ERROR_PATTERNS)


def enable_quiet_mode():
    """Enable quiet mode. Patches output functions on first call."""
    global _quiet, _patched
    _quiet = True

    if _patched:
        return
    _patched = True

    # Patch rich.console.Console.print (covers console.print and rprint)
    _original_console_print = rich.console.Console.print

    def _quiet_console_print(self, *args, **kwargs):
        if not _quiet or (args and _is_error(args[0])):
            _original_console_print(self, *args, **kwargs)

    rich.console.Console.print = _quiet_console_print

    # Patch click.echo
    _original_echo = click.echo

    def _quiet_echo(message=None, **kwargs):
        if not _quiet:
            _original_echo(message, **kwargs)
        elif _is_error(message):
            _original_echo(message, **kwargs)
        elif kwargs.get("err"):
            _original_echo(message, **kwargs)

    click.echo = _quiet_echo

    # Patch click.secho
    _original_secho = click.secho

    def _quiet_secho(message=None, **kwargs):
        if not _quiet:
            _original_secho(message, **kwargs)
        elif kwargs.get("fg") == "red" or kwargs.get("err"):
            _original_secho(message, **kwargs)
        elif _is_error(message):
            _original_secho(message, **kwargs)

    click.secho = _quiet_secho


def disable_quiet_mode():
    """Disable quiet mode. Patched wrappers will pass through normally."""
    global _quiet
    _quiet = False
