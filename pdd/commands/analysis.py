"""
Analysis commands (detect-change, conflicts, bug, crash, trace).
"""
import click
from typing import Optional, Tuple

from ..detect_change_main import detect_change_main
from ..conflicts_main import conflicts_main
from ..bug_main import bug_main
from ..crash_main import crash_main
from ..trace_main import trace_main
from ..track_cost import track_cost
from ..core.errors import handle_error

@click.command("detect-change")
@click.argument("code_file", type=click.Path(exists=True, dir_okay=False))
@click.pass_context
@track_cost
def detect_change(
    ctx: click.Context,
    code_file: str,
) -> Optional[Tuple[bool, float, str]]:
    """Detect if a code file has changed significantly."""
    try:
        result, total_cost, model_name = detect_change_main(
            ctx=ctx,
            code_file=code_file,
        )
        return result, total_cost, model_name
    except Exception as exception:
        handle_error(exception, "detect-change", ctx.obj.get("quiet", False))
        return None


@click.command("conflicts")
@click.argument("prompt_file", type=click.Path(exists=True, dir_okay=False))
@click.pass_context
@track_cost
def conflicts(
    ctx: click.Context,
    prompt_file: str,
) -> Optional[Tuple[str, float, str]]:
    """Check for conflicts in a prompt file."""
    try:
        result, total_cost, model_name = conflicts_main(
            ctx=ctx,
            prompt_file=prompt_file,
        )
        return result, total_cost, model_name
    except Exception as exception:
        handle_error(exception, "conflicts", ctx.obj.get("quiet", False))
        return None


@click.command("bug")
@click.argument("code_file", type=click.Path(exists=True, dir_okay=False))
@click.argument("error_log", type=click.Path(exists=True, dir_okay=False))
@click.option(
    "--output",
    type=click.Path(writable=True),
    default=None,
    help="Specify where to save the bug report (file or directory).",
)
@click.pass_context
@track_cost
def bug(
    ctx: click.Context,
    code_file: str,
    error_log: str,
    output: Optional[str],
) -> Optional[Tuple[str, float, str]]:
    """Analyze a bug given code and an error log."""
    try:
        result, total_cost, model_name = bug_main(
            ctx=ctx,
            code_file=code_file,
            error_log=error_log,
            output=output,
        )
        return result, total_cost, model_name
    except Exception as exception:
        handle_error(exception, "bug", ctx.obj.get("quiet", False))
        return None


@click.command("crash")
@click.argument("code_file", type=click.Path(exists=True, dir_okay=False))
@click.pass_context
@track_cost
def crash(
    ctx: click.Context,
    code_file: str,
) -> Optional[Tuple[str, float, str]]:
    """Analyze a crash dump or error output."""
    try:
        result, total_cost, model_name = crash_main(
            ctx=ctx,
            code_file=code_file,
        )
        return result, total_cost, model_name
    except Exception as exception:
        handle_error(exception, "crash", ctx.obj.get("quiet", False))
        return None


@click.command("trace")
@click.argument("code_file", type=click.Path(exists=True, dir_okay=False))
@click.pass_context
@track_cost
def trace(
    ctx: click.Context,
    code_file: str,
) -> Optional[Tuple[str, float, str]]:
    """Trace execution flow of a code file."""
    try:
        result, total_cost, model_name = trace_main(
            ctx=ctx,
            code_file=code_file,
        )
        return result, total_cost, model_name
    except Exception as exception:
        handle_error(exception, "trace", ctx.obj.get("quiet", False))
        return None
