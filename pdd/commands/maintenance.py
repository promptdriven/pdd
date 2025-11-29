"""
Maintenance commands (sync, auto_deps, setup).
"""
import click
from typing import Optional, Tuple

from ..sync_main import sync_main
from ..auto_deps_main import auto_deps_main
from ..track_cost import track_cost
from ..core.errors import handle_error
from ..core.utils import _run_setup_utility

@click.command("sync")
@click.argument("prompt_file", required=False, type=click.Path(exists=True, dir_okay=False))
@click.option(
    "--watch",
    is_flag=True,
    default=False,
    help="Watch for file changes and sync automatically.",
)
@click.option(
    "--recursive",
    is_flag=True,
    default=False,
    help="Recursively sync all prompts in the directory.",
)
@click.pass_context
@track_cost
def sync(
    ctx: click.Context,
    prompt_file: Optional[str],
    watch: bool,
    recursive: bool,
) -> Optional[Tuple[str, float, str]]:
    """
    Synchronize prompts with code and tests.

    If PROMPT_FILE is provided, syncs that specific prompt.
    If no argument is provided, syncs all prompts in the current directory (or recursively with --recursive).
    """
    try:
        result, total_cost, model_name = sync_main(
            ctx=ctx,
            prompt_file=prompt_file,
            watch=watch,
            recursive=recursive,
        )
        return result, total_cost, model_name
    except Exception as exception:
        handle_error(exception, "sync", ctx.obj.get("quiet", False))
        return None


@click.command("auto-deps")
@click.argument("project_path", type=click.Path(exists=True, file_okay=False))
@click.option(
    "--output",
    type=click.Path(writable=True),
    default=None,
    help="Specify where to save the dependency graph (file or directory).",
)
@click.pass_context
@track_cost
def auto_deps(
    ctx: click.Context,
    project_path: str,
    output: Optional[str],
) -> Optional[Tuple[str, float, str]]:
    """Analyze project dependencies and generate a report."""
    try:
        result, total_cost, model_name = auto_deps_main(
            ctx=ctx,
            project_path=project_path,
            output=output,
        )
        return result, total_cost, model_name
    except Exception as exception:
        handle_error(exception, "auto-deps", ctx.obj.get("quiet", False))
        return None


@click.command("setup")
def setup():
    """Run the interactive setup utility."""
    try:
        _run_setup_utility()
    except Exception as e:
        handle_error(e, "setup", False)
