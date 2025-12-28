"""
Maintenance commands (sync, auto_deps, setup).
"""
import click
from typing import Optional, Tuple
from pathlib import Path

from ..sync_main import sync_main
from ..auto_deps_main import auto_deps_main
from ..track_cost import track_cost
from ..core.errors import handle_error
from ..core.utils import _run_setup_utility

@click.command("sync")
@click.argument("basename", required=True)
@click.option(
    "--max-attempts",
    type=int,
    default=None,
    help="Maximum number of fix attempts. Default: 3 or .pddrc value.",
)
@click.option(
    "--budget",
    type=float,
    default=None,
    help="Maximum total cost for the sync process. Default: 20.0 or .pddrc value.",
)
@click.option(
    "--skip-verify",
    is_flag=True,
    default=False,
    help="Skip the functional verification step.",
)
@click.option(
    "--skip-tests",
    is_flag=True,
    default=False,
    help="Skip unit test generation and fixing.",
)
@click.option(
    "--target-coverage",
    type=float,
    default=None,
    help="Desired code coverage percentage. Default: 90.0 or .pddrc value.",
)
@click.option(
    "--dry-run",
    is_flag=True,
    default=False,
    help="Analyze sync state without executing operations. Shows what sync would do.",
)
@click.option(
    "--log",
    is_flag=True,
    default=False,
    hidden=True,
    help="Deprecated: Use --dry-run instead.",
)
@click.pass_context
@track_cost
def sync(
    ctx: click.Context,
    basename: str,
    max_attempts: Optional[int],
    budget: Optional[float],
    skip_verify: bool,
    skip_tests: bool,
    target_coverage: Optional[float],
    dry_run: bool,
    log: bool,
) -> Optional[Tuple[str, float, str]]:
    """
    Synchronize prompts with code and tests.

    BASENAME is the base name of the prompt file (e.g., 'my_module' for 'prompts/my_module_python.prompt').
    """
    # Handle deprecated --log flag
    if log:
        click.echo(
            click.style(
                "Warning: --log is deprecated, use --dry-run instead.",
                fg="yellow"
            ),
            err=True
        )
        dry_run = True

    try:
        result, total_cost, model_name = sync_main(
            ctx=ctx,
            basename=basename,
            max_attempts=max_attempts,
            budget=budget,
            skip_verify=skip_verify,
            skip_tests=skip_tests,
            target_coverage=target_coverage,
            dry_run=dry_run,
        )
        return str(result), total_cost, model_name
    except click.Abort:
        raise
    except Exception as exception:
        handle_error(exception, "sync", ctx.obj.get("quiet", False))
        return None


@click.command("auto-deps")
@click.argument("prompt_file", type=click.Path(exists=True, dir_okay=False))
# exists=False to allow manual handling of quoted paths or paths with globs that shell didn't expand
@click.argument("directory_path", type=click.Path(exists=False, file_okay=False))
@click.option(
    "--output",
    type=click.Path(writable=True),
    default=None,
    help="Specify where to save the modified prompt (file or directory).",
)
@click.option(
    "--csv",
    type=click.Path(writable=True),
    default=None,
    help="Specify the CSV file that contains or will contain dependency information.",
)
@click.option(
    "--force-scan",
    is_flag=True,
    default=False,
    help="Force rescanning of all potential dependency files even if they exist in the CSV file.",
)
@click.pass_context
@track_cost
def auto_deps(
    ctx: click.Context,
    prompt_file: str,
    directory_path: str,
    output: Optional[str],
    csv: Optional[str],
    force_scan: bool,
) -> Optional[Tuple[str, float, str]]:
    """Analyze project dependencies and update the prompt file."""
    try:
        # Strip quotes from directory_path if present (e.g. passed incorrectly)
        if directory_path:
            directory_path = directory_path.strip('"').strip("'")

        # auto_deps_main signature: (ctx, prompt_file, directory_path, auto_deps_csv_path, output, force_scan)
        result, total_cost, model_name = auto_deps_main(
            ctx=ctx,
            prompt_file=prompt_file,
            directory_path=directory_path,
            auto_deps_csv_path=csv,
            output=output,
            force_scan=force_scan
        )
        return result, total_cost, model_name
    except click.Abort:
        raise
    except Exception as exception:
        handle_error(exception, "auto-deps", ctx.obj.get("quiet", False))
        return None


@click.command("setup")
@click.pass_context
def setup(ctx: click.Context):
    """Run the interactive setup utility."""
    try:
        # Import here to allow proper mocking
        from .. import cli as cli_module
        quiet = ctx.obj.get("quiet", False) if ctx.obj else False
        # First install completion
        cli_module.install_completion(quiet=quiet)
        # Then run setup utility
        _run_setup_utility()
    except Exception as e:
        handle_error(e, "setup", False)