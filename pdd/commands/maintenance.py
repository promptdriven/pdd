"""
Maintenance commands (sync, auto_deps, setup).
"""
import click
from typing import Optional, Tuple
from pathlib import Path

from ..sync_main import sync_main
from ..auto_deps_main import auto_deps_main
from ..agentic_sync import _is_github_issue_url, run_agentic_sync
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
@click.option(
    "--no-steer",
    "no_steer",
    is_flag=True,
    default=False,
    help="Disable interactive steering of sync operations.",
)
@click.option(
    "--steer-timeout",
    type=float,
    default=None,
    help="Timeout in seconds for steering prompts (default: 8.0).",
)
@click.option(
    "--agentic",
    is_flag=True,
    default=False,
    help="Use agentic mode for Python (skip iterative loops, trust agent results).",
)
@click.option(
    "--timeout-adder",
    type=float,
    default=0.0,
    help="Additional timeout per step (agentic sync mode).",
)
@click.option(
    "--no-github-state",
    is_flag=True,
    default=False,
    help="Disable GitHub comment updates (agentic sync mode).",
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
    no_steer: bool,
    steer_timeout: Optional[float],
    agentic: bool,
    timeout_adder: float,
    no_github_state: bool,
) -> Optional[Tuple[str, float, str]]:
    """
    Synchronize prompts with code and tests.

    BASENAME is the base name of the prompt file (e.g., 'my_module' for 'prompts/my_module_python.prompt'),
    or a GitHub issue URL for agentic multi-module sync.
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

    # Detect GitHub issue URL -> dispatch to agentic sync
    if _is_github_issue_url(basename):
        return _run_agentic_sync_dispatch(
            ctx=ctx,
            issue_url=basename,
            budget=budget,
            skip_verify=skip_verify,
            skip_tests=skip_tests,
            agentic=agentic,
            no_steer=no_steer,
            max_attempts=max_attempts,
            timeout_adder=timeout_adder,
            no_github_state=no_github_state,
        )

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
            no_steer=no_steer,
            steer_timeout=steer_timeout,
            agentic_mode=agentic,
        )
        return str(result), total_cost, model_name
    except click.Abort:
        raise
    except Exception as exception:
        handle_error(exception, "sync", ctx.obj.get("quiet", False))
        return None


def _run_agentic_sync_dispatch(
    ctx: click.Context,
    issue_url: str,
    budget: Optional[float],
    skip_verify: bool,
    skip_tests: bool,
    agentic: bool,
    no_steer: bool,
    max_attempts: Optional[int],
    timeout_adder: float,
    no_github_state: bool,
) -> Optional[Tuple[str, float, str]]:
    """Dispatch to agentic sync runner for GitHub issue URLs."""
    ctx.ensure_object(dict)
    quiet = ctx.obj.get("quiet", False)
    verbose = ctx.obj.get("verbose", False)

    try:
        success, message, cost, model = run_agentic_sync(
            issue_url=issue_url,
            verbose=verbose,
            quiet=quiet,
            budget=budget,
            skip_verify=skip_verify,
            skip_tests=skip_tests,
            agentic_mode=agentic,
            no_steer=no_steer,
            max_attempts=max_attempts,
            timeout_adder=timeout_adder,
            use_github_state=not no_github_state,
        )

        if not quiet:
            status = "Success" if success else "Failed"
            click.echo(f"Status: {status}")
            click.echo(f"Message: {message}")
            click.echo(f"Cost: ${cost:.4f}")
            click.echo(f"Model: {model}")

        if not success:
            raise click.exceptions.Exit(1)

        return message, cost, model

    except (click.Abort, click.exceptions.Exit):
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