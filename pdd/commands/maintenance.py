"""
Maintenance and setup commands for the PDD CLI: ``sync``, ``auto-deps``,
``setup``, and the ``metadata`` command group.
"""
from __future__ import annotations

import warnings
from typing import Any, Dict, Optional, Tuple

import click
from rich.console import Console

from ..agentic_sync import _is_github_issue_url, run_agentic_sync, run_global_sync
from ..auto_deps_main import auto_deps_main
from ..core.errors import handle_error
from ..metadata_tags import generate_metadata_tags
from ..sync_main import sync_main
from ..track_cost import track_cost

console = Console()


# ---------------------------------------------------------------------------
# Helper dispatchers
# ---------------------------------------------------------------------------

def _run_agentic_sync_dispatch(
    ctx: click.Context,
    issue_url: str,
    budget: Optional[float],
    skip_verify: bool,
    skip_tests: bool,
    dry_run: bool,
    agentic: bool,
    no_steer: bool,
    max_attempts: Optional[int],
    timeout_adder: float,
    no_github_state: bool,
    one_session: bool = True,
    durable: bool = False,
    durable_branch: Optional[str] = None,
    no_resume: bool = False,
    durable_max_parallel: Optional[int] = None,
) -> Optional[Tuple[str, float, str]]:
    """Dispatch to ``run_agentic_sync`` and display results.

    Returns ``(message, cost, model)`` on success or ``None`` if a generic
    exception was caught. Raises ``click.exceptions.Exit(1)`` on functional
    failure.
    """
    obj = ctx.obj or {}
    quiet = bool(obj.get("quiet", False))
    verbose = bool(obj.get("verbose", False))
    try:
        success, message, cost, model = run_agentic_sync(
            issue_url=issue_url,
            verbose=verbose,
            quiet=quiet,
            budget=budget,
            skip_verify=skip_verify,
            skip_tests=skip_tests,
            dry_run=dry_run,
            agentic_mode=agentic,
            no_steer=no_steer,
            max_attempts=max_attempts,
            timeout_adder=timeout_adder,
            use_github_state=not no_github_state,
            one_session=one_session,
            durable=durable,
            durable_branch=durable_branch,
            no_resume=no_resume,
            durable_max_parallel=durable_max_parallel,
        )
    except (click.Abort, click.exceptions.Exit):
        raise
    except Exception as exc:  # noqa: BLE001
        handle_error(exc, "sync", quiet)
        return None

    if not quiet:
        console.print(f"[cyan]{message}[/cyan]")
    if not success:
        raise click.exceptions.Exit(1)
    return message, cost, model


def _run_global_sync_dispatch(
    ctx: click.Context,
    budget: Optional[float],
    skip_verify: bool,
    skip_tests: bool,
    dry_run: bool,
    agentic: bool,
    no_steer: bool,
    max_attempts: Optional[int],
    target_coverage: Optional[float],
    one_session: bool = False,
    timeout_adder: float = 0.0,
) -> Optional[Tuple[str, float, str]]:
    """Dispatch to ``run_global_sync`` for project-wide architecture sync."""
    obj = ctx.obj or {}
    quiet = bool(obj.get("quiet", False))
    verbose = bool(obj.get("verbose", False))
    local = bool(obj.get("local", False))
    try:
        success, message, cost, model = run_global_sync(
            verbose=verbose,
            quiet=quiet,
            budget=budget,
            skip_verify=skip_verify,
            skip_tests=skip_tests,
            agentic_mode=agentic,
            no_steer=no_steer,
            max_attempts=max_attempts,
            dry_run=dry_run,
            target_coverage=target_coverage,
            one_session=one_session,
            local=local,
            timeout_adder=timeout_adder,
        )
    except (click.Abort, click.exceptions.Exit):
        raise
    except Exception as exc:  # noqa: BLE001
        handle_error(exc, "sync", quiet)
        return None

    if not quiet:
        console.print(f"[cyan]{message}[/cyan]")
    if not success:
        raise click.exceptions.Exit(1)
    return message, cost, model


def _run_setup_utility() -> None:
    """Run the interactive setup utility (API keys, model config, etc.).

    Imported lazily to avoid pulling heavy/optional dependencies at module
    load time. Best-effort: if the setup utility is unavailable this is a
    no-op so the ``setup`` command can still install completions.
    """
    try:
        from ..setup_utility import run_setup_utility  # type: ignore
    except Exception:  # noqa: BLE001
        return
    try:
        run_setup_utility()
    except Exception:  # noqa: BLE001
        # Setup utility failures shouldn't crash the CLI; install_completion
        # already succeeded by this point.
        return


# ---------------------------------------------------------------------------
# sync command
# ---------------------------------------------------------------------------

@click.command(name="sync")
@click.argument("basename", required=False)
@click.option("--max-attempts", type=int, default=None, help="Maximum number of fix attempts.")
@click.option("--budget", type=float, default=None, help="Maximum total cost allowed (USD).")
@click.option("--skip-verify", is_flag=True, default=False, help="Skip functional verification.")
@click.option("--skip-tests", is_flag=True, default=False, help="Skip unit test generation/fixing.")
@click.option("--target-coverage", type=float, default=None, help="Desired code coverage percentage.")
@click.option("--dry-run", is_flag=True, default=False, help="Analyze state without executing.")
@click.option("--log", "log_flag", is_flag=True, default=False, help="Deprecated: alias for --dry-run.")
@click.option("--one-session", "one_session_flag", is_flag=True, default=False,
              help="Run example/crash/verify/test/fix in a single agentic session.")
@click.option("--no-one-session", "no_one_session_flag", is_flag=True, default=False,
              help="Disable single-session mode (default for single-module sync).")
@click.option("--no-steer", is_flag=True, default=False, help="Disable interactive steering.")
@click.option("--steer-timeout", type=float, default=8.0, help="Steering prompt timeout in seconds.")
@click.option("--agentic", is_flag=True, default=False, help="Enable agentic mode for single-module sync.")
@click.option("--timeout-adder", type=float, default=0.0, help="Extra timeout (seconds) per step for agentic sync.")
@click.option("--no-github-state", is_flag=True, default=False, help="Disable GitHub state persistence.")
@click.option("--durable", is_flag=True, default=False, help="Use durable issue sync with checkpoint commits.")
@click.option("--durable-branch", type=str, default=None, help="Override durable branch name.")
@click.option("--no-resume", is_flag=True, default=False, help="Do not resume an existing durable sync.")
@click.option("--durable-max-parallel", type=int, default=None, help="Max parallel children for durable sync.")
@click.pass_context
@track_cost
def sync(
    ctx: click.Context,
    basename: Optional[str],
    max_attempts: Optional[int],
    budget: Optional[float],
    skip_verify: bool,
    skip_tests: bool,
    target_coverage: Optional[float],
    dry_run: bool,
    log_flag: bool,
    one_session_flag: bool,
    no_one_session_flag: bool,
    no_steer: bool,
    steer_timeout: float,
    agentic: bool,
    timeout_adder: float,
    no_github_state: bool,
    durable: bool,
    durable_branch: Optional[str],
    no_resume: bool,
    durable_max_parallel: Optional[int],
) -> Optional[Tuple[Dict[str, Any], float, str]]:
    """Synchronize a prompt with its code, tests, and examples."""
    obj = ctx.obj or {}
    quiet = bool(obj.get("quiet", False))

    # Handle deprecated --log flag (alias for --dry-run).
    if log_flag:
        message = "--log is deprecated; use --dry-run instead."
        warnings.warn(message, DeprecationWarning, stacklevel=2)
        console.print(f"[yellow]Warning: {message}[/yellow]")
        dry_run = True

    # Validate durable flags.
    is_issue_url = basename is not None and _is_github_issue_url(basename)
    if durable and not is_issue_url:
        raise click.UsageError(
            "--durable requires a GitHub issue URL as the BASENAME argument."
        )
    if (durable_branch is not None or no_resume or durable_max_parallel is not None) and not durable:
        raise click.UsageError(
            "--durable-branch, --no-resume, and --durable-max-parallel require --durable."
        )

    # Resolve one_session: default True for issue URL sync, False otherwise.
    if one_session_flag:
        one_session = True
    elif no_one_session_flag:
        one_session = False
    else:
        one_session = bool(is_issue_url)

    try:
        if basename is None:
            result = _run_global_sync_dispatch(
                ctx=ctx,
                budget=budget,
                skip_verify=skip_verify,
                skip_tests=skip_tests,
                dry_run=dry_run,
                agentic=agentic,
                no_steer=no_steer,
                max_attempts=max_attempts,
                target_coverage=target_coverage,
                one_session=one_session,
                timeout_adder=timeout_adder,
            )
            if result is None:
                return None
            message, cost, model = result
            return {"global_sync": True, "message": message}, cost, model

        if is_issue_url:
            result = _run_agentic_sync_dispatch(
                ctx=ctx,
                issue_url=basename,
                budget=budget,
                skip_verify=skip_verify,
                skip_tests=skip_tests,
                dry_run=dry_run,
                agentic=agentic,
                no_steer=no_steer,
                max_attempts=max_attempts,
                timeout_adder=timeout_adder,
                no_github_state=no_github_state,
                one_session=one_session,
                durable=durable,
                durable_branch=durable_branch,
                no_resume=no_resume,
                durable_max_parallel=durable_max_parallel,
            )
            if result is None:
                return None
            message, cost, model = result
            return {"issue_url": basename, "message": message}, cost, model

        # Single-module sync.
        res, cost, model = sync_main(
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
            one_session=one_session,
        )
        if isinstance(res, dict) and res.get("overall_success") is False:
            raise click.exceptions.Exit(1)
        return res, cost, model
    except (click.Abort, click.exceptions.Exit, click.ClickException):
        raise
    except Exception as exc:  # noqa: BLE001
        handle_error(exc, "sync", quiet)
        return None


# ---------------------------------------------------------------------------
# auto-deps command
# ---------------------------------------------------------------------------

@click.command(name="auto-deps")
@click.argument("prompt_file", type=click.Path(exists=True, dir_okay=False))
@click.argument("directory_path", type=str)
@click.option("--output", type=click.Path(writable=True), default=None,
              help="Where to save the modified prompt file.")
@click.option("--csv", "csv_path", type=click.Path(writable=True), default=None,
              help="Path to the project dependencies CSV file.")
@click.option("--force-scan", is_flag=True, default=False, help="Force re-scanning all files.")
@click.option("--include-docs", is_flag=True, default=False,
              help="Include .md/.txt/.rst documentation files in dependency discovery.")
@click.option("--no-dedup", is_flag=True, default=False,
              help="Disable redundant inline content removal after inserting includes.")
@click.option("--concurrency", type=int, default=1, show_default=True,
              help="Number of parallel workers for file summarization LLM calls.")
@click.pass_context
@track_cost
def auto_deps(
    ctx: click.Context,
    prompt_file: str,
    directory_path: str,
    output: Optional[str],
    csv_path: Optional[str],
    force_scan: bool,
    include_docs: bool,
    no_dedup: bool,
    concurrency: int,
) -> Optional[Tuple[str, float, str]]:
    """Analyze and insert dependencies into a prompt file."""
    obj = ctx.obj if ctx.obj is not None else {}
    if ctx.obj is None:
        ctx.obj = obj
    quiet = bool(obj.get("quiet", False))

    # Strip surrounding quotes that may survive shell parsing in some setups.
    cleaned_directory = directory_path
    if cleaned_directory and len(cleaned_directory) >= 2 and (
        (cleaned_directory[0] == '"' and cleaned_directory[-1] == '"')
        or (cleaned_directory[0] == "'" and cleaned_directory[-1] == "'")
    ):
        cleaned_directory = cleaned_directory[1:-1]

    # Surface new options on ctx.obj for downstream code that prefers that path.
    obj["include_docs"] = include_docs
    obj["no_dedup"] = no_dedup
    obj["concurrency"] = concurrency

    try:
        result = auto_deps_main(
            ctx=ctx,
            prompt_file=prompt_file,
            directory_path=cleaned_directory,
            output=output,
            auto_deps_csv_path=csv_path,
            force_scan=force_scan,
            include_docs=include_docs,
            no_dedup=no_dedup,
            concurrency=concurrency,
        )
    except (click.Abort, click.exceptions.Exit, click.ClickException):
        raise
    except Exception as exc:  # noqa: BLE001
        handle_error(exc, "auto-deps", quiet)
        return None

    if result is None:
        return None
    if isinstance(result, tuple):
        return result  # type: ignore[return-value]
    return result, 0.0, "auto-deps"


# ---------------------------------------------------------------------------
# setup command
# ---------------------------------------------------------------------------

@click.command(name="setup")
@click.pass_context
def setup(ctx: click.Context) -> None:
    """Install shell completion and run the setup utility."""
    obj = ctx.obj or {}
    quiet = bool(obj.get("quiet", False))
    try:
        from .. import cli as cli_module
        cli_module.install_completion(quiet=quiet)
        _run_setup_utility()
    except (click.Abort, click.exceptions.Exit, click.ClickException):
        raise
    except Exception as exc:  # noqa: BLE001
        handle_error(exc, "setup", quiet)


# ---------------------------------------------------------------------------
# metadata command group
# ---------------------------------------------------------------------------

@click.group(name="metadata")
def metadata_group() -> None:
    """Generate or refresh PDD metadata tags in prompt files."""


@metadata_group.command(name="tags")
@click.argument("prompt_file", type=click.Path(exists=True, dir_okay=False))
@click.option(
    "--from",
    "source",
    type=click.Choice(["prompt-code", "architecture"]),
    default="prompt-code",
    show_default=True,
    help="Source for tag synthesis: prompt + code, or architecture.json.",
)
@click.option("--force", is_flag=True, default=False,
              help="Refresh existing tags instead of preserving them.")
@click.option("--dry-run", is_flag=True, default=False,
              help="Print a unified diff without writing.")
@click.option("--output", type=click.Path(writable=True), default=None,
              help="Write merged prompt to PATH instead of in-place.")
@click.pass_context
@track_cost
def metadata_tags(
    ctx: click.Context,
    prompt_file: str,
    source: str,
    force: bool,
    dry_run: bool,
    output: Optional[str],
) -> Optional[Tuple[Dict[str, Any], float, str]]:
    """Generate or refresh metadata tags for a prompt file."""
    obj = ctx.obj or {}
    quiet = bool(obj.get("quiet", False))
    try:
        result = generate_metadata_tags(
            prompt_file=prompt_file,
            source=source,
            force=force,
            dry_run=dry_run,
            output_path=output,
            strength=obj.get("strength"),
            temperature=obj.get("temperature"),
            verbose=obj.get("verbose"),
        )
    except (click.Abort, click.exceptions.Exit, click.ClickException):
        raise
    except Exception as exc:  # noqa: BLE001
        handle_error(exc, "metadata tags", quiet)
        return None

    # generate_metadata_tags may return (success, errors) or a richer tuple.
    if isinstance(result, tuple) and len(result) >= 2:
        success = bool(result[0])
        errors = result[1] if isinstance(result[1], (list, tuple)) else []
        cost = result[2] if len(result) > 2 else 0.0
        model = result[3] if len(result) > 3 else "metadata-tags"
    else:
        success, errors, cost, model = True, [], 0.0, "metadata-tags"

    if not success:
        for err in errors:
            console.print(f"[red]Error: {err}[/red]")
        raise click.ClickException("metadata tags generation failed")

    return {"success": True}, float(cost), str(model)


# ---------------------------------------------------------------------------
# Aliases / exports for the command registry
# ---------------------------------------------------------------------------

# ``pdd.commands.__init__`` imports these symbols by name.
sync_code = sync
metadata = metadata_group


def register(cli: click.Group) -> None:
    """Register maintenance subcommands with the given Click group."""
    cli.add_command(sync)
    cli.add_command(auto_deps)
    cli.add_command(setup)
    cli.add_command(metadata_group)
