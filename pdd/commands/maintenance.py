from __future__ import annotations

import os
import sys
import re
from pathlib import Path
from typing import Optional, Tuple, Any, List, Dict

import click
from rich.console import Console

from ..track_cost import track_cost
from ..sync_main import sync_main
from ..agentic_sync import (
    _is_github_issue_url,
    run_agentic_sync,
    run_global_sync,
)
from ..architecture_sync import sync_prompts_to_architecture
from ..auto_deps_main import auto_deps_main
from ..construct_paths import _find_pddrc_file, _load_pddrc_config
from ..core.errors import handle_error
from ..core.utils import _run_setup_utility

DEFAULT_SYNC_BUDGET = 20.0

console = Console()


def _resolve_global_sync_budget(budget: Optional[float]) -> float:
    """Resolve budget from CLI, .pddrc, or fallback to default."""
    if budget is not None:
        return budget
    
    try:
        pddrc_path = _find_pddrc_file(Path.cwd())
        if pddrc_path:
            config = _load_pddrc_config(pddrc_path)
            config_budget = config.get("contexts", {}).get("default", {}).get("defaults", {}).get("budget")
            if config_budget is not None:
                return float(config_budget)
    except (TypeError, ValueError):
        pass
    
    return DEFAULT_SYNC_BUDGET


def _resolve_global_sync_target_coverage(target_coverage: Optional[float]) -> Optional[float]:
    """Resolve target coverage from CLI, .pddrc, or return None."""
    if target_coverage is not None:
        return target_coverage
    
    try:
        pddrc_path = _find_pddrc_file(Path.cwd())
        if pddrc_path:
            config = _load_pddrc_config(pddrc_path)
            config_cov = config.get("contexts", {}).get("default", {}).get("defaults", {}).get("target_coverage")
            if config_cov is not None:
                return float(config_cov)
    except (TypeError, ValueError):
        pass
    
    return None


def _run_agentic_sync_dispatch(
    ctx: click.Context,
    issue_url: str,
    budget: float,
    skip_verify: bool,
    skip_tests: bool,
    dry_run: bool,
    agentic: bool,
    no_steer: bool,
    max_attempts: Optional[int],
    one_session: bool,
    timeout_adder: float,
    no_github_state: bool,
    durable: bool,
    durable_branch: Optional[str],
    no_resume: bool,
    durable_max_parallel: Optional[int],
) -> Tuple[str, float, str]:
    """Dispatch and print results for agentic issue sync."""
    quiet = ctx.obj.get("quiet", False)
    verbose = ctx.obj.get("verbose", False)
    use_github_state = not no_github_state
    
    reasoning_time = ctx.obj.get("time") if ctx.obj.get("time_explicit") else None

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
            one_session=one_session,
            timeout_adder=timeout_adder,
            use_github_state=use_github_state,
            durable=durable,
            durable_branch=durable_branch,
            no_resume=no_resume,
            durable_max_parallel=durable_max_parallel,
            reasoning_time=reasoning_time,
        )

        if not quiet:
            click.echo(f"Status: {'Success' if success else 'Failed'}")
            click.echo(f"Message: {message}")
            click.echo(f"Cost: ${cost:.4f}")
            click.echo(f"Model: {model}")

        if not success:
            raise click.exceptions.Exit(1)
        
        return message, cost, model
    except (click.Abort, click.exceptions.Exit):
        raise
    except Exception as e:
        handle_error(e, "sync", quiet)
        return "", 0.0, "local"


def _run_global_sync_dispatch(
    ctx: click.Context,
    budget: float,
    skip_verify: bool,
    skip_tests: bool,
    target_coverage: Optional[float],
    dry_run: bool,
    agentic: bool,
    no_steer: bool,
    max_attempts: Optional[int],
    one_session: bool = False,
    timeout_adder: float = 0.0,
) -> Tuple[str, float, str]:
    """Dispatch and print results for project-wide Tier 1 architecture sync."""
    quiet = ctx.obj.get("quiet", False)
    verbose = ctx.obj.get("verbose", False)
    local = ctx.obj.get("local", False)

    try:
        success, message, cost, model = run_global_sync(
            verbose=verbose,
            quiet=quiet,
            budget=budget,
            skip_verify=skip_verify,
            skip_tests=skip_tests,
            target_coverage=target_coverage,
            dry_run=dry_run,
            agentic=agentic,
            no_steer=no_steer,
            max_attempts=max_attempts,
            one_session=one_session,
            timeout_adder=timeout_adder,
            local=local,
        )

        if not quiet:
            click.echo(f"Status: {'Success' if success else 'Failed'}")
            click.echo(f"Message: {message}")
            click.echo(f"Cost: ${cost:.4f}")
            click.echo(f"Model: {model}")

        if not success:
            raise click.exceptions.Exit(1)
            
        return message, cost, model

    except (click.Abort, click.exceptions.Exit):
        raise
    except Exception as e:
        handle_error(e, "global-sync", quiet)
        return "", 0.0, "local"


@click.command("sync")
@click.argument("basename", required=False)
@click.option("--max-attempts", type=int, default=None, help="Maximum number of fix attempts. Default: 3 or .pddrc value.")
@click.option("--budget", type=float, default=None, help="Maximum total cost for the sync process. Default: 20.0 or .pddrc value.")
@click.option("--skip-verify", is_flag=True, default=False, help="Skip verification step.")
@click.option("--skip-tests", is_flag=True, default=False, help="Skip unit test generation/fixing.")
@click.option("--target-coverage", type=float, default=None, help="Desired coverage percentage. Default: 90.0 or .pddrc value.")
@click.option("--dry-run", is_flag=True, default=False, help="Analyze sync state without executing operations.")
@click.option("--log", is_flag=True, default=False, hidden=True)
@click.option("--no-steer", "no_steer", is_flag=True, default=False, help="Disable interactive steering of sync operations.")
@click.option("--steer-timeout", type=float, default=None, help="Timeout in seconds for steering prompts.")
@click.option("--agentic", is_flag=True, default=False, help="Use agentic mode for Python.")
@click.option("--timeout-adder", type=float, default=0.0, help="Additional seconds added on top of the per-module wall-clock cap.")
@click.option("--no-github-state", is_flag=True, default=False, help="Disable GitHub comment updates.")
@click.option("--one-session/--no-one-session", default=None, help="Use single LLM session context.")
@click.option("--durable", is_flag=True, default=False, help="Run each module in an isolated worktree and checkpoint to a durable branch.")
@click.option("--durable-branch", type=str, default=None, help="Override the durable checkpoint branch name.")
@click.option("--no-resume", is_flag=True, default=False, help="Ignore existing checkpoint trailers.")
@click.option("--durable-max-parallel", type=int, default=None, help="Cap concurrent module worktrees.")
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
    log: bool,
    no_steer: bool,
    steer_timeout: Optional[float],
    agentic: bool,
    timeout_adder: float,
    no_github_state: bool,
    one_session: Optional[bool],
    durable: bool,
    durable_branch: Optional[str],
    no_resume: bool,
    durable_max_parallel: Optional[int],
) -> Any:
    """Synchronize a prompt with its code, tests, and examples."""
    ctx.ensure_object(dict)

    if log:
        click.echo(click.style("Warning: --log is deprecated, use --dry-run instead.", fg="yellow"), err=True)
        dry_run = True

    resolved_budget = _resolve_global_sync_budget(budget)
    resolved_target_coverage = _resolve_global_sync_target_coverage(target_coverage)

    is_url = bool(basename and _is_github_issue_url(basename))

    # Durable option validation
    if not is_url:
        if durable or durable_branch is not None or no_resume or durable_max_parallel is not None:
            raise click.UsageError("Durable sync options require a GitHub issue URL.")
    else:
        if not durable and (durable_branch is not None or no_resume or durable_max_parallel is not None):
            raise click.UsageError("--durable-branch, --no-resume, and --durable-max-parallel require --durable.")

    if not basename:
        effective_one_session = one_session if one_session is not None else False
        return _run_global_sync_dispatch(
            ctx,
            budget=resolved_budget,
            skip_verify=skip_verify,
            skip_tests=skip_tests,
            target_coverage=resolved_target_coverage,
            dry_run=dry_run,
            agentic=agentic,
            no_steer=no_steer,
            max_attempts=max_attempts,
            one_session=effective_one_session,
            timeout_adder=timeout_adder,
        )

    elif is_url:
        effective_one_session = one_session if one_session is not None else True
        return _run_agentic_sync_dispatch(
            ctx,
            issue_url=basename,
            budget=resolved_budget,
            skip_verify=skip_verify,
            skip_tests=skip_tests,
            dry_run=dry_run,
            agentic=agentic,
            no_steer=no_steer,
            max_attempts=max_attempts,
            one_session=effective_one_session,
            timeout_adder=timeout_adder,
            no_github_state=no_github_state,
            durable=durable,
            durable_branch=durable_branch,
            no_resume=no_resume,
            durable_max_parallel=durable_max_parallel,
        )

    else:
        effective_one_session = one_session if one_session is not None else False
        try:
            return sync_main(
                ctx=ctx,
                basename=basename,
                max_attempts=max_attempts,
                budget=resolved_budget,
                skip_verify=skip_verify,
                skip_tests=skip_tests,
                target_coverage=resolved_target_coverage,
                dry_run=dry_run,
                agentic_mode=agentic,
                no_steer=no_steer,
                steer_timeout=steer_timeout,
                timeout_adder=timeout_adder,
                one_session=effective_one_session,
            )
        except (click.Abort, click.exceptions.Exit):
            raise
        except Exception as e:
            quiet = ctx.obj.get("quiet", False)
            handle_error(e, "sync", quiet)
            return None


def _echo_architecture_sync_result(result: Dict[str, Any], *, dry_run: bool) -> None:
    """Print the formatted results of the architecture sync."""
    if dry_run:
        click.echo(f"Dry run: would update {result.get('updated_count', 0)} module(s); skipped {result.get('skipped_count', 0)}.")
    else:
        click.echo(f"Updated {result.get('updated_count', 0)} module(s); skipped {result.get('skipped_count', 0)}.")

    for entry in result.get("results", []):
        if entry.get("updated"):
            click.echo(f"UPDATED {entry.get('filename')}")
        elif not entry.get("success"):
            click.echo(f"ERROR {entry.get('filename')}: {entry.get('error')}")

    if result.get("errors"):
        click.echo("Sync errors:")
        for error in result.get("errors"):
            click.echo(f"- {error}")

    validation = result.get("validation", {})
    if validation.get("errors"):
        click.echo("Validation errors:")
        for error in validation.get("errors"):
            click.echo(f"- {error.get('message')}")
    if validation.get("warnings"):
        click.echo("Validation warnings:")
        for warning in validation.get("warnings"):
            click.echo(f"- {warning.get('message')}")


@click.command("sync-architecture")
@click.argument("filenames", nargs=-1)
@click.option("--dry-run", is_flag=True, default=False, help="Analyze prompt-to-architecture sync without writing architecture.json.")
@click.pass_context
@track_cost
def sync_architecture(ctx: click.Context, filenames: Tuple[str, ...], dry_run: bool) -> Any:
    """Sync architecture.json from prompt metadata tags"""
    quiet = ctx.obj.get("quiet", False)
    try:
        result = sync_prompts_to_architecture(filenames=list(filenames) or None, dry_run=dry_run)
        
        if not quiet:
            _echo_architecture_sync_result(result, dry_run=dry_run)
            
        if not result.get("success"):
            raise click.exceptions.Exit(1)
            
        return result, 0.0, "local"
        
    except (click.Abort, click.exceptions.Exit):
        raise
    except Exception as e:
        handle_error(e, "sync-architecture", quiet)
        return None


@click.command("auto-deps")
@click.argument("prompt_file", type=click.Path(exists=True, dir_okay=False))
@click.argument("directory_path", type=click.Path(exists=False, file_okay=False))
@click.option("--output", type=str, default=None, help="Specify where to save the modified prompt file.")
@click.option("--csv", "csv_filename", type=str, default=None, help="Specify the CSV file for dependency info.")
@click.option("--force-scan", is_flag=True, default=False, help="Force rescanning of all potential dependency files.")
@click.option("--include-docs", is_flag=True, default=False, help="Include documentation files in dependency discovery.")
@click.option("--no-dedup", is_flag=True, default=False, help="Skip the redundant inline content removal pass.")
@click.option("--concurrency", type=int, default=1, help="Maximum number of parallel LLM calls for dependency analysis.")
@click.pass_context
@track_cost
def auto_deps(
    ctx: click.Context,
    prompt_file: str,
    directory_path: str,
    output: Optional[str],
    csv_filename: Optional[str],
    force_scan: bool,
    include_docs: bool,
    no_dedup: bool,
    concurrency: int,
) -> Any:
    """Analyze and insert dependencies into a prompt file"""
    ctx.ensure_object(dict)
    ctx.obj["include_docs"] = include_docs
    ctx.obj["no_dedup"] = no_dedup
    ctx.obj["concurrency"] = concurrency

    if directory_path:
        directory_path = directory_path.strip('"').strip("'")

    try:
        return auto_deps_main(
            ctx=ctx,
            prompt_file=prompt_file,
            directory_path=directory_path,
            auto_deps_csv_path=csv_filename,
            output=output,
            force_scan=force_scan,
            include_docs=include_docs,
            no_dedup=no_dedup,
            concurrency=concurrency,
        )
    except (click.Abort, click.exceptions.Exit):
        raise
    except Exception as e:
        quiet = ctx.obj.get("quiet", False)
        handle_error(e, "auto-deps", quiet)
        return None


@click.command("setup")
@click.pass_context
def setup(ctx: click.Context) -> None:
    """Install shell completion and run setup utility"""
    quiet = ctx.obj.get("quiet", False)
    try:
        from .. import cli as cli_module
        cli_module.install_completion(quiet=quiet)
        _run_setup_utility()
    except (click.Abort, click.exceptions.Exit):
        raise
    except Exception as e:
        handle_error(e, "setup", False)