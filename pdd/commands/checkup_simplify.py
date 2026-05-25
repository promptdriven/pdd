"""``pdd checkup simplify`` — conservative agentic code simplification."""
from __future__ import annotations

from pathlib import Path
from typing import Optional, Tuple

import click

from ..checkup_simplify import run_checkup_simplify
from ..track_cost import track_cost


@click.command(
    "simplify",
    context_settings={"ignore_unknown_options": True},
)
@click.argument("path", required=False, type=click.Path(exists=True))
@click.option(
    "--apply",
    is_flag=True,
    default=False,
    help="Apply safe simplifications (default is dry-run suggestions only).",
)
@click.option(
    "--dry-run",
    is_flag=True,
    default=False,
    help="Explicitly run in dry-run mode (default when --apply is omitted).",
)
@click.option(
    "--since",
    default=None,
    help="Only simplify files changed since a Git ref (e.g. HEAD~1).",
)
@click.option(
    "--staged",
    is_flag=True,
    default=False,
    help="Only simplify staged files.",
)
@click.option(
    "--max-files",
    type=int,
    default=None,
    help="Maximum number of files to process.",
)
@click.option(
    "--evidence",
    is_flag=True,
    default=False,
    help="Write a machine-readable report under .pdd/evidence/checkups/.",
)
@click.option(
    "--verify",
    is_flag=True,
    default=False,
    help="After --apply, run format/lint/typecheck/tests from config.",
)
@click.option(
    "--no-format",
    is_flag=True,
    default=False,
    help="Skip the formatter step when using --verify.",
)
@click.pass_context
@track_cost
def checkup_simplify(
    ctx: click.Context,
    path: Optional[str],
    apply: bool,
    dry_run: bool,
    since: Optional[str],
    staged: bool,
    max_files: Optional[int],
    evidence: bool,
    verify: bool,
    no_format: bool,
) -> Optional[Tuple[str, float, str]]:
    """Run a conservative simplification pass over selected source files."""
    if apply and dry_run:
        raise click.UsageError("Use either --apply or --dry-run, not both.")

    if since and staged:
        raise click.UsageError("--since and --staged are mutually exclusive.")

    mode = "apply" if apply else "dry-run"
    target_path = Path(path) if path else None
    obj = ctx.obj or {}

    try:
        result = run_checkup_simplify(
            path=target_path,
            mode=mode,
            since=since,
            staged=staged,
            max_files=max_files,
            evidence=evidence,
            verify=verify,
            no_format=no_format,
            quiet=bool(obj.get("quiet")),
            verbose=bool(obj.get("verbose")),
            reasoning_time=obj.get("time") if obj.get("time_explicit") else None,
        )
    except ValueError as exc:
        raise click.UsageError(str(exc)) from exc

    if not obj.get("quiet"):
        for line in result.summary_lines:
            click.echo(line)
        if result.provider:
            click.echo(f"\nAgent: {result.provider}  Cost: ${result.cost:.4f}")

    if result.exit_code:
        raise click.exceptions.Exit(result.exit_code)
    return None
