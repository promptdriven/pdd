"""``pdd checkup simplify`` — Claude Code ``/simplify`` integration."""
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
    help="Run Claude Code /simplify (edits files). Without this flag, only list targets.",
)
@click.option(
    "--since",
    default=None,
    help="Only include files changed since a Git ref (e.g. HEAD~1) in scope.",
)
@click.option(
    "--staged",
    is_flag=True,
    default=False,
    help="Only include staged files in scope.",
)
@click.option(
    "--max-files",
    type=int,
    default=None,
    help="Maximum number of files to process.",
)
@click.option(
    "--attempts",
    type=click.IntRange(min=1),
    default=None,
    help="Independent /simplify candidates; the passing candidate touching fewest files wins.",
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
    since: Optional[str],
    staged: bool,
    max_files: Optional[int],
    attempts: Optional[int],
    evidence: bool,
    verify: bool,
    no_format: bool,
) -> Optional[Tuple[str, float, str]]:
    """Run Claude Code bundled /simplify over selected source files."""
    if since and staged:
        raise click.UsageError("--since and --staged are mutually exclusive.")

    target_path = Path(path) if path else None
    obj = ctx.obj or {}

    try:
        result = run_checkup_simplify(
            path=target_path,
            apply=apply,
            since=since,
            staged=staged,
            max_files=max_files,
            attempts=attempts,
            evidence=evidence,
            verify=verify,
            no_format=no_format,
            quiet=bool(obj.get("quiet")),
            verbose=bool(obj.get("verbose")),
        )
    except ValueError as exc:
        raise click.UsageError(str(exc)) from exc

    if not obj.get("quiet"):
        for line in result.summary_lines:
            click.echo(line)
        if result.provider and apply:
            click.echo(f"\nAgent: {result.provider}  Cost: ${result.cost:.4f}")

    if result.exit_code:
        raise click.exceptions.Exit(result.exit_code)
