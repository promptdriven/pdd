"""Replay command for expanded prompt context snapshots."""
from __future__ import annotations

import json as json_module
from pathlib import Path
from typing import Optional

import click

from ..context_snapshot import replay_snapshot
from ..core.errors import handle_error


@click.command("replay")
@click.argument("run_artifact", type=click.Path(exists=True, dir_okay=False))
@click.option(
    "--output",
    type=click.Path(dir_okay=False, writable=True),
    default=None,
    help="Write the reconstructed expanded prompt to a file.",
)
@click.option(
    "--verify-only",
    is_flag=True,
    default=False,
    help="Verify the snapshot without writing or printing the expanded prompt.",
)
@click.option(
    "--print-expanded",
    is_flag=True,
    default=False,
    help="Print the reconstructed expanded prompt to stdout.",
)
@click.option(
    "--json",
    "json_output",
    is_flag=True,
    default=False,
    help="Emit machine-readable replay status.",
)
@click.pass_context
def replay(
    ctx: click.Context,
    run_artifact: str,
    output: Optional[str],
    verify_only: bool,
    print_expanded: bool,
    json_output: bool,
) -> None:
    """Reconstruct and audit expanded prompt context from a run artifact."""

    try:
        result = replay_snapshot(run_artifact)
        expanded_prompt = result.pop("expanded_prompt")

        quiet = bool((ctx.obj or {}).get("quiet", False))

        if output and not verify_only:
            Path(output).write_text(expanded_prompt, encoding="utf-8")
            result["reconstructed_output_path"] = output
        elif output and verify_only:
            result["reconstructed_output_path"] = None
            result["output_skipped"] = "verify_only"
        elif print_expanded and not verify_only and not json_output:
            click.echo(expanded_prompt)

        if json_output:
            click.echo(json_module.dumps(result, indent=2, sort_keys=True))
        elif not quiet:
            click.echo(
                "Replay verified: "
                f"{result['expanded_sha256']} "
                f"({result['snapshot_manifest_path']})"
            )
    except (click.Abort, click.UsageError, click.exceptions.Exit):
        raise
    except Exception as exc:
        if json_output:
            click.echo(
                json_module.dumps(
                    {"success": False, "error": str(exc)},
                    indent=2,
                    sort_keys=True,
                ),
                err=True,
            )
            raise click.exceptions.Exit(1) from exc
        handle_error(exc, "replay", ctx.obj.get("quiet", False))
