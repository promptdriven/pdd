"""Policy commands for snapshot and reproducibility enforcement."""
from __future__ import annotations

import json
import sys
from pathlib import Path
from typing import Optional

import click

from ..context_snapshot_policy import check_snapshot_policy


@click.group(name="policy")
def policy_group() -> None:
    """Policy checks for reproducibility and side effects."""


@policy_group.command(name="snapshot")
@click.argument("prompt_file", type=click.Path(exists=True, dir_okay=False, path_type=Path))
@click.option(
    "--project-root",
    type=click.Path(exists=True, file_okay=False, path_type=Path),
    default=".",
    show_default=True,
    help="Project root containing .pdd/evidence.",
)
@click.option("--json", "as_json", is_flag=True, help="Emit machine-readable results.")
def snapshot(prompt_file: Path, project_root: Path, as_json: bool) -> None:
    """Reject prompts with nondeterministic tags that lack a replayable snapshot."""

    passed, message = check_snapshot_policy(prompt_file, project_root)
    payload = {
        "passed": passed,
        "prompt": str(prompt_file),
        "message": message,
    }
    if as_json:
        click.echo(json.dumps(payload, indent=2, sort_keys=True))
    elif passed:
        click.secho(f"PASS: {message}", fg="green")
    else:
        click.secho(f"FAIL: {message}", fg="red")

    if not passed:
        sys.exit(1)
