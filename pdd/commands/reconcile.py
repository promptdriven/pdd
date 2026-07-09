"""Continuous sync reconcile and hook commands."""
from __future__ import annotations

import json
import stat
import sys
from typing import Optional

import click

from ..continuous_sync import build_report, project_root


def _emit_report(report: dict, as_json: bool) -> None:
    if as_json:
        click.echo(json.dumps(report, indent=2, sort_keys=True))
        return
    summary = report["summary"]
    click.echo(
        f"metadata_stale={summary['metadata_stale']} "
        f"conflicts={summary['conflicts']} "
        f"unbaselined={summary['unbaselined']} "
        f"failures={summary['failures']}"
    )


@click.command("reconcile")
@click.option(
    "--json",
    "as_json",
    is_flag=True,
    default=False,
    help="Emit machine-readable JSON.",
)
@click.option(
    "--strict",
    is_flag=True,
    default=False,
    help="Exit non-zero when drift or metadata issues remain.",
)
@click.option(
    "--heal",
    is_flag=True,
    default=False,
    help="Refresh valid stale fingerprints without LLM calls.",
)
@click.option(
    "--ledger",
    is_flag=True,
    default=False,
    help="Append detected drift to .pdd/drift-ledger.jsonl.",
)
@click.option(
    "--module",
    "module_name",
    default=None,
    help="Limit reconciliation to one module basename.",
)
@click.pass_context
def reconcile(
    ctx: click.Context,
    as_json: bool,
    strict: bool,
    heal: bool,
    ledger: bool,
    module_name: Optional[str],
) -> None:
    # pylint: disable=too-many-arguments,too-many-positional-arguments
    """Classify and optionally reconcile PDD fingerprint drift."""
    ctx.ensure_object(dict)
    if as_json:
        ctx.obj["_suppress_result_summary"] = True
    report = build_report(
        consumer="reconcile",
        modules=[module_name] if module_name else None,
        heal=heal,
        ledger=ledger,
    )
    _emit_report(report, as_json)
    if strict and not report["ok"]:
        raise click.exceptions.Exit(1)


@click.command("install-hooks")
@click.option(
    "--force",
    "force_hook",
    is_flag=True,
    default=False,
    help="Overwrite an existing PDD hook.",
)
@click.pass_context
def install_hooks(ctx: click.Context, force_hook: bool) -> None:
    """Install a lightweight pre-commit drift-ledger hook."""
    ctx.ensure_object(dict)
    root = project_root()
    git_dir = root / ".git"
    if not git_dir.exists():
        raise click.ClickException("No .git directory found for hook installation.")
    hook_path = git_dir / "hooks" / "pre-commit"
    hook_path.parent.mkdir(parents=True, exist_ok=True)
    marker = "# pdd continuous-sync drift ledger"
    if hook_path.exists() and marker not in hook_path.read_text(
        encoding="utf-8",
        errors="ignore",
    ):
        if not force_hook:
            raise click.ClickException(
                f"{hook_path} already exists; rerun with --force to replace it."
            )
    script = "\n".join(
        [
            "#!/bin/sh",
            marker,
            f'"{sys.executable}" -m pdd reconcile --json --ledger >/dev/null',
            "exit 0",
            "",
        ]
    )
    hook_path.write_text(script, encoding="utf-8")
    hook_path.chmod(
        hook_path.stat().st_mode | stat.S_IXUSR | stat.S_IXGRP | stat.S_IXOTH
    )
    if not ctx.obj.get("quiet", False):
        click.echo(f"Installed {hook_path}")
