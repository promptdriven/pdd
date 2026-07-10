"""Continuous sync reconcile and hook commands."""
from __future__ import annotations

import json
import stat
import subprocess
import sys
from pathlib import Path
from typing import Optional

import click

from ..continuous_sync import (
    CheckResult,
    build_report,
    project_root,
    resolve_units,
    run_check,
)


def _pre_commit_hook_path(root: Path) -> Path:
    """Resolve the Git-managed pre-commit hook path for ``root``."""
    commands = (
        ["git", "rev-parse", "--path-format=absolute", "--git-path", "hooks/pre-commit"],
        ["git", "rev-parse", "--git-path", "hooks/pre-commit"],
    )
    last_error = ""
    for command in commands:
        result = subprocess.run(
            command,
            cwd=str(root),
            capture_output=True,
            text=True,
            check=False,
        )
        if result.returncode != 0:
            last_error = (result.stderr or "").strip()
            continue
        raw_path = (result.stdout or "").strip()
        if not raw_path:
            continue
        hook_path = Path(raw_path)
        if not hook_path.is_absolute():
            hook_path = root / hook_path
        return hook_path
    message = "Not inside a Git worktree."
    if last_error:
        message = last_error
    raise click.ClickException(f"Unable to resolve Git hook path: {message}")


def _emit_report(report: dict, as_json: bool) -> None:
    if as_json:
        click.echo(json.dumps(report, indent=2, sort_keys=True))
        return
    summary = report["summary"]
    parts = [
        f"metadata_stale={summary['metadata_stale']}",
        f"conflicts={summary['conflicts']}",
        f"unbaselined={summary['unbaselined']}",
        f"failures={summary['failures']}",
    ]
    if report.get("stamped"):
        parts.append(f"stamped={len(report['stamped'])}")
    click.echo(" ".join(parts))


def _emit_check(result: CheckResult, as_json: bool) -> None:
    """Render a ``--check`` verification result (parity with the CI stamper)."""
    if as_json:
        payload = {
            "ok": result.ok,
            "stampable": result.stampable,
            "ignored": result.ignored,
            "waived": result.waived,
            "missing": result.missing,
            "stale": [{"basename": b, "fields": f} for b, f in result.stale],
            "no_code": result.no_code,
        }
        click.echo(json.dumps(payload, indent=2, sort_keys=True))
        return
    click.echo(
        f"checked {result.stampable} stampable units; "
        f"ignored={result.ignored} waived={result.waived}"
    )
    for name in result.no_code:
        click.echo(f"  no code file (add a waiver): {name}", err=True)
    for name in result.missing:
        click.echo(f"  missing fingerprint: {name}", err=True)
    for name, fields in result.stale:
        click.echo(f"  stale: {name}: {', '.join(fields)}", err=True)
    if result.ok:
        click.echo("all fingerprints current")


@click.command("reconcile")
@click.argument("basename", required=False)
@click.option(
    "--json",
    "as_json",
    is_flag=True,
    default=False,
    help="Emit machine-readable JSON.",
)
@click.option(
    "--check",
    is_flag=True,
    default=False,
    help="Verify fingerprints are current; exit non-zero on drift (no writes).",
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
    help="Stamp single-sided drift to the current tree (no LLM, no regen).",
)
@click.option(
    "--accept-current",
    "accept_current",
    is_flag=True,
    default=False,
    help="Stamp CONFLICT units, accepting the current tree as the agreed baseline.",
)
@click.option(
    "--backfill",
    is_flag=True,
    default=False,
    help="Stamp UNBASELINED units (missing/invalid fingerprint) to set a baseline.",
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
    help="Alias for the BASENAME argument (limit to one unit).",
)
@click.pass_context
def reconcile(
    ctx: click.Context,
    basename: Optional[str],
    as_json: bool,
    check: bool,
    strict: bool,
    heal: bool,
    accept_current: bool,
    backfill: bool,
    ledger: bool,
    module_name: Optional[str],
) -> None:
    # pylint: disable=too-many-arguments,too-many-positional-arguments
    """Classify PDD fingerprint drift and stamp the safe cases (no LLM).

    With no flags, reports each unit's status without writing. ``--heal`` stamps
    single-sided drift; ``--accept-current`` additionally stamps CONFLICT units;
    ``--backfill`` additionally stamps UNBASELINED units. ``--check`` is a
    read-only verification (same contract as the CI stamper) that exits non-zero
    on any non-current unit. BASENAME (or ``--module``) limits the run to one unit.
    """
    ctx.ensure_object(dict)
    if as_json:
        ctx.obj["_suppress_result_summary"] = True
    target = basename or module_name
    modules = [target] if target else None

    # A targeted run that matches no unit must fail loudly, not silently pass with
    # 0 units (#1969 review pass 2 finding 3: a typo'd basename would otherwise
    # exit 0 / ok:true and skip the intended unit in CI/runbook checks).
    if target is not None and not resolve_units(project_root(), modules=modules):
        raise click.ClickException(
            f"No PDD unit matches '{target}'. Run `pdd reconcile` (no argument) to "
            "verify all units, or check the basename / --module spelling."
        )

    if check:
        result = run_check(modules=modules)
        _emit_check(result, as_json)
        if not result.ok:
            raise click.exceptions.Exit(1)
        return

    report = build_report(
        consumer="reconcile",
        modules=modules,
        heal=heal,
        ledger=ledger,
        accept_current=accept_current,
        backfill=backfill,
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
    hook_path = _pre_commit_hook_path(root)
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
