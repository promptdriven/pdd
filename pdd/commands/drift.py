"""``pdd checkup drift`` subcommand implementation."""
from __future__ import annotations

import json
from pathlib import Path
from typing import Optional

import click

from ..drift_main import run_drift


@click.command("drift")
@click.argument("devunit")
@click.option("--runs", default=1, show_default=True, type=int, help="Number of regeneration runs.")
@click.option("--model", default=None, help="Model override for regeneration runs.")
@click.option(
    "--from-evidence",
    type=click.Path(exists=True, dir_okay=False),
    default=None,
    help="Evidence manifest path (default: .pdd/evidence/devunits/<devunit>.latest.json).",
)
@click.option(
    "--code-file",
    type=click.Path(exists=True, dir_okay=False),
    default=None,
    help="Explicit generated code file path.",
)
@click.option(
    "--dry-run",
    is_flag=True,
    default=False,
    help="Do not regenerate; compare current artifact stability only.",
)
@click.option("--json", "as_json", is_flag=True, default=False, help="Emit machine-readable JSON.")
def drift_cmd(
    devunit: str,
    runs: int,
    model: Optional[str],
    from_evidence: Optional[str],
    code_file: Optional[str],
    dry_run: bool,
    as_json: bool,
) -> None:
    """Check regeneration stability for a PDD dev unit.

    Re-generates code (unless ``--dry-run``), compares public API and hashes,
    and runs local tests when available.
    """
    if runs < 1:
        raise click.UsageError("--runs must be at least 1")

    project_root = Path.cwd()
    try:
        report = run_drift(
            devunit,
            project_root,
            runs=runs,
            model=model,
            from_evidence=Path(from_evidence) if from_evidence else None,
            code_file=Path(code_file) if code_file else None,
            dry_run=dry_run,
        )
    except (FileNotFoundError, RuntimeError) as exc:
        raise click.ClickException(str(exc)) from exc

    if as_json:
        click.echo(json.dumps(report.as_dict(), indent=2))
    else:
        click.echo(f"PDD Drift Report: {report.devunit}\n")
        payload = report.as_dict()
        click.echo(f"Runs: {payload['runs']}")
        click.echo(f"Tests: {payload['tests']}")
        click.echo(f"Stories: {payload['stories']}")
        click.echo(f"Verify: {payload['verify']}")
        click.echo(f"Policy: {payload['policy']}")
        click.echo("\nOutput drift:")
        api_status = "unchanged" if report.public_api_unchanged else "changed"
        impl_status = "changed" if report.implementation_changed else "unchanged"
        behavior_status = "unchanged" if report.behavior_unchanged else "changed"
        click.echo(f"- public API: {api_status}")
        click.echo(f"- implementation structure: {impl_status}")
        click.echo(f"- behavior: {behavior_status}")
        click.echo(f"\nStatus: {report.status}")

    raise click.exceptions.Exit(report.exit_code)
