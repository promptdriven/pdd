from __future__ import annotations

import json
import typing as t

import click

metadata_group = click.Group(
    name="metadata",
    help="Inspect and finalize PDD dev-unit metadata."
)

@metadata_group.command(name="finalize", help="Finalize or audit metadata for a single dev unit")
@click.argument("target", required=True)
@click.option("--dry-run", is_flag=True, default=False, help="Print current metadata state without writing.")
@click.option("--json", "json_output", is_flag=True, default=False, help="Emit report as a single JSON object to stdout.")
@click.option("--language", help="Override language detection (e.g., python, typescript).")
@click.option("--context", "context_override", help="Override .pddrc context selection.")
@click.option("--quiet", is_flag=True, default=False, help="Suppress non-error output in human-readable mode.")
def finalize(
    target: str,
    dry_run: bool,
    json_output: bool,
    language: str | None,
    context_override: str | None,
    quiet: bool,
) -> None:
    """Finalize or audit metadata for a single dev unit."""
    # Lazy import to avoid loading heavy modules or internal logic unless this command is run
    try:
        from ..metadata_finalize import finalize_metadata
        import dataclasses
    except ImportError as e:
        click.echo(f"error: Could not import internal dependencies: {e}", err=True)
        raise click.exceptions.Exit(2)

    try:
        report = finalize_metadata(
            target=target,
            language=language,
            context_override=context_override,
            dry_run=dry_run,
        )
    except (click.exceptions.Exit, click.Abort):
        raise
    except ValueError as e:
        click.echo(f"error: {e}", err=True)
        raise click.exceptions.Exit(2)
    except Exception as e:
        click.echo(f"error: {e}", err=True)
        raise click.exceptions.Exit(2)

    if json_output:
        report_dict = dataclasses.asdict(report)
        click.echo(json.dumps(report_dict, indent=2, default=str))
    elif not quiet:
        click.echo(f"metadata: {report.basename} [{report.language}]")
        
        for kind, path in report.paths.items():
            is_present = report.files_present.get(kind, False)
            marker = "[present]" if is_present else "[MISSING]"
            click.echo(f"  {kind}: {path} {marker}")

        stale_str = f" ({', '.join(report.stale_components)})" if report.stale_components else ""
        click.echo(f"fingerprint: {report.fingerprint_state}{stale_str}")
        click.echo(f"run_report: {report.run_report_state}")

        if not dry_run:
            if report.wrote_fingerprint:
                click.echo("wrote fingerprint")
            if report.cleared_run_report:
                click.echo("cleared stale run report")

        for warning in report.warnings:
            click.echo(f"warning: {warning}")

    if dry_run:
        drift_detected = (
            report.fingerprint_state != "current" or
            report.run_report_state in ("stale",)
        )
        if drift_detected:
            raise click.exceptions.Exit(1)

    raise click.exceptions.Exit(0)