"""``pdd checkup drift`` subcommand implementation."""

from __future__ import annotations

import json
from pathlib import Path
from typing import Optional

import click

from ..drift_main import DEFAULT_MAX_COST_USD, DriftInputError, run_drift


@click.command("drift")
@click.argument("devunit")
@click.option(
    "--runs",
    default=1,
    show_default=True,
    type=int,
    help="Number of regeneration runs.",
)
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
@click.option(
    "--json", "as_json", is_flag=True, default=False, help="Emit machine-readable JSON."
)
@click.option(
    "--max-cost",
    "max_cost_usd",
    type=float,
    default=None,
    help=(
        f"Maximum USD budget for regeneration and behavioral checks "
        f"(default ${DEFAULT_MAX_COST_USD:.0f} for non-dry-run runs)."
    ),
)
def drift_cmd(
    devunit: str,
    runs: int,
    model: Optional[str],
    from_evidence: Optional[str],
    code_file: Optional[str],
    dry_run: bool,
    as_json: bool,
    max_cost_usd: Optional[float],
) -> None:
    """Check regeneration stability for a PDD dev unit.

    Re-generates code into isolated temp paths (unless ``--dry-run``),
    compares each candidate against the baseline artifact, and runs
    configured behavioral checks. Policy runs only when a policy file or
    explicit policy/gate validation is configured (ordinary evidence alone
    does not enable it).
    """
    if runs < 1:
        raise click.UsageError("--runs must be at least 1")

    project_root = Path.cwd()
    effective_max_cost = max_cost_usd
    if effective_max_cost is None and not dry_run:
        effective_max_cost = DEFAULT_MAX_COST_USD
    try:
        report = run_drift(
            devunit,
            project_root,
            runs=runs,
            model=model,
            from_evidence=Path(from_evidence) if from_evidence else None,
            code_file=Path(code_file) if code_file else None,
            dry_run=dry_run,
            max_cost_usd=effective_max_cost,
        )
    except DriftInputError as exc:
        if as_json:
            click.echo(
                json.dumps(
                    {
                        "status": "error",
                        "error": {"code": exc.code, "message": str(exc)},
                    },
                    indent=2,
                )
            )
            raise click.exceptions.Exit(1) from exc
        raise click.ClickException(str(exc)) from exc
    except (FileNotFoundError, RuntimeError) as exc:
        if as_json:
            click.echo(
                json.dumps(
                    {
                        "status": "error",
                        "error": {
                            "code": "drift_runtime_error",
                            "message": str(exc),
                        },
                    },
                    indent=2,
                )
            )
            raise click.exceptions.Exit(1) from exc
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
        if payload.get("policy_check_unavailable"):
            click.echo(
                "Policy note: gate command unavailable; policy check failed closed."
            )
        if payload.get("max_cost_usd") is not None:
            click.echo(f"Max cost: ${payload['max_cost_usd']:.4f}")
        click.echo(f"Total cost: ${payload['total_cost_usd']:.4f}")
        click.echo("\nOutput drift:")
        api_status = "unchanged" if report.public_api_unchanged else "changed"
        impl_status = "changed" if report.implementation_changed else "unchanged"
        behavior_status = "unchanged" if report.behavior_unchanged else "changed"
        click.echo(f"- public API: {api_status}")
        click.echo(f"- implementation structure: {impl_status}")
        click.echo(f"- behavior: {behavior_status}")
        click.echo(f"\nStatus: {report.status}")

    raise click.exceptions.Exit(report.exit_code)
