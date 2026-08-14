"""``pdd-k8s`` command line interface."""

from __future__ import annotations

import json
from pathlib import Path

import click

from . import doctor as doctor_module
from . import manifests, orchestrator
from .config import (
    CONFIG_RELATIVE_PATH,
    ConfigError,
    DeploymentConfig,
    config_path,
    load_config,
)

STARTER_MANIFEST = """\
# PDD local service deployments.
#
# Dev Units are implementation units, not pods. A service names the Dev Units
# whose generated code ships together in one container image. PDD never writes
# a Dockerfile for you: point each service at one you maintain.
version: 1

cluster:
  name: pdd-local
  namespace: pdd-local

services:
  api:
    dev_units: [router]
    dockerfile: deploy/Dockerfile
    context: .
    port: 8000
    replicas: 1
    health:
      path: /health
"""

_STATE_COLORS = {
    "running": "green",
    "failed": "red",
    "pending": "yellow",
    "not deployed": "white",
}
_CHECK_MARKS = {
    doctor_module.OK: ("✔", "green"),
    doctor_module.WARN: ("!", "yellow"),
    doctor_module.FAIL: ("✘", "red"),
}


def _resolve_config(project_root: Path) -> DeploymentConfig:
    try:
        return load_config(project_root)
    except ConfigError as error:
        raise click.ClickException(str(error)) from error


def _report(message: str) -> None:
    click.secho(f"  {message}", fg="cyan")


@click.group(context_settings={"help_option_names": ["-h", "--help"]})
@click.option(
    "--project-root",
    type=click.Path(file_okay=False, exists=True, path_type=Path),
    default=Path.cwd,
    help="Project directory containing .pdd/ (defaults to the current directory).",
)
@click.pass_context
def cli(ctx: click.Context, project_root: Path) -> None:
    """Run selected PDD services on a local Kubernetes cluster.

    This is an opt-in companion to PDD. Projects without
    .pdd/deployments.yaml are unaffected.
    """
    ctx.ensure_object(dict)
    ctx.obj["project_root"] = project_root.resolve()


@cli.command()
@click.option("--force", is_flag=True, help="Overwrite an existing manifest.")
@click.pass_context
def init(ctx: click.Context, force: bool) -> None:
    """Create a starter .pdd/deployments.yaml."""
    root: Path = ctx.obj["project_root"]
    path = config_path(root)
    if path.exists() and not force:
        raise click.ClickException(f"{path} already exists. Use --force to overwrite it.")

    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(STARTER_MANIFEST, encoding="utf-8")
    click.secho(f"Created {CONFIG_RELATIVE_PATH}", fg="green")

    discovered = sorted(doctor_module.discover_dev_units(root))
    if discovered:
        click.echo(f"Dev Units found in this project: {', '.join(discovered)}")
    click.echo("Edit the manifest to map your Dev Units onto services, then run 'pdd-k8s doctor'.")


@cli.command()
@click.option("--json", "as_json", is_flag=True, help="Emit machine-readable output.")
@click.pass_context
def doctor(ctx: click.Context, as_json: bool) -> None:
    """Check Docker, kind, kubectl, the manifest and each service."""
    root: Path = ctx.obj["project_root"]
    try:
        config: DeploymentConfig | None = load_config(root)
    except ConfigError:
        config = None

    checks = doctor_module.run_doctor(root, config)
    if as_json:
        click.echo(json.dumps({"checks": [check.as_dict() for check in checks]}, indent=2))
    else:
        for check in checks:
            mark, color = _CHECK_MARKS[check.status]
            click.secho(f"{mark} {check.name}: {check.detail}", fg=color)
            if check.remedy:
                click.secho(f"    → {check.remedy}", fg="white")

    blocking = doctor_module.blocking(checks)
    if blocking:
        raise SystemExit(1)
    if not as_json:
        click.secho("\nReady to deploy.", fg="green")


@cli.command()
@click.pass_context
def services(ctx: click.Context) -> None:
    """List the services defined in the manifest and their Dev Units."""
    config = _resolve_config(ctx.obj["project_root"])
    click.secho(f"Cluster: {config.cluster.name} (namespace {config.cluster.namespace})\n", fg="white")
    for service in config.select([]):
        click.secho(service.name, fg="cyan", bold=True)
        click.echo(f"  dev units : {', '.join(service.dev_units)}")
        click.echo(f"  image     : {service.image}")
        click.echo(f"  dockerfile: {service.dockerfile}")
        click.echo(f"  port      : {service.port}  health: {service.health.path}")


@cli.command()
@click.argument("service_names", metavar="[SERVICE]...", nargs=-1)
@click.option("--skip-doctor", is_flag=True, help="Deploy without running preflight checks.")
@click.pass_context
def up(ctx: click.Context, service_names: tuple[str, ...], skip_doctor: bool) -> None:
    """Build, load and deploy services (all services when none named)."""
    root: Path = ctx.obj["project_root"]
    config = _resolve_config(root)

    if not skip_doctor:
        blocking = doctor_module.blocking(doctor_module.run_doctor(root, config))
        # A missing cluster is only a warning; doctor's failures are real blockers.
        if blocking:
            for check in blocking:
                click.secho(f"✘ {check.name}: {check.detail}", fg="red")
                if check.remedy:
                    click.secho(f"    → {check.remedy}", fg="white")
            raise click.ClickException("Preflight checks failed. Fix the above or pass --skip-doctor.")

    try:
        selected = config.select(list(service_names))
    except ConfigError as error:
        raise click.ClickException(str(error)) from error

    outcomes = orchestrator.up(config, selected, report=_report)
    failed = False
    for outcome in outcomes:
        if outcome.ok:
            click.secho(f"✔ {outcome.service} is ready", fg="green")
        else:
            failed = True
            click.secho(f"✘ {outcome.service} failed — {outcome.failure()}", fg="red")
    if failed:
        raise SystemExit(1)


@cli.command()
@click.option("--json", "as_json", is_flag=True, help="Emit machine-readable output.")
@click.pass_context
def status(ctx: click.Context, as_json: bool) -> None:
    """Show deploy state, pod readiness and restarts for every service."""
    config = _resolve_config(ctx.obj["project_root"])
    payload = orchestrator.status(config, config.select([]))

    if as_json:
        click.echo(json.dumps(payload, indent=2))
        return

    if not payload["available"]:
        click.secho(payload["message"] or "Local cluster is unavailable.", fg="yellow")
        return

    click.secho(f"Cluster {payload['cluster']} · namespace {payload['namespace']}\n", fg="white")
    for service in payload["services"]:
        color = _STATE_COLORS.get(service["state"], "white")
        click.secho(
            f"{service['name']:<16} {service['state']:<12}"
            f" {service['ready_replicas']}/{service['desired_replicas']} ready"
            f"  {service['restarts']} restarts",
            fg=color,
        )
        click.echo(f"  dev units: {', '.join(service['dev_units'])}")
        for pod in service["pods"]:
            click.echo(f"  · {pod['name']}  {pod['phase']}  health={pod['health']}  node={pod['node']}")
        for event in service["events"]:
            click.secho(f"  ! {event}", fg="yellow")


@cli.command()
@click.argument("service_name")
@click.option("--tail", default=200, show_default=True, help="Number of lines to show.")
@click.pass_context
def logs(ctx: click.Context, service_name: str, tail: int) -> None:
    """Tail aggregated logs for one service."""
    config = _resolve_config(ctx.obj["project_root"])
    try:
        service = config.select([service_name])[0]
    except ConfigError as error:
        raise click.ClickException(str(error)) from error

    text, failure = orchestrator.logs(config, service, tail=tail)
    if failure:
        raise click.ClickException(failure)
    click.echo(text.rstrip() or f"No logs yet for '{service_name}'.")


@cli.command()
@click.argument("service_names", metavar="[SERVICE]...", nargs=-1)
@click.option(
    "--cluster",
    "remove_cluster",
    is_flag=True,
    help="Also delete the local kind cluster.",
)
@click.pass_context
def down(ctx: click.Context, service_names: tuple[str, ...], remove_cluster: bool) -> None:
    """Remove services from the local cluster."""
    config = _resolve_config(ctx.obj["project_root"])
    try:
        selected = config.select(list(service_names))
    except ConfigError as error:
        raise click.ClickException(str(error)) from error

    for outcome in orchestrator.down(config, selected, report=_report):
        color = "green" if outcome.ok else "red"
        click.secho(f"{'✔' if outcome.ok else '✘'} {outcome.service}: {outcome.steps[0].detail}", fg=color)

    if remove_cluster:
        if service_names:
            raise click.ClickException("--cluster removes everything; do not also name services.")
        step = orchestrator.delete_cluster(config, report=_report)
        click.secho(step.detail, fg="green" if step.ok else "red")


@cli.command()
@click.argument("service_names", metavar="[SERVICE]...", nargs=-1)
@click.pass_context
def manifest(ctx: click.Context, service_names: tuple[str, ...]) -> None:
    """Print the generated Kubernetes manifests without applying them."""
    config = _resolve_config(ctx.obj["project_root"])
    try:
        selected = config.select(list(service_names))
    except ConfigError as error:
        raise click.ClickException(str(error)) from error
    click.echo(manifests.render(selected, config.cluster))


def main() -> None:
    cli(obj={})


if __name__ == "__main__":
    main()
