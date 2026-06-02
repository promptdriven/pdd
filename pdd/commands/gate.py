"""``pdd checkup gate`` command implementation for evidence policy checks."""
from __future__ import annotations

import json
from pathlib import Path
from typing import Optional

import click

from ..gate_main import run_gate_policy


@click.command("gate")
@click.argument("target", required=False, default=None)
@click.option(
    "--policy",
    "policy_path",
    type=click.Path(exists=True, dir_okay=False),
    default=None,
    help="Policy YAML file (default: built-in policy).",
)
@click.option(
    "--stories-dir",
    type=click.Path(exists=True, file_okay=False),
    default=None,
    help="User stories directory for contract coverage checks.",
)
@click.option(
    "--tests-dir",
    type=click.Path(exists=True, file_okay=False),
    default=None,
    help="Tests directory for contract coverage checks.",
)
@click.option("--json", "as_json", is_flag=True, default=False, help="Emit machine-readable JSON.")
def gate_cmd(
    target: Optional[str],
    policy_path: Optional[str],
    stories_dir: Optional[str],
    tests_dir: Optional[str],
    as_json: bool,
) -> None:
    """Enforce PDD evidence policies for CI (manifests, freshness, contracts).

    Reads ``.pdd/evidence/devunits/*.latest.json`` and applies policy rules for
    story/verify/test status, output freshness, and contract coverage.
    """
    project_root = Path.cwd()
    try:
        result = run_gate_policy(
            project_root,
            policy_path=Path(policy_path) if policy_path else None,
            target=target,
            stories_dir=Path(stories_dir) if stories_dir else None,
            tests_dir=Path(tests_dir) if tests_dir else None,
        )
    except FileNotFoundError as exc:
        raise click.ClickException(str(exc)) from exc

    if as_json:
        click.echo(json.dumps(result.as_dict(), indent=2))
    else:
        if result.passed:
            click.echo(
                f"PDD gate passed ({result.manifests_checked} manifest(s) checked)"
            )
        else:
            click.echo("PDD gate failed\n")
            for failure in result.failures:
                click.echo(f"- {failure.message}")
                if failure.fix_command:
                    click.echo(f"  Run: {failure.fix_command}")

    raise click.exceptions.Exit(result.exit_code)
