"""Waiver policy gate for ``pdd checkup gate``."""
from __future__ import annotations

import json
from pathlib import Path
from typing import Any

import click
import yaml

from ..contract_ir import parse_prompt_contracts
from ..waiver_policy import summarize_waivers


def _discover_prompts(target: Path) -> list[Path]:
    if target.is_file():
        return [target] if target.suffix == ".prompt" else []
    return sorted(
        p for p in target.rglob("*.prompt")
        if not p.name.lower().endswith("_llm.prompt")
    )


def _load_gate_policy(policy_file: Path, *, explicit: bool) -> dict[str, bool]:
    defaults = {
        "allow_waivers": True,
        "forbid_waivers": False,
        "require_expiration": False,
        "enforce_expiration": False,
    }
    if not policy_file.exists():
        if explicit:
            raise click.ClickException(f'Policy file not found: "{policy_file}"')
        return defaults
    try:
        raw = yaml.safe_load(policy_file.read_text(encoding="utf-8")) or {}
    except (yaml.YAMLError, OSError) as exc:
        if explicit:
            raise click.ClickException(
                f'Policy file unreadable: "{policy_file}": {exc}'
            ) from exc
        click.echo(
            f'Warning: ignoring unreadable policy file "{policy_file}": {exc}',
            err=True,
        )
        return defaults
    gate = raw.get("gate") if isinstance(raw, dict) else None
    if not isinstance(gate, dict):
        if explicit:
            raise click.ClickException(
                f'Policy file "{policy_file}" has no top-level `gate:` mapping.'
            )
        return defaults
    for key in tuple(defaults):
        value = gate.get(key)
        if isinstance(value, bool):
            defaults[key] = value
    return defaults


@click.command("gate")
@click.argument("target", required=False, default="prompts/")
@click.option("--json", "as_json", is_flag=True, default=False, help="Emit JSON output.")
@click.option(
    "--policy-file",
    "policy_file",
    type=click.Path(path_type=Path, dir_okay=False),
    default=None,
    help="Policy source (YAML). Reads `gate.*` keys when present. Defaults to `.pddrc`.",
)
@click.option("--allow-waivers/--no-allow-waivers", default=None)
@click.option("--forbid-waivers/--no-forbid-waivers", default=None)
@click.option("--require-expiration/--no-require-expiration", default=None)
@click.option("--enforce-expiration/--no-enforce-expiration", default=None)
def gate_cmd(  # pylint: disable=too-many-arguments,too-many-locals
    target: str,
    as_json: bool,
    policy_file: Path | None,
    allow_waivers: bool | None,
    forbid_waivers: bool | None,
    require_expiration: bool | None,
    enforce_expiration: bool | None,
) -> None:
    """Validate waiver policy across prompt files."""
    target_path = Path(target)
    if not target_path.exists():
        raise click.ClickException(f'Path not found: "{target}"')

    resolved_policy = policy_file or Path(".pddrc")
    policy = _load_gate_policy(resolved_policy, explicit=policy_file is not None)
    overrides = {
        "allow_waivers": allow_waivers,
        "forbid_waivers": forbid_waivers,
        "require_expiration": require_expiration,
        "enforce_expiration": enforce_expiration,
    }
    for key, value in overrides.items():
        if value is not None:
            policy[key] = value
    if policy["forbid_waivers"]:
        policy["allow_waivers"] = False

    rows: list[dict[str, Any]] = []
    violations: list[str] = []
    for prompt_path in _discover_prompts(target_path):
        ir = parse_prompt_contracts(prompt_path)
        for waiver in summarize_waivers(ir.waivers, ir.known_rule_ids):
            waiver_row = {"prompt": str(prompt_path), **waiver}
            outcome = "pass"
            reasons: list[str] = []

            status = str(waiver_row.get("status") or "")
            if status in {"malformed", "unknown-rule"}:
                reasons.append(status)
            if not policy["allow_waivers"]:
                reasons.append("waivers-forbidden")
            if policy["require_expiration"] and waiver_row.get("expires") is None:
                reasons.append("missing-expiration")
            if policy["enforce_expiration"] and status == "expired":
                reasons.append("expired")

            if reasons:
                outcome = "fail"
                violations.append(
                    f"{prompt_path}: {waiver_row.get('id')} ({', '.join(reasons)})"
                )
            waiver_row["policy_outcome"] = outcome
            waiver_row["policy_reasons"] = reasons
            rows.append(waiver_row)

    payload = {
        "policy": policy,
        "waivers": rows,
        "violations": violations,
        "ok": not violations,
    }
    if as_json:
        click.echo(json.dumps(payload, indent=2))
    else:
        if not rows:
            click.echo("No waivers found.")
        for row in rows:
            reasons = ",".join(row["policy_reasons"]) if row["policy_reasons"] else "-"
            click.echo(
                f"{row['prompt']} {row['id']} rule={row['rule_id']} "
                f"status={row['status']} expires={row['expires'] or '-'} "
                f"outcome={row['policy_outcome']} reasons={reasons}"
            )
        if violations:
            click.echo("Policy violations:")
            for violation in violations:
                click.echo(f"  - {violation}")

    raise click.exceptions.Exit(1 if violations else 0)
