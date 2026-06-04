"""``pdd checkup gate`` — evidence manifest and waiver policy enforcement."""
from __future__ import annotations

import json
from dataclasses import dataclass, field
from pathlib import Path
from typing import Any, Optional

import click
import yaml

from ..contract_check import _check_coverage_entries
from ..contract_ir import parse_prompt_contracts
from ..checkup_advisory import advisory_for_review, final_exit_code, report_as_dict
from ..gate_main import GateResult, run_gate_policy
from ..waiver_policy import summarize_waivers, waiver_id_to_rule_map
from .checkup_review_options import review_option


def _discover_prompts(target: Path) -> list[Path]:
    if target.is_file():
        return [target] if target.suffix == ".prompt" else []
    return sorted(
        p for p in target.rglob("*.prompt")
        if not p.name.lower().endswith("_llm.prompt")
    )


def _is_prompt_file_target(target: Optional[str]) -> bool:
    """True when TARGET is a single ``.prompt`` file (waiver-only scan)."""
    if not target:
        return False
    return Path(target).suffix == ".prompt"


def _load_waiver_gate_policy(policy_file: Path, *, explicit: bool) -> dict[str, bool]:
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


@dataclass
class _WaiverGateResult:
    passed: bool
    policy: dict[str, bool]
    waivers: list[dict[str, Any]] = field(default_factory=list)
    violations: list[str] = field(default_factory=list)

    def as_dict(self) -> dict[str, Any]:
        return {
            "passed": self.passed,
            "policy": dict(self.policy),
            "waivers": self.waivers,
            "violations": self.violations,
        }


def _run_waiver_gate(
    target: Path,
    *,
    policy_file: Path,
    explicit_policy: bool,
    allow_waivers: bool | None,
    forbid_waivers: bool | None,
    require_expiration: bool | None,
    enforce_expiration: bool | None,
) -> _WaiverGateResult:
    if not target.exists():
        raise click.ClickException(f'Path not found: "{target}"')

    policy = _load_waiver_gate_policy(policy_file, explicit=explicit_policy)
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
    for prompt_path in _discover_prompts(target):
        ir = parse_prompt_contracts(prompt_path)
        coverage_text = ir.sections.get("coverage", "")
        if coverage_text:
            for issue in _check_coverage_entries(
                coverage_text,
                ir.known_rule_ids,
                ir.known_waiver_ids,
                waiver_id_to_rule_map(ir.waivers),
            ):
                if issue.level == "error":
                    violations.append(f"{prompt_path}: {issue.code} ({issue.message})")

        for waiver in summarize_waivers(ir.waivers, ir.known_rule_ids):
            waiver_row = {"prompt": str(prompt_path), **waiver}
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
                violations.append(
                    f"{prompt_path}: {waiver_row.get('id')} ({', '.join(reasons)})"
                )
            waiver_row["policy_outcome"] = "fail" if reasons else "pass"
            waiver_row["policy_reasons"] = reasons
            rows.append(waiver_row)

    return _WaiverGateResult(
        passed=not violations,
        policy=policy,
        waivers=rows,
        violations=violations,
    )


@click.command("gate")
@click.argument("target", required=False, default=None)
@click.option(
    "--policy",
    "evidence_policy_path",
    type=click.Path(exists=True, dir_okay=False),
    default=None,
    help="Evidence policy YAML file (default: built-in policy).",
)
@click.option(
    "--policy-file",
    "waiver_policy_file",
    type=click.Path(path_type=Path, dir_okay=False),
    default=None,
    help="Waiver policy source (YAML). Reads `gate.*` keys. Defaults to `.pddrc`.",
)
@click.option(
    "--prompts-dir",
    type=click.Path(exists=True, file_okay=False, path_type=Path),
    default=None,
    help="Prompt tree for waiver checks (default: prompts/, or TARGET when a .prompt path).",
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
@click.option("--allow-waivers/--no-allow-waivers", default=None)
@click.option("--forbid-waivers/--no-forbid-waivers", default=None)
@click.option("--require-expiration/--no-require-expiration", default=None)
@click.option("--enforce-expiration/--no-enforce-expiration", default=None)
@click.option(
    "--skip-evidence",
    is_flag=True,
    default=False,
    help="Run waiver policy only (no evidence manifest checks).",
)
@click.option(
    "--skip-waivers",
    is_flag=True,
    default=False,
    help="Run evidence policy only (no waiver scans).",
)
@review_option
@click.pass_context
def gate_cmd(  # pylint: disable=too-many-arguments,too-many-locals
    ctx: click.Context,
    review: str,
    target: Optional[str],
    evidence_policy_path: Optional[str],
    waiver_policy_file: Path | None,
    prompts_dir: Optional[Path],
    stories_dir: Optional[str],
    tests_dir: Optional[str],
    as_json: bool,
    allow_waivers: bool | None,
    forbid_waivers: bool | None,
    require_expiration: bool | None,
    enforce_expiration: bool | None,
    skip_evidence: bool,
    skip_waivers: bool,
) -> None:
    """Enforce PDD evidence manifests and waiver policy across prompt contracts."""
    project_root = Path.cwd()
    prompt_only = _is_prompt_file_target(target)
    run_evidence = not skip_evidence and not prompt_only
    run_waivers = not skip_waivers

    if run_evidence:
        try:
            evidence_result = run_gate_policy(
                project_root,
                policy_path=Path(evidence_policy_path) if evidence_policy_path else None,
                target=target,
                stories_dir=Path(stories_dir) if stories_dir else None,
                tests_dir=Path(tests_dir) if tests_dir else None,
            )
        except FileNotFoundError as exc:
            raise click.ClickException(str(exc)) from exc
    else:
        evidence_result = GateResult(passed=True, manifests_checked=0)

    if run_waivers:
        resolved_waiver_policy = waiver_policy_file or Path(".pddrc")
        if prompt_only:
            waiver_root = Path(target)
        else:
            waiver_root = prompts_dir or Path("prompts")
        if waiver_root.exists():
            waiver_result = _run_waiver_gate(
                waiver_root,
                policy_file=resolved_waiver_policy,
                explicit_policy=waiver_policy_file is not None,
                allow_waivers=allow_waivers,
                forbid_waivers=forbid_waivers,
                require_expiration=require_expiration,
                enforce_expiration=enforce_expiration,
            )
        else:
            waiver_result = _WaiverGateResult(passed=True, policy={})
    else:
        waiver_result = _WaiverGateResult(passed=True, policy={})

    passed = evidence_result.passed and waiver_result.passed
    exit_code = 0 if passed else 1

    advisory = advisory_for_review(
        review,
        {
            "passed": passed,
            "evidence": evidence_result.as_dict(),
            "waivers": waiver_result.as_dict(),
        },
        command="pdd checkup gate",
        ctx_obj=ctx.obj,
    )
    if as_json:
        payload: dict[str, Any] = {
            "passed": passed,
            "exit_code": exit_code,
            "evidence": evidence_result.as_dict(),
            "waivers": waiver_result.as_dict(),
        }
        if review == "explain":
            payload["advisory"] = report_as_dict(advisory)
        if hasattr(evidence_result, "manifests_checked"):
            payload["manifests_checked"] = evidence_result.manifests_checked
        click.echo(json.dumps(payload, indent=2))
    else:
        if run_evidence:
            if evidence_result.passed and evidence_result.manifests_checked:
                click.echo(
                    "Evidence gate passed "
                    f"({evidence_result.manifests_checked} manifest(s) checked)"
                )
            elif not evidence_result.passed:
                click.echo("Evidence gate failed")
                for failure in evidence_result.failures:
                    click.echo(f"- {failure.message}")
                    if failure.fix_command:
                        click.echo(f"  Run: {failure.fix_command}")
        if run_waivers:
            if not waiver_result.waivers:
                click.echo("No waivers found.")
            for row in waiver_result.waivers:
                reasons = ",".join(row["policy_reasons"]) if row["policy_reasons"] else "-"
                click.echo(
                    f"{row['prompt']} {row['id']} rule={row['rule_id']} "
                    f"status={row['status']} expires={row['expires'] or '-'} "
                    f"outcome={row['policy_outcome']} reasons={reasons}"
                )
        if run_waivers and waiver_result.violations:
            click.echo("Waiver policy violations:")
            for violation in waiver_result.violations:
                click.echo(f"  - {violation}")
        if not passed:
            click.echo("PDD gate failed")
        if review == "explain" and advisory.findings:
            click.echo(f"[advisory] status={advisory.status}")
            for finding in advisory.findings:
                click.echo(f"  [{finding.severity}] {finding.area}: {finding.message}")

    raise click.exceptions.Exit(final_exit_code(exit_code, advisory))
