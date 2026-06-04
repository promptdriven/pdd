"""Deterministic contract checks for ``pdd contracts check`` and ``pdd checkup contract check``."""
from __future__ import annotations

import json
from pathlib import Path
from typing import Optional

import click

from ..checkup_advisory import advisory_for_review, final_exit_code, report_as_dict
from ..contract_check import ContractResult, check_directory, check_prompt, check_stories
from ..contract_ir import parse_prompt_contracts
from ..waiver_policy import summarize_waivers
from .checkup_review_options import review_option


def _exit_code(results: list[ContractResult], *, strict: bool) -> int:
    errors = sum(result.error_count for result in results)
    warnings = sum(result.warn_count for result in results)
    if errors or (strict and warnings):
        return 2
    return 1 if warnings else 0


@click.group(name="contracts")
def contracts_cli() -> None:
    """Deterministic contract section checks for prompt files."""


@contracts_cli.command("check")
@click.argument("target", type=click.Path(exists=True))
@click.option("--json", "as_json", is_flag=True, default=False, help="Output results as JSON.")
@click.option(
    "--strict",
    is_flag=True,
    default=False,
    help="Treat all warnings as errors.",
)
@click.option(
    "--stories",
    "stories_dir",
    type=click.Path(exists=True, file_okay=False),
    default=None,
    help="Scan a user-story directory for rule references.",
)
@review_option
@click.pass_context
def contracts_check(
    ctx: click.Context,
    review: str,
    target: str,
    as_json: bool,
    strict: bool,
    stories_dir: Optional[str],
) -> None:
    """Check contract sections for deterministic structural defects."""
    target_path = Path(target)
    if target_path.is_file():
        results = [check_prompt(target_path, strict=strict)]
    else:
        results = check_directory(target_path, strict=strict)

    if stories_dir is not None:
        prompts_dir = target_path if target_path.is_dir() else target_path.parent
        results.extend(check_stories(Path(stories_dir), prompts_dir, strict=strict))

    waiver_rows_by_path: dict[str, list[dict[str, object]]] = {}
    for result in results:
        if result.path.suffix != ".prompt":
            continue
        ir = parse_prompt_contracts(result.path)
        waiver_rows_by_path[str(result.path)] = summarize_waivers(ir.waivers, ir.known_rule_ids)

    payload: list[dict[str, object]] = []
    for result in results:
        row = result.as_dict()
        row["waivers"] = waiver_rows_by_path.get(str(result.path), [])
        payload.append(row)
    advisory = advisory_for_review(
        review,
        payload,
        command="pdd checkup contract check",
        ctx_obj=ctx.obj,
    )
    if as_json:
        if review == "explain":
            payload = [
                {**row, "advisory": report_as_dict(advisory)}
                for row in payload
            ]
        click.echo(json.dumps(payload, indent=2))
    else:
        for result in results:
            click.echo(
                f"{result.path}: {result.warn_count} warning(s), "
                f"{result.error_count} error(s)"
            )
            waiver_rows = waiver_rows_by_path.get(str(result.path), [])
            if waiver_rows:
                click.echo("  Waivers:")
                for waiver in waiver_rows:
                    expires = waiver.get("expires") or "-"
                    click.echo(
                        "    "
                        f"{waiver.get('id')}: rule={waiver.get('rule_id')} "
                        f"status={waiver.get('status')} expires={expires}"
                    )
            for issue in result.issues:
                click.echo(f"  {issue.level.upper()} {issue.code}: {issue.message}")

    raise click.exceptions.Exit(
        final_exit_code(_exit_code(results, strict=strict), advisory)
    )
