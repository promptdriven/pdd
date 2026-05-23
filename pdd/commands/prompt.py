"""Deterministic prompt lint command used by ``pdd checkup lint``."""
from __future__ import annotations

import json
from pathlib import Path
from typing import Optional

import click

from ..prompt_lint import LintResult, scan_prompt, scan_stories


def _exit_code(results: list[LintResult], *, strict: bool) -> int:
    errors = sum(result.error_count for result in results)
    warnings = sum(result.warn_count for result in results)
    if errors or (strict and warnings):
        return 2
    return 1 if warnings else 0


@click.command("lint")
@click.argument("target", required=False, type=click.Path(exists=True))
@click.option(
    "--stories",
    "stories_dir",
    type=click.Path(exists=True, file_okay=False),
    default=None,
    help="Scan a user-story directory, optionally alongside TARGET.",
)
@click.option("--json", "as_json", is_flag=True, default=False, help="Output results as JSON.")
@click.option(
    "--strict",
    is_flag=True,
    default=False,
    help="Treat all warnings as errors.",
)
def prompt_lint(
    target: Optional[str],
    stories_dir: Optional[str],
    as_json: bool,
    strict: bool,
) -> None:
    """Lint prompts and user stories for deterministic ambiguity findings."""
    if target is None and stories_dir is None:
        raise click.UsageError("Missing argument 'TARGET' unless --stories is supplied.")

    results: list[LintResult] = []
    if target is not None:
        path = Path(target)
        if path.is_file():
            results.append(scan_prompt(path, strict=strict))
        else:
            results.extend(
                scan_prompt(candidate, strict=strict)
                for candidate in sorted(path.rglob("*.prompt"))
            )
    if stories_dir is not None:
        results.extend(scan_stories(Path(stories_dir), strict=strict))

    if as_json:
        click.echo(json.dumps([result.as_dict() for result in results], indent=2))
    else:
        for result in results:
            click.echo(
                f"{result.path}: {result.warn_count} warning(s), "
                f"{result.error_count} error(s)"
            )
            for issue in result.issues:
                click.echo(f"  {issue.level.upper()} [{issue.section}] {issue.message}")

    raise click.exceptions.Exit(_exit_code(results, strict=strict))
