"""Commands for inspecting prompt and story assets."""
# pylint: disable=unknown-option-value
from __future__ import annotations

import json
from pathlib import Path
from typing import Optional

import click

from ..checkup_advisory import advisory_for_review, final_exit_code, report_as_dict
from ..prompt_lint import LintResult, scan_prompt, scan_stories
from .checkup_review_options import review_option


@click.group(name="prompt")
def prompt_group() -> None:
    """Inspect and maintain prompt assets."""


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
@click.option(
    "--llm",
    "use_llm",
    is_flag=True,
    default=False,
    help="Deprecated alias for --review explain.",
)
@review_option
@click.pass_context
def prompt_lint(  # pylint: disable=too-many-arguments,too-many-positional-arguments,too-many-branches,unknown-option-value
    ctx: click.Context,
    review: str,
    target: Optional[str],
    stories_dir: Optional[str],
    as_json: bool,
    strict: bool,
    use_llm: bool,
) -> None:
    """Lint prompts and user stories for quality and ambiguity (read-only, advisory).

    By default, runs a fast local heuristic scan suitable for CI. For prompt authoring,
    pass --llm to add an advisory LLM review of ambiguous prose (requires PDD Cloud
    or configured API credentials). Results are never written back to your files.
    """
    if target is None and stories_dir is None:
        raise click.UsageError("Missing argument 'TARGET' unless --stories is supplied.")

    if use_llm:
        click.echo(
            "DeprecationWarning: --llm is deprecated; use --review explain",
            err=True,
        )
        review = "explain"

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

    deterministic_exit_code = _exit_code(results, strict=strict)
    payload = [result.as_dict() for result in results]
    advisory = advisory_for_review(
        review,
        payload,
        command="pdd checkup lint",
        ctx_obj=ctx.obj,
    )

    if as_json:
        if review == "explain":
            payload = [
                {**item, "advisory": report_as_dict(advisory)}
                for item in payload
            ]
        click.echo(json.dumps(payload, indent=2))
    else:
        for result in results:
            click.echo(
                f"{result.path}: {result.warn_count} warning(s), "
                f"{result.error_count} error(s)"
            )
            for issue in result.issues:
                click.echo(f"  {issue.level.upper()} [{issue.section}] {issue.message}")

    exit_code = _exit_code(results, strict=True) if strict else deterministic_exit_code
    raise click.exceptions.Exit(final_exit_code(exit_code, advisory))


prompt_group.add_command(prompt_lint)
