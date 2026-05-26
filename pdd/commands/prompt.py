"""Commands for inspecting prompt and story assets."""
# pylint: disable=unknown-option-value
from __future__ import annotations

import json
from pathlib import Path
from typing import Optional

import click

from ..prompt_lint import LintResult, run_llm_ambiguity_pass, scan_prompt, scan_stories


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
    "--ambiguity",
    is_flag=True,
    default=False,
    hidden=True,
    help="Enable deterministic ambiguity and observation checks on prompt and story text.",
)
@click.option(
    "--llm",
    "use_llm",
    is_flag=True,
    default=False,
    help=(
        "Add advisory LLM review of ambiguous prompt/story prose (recommended for authoring; "
        "requires PDD Cloud or configured API credentials)."
    ),
)
@click.pass_context
def prompt_lint(  # pylint: disable=too-many-arguments,too-many-positional-arguments,too-many-branches,unknown-option-value
    ctx: click.Context,
    target: Optional[str],
    stories_dir: Optional[str],
    as_json: bool,
    strict: bool,
    ambiguity: bool,
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
        ambiguity = True

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
    if ambiguity and use_llm:
        obj = ctx.obj or {}
        use_cloud = not bool(obj.get("local", False))
        for result in results:
            llm_issues = run_llm_ambiguity_pass(
                result.path,
                strength=obj.get("strength", 0.5),
                temperature=obj.get("temperature", 0.0),
                time=obj.get("time"),
                verbose=obj.get("verbose", False),
                use_cloud=use_cloud,
            )
            if strict:
                for issue in llm_issues:
                    issue.level = "error"
            result.issues.extend(llm_issues)

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

    if strict:
        raise click.exceptions.Exit(_exit_code(results, strict=True))
    raise click.exceptions.Exit(deterministic_exit_code)


prompt_group.add_command(prompt_lint)
