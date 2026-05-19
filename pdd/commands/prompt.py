# pylint: disable=duplicate-code
"""
Prompt authoring and quality utilities (pdd prompt …).
"""
from __future__ import annotations

import json as _json
from pathlib import Path
from typing import Optional

import click
from rich.console import Console
from rich.markup import escape

from ..prompt_lint import (
    LintIssue,
    LintResult,
    apply_suggestions,
    run_llm_ambiguity_pass,
    scan_prompt,
    scan_stories,
)

_console = Console(highlight=False)


# ---------------------------------------------------------------------------
# Rich output helpers
# ---------------------------------------------------------------------------

def _render_issue(issue: LintIssue) -> None:
    """Print one LintIssue to the console in the canonical format."""
    badge_style = "bold red" if issue.level == "error" else "bold yellow"
    badge = f"[{badge_style}]{issue.level.upper()}[/{badge_style}]"
    loc = f"[dim][{escape(issue.section)}][/dim]"
    _console.print(f"  {badge}  {loc}  {escape(issue.message)}")
    if issue.line:
        _console.print(f"       [dim italic]{escape(issue.line[:120])}[/dim italic]")
    if issue.interpretations:
        _console.print("       Possible interpretations:")
        for idx, interp in enumerate(issue.interpretations, 1):
            _console.print(f"         {idx}. {escape(interp)}")
    if issue.suggestion:
        _console.print(
            f"       [cyan]Suggestion:[/cyan] Add to <vocabulary>:\n"
            f"         [green]{escape(issue.suggestion)}[/green]"
        )


def _render_result(result: LintResult, *, quiet: bool = False) -> None:
    """Print a LintResult header + all its issues."""
    total = len(result.issues)
    if total == 0:
        if not quiet:
            _console.print(f"[bold]{result.path}[/bold]  [green]✓ clean[/green]")
        return
    _console.print(f"[bold]{result.path}[/bold]  "
                   f"[yellow]{result.warn_count} warn[/yellow]  "
                   f"[red]{result.error_count} error[/red]")
    for issue in result.issues:
        _render_issue(issue)


# ---------------------------------------------------------------------------
# Click group and command
# ---------------------------------------------------------------------------

@click.group(name="prompt")
def prompt_group() -> None:
    """Prompt authoring and quality utilities."""


@prompt_group.command("lint")
@click.argument("target", required=False, type=click.Path(exists=True))
@click.option(
    "--ambiguity",
    is_flag=True,
    default=False,
    help="Enable ambiguity review options; required with --llm.",
)
@click.option(
    "--stories",
    "stories_dir",
    type=click.Path(exists=False),
    default=None,
    help="Scan a user story directory (may be combined with TARGET).",
)
@click.option(
    "--json",
    "as_json",
    is_flag=True,
    default=False,
    help="Output results as JSON.",
)
@click.option(
    "--llm",
    is_flag=True,
    default=False,
    help="Run optional LLM ambiguity pass (requires --ambiguity).",
)
@click.option(
    "--strict",
    is_flag=True,
    default=False,
    help="Treat all warnings as errors (exit 2 even for warnings).",
)
@click.option(
    "--apply",
    "apply_fixes",
    is_flag=True,
    default=False,
    help="Write suggested <vocabulary> entries back into the scanned file(s).",
)
@click.pass_context
def prompt_lint(  # pylint: disable=too-many-arguments,too-many-locals,too-many-branches
    ctx: click.Context,
    target: Optional[str],
    ambiguity: bool,
    stories_dir: Optional[str],
    as_json: bool,
    llm: bool,
    strict: bool,
    apply_fixes: bool,
) -> None:
    """Lint a prompt file or user-story directory for ambiguous terms.

    \b
    Examples:
      pdd prompt lint prompts/foo_python.prompt
      pdd prompt lint --ambiguity prompts/foo_python.prompt
      pdd prompt lint --stories user_stories/
      pdd prompt lint --stories user_stories/ prompts/foo_python.prompt
      pdd prompt lint --json prompts/foo_python.prompt
      pdd prompt lint --ambiguity --llm prompts/foo_python.prompt
      pdd prompt lint --apply prompts/foo_python.prompt

    \b
    Exit codes:
      0  no issues
      1  warnings only (unless --strict)
      2  errors present, or any issue with --strict
    """
    if llm and not ambiguity:
        raise click.UsageError("--llm requires --ambiguity.")
    if target is None and stories_dir is None:
        raise click.UsageError("Missing argument 'TARGET' unless --stories is supplied.")
    if stories_dir is not None:
        story_path = Path(stories_dir)
        if not story_path.is_dir():
            hint = ""
            if ".prompt" in story_path.name or ".prompt" in str(story_path):
                hint = (
                    "\n\nTo scan a prompt and stories together, pass the story "
                    "directory after --stories and the prompt as TARGET, for example:\n"
                    "  pdd prompt lint --stories user_stories/prompt_lint_samples/ "
                    "prompts/foo_python.prompt"
                )
            raise click.UsageError(
                f"--stories expects a directory containing story__*.md files, "
                f"got '{stories_dir}'.{hint}"
            )

    obj = ctx.obj or {}
    quiet: bool = obj.get("quiet", False)
    verbose: bool = obj.get("verbose", False)
    strength: float = obj.get("strength", 0.5)
    temperature: float = obj.get("temperature", 0.0)
    time_val: Optional[float] = obj.get("time")

    all_results: list[LintResult] = []

    if target is not None:
        target_path = Path(target)

        # Scan a single prompt file
        if target_path.is_file():
            result = scan_prompt(target_path, strict=strict)
            if llm:
                llm_issues = run_llm_ambiguity_pass(
                    target_path,
                    strength=strength,
                    temperature=temperature,
                    time=time_val,
                    verbose=verbose,
                )
                if strict:
                    for issue in llm_issues:
                        issue.level = "error"
                result.issues.extend(llm_issues)
            all_results.append(result)

        # Scan a directory of prompts
        elif target_path.is_dir():
            for prompt_path in sorted(target_path.rglob("*.prompt")):
                all_results.append(scan_prompt(prompt_path, strict=strict))

    # Scan user stories directory (via --stories flag)
    if stories_dir is not None:
        all_results.extend(scan_stories(Path(stories_dir), strict=strict))

    # --apply: write vocabulary suggestions back (read-only otherwise)
    if apply_fixes:
        for result in all_results:
            if result.issues and result.path.is_file():
                written = apply_suggestions(result.path, result.issues)
                if not quiet and written:
                    _console.print(
                        f"[green]Applied {written} vocabulary suggestion(s) to "
                        f"{result.path}[/green]"
                    )

    # Output
    if as_json:
        click.echo(_json.dumps([r.as_dict() for r in all_results], indent=2))
    else:
        for result in all_results:
            _render_result(result, quiet=quiet)

    # Determine exit code
    total_errors = sum(r.error_count for r in all_results)
    total_warns = sum(r.warn_count for r in all_results)

    if total_errors > 0 or (strict and total_warns > 0):
        raise click.exceptions.Exit(2)
    if total_warns > 0:
        raise click.exceptions.Exit(1)
