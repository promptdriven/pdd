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

from ..contract_check import check_prompt as check_contract_prompt
from ..contract_compile import compile_prompt
from ..prompt_lint import (
    LintIssue,
    LintResult,
    apply_suggestions,
    run_llm_ambiguity_pass,
    run_llm_guidance_pass,
    scan_prompt,
)
from ..prompt_lint_pipeline import (
    PromptLintPipelineOptions,
    concrete_suggestion,
    run_prompt_lint_pipeline,
)

# Re-exported for tests that patch LLM helpers on this module.
__all__ = [
    "apply_suggestions",
    "run_llm_ambiguity_pass",
    "run_llm_guidance_pass",
]

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


def _render_guidance(guidance: dict) -> None:
    """Render one prompt coach guidance payload."""
    _console.print(f"[bold]{escape(str(guidance.get('path', '')))}[/bold]")
    if guidance.get("error"):
        _console.print(f"  [bold red]ERROR[/bold red] {escape(str(guidance['error']))}")
        return
    summary = str(guidance.get("summary", "")).strip()
    if summary:
        _console.print(f"  [cyan]Summary:[/cyan] {escape(summary)}")
    sections = (
        ("vocabulary_suggestions", "Vocabulary Suggestions"),
        ("rule_rewrites", "Formalizable Rule Rewrites"),
        ("acceptance_criteria_improvements", "Acceptance Criteria Improvements"),
        ("formalization_notes", "Formalization Notes"),
    )
    for key, title in sections:
        items = guidance.get(key, [])
        if not items:
            continue
        _console.print(f"  [cyan]{title}:[/cyan]")
        for item in items:
            _console.print(f"    - {escape(_guidance_item_text(item))}")


def _guidance_item_text(item: object) -> str:
    """Render a guidance list item compactly."""
    if not isinstance(item, dict):
        return str(item)
    parts: list[str] = []
    for key in ("term", "rule_id", "finding", "suggestion", "rewrite", "criterion", "why"):
        value = item.get(key)
        if value:
            parts.append(f"{key}: {value}")
    return "; ".join(parts) if parts else _json.dumps(item, sort_keys=True)


def _render_clarify_summary(path: Path, written: int) -> None:
    """Render deterministic follow-up checks after prompt clarify writes."""
    lint_result = scan_prompt(path)
    contract_result = check_contract_prompt(path)
    compile_result = compile_prompt(path)
    _console.print(f"[green]Wrote {written} vocabulary definition(s).[/green]")
    _console.print(
        "[cyan]Recheck:[/cyan] "
        f"lint {lint_result.warn_count} warn/{lint_result.error_count} error; "
        f"contracts {contract_result.warn_count} warn/{contract_result.error_count} error; "
        f"compile {compile_result.error_count} error"
    )


def _pipeline_options_from_ctx(
    ctx: click.Context,
    *,
    target: Optional[str],
    stories_dir: Optional[str],
    strict: bool,
    llm: bool,
    apply_fixes: bool,
    non_interactive: bool,
) -> PromptLintPipelineOptions:
    """Build pipeline options from Click context and flags."""
    obj = ctx.obj or {}
    return PromptLintPipelineOptions(
        target=Path(target) if target is not None else None,
        stories_dir=Path(stories_dir) if stories_dir is not None else None,
        strict=strict,
        llm=llm,
        apply_fixes=apply_fixes,
        non_interactive=non_interactive,
        strength=obj.get("strength", 0.5),
        temperature=obj.get("temperature", 0.0),
        time=obj.get("time"),
        verbose=obj.get("verbose", False),
    )


def _clarify_prompts() -> tuple:
    """Click prompt callables for interactive clarify."""

    def choice_prompt(message: str, *, type: object, default: str = "", show_choices: bool = False) -> str:
        if isinstance(type, list):
            type = click.Choice(type)
        return click.prompt(message, type=type, default=default, show_choices=show_choices)

    def int_prompt(message: str, *, type: object) -> int:
        return click.prompt(message, type=type)

    return (choice_prompt, click.prompt, int_prompt)


def _display_clarify_issue(issue: LintIssue) -> None:
    """Show one ambiguous term before the author chooses a definition."""
    suggestion = concrete_suggestion(issue)
    _console.print(f"\n[bold]Ambiguous term:[/bold] {escape(issue.term)}")
    if issue.interpretations:
        _console.print("[cyan]Possible interpretations:[/cyan]")
        for idx, interpretation in enumerate(issue.interpretations, 1):
            _console.print(f"  {idx}. {escape(interpretation)}")
    if suggestion:
        _console.print(f"[cyan]Suggested definition:[/cyan] {escape(suggestion)}")


def _validate_lint_flags(
    *,
    ambiguity: bool,
    llm: bool,
    non_interactive: bool,
) -> None:
    llm_mode = ambiguity or llm
    if non_interactive and not llm_mode:
        raise click.UsageError("--non-interactive requires --ambiguity.")


def _lint_exit_code(results: list[LintResult], *, strict: bool) -> int:
    total_errors = sum(r.error_count for r in results)
    total_warns = sum(r.warn_count for r in results)
    if total_errors > 0 or (strict and total_warns > 0):
        return 2
    if total_warns > 0:
        return 1
    return 0


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
    help=(
        "Run LLM ambiguity review; coaching and clarification run automatically "
        "when ambiguities are found."
    ),
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
    hidden=True,
    help="Deprecated alias for --ambiguity.",
)
@click.option(
    "--non-interactive",
    is_flag=True,
    default=False,
    help="With --ambiguity, accept concrete LLM vocabulary suggestions without prompting.",
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
    non_interactive: bool,
    strict: bool,
    apply_fixes: bool,
) -> None:
    """Lint a prompt file or user-story directory for ambiguous terms.

    Deterministic checks always run. Pass --ambiguity for LLM review; when
    ambiguities are found, coaching and clarification run automatically.

    \b
    Examples:
      pdd prompt lint prompts/foo_python.prompt
      pdd prompt lint --stories user_stories/
      pdd prompt lint --json prompts/foo_python.prompt
      pdd prompt lint --ambiguity prompts/foo_python.prompt
      pdd prompt lint --ambiguity --non-interactive prompts/foo_python.prompt
      pdd prompt lint --ambiguity --apply prompts/foo_python.prompt

    \b
    Exit codes:
      0  no issues
      1  warnings only (unless --strict)
      2  errors present, or any issue with --strict
    """
    llm_mode = ambiguity or llm
    _validate_lint_flags(
        ambiguity=ambiguity,
        llm=llm,
        non_interactive=non_interactive,
    )
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
    options = _pipeline_options_from_ctx(
        ctx,
        target=target,
        stories_dir=stories_dir,
        strict=strict,
        llm=llm_mode,
        apply_fixes=apply_fixes,
        non_interactive=non_interactive or as_json,
    )
    interactive_clarify = llm_mode and not non_interactive and not as_json
    pipeline = run_prompt_lint_pipeline(
        options,
        clarify_prompts=_clarify_prompts() if interactive_clarify else None,
        before_clarify_issue=_display_clarify_issue if interactive_clarify else None,
    )

    for path, written in pipeline.apply_written:
        if not quiet:
            _console.print(
                f"[green]Applied {written} vocabulary suggestion(s) to {path}[/green]"
            )

    if llm_mode and not as_json:
        for _path in pipeline.clarify_no_issues:
            _console.print("[green]No LLM-detected ambiguities to clarify.[/green]")
        for path, written in pipeline.clarify_written:
            _render_clarify_summary(path, written)

    if as_json:
        if llm_mode and pipeline.guidances:
            payload = {
                "results": [r.as_dict() for r in pipeline.results],
                "guidance": pipeline.guidances,
            }
            click.echo(_json.dumps(payload, indent=2))
        else:
            click.echo(_json.dumps([r.as_dict() for r in pipeline.results], indent=2))
    else:
        for result in pipeline.results:
            _render_result(result, quiet=quiet)
        if llm_mode and pipeline.guidances:
            for guidance in pipeline.guidances:
                ambiguities = guidance.get("ambiguities", [])
                if ambiguities:
                    _console.print("[cyan]Ambiguities detected before coaching:[/cyan]")
                    for item in ambiguities:
                        issue = LintIssue(
                            level="warn",
                            term=str(item.get("term", "")),
                            section=str(item.get("section", "llm")),
                            line=str(item.get("line", "")),
                            message=str(item.get("message", "")),
                            suggestion=str(item.get("suggestion", "")),
                            interpretations=[
                                str(x) for x in item.get("interpretations", [])
                            ],
                        )
                        _render_issue(issue)
                _render_guidance(guidance)

    if llm_mode and not strict:
        raise click.exceptions.Exit(0)
    raise click.exceptions.Exit(_lint_exit_code(pipeline.results, strict=strict))
