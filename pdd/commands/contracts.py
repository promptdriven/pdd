# pylint: disable=duplicate-code
"""
Contract authoring quality utilities (pdd contracts …).
"""
from __future__ import annotations

import json as _json
from pathlib import Path
from typing import Optional

import click
from rich.console import Console
from rich.markup import escape

from ..contract_check import (
    ContractIssue,
    ContractResult,
    check_directory,
    check_prompt,
    check_stories,
    run_llm_ambiguity_pass,
)
from ..contract_compile import ContractIR, compile_directory, compile_prompt

_console = Console(highlight=False)


# ---------------------------------------------------------------------------
# Rich output helpers
# ---------------------------------------------------------------------------

def _render_issue(issue: ContractIssue) -> None:
    """Print one ContractIssue to the console."""
    badge_style = "bold red" if issue.level == "error" else "bold yellow"
    badge = f"[{badge_style}]{issue.level.upper()}[/{badge_style}]"

    code_str = f"[dim cyan]{escape(issue.code)}[/dim cyan]"
    rid_str = (
        f"  [dim magenta]{escape(issue.rule_id)}[/dim magenta]"
        if issue.rule_id
        else ""
    )
    loc_str = f"  [dim][{escape(issue.section)}][/dim]" if issue.section else ""

    _console.print(f"  {badge}  {code_str}{rid_str}{loc_str}  {escape(issue.message)}")

    if issue.line:
        _console.print(f"       [dim italic]{escape(issue.line[:120])}[/dim italic]")

    if issue.interpretations:
        _console.print("       Possible interpretations:")
        for idx, interp in enumerate(issue.interpretations, 1):
            _console.print(f"         {idx}. {escape(interp)}")

    if issue.suggestion and "<add a precise" not in issue.suggestion:
        _console.print(
            f"       [cyan]Suggestion:[/cyan]\n"
            f"         [green]{escape(issue.suggestion)}[/green]"
        )


def _render_result(result: ContractResult, *, quiet: bool = False) -> None:
    """Print a ContractResult header and all its issues."""
    if not result.issues:
        if not quiet:
            _console.print(f"[bold]{result.path}[/bold]  [green]✓ clean[/green]")
        return
    _console.print(
        f"[bold]{result.path}[/bold]  "
        f"[yellow]{result.warn_count} warn[/yellow]  "
        f"[red]{result.error_count} error[/red]"
    )
    for issue in result.issues:
        _render_issue(issue)


def _render_ir(result: ContractIR, *, quiet: bool = False) -> None:
    """Print a compiled ContractIR summary."""
    if not result.has_contract_rules:
        if not quiet:
            _console.print(
                f"[bold]{result.path}[/bold]  "
                "[dim]No <contract_rules> section — no contract IR.[/dim]"
            )
        return

    status = "[green]compiled[/green]" if result.error_count == 0 else "[red]failed[/red]"
    _console.print(
        f"[bold]{result.path}[/bold]  {status}  "
        f"[cyan]{result.rule_count} rules[/cyan]  "
        f"[red]{result.error_count} errors[/red]"
    )
    for rule in result.rules:
        obligations = ", ".join(
            f"{obligation.type}:{obligation.modal}"
            for obligation in rule.obligations
        ) or "-"
        _console.print(
            f"  [magenta]{escape(rule.id)}[/magenta]  "
            f"{escape(rule.title or '-') }  "
            f"[dim]condition:[/dim] {escape(rule.condition or '-') }  "
            f"[dim]obligations:[/dim] {escape(obligations)}"
        )
    for error in result.compile_errors:
        _console.print(
            f"  [bold red]ERROR[/bold red]  "
            f"[dim cyan]{escape(error.code)}[/dim cyan]  "
            f"[dim magenta]{escape(error.rule_id)}[/dim magenta]  "
            f"{escape(error.message)}"
        )
        if error.line:
            _console.print(f"       [dim italic]{escape(error.line[:120])}[/dim italic]")


# ---------------------------------------------------------------------------
# Click group and command
# ---------------------------------------------------------------------------

@click.group(name="contracts")
def contracts_group() -> None:
    """Contract authoring quality utilities."""


@contracts_group.command("check")
@click.argument("target", type=click.Path(exists=True))
@click.option(
    "--json",
    "as_json",
    is_flag=True,
    default=False,
    help="Output results as JSON.",
)
@click.option(
    "--strict",
    is_flag=True,
    default=False,
    help="Treat all warnings as errors (exit 2 even for warnings).",
)
@click.option(
    "--stories",
    "stories_dir",
    type=click.Path(exists=True, file_okay=False),
    default=None,
    help="Scan a user-story directory for ## Covers rule-ID validity.",
)
@click.option(
    "--llm-ambiguity",
    "llm_ambiguity",
    is_flag=True,
    default=False,
    help="Run optional LLM ambiguity review on <contract_rules> terms.",
)
@click.pass_context
def contracts_check(  # pylint: disable=too-many-arguments,too-many-locals,too-many-branches
    ctx: click.Context,
    target: str,
    as_json: bool,
    strict: bool,
    stories_dir: Optional[str],
    llm_ambiguity: bool,
) -> None:
    """Check prompt contract sections for structural authoring defects.

    \b
    Examples:
      pdd contracts check prompts/foo_python.prompt
      pdd contracts check prompts/
      pdd contracts check --json prompts/
      pdd contracts check --strict prompts/foo_python.prompt
      pdd contracts check --stories user_stories/ prompts/foo_python.prompt
      pdd contracts check --llm-ambiguity prompts/foo_python.prompt

    \b
    Checks (deterministic, no LLM required):
      DUPLICATE_ID        — same rule ID used more than once
      MALFORMED_ID        — ID prefix doesn't match R-NNN or sequential N.
      NON_SEQUENTIAL_ID   — gap in explicit rule IDs (warn only)
      MISSING_MODAL       — rule lacks MUST / MUST NOT / MAY / SHOULD
      VAGUE_TERM          — vague phrase without <vocabulary> definition
      UNKNOWN_COVERAGE_REF — <coverage> cites an ID not in <contract_rules>
      UNCOVERED_MUST_NOT  — MUST NOT rule absent from <coverage> (when present)
      UNKNOWN_STORY_REF   — story ## Covers cites an unknown rule ID

    \b
    Exit codes:
      0  no issues
      1  warnings only (unless --strict)
      2  errors present, or any issue with --strict
    """
    obj = ctx.obj or {}
    quiet: bool = obj.get("quiet", False)
    verbose: bool = obj.get("verbose", False)
    strength: float = obj.get("strength", 0.5)
    temperature: float = obj.get("temperature", 0.0)
    time_val: Optional[float] = obj.get("time")

    all_results: list[ContractResult] = []
    target_path = Path(target)

    # Scan a single prompt file
    if target_path.is_file():
        result = check_prompt(target_path, strict=strict)
        if llm_ambiguity:
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
        for prompt_result in check_directory(target_path, strict=strict):
            if llm_ambiguity:
                llm_issues = run_llm_ambiguity_pass(
                    prompt_result.path,
                    strength=strength,
                    temperature=temperature,
                    time=time_val,
                    verbose=verbose,
                )
                if strict:
                    for issue in llm_issues:
                        issue.level = "error"
                prompt_result.issues.extend(llm_issues)
            all_results.append(prompt_result)

    # Scan user-story directory
    if stories_dir is not None:
        prompts_dir = target_path if target_path.is_dir() else target_path.parent
        all_results.extend(
            check_stories(Path(stories_dir), prompts_dir, strict=strict)
        )

    # Output
    if as_json:
        click.echo(_json.dumps([r.as_dict() for r in all_results], indent=2))
    else:
        for result in all_results:
            _render_result(result, quiet=quiet)

    # Exit code
    total_errors = sum(r.error_count for r in all_results)
    total_warns = sum(r.warn_count for r in all_results)

    if total_errors > 0 or (strict and total_warns > 0):
        raise click.exceptions.Exit(2)
    if total_warns > 0:
        raise click.exceptions.Exit(1)


@contracts_group.command("compile")
@click.argument("target", type=click.Path(exists=True))
@click.option(
    "--json",
    "as_json",
    is_flag=True,
    default=False,
    help="Output compiled contract IR as JSON.",
)
@click.pass_context
def contracts_compile(
    ctx: click.Context,
    target: str,
    as_json: bool,
) -> None:
    """Compile <contract_rules> into deterministic JSON contract IR.

    \b
    Examples:
      pdd contracts compile prompts/foo_python.prompt
      pdd contracts compile --json prompts/foo_python.prompt
      pdd contracts compile prompts/

    \b
    The v1 compiler is intentionally conservative. It requires each rule to
    have an explicit stable ID such as R1, a parseable "When ..." condition,
    and at least one observable obligation such as:
      MUST return HTTP 409
      MUST write one upload record
      MUST NOT write a new upload record
      MUST NOT call provider_client
      MUST emit refund_rejected
      MUST raise ValueError

    Prompts without <contract_rules> are legacy-safe and exit 0.
    """
    obj = ctx.obj or {}
    quiet: bool = obj.get("quiet", False)
    target_path = Path(target)

    if target_path.is_file():
        results = [compile_prompt(target_path)]
    else:
        results = compile_directory(target_path)

    if as_json:
        click.echo(_json.dumps([r.as_dict() for r in results], indent=2))
    else:
        for result in results:
            _render_ir(result, quiet=quiet)

    if any(result.error_count > 0 for result in results):
        raise click.exceptions.Exit(2)
