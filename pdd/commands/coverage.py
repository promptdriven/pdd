# pylint: disable=too-many-arguments,too-many-locals
"""
Coverage commands — contract coverage matrix.

Usage examples::

    pdd checkup coverage prompts/refund_payment_python.prompt
    pdd checkup coverage prompts/
    pdd checkup coverage --json prompts/
"""
from __future__ import annotations

import json
from pathlib import Path
from typing import Optional

import click
from rich.console import Console
from rich.table import Table
from rich import box

from ..coverage_contracts import (
    STATUS_CHECKED,
    STATUS_STORY_ONLY,
    STATUS_TEST_ONLY,
    STATUS_UNCHECKED,
    STATUS_WAIVED,
    STATUS_FAILED,
    CoverageResult,
    RuleCoverage,
    build_coverage,
    build_coverage_directory,
)

console = Console(stderr=True)
stdout_console = Console()

# Status → colour mapping for human-readable output
_STATUS_STYLE: dict[str, str] = {
    STATUS_CHECKED: "green",
    STATUS_STORY_ONLY: "yellow",
    STATUS_TEST_ONLY: "cyan",
    STATUS_UNCHECKED: "red",
    STATUS_WAIVED: "dim",
    STATUS_FAILED: "bold red",
}

_STATUS_LABEL: dict[str, str] = {
    STATUS_CHECKED: "checked",
    STATUS_STORY_ONLY: "story-only",
    STATUS_TEST_ONLY: "test-only",
    STATUS_UNCHECKED: "unchecked",
    STATUS_WAIVED: "waived",
    STATUS_FAILED: "failed",
}


def _format_list(items: list[str], fallback: str = "-") -> str:
    """Join items with newline, or return fallback if empty."""
    return "\n".join(items) if items else fallback


def _render_result_table(result: CoverageResult) -> None:
    """Render one CoverageResult as a Rich table to stdout."""
    stdout_console.print(f"\n[bold]Prompt:[/bold] {result.path}")

    if result.error:
        stdout_console.print(f"  [red]Error:[/red] {result.error}")
        return

    if result.read_errors:
        stdout_console.print("  [yellow]Scanner read errors:[/yellow]")
        for message in result.read_errors:
            stdout_console.print(f"    {message}")

    if result.regression_warnings:
        stdout_console.print("  [yellow]Story regression warnings:[/yellow]")
        for message in result.regression_warnings:
            stdout_console.print(f"    {message}")

    if result.stories:
        story_table = Table(
            box=box.SIMPLE_HEAD,
            show_header=True,
            header_style="bold",
            expand=False,
        )
        story_table.add_column("Story", style="bold", no_wrap=True)
        story_table.add_column("Regression", no_wrap=True)
        story_table.add_column("Tests")
        for story in result.stories:
            status_style = {
                "story-regression-passing": "green",
                "story-regression-missing": "yellow",
                "story-regression-stale": "bold red",
            }.get(story.status, "")
            story_table.add_row(
                story.story_id,
                f"[{status_style}]{story.status}[/{status_style}]",
                _format_list(story.tests),
            )
        stdout_console.print(story_table)

    if result.cross_unit_stories:
        partners_by_story: dict[str, set[str]] = {
            story_name: set() for story_name in result.cross_unit_stories
        }
        for rule in result.rules:
            if not getattr(rule, "is_cross_unit", False):
                continue
            for story_name in rule.stories:
                if story_name in partners_by_story:
                    partners_by_story[story_name].update(rule.cross_unit_partners)

        cross_table = Table(
            title="Cross-dev-unit stories",
            box=box.SIMPLE_HEAD,
            show_header=True,
            header_style="bold",
            expand=False,
        )
        cross_table.add_column("Story", style="bold", no_wrap=True)
        cross_table.add_column("Linked Units")
        for story_name in result.cross_unit_stories:
            cross_table.add_row(
                story_name,
                _format_list(sorted(partners_by_story.get(story_name, set()))),
            )
        stdout_console.print(cross_table)

    if not result.has_contract_rules:
        stdout_console.print("  [dim]No <contract_rules> section — no contract coverage data.[/dim]")
        return

    if not result.rules:
        stdout_console.print("  [dim]No rules found in <contract_rules>.[/dim]")
        return

    table = Table(
        box=box.SIMPLE_HEAD,
        show_header=True,
        header_style="bold",
        expand=False,
    )
    table.add_column("Rule", style="bold", no_wrap=True)
    table.add_column("Status", no_wrap=True)
    table.add_column("Stories")
    table.add_column("Tests")

    for rule in result.rules:
        style = _STATUS_STYLE.get(rule.status, "")
        label = _STATUS_LABEL.get(rule.status, rule.status)

        stories_cell = _format_list(rule.stories)
        if rule.waiver:
            suffix = ""
            if rule.waiver_status:
                suffix += f" [{rule.waiver_status}]"
            if rule.waiver_expires:
                suffix += f" expires={rule.waiver_expires}"
            tests_cell = f"waiver: {rule.waiver}{suffix}"
        elif rule.failures:
            tests_cell = _format_list(rule.failures)
        else:
            tests_cell = _format_list(rule.tests)

        table.add_row(
            rule.rule_id,
            f"[{style}]{label}[/{style}]",
            stories_cell,
            tests_cell,
        )

    stdout_console.print(table)

    summary = result.summary
    total = summary["total"]
    ok = summary["checked"] + summary["waived"]
    stdout_console.print(
        f"  Summary: {ok}/{total} rules fully covered "
        f"(checked={summary['checked']}, waived={summary['waived']}, "
        f"story-only={summary['story_only']}, test-only={summary['test_only']}, "
        f"unchecked={summary['unchecked']}, failed={summary['failed']})"
    )


@click.command("coverage")
@click.option(
    "--contracts",
    "use_contracts",
    is_flag=True,
    default=False,
    hidden=True,
    help="Compatibility alias; contract coverage is implied by this command.",
)
@click.option(
    "--json",
    "as_json",
    is_flag=True,
    default=False,
    help="Emit machine-readable JSON to stdout.",
)
@click.option(
    "--stories-dir",
    "--stories",
    "stories_dir",
    default=None,
    type=click.Path(file_okay=False),
    help=(
        "Directory containing story__*.md files (default: user_stories/). "
        "Alias: --stories (same flag as pdd contracts check)."
    ),
)
@click.option(
    "--tests-dir",
    "tests_dir",
    default=None,
    type=click.Path(file_okay=False),
    help="Directory containing test_*.py files (default: tests/).",
)
@click.option(
    "--story-regression-gate",
    "story_regression_gate",
    type=click.Choice(["off", "warn", "strict"]),
    default="warn",
    show_default=True,
    help="How missing/stale story regression tests affect this coverage run.",
)
@click.argument(
    "target",
    default="prompts/",
    required=False,
)
@click.pass_context
def coverage_cmd(
    ctx: click.Context,  # pylint: disable=unused-argument
    use_contracts: bool,  # pylint: disable=unused-argument
    as_json: bool,
    stories_dir: Optional[str],
    tests_dir: Optional[str],
    story_regression_gate: str,
    target: str,
) -> None:
    """Build a contract coverage matrix mapping rules to stories and tests.

    TARGET can be a single .prompt file or a directory (default: prompts/).
    Contract coverage is implied by the command name.

    Exit codes:
      0  all rules checked or waived, no scanner read errors
      1  coverage gaps and/or unreadable story/test files under scan dirs
      2  fatal error (missing TARGET, unreadable prompt file)

    JSON output uses an envelope ``{results, total_prompts, ...}``; see
    docs/coverage_contracts.md. ``pdd contracts check --json`` emits a
    top-level array of contract-check results instead.
    """
    stories_path = Path(stories_dir) if stories_dir else None
    tests_path = Path(tests_dir) if tests_dir else None

    target_path = Path(target)
    results: list[CoverageResult] = []

    if not target_path.exists():
        error_msg = f'Path not found: "{target}"'
        if as_json:
            print(json.dumps({"error": error_msg, "results": []}))
        else:
            console.print(f"[red]Error:[/red] {error_msg}")
        raise click.exceptions.Exit(2)

    if target_path.is_file():
        results.append(build_coverage(target_path, stories_path, tests_path))
    else:
        results = build_coverage_directory(target_path, stories_path, tests_path)

    # Determine exit code: fatal prompt errors (2) vs gaps/read issues (1)
    has_fatal = any(r.error for r in results)
    has_read_errors = any(r.read_errors for r in results)
    has_gap = any(
        rc.status in (STATUS_UNCHECKED, STATUS_STORY_ONLY, STATUS_TEST_ONLY)
        or rc.status == STATUS_FAILED
        for r in results
        for rc in r.rules
    )
    has_story_regression_gap = any(
        story.status in {"story-regression-missing", "story-regression-stale"}
        for r in results
        for story in r.stories
    )

    if as_json:
        output = {
            "results": [r.as_dict() for r in results],
            "total_prompts": len(results),
            "prompts_with_contracts": sum(1 for r in results if r.has_contract_rules),
            "story_regression_gate": story_regression_gate,
        }
        print(json.dumps(output, indent=2))
    else:
        if not results:
            stdout_console.print("[dim]No prompt files found.[/dim]")
        else:
            for result in results:
                _render_result_table(result)

    if has_fatal:
        raise click.exceptions.Exit(2)
    if story_regression_gate == "strict" and has_story_regression_gap:
        raise click.exceptions.Exit(1)
    if has_gap or has_read_errors:
        raise click.exceptions.Exit(1)
