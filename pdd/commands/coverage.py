# pylint: disable=too-many-arguments,too-many-locals
"""
Coverage commands — contract coverage matrix.

Usage examples::

    pdd coverage --contracts prompts/refund_payment_python.prompt
    pdd coverage --contracts prompts/
    pdd coverage --contracts --json prompts/
    pdd coverage --contracts --stories-dir user_stories --tests-dir tests prompts/
"""
from __future__ import annotations

import json
import sys
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
            tests_cell = f"waiver: {rule.waiver}"
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
    required=True,
    help="Build a rule-to-evidence coverage matrix from <contract_rules>.",
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
    "stories_dir",
    default=None,
    type=click.Path(file_okay=False),
    help="Directory containing story__*.md files (default: user_stories/).",
)
@click.option(
    "--tests-dir",
    "tests_dir",
    default=None,
    type=click.Path(file_okay=False),
    help="Directory containing test_*.py files (default: tests/).",
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
    target: str,
) -> None:
    """Build a contract coverage matrix mapping rules to stories and tests.

    TARGET can be a single .prompt file or a directory (default: prompts/).
    Requires --contracts flag.

    Exit codes:
      0  all rules checked or waived
      1  at least one unchecked, story-only, or test-only rule
      2  error (file not found, parse failure)
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
        sys.exit(2)

    if target_path.is_file():
        results.append(build_coverage(target_path, stories_path, tests_path))
    else:
        results = build_coverage_directory(target_path, stories_path, tests_path)

    # Determine exit code
    has_error = any(r.error for r in results)
    has_gap = any(
        rc.status in (STATUS_UNCHECKED, STATUS_STORY_ONLY, STATUS_TEST_ONLY)
        or rc.status == STATUS_FAILED
        for r in results
        for rc in r.rules
    )

    if as_json:
        output = {
            "results": [r.as_dict() for r in results],
            "total_prompts": len(results),
            "prompts_with_contracts": sum(1 for r in results if r.has_contract_rules),
        }
        print(json.dumps(output, indent=2))
    else:
        if not results:
            stdout_console.print("[dim]No prompt files found.[/dim]")
        else:
            for result in results:
                _render_result_table(result)

    if has_error:
        sys.exit(2)
    elif has_gap:
        sys.exit(1)
    sys.exit(0)
