"""
Example demonstrating how to programmatically execute prompt checkups,
generate a unified prompt source-set report, and render findings.
"""

from __future__ import annotations

import os
import sys
from pathlib import Path
from rich.console import Console

# Import the orchestrator and report models from the pdd package
from pdd.checkup_prompt_main import (
    build_prompt_source_set_report,
    render_prompt_source_set_report,
    PromptSourceSetReport,
)

# Initialize a rich console for beautifully formatted terminal outputs
console = Console()


def setup_mock_project(project_root: Path) -> tuple[Path, Path, Path]:
    """
    Sets up a mock prompt project with contract rules, a user story, and test coverage
    to simulate a real-world repository state.
    
    Parameters:
        project_root: The Path to the directory where mock files should be written.
        
    Returns:
        A tuple of (prompt_path, stories_dir, tests_dir).
    """
    stories_dir = project_root / "user_stories"
    tests_dir = project_root / "tests"
    
    # Ensure fresh directory structures
    stories_dir.mkdir(parents=True, exist_ok=True)
    tests_dir.mkdir(parents=True, exist_ok=True)

    # 1. Create a prompt file containing structural sections and contract rules
    prompt_path = project_root / "translate_python.prompt"
    prompt_content = """<system>
You are an expert translator.
</system>

<contract_rules>
R1: Output MUST be valid, well-formed JSON.
R2: Do NOT include conversational filler before or after the JSON payload.
</contract_rules>

<coverage>
R1: story__translation.md, test_R1_json_format
R2: story__translation.md
</coverage>
"""
    prompt_path.write_text(prompt_content, encoding="utf-8")

    # 2. Create a user story markdown file that covers both R1 and R2
    story_path = stories_dir / "story__translation.md"
    story_content = """# Story: High Quality Translation

<!-- pdd-story-prompts: translate_python.prompt -->

## Covers
- translate_python.prompt#R1
- translate_python.prompt#R2

## Acceptance Criteria
- Ensure output is valid JSON.
- Ensure no conversational filler.
"""
    story_path.write_text(story_content, encoding="utf-8")

    # 3. Create a python test file checking R1 (leaving R2 story-only)
    test_path = tests_dir / "test_translation.py"
    test_content = """# R1: Verify that output is valid JSON
def test_R1_json_format():
    assert True
"""
    test_path.write_text(test_content, encoding="utf-8")

    return prompt_path, stories_dir, tests_dir


def main() -> None:
    # Anchor all created output files to the local './output' directory
    project_root = Path("./output").resolve()
    
    console.print(f"[bold blue]Setting up mock project at {project_root}...[/bold blue]")
    prompt_path, stories_dir, tests_dir = setup_mock_project(project_root)

    console.print("\n[bold green]Running deterministic source-set checkup...[/bold green]")
    
    # Orchestrate the checkup engines (lint, contract, coverage, snapshot, gate)
    # to yield a unified PromptSourceSetReport.
    report: PromptSourceSetReport = build_prompt_source_set_report(
        prompt_path=prompt_path,
        target="translate_python",
        project_root=project_root,
        stories_dir=stories_dir,
        tests_dir=tests_dir,
        strict=False,
    )

    console.print("\n[bold yellow]--- Rendered Human Readable Report ---[/bold yellow]")
    # Use the built-in click renderer to output the overview
    render_prompt_source_set_report(report, quiet=False)

    console.print("\n[bold yellow]--- Programmatic Report Metadata ---[/bold yellow]")
    console.print(f"Report Schema: [cyan]{report.as_dict()['schema']}[/cyan]")
    console.print(f"Overall Status: [bold]{report.status.upper()}[/bold]")
    console.print(f"Has Contract Rules: [green]{report.coverage.has_contract_rules if report.coverage else False}[/green]")
    console.print(f"Deterministic Exit Code: [red]{report.deterministic_exit_code()}[/red]")

    # Inspect parsed coverage rules and print their identified status
    if report.coverage:
        console.print("\n[bold yellow]--- Rule Coverage Summary ---[/bold yellow]")
        for rule in report.coverage.rules:
            console.print(
                f"Rule [bold cyan]{rule.rule_id}[/bold cyan]: "
                f"Status=[magenta]{rule.status}[/magenta], "
                f"Stories={rule.stories}, "
                f"Tests={rule.tests}"
            )


if __name__ == "__main__":
    main()