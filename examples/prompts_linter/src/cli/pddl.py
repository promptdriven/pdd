"""
src/cli/pddl.py

The primary command-line interface for the PDD Prompt Linter.
Handles user commands, argument parsing, and output formatting.
"""

import sys
import typer
from pathlib import Path
from typing import Optional
from enum import Enum

# Import backend components
from src.backend.core.lint_engine import LintEngine
from src.backend.models.findings import LintReport, Severity
from src.backend.rules.registry import default_registry

# IMPORTANT: Import rules module to trigger registration side-effects
import src.backend.rules.pdd_rules  # noqa: F401

app = typer.Typer(
    name="pddl",
    help="Prompt-Driven Development (PDD) Linter CLI",
    no_args_is_help=True,
    add_completion=False,
)


class OutputFormat(str, Enum):
    TEXT = "text"
    JSON = "json"


@app.command()
def lint(
    file: Path = typer.Argument(
        ...,
        exists=True,
        file_okay=True,
        dir_okay=False,
        readable=True,
        help="Path to the prompt file to lint.",
    ),
    format: OutputFormat = typer.Option(
        OutputFormat.TEXT, "--format", "-f", help="Output format (text or json)."
    ),
    resolve_includes: bool = typer.Option(
        False, "--resolve-includes", "-r", help="Resolve <include> tags before linting."
    ),
    config: Optional[Path] = typer.Option(
        None, "--config", "-c", help="Path to a configuration file."
    ),
):
    """
    Lint a prompt file against PDD rules.
    """
    try:
        # 1. Read Content
        try:
            content = file.read_text(encoding="utf-8")
        except FileNotFoundError:
            typer.secho(f"Error: File not found: {file}", err=True, fg=typer.colors.RED)
            raise typer.Exit(code=2)
        except Exception as e:
            typer.secho(f"Error reading file: {e}", err=True, fg=typer.colors.RED)
            raise typer.Exit(code=2)

        # 2. Prepare Options
        options = {
            "resolve_includes": resolve_includes,
            "config_path": str(config) if config else None,
        }

        # 3. Initialize Engine and Execute
        engine = LintEngine()
        report = engine.lint(content, file_path=str(file), options=options)

        # 4. Render Output
        if format == OutputFormat.JSON:
            # Print raw JSON to stdout
            typer.echo(report.model_dump_json(indent=2))
        else:
            _print_text_report(report)

        # 5. Determine Exit Code
        # Exit 1 if there are any errors, otherwise 0
        if report.summary.issue_counts.error > 0:
            raise typer.Exit(code=1)
        else:
            raise typer.Exit(code=0)

    except typer.Exit:
        raise
    except Exception as e:
        typer.secho(f"Unexpected error: {e}", err=True, fg=typer.colors.RED)
        raise typer.Exit(code=2)


@app.command()
def rules():
    """
    List all available linting rules.
    """
    rules_list = default_registry.get_all_rules()
    
    typer.secho("Available PDD Linting Rules:", bold=True)
    typer.echo("=" * 40)
    
    for rule in rules_list:
        # Color code the ID based on default severity
        color = typer.colors.WHITE
        if rule.severity == "error":
            color = typer.colors.RED
        elif rule.severity == "warn":
            color = typer.colors.YELLOW
        elif rule.severity == "info":
            color = typer.colors.BLUE
            
        rule_id_str = typer.style(f"{rule.rule_id:<10}", fg=color, bold=True)
        typer.echo(f"{rule_id_str} {rule.title}")


@app.command()
def explain(rule_id: str):
    """
    Get detailed information about a specific rule.
    """
    rule = default_registry.get_rule(rule_id.upper())
    
    if not rule:
        typer.secho(f"Error: Rule '{rule_id}' not found.", fg=typer.colors.RED, err=True)
        raise typer.Exit(code=2)

    typer.secho(f"Rule: {rule.rule_id} - {rule.title}", bold=True, fg=typer.colors.GREEN)
    typer.echo(f"Severity: {rule.severity.upper()}")
    typer.echo("-" * 40)
    
    # Since FunctionalRule might not have a docstring or detailed description attribute 
    # exposed in the base class in the provided snippet, we use what we have.
    # If the rule class had a 'description' or 'rationale' field, we would print it here.
    # For now, we print the docstring of the analyze method or the function itself.
    
    description = "No detailed description available."
    if hasattr(rule, 'func') and rule.func.__doc__:
        description = rule.func.__doc__.strip()
    elif rule.__doc__:
        description = rule.__doc__.strip()
        
    typer.echo(description)


def _print_text_report(report: LintReport):
    """
    Renders the LintReport in a human-readable format to stdout.
    """
    # Header
    score_color = typer.colors.GREEN
    if report.summary.score < 50:
        score_color = typer.colors.RED
    elif report.summary.score < 80:
        score_color = typer.colors.YELLOW

    typer.secho("\nPDD Lint Report", bold=True, underline=True)
    typer.echo(f"File: {report.filename}")
    typer.echo(f"Score: ", nl=False)
    typer.secho(f"{report.summary.score}/100", fg=score_color, bold=True)
    typer.echo(f"Tokens (est): {report.summary.token_count_estimate}")
    
    counts = report.summary.issue_counts
    summary_str = f"Errors: {counts.error} | Warnings: {counts.warn} | Info: {counts.info}"
    typer.secho(summary_str, dim=True)
    typer.echo("=" * 60)

    if not report.findings:
        typer.secho("No issues found. Great job!", fg=typer.colors.GREEN)
        return

    # Group findings by severity for cleaner output
    # Order: Error -> Warn -> Info
    sorted_findings = sorted(
        report.findings, 
        key=lambda x: (
            0 if x.severity == Severity.ERROR else 
            1 if x.severity == Severity.WARN else 
            2
        )
    )

    for finding in sorted_findings:
        # Determine color
        color = typer.colors.BLUE
        label = "INFO"
        if finding.severity == Severity.ERROR:
            color = typer.colors.RED
            label = "ERROR"
        elif finding.severity == Severity.WARN:
            color = typer.colors.YELLOW
            label = "WARN"

        # Print Finding Header
        typer.secho(f"[{label}] {finding.rule_id}: {finding.title}", fg=color, bold=True)
        
        # Print Location
        loc_str = "File-level"
        if finding.evidence:
            loc_str = f"Lines {finding.evidence.line_start}-{finding.evidence.line_end}"
        # Fallback for older rule implementations that might use line_number directly in message or custom fields
        # (The provided Finding model uses 'evidence', but the rules.py uses a helper that might map line_number to evidence)
        # Based on provided models, 'evidence' is the standard.
        
        typer.secho(f"  Location: {loc_str}", dim=True)
        
        # Print Message
        typer.echo(f"  {finding.message}")

        # Print Suggested Edits
        if finding.suggested_edits:
            typer.secho("  Suggested Edit:", fg=typer.colors.CYAN)
            for edit in finding.suggested_edits:
                # Indent the snippet
                snippet = edit.snippet.replace("\n", "\n    ")
                typer.echo(f"    {snippet}")
        
        typer.echo("-" * 60)


if __name__ == "__main__":
    app()