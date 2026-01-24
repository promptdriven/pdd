"""
src/cli/cli.py

This module implements the Command Line Interface (CLI) for the PDD Prompt Linter.
It handles argument parsing, configuration, pipeline orchestration, and output rendering.
"""

import sys
from pathlib import Path
from typing import Optional
from enum import Enum
try:
    from typing import Annotated
except ImportError:
    from typing_extensions import Annotated

import typer
import click
from rich.console import Console
from rich.panel import Panel
from rich.syntax import Syntax

# Import internal modules
from src.utils.models import Severity
from src.utils.pipeline import lint_file, LintConfig
from src.utils.report import render_report

# Initialize Typer app and Rich console
app = typer.Typer(
    name="pdd-linter",
    help="PDD Prompt Linter: Analyze and improve prompts based on Prompt Driven Development principles.",
    add_completion=False,
)
console = Console()

class OutputFormat(str, Enum):
    TEXT = "text"
    JSON = "json"
    MD = "md"

class FailOnLevel(str, Enum):
    WARNING = "warning"
    ERROR = "error"

class LLMProvider(str, Enum):
    AUTO = "auto"
    OPENAI = "openai"
    ANTHROPIC = "anthropic"
    GOOGLE = "google"
    CUSTOM = "custom"

# Define a subclass of LintConfig to hold CLI-specific fields
# that might not be in the base LintConfig definition yet.
class CLIConfig(LintConfig):
    provider: Optional[str] = None
    llm_base_url: Optional[str] = None
    llm_max_retries: Optional[int] = None
    budget: Optional[int] = None
    grounding: Optional[str] = None
    assume_cloud_grounding: Optional[bool] = None
    assume_local: Optional[bool] = None
    
    # Allow extra fields for forward compatibility
    model_config = {"extra": "allow"}

def _get_severity_rank(severity: Severity) -> int:
    """
    Helper to map severity to an integer for comparison.
    INFO=0, WARNING=1, ERROR=2.
    """
    if severity == Severity.ERROR:
        return 2
    if severity == Severity.WARNING:
        return 1
    return 0


@app.command()
def main(
    prompt_file: Annotated[
        Path, 
        typer.Argument(
            exists=False, # We handle existence check manually for better error messages
            help="Path to the prompt file to lint."
        )
    ],
    # --- Configuration Flags ---
    format: Annotated[
        OutputFormat, 
        typer.Option(
            "--format", "-f",
            help="Output format.",
            case_sensitive=False
        )
    ] = OutputFormat.TEXT,
    severity_threshold: Annotated[
        str, 
        typer.Option(
            "--severity-threshold", "-t",
            help="Minimum severity level to display.",
            click_type=click.Choice(["info", "warning", "error"], case_sensitive=False)
        )
    ] = "info",
    fail_on: Annotated[
        Optional[FailOnLevel], 
        typer.Option(
            "--fail-on",
            help="Return exit code 1 if issues of this severity (or higher) are found.",
            case_sensitive=False
        )
    ] = None,
    fix: Annotated[
        bool, 
        typer.Option(
            "--fix", 
            help="Enable auto-fix generation (requires LLM)."
        )
    ] = False,
    in_place: Annotated[
        bool, 
        typer.Option(
            "--in-place", "-i",
            help="Overwrite the original file with the fixed version (requires --fix)."
        )
    ] = False,
    fix_output: Annotated[
        Optional[Path], 
        typer.Option(
            "--fix-output", 
            help="Path to save the fixed prompt (requires --fix)."
        )
    ] = None,
    output: Annotated[
        Optional[Path], 
        typer.Option(
            "--output", "-o",
            help="Path to write the analysis report to."
        )
    ] = None,
    
    # --- Grounding Flags ---
    assume_cloud_grounding: Annotated[
        bool, 
        typer.Option(
            "--assume-cloud-grounding",
            help="Assume cloud-native context (mutually exclusive with --assume-local)."
        )
    ] = False,
    assume_local: Annotated[
        bool, 
        typer.Option(
            "--assume-local",
            help="Assume local execution context (mutually exclusive with --assume-cloud-grounding)."
        )
    ] = False,

    # --- LLM Configuration Flags ---
    use_llm: Annotated[
        bool, 
        typer.Option(
            "--llm/--no-llm",
            help="Enable or disable LLM-based analysis."
        )
    ] = True,
    llm_provider: Annotated[
        LLMProvider, 
        typer.Option(
            "--llm-provider",
            help="LLM provider to use.",
            case_sensitive=False
        )
    ] = LLMProvider.AUTO,
    llm_model: Annotated[
        Optional[str], 
        typer.Option(
            "--llm-model",
            help="Specific model name override."
        )
    ] = None,
    llm_base_url: Annotated[
        Optional[str], 
        typer.Option(
            "--llm-base-url",
            help="API base URL override."
        )
    ] = None,
    llm_timeout_seconds: Annotated[
        int, 
        typer.Option(
            "--llm-timeout-seconds",
            help="Timeout for LLM requests in seconds."
        )
    ] = 20,
    llm_max_retries: Annotated[
        int, 
        typer.Option(
            "--llm-max-retries",
            help="Maximum number of retries for LLM requests."
        )
    ] = 2,
    llm_budget_tokens: Annotated[
        int, 
        typer.Option(
            "--llm-budget-tokens",
            help="Token budget for LLM analysis."
        )
    ] = 2000,
):
    """
    Analyze a prompt file for adherence to PDD (Prompt Driven Development) principles.
    """
    
    # 1. Validate Flag Combinations
    if in_place and not fix:
        console.print("[red]Error: --in-place requires --fix to be enabled.[/red]")
        raise typer.Exit(code=1)
    
    if fix_output and not fix:
        console.print("[red]Error: --fix-output requires --fix to be enabled.[/red]")
        raise typer.Exit(code=1)
        
    if in_place and fix_output:
        console.print("[red]Error: --in-place and --fix-output are mutually exclusive.[/red]")
        raise typer.Exit(code=1)

    if assume_cloud_grounding and assume_local:
        console.print("[red]Error: --assume-cloud-grounding and --assume-local are mutually exclusive.[/red]")
        raise typer.Exit(code=1)

    # 2. Validate Input File
    # We read the file to validate access permissions and existence as requested
    try:
        prompt_file.read_text(encoding="utf-8")
    except FileNotFoundError:
        console.print(f"[red]Error: File not found: {prompt_file}[/red]")
        raise typer.Exit(code=1)
    except PermissionError:
        console.print(f"[red]Error: Permission denied reading file: {prompt_file}[/red]")
        raise typer.Exit(code=1)
    except Exception as e:
        console.print(f"[red]Error reading file: {e}[/red]")
        raise typer.Exit(code=1)

    # 3. Configure Pipeline
    
    # Determine grounding
    grounding_val = None
    if assume_cloud_grounding:
        grounding_val = "cloud"
    elif assume_local:
        grounding_val = "local"

    try:
        # Use CLIConfig to capture all flags, even those not yet in LintConfig
        config = CLIConfig(
            use_llm=use_llm,
            generate_fix=fix,
            llm_timeout=llm_timeout_seconds,
            llm_model_override=llm_model,
            
            # Extra fields supported by CLIConfig
            provider=llm_provider.value,
            llm_max_retries=llm_max_retries,
            budget=llm_budget_tokens,
            llm_base_url=llm_base_url,
            assume_cloud_grounding=assume_cloud_grounding,
            assume_local=assume_local,
            grounding=grounding_val
        )
        
    except TypeError as e:
        console.print(f"[red]Configuration Error (TypeError): {e}[/red]")
        raise typer.Exit(code=1)
    except Exception as e:
        console.print(f"[red]Configuration Error: {e}[/red]")
        raise typer.Exit(code=1)

    # 4. Run Pipeline
    try:
        report = lint_file(prompt_file, config=config)
    except Exception as e:
        console.print(f"[red]Unexpected error during pipeline execution: {e}[/red]")
        raise typer.Exit(code=1)

    # 5. Handle Fixes
    if fix:
        if report.suggested_fix:
            if in_place:
                try:
                    prompt_file.write_text(report.suggested_fix, encoding="utf-8")
                    console.print(f"[green]Fixed prompt written to {prompt_file} (in-place).[/green]")
                except Exception as e:
                    console.print(f"[red]Error writing fix in-place: {e}[/red]")
            elif fix_output:
                try:
                    fix_output.parent.mkdir(parents=True, exist_ok=True)
                    fix_output.write_text(report.suggested_fix, encoding="utf-8")
                    console.print(f"[green]Fixed prompt written to {fix_output}.[/green]")
                except Exception as e:
                    console.print(f"[red]Error writing fix to output file: {e}[/red]")
            else:
                # Print to stdout if no file destination specified
                # We use a Panel to distinguish it from the report
                console.print(Panel(
                    Syntax(report.suggested_fix, "text", theme="monokai", word_wrap=True),
                    title="Suggested Fix",
                    border_style="green"
                ))
        else:
            console.print("[yellow]Warning: --fix was requested, but no fix scaffold was generated.[/yellow]")

    # 6. Filter Issues by Severity for Display
    # We keep the original list for the exit code check, but filter for rendering
    original_issues = report.issues
    
    try:
        threshold_enum = Severity(severity_threshold.lower())
    except ValueError:
        threshold_enum = Severity.INFO

    threshold_rank = _get_severity_rank(threshold_enum)
    filtered_issues = [
        issue for issue in original_issues 
        if _get_severity_rank(issue.severity) >= threshold_rank
    ]
    
    # Temporarily swap issues for rendering
    report.issues = filtered_issues

    # 7. Render Report
    output_path_str = str(output) if output else None
    try:
        # Pass format as positional argument to match render_report signature
        render_report(report, format.value, output_path=output_path_str)
    except Exception as e:
        console.print(f"[red]Error rendering report: {e}[/red]")
        # Restore issues before exiting just in case
        report.issues = original_issues
        raise typer.Exit(code=1)

    # Restore original issues for logic checks
    report.issues = original_issues

    # 8. Determine Exit Code
    exit_code = 0

    # Critical failure condition: Score is 0 and there are errors
    has_errors = any(i.severity == Severity.ERROR for i in report.issues)
    if report.score == 0 and has_errors:
        exit_code = 1

    # Fail-on threshold condition
    if fail_on:
        try:
            fail_rank = _get_severity_rank(Severity(fail_on.value))
        except ValueError:
            fail_rank = 1 # Default to warning if mapping fails
            
        if any(_get_severity_rank(i.severity) >= fail_rank for i in report.issues):
            exit_code = 1

    raise typer.Exit(code=exit_code)


if __name__ == "__main__":
    app()