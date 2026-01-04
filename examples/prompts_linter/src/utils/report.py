import json
from typing import Optional
from rich.console import Console
from rich.table import Table
from rich.panel import Panel
from rich.text import Text
from rich import box

# Import models based on the provided dependencies structure
from src.utils.models import Report, Issue, Severity

# Global console instance
console = Console()

def _render_text(report: Report, output_path: Optional[str] = None) -> None:
    """
    Renders the report to the console using Rich.
    If output_path is provided, writes plain text (no ANSI codes) to the file.
    """
    # Determine destination: stdout or a file capture
    target_console = console
    file_handle = None
    
    try:
        if output_path:
            file_handle = open(output_path, "w", encoding="utf-8")
            # Create a file-bound console that forces terminal mode off (no colors)
            target_console = Console(file=file_handle, force_terminal=False, no_color=True)

        # 1. Header / Summary
        score_color = "green" if report.score >= 80 else "yellow" if report.score >= 50 else "red"
        summary_text = Text(f"Score: {report.score}/100", style=f"bold {score_color}")
        
        if report.summary:
            summary_text.append(f"\n\n{report.summary}", style="default")

        target_console.print(Panel(
            summary_text, 
            title=f"Report: {report.filepath}", 
            expand=False,
            border_style="blue"
        ))
        target_console.print() # Spacer

        # 2. Issues Table
        if not report.issues:
            target_console.print(Panel("No issues found. Great job!", style="green"))
        else:
            table = Table(title="Detected Issues", box=box.SIMPLE)
            table.add_column("Rule", style="cyan", no_wrap=True)
            table.add_column("Severity", style="bold")
            table.add_column("Line", justify="right")
            table.add_column("Description")

            for issue in report.issues:
                # Map severity to color
                sev_style = "white"
                if issue.severity == Severity.ERROR:
                    sev_style = "red"
                elif issue.severity == Severity.WARNING:
                    sev_style = "yellow"
                elif issue.severity == Severity.INFO:
                    sev_style = "blue"

                table.add_row(
                    issue.rule_id,
                    Text(issue.severity.value, style=sev_style),
                    str(issue.line_number),
                    issue.description
                )

            target_console.print(table)
            
        # 3. LLM Analysis (Optional display if present)
        if report.llm_analysis:
            target_console.print()
            target_console.print(Panel(
                f"LLM Feedback: {report.llm_analysis.guide_alignment_summary}",
                title="AI Analysis",
                border_style="magenta"
            ))

    finally:
        if file_handle:
            file_handle.close()


def _render_markdown(report: Report) -> str:
    """
    Generates a Markdown string representation of the report.
    """
    lines = []
    lines.append(f"# PDD Prompt Report: `{report.filepath}`")
    lines.append("")
    lines.append(f"## Score: {report.score}/100")
    lines.append("")
    
    if report.summary:
        lines.append("### Summary")
        lines.append(report.summary)
        lines.append("")

    lines.append("### Issues")
    if not report.issues:
        lines.append("_No issues found._")
    else:
        # Markdown Table Header
        lines.append("| Rule | Severity | Line | Description |")
        lines.append("|---|---|---|---|")
        
        for issue in report.issues:
            lines.append(
                f"| {issue.rule_id} | {issue.severity.value} | {issue.line_number} | {issue.description} |"
            )
    
    if report.llm_analysis:
        lines.append("")
        lines.append("### AI Analysis")
        lines.append(report.llm_analysis.guide_alignment_summary)

    return "\n".join(lines)


def _render_json(report: Report) -> str:
    """
    Generates a JSON string representation of the report.
    """
    return report.model_dump_json(indent=2)


def render_report(report: Report, fmt: str, output_path: Optional[str] = None) -> None:
    """
    Main entry point to render the report.
    
    Args:
        report: The Report object to render.
        fmt: The format to render ('text', 'json', 'md').
        output_path: Optional file path to write the output to.
    """
    format_lower = fmt.lower()
    content = ""

    # Handle Text/Console rendering separately because it handles its own I/O logic
    # specifically for the rich library vs plain text file writing.
    if format_lower == "text":
        _render_text(report, output_path)
        return

    # Handle String-based formats (JSON, MD)
    if format_lower == "json":
        content = _render_json(report)
    elif format_lower == "md":
        content = _render_markdown(report)
    else:
        raise ValueError(f"Unsupported format: {fmt}. Choose from 'text', 'json', 'md'.")

    # Output Handling for String formats
    if output_path:
        try:
            with open(output_path, "w", encoding="utf-8") as f:
                f.write(content)
        except IOError as e:
            console.print(f"[red]Error writing to file {output_path}: {e}[/red]")
    else:
        # Print to stdout
        print(content)