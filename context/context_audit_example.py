# context/context_audit_example.py
"""Example: audit a prompt's context-window usage by source with the shared core.

Demonstrates :func:`pdd.context_audit.audit_prompt_file`, the deterministic,
no-LLM core that both ``pdd context`` and the ``pdd connect`` context-audit
endpoint use. It builds a tiny prompt with a resolvable include and a deferred
``<shell>`` tag, runs the audit, and prints the structured per-source result.
"""
from __future__ import annotations

from pathlib import Path

from rich.console import Console

from pdd.context_audit import audit_prompt_text, row_percent, threshold_exceeded

console = Console()


def run_context_audit_example() -> None:
    """Write a sample prompt under ./output and audit its context usage."""
    output_dir = Path("./output")
    (output_dir / "context").mkdir(parents=True, exist_ok=True)

    # A resolvable include whose realized content is attributed to its own row.
    include_path = output_dir / "context" / "preamble.txt"
    include_path.write_text("alpha beta gamma delta epsilon", encoding="utf-8")

    prompt_path = output_dir / "demo_python.prompt"
    prompt_path.write_text(
        "Write the module.\n"
        "<include>context/preamble.txt</include>\n"
        "<shell>echo deferred and not counted</shell>\n",
        encoding="utf-8",
    )

    # No LLM call, no shell run, no web fetch — purely deterministic. ``base_dir``
    # resolves the prompt's relative includes from ./output (where we wrote them).
    audit = audit_prompt_text(
        prompt_path.read_text(encoding="utf-8"), model="gpt-4o", base_dir=str(output_dir)
    )

    console.print(f"[bold]Model:[/bold] {audit.model}")
    console.print(
        f"[bold]Total:[/bold] {audit.total_tokens} tokens "
        f"(limit={audit.context_limit}, used={audit.percent_used}%)"
    )
    console.print("[bold]By source:[/bold]")
    for row in audit.rows:
        share = row_percent(row, audit.total_tokens)
        note = f"  ({row.note})" if row.note else ""
        console.print(f"  [{row.status}] {row.source}: {row.tokens} tokens ({share}%){note}")

    if audit.warnings:
        console.print("[bold yellow]Warnings:[/bold yellow]")
        for warning in audit.warnings:
            console.print(f"  - {warning}")

    over_budget = threshold_exceeded(audit.percent_used, threshold=80)
    console.print(f"[bold]Over 80% budget:[/bold] {over_budget}")


if __name__ == "__main__":
    run_context_audit_example()
