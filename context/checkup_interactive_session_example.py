"""Demo script for the interactive prompt-repair session.

Usage:
    python context/checkup_interactive_session_example.py

    # To force the LLM session even if Pi is available:
    python context/checkup_interactive_session_example.py --llm

    # To force the Fake session (no LLM, no Pi, instant):
    python context/checkup_interactive_session_example.py --fake
"""
from __future__ import annotations

import sys
from pathlib import Path

# Ensure the parent directory is in the path so we can import the pdd package
sys.path.insert(0, str(Path(__file__).resolve().parents[1]))

import click

from pdd.checkup_interactive_session import (
    ApprovedPatch,
    FakeInteractiveSession,
    LlmInteractiveSession,
    PiInteractiveSession,
    make_session,
)

# A realistic sample report with two findings
SAMPLE_REPORT = {
    "schema": "pdd.prompt_source_set_report.v1",
    "findings": [
        {
            "finding_id": "F-001",
            "check": "prompt-source-set",
            "status": "failed",
            "summary": "Refund window is not explicitly defined — 'as soon as possible' is ambiguous",
            "details": (
                "The refund policy uses vague language. Downstream code that checks "
                "this prompt will fail because there is no measurable deadline."
            ),
            "file": "prompts/refund_policy.prompt",
        },
        {
            "finding_id": "F-002",
            "check": "prompt-source-set",
            "status": "failed",
            "summary": "Missing vocabulary definition for 'partial_refund'",
            "details": (
                "The term 'partial_refund' is used in contract rules but never defined "
                "in the vocabulary section."
            ),
            "file": "prompts/refund_policy.prompt",
        },
    ],
}


@click.command()
@click.option("--llm", "mode", flag_value="llm", help="Use LlmInteractiveSession (real LLM, no Pi)")
@click.option("--fake", "mode", flag_value="fake", help="Use FakeInteractiveSession (instant, no LLM)")
@click.option("--mode", "mode", default="auto", hidden=True)
def main(mode: str) -> None:
    click.echo("\nInteractive Prompt-Repair Session Demo")
    click.echo("=" * 40)

    pi_ok = PiInteractiveSession.is_available()
    click.echo(f"Pi  available : {pi_ok}  (Node >=22 + @earendil-works/pi-coding-agent)")
    click.echo(f"LLM available : always  (uses pdd's configured model)")
    click.echo(f"Mode          : {mode}\n")

    if mode == "fake":
        # Pre-load patches so the session is instant and deterministic
        session = FakeInteractiveSession(patches=[
            ApprovedPatch(
                kind="vocab_definition",
                target=Path("prompts/refund_policy.prompt"),
                anchor={"section": "Vocabulary"},
                replacement="- refund_window: 30 calendar days from purchase date",
                finding_id="F-001",
            ),
            ApprovedPatch(
                kind="vocab_definition",
                target=Path("prompts/refund_policy.prompt"),
                anchor={"section": "Vocabulary"},
                replacement="- partial_refund: a refund for less than the original purchase amount",
                finding_id="F-002",
            ),
        ])
    elif mode == "llm":
        session = LlmInteractiveSession()
    else:
        # auto: Pi-first, LLM fallback
        session = make_session()
        backend = "Pi" if isinstance(session, PiInteractiveSession) else "LLM"
        click.echo(f"Selected backend: {backend}\n")

    session.seed(SAMPLE_REPORT)

    click.echo(f"Seeded report with {len(SAMPLE_REPORT['findings'])} finding(s).")
    click.echo("Running session…\n")
    session.run()

    patches = session.approved_patches()
    click.echo(f"\n{'─' * 40}")
    click.echo(f"Approved patches: {len(patches)}")
    for i, p in enumerate(patches, 1):
        click.echo(f"\n  Patch #{i}")
        click.echo(f"    Finding : {p.finding_id}")
        click.echo(f"    Kind    : {p.kind}")
        click.echo(f"    File    : {p.target}")
        click.echo(f"    Anchor  : {p.anchor}")
        click.echo(f"    Replace : {p.replacement}")

    if not patches:
        click.echo("  (no patches approved)")


if __name__ == "__main__":
    main()
