"""Interactive checkup orchestration for .prompt file targets.

Orchestrates: report → InteractiveRepairSession → optional apply.
"""
from __future__ import annotations

from pathlib import Path
from typing import Optional

import click

from .checkup_prompt_main import SourceSetFinding, build_prompt_source_set_report


class InteractiveRepairSession:
    """Stub duck-typed protocol for the Block 1 InteractiveRepairSession.

    Exposes ask(prompt: str) -> str and an iterable findings interface.
    Replace with the real implementation once Block 1 is merged.
    """

    def __init__(self, findings: list[SourceSetFinding]) -> None:
        self._findings = list(findings)

    def ask(self, prompt: str) -> str:  # noqa: ARG002
        """Return a clarification answer (stub: returns empty string)."""
        return ""

    def __iter__(self):  # type: ignore[override]
        return iter(self._findings)


def run_interactive_checkup(
    target: str,
    *,
    apply: bool = False,
    dry_run: bool = False,
    project_root: Optional[Path] = None,
    strict: bool = False,
    quiet: bool = False,
) -> Optional[tuple[str, float, str]]:
    """Orchestrate report → session → optional apply for a .prompt target.

    Guards (enforced by the CLI layer before this is called):
    - --apply requires --interactive
    - non-TTY + --interactive raises UsageError
    - --dry-run: no writes (including no backup)
    - --interactive without --apply: no writes
    """
    root = project_root if project_root is not None else Path.cwd()
    report = build_prompt_source_set_report(
        Path(target),
        target=target,
        project_root=root,
        strict=strict,
    )

    if not quiet:
        click.echo(f"Interactive checkup: {target}")
        click.echo(f"Status: {report.status}  Findings: {len(report.findings)}")

    session = InteractiveRepairSession(report.findings)

    skipped = 0
    for finding in session:
        if not quiet:
            click.echo(f"\n[{finding.finding_id}] ({finding.severity}) {finding.message}")
            if finding.evidence:
                click.echo(f"  Evidence: {finding.evidence[:200]}")

        recommended = finding.recommended_action or "Apply automated fix"
        click.echo(
            f"\nChoose one:\n"
            f"[1] {recommended}\n"
            f"[2] Preview only\n"
            f"[3] Write my own definition\n"
            f"[4] Skip"
        )
        choice = click.prompt("Choice", type=click.IntRange(1, 4), default=4)

        if choice == 4:
            skipped += 1
            continue
        if choice == 3:
            session.ask(f"Clarify finding {finding.finding_id}")
            continue
        if choice == 1 and apply and not dry_run:
            # Block 3 applicator not yet merged — stub only.
            if not quiet:
                click.echo(f"  [stub] Would apply fix for {finding.finding_id} (Block 3 not merged).")

    cost = 0.0
    model = ""
    message = (
        f"Interactive checkup complete: {report.status} "
        f"({len(report.findings)} findings, {skipped} skipped)"
    )
    if not quiet:
        click.echo(f"\n{message}")
    return message, cost, model
