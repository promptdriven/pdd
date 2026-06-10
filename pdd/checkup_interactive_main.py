"""Interactive checkup orchestration for prompt-shaped ``pdd checkup`` targets."""

from __future__ import annotations

from copy import deepcopy
from pathlib import Path
from typing import Callable, Optional, Union

import click

from .checkup_interactive_session import (
    ApprovedPatch,
    InteractiveRepairSession,
    NON_APPROVING_PATCH_KINDS,
    RepairOption,
)
from .checkup_prompt_apply import apply_approved_patches as run_patch_apply
from .checkup_prompt_main import (
    PromptSourceSetReport,
    SourceSetFinding,
    build_prompt_source_set_report,
)

_EVIDENCE_EXCERPT_LEN = 200
_PRIMARY_KIND_BY_SOURCE = {
    "lint": "vocab_definition",
    "contract": "contract_rule",
    "coverage": "coverage_line",
    "gate": "waiver",
    "snapshot": "contract_rule",
}
_SessionType = Union[InteractiveRepairSession, "ClickInteractiveSession"]


def _truncate_excerpt(text: str, max_len: int = _EVIDENCE_EXCERPT_LEN) -> str:
    cleaned = " ".join(str(text).split())
    if len(cleaned) <= max_len:
        return cleaned
    return cleaned[: max_len - 3] + "..."


def filter_interactive_findings(
    report: PromptSourceSetReport,
    *,
    explicit_interactive: bool,
) -> list[SourceSetFinding]:
    """Return findings that belong in an interactive repair session."""
    if explicit_interactive:
        return list(report.findings)
    return [finding for finding in report.findings if finding.requires_clarification]


def build_repair_options_for_finding(
    finding: SourceSetFinding,
    *,
    project_root: Optional[Path] = None,
    fallback_target: Optional[Path] = None,
) -> list[RepairOption]:
    """Build up to two repair candidates from one structured finding."""
    primary_action = finding.recommended_action or "Apply suggested repair"
    primary_preview = _truncate_excerpt(finding.evidence or finding.message)
    alternate_label = "Alternative repair"
    alternate_preview = _truncate_excerpt(finding.message)
    primary_kind = _PRIMARY_KIND_BY_SOURCE.get(finding.source_check, "vocab_definition")
    alternate_kind = (
        "story_template"
        if finding.file.suffix.lower() == ".md"
        else "append_covers"
    )
    target = finding.file
    source_path = finding.file
    if project_root is not None and not source_path.is_absolute():
        source_path = project_root / source_path
    if fallback_target is not None and not source_path.exists():
        source_path = fallback_target
        target = fallback_target
    if project_root is not None:
        try:
            target = source_path.resolve().relative_to(project_root.resolve())
        except ValueError:
            target = source_path
    return [
        RepairOption(
            label=primary_action,
            preview=primary_preview,
            patch=ApprovedPatch(
                kind=primary_kind,
                target=target,
                anchor={"finding_id": finding.finding_id, "line": finding.line},
                replacement=primary_action,
                finding_id=finding.finding_id,
            ),
        ),
        RepairOption(
            label=alternate_label,
            preview=alternate_preview,
            patch=ApprovedPatch(
                kind=alternate_kind,
                target=target,
                anchor={"finding_id": finding.finding_id, "line": finding.line},
                replacement=alternate_preview,
                finding_id=finding.finding_id,
            ),
        ),
    ]


class ClickInteractiveSession:
    """Click-native ``InteractiveRepairSession`` backed by report findings."""

    def __init__(self) -> None:
        self.report: PromptSourceSetReport | None = None
        self._options_by_finding: dict[str, list[RepairOption]] = {}
        self.presented_options: dict[str, list[RepairOption]] = {}
        self.recorded_choices: list[tuple[str, RepairOption]] = []

    def seed(self, report: PromptSourceSetReport) -> None:
        """Index repair options from a structured source-set report."""
        self.report = report
        self._options_by_finding = {
            finding.finding_id: build_repair_options_for_finding(
                finding,
                project_root=report.project_root,
                fallback_target=report.prompt_path,
            )
            for finding in report.findings
        }

    def present_finding(self, finding_id: str) -> list[RepairOption]:
        """Return repair candidates for one finding."""
        options = list(self._options_by_finding.get(finding_id, []))
        self.presented_options[finding_id] = options
        return list(options)

    def ask(self, question: str) -> str:
        """Ask a free-form clarification question in the terminal."""
        return click.prompt(question, type=str, default="", show_default=False)

    def record_choice(self, finding_id: str, option: RepairOption) -> None:
        """Record one validated menu choice for a finding."""
        presented = self.presented_options.get(finding_id)
        if presented is None or option not in presented:
            raise ValueError(
                f"repair option {option.label!r} was not presented for {finding_id!r}"
            )
        if any(existing_id == finding_id for existing_id, _ in self.recorded_choices):
            raise ValueError(f"choice already recorded for {finding_id!r}")
        self.recorded_choices.append((finding_id, option))

    def approved_patches(self) -> list[ApprovedPatch]:
        """Return approving patches from recorded menu choices."""
        patches: list[ApprovedPatch] = []
        for finding_id, option in self.recorded_choices:
            patch = option.patch
            if (
                isinstance(patch, ApprovedPatch)
                and patch.kind not in NON_APPROVING_PATCH_KINDS
            ):
                copied = deepcopy(patch)
                if not copied.finding_id:
                    copied.finding_id = finding_id
                patches.append(copied)
        return patches


def _skip_option(finding: SourceSetFinding) -> RepairOption:
    return RepairOption(
        label="Skip",
        preview="Skip this finding",
        patch=ApprovedPatch(
            kind="skip",
            target=finding.file,
            anchor={"finding_id": finding.finding_id},
            replacement="",
            finding_id=finding.finding_id,
        ),
    )


def _custom_option(finding: SourceSetFinding, definition: str) -> RepairOption:
    return RepairOption(
        label="Write my own definition",
        preview=_truncate_excerpt(definition),
        patch=ApprovedPatch(
            kind="custom_no_patch",
            target=finding.file,
            anchor={"finding_id": finding.finding_id},
            replacement=definition,
            finding_id=finding.finding_id,
        ),
    )


def _append_presented_option(
    session: ClickInteractiveSession,
    finding_id: str,
    option: RepairOption,
) -> None:
    presented = session.presented_options.get(finding_id)
    if presented is None:
        raise ValueError(f"finding {finding_id!r} was not presented")
    if option not in presented:
        session.presented_options[finding_id] = list(presented) + [option]


def _register_dynamic_option(
    session: _SessionType,
    finding_id: str,
    option: RepairOption,
) -> None:
    """Add a dynamically-created option (skip/custom) to any session that tracks presented_options.

    Both ClickInteractiveSession and FakeInteractiveSession validate that an option
    was presented before record_choice() accepts it.  This helper registers the
    option with whichever session type is in use so the subsequent record_choice()
    call succeeds without requiring an isinstance check.
    """
    presented_options = getattr(session, "presented_options", None)
    if not isinstance(presented_options, dict):
        return
    presented = presented_options.get(finding_id)
    if presented is None:
        return
    if option not in presented:
        presented_options[finding_id] = list(presented) + [option]


def _prompt_menu_choice(
    finding: SourceSetFinding,
    options: list[RepairOption],
) -> int:
    click.echo(f"\n[{finding.finding_id}] {finding.message}")
    if finding.evidence:
        click.echo(f"  {_truncate_excerpt(finding.evidence)}")

    label_a = options[0].label if options else "Option A"
    preview_a = options[0].preview if options else "(unavailable)"
    label_b = options[1].label if len(options) > 1 else "Option B"
    preview_b = options[1].preview if len(options) > 1 else "(unavailable)"

    click.echo("\nChoose one:")
    click.echo(f"[1] {label_a} — {preview_a}")
    click.echo(f"[2] {label_b} — {preview_b}")
    click.echo("[3] Write my own definition")
    click.echo("[4] Skip")
    return click.prompt("Choice", type=click.IntRange(1, 4), default=4)


def apply_approved_patches(
    patches: list[ApprovedPatch],
    *,
    dry_run: bool,
    quiet: bool,
    project_root: Path,
    original_target: str,
    strict: bool,
    choices_by_finding: dict[str, int],
) -> int:
    """Delegate to the deterministic patch applicator and return postflight exit code."""
    if not patches:
        return 0
    result = run_patch_apply(
        patches,
        repo_root=project_root,
        original_target=original_target,
        dry_run=dry_run,
        interactive=True,
        strict=strict,
        choices_by_finding=choices_by_finding,
    )
    if not quiet:
        if result.log_path is not None:
            click.echo(f"Apply log: {result.log_path}")
        if result.backup_root is not None:
            click.echo(f"Backups: {result.backup_root}")
        for record in result.findings:
            if record.status == "rejected":
                reason = f": {record.reason}" if record.reason else ""
                click.echo(
                    f"Rejected approved patch for {record.target_path}{reason}",
                    err=True,
                )
        click.echo(f"Postflight: {result.postflight_status}")
    return result.exit_code


def run_interactive_checkup(
    target: str,
    *,
    apply: bool = False,
    dry_run: bool = False,
    project_root: Optional[Path] = None,
    strict: bool = False,
    quiet: bool = False,
    explicit_interactive: bool = True,
    session_factory: Optional[Callable[[], InteractiveRepairSession]] = None,
) -> Optional[tuple[str, float, str]]:
    """Orchestrate report → session → optional apply for one prompt target."""
    root = project_root if project_root is not None else Path.cwd()
    prompt_path = Path(target)
    if not prompt_path.is_absolute():
        prompt_path = root / prompt_path
    if not prompt_path.is_file():
        raise click.UsageError(
            f"--interactive requires a single .prompt file target, got {target!r}."
        )

    report = build_prompt_source_set_report(
        prompt_path,
        target=target,
        project_root=root,
        strict=strict,
    )
    findings = filter_interactive_findings(
        report,
        explicit_interactive=explicit_interactive,
    )

    if not quiet:
        click.echo(f"Interactive checkup: {target}")
        click.echo(
            f"Status: {report.status}  Findings: {len(report.findings)}  "
            f"In scope: {len(findings)}"
        )

    session: _SessionType
    if session_factory is not None:
        session = session_factory()
    else:
        session = ClickInteractiveSession()
    session.seed(report)

    skipped = 0
    choices_by_finding: dict[str, int] = {}
    for finding in findings:
        options = session.present_finding(finding.finding_id)
        choice = _prompt_menu_choice(finding, options)
        choices_by_finding[finding.finding_id] = choice

        if choice == 4:
            skip_option = _skip_option(finding)
            _register_dynamic_option(session, finding.finding_id, skip_option)
            session.record_choice(finding.finding_id, skip_option)
            skipped += 1
            continue

        if choice == 3:
            definition = session.ask("Enter your definition:")
            custom_option = _custom_option(finding, definition)
            _register_dynamic_option(session, finding.finding_id, custom_option)
            session.record_choice(finding.finding_id, custom_option)
            continue

        index = choice - 1
        if 0 <= index < len(options):
            session.record_choice(finding.finding_id, options[index])
        else:
            click.echo(
                f"  Warning: option {choice} unavailable for [{finding.finding_id}] "
                f"({len(options)} option(s) presented). Skipping finding.",
                err=True,
            )
            skipped += 1

    patches = session.approved_patches()
    postflight_exit = 0
    if apply:
        postflight_exit = apply_approved_patches(
            patches,
            dry_run=dry_run,
            quiet=quiet,
            project_root=root,
            original_target=target,
            strict=strict,
            choices_by_finding=choices_by_finding,
        )

    cost = 0.0
    model = ""
    message = (
        f"Interactive checkup complete: {report.status} "
        f"({len(findings)} findings, {skipped} skipped)"
    )
    if not quiet:
        click.echo(f"\n{message}")
    if postflight_exit:
        raise click.exceptions.Exit(postflight_exit)
    return message, cost, model
