"""Unified prompt source-set report orchestration for ``pdd checkup`` prompt targets."""
from __future__ import annotations

import json
import logging
from dataclasses import dataclass, field
from pathlib import Path
from typing import Any, Optional, Sequence

import click

from .context_snapshot_policy import check_snapshot_policy
from .contract_check import check_prompt
from .coverage_contracts import (
    STATUS_FAILED,
    STATUS_STORY_ONLY,
    STATUS_UNCHECKED,
    CoverageResult,
    build_coverage,
)
from .construct_paths import _strip_language_suffix
from .gate_main import GateResult, run_gate_policy
from .prompt_lint import LintResult, scan_prompt
from .source_set_model import resolve_prompt_targets
from .user_story_tests import _resolve_stories_dir

logger = logging.getLogger(__name__)

REPORT_SCHEMA = "pdd.prompt_source_set_report.v1"


_CLARIFICATION_CODE_MARKERS = (
    "VAGUE",
    "DUPLICATE_ID",
    "STORY_ONLY_AMBIGUOUS",
    "UNKNOWN",
    "MALFORMED",
    "AMBIGUOUS",
    "WAIVER_NOT_ALLOWED",
)


def _finding_requires_clarification(code: str, source_check: str = "") -> bool:
    """Return whether a finding must be routed through human clarification."""
    upper = code.upper()
    if source_check == "gate" and "WAIVER" in upper:
        return True
    return any(marker in upper for marker in _CLARIFICATION_CODE_MARKERS)


def _clarification_reason_for(
    *,
    code: str,
    source_check: str,
    rule_id: str = "",
    message: str = "",
) -> str:
    """Derive a compact deterministic reason for a clarification-required finding."""
    upper = code.upper()
    rule_suffix = f" ({rule_id})" if rule_id else ""
    if "VAGUE" in upper:
        return "Term is undefined and may be interpreted inconsistently."
    if "DUPLICATE_ID" in upper:
        return f"Duplicate IDs require choosing the intended canonical contract{rule_suffix}."
    if "STORY_ONLY_AMBIGUOUS" in upper:
        return f"Coverage cannot be assigned deterministically to one story{rule_suffix}."
    if source_check == "gate" or "WAIVER" in upper:
        return f"Policy intent is unclear and requires human decision{rule_suffix}."
    if any(marker in upper for marker in ("UNKNOWN", "MALFORMED", "AMBIGUOUS")):
        return f"Ambiguous source-set metadata requires human decision{rule_suffix}."
    if message:
        return "Finding requires human clarification before automated repair."
    return ""


@dataclass
class SourceSetFinding:
    """One deterministic finding in the unified prompt source-set report."""

    finding_id: str
    source_check: str
    severity: str
    file: Path
    line: str = ""
    message: str = ""
    evidence: str = ""
    recommended_action: str = ""
    fix_command: str = ""
    code: str = ""
    rule_id: str = ""
    # Repair hints consumed by the non-interactive repair orchestrator (#1422).
    requires_clarification: bool = False
    clarification_reason: str = ""
    confidence: Optional[float] = None

    def __post_init__(self) -> None:
        if not self.requires_clarification and _finding_requires_clarification(
            self.code,
            self.source_check,
        ):
            self.requires_clarification = True
        if self.requires_clarification and not self.clarification_reason:
            self.clarification_reason = _clarification_reason_for(
                code=self.code,
                source_check=self.source_check,
                rule_id=self.rule_id,
                message=self.message,
            )

    @property
    def is_error(self) -> bool:
        return self.severity == "error"

    def as_dict(self) -> dict[str, Any]:
        payload: dict[str, Any] = {
            "id": self.finding_id,
            "source_check": self.source_check,
            "severity": self.severity,
            "file": str(self.file),
            "line": self.line,
            "message": self.message,
            "evidence": self.evidence,
            "recommended_action": self.recommended_action,
            "fix_command": self.fix_command,
            "code": self.code,
            "rule_id": self.rule_id,
            "requires_clarification": self.requires_clarification,
            "clarification_reason": self.clarification_reason,
        }
        if self.confidence is not None:
            payload["confidence"] = self.confidence
        return payload


@dataclass
class PromptSourceSetReport:
    """Structured aggregate of all source-set checks for one prompt."""

    prompt_path: Path
    project_root: Path
    target: str
    findings: list[SourceSetFinding] = field(default_factory=list)
    coverage: Optional[CoverageResult] = None
    gate: Optional[GateResult] = None
    lint: Optional[LintResult] = None
    contract_passed: bool = True
    checks: list[dict[str, Any]] = field(default_factory=list)

    @property
    def error_count(self) -> int:
        return sum(1 for finding in self.findings if finding.is_error)

    @property
    def warn_count(self) -> int:
        return sum(1 for finding in self.findings if finding.severity == "warn")

    @property
    def passed(self) -> bool:
        if self.coverage and self.coverage.error:
            return False
        if self.gate and not self.gate.passed:
            return False
        if not self.contract_passed:
            return False
        return self.error_count == 0

    @property
    def status(self) -> str:
        if not self.passed:
            return "fail"
        if self.warn_count:
            return "warn"
        return "pass"

    def recommended_actions(self) -> list[str]:
        actions: list[str] = []

        def _display_path(path: Path) -> str:
            try:
                return str(path.relative_to(self.project_root))
            except ValueError:
                return str(path)

        if self.lint and self.lint.error_count:
            actions.append(f"pdd checkup lint {_display_path(self.prompt_path)}")
        if not self.contract_passed:
            actions.append(
                f"pdd checkup contract check {_display_path(self.prompt_path)}"
            )
        if self.coverage and self.coverage.has_contract_rules:
            summary = self.coverage.summary
            if summary.get("unchecked") or summary.get("failed"):
                actions.append(
                    f"pdd checkup coverage {_display_path(self.prompt_path)}"
                )
        if self.gate and not self.gate.passed:
            actions.append(
                f"pdd checkup gate {_strip_language_suffix(self.prompt_path)}"
            )
        if any(finding.source_check == "snapshot" for finding in self.findings):
            actions.append(f"pdd checkup snapshot {_display_path(self.prompt_path)}")
        if any(finding.source_check == "drift" for finding in self.findings):
            basename = _strip_language_suffix(self.prompt_path)
            actions.append(f"pdd checkup drift {basename}")
        if not actions:
            actions.append("Source set looks ready to generate from.")
        return actions

    def deterministic_exit_code(self, *, strict: bool = False) -> int:
        if self.error_count or (strict and self.warn_count):
            return 2
        return 1 if self.warn_count else 0

    def as_dict(self, *, strict: bool = False) -> dict[str, Any]:
        return {
            "schema": REPORT_SCHEMA,
            "status": self.status,
            "target": self.target,
            "prompt": str(self.prompt_path),
            "checks": self.checks,
            "findings": [finding.as_dict() for finding in self.findings],
            "actions": self.recommended_actions(),
            "deterministic_exit_code": self.deterministic_exit_code(strict=strict),
        }


def _finding_id(engine: str, path: Path, index: int, code: str = "") -> str:
    slug = path.stem.replace(".", "_")
    suffix = code or "issue"
    return f"{engine}:{slug}:{index}:{suffix}"


def _record_check(
    report: PromptSourceSetReport,
    name: str,
    *,
    status: str,
    reason: str = "",
) -> None:
    """Append one check result. ``reason`` explains skip/note statuses for humans."""
    entry: dict[str, Any] = {"name": name, "status": status}
    if reason:
        entry["reason"] = reason
    report.checks.append(entry)


def build_prompt_source_set_report(
    prompt_path: Path,
    *,
    target: str,
    project_root: Optional[Path] = None,
    strict: bool = False,
    stories_dir: Optional[Path] = None,
    tests_dir: Optional[Path] = None,
) -> PromptSourceSetReport:
    """Run deterministic engines and collect a unified source-set report."""
    root = (project_root or Path.cwd()).resolve()
    prompt_path = prompt_path.resolve()
    # Anchor coverage/gate source-set dirs to the resolved project root so that
    # `pdd checkup` invoked from outside the project still finds the right paths.
    # PDD_USER_STORIES_DIR is honoured via _resolve_stories_dir for consistency.
    if stories_dir is None:
        stories_dir = _resolve_stories_dir(root=root)
    if tests_dir is None:
        tests_dir = root / "tests"
    report = PromptSourceSetReport(
        prompt_path=prompt_path,
        project_root=root,
        target=target,
    )

    lint_result = scan_prompt(prompt_path, strict=strict)
    report.lint = lint_result
    lint_status = "pass" if lint_result.error_count == 0 else "fail"
    if lint_result.error_count == 0 and lint_result.warn_count:
        lint_status = "warn"
    _record_check(report, "lint", status=lint_status)
    for index, issue in enumerate(lint_result.issues):
        report.findings.append(
            SourceSetFinding(
                finding_id=_finding_id("lint", prompt_path, index, issue.code or "lint"),
                source_check="lint",
                severity=issue.level,
                file=prompt_path,
                line=issue.line,
                message=issue.message,
                evidence=issue.section,
                recommended_action="Define the term in <vocabulary> or rewrite with observable criteria.",
                fix_command=f"pdd checkup lint {prompt_path}",
                code=issue.code,
            )
        )

    contract_result = check_prompt(prompt_path, strict=strict)
    report.contract_passed = contract_result.error_count == 0
    contract_status = "pass" if report.contract_passed else "fail"
    if report.contract_passed and contract_result.warn_count:
        contract_status = "warn"
    _record_check(report, "contract", status=contract_status)
    for index, issue in enumerate(contract_result.issues):
        report.findings.append(
            SourceSetFinding(
                finding_id=_finding_id(
                    "contract", prompt_path, index, issue.code or "contract"
                ),
                source_check="contract",
                severity=issue.level,
                file=prompt_path,
                line=issue.line,
                message=issue.message,
                evidence=issue.section,
                recommended_action=issue.suggestion or "Fix the contract section defect.",
                fix_command=f"pdd checkup contract check {prompt_path}",
                code=issue.code,
                rule_id=issue.rule_id,
            )
        )

    report.coverage = build_coverage(
        prompt_path,
        stories_dir=stories_dir,
        tests_dir=tests_dir,
    )
    waiver_issues = [
        issue for issue in contract_result.issues if issue.section == "waivers"
    ]
    if waiver_issues:
        waiver_status = (
            "fail"
            if any(issue.level == "error" for issue in waiver_issues)
            else "warn"
        )
        _record_check(report, "waivers", status=waiver_status)
    elif report.coverage.has_contract_rules:
        _record_check(report, "waivers", status="pass")
    else:
        _record_check(report, "waivers", status="skip")
    if report.coverage.error:
        _record_check(report, "coverage", status="fail")
        report.findings.append(
            SourceSetFinding(
                finding_id=_finding_id("coverage", prompt_path, 0, "error"),
                source_check="coverage",
                severity="error",
                file=prompt_path,
                message=report.coverage.error,
                recommended_action="Fix coverage analysis inputs.",
                fix_command=f"pdd checkup coverage {prompt_path}",
                code="coverage_error",
            )
        )
    elif not report.coverage.has_contract_rules:
        _record_check(
            report,
            "coverage",
            status="skip",
            reason="no <contract_rules> to cover",
        )
    else:
        coverage_status = "pass"
        for index, rule in enumerate(report.coverage.rules):
            if rule.status in {STATUS_UNCHECKED, STATUS_FAILED}:
                level = "error" if rule.status == STATUS_FAILED else "warn"
                if level == "error":
                    coverage_status = "fail"
                elif coverage_status == "pass":
                    coverage_status = "warn"
                message = (
                    f"Rule {rule.rule_id}: {rule.status}"
                    + (f" — {', '.join(rule.failures)}" if rule.failures else "")
                )
                report.findings.append(
                    SourceSetFinding(
                        finding_id=_finding_id(
                            "coverage", prompt_path, index, rule.rule_id
                        ),
                        source_check="coverage",
                        severity=level,
                        file=prompt_path,
                        message=message,
                        recommended_action="Add story/test coverage or a waiver.",
                        fix_command=f"pdd checkup coverage {prompt_path}",
                        code=rule.status,
                        rule_id=rule.rule_id,
                    )
                )
            elif rule.status == STATUS_STORY_ONLY and len(rule.stories) > 1:
                if coverage_status == "pass":
                    coverage_status = "warn"
                report.findings.append(
                    SourceSetFinding(
                        finding_id=_finding_id(
                            "coverage", prompt_path, index, "story_only_ambiguous"
                        ),
                        source_check="coverage",
                        severity="warn",
                        file=prompt_path,
                        message=(
                            f"Rule {rule.rule_id}: story-only coverage matched "
                            f"{len(rule.stories)} stories"
                        ),
                        evidence=", ".join(rule.stories),
                        recommended_action=(
                            "Clarify which story is canonical or add deterministic test coverage."
                        ),
                        fix_command=f"pdd checkup coverage {prompt_path}",
                        code="story_only_ambiguous",
                        rule_id=rule.rule_id,
                    )
                )
        _record_check(report, "coverage", status=coverage_status)

    basename = _strip_language_suffix(prompt_path)

    from .evidence_store import devunits_dir, resolve_prompt_path

    latest_manifest = devunits_dir(root) / f"{basename}.latest.json"
    resolved_prompt = resolve_prompt_path(root, basename)
    prompt_matches_devunit = (
        resolved_prompt is not None
        and resolved_prompt.resolve() == prompt_path.resolve()
    )

    if latest_manifest.is_file():
        try:
            report.gate = run_gate_policy(
                root,
                target=basename,
                stories_dir=stories_dir,
                tests_dir=tests_dir,
            )
        except (ValueError, OSError) as exc:
            logger.warning("Gate policy check failed for %s: %s", basename, exc)
            _record_check(report, "gate", status="fail")
            report.findings.append(
                SourceSetFinding(
                    finding_id=_finding_id("gate", prompt_path, 0, "gate_error"),
                    source_check="gate",
                    severity="error",
                    file=prompt_path,
                    message=f"Gate check failed (manifest may be corrupt): {exc}",
                    recommended_action="Re-capture evidence or delete the corrupt manifest.",
                    fix_command=f"pdd --evidence generate {basename}",
                    code="gate_error",
                )
            )
            report.gate = None
        if report.gate is not None:
            gate_status = "pass" if report.gate.passed else "fail"
            _record_check(report, "gate", status=gate_status)
        for index, failure in enumerate((report.gate.failures if report.gate else [])):
            severity = "error"
            report.findings.append(
                SourceSetFinding(
                    finding_id=_finding_id("gate", prompt_path, index, failure.code),
                    source_check="gate",
                    severity=severity,
                    file=prompt_path,
                    message=failure.message,
                    recommended_action="Resolve evidence or waiver policy failures.",
                    fix_command=failure.fix_command or f"pdd checkup gate {basename}",
                    code=failure.code,
                )
            )
        _record_check(report, "drift", status="note")
        report.findings.append(
            SourceSetFinding(
                finding_id=_finding_id("drift", prompt_path, 0, "readiness"),
                source_check="drift",
                severity="info",
                file=prompt_path,
                message=(
                    f"Evidence manifest present for {basename}; consider "
                    f"`pdd checkup drift {basename}` before shipping regenerated code."
                ),
                recommended_action="Run drift check when evidence-backed regeneration matters.",
                fix_command=f"pdd checkup drift {basename}",
                code="drift_readiness",
            )
        )
    elif prompt_matches_devunit:
        _record_check(report, "gate", status="warn")
        report.findings.append(
            SourceSetFinding(
                finding_id=_finding_id("gate", prompt_path, 0, "missing_evidence"),
                source_check="gate",
                severity="warn",
                file=prompt_path,
                message=f"No evidence manifest for dev unit {basename}",
                recommended_action="Capture evidence before shipping generated code.",
                fix_command=f"pdd --evidence generate {basename}",
                code="missing_evidence",
            )
        )
        _record_check(
            report,
            "drift",
            status="skip",
            reason="no baseline evidence snapshot to compare",
        )
    else:
        _record_check(
            report,
            "gate",
            status="skip",
            reason="no evidence manifest; not a tracked dev unit",
        )
        _record_check(
            report,
            "drift",
            status="skip",
            reason="no baseline evidence snapshot to compare",
        )

    snapshot_passed, snapshot_message = check_snapshot_policy(prompt_path, root)
    if snapshot_passed:
        _record_check(report, "snapshot", status="pass")
    else:
        _record_check(report, "snapshot", status="fail")
        report.findings.append(
            SourceSetFinding(
                finding_id=_finding_id("snapshot", prompt_path, 0, "snapshot_policy"),
                source_check="snapshot",
                severity="error",
                file=prompt_path,
                message=snapshot_message,
                recommended_action="Capture replayable snapshot evidence.",
                fix_command=f"pdd checkup snapshot {prompt_path}",
                code="snapshot_policy",
            )
        )

    return report


def render_prompt_source_set_report(
    report: PromptSourceSetReport,
    *,
    quiet: bool = False,
) -> None:
    """Print a human-readable unified report."""
    if quiet:
        return

    click.echo(f"Prompt: {report.prompt_path}")
    click.echo(f"Status: {report.status.upper()}")
    click.echo(
        f"Findings: {report.error_count} error(s), {report.warn_count} warning(s)"
    )

    if not report.findings:
        click.echo("No findings.")
    else:
        for finding in report.findings:
            click.echo(
                f"  [{finding.severity}] {finding.source_check}: {finding.message}"
            )

    click.echo("\nNext:")
    for action in report.recommended_actions():
        click.echo(f"  - {action}")


def render_automatic_gate_summary(
    reports: Sequence[PromptSourceSetReport],
    *,
    mode: str,
    quiet: bool = False,
) -> None:
    """Print the concise automatic-gate output format from issue #1420."""
    if quiet:
        return

    blocking = [report for report in reports if not report.passed or report.warn_count]
    if not blocking:
        click.echo("Prompt checkup: pass")
        return

    click.echo("Prompt checkup: needs attention\n")
    index = 1
    for report in blocking:
        for finding in report.findings:
            if finding.severity in {"error", "warn"}:
                click.echo(f"{index}. {finding.message}")
                index += 1

    sample = blocking[0].prompt_path
    click.echo("\nNext:")
    click.echo(f"- pdd checkup {sample}")
    if mode == "warn":
        click.echo("- Or continue with --prompt-checkup warn")


def _deterministic_exit_code(
    reports: Sequence[PromptSourceSetReport],
    *,
    strict: bool,
) -> int:
    return max((report.deterministic_exit_code(strict=strict) for report in reports), default=0)


def run_checkup_prompt(  # pylint: disable=too-many-arguments,too-many-locals
    target: str,
    *,
    explain: bool = False,
    as_json: bool = False,
    quiet: bool = False,
    strict: bool = False,
    project_root: Optional[Path] = None,
) -> tuple[bool, str, float, str, int]:
    """Run the unified prompt source-set report for a prompt-shaped target."""
    root = (project_root or Path.cwd()).resolve()
    prompt_paths = resolve_prompt_targets(target, project_root=root)
    reports = [
        build_prompt_source_set_report(
            prompt_path,
            target=target,
            project_root=root,
            strict=strict,
        )
        for prompt_path in prompt_paths
    ]
    exit_code = _deterministic_exit_code(reports, strict=strict)
    stage1_pass = exit_code == 0

    if not as_json:
        for report in reports:
            render_prompt_source_set_report(report, quiet=quiet)
            if len(reports) > 1 and not quiet:
                click.echo("")

    if explain and not quiet and not as_json:
        click.echo("\n[explain] Deterministic findings (read-only, non-fatal):")
        if not any(report.findings for report in reports):
            click.echo("  No findings to explain.")
        for report in reports:
            for finding in report.findings:
                click.echo(
                    f"  [{finding.finding_id}] {finding.source_check}: {finding.message}"
                )

    if as_json:
        payload: dict[str, Any] = {
            "schema": REPORT_SCHEMA,
            "target": target,
            "status": "pass" if stage1_pass else ("warn" if exit_code == 1 else "fail"),
            "reports": [report.as_dict(strict=strict) for report in reports],
            "deterministic_exit_code": exit_code,
        }
        click.echo(json.dumps(payload, indent=2, sort_keys=True))

    names = ", ".join(item.prompt_path.name for item in reports)
    summary = "PASS" if stage1_pass else "FAIL"
    total_errors = sum(item.error_count for item in reports)
    total_warnings = sum(item.warn_count for item in reports)
    message = (
        f"Prompt source-set check {summary} for {names} "
        f"({total_errors} error(s), {total_warnings} warning(s))."
    )
    return stage1_pass, message, 0.0, "", exit_code


def run_checkup_prompt_paths(
    prompt_paths: Sequence[Path],
    *,
    target: str = "",
    project_root: Optional[Path] = None,
    strict: bool = False,
) -> tuple[list[PromptSourceSetReport], int]:
    """Build reports for explicit prompt paths (automatic gate hook)."""
    root = (project_root or Path.cwd()).resolve()
    reports = [
        build_prompt_source_set_report(
            prompt_path,
            target=target or str(prompt_path),
            project_root=root,
            strict=strict,
        )
        for prompt_path in prompt_paths
    ]
    return reports, _deterministic_exit_code(reports, strict=strict)
