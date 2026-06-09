"""Tool wrappers for individual checkup engines used by ``CheckupAgent``."""

from __future__ import annotations

from dataclasses import dataclass
from typing import Protocol

from .checkup_prompt_main import PromptSourceSetReport, SourceSetFinding

ALL_TOOL_NAMES = ("lint", "contract", "coverage", "gate", "snapshot", "drift")


@dataclass
class ToolResult:
    """Result of running one checkup tool against a report."""

    check_name: str
    status: str  # "pass", "fail", "warn", "skip", "note", "error"
    findings: list[SourceSetFinding]

    @property
    def has_findings(self) -> bool:
        return bool(self.findings)

    @property
    def is_clean(self) -> bool:
        return self.status in ("pass", "skip")


class CheckupTool(Protocol):
    """Protocol for a single checkup engine tool."""

    name: str
    description: str

    def extract(self, report: PromptSourceSetReport) -> ToolResult:
        """Extract this tool's result from a pre-computed report."""
        ...


def _status_for(report: PromptSourceSetReport, check_name: str) -> str:
    for entry in report.checks:
        if entry.get("name") == check_name:
            return entry.get("status", "skip")
    return "skip"


def _findings_for(report: PromptSourceSetReport, source_check: str) -> list[SourceSetFinding]:
    return [f for f in report.findings if f.source_check == source_check]


class LintTool:
    name = "lint"
    description = "Scan prompts for vague language, ambiguous requirements, and quality issues."

    def extract(self, report: PromptSourceSetReport) -> ToolResult:
        return ToolResult(
            check_name=self.name,
            status=_status_for(report, "lint"),
            findings=_findings_for(report, "lint"),
        )


class ContractTool:
    name = "contract"
    description = "Verify contract rules are well-formed, unambiguous, and testable."

    def extract(self, report: PromptSourceSetReport) -> ToolResult:
        return ToolResult(
            check_name=self.name,
            status=_status_for(report, "contract"),
            findings=_findings_for(report, "contract"),
        )


class CoverageTool:
    name = "coverage"
    description = "Check that user stories are covered by contract rules."

    def extract(self, report: PromptSourceSetReport) -> ToolResult:
        return ToolResult(
            check_name=self.name,
            status=_status_for(report, "coverage"),
            findings=_findings_for(report, "coverage"),
        )


class GateTool:
    name = "gate"
    description = "Verify evidence manifests and waiver policy are satisfied."

    def extract(self, report: PromptSourceSetReport) -> ToolResult:
        return ToolResult(
            check_name=self.name,
            status=_status_for(report, "gate"),
            findings=_findings_for(report, "gate"),
        )


class SnapshotTool:
    name = "snapshot"
    description = "Ensure nondeterministic prompt context has a replayable snapshot."

    def extract(self, report: PromptSourceSetReport) -> ToolResult:
        return ToolResult(
            check_name=self.name,
            status=_status_for(report, "snapshot"),
            findings=_findings_for(report, "snapshot"),
        )


class DriftTool:
    name = "drift"
    description = "Detect regeneration drift between the prompt and its generated output."

    def extract(self, report: PromptSourceSetReport) -> ToolResult:
        return ToolResult(
            check_name=self.name,
            status=_status_for(report, "drift"),
            findings=_findings_for(report, "drift"),
        )


ALL_TOOLS: dict[str, CheckupTool] = {
    t.name: t  # type: ignore[attr-defined]
    for t in [
        LintTool(),
        ContractTool(),
        CoverageTool(),
        GateTool(),
        SnapshotTool(),
        DriftTool(),
    ]
}
