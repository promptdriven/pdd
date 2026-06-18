"""Tool wrappers for individual checkup engines used by ``CheckupAgent``."""

from __future__ import annotations

from dataclasses import dataclass
from typing import Optional, Protocol

from .checkup_prompt_main import PromptSourceSetReport, SourceSetFinding

ALL_TOOL_NAMES = ("lint", "contract", "coverage", "gate", "snapshot", "drift")


# Fallback skip reasons keyed by tool name, used when the report did not record
# an explicit reason (e.g. a tool that is absent from ``report.checks`` and so
# defaults to "skip").  Kept structural — not demo-specific copy.
_DEFAULT_SKIP_REASONS: dict[str, str] = {
    "lint": "no prompt body to scan",
    "contract": "no <contract> or <contract_rules> section",
    "coverage": "no <contract_rules> to cover",
    "gate": "no evidence manifest; not a tracked dev unit",
    "snapshot": "no nondeterministic context declared",
    "drift": "no baseline evidence snapshot to compare",
}


@dataclass
class ToolResult:
    """Result of running one checkup tool against a report."""

    check_name: str
    status: str  # "pass", "fail", "warn", "skip", "note", "error"
    findings: list[SourceSetFinding]
    skip_reason: str = ""  # populated only when status == "skip"

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


def _check_entry(report: PromptSourceSetReport, check_name: str) -> Optional[dict]:
    for entry in report.checks:
        if entry.get("name") == check_name:
            return entry
    return None


def _status_for(report: PromptSourceSetReport, check_name: str) -> str:
    entry = _check_entry(report, check_name)
    return entry.get("status", "skip") if entry is not None else "skip"


def _reason_for(report: PromptSourceSetReport, check_name: str, status: str) -> str:
    """Return a human skip reason: the report's recorded reason, or a default."""
    if status != "skip":
        return ""
    entry = _check_entry(report, check_name)
    if entry is not None and entry.get("reason"):
        return entry["reason"]
    return _DEFAULT_SKIP_REASONS.get(check_name, "")


def _findings_for(report: PromptSourceSetReport, source_check: str) -> list[SourceSetFinding]:
    return [f for f in report.findings if f.source_check == source_check]


class _BaseTool:
    """Shared ``extract`` that reads status, findings, and skip reason."""

    name: str = ""
    description: str = ""

    def extract(self, report: PromptSourceSetReport) -> ToolResult:
        status = _status_for(report, self.name)
        return ToolResult(
            check_name=self.name,
            status=status,
            findings=_findings_for(report, self.name),
            skip_reason=_reason_for(report, self.name, status),
        )


class LintTool(_BaseTool):
    name = "lint"
    description = "prompt hygiene and vague terms"


class ContractTool(_BaseTool):
    name = "contract"
    description = "input/output contract consistency"


class CoverageTool(_BaseTool):
    name = "coverage"
    description = "requirement/example coverage"


class GateTool(_BaseTool):
    name = "gate"
    description = "configured blocking policy"


class SnapshotTool(_BaseTool):
    name = "snapshot"
    description = "current prompt state"


class DriftTool(_BaseTool):
    name = "drift"
    description = "baseline comparison"


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
