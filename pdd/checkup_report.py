"""Human-facing helpers for the agentic ``pdd checkup`` UX.

This module is deliberately free of Click / I/O side effects except the explicit
``write_artifacts`` entry point, so the accounting, grouping, and risk logic can
be unit-tested directly.

Concepts
--------
* **repair risk** — ``low`` fixes are mechanical and safe to auto-apply; ``medium``
  fixes need human judgement (e.g. defining a vague term) and are saved for
  review; ``high`` fixes touch evidence/contracts and are left as manual TODOs.
* **finding groups** — repeated findings with the same ``(source_check, code)``
  collapse into one group so the user answers one prompt, not ten.
* **accounting** — a single source of truth for the final summary numbers.
* **artifacts** — a short Markdown report and a patch preview, written only when
  there is something worth writing.
"""

from __future__ import annotations

from dataclasses import dataclass, field
from pathlib import Path
from typing import Iterable, Optional, Sequence

# ---------------------------------------------------------------------------
# Repair risk
# ---------------------------------------------------------------------------

RISK_LOW = "low"
RISK_MEDIUM = "medium"
RISK_HIGH = "high"


# Checks whose fixes require real artifacts (evidence, stories, snapshots) rather
# than a mechanical prompt edit. Their repairs are never auto-applied.
_EVIDENCE_CHECKS = frozenset({"coverage", "gate", "snapshot", "drift"})


def repair_risk_for(finding) -> str:
    """Classify how safe it is to auto-apply a repair for ``finding``.

    * ``error``-severity findings touch contracts/evidence → ``high`` (manual).
    * ``requires_clarification`` findings (vague terms, ambiguous rules) need a
      human to supply meaning — never fabricate it → ``medium`` (save for review).
    * coverage/gate/snapshot/drift findings need real artifacts, not a prompt
      edit → ``medium`` (save for review).
    * everything else is a mechanical, low-risk fix.
    """
    if finding is None:
        return RISK_LOW
    if getattr(finding, "severity", "") == "error":
        return RISK_HIGH
    if getattr(finding, "requires_clarification", False):
        return RISK_MEDIUM
    if getattr(finding, "source_check", "") in _EVIDENCE_CHECKS:
        return RISK_MEDIUM
    return RISK_LOW


# ---------------------------------------------------------------------------
# Finding groups
# ---------------------------------------------------------------------------


@dataclass
class FindingGroup:
    """One or more findings sharing the same ``(source_check, code)``."""

    source_check: str
    code: str
    findings: list = field(default_factory=list)

    @property
    def size(self) -> int:
        return len(self.findings)

    @property
    def is_grouped(self) -> bool:
        return self.size > 1

    @property
    def risk(self) -> str:
        return repair_risk_for(self.findings[0]) if self.findings else RISK_LOW

    @property
    def section(self) -> str:
        """The prompt section the findings live in (best-effort, from evidence)."""
        for f in self.findings:
            sect = getattr(f, "evidence", "") or ""
            if sect:
                return sect
        return ""

    @property
    def recommended_action(self) -> str:
        return getattr(self.findings[0], "recommended_action", "") if self.findings else ""

    def terms(self) -> list[str]:
        """Quoted terms extracted from finding messages, when present."""
        out: list[str] = []
        for f in self.findings:
            msg = getattr(f, "message", "") or ""
            term = _extract_quoted(msg)
            if term:
                out.append(term)
        return out


def group_findings(findings: Iterable) -> list[FindingGroup]:
    """Group findings by ``(source_check, code)`` preserving first-seen order."""
    order: list[tuple[str, str]] = []
    buckets: dict[tuple[str, str], FindingGroup] = {}
    for f in findings:
        key = (getattr(f, "source_check", ""), getattr(f, "code", ""))
        if key not in buckets:
            buckets[key] = FindingGroup(source_check=key[0], code=key[1])
            order.append(key)
        buckets[key].findings.append(f)
    return [buckets[k] for k in order]


def _extract_quoted(text: str) -> str:
    for quote in ('"', "'", "`", "“"):
        if quote in text:
            start = text.index(quote)
            rest = text[start + 1 :]
            for endq in ('"', "'", "`", "”"):
                if endq in rest:
                    return rest[: rest.index(endq)]
    return ""


# ---------------------------------------------------------------------------
# Human wording
# ---------------------------------------------------------------------------


def humanize_group_summary(group: FindingGroup) -> list[str]:
    """Concise, human-readable summary lines for a finding group."""
    lines: list[str] = []
    section = f" in {group.section}" if group.section else ""
    if group.code == "VAGUE_TERM_UNDEFINED" and group.is_grouped:
        terms = group.terms()
        lines.append(
            f"Found {group.size} undefined vague terms{section}:"
        )
        lines.append("")
        lines.append("  " + _wrap_terms(terms))
        lines.append("")
        lines.append("These terms can make generated code or tests interpret the")
        lines.append("prompt inconsistently.")
        lines.append("")
        lines.append("Recommended fix:")
        lines.append("  Add a <vocabulary> block with observable definitions.")
    elif group.is_grouped:
        lines.append(f"Found {group.size} {group.code} findings{section}.")
        if group.recommended_action:
            lines.append(f"Recommended fix: {group.recommended_action}")
    else:
        f = group.findings[0]
        lines.append(humanize_finding(f))
    return lines


def humanize_finding(finding) -> str:
    """One-line human wording for a single finding."""
    term = _extract_quoted(getattr(finding, "message", "") or "")
    section = getattr(finding, "evidence", "") or ""
    if getattr(finding, "code", "") == "VAGUE_TERM_UNDEFINED" and term:
        loc = f" in {section}" if section else ""
        return f'"{term}" is used{loc} but not defined in <vocabulary>.'
    return getattr(finding, "message", "") or getattr(finding, "code", "finding")


def _wrap_terms(terms: Sequence[str], per_line: int = 5) -> str:
    rows = []
    for i in range(0, len(terms), per_line):
        rows.append(", ".join(terms[i : i + per_line]))
    return ("," + "\n  ").join(rows) if len(rows) > 1 else (rows[0] if rows else "")


# ---------------------------------------------------------------------------
# Accounting
# ---------------------------------------------------------------------------


def decision_for(status: str, *, strict: bool, blocking: bool) -> tuple[str, bool]:
    """Map a checkup result to a lifecycle decision.

    Returns ``(text, can_continue)`` where ``text`` is shown after ``Decision:``
    and ``can_continue`` is False only when the workflow must block (so the next
    PDD step — code generation / modification — should not proceed).
    """
    if blocking:
        reason = "strict failure" if strict else "blocking findings"
        return f"{reason} → block", False
    if status == "warn":
        return "warn → continue with review note", True
    if status == "fail":
        return "fail → continue with review note", True
    return "pass → continue", True


@dataclass
class CheckupAccounting:
    """Single source of truth for the final-summary numbers."""

    total: int = 0
    fixed_manually: int = 0
    fixed_automatically: int = 0
    skipped_by_user: int = 0
    saved_for_review: int = 0
    manual_todo: int = 0
    patches_applied: int = 0
    patches_queued: int = 0
    patches_failed: int = 0

    @property
    def remaining(self) -> int:
        done = self.fixed_manually + self.fixed_automatically + self.skipped_by_user
        return max(0, self.total - done)

    def summary_lines(
        self,
        status: str,
        artifacts: Optional[dict] = None,
        decision: Optional[str] = None,
    ) -> list[str]:
        applied_mode = self.patches_applied > 0
        lines = [f"Checkup complete: {status}", ""]
        lines.append("Findings:")
        lines.append(f"  Total: {self.total}")
        lines.append(f"  Fixed manually: {self.fixed_manually}")
        lines.append(f"  Fixed automatically: {self.fixed_automatically}")
        lines.append(f"  Skipped by user: {self.skipped_by_user}")
        lines.append(f"  Remaining: {self.remaining}")
        lines.append("")
        lines.append("Patches:")
        lines.append(f"  Applied: {self.patches_applied}")
        lines.append(f"  Queued: {self.patches_queued}")
        if applied_mode:
            lines.append(f"  Failed: {self.patches_failed}")
        else:
            lines.append(f"  Saved for review: {self.saved_for_review}")
        if artifacts:
            lines.append("")
            lines.append("Artifacts:")
            if artifacts.get("patch"):
                lines.append(f"  Patch preview: {artifacts['patch']}")
            if artifacts.get("report"):
                lines.append(f"  Report: {artifacts['report']}")
        if decision:
            lines.append("")
            lines.append("Decision:")
            lines.append(f"  {decision}")
        return lines


# ---------------------------------------------------------------------------
# Artifacts
# ---------------------------------------------------------------------------


def artifact_dir(project_root: Path) -> Path:
    return Path(project_root) / ".pdd" / "checkup"


def render_report_markdown(
    *,
    target: str,
    status: str,
    tool_results: Sequence,
    groups: Sequence[FindingGroup],
    accounting: CheckupAccounting,
    applied: bool,
) -> str:
    lines: list[str] = []
    lines.append(f"# Checkup report — `{target}`")
    lines.append("")
    lines.append(f"**Overall status:** {status}")
    lines.append("")
    lines.append("## Checks")
    lines.append("")
    lines.append("| Tool | Status | Notes |")
    lines.append("|------|--------|-------|")
    for tr in tool_results:
        note = tr.skip_reason if tr.status == "skip" else ""
        n = len(tr.findings)
        if note == "" and n:
            note = f"{n} finding(s)"
        lines.append(f"| {tr.check_name} | {tr.status} | {note} |")
    lines.append("")
    if groups:
        lines.append("## Findings")
        lines.append("")
        for g in groups:
            risk = g.risk
            lines.append(f"### {g.source_check}: {g.code} ({g.size}, risk: {risk})")
            lines.append("")
            for line in humanize_group_summary(g):
                lines.append(line)
            lines.append("")
            lines.append("Finding IDs:")
            for f in g.findings:
                lines.append(f"- `{f.finding_id}`")
            lines.append("")
    lines.append("## Summary")
    lines.append("")
    for line in accounting.summary_lines(status):
        lines.append(line)
    lines.append("")
    verb = "applied to the prompt" if applied else "saved for review (not applied)"
    lines.append(f"_Patches were {verb}._")
    lines.append("")
    return "\n".join(lines)


def render_patch_preview(patches: Sequence, *, target: str) -> str:
    lines: list[str] = []
    lines.append(f"# Patch preview — {target}")
    lines.append("# Generated by `pdd checkup`. Review before applying.")
    lines.append("")
    if not patches:
        lines.append("# (no patches proposed)")
        return "\n".join(lines) + "\n"
    for i, p in enumerate(patches, 1):
        lines.append(f"## Patch {i}: {getattr(p, 'finding_id', '')}")
        lines.append(f"# kind: {getattr(p, 'kind', '')}")
        lines.append(f"# target: {getattr(p, 'target', '')}")
        anchor = getattr(p, "anchor", {}) or {}
        if anchor:
            lines.append(f"# anchor: {anchor}")
        lines.append("# replacement:")
        for rline in str(getattr(p, "replacement", "")).splitlines() or [""]:
            lines.append(f"  {rline}")
        lines.append("")
    return "\n".join(lines) + "\n"


def write_artifacts(
    *,
    project_root: Path,
    prompt_path: Path,
    target: str,
    status: str,
    tool_results: Sequence,
    groups: Sequence[FindingGroup],
    accounting: CheckupAccounting,
    patches: Sequence,
    applied: bool,
) -> dict:
    """Write a report and (when patches exist) a patch preview.

    Returns ``{"report": Path, "patch": Path|None}``. Writes nothing and returns
    an empty dict when there are no findings (a clean pass needs no artifacts).
    """
    if not groups and not patches:
        return {}
    out_dir = artifact_dir(project_root)
    out_dir.mkdir(parents=True, exist_ok=True)
    stem = Path(prompt_path).stem

    report_path = out_dir / f"{stem}.report.md"
    report_path.write_text(
        render_report_markdown(
            target=target,
            status=status,
            tool_results=tool_results,
            groups=groups,
            accounting=accounting,
            applied=applied,
        ),
        encoding="utf-8",
    )
    artifacts: dict = {"report": report_path}

    if patches:
        patch_path = out_dir / f"{stem}.patch"
        patch_path.write_text(
            render_patch_preview(patches, target=target), encoding="utf-8"
        )
        artifacts["patch"] = patch_path
    return artifacts


# ---------------------------------------------------------------------------
# Plan display
# ---------------------------------------------------------------------------


def compact_plan_line(tools: Sequence[str]) -> str:
    return "Plan:\n  " + ", ".join(tools)


def descriptive_plan_lines(tools: Sequence[str], descriptions: dict) -> list[str]:
    lines = ["Plan:"]
    width = max((len(t) for t in tools), default=0)
    for t in tools:
        desc = descriptions.get(t, "")
        lines.append(f"  {t.ljust(width)}  — {desc}" if desc else f"  {t}")
    return lines
