"""Bounded JSON artifact for standalone agentic PR checkup runs."""

from __future__ import annotations

from typing import Any, Dict, Iterable, List, Mapping, Optional, Set

AGENTIC_V1_SCHEMA = "pdd.checkup.agentic.v1"
TEXT_LIMIT = 2000
SUMMARY_LIMIT = 1000
MAX_FINDINGS = 100
MAX_FIX_ATTEMPTS = 50


def build_agentic_v1_artifact(
    *,
    context: Any,
    state: Any,
    final_state: Mapping[str, Any],
) -> Dict[str, Any]:
    """Build the stable ``pdd.checkup.agentic.v1`` JSON payload."""
    findings = _dedupe_findings(_iter_findings(state))[:MAX_FINDINGS]
    no_fix = bool(getattr(state, "agentic_no_fix", False))
    reviewer_status = dict(final_state.get("reviewer_status") or {})
    reviewers = [
        {
            "name": _bounded(role),
            "role": _bounded(role),
            "command": _bounded(
                (getattr(state, "agentic_reviewer_commands", {}) or {}).get(role, "")
            ),
            "status": _reviewer_status(status),
            "finding_count": _count_findings(findings, role),
            "blocking_count": _count_findings(findings, role, blocking_only=True),
        }
        for role, status in reviewer_status.items()
        if status != "fixer"
    ]
    fixes = [] if no_fix else _iter_fixes(final_state.get("fixes") or [])
    decision, reason = _verdict(
        reviewer_status=reviewer_status,
        findings=findings,
        fresh_final_status=str(final_state.get("fresh_final_status") or "missing"),
        stop_reason=str(final_state.get("stop_reason") or ""),
        max_rounds=bool(final_state.get("max_rounds_reached")),
        max_cost=bool(final_state.get("max_cost_reached")),
        max_duration=bool(final_state.get("max_duration_reached")),
    )
    return {
        "schema": AGENTIC_V1_SCHEMA,
        "owner": _bounded(getattr(context, "pr_owner", "")),
        "repo": _bounded(getattr(context, "pr_repo", "")),
        "pr_number": getattr(context, "pr_number", None),
        "head_sha": _bounded(final_state.get("remote_pr_head_sha") or ""),
        "status": _artifact_status(decision, reason),
        "layer1": _layer1(final_state),
        "pr": {
            "url": _bounded(getattr(context, "pr_url", "")),
            "owner": _bounded(getattr(context, "pr_owner", "")),
            "repo": _bounded(getattr(context, "pr_repo", "")),
            "number": getattr(context, "pr_number", None),
            "head_sha": _bounded(final_state.get("remote_pr_head_sha") or ""),
            "reviewed_head_sha": _bounded(final_state.get("reviewed_head_sha") or ""),
            "verified_head_sha": _bounded(final_state.get("verified_head_sha") or ""),
        },
        "issue": {
            "url": _bounded(getattr(context, "issue_url", "")),
            "number": getattr(context, "issue_number", None),
            "has_issue": bool(getattr(context, "has_issue", False)),
            "aligned": final_state.get("issue_aligned"),
        },
        "mode": "nofix" if no_fix else "fix",
        "adversarial_prompt": _bounded(
            getattr(state, "agentic_adversarial_prompt", "") or "",
            limit=SUMMARY_LIMIT,
        ),
        "reviewers": reviewers,
        "findings": findings,
        "fix_attempts": fixes[:MAX_FIX_ATTEMPTS],
        "validation_after_fix": {
            "status": "skipped" if no_fix else _validation_status(final_state),
            "fresh_final_status": _bounded(final_state.get("fresh_final_status") or ""),
            "verification_status_by_round": dict(
                final_state.get("verification_status_by_round") or {}
            ),
        },
        "fresh_final_review": {
            "requested_role": _bounded(
                getattr(state, "agentic_fresh_final_review_role", "") or ""
            ),
            "provider": _bounded(
                getattr(state, "agentic_fresh_final_review_role", "") or ""
            ),
            "status": _bounded(final_state.get("fresh_final_status") or "missing"),
            "finding_count": len(findings),
            "new_context": bool(getattr(state, "agentic_fresh_final_review_role", "")),
        },
        "budget": {
            "max_rounds": getattr(state, "agentic_max_rounds", 0),
            "max_cost": getattr(state, "agentic_max_cost", 0.0),
            "max_minutes": getattr(state, "agentic_max_minutes", 0.0),
            "total_cost": final_state.get("total_cost"),
            "max_rounds_reached": bool(final_state.get("max_rounds_reached")),
            "max_minutes_reached": bool(final_state.get("max_duration_reached")),
            "max_cost_reached": bool(final_state.get("max_cost_reached")),
            "max_duration_reached": bool(final_state.get("max_duration_reached")),
        },
        "verdict": {
            "decision": decision,
            "reason": _bounded(reason, limit=SUMMARY_LIMIT),
        },
        "stop_reason": _bounded(final_state.get("stop_reason") or ""),
    }


def _iter_findings(state: Any) -> List[Dict[str, Any]]:
    raw_findings = getattr(state, "findings", [])
    out: List[Dict[str, Any]] = []
    for finding in raw_findings:
        if hasattr(finding, "to_dict"):
            payload = finding.to_dict()
        elif isinstance(finding, Mapping):
            payload = dict(finding)
        else:
            continue
        out.append(
            {
                "key": _bounded(payload.get("key") or ""),
                "reviewer": _bounded(payload.get("reviewer") or ""),
                "severity": _bounded(payload.get("severity") or ""),
                "blocking": str(payload.get("severity") or "").lower()
                in {"blocker", "critical", "high", "medium"},
                "area": _bounded(payload.get("area") or ""),
                "path": _finding_path(payload.get("location") or ""),
                "line": _finding_line(payload.get("location") or ""),
                "location": _bounded(payload.get("location") or ""),
                "evidence": _bounded(payload.get("evidence") or ""),
                "summary": _bounded(payload.get("finding") or ""),
                "finding": _bounded(payload.get("finding") or ""),
                "suggested_fix": _bounded(payload.get("required_fix") or ""),
                "required_fix": _bounded(payload.get("required_fix") or ""),
                "status": _bounded(payload.get("status") or "open"),
            }
        )
    return out


def _dedupe_findings(findings: Iterable[Dict[str, Any]]) -> List[Dict[str, Any]]:
    seen: Set[str] = set()
    out: List[Dict[str, Any]] = []
    for finding in findings:
        key = str(finding.get("key") or "").strip()
        if not key:
            key = "|".join(
                str(finding.get(part) or "")
                for part in ("reviewer", "location", "finding", "required_fix")
            )
        if key in seen:
            continue
        seen.add(key)
        out.append(finding)
    return out


def _iter_fixes(raw_fixes: Iterable[Any]) -> List[Dict[str, Any]]:
    out: List[Dict[str, Any]] = []
    for item in raw_fixes:
        if not isinstance(item, Mapping):
            continue
        out.append(
            {
                "fixer": _bounded(item.get("fixer") or ""),
                "provider": _bounded(item.get("fixer") or ""),
                "success": bool(item.get("success")),
                "summary": _bounded(item.get("summary") or "", limit=SUMMARY_LIMIT),
                "changed_files": [
                    _bounded(path, limit=SUMMARY_LIMIT)
                    for path in list(item.get("changed_files") or [])[:100]
                ],
                "round_number": item.get("round_number"),
                "fixer_result": _bounded(item.get("fixer_result") or ""),
                "push_status": _bounded(item.get("push_status") or ""),
                "status": _fix_status(item),
                "commit_sha": _bounded(item.get("pushed_head_sha") or ""),
            }
        )
    return out


def _validation_status(final_state: Mapping[str, Any]) -> str:
    statuses = set((final_state.get("verification_status_by_round") or {}).values())
    if "verified" in statuses:
        return "verified"
    if "stale" in statuses:
        return "stale"
    if "unverified" in statuses:
        return "unverified"
    if "skipped" in statuses:
        return "skipped"
    return "missing"


def _layer1(final_state: Mapping[str, Any]) -> Dict[str, Any]:
    gate_runs = final_state.get("gates") or []
    blockers: List[Any] = []
    for run in gate_runs:
        if not isinstance(run, Mapping):
            continue
        for result in run.get("results") or []:
            if isinstance(result, Mapping) and not result.get("passed", False):
                blockers.append(_bounded_mapping(result))
    if blockers:
        status = "failed"
    elif gate_runs:
        status = "passed"
    else:
        status = "skipped"
    return {
        "status": status,
        "blockers": blockers[:50],
    }


def _verdict(
    *,
    reviewer_status: Mapping[str, Any],
    findings: List[Dict[str, Any]],
    fresh_final_status: str,
    stop_reason: str,
    max_rounds: bool,
    max_cost: bool,
    max_duration: bool,
) -> tuple[str, str]:
    hard_statuses = {"failed", "degraded", "missing"}
    if max_rounds or max_cost or max_duration:
        return "needs_human", stop_reason or "review budget exhausted"
    if any(str(status) in hard_statuses for status in reviewer_status.values()):
        return "needs_human", stop_reason or "reviewer did not complete cleanly"
    if any(finding.get("status") == "open" for finding in findings):
        return "fail", stop_reason or "open findings remain"
    if fresh_final_status == "clean":
        return "pass", stop_reason or "fresh final review is clean"
    return "needs_human", stop_reason or "fresh final review is missing"


def _artifact_status(decision: str, reason: str) -> str:
    if "budget" in reason.lower() or "max " in reason.lower():
        return "budget_exhausted"
    if decision == "pass":
        return "passed"
    if decision == "fail":
        return "failed"
    return "needs_human"


def _reviewer_status(status: Any) -> str:
    value = str(status or "").strip().lower()
    if value == "findings":
        return "blocking"
    if value == "failed":
        return "error"
    return value or "missing"


def _fix_status(item: Mapping[str, Any]) -> str:
    push_status = str(item.get("push_status") or "").lower()
    fixer_result = str(item.get("fixer_result") or "").lower()
    if push_status == "pushed":
        return "applied"
    if fixer_result == "skipped" or push_status == "not_attempted":
        return "skipped"
    if not item.get("success"):
        return "failed"
    return push_status or fixer_result or "skipped"


def _count_findings(
    findings: Iterable[Mapping[str, Any]],
    reviewer: str,
    *,
    blocking_only: bool = False,
) -> int:
    count = 0
    for finding in findings:
        if finding.get("reviewer") != reviewer:
            continue
        if blocking_only and not finding.get("blocking"):
            continue
        count += 1
    return count


def _finding_path(location: Any) -> str:
    text = str(location or "")
    if ":" in text:
        return _bounded(text.rsplit(":", 1)[0])
    return _bounded(text)


def _finding_line(location: Any) -> Optional[int]:
    text = str(location or "")
    if ":" not in text:
        return None
    tail = text.rsplit(":", 1)[1]
    return int(tail) if tail.isdigit() else None


def _bounded(value: Any, *, limit: int = TEXT_LIMIT) -> str:
    text = _scrub(str(value or ""))
    if len(text) <= limit:
        return text
    head = max(limit - 80, 0)
    return text[:head].rstrip() + "\n...[truncated by pdd.checkup.agentic.v1]..."


def _bounded_mapping(value: Mapping[str, Any]) -> Dict[str, Any]:
    out: Dict[str, Any] = {}
    for key, raw in value.items():
        if isinstance(raw, (str, int, float, bool)) or raw is None:
            out[str(key)] = _bounded(raw)
        elif isinstance(raw, list):
            out[str(key)] = [
                _bounded(item) if not isinstance(item, Mapping) else _bounded_mapping(item)
                for item in raw[:50]
            ]
        elif isinstance(raw, Mapping):
            out[str(key)] = _bounded_mapping(raw)
        else:
            out[str(key)] = _bounded(raw)
    return out


def _scrub(text: str) -> str:
    try:
        from .checkup_review_loop import _scrub_secrets  # pylint: disable=import-outside-toplevel

        return _scrub_secrets(text)
    except Exception:  # pragma: no cover - defensive fallback during partial imports
        return text
