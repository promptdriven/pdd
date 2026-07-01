"""Structured artifact for agentic fallback/mirror checkup runs."""

from __future__ import annotations

from typing import Any, Dict, Iterable, List, Mapping, Optional

AGENTIC_V1_SCHEMA = "pdd.checkup.agentic.v1"
DEFAULT_MIRROR_PROMPT = (
    "Using the same criteria as canonical `pdd checkup`, find concrete reasons "
    "this PR should not merge. Do not introduce new merge criteria. Report only "
    "verifiable blockers or material risks."
)
TEXT_LIMIT = 2000

CANONICAL_PASS_AGENTIC_MIRROR_CLEAN = "canonical_pass_agentic_mirror_clean"
CANONICAL_PASS_AGENTIC_MIRROR_BLOCKING = "canonical_pass_agentic_mirror_blocking"
CANONICAL_UNKNOWN_AGENTIC_FALLBACK_PASS = "canonical_unknown_agentic_fallback_pass"
CANONICAL_UNKNOWN_AGENTIC_FALLBACK_BLOCKING = (
    "canonical_unknown_agentic_fallback_blocking"
)
CANONICAL_FAIL_AGENTIC_NOT_AUTHORITATIVE = "canonical_fail_agentic_not_authoritative"

_INFRA_MARKERS = (
    "auth",
    "authentication",
    "could not complete",
    "degraded",
    "malformed",
    "missing",
    "parse",
    "parser",
    "provider",
    "rate",
    "timeout",
    "timed out",
    "unknown",
    "unreadable",
)


def classify_canonical_result(
    *,
    success: bool,
    message: str,
    final_state: Optional[Mapping[str, Any]] = None,
) -> str:
    """Classify canonical checkup output as pass, fail, or unknown."""
    if isinstance(final_state, Mapping):
        statuses = final_state.get("reviewer_status") or {}
        findings = final_state.get("findings") or []
        if any(isinstance(item, Mapping) and item.get("status") == "open" for item in findings):
            return "fail"
        if any(str(value) in {"failed", "degraded", "missing"} for value in statuses.values()):
            return "unknown"
        if final_state.get("max_rounds_reached") or final_state.get("max_cost_reached"):
            return "unknown"
        if final_state.get("max_duration_reached"):
            return "unknown"
        if final_state.get("fresh_final_status") in {"failed", "degraded", "missing"}:
            return "unknown"
    if success:
        return "pass"
    lowered = (message or "").lower()
    if any(marker in lowered for marker in _INFRA_MARKERS):
        return "unknown"
    return "fail"


def build_agentic_mirror_artifact(
    *,
    owner: str,
    repo: str,
    pr_number: int,
    pr_url: str,
    issue_url: str,
    canonical_success: bool,
    canonical_message: str,
    canonical_final_state: Optional[Mapping[str, Any]],
    mirror_final_state: Optional[Mapping[str, Any]],
    mirror_prompt: str,
    reviewers: Mapping[str, str],
    mode: str,
    total_cost: float,
) -> Dict[str, Any]:
    """Build the stable fallback/mirror artifact consumed by hosted checkup."""
    canonical = classify_canonical_result(
        success=canonical_success,
        message=canonical_message,
        final_state=canonical_final_state,
    )
    mirror_status = _mirror_status(mirror_final_state)
    status = _combined_status(canonical, mirror_status)
    canonical_reason = _bounded(canonical_message)
    mirror_findings = _findings(mirror_final_state)
    return {
        "schema": AGENTIC_V1_SCHEMA,
        "owner": _bounded(owner),
        "repo": _bounded(repo),
        "pr_number": pr_number,
        "pr_url": _bounded(pr_url),
        "issue_url": _bounded(issue_url),
        "mode": mode,
        "status": status,
        "canonical": {
            "source": "pdd.checkup.final_gate.v1",
            "classification": canonical,
            "success": bool(canonical_success),
            "reason": canonical_reason,
            "final_state": _bounded_final_state(canonical_final_state),
        },
        "agentic_mirror": {
            "authoritative": False,
            "status": mirror_status,
            "prompt": _bounded(mirror_prompt),
            "reviewers": [
                {"name": _bounded(name), "command": _bounded(command)}
                for name, command in reviewers.items()
            ],
            "findings": mirror_findings,
        },
        "verdict": {
            "decision": _decision(canonical, mirror_status),
            "reason": _verdict_reason(status, canonical_reason, mirror_findings),
        },
        "budget": {
            "total_cost": total_cost,
            "max_rounds_reached": bool(
                (canonical_final_state or {}).get("max_rounds_reached")
            ),
            "max_minutes_reached": bool(
                (canonical_final_state or {}).get("max_duration_reached")
            ),
            "max_cost_reached": bool(
                (canonical_final_state or {}).get("max_cost_reached")
            ),
        },
    }


def _combined_status(canonical: str, mirror_status: str) -> str:
    mirror_blocking = mirror_status == "blocking"
    if canonical == "pass":
        return (
            CANONICAL_PASS_AGENTIC_MIRROR_BLOCKING
            if mirror_blocking
            else CANONICAL_PASS_AGENTIC_MIRROR_CLEAN
        )
    if canonical == "unknown":
        return (
            CANONICAL_UNKNOWN_AGENTIC_FALLBACK_BLOCKING
            if mirror_blocking
            else CANONICAL_UNKNOWN_AGENTIC_FALLBACK_PASS
        )
    return CANONICAL_FAIL_AGENTIC_NOT_AUTHORITATIVE


def _decision(canonical: str, mirror_status: str) -> str:
    if mirror_status == "blocking":
        return "fail"
    if canonical == "pass":
        return "pass"
    if canonical == "unknown" and mirror_status == "clean":
        return "pass"
    return "fail" if canonical == "fail" else "needs_human"


def _mirror_status(final_state: Optional[Mapping[str, Any]]) -> str:
    if not isinstance(final_state, Mapping):
        return "skipped"
    if any(finding.get("status") == "open" for finding in _raw_findings(final_state)):
        return "blocking"
    statuses = final_state.get("reviewer_status") or {}
    if any(str(value) in {"failed", "degraded", "missing"} for value in statuses.values()):
        return "unknown"
    return "clean" if final_state.get("fresh_final_status") == "clean" else "unknown"


def _findings(final_state: Optional[Mapping[str, Any]]) -> List[Dict[str, Any]]:
    out: List[Dict[str, Any]] = []
    for item in _raw_findings(final_state):
        if item.get("status") != "open":
            continue
        out.append(
            {
                "reviewer": _bounded(item.get("reviewer") or ""),
                "severity": _bounded(item.get("severity") or ""),
                "area": _bounded(item.get("area") or ""),
                "location": _bounded(item.get("location") or ""),
                "summary": _bounded(item.get("finding") or ""),
                "suggested_fix": _bounded(item.get("required_fix") or ""),
            }
        )
    return out[:100]


def _raw_findings(final_state: Optional[Mapping[str, Any]]) -> Iterable[Mapping[str, Any]]:
    if not isinstance(final_state, Mapping):
        return []
    findings = final_state.get("findings") or []
    return [item for item in findings if isinstance(item, Mapping)]


def _bounded_final_state(final_state: Optional[Mapping[str, Any]]) -> Dict[str, Any]:
    if not isinstance(final_state, Mapping):
        return {}
    keys = (
        "fresh_final_status",
        "issue_aligned",
        "stop_reason",
        "max_rounds_reached",
        "max_cost_reached",
        "max_duration_reached",
        "source_of_truth",
    )
    return {key: _bounded_value(final_state.get(key)) for key in keys if key in final_state}


def _bounded_value(value: Any) -> Any:
    if isinstance(value, str):
        return _bounded(value)
    if isinstance(value, Mapping):
        return {str(key): _bounded_value(raw) for key, raw in value.items()}
    if isinstance(value, list):
        return [_bounded_value(item) for item in value[:50]]
    return value


def _verdict_reason(status: str, canonical_reason: str, findings: List[Dict[str, Any]]) -> str:
    if status == CANONICAL_FAIL_AGENTIC_NOT_AUTHORITATIVE:
        return _bounded(
            "Canonical checkup failed; agentic mirror is non-authoritative. "
            + canonical_reason
        )
    if findings:
        return _bounded("Agentic mirror reported non-authoritative blockers.")
    return _bounded(canonical_reason or status)


def _bounded(value: Any, *, limit: int = TEXT_LIMIT) -> str:
    text = _scrub(str(value or ""))
    if len(text) <= limit:
        return text
    return text[: max(limit - 80, 0)].rstrip() + "\n...[truncated by pdd.checkup.agentic.v1]..."


def _scrub(text: str) -> str:
    try:
        from .checkup_review_loop import _scrub_secrets  # pylint: disable=import-outside-toplevel

        return _scrub_secrets(text)
    except Exception:  # pragma: no cover - defensive fallback during partial imports
        return text
