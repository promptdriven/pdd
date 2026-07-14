"""Bounded/redacted ``pdd.checkup.agentic.v1`` artifact builder.

Pure data-assembly module: it accepts loop state, config, and context from
:func:`pdd.checkup_review_loop.run_checkup_review_loop` and emits a bounded,
redacted ``pdd.checkup.agentic.v1`` JSON artifact. It performs no subprocess
calls, no GitHub API calls, and has no side effects beyond building the
artifact object. Secret scrubbing is delegated to
``pdd.checkup_review_loop._scrub_secrets`` (imported lazily so this module and
``checkup_review_loop`` can depend on each other without an import cycle).

This module is the SINGLE SOURCE OF TRUTH for the agentic authority vocabulary
(:data:`AGENTIC_AUTHORITY_STATUSES`). Hosted consumers (the pdd_cloud
``checkup_verdict_engine``) mirror the tuple verbatim and MUST NOT extend it.
"""

from __future__ import annotations

import json
import logging
import math
import re
from collections.abc import Mapping, Sequence
from typing import Any, Dict, List, Literal, Optional, Tuple

from pydantic import BaseModel, Field

logger = logging.getLogger(__name__)

# ---------------------------------------------------------------------------
# Module constants
# ---------------------------------------------------------------------------

AGENTIC_V1_SCHEMA = "pdd.checkup.agentic.v1"
FINDING_TEXT_MAX_CHARS = 2000
AGENTIC_ARTIFACT_MAX_BYTES = 256 * 1024
AGENTIC_LIST_MAX_ITEMS = 100
AGENTIC_NESTED_LIST_MAX_ITEMS = 50

# The closed tuple of the five canonical-vs-agentic authority statuses, in this
# exact spelling. This tuple is the single source of truth for the authority
# vocabulary; downstream (pdd_cloud) mirrors it verbatim and never extends it.
AGENTIC_AUTHORITY_STATUSES = (
    "canonical_pass_agentic_mirror_clean",
    "canonical_pass_agentic_mirror_blocking",
    "canonical_unknown_agentic_fallback_pass",
    "canonical_unknown_agentic_fallback_blocking",
    "canonical_fail_agentic_not_authoritative",
)

AgenticAuthorityStatus = Literal[
    "canonical_pass_agentic_mirror_clean",
    "canonical_pass_agentic_mirror_blocking",
    "canonical_unknown_agentic_fallback_pass",
    "canonical_unknown_agentic_fallback_blocking",
    "canonical_fail_agentic_not_authoritative",
]
AgenticArtifactStatus = Literal[
    "passed", "failed", "needs_human", "error", "timeout", "budget_exhausted"
]


# ---------------------------------------------------------------------------
# Pydantic v2 models
# ---------------------------------------------------------------------------


class AgenticLayer1(BaseModel):
    """Layer-1 (PR-scoped checkup) outcome block."""

    status: Literal["pass", "fail", "unknown"]
    blockers: List[str] = Field(default_factory=list)


class AgenticReviewer(BaseModel):
    """Per-reviewer summary row."""

    name: str
    command: str
    status: str
    finding_count: int = 0
    blocking_count: int = 0


class AgenticFinding(BaseModel):
    """A single normalized reviewer finding."""

    reviewer: str
    severity: str
    blocking: bool
    path: Optional[str] = None
    line: Optional[int] = None
    summary: str = ""
    suggested_fix: str = ""


class AgenticFixAttempt(BaseModel):
    """One fixer attempt record (never populated in nofix mode; R3)."""

    provider: str
    status: Literal["skipped", "applied", "failed", "timeout"]
    changed_files: List[str] = Field(default_factory=list)
    commit_sha: Optional[str] = None


class AgenticValidationResult(BaseModel):
    """Validation-after-fix outcome block."""

    status: Literal["not_run", "verified", "unverified"]
    evidence: List[str] = Field(default_factory=list)


class AgenticFreshFinalReview(BaseModel):
    """Fresh final review (new context/session) outcome block."""

    provider: str
    status: Literal[
        "clean",
        "findings",
        "missing",
        "failed",
        "degraded",
        "error",
        "timeout",
        "blocked",
    ]
    finding_count: int = 0


class AgenticVerdict(BaseModel):
    """Final agentic verdict block."""

    decision: Literal["pass", "block", "unknown"]
    reason: str = ""


class AgenticBudget(BaseModel):
    """Budget-cap booleans, computed fresh at artifact-build time (R5)."""

    max_rounds_reached: bool = False
    max_minutes_reached: bool = False
    max_cost_reached: bool = False


class AgenticTruncation(BaseModel):
    """Deterministic public-artifact omission accounting."""

    truncated: bool = False
    max_serialized_bytes: int = AGENTIC_ARTIFACT_MAX_BYTES
    serialized_bytes: int = 0
    original_counts: Dict[str, int] = Field(default_factory=dict)
    omitted_counts: Dict[str, int] = Field(default_factory=dict)


class AgenticV1Artifact(BaseModel):
    """Top-level ``pdd.checkup.agentic.v1`` artifact.

    ``schema_version`` (not ``schema``) is a constant equal to
    :data:`AGENTIC_V1_SCHEMA`; ``schema`` would shadow the Pydantic v2
    ``BaseModel.schema`` attribute and emit a warning. The serialized JSON key
    is ``schema_version`` (R1). ``authority`` is always a member of
    :data:`AGENTIC_AUTHORITY_STATUSES` (R6).
    """

    schema_version: Literal["pdd.checkup.agentic.v1"] = AGENTIC_V1_SCHEMA
    # Transport metadata. The pure builder leaves this unset; the standalone
    # publisher fills the exact nonce-scoped public path before persistence.
    artifact_path: Optional[str] = None
    owner: str = ""
    repo: str = ""
    pr_number: int = 0
    head_sha: str = ""
    mode: Literal["fix", "nofix"] = "fix"
    # One of: passed | failed | needs_human | error | timeout | budget_exhausted.
    status: AgenticArtifactStatus = "error"
    authority: AgenticAuthorityStatus = AGENTIC_AUTHORITY_STATUSES[0]
    layer1: AgenticLayer1 = Field(
        default_factory=lambda: AgenticLayer1(status="unknown")
    )
    reviewers: List[AgenticReviewer] = Field(default_factory=list)
    findings: List[AgenticFinding] = Field(default_factory=list)
    fix_attempts: List[AgenticFixAttempt] = Field(default_factory=list)
    validation_after_fix: AgenticValidationResult = Field(
        default_factory=lambda: AgenticValidationResult(status="not_run")
    )
    fresh_final_review: AgenticFreshFinalReview = Field(
        default_factory=lambda: AgenticFreshFinalReview(provider="", status="missing")
    )
    verdict: AgenticVerdict = Field(
        default_factory=lambda: AgenticVerdict(decision="unknown")
    )
    budget: AgenticBudget = Field(default_factory=AgenticBudget)
    truncation: Optional[AgenticTruncation] = None


# ---------------------------------------------------------------------------
# Helpers
# ---------------------------------------------------------------------------


def _scrub(text: str) -> str:
    """Route free text through the review-loop secret scrubber (lazy import)."""
    if not text:
        return ""
    try:
        from .checkup_review_loop import _scrub_secrets

        return _scrub_secrets(text)
    except Exception:  # pragma: no cover - defensive: fail closed on secrets
        logger.warning("Secret scrubber unavailable; omitting free-text field")
        return "[REDACTED: secret scrubber unavailable]"


def _bounded(text: str) -> str:
    """Scrub and cap a free-text field at :data:`FINDING_TEXT_MAX_CHARS`."""
    scrubbed = _scrub(str(text or ""))
    if len(scrubbed) > FINDING_TEXT_MAX_CHARS:
        return scrubbed[:FINDING_TEXT_MAX_CHARS]
    return scrubbed


def _pretty_size(artifact: AgenticV1Artifact) -> int:
    """Return bytes used by the public pretty-JSON persistence format."""
    return len(json.dumps(artifact.model_dump(), indent=2).encode("utf-8"))


def _bound_public_artifact(artifact: AgenticV1Artifact) -> AgenticV1Artifact:
    """Cap all list families and the complete serialized artifact.

    Inputs have already passed through ``_bounded`` (scrub then truncate).
    Items are retained in their original deterministic order and omitted only
    from the tail, so repeated builds from identical state are byte-stable.
    """
    original_counts = {
        "layer1.blockers": len(artifact.layer1.blockers),
        "reviewers": len(artifact.reviewers),
        "findings": len(artifact.findings),
        "fix_attempts": len(artifact.fix_attempts),
        "fix_attempts.changed_files": sum(
            len(attempt.changed_files) for attempt in artifact.fix_attempts
        ),
        "validation_after_fix.evidence": len(artifact.validation_after_fix.evidence),
    }
    omitted = {key: 0 for key in original_counts}

    def cap(values: List[Any], limit: int, key: str) -> None:
        if len(values) > limit:
            omitted[key] += len(values) - limit
            del values[limit:]

    cap(artifact.layer1.blockers, AGENTIC_LIST_MAX_ITEMS, "layer1.blockers")
    cap(artifact.reviewers, AGENTIC_LIST_MAX_ITEMS, "reviewers")
    cap(artifact.findings, AGENTIC_LIST_MAX_ITEMS, "findings")
    cap(artifact.fix_attempts, AGENTIC_LIST_MAX_ITEMS, "fix_attempts")
    # Count changed files lost with top-level attempts before capping each
    # retained nested list.
    omitted["fix_attempts.changed_files"] += original_counts[
        "fix_attempts.changed_files"
    ] - sum(len(attempt.changed_files) for attempt in artifact.fix_attempts)
    for attempt in artifact.fix_attempts:
        cap(
            attempt.changed_files,
            AGENTIC_NESTED_LIST_MAX_ITEMS,
            "fix_attempts.changed_files",
        )
    cap(
        artifact.validation_after_fix.evidence,
        AGENTIC_LIST_MAX_ITEMS,
        "validation_after_fix.evidence",
    )

    artifact.truncation = AgenticTruncation(
        truncated=any(omitted.values()),
        original_counts=original_counts,
        omitted_counts=omitted,
    )

    def drop_tail() -> bool:
        """Drop one deterministic detail item, retaining verdict aggregates."""
        if artifact.findings:
            artifact.findings.pop()
            omitted["findings"] += 1
            return True
        nested = next(
            (
                attempt.changed_files
                for attempt in reversed(artifact.fix_attempts)
                if attempt.changed_files
            ),
            None,
        )
        if nested is not None:
            nested.pop()
            omitted["fix_attempts.changed_files"] += 1
            return True
        if artifact.fix_attempts:
            attempt = artifact.fix_attempts.pop()
            omitted["fix_attempts"] += 1
            omitted["fix_attempts.changed_files"] += len(attempt.changed_files)
            return True
        if artifact.reviewers:
            artifact.reviewers.pop()
            omitted["reviewers"] += 1
            return True
        if artifact.layer1.blockers:
            artifact.layer1.blockers.pop()
            omitted["layer1.blockers"] += 1
            return True
        if artifact.validation_after_fix.evidence:
            artifact.validation_after_fix.evidence.pop()
            omitted["validation_after_fix.evidence"] += 1
            return True
        return False

    # Cardinality alone cannot bound adversarial 2k strings across several
    # families.  Reduce tail entries until the exact pretty-JSON representation
    # fits.  The byte-count field participates in the measurement, so iterate
    # to a fixed point and re-check the ceiling after every digit-width change.
    while True:
        artifact.truncation.omitted_counts = dict(omitted)
        serialized_bytes = _pretty_size(artifact)
        if serialized_bytes <= AGENTIC_ARTIFACT_MAX_BYTES:
            if artifact.truncation.serialized_bytes == serialized_bytes:
                break
            artifact.truncation.serialized_bytes = serialized_bytes
            continue
        if not drop_tail():  # Fixed-size scalar schema is below the ceiling.
            break
        artifact.truncation.truncated = True
    return artifact


# Fallback blocking-severity set, kept byte-for-byte in sync with
# ``pdd.checkup_review_loop.DEFAULT_BLOCKING_SEVERITIES``. The artifact's
# blocking classification MUST mirror the review-loop's own gating policy
# (``_required_findings`` gates on ``config.blocking_severities``), otherwise the
# machine-readable artifact can report a false clean/pass for a PR that the
# canonical loop still treats as blocked (e.g. an open ``medium`` finding). This
# default is only used when the supplied ``config`` carries no explicit
# ``blocking_severities`` tuple.
_DEFAULT_BLOCKING_SEVERITIES = ("blocker", "critical", "medium")
_SEVERITY_RE = re.compile(
    r"\b(blocker|critical|high|medium|major|low|minor|nit|info)\b", re.IGNORECASE
)
_PATH_LINE_RE = re.compile(r"([\w./\-]+\.\w+):(\d+)")


def _blocking_severities(config: Any) -> set:
    """Return the lowercased set of severities the review loop treats as blocking.

    Mirrors ``pdd.checkup_review_loop._required_findings``, which gates
    unresolved findings on ``config.blocking_severities``. Falls back to
    :data:`_DEFAULT_BLOCKING_SEVERITIES` (the canonical
    ``ReviewLoopConfig`` default) when the config exposes no explicit tuple, so
    the artifact's ``blocking`` flags never under-report relative to the loop's
    own policy.
    """
    severities = getattr(config, "blocking_severities", None)
    if severities:
        try:
            resolved = {
                str(sev).strip().lower() for sev in severities if str(sev).strip()
            }
        except TypeError:
            resolved = set()
        if resolved:
            return resolved
    return {sev.lower() for sev in _DEFAULT_BLOCKING_SEVERITIES}


def _resolve_authority(canonical_status: str, agentic_blocking: bool) -> str:
    """Map the canonical final-gate outcome and the agentic mirror outcome onto
    exactly one member of :data:`AGENTIC_AUTHORITY_STATUSES` (R6).

    ``canonical_status`` is normalized to ``"pass"``, ``"fail"``, or
    ``"unknown"`` (any unrecognized value fails closed to ``"unknown"``). A
    canonical ``fail`` is authoritative regardless of the agentic outcome and
    always resolves to ``canonical_fail_agentic_not_authoritative``.
    """
    normalized = str(canonical_status or "").strip().lower()
    if normalized not in ("pass", "fail", "unknown"):
        normalized = "unknown"
    blocking = bool(agentic_blocking)

    if normalized == "fail":
        return "canonical_fail_agentic_not_authoritative"
    if normalized == "pass":
        return (
            "canonical_pass_agentic_mirror_blocking"
            if blocking
            else "canonical_pass_agentic_mirror_clean"
        )
    # unknown
    return (
        "canonical_unknown_agentic_fallback_blocking"
        if blocking
        else "canonical_unknown_agentic_fallback_pass"
    )


def _normalize_findings(
    text: str,
    reviewer_name: str,
    blocking_severities: Optional[set] = None,
) -> List[AgenticFinding]:
    """Best-effort parser that extracts structured findings from reviewer output.

    On parse failure returns ``[]`` (the caller then sets the reviewer status to
    ``degraded``; R4). Every free-text field is scrubbed and capped at
    :data:`FINDING_TEXT_MAX_CHARS`.

    ``blocking_severities`` is the lowercased set of severities the review loop
    treats as blocking (see :func:`_blocking_severities`); when omitted it
    defaults to the canonical :data:`_DEFAULT_BLOCKING_SEVERITIES` so the
    artifact's ``blocking`` flags mirror the loop's own gating policy.
    """
    blocking = (
        blocking_severities
        if blocking_severities is not None
        else {sev.lower() for sev in _DEFAULT_BLOCKING_SEVERITIES}
    )
    findings: List[AgenticFinding] = []
    raw = text or ""
    if not str(raw).strip():
        return []
    try:
        # The canonical parser has the authoritative plain-text clean rules.
        # Honor that classification before the compatibility severity miner so
        # prose such as "No critical findings" cannot become a fake blocker.
        try:
            from .checkup_review_loop import (  # pylint: disable=import-outside-toplevel
                _parse_review_output,
            )

            canonical = _parse_review_output(str(raw), reviewer_name, 0)
        except Exception:  # fail closed and continue through bounded mirror parsing
            canonical = None
        if canonical is not None and canonical.status == "clean":
            return []
        try:
            # Use the review loop's canonical extractor so the mirror accepts
            # exactly the same bare, embedded, and fenced JSON shapes as the
            # reviewer parser.  In particular, do this before the severity
            # regex fallback: a clean JSON summary such as "No critical issues
            # found" is not itself a critical finding.
            from .checkup_review_loop import _extract_json

            payload = _extract_json(str(raw))
        except (ImportError, TypeError):
            payload = None
        if isinstance(payload, dict):
            raw_findings = payload.get("findings")
            # Mirror ``_parse_review_output``: once a JSON reviewer payload has
            # been recognized, an absent/non-list findings field is an empty
            # result, not an invitation to mine its summary with regexes.
            if not isinstance(raw_findings, list):
                return []
            for item in raw_findings:
                if not isinstance(item, dict):
                    continue
                severity = _coerce_str(item.get("severity"), "info").strip().lower()
                if severity not in {
                    "blocker",
                    "critical",
                    "high",
                    "medium",
                    "low",
                    "info",
                }:
                    severity = "info"
                try:
                    line_no = (
                        int(item["line"]) if item.get("line") is not None else None
                    )
                except (TypeError, ValueError):
                    line_no = None
                findings.append(
                    AgenticFinding(
                        reviewer=_bounded(reviewer_name),
                        severity=_bounded(severity),
                        blocking=severity in blocking,
                        path=_bounded(_coerce_str(item.get("path") or item.get("file")))
                        or None,
                        line=line_no,
                        summary=_bounded(
                            _coerce_str(item.get("summary") or item.get("finding"))
                        ),
                        suggested_fix=_bounded(
                            _coerce_str(
                                item.get("suggested_fix") or item.get("required_fix")
                            )
                        ),
                    )
                )
            return findings
        for line in str(raw).splitlines():
            stripped = line.strip()
            if not stripped:
                continue
            sev_match = _SEVERITY_RE.search(stripped)
            if not sev_match:
                continue
            severity = sev_match.group(1).lower()
            path: Optional[str] = None
            line_no: Optional[int] = None
            loc_match = _PATH_LINE_RE.search(stripped)
            if loc_match:
                path = loc_match.group(1)
                try:
                    line_no = int(loc_match.group(2))
                except (TypeError, ValueError):
                    line_no = None
            findings.append(
                AgenticFinding(
                    reviewer=_bounded(reviewer_name),
                    severity=_bounded(severity),
                    blocking=severity in blocking,
                    path=_bounded(path) if path else None,
                    line=line_no,
                    summary=_bounded(stripped),
                    suggested_fix="",
                )
            )
    except Exception:  # pragma: no cover - defensive: parse failure -> []
        logger.warning("Finding normalization failed for reviewer %s", reviewer_name)
        return []
    return findings


def _deduplicate_findings(findings: List[AgenticFinding]) -> List[AgenticFinding]:
    """Deduplicate on ``(reviewer, path, line, severity)``; prose-only findings
    (no path/line) dedup on the first 64 characters of ``summary``.
    """
    seen: set = set()
    deduped: List[AgenticFinding] = []
    for finding in findings:
        if finding.path is None and finding.line is None:
            key: Any = (
                "prose",
                finding.reviewer,
                finding.severity,
                (finding.summary or "")[:64],
            )
        else:
            key = (finding.reviewer, finding.path, finding.line, finding.severity)
        if key in seen:
            continue
        seen.add(key)
        deduped.append(finding)
    return deduped


def _coerce_str(value: Any, default: str = "") -> str:
    if value is None:
        return default
    return str(value)


def _finding_reviewers(value: Any) -> set[str]:
    """Decode the schema-compatible comma-separated attribution set."""
    return {
        role.strip() for role in _coerce_str(value).split(",") if role.strip()
    }


def _mapping(value: Any) -> Dict[Any, Any]:
    """Return a shallow dict for mapping-shaped runtime state, else ``{}``."""
    if isinstance(value, Mapping):
        try:
            return dict(value)
        except (TypeError, ValueError):
            return {}
    return {}


def _sequence(value: Any) -> List[Any]:
    """Return a list for non-text sequence-shaped runtime state, else ``[]``."""
    if isinstance(value, Sequence) and not isinstance(value, (str, bytes, bytearray)):
        try:
            return list(value)
        except TypeError:
            return []
    return []


def _runtime_mapping(obj: Any, name: str) -> Dict[Any, Any]:
    """Read a restored mapping field or raise into the fail-closed wrapper."""
    value = getattr(obj, name, {})
    if value is None:
        return {}
    if not isinstance(value, Mapping):
        raise TypeError(f"{name} must be a mapping")
    return _mapping(value)


def _runtime_sequence(obj: Any, name: str) -> List[Any]:
    """Read a restored non-text sequence or raise into the fail-closed wrapper."""
    value = getattr(obj, name, [])
    if value is None:
        return []
    if not isinstance(value, Sequence) or isinstance(value, (str, bytes, bytearray)):
        raise TypeError(f"{name} must be a non-text sequence")
    return _sequence(value)


def _split_location(location: Any) -> Tuple[Optional[str], Optional[int]]:
    """Split a production ``ReviewFinding.location`` into path and line.

    Function/symbol locations such as ``pdd/foo.py:helper`` are preserved as a
    path-like location with no invented line number.
    """
    text = _coerce_str(location).strip()
    if not text:
        return None, None
    match = re.fullmatch(r"(.+\.[A-Za-z0-9_]+):(\d+)", text)
    if not match:
        return text, None
    try:
        return match.group(1), int(match.group(2))
    except (TypeError, ValueError):  # pragma: no cover - regex guarantees digits
        return text, None


def _num(obj: Any, *names: str) -> Optional[float]:
    """Return the first numeric attribute among ``names`` on ``obj``, else None.

    Booleans are rejected (``isinstance(True, int)`` is truthy in Python) so a
    stray flag never masquerades as a numeric cap/consumption value.
    """
    for name in names:
        value = getattr(obj, name, None)
        if isinstance(value, bool):
            continue
        if isinstance(value, (int, float)):
            number = float(value)
            if not math.isfinite(number):
                raise ValueError(f"{name} must be finite")
            return number
    return None


def _recompute_budget_flags(loop_state: Any, config: Any) -> "AgenticBudget":
    """R5: recompute ``budget.max_*_reached`` from ACTUAL consumption vs caps.

    Issue #1788 re-review: the builder must not copy the persisted
    ``loop_state.max_*_reached`` flags. Those are only set at the review loop's
    in-loop budget checks, so work performed after the final check (e.g. the
    fresh-final review, the final gate, report rendering) can cross a cap or the
    wall-clock deadline without ever flipping them — yielding a
    ``max_cost_reached=false`` artifact on a run that actually overran its cost
    cap. Instead compare the real ``rounds_completed`` / ``elapsed_minutes`` /
    ``total_cost`` carried on the loop state against the configured caps.

    A flag is only left to the persisted value when neither an actual nor a
    positive cap is available (minimal/legacy state objects), and even then it is
    OR-ed with the persisted signal so a real in-loop trip is never lost. This is
    fail-closed: an unknown value never downgrades a reached cap to ``False``.
    """
    max_rounds = _num(config, "max_rounds", "max_review_rounds")
    max_minutes = _num(config, "max_minutes", "max_review_minutes")
    max_cost = _num(config, "max_cost", "max_review_cost")

    rounds_used = _num(loop_state, "rounds_completed", "rounds_used")
    minutes_used = _num(loop_state, "elapsed_minutes")
    cost_used = _num(loop_state, "total_cost")

    def _reached(used: Optional[float], cap: Optional[float], persisted: bool) -> bool:
        if used is not None and cap is not None and cap > 0:
            # Recomputed from actuals; OR with any persisted in-loop trip so a
            # real cap hit recorded mid-loop is never dropped.
            return bool(used >= cap) or bool(persisted)
        return bool(persisted)

    persisted_rounds = bool(getattr(loop_state, "max_rounds_reached", False))
    fresh_status = (
        _coerce_str(getattr(loop_state, "fresh_final_status", "missing") or "missing")
        .strip()
        .lower()
    )
    # Finishing cleanly on the last allowed round consumed the budget but did
    # not exhaust it: no additional round was required. The loop's persisted
    # flag remains authoritative when it explicitly stopped for max rounds;
    # otherwise an actual boundary crossing only exhausts when the outcome is
    # still non-clean and would require more work.
    rounds_reached = persisted_rounds
    if rounds_used is not None and max_rounds is not None and max_rounds > 0:
        rounds_reached = rounds_reached or (
            rounds_used >= max_rounds and fresh_status != "clean"
        )

    return AgenticBudget(
        max_rounds_reached=rounds_reached,
        max_minutes_reached=_reached(
            minutes_used,
            max_minutes,
            bool(getattr(loop_state, "max_duration_reached", False)),
        ),
        max_cost_reached=_reached(
            cost_used, max_cost, bool(getattr(loop_state, "max_cost_reached", False))
        ),
    )


def _canonical_status_from_gate(final_gate_report: Any) -> str:
    """Derive ``pass``/``fail``/``unknown`` from a Layer-1/final-gate report."""
    if not isinstance(final_gate_report, dict):
        return "unknown"
    for key in ("layer1_status", "status", "final_gate_status"):
        raw = str(final_gate_report.get(key, "") or "").strip().lower()
        if raw in ("pass", "passed", "clean", "success", "ok"):
            return "pass"
        if raw in ("fail", "failed", "blocked", "error"):
            return "fail"
    return "unknown"


# ``ReviewLoopState.raw_outputs`` keys are compound. Reviewer passes use
# ``"{mode}:{reviewer}:round{N}"`` (optionally ``:parse-repair``), while fixer
# passes use ``"fix:{fixer}:for:{reviewer}:round{N}"`` and
# ``"sot-repair:{fixer}:round{N}"``. Only reviewer passes carry reviewer
# findings, so fixer keys are skipped when attributing findings.
_FIXER_OUTPUT_PREFIXES = ("fix:", "sot-repair:")


def _reviewer_name_from_key(key: str) -> Optional[str]:
    """Return the plain reviewer role for a raw-output key, or ``None``.

    ``None`` means the entry is a fixer output (not a reviewer pass) and must not
    be attributed to a reviewer. A plain key with no ``:`` (e.g. ``"codex"``) is
    returned unchanged so direct callers/tests keep working.
    """
    text = str(key or "").strip()
    if not text:
        return None
    if text.startswith(_FIXER_OUTPUT_PREFIXES):
        return None
    if ":" not in text:
        return text
    parts = text.split(":")
    # "{mode}:{reviewer}:round{N}" (+ optional trailing token).
    if len(parts) >= 3 and parts[2].startswith("round"):
        return parts[1] or None
    return None


def _map_fix_status(fixer_result: Any, push_status: Any) -> str:
    """Map a ``FixResult`` onto the spec ``fix_attempts[].status`` vocabulary.

    Spec values: ``skipped | applied | failed | timeout``. ``FixResult`` carries
    ``fixer_result`` in ``{attempted, skipped, failed}``, but that describes the
    fixer subprocess only.  A fix is ``applied`` exclusively when the separate
    push trust boundary says ``pushed``.
    """
    result = _coerce_str(fixer_result).strip().lower()
    push = _coerce_str(push_status).strip().lower()
    if push == "push_failed":
        return "failed"
    if push == "pushed":
        return "applied"
    if "timeout" in result:
        return "timeout"
    if result in ("skipped", "failed"):
        return result
    # ``not_attempted``, a missing push status, and unknown push states are all
    # non-applied.  This includes an otherwise-successful fixer that a
    # prompt/source guard stopped before commit/push.
    return "skipped"


def _map_status(
    *,
    passed: bool,
    budget_exhausted: bool,
    needs_human: bool,
    timed_out: bool,
    errored: bool,
) -> str:
    """Map the review outcome onto the spec top-level ``status`` vocabulary.

    Spec values: ``passed | failed | needs_human | error | timeout |
    budget_exhausted``.
    """
    if passed:
        return "passed"
    if budget_exhausted:
        return "budget_exhausted"
    if timed_out:
        return "timeout"
    if errored:
        return "error"
    if needs_human:
        return "needs_human"
    return "failed"


# ---------------------------------------------------------------------------
# Public builder
# ---------------------------------------------------------------------------


def _build_agentic_v1_artifact(
    *,
    loop_state: Any,
    config: Any,
    context: Any,
    final_gate_report: Any,
) -> AgenticV1Artifact:
    """Assemble the bounded/redacted ``pdd.checkup.agentic.v1`` artifact.

    Pure data assembly from review-loop state. Graceful degradation: extraction
    failures log a WARNING and fall back to safe defaults; this function never
    crashes the caller.
    """
    # --- mode (R3): nofix never carries fix attempts ----------------------
    no_fix = bool(getattr(config, "no_fix", False)) or bool(
        getattr(config, "review_only", False)
    )
    mode = "nofix" if no_fix else "fix"

    # --- identity/context -------------------------------------------------
    owner = _bounded(
        _coerce_str(
            getattr(context, "pr_owner", "") or getattr(context, "repo_owner", "")
        )
    )
    repo = _bounded(
        _coerce_str(
            getattr(context, "pr_repo", "") or getattr(context, "repo_name", "")
        )
    )
    try:
        pr_number = int(getattr(context, "pr_number", 0) or 0)
    except (TypeError, ValueError):
        pr_number = 0
    head_sha = _bounded(
        _coerce_str(
            getattr(loop_state, "verified_head_sha", None)
            or getattr(loop_state, "remote_pr_head_sha", None)
            or getattr(loop_state, "reviewed_head_sha", None)
            or ""
        )
    )

    # --- reviewers + findings --------------------------------------------
    # Mirror the review loop's own blocking policy (``config.blocking_severities``
    # via ``_required_findings``) so the artifact never under-reports blocking
    # findings relative to the canonical loop (e.g. an open ``medium``).
    blocking_severities = _blocking_severities(config)
    reviewer_status: Dict[str, str] = _runtime_mapping(loop_state, "reviewer_status")
    raw_outputs = _runtime_sequence(loop_state, "raw_outputs")
    raw_structured_findings = _runtime_sequence(loop_state, "findings")
    findings_by_reviewer: Dict[str, List[AgenticFinding]] = {}
    reviewers_with_output: set = set()
    for entry in raw_outputs:
        try:
            raw_key, output_text = entry[0], entry[1]
        except (TypeError, IndexError, KeyError):
            continue
        # Normalize the compound raw-output key to the plain reviewer role; skip
        # fixer outputs so their prose is never parsed as reviewer findings.
        reviewer_name = _reviewer_name_from_key(_coerce_str(raw_key))
        if not reviewer_name:
            continue
        reviewers_with_output.add(reviewer_name)
        parsed = (
            []
            if raw_structured_findings
            else _normalize_findings(
                _coerce_str(output_text), reviewer_name, blocking_severities
            )
        )
        findings_by_reviewer.setdefault(reviewer_name, []).extend(parsed)

    # Prefer already-structured loop findings when present.
    structured: List[AgenticFinding] = []
    open_structured: List[AgenticFinding] = []
    for f in raw_structured_findings:
        try:
            severity = _coerce_str(getattr(f, "severity", "") or "info").lower()
            finding_path, finding_line = _split_location(getattr(f, "location", None))
            finding = AgenticFinding(
                reviewer=_bounded(_coerce_str(getattr(f, "reviewer", "") or "unknown")),
                severity=_bounded(severity),
                blocking=severity in blocking_severities,
                path=_bounded(finding_path) if finding_path else None,
                line=finding_line,
                summary=_bounded(_coerce_str(getattr(f, "finding", ""))),
                suggested_fix=_bounded(_coerce_str(getattr(f, "required_fix", ""))),
            )
            structured.append(finding)
            finding_status = (
                _coerce_str(getattr(f, "status", "open") or "open").strip().lower()
            )
            if finding_status != "fixed":
                open_structured.append(finding)
        except Exception:  # pragma: no cover - defensive
            continue

    all_findings = _deduplicate_findings(
        structured + [f for group in findings_by_reviewer.values() for f in group]
    )

    reviewers: List[AgenticReviewer] = []
    # Provenance must describe work that actually ran. Hosted artifact-only
    # command requests are intentionally excluded from canonical execution, so
    # they must not be serialized as though a reviewer invoked them.
    reviewer_commands: Dict[str, str] = _runtime_mapping(config, "reviewer_commands")
    # The loop reports a role as ``fixer`` in reviewer_status purely for
    # traceability; that is not a reviewer verdict, so skip it here.
    for name, status in reviewer_status.items():
        if name == "fresh-final" or _coerce_str(status) == "fixer":
            continue
        own = [f for f in all_findings if name in _finding_reviewers(f.reviewer)]
        status_str = _coerce_str(status)
        # R4: a reviewer that reported findings/blocking but whose output could
        # not be parsed into any structured finding is degraded, never reported
        # as if it produced clean/attributable results. A genuinely clean
        # reviewer (no findings) stays clean.
        parse_failed = (
            name in reviewers_with_output
            and status_str in ("findings", "blocking")
            and not own
        )
        resolved_status = "degraded" if parse_failed else status_str
        reviewers.append(
            AgenticReviewer(
                name=_bounded(_coerce_str(name)),
                command=_bounded(_coerce_str(reviewer_commands.get(name, ""))),
                status=_bounded(resolved_status),
                finding_count=len(own),
                blocking_count=sum(1 for f in own if f.blocking),
            )
        )

    # --- fix attempts (R3: empty in nofix) --------------------------------
    raw_fixes = _runtime_sequence(loop_state, "fixes")
    fix_attempts: List[AgenticFixAttempt] = []
    if not no_fix:
        for fx in raw_fixes:
            try:
                fix_attempts.append(
                    AgenticFixAttempt(
                        provider=_bounded(
                            _coerce_str(
                                getattr(fx, "fixer", None)
                                or getattr(fx, "provider", "")
                                or "unknown"
                            )
                        ),
                        status=_map_fix_status(
                            getattr(fx, "fixer_result", None),
                            getattr(fx, "push_status", None),
                        ),
                        changed_files=[
                            _bounded(_coerce_str(path))
                            for path in (getattr(fx, "changed_files", []) or [])
                        ],
                        commit_sha=(
                            _bounded(_coerce_str(getattr(fx, "pushed_head_sha", None)))
                            if _coerce_str(getattr(fx, "push_status", None))
                            .strip()
                            .lower()
                            == "pushed"
                            else None
                        ),
                    )
                )
            except Exception:  # pragma: no cover - defensive
                continue

    # --- layer1 -----------------------------------------------------------
    canonical_status = _canonical_status_from_gate(final_gate_report)
    layer1_blockers: List[str] = []
    if isinstance(final_gate_report, dict):
        for blk in final_gate_report.get("blockers", []) or []:
            layer1_blockers.append(_bounded(_coerce_str(blk)))
    layer1 = AgenticLayer1(status=canonical_status, blockers=layer1_blockers)

    # --- fresh final review ----------------------------------------------
    fresh_status = _coerce_str(
        getattr(loop_state, "fresh_final_status", "missing") or "missing"
    )
    fresh_provider = _bounded(
        _coerce_str(
            getattr(config, "fresh_final_review_role", None)
            or getattr(loop_state, "active_reviewer", "")
            or ""
        )
    )
    fresh_final_review = AgenticFreshFinalReview(
        provider=fresh_provider,
        status=fresh_status,
        finding_count=sum(1 for f in all_findings if f.reviewer == "fresh-final"),
    )

    # --- validation after fix --------------------------------------------
    verified = _coerce_str(getattr(loop_state, "verified_head_sha", "") or "")
    # Issue #1788 (re-review): when ``_finalize`` proved the reviewed/verified
    # head is stale it downgrades the round to ``stale`` and reverts fixed
    # findings, but leaves ``verified_head_sha`` set for the rendered report.
    # The mirror must not report that stale SHA as a ``verified`` validation, so
    # fail the evidence closed to ``unverified`` (which the pass predicate treats
    # as not-clean) and drop the stale SHA evidence.
    validation_stale = bool(getattr(loop_state, "validation_stale", False))
    fix_was_attempted = bool(raw_fixes) and not no_fix
    if not fix_was_attempted:
        validation_status = "not_run"
    elif validation_stale:
        validation_status = "unverified"
    else:
        validation_status = "verified" if verified else "unverified"
    validation_after_fix = AgenticValidationResult(
        status=validation_status,
        evidence=[_bounded(verified)] if validation_status == "verified" else [],
    )

    # --- budget (R5: computed fresh from config caps vs actual) -----------
    budget = _recompute_budget_flags(loop_state, config)
    budget_exhausted = (
        budget.max_rounds_reached
        or budget.max_minutes_reached
        or budget.max_cost_reached
    )

    # --- agentic verdict + blocking signal --------------------------------
    # A clean pass is derived purely from the outcome: the fresh-final review is
    # clean and no blocking findings remain. ``stop_reason`` is NOT a failure
    # gate — ``run_checkup_review_loop`` sets it on EVERY exit path, including a
    # clean one (e.g. "Primary reviewer is clean."), so it is reported as the
    # verdict reason but never used to decide pass/fail.
    # ``all_findings`` intentionally preserves historical reviewer text for the
    # artifact, including raw output from earlier rounds and structured findings
    # whose loop status is now ``fixed``. The pass/fail signal must instead use
    # the current unresolved loop state when it is available.
    verdict_findings = (
        _deduplicate_findings(open_structured) if structured else all_findings
    )
    stop_reason = _bounded(_coerce_str(getattr(loop_state, "stop_reason", "")))
    # A successful reviewer fallback intentionally leaves the failed primary
    # row in the artifact for diagnostics.  Once the loop has promoted a
    # different active reviewer, only that active/otherwise-unsuperseded state
    # is authoritative for the verdict.  Preserve every row and finding in the
    # artifact, but exclude explicitly superseded reviewer data from gating.
    active_reviewer = _coerce_str(getattr(loop_state, "active_reviewer", "")).strip()
    original_reviewer = _coerce_str(
        getattr(loop_state, "original_reviewer", "")
    ).strip()
    superseded_reviewers: set = set()
    if active_reviewer and original_reviewer and active_reviewer != original_reviewer:
        superseded_reviewers.add(original_reviewer)
    reviewer_status_details = _runtime_mapping(loop_state, "reviewer_status_details")
    for name, detail in reviewer_status_details.items():
        if not isinstance(detail, dict):
            continue
        if _coerce_str(detail.get("superseded_by_fallback")).strip().lower() == "true":
            superseded_reviewers.add(_coerce_str(name))

    hard_reviewer_states = {
        "failed",
        "degraded",
        "missing",
        "error",
        "timeout",
        "blocked",
    }
    active_status = _coerce_str(reviewer_status.get(active_reviewer)).strip().lower()
    if active_reviewer and active_status and active_status not in hard_reviewer_states:
        # Compatibility with older/minimal loop-state objects that predate
        # ``original_reviewer``: promotion of a usable active reviewer is enough
        # to identify other retained hard-failure rows as diagnostics.
        superseded_reviewers.update(
            r.name
            for r in reviewers
            if r.name != active_reviewer and r.status in hard_reviewer_states
        )

    verdict_findings = [
        finding
        for finding in verdict_findings
        if not (
            _finding_reviewers(finding.reviewer)
            and _finding_reviewers(finding.reviewer).issubset(superseded_reviewers)
        )
    ]
    remaining_open = [f for f in verdict_findings if f.blocking]
    reviewer_states = {
        r.status for r in reviewers if r.name not in superseded_reviewers
    }
    hard_reviewer_state = bool(reviewer_states & hard_reviewer_states)
    validation_clean = validation_status in {"not_run", "verified"}
    alignment_required = bool(getattr(context, "has_issue", False))
    issue_aligned = getattr(loop_state, "issue_aligned", None)
    alignment_clean = not alignment_required or issue_aligned is True
    passed = (
        canonical_status != "fail"
        and not budget_exhausted
        and not hard_reviewer_state
        and fresh_status == "clean"
        and validation_clean
        and alignment_clean
        and not remaining_open
    )
    agentic_blocking = not passed
    decision = "pass" if passed else "block"
    if not alignment_clean:
        stop_reason = "Issue alignment was not proven by the reviewer."
    verdict = AgenticVerdict(decision=decision, reason=stop_reason)
    # A reviewer that failed/degraded/errored (not a content block) means the
    # outcome could not be decided by the reviewers → needs_human.
    needs_human = (
        bool(reviewer_states & {"failed", "degraded", "missing", "error"})
        and not remaining_open
    )
    timed_out = fresh_status == "timeout" or "timeout" in reviewer_states
    errored = fresh_status == "error" or "error" in reviewer_states
    status = _map_status(
        passed=passed,
        budget_exhausted=budget_exhausted,
        needs_human=needs_human,
        timed_out=timed_out,
        errored=errored,
    )

    # --- authority (R6) ---------------------------------------------------
    authority = _resolve_authority(canonical_status, agentic_blocking)

    try:
        return AgenticV1Artifact(
            schema_version=AGENTIC_V1_SCHEMA,
            owner=owner,
            repo=repo,
            pr_number=pr_number,
            head_sha=head_sha,
            mode=mode,
            status=status,
            authority=authority,
            layer1=layer1,
            reviewers=reviewers,
            findings=all_findings,
            fix_attempts=fix_attempts,
            validation_after_fix=validation_after_fix,
            fresh_final_review=fresh_final_review,
            verdict=verdict,
            budget=budget,
        )
    except Exception:  # pragma: no cover - defensive: always fail closed
        logger.warning(
            "Falling back to a minimal agentic artifact after assembly error"
        )
        return _fail_closed_artifact(
            context=context,
            config=config,
            final_gate_report=final_gate_report,
            reason="Artifact assembly failed closed.",
        )


def _fail_closed_artifact(
    *,
    context: Any,
    config: Any,
    final_gate_report: Any,
    reason: str,
) -> AgenticV1Artifact:
    """Build a minimal blocker without erasing authoritative gate failure."""
    canonical_status = _canonical_status_from_gate(final_gate_report)
    try:
        owner = _bounded(
            _coerce_str(
                getattr(context, "pr_owner", "") or getattr(context, "repo_owner", "")
            )
        )
        repo = _bounded(
            _coerce_str(
                getattr(context, "pr_repo", "") or getattr(context, "repo_name", "")
            )
        )
        pr_number = int(getattr(context, "pr_number", 0) or 0)
    except Exception:  # pragma: no cover - malformed compatibility object
        owner, repo, pr_number = "", "", 0
    try:
        mode = (
            "nofix"
            if bool(getattr(config, "review_only", False))
            or bool(getattr(config, "no_fix", False))
            else "fix"
        )
    except Exception:  # pragma: no cover - malformed compatibility object
        mode = "fix"
    blockers: List[str] = []
    if canonical_status == "fail" and isinstance(final_gate_report, dict):
        raw_blockers = final_gate_report.get("blockers", [])
        if isinstance(raw_blockers, Sequence) and not isinstance(
            raw_blockers, (str, bytes, bytearray)
        ):
            blockers = [_bounded(_coerce_str(value)) for value in raw_blockers]
    return AgenticV1Artifact(
        schema_version=AGENTIC_V1_SCHEMA,
        owner=owner,
        repo=repo,
        pr_number=pr_number,
        mode=mode,
        status="error",
        authority=_resolve_authority(canonical_status, True),
        layer1=AgenticLayer1(status=canonical_status, blockers=blockers),
        fresh_final_review=AgenticFreshFinalReview(provider="", status="missing"),
        verdict=AgenticVerdict(decision="block", reason=_bounded(reason)),
    )


def build_agentic_v1_artifact(
    *,
    loop_state: Any,
    config: Any,
    context: Any,
    final_gate_report: Any,
) -> AgenticV1Artifact:
    """Build an agentic artifact and never propagate malformed runtime state.

    Review-loop state can be restored from older or partially-written JSON, so
    mappings and sequences are not trusted solely because an attribute exists.
    Any unexpected extraction failure returns a valid, blocking v1 artifact;
    callers never receive an exception or a false pass.
    """
    try:
        return _bound_public_artifact(
            _build_agentic_v1_artifact(
                loop_state=loop_state,
                config=config,
                context=context,
                final_gate_report=final_gate_report,
            )
        )
    except Exception as exc:  # pragma: no cover - last-resort compatibility
        logger.warning(
            "Agentic artifact extraction failed closed: %s", type(exc).__name__
        )
        return _bound_public_artifact(
            _fail_closed_artifact(
                context=context,
                config=config,
                final_gate_report=final_gate_report,
                reason="Artifact extraction failed closed.",
            )
        )
