"""Versioned, automation-safe results for ``pdd detect --stories``."""

from __future__ import annotations

import json
import os
import re
import tempfile
import uuid
from dataclasses import asdict, dataclass
from datetime import datetime, timezone
from decimal import Decimal
from pathlib import Path
from typing import Any, Dict, List, Literal, Optional, Sequence

from .user_story_tests import (
    CONTRACTS_SUBDIR,
    CONTRACT_SUFFIX,
    STORY_PREFIX,
    _parse_story_prompt_metadata,
)

SCHEMA_VERSION = "pdd.detect.stories.v1"
StoryVerdict = Literal["PASS", "FAIL", "UNKNOWN"]

_SECRET_VALUE_RE = re.compile(
    r"(?i)(?:bearer\s+|(?:api[_-]?key|token|password|secret)\s*[=:]\s*)[^\s,;]+"
)


def _redact_message(message: str) -> str:
    """Keep diagnostics useful without persisting provider secrets or local paths."""
    redacted = _SECRET_VALUE_RE.sub("[REDACTED]", message)
    home = str(Path.home())
    if home:
        redacted = redacted.replace(home, "~")
    # Provider exception text is not a stable API and may contain request data.
    # Keep only a bounded, single-line diagnostic after the explicit redactions.
    return " ".join(redacted.split())[:500]


@dataclass(frozen=True)
class StoryDiagnostic:
    """A stable diagnostic suitable for automation decisions."""

    code: str
    severity: Literal["warning", "error"]
    message: str
    retryable: bool = False


@dataclass(frozen=True)
class StoryDetectionItem:
    """One explicit verdict for one scoped story."""

    story: str
    contract: Optional[str]
    linked_prompts: List[str]
    verdict: StoryVerdict
    changes: List[Dict[str, Any]]
    warnings: List[StoryDiagnostic]
    errors: List[StoryDiagnostic]
    cost_usd: Optional[str] = None


def _portable_path(path: Path, project_root: Path) -> str:
    try:
        resolved = path.resolve()
        project = project_root.resolve()
    except (OSError, RuntimeError, ValueError):
        return "<unresolved>"
    try:
        return resolved.relative_to(project).as_posix()
    except ValueError:
        return (
            f"<outside-scope>/{resolved.name}" if resolved.name else "<outside-scope>"
        )


def _safe_reference(reference: str) -> str:
    """Avoid echoing absolute or traversal-bearing metadata into JSON."""
    try:
        path = Path(reference)
    except (TypeError, ValueError, OSError):
        return "<external>"
    if path.is_absolute() or ".." in path.parts:
        return path.name or "<external>"
    return reference


def _contract_for(story: Path) -> Path:
    slug = story.name
    if slug.startswith(STORY_PREFIX):
        slug = slug[len(STORY_PREFIX) :]
    if slug.endswith(".md"):
        slug = slug[:-3]
    return story.parent / CONTRACTS_SUBDIR / f"{slug}{CONTRACT_SUFFIX}"


def _normalize_changes(row: Dict[str, Any]) -> List[Dict[str, Any]]:
    raw = row.get("changes", row.get("changes_list", []))
    if not isinstance(raw, list):
        return [{"instruction": str(raw)}]
    normalized: List[Dict[str, Any]] = []
    for change in raw:
        normalized.append(
            change if isinstance(change, dict) else {"instruction": str(change)}
        )
    return normalized


def _normalize_cost(value: Any) -> Optional[str]:
    """Serialize an optional per-story cost without binary-float drift."""
    if value is None:
        return None
    try:
        return format(Decimal(str(value)), "f")
    except (ArithmeticError, ValueError, TypeError):
        return None


def _diagnostic_from_value(value: Any, *, default_code: str) -> StoryDiagnostic:
    """Adapt a legacy diagnostic value into the stable public shape."""
    if isinstance(value, dict):
        code = str(value.get("code") or default_code)
        severity_value = value.get("severity")
        severity: Literal["warning", "error"] = (
            "warning" if severity_value == "warning" else "error"
        )
        if code.startswith(("provider:", "auth:", "internal:")):
            message = "The detector provider reported an infrastructure error."
        else:
            message = _redact_message(
                str(value.get("message") or "The detector returned a diagnostic.")
            )
        retryable = bool(value.get("retryable", False))
        return StoryDiagnostic(code, severity, message, retryable)
    return StoryDiagnostic(default_code, "error", _redact_message(str(value)), False)


def _row_diagnostics(
    row: Dict[str, Any],
) -> tuple[List[StoryDiagnostic], List[StoryDiagnostic]]:
    """Read optional warning/error lists emitted by newer detector adapters."""
    warnings = row.get("warnings", [])
    errors = row.get("errors", [])
    if not isinstance(warnings, list):
        warnings = [warnings]
    if not isinstance(errors, list):
        errors = [errors]
    return (
        [
            _diagnostic_from_value(value, default_code="detector:WARNING")
            for value in warnings
        ],
        [
            _diagnostic_from_value(value, default_code="detector:ERROR")
            for value in errors
        ],
    )


def build_story_detection_document(
    *,
    story_files: Sequence[Path],
    raw_results: Sequence[Dict[str, Any]],
    passed: bool,
    total_cost: float,
    model: str,
    project_root: Path,
    stories_dir: Path,
    prompts_dir: Path,
    include_llm: bool,
    fail_fast: bool,
    read_only: bool,
    invocation_id: Optional[str] = None,
    started_at: Optional[datetime] = None,
) -> Dict[str, Any]:
    """Adapt legacy detector rows into a complete, fail-closed v1 document."""
    started = started_at or datetime.now(timezone.utc)
    by_story: Dict[str, List[Dict[str, Any]]] = {}
    for row in raw_results:
        key = str(Path(str(row.get("story", ""))).resolve())
        by_story.setdefault(key, []).append(row)

    items: List[StoryDetectionItem] = []
    for story in story_files:
        story_key = str(story.resolve())
        rows = by_story.pop(story_key, [])
        contract = _contract_for(story)
        linked = _parse_story_prompt_metadata(story.read_text(encoding="utf-8"))
        errors: List[StoryDiagnostic] = []
        warnings: List[StoryDiagnostic] = []
        changes: List[Dict[str, Any]] = []

        if not contract.is_file():
            errors.append(
                StoryDiagnostic(
                    "story:MISSING_CONTRACT", "error", "Story contract is missing."
                )
            )
        for prompt_ref in linked:
            candidates = (
                project_root / prompt_ref,
                prompts_dir / prompt_ref,
                prompts_dir / Path(prompt_ref).name,
            )
            resolved = next(
                (
                    candidate.resolve()
                    for candidate in candidates
                    if candidate.is_file()
                ),
                None,
            )
            if resolved is None:
                errors.append(
                    StoryDiagnostic(
                        "prompt:UNRESOLVED_LINK",
                        "error",
                        f"Linked prompt could not be resolved: {_safe_reference(prompt_ref)}",
                    )
                )
                continue
            try:
                resolved.relative_to(prompts_dir.resolve())
            except ValueError:
                errors.append(
                    StoryDiagnostic(
                        "prompt:OUTSIDE_SCOPE",
                        "error",
                        "Linked prompt is outside the requested prompt scope: "
                        f"{_safe_reference(prompt_ref)}",
                    )
                )
            if resolved.name.lower().endswith("_llm.prompt") and not include_llm:
                errors.append(
                    StoryDiagnostic(
                        "prompt:LLM_EXCLUDED",
                        "error",
                        "Linked LLM prompt requires --include-llm: "
                        f"{_safe_reference(prompt_ref)}",
                    )
                )
        if len(rows) != 1:
            code = (
                "detector:INCOMPLETE_RESULT"
                if not rows
                else "detector:CONFLICTING_VERDICT"
            )
            errors.append(
                StoryDiagnostic(
                    code,
                    "error",
                    "Detector did not return exactly one trustworthy row.",
                )
            )
            verdict: StoryVerdict = "UNKNOWN"
        else:
            row = rows[0]
            row_warnings, row_errors = _row_diagnostics(row)
            warnings.extend(row_warnings)
            errors.extend(row_errors)
            changes = _normalize_changes(row)
            row_error = row.get("error")
            if row_error:
                error_code = (
                    "prompt:UNRESOLVED_LINK"
                    if "prompt" in str(row_error).lower()
                    else "detector:INCOMPLETE_RESULT"
                )
                errors.append(
                    StoryDiagnostic(
                        error_code,
                        "error",
                        (
                            "A linked prompt could not be resolved."
                            if error_code == "prompt:UNRESOLVED_LINK"
                            else "The detector returned an error diagnostic."
                        ),
                    )
                )
                verdict = "UNKNOWN"
            elif row.get("passed") is True:
                verdict = "PASS"
            elif row.get("passed") is False:
                verdict = "FAIL"
            else:
                errors.append(
                    StoryDiagnostic(
                        "detector:INCOMPLETE_RESULT",
                        "error",
                        "Detector omitted a boolean verdict.",
                    )
                )
                verdict = "UNKNOWN"
            if verdict == "PASS" and changes:
                errors.append(
                    StoryDiagnostic(
                        "detector:CONFLICTING_VERDICT",
                        "error",
                        "Detector marked the story passed while returning proposed changes.",
                    )
                )
        if errors:
            verdict = "UNKNOWN"

        items.append(
            StoryDetectionItem(
                story=_portable_path(story, project_root),
                contract=(
                    _portable_path(contract, project_root)
                    if contract.is_file()
                    else None
                ),
                linked_prompts=sorted(linked),
                verdict=verdict,
                changes=changes,
                warnings=warnings,
                errors=errors,
                cost_usd=(
                    _normalize_cost(rows[0].get("cost_usd", rows[0].get("cost")))
                    if len(rows) == 1
                    else None
                ),
            )
        )

    for duplicate in by_story.values():
        if duplicate:
            items.append(
                StoryDetectionItem(
                    story=(
                        _portable_path(
                            Path(str(duplicate[0].get("story", ""))), project_root
                        )
                        if duplicate[0].get("story")
                        else "<unknown>"
                    ),
                    contract=None,
                    linked_prompts=[],
                    verdict="UNKNOWN",
                    changes=[],
                    warnings=[],
                    errors=[
                        StoryDiagnostic(
                            "scope:UNEXPECTED_STORY",
                            "error",
                            "Detector returned a story outside the requested scope.",
                        )
                    ],
                )
            )

    trustworthy_pass = (
        bool(items) and passed and all(item.verdict == "PASS" for item in items)
    )
    has_unknown = any(item.verdict == "UNKNOWN" for item in items)
    top_warnings = [diagnostic for item in items for diagnostic in item.warnings]
    top_errors = [diagnostic for item in items for diagnostic in item.errors]
    outcome = (
        "PASS"
        if trustworthy_pass
        else ("INCOMPLETE" if has_unknown else "STORY_FAILURE")
    )
    now = datetime.now(timezone.utc)
    return {
        "schema_version": SCHEMA_VERSION,
        "invocation_id": invocation_id or str(uuid.uuid4()),
        "scope": {
            "project_root": _portable_path(project_root, project_root),
            "stories_dir": _portable_path(stories_dir, project_root),
            "prompts_dir": _portable_path(prompts_dir, project_root),
            "include_llm": include_llm,
            "fail_fast": fail_fast,
            "read_only": read_only,
            "stories": [_portable_path(path, project_root) for path in story_files],
        },
        "outcome": outcome,
        "all_pass": trustworthy_pass,
        "results": [asdict(item) for item in items],
        "warnings": [asdict(diagnostic) for diagnostic in top_warnings],
        "errors": [asdict(diagnostic) for diagnostic in top_errors],
        "usage": {
            "cost_usd": format(Decimal(str(total_cost)), "f"),
            "cost_source": "actual",
            "model": model,
            "attempted_stories": len(raw_results),
            "completed_stories": sum(item.verdict != "UNKNOWN" for item in items),
        },
        "started_at": started.isoformat(),
        "finished_at": now.isoformat(),
        "duration_ms": max(0, int((now - started).total_seconds() * 1000)),
        "stop_reason": (
            "all_stories_passed"
            if trustworthy_pass
            else ("incomplete_result" if has_unknown else "stories_failed")
        ),
    }


def failure_document(
    *, outcome: str, code: str, message: str, retryable: bool
) -> Dict[str, Any]:
    """Return a schema-valid document when evaluation cannot start or finish."""
    now = datetime.now(timezone.utc).isoformat()
    return {
        "schema_version": SCHEMA_VERSION,
        "invocation_id": str(uuid.uuid4()),
        "scope": {},
        "outcome": outcome,
        "all_pass": False,
        "results": [],
        "warnings": [],
        "errors": [asdict(StoryDiagnostic(code, "error", message, retryable))],
        "usage": {
            "cost_usd": None,
            "cost_source": "unavailable",
            "model": "",
            "attempted_stories": 0,
            "completed_stories": 0,
        },
        "started_at": now,
        "finished_at": now,
        "duration_ms": 0,
        "stop_reason": code,
    }


def render_json(document: Dict[str, Any]) -> str:
    """Serialize a deterministic document without terminal formatting."""
    return json.dumps(
        document, sort_keys=True, separators=(",", ":"), ensure_ascii=False
    )


def write_json_atomic(path: Path, document: Dict[str, Any]) -> None:
    """Atomically replace *path* with a complete JSON document."""
    path.parent.mkdir(parents=True, exist_ok=True)
    fd, temporary = tempfile.mkstemp(prefix=f".{path.name}.", dir=str(path.parent))
    try:
        with os.fdopen(fd, "w", encoding="utf-8") as handle:
            handle.write(render_json(document) + "\n")
            handle.flush()
            os.fsync(handle.fileno())
        os.replace(temporary, path)
    except BaseException:
        try:
            os.unlink(temporary)
        except FileNotFoundError:
            pass
        raise
