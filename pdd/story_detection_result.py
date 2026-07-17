"""Versioned, automation-safe results for ``pdd detect --stories``."""

from __future__ import annotations

import json
import math
import os
import re
import tempfile
import uuid
from collections.abc import Mapping
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

_SECRET_FIELD_NAMES = frozenset(
    {"accesstoken", "apikey", "authorization", "password", "secret", "token"}
)
_QUOTED_SECRET_FIELD_RE = re.compile(
    r"""(?ix)(?P<label>["']?(?:access[_-]?token|api[_-]?key|token|password|secret|authorization)["']?\s*[:=]\s*)
        (?P<quote>["'])(?:\\.|(?!(?P=quote)).)*(?P=quote)"""
)
_AUTHORIZATION_VALUE_RE = re.compile(
    r"(?i)(authorization\s*[:=]\s*)(?:bearer\s+)?[^\s,;]+"
)
_SECRET_VALUE_RE = re.compile(
    r"(?i)(?:bearer\s+|(?:access[_-]?token|api[_-]?key|token|password|secret)\s*[=:]\s*)[^\s,;]+"
)
_LOCAL_PATH_RE = re.compile(r"(?<![\w])/(?:Users|home|private|tmp|var)/[^\s,;]+")
_DIAGNOSTIC_CODE_RE = re.compile(r"[a-z][a-z0-9_-]{0,31}:[A-Z][A-Z0-9_-]{0,63}\Z")


def _is_secret_field(key: str) -> bool:
    """Recognize credential keys despite common case and separator variants."""
    normalized = re.sub(r"[^a-z0-9]", "", key.lower())
    return normalized in _SECRET_FIELD_NAMES or normalized.endswith(("secret", "token"))


def _redact_message(message: str) -> str:
    """Keep diagnostics useful without persisting provider secrets or local paths."""
    redacted = _QUOTED_SECRET_FIELD_RE.sub(
        lambda match: (
            f"{match.group('label')}{match.group('quote')}[REDACTED]{match.group('quote')}"
        ),
        message,
    )
    redacted = _AUTHORIZATION_VALUE_RE.sub(r"\1[REDACTED]", redacted)
    redacted = _SECRET_VALUE_RE.sub("[REDACTED]", redacted)
    redacted = _LOCAL_PATH_RE.sub("[REDACTED_PATH]", redacted)
    home = str(Path.home())
    if home:
        redacted = redacted.replace(home, "~")
    # Provider exception text is not a stable API and may contain request data.
    # Keep only a bounded, single-line diagnostic after the explicit redactions.
    return " ".join(redacted.split())[:500]


def _safe_diagnostic_code(value: Any, default: str) -> str:
    """Keep untrusted diagnostic identifiers bounded and credential-free."""
    candidate = str(value or "")
    normalized = re.sub(r"[^a-z0-9]", "", candidate.lower())
    if (
        not _DIAGNOSTIC_CODE_RE.fullmatch(candidate)
        or any(marker in normalized for marker in ("apikey", "authorization", "password", "secret", "token", "bearer"))
    ):
        return default
    return candidate


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


def _is_regular_in_scope(path: Path, root: Path) -> bool:
    """Require a non-symlink regular file whose resolved path stays in *root*."""
    if path.is_symlink() or not path.is_file():
        return False
    try:
        path.resolve().relative_to(root.resolve())
    except (OSError, RuntimeError, ValueError):
        return False
    return True


def _normalize_changes(row: Dict[str, Any]) -> List[Dict[str, Any]]:
    def sanitize(key: str, value: Any) -> Any:
        if _is_secret_field(key):
            return "[REDACTED]"
        if isinstance(value, str):
            if key.lower() in {"prompt", "prompt_name", "prompt_file", "path"}:
                return _safe_reference(value)
            return _redact_message(value)
        if isinstance(value, dict):
            return {
                str(nested_key): sanitize(str(nested_key), nested_value)
                for nested_key, nested_value in value.items()
            }
        if isinstance(value, (set, frozenset)):
            return [
                sanitize(key, nested_value) for nested_value in sorted(value, key=repr)
            ]
        if isinstance(value, (list, tuple)):
            return [sanitize(key, nested_value) for nested_value in value]
        if isinstance(value, float) and not math.isfinite(value):
            return None
        if value is None or isinstance(value, (bool, int, float)):
            return value
        if isinstance(value, Mapping):
            return {
                str(nested_key): sanitize(str(nested_key), nested_value)
                for nested_key, nested_value in value.items()
            }
        return _redact_message(str(value))

    raw = row.get("changes", row.get("changes_list", []))
    if not isinstance(raw, list):
        return [{"instruction": _redact_message(str(raw))}]
    normalized: List[Dict[str, Any]] = []
    for change in raw:
        if not isinstance(change, dict):
            normalized.append({"instruction": _redact_message(str(change))})
            continue
        normalized.append(
            {str(key): sanitize(str(key), value) for key, value in change.items()}
        )
    return normalized


def _normalize_cost(value: Any) -> Optional[str]:
    """Serialize an optional per-story cost without binary-float drift."""
    if value is None:
        return None
    try:
        decimal_value = Decimal(str(value))
        if not decimal_value.is_finite() or decimal_value < 0:
            return None
        return format(decimal_value, "f")
    except (ArithmeticError, ValueError, TypeError):
        return None


def _diagnostic_from_value(value: Any, *, default_code: str) -> StoryDiagnostic:
    """Adapt a legacy diagnostic value into the stable public shape."""
    if isinstance(value, dict):
        code = _safe_diagnostic_code(value.get("code"), default_code)
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
    contract_files: Mapping[Path, Path] | None = None,
    allowed_prompt_files: Sequence[Path] | None = None,
    manifest_story_prompts: Mapping[Path, Sequence[Path]] | None = None,
    include_llm: bool,
    fail_fast: bool,
    read_only: bool,
    invocation_id: Optional[str] = None,
    started_at: Optional[datetime] = None,
) -> Dict[str, Any]:
    """Adapt legacy detector rows into a complete, fail-closed v1 document."""
    started = started_at or datetime.now(timezone.utc)
    by_story: Dict[str, List[Dict[str, Any]]] = {}
    malformed_rows = 0
    if not isinstance(raw_results, (list, tuple)):
        malformed_rows = 1
        raw_rows: Sequence[Any] = ()
    else:
        raw_rows = raw_results
    for row in raw_rows:
        if not isinstance(row, dict):
            malformed_rows += 1
            continue
        try:
            key = str(Path(str(row.get("story", ""))).resolve())
        except (OSError, RuntimeError, ValueError, TypeError):
            malformed_rows += 1
            continue
        by_story.setdefault(key, []).append(row)

    items: List[StoryDetectionItem] = []
    for story in story_files:
        try:
            story_key = str(story.resolve())
        except (OSError, RuntimeError, ValueError):
            story_key = "<invalid-story-path>"
        rows = by_story.pop(story_key, [])
        story_resolved = story.resolve()
        contract = (
            contract_files.get(story_resolved, _contract_for(story))
            if contract_files is not None
            else _contract_for(story)
        )
        errors: List[StoryDiagnostic] = []
        warnings: List[StoryDiagnostic] = []
        changes: List[Dict[str, Any]] = []
        item_cost: Optional[str] = None
        try:
            linked_refs = _parse_story_prompt_metadata(
                story.read_text(encoding="utf-8")
            )
        except (OSError, UnicodeError, ValueError):
            linked_refs = []
            errors.append(
                StoryDiagnostic(
                    "story:UNREADABLE",
                    "error",
                    "Story file could not be read as UTF-8.",
                )
            )
        linked = sorted(_safe_reference(ref) for ref in linked_refs)

        contract_valid = _is_regular_in_scope(
            contract,
            stories_dir if contract_files is None else project_root,
        )
        if not contract_valid:
            errors.append(
                StoryDiagnostic(
                    (
                        "story:INVALID_CONTRACT"
                        if contract.exists() or contract.is_symlink()
                        else "story:MISSING_CONTRACT"
                    ),
                    "error",
                    (
                        "Story contract is not a regular in-scope file."
                        if contract.exists() or contract.is_symlink()
                        else "Story contract is missing."
                    ),
                )
            )
        for prompt_ref in linked_refs:
            if allowed_prompt_files is not None:
                allowed = tuple(Path(candidate).resolve() for candidate in allowed_prompt_files)
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
                        and candidate.resolve() in allowed
                    ),
                    None,
                )
                prompt_in_scope = resolved is not None
            else:
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
                prompt_in_scope = False
            if resolved is None:
                errors.append(
                    StoryDiagnostic(
                        "prompt:UNRESOLVED_LINK",
                        "error",
                        f"Linked prompt could not be resolved: {_safe_reference(prompt_ref)}",
                    )
                )
                continue
            if allowed_prompt_files is not None:
                prompt_in_scope = resolved in allowed
            else:
                try:
                    resolved.relative_to(prompts_dir.resolve())
                    prompt_in_scope = True
                except ValueError:
                    prompt_in_scope = False
            if not prompt_in_scope:
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
        if manifest_story_prompts is not None:
            expected = {
                Path(path).resolve()
                for path in manifest_story_prompts.get(story_resolved, ())
            }
            actual: set[Path] = set()
            for prompt_ref in linked_refs:
                for candidate in (
                    project_root / prompt_ref,
                    prompts_dir / prompt_ref,
                    prompts_dir / Path(prompt_ref).name,
                ):
                    if candidate.is_file():
                        actual.add(candidate.resolve())
                        break
            if actual != expected:
                errors.append(
                    StoryDiagnostic(
                        "scope:MANIFEST_MISMATCH",
                        "error",
                        "Story prompt metadata does not match the exact scope manifest.",
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
            if "cost_usd" in row or "cost" in row:
                item_cost = _normalize_cost(row.get("cost_usd", row.get("cost")))
                if item_cost is None:
                    errors.append(
                        StoryDiagnostic(
                            "billing:INVALID_STORY_COST",
                            "error",
                            "Detector returned malformed per-story cost data.",
                            retryable=True,
                        )
                    )
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
                    _portable_path(contract, project_root) if contract_valid else None
                ),
                linked_prompts=sorted(linked),
                verdict=verdict,
                changes=changes,
                warnings=warnings,
                errors=errors,
                cost_usd=item_cost,
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

    normalized_model = model.strip() if isinstance(model, str) else ""
    valid_model = bool(normalized_model)
    aggregate_cost = _normalize_cost(total_cost)
    top_warnings = [diagnostic for item in items for diagnostic in item.warnings]
    top_errors = [diagnostic for item in items for diagnostic in item.errors]
    if malformed_rows:
        top_errors.append(
            StoryDiagnostic(
                "detector:MALFORMED_RESULT",
                "error",
                "Detector returned malformed story result rows.",
            )
        )
    if not isinstance(passed, bool):
        top_errors.append(
            StoryDiagnostic(
                "detector:MALFORMED_RESULT",
                "error",
                "Detector returned a non-boolean aggregate verdict.",
            )
        )
    if not valid_model:
        top_errors.append(
            StoryDiagnostic(
                "provenance:INVALID_MODEL",
                "error",
                "Detector returned invalid model provenance.",
            )
        )
    if aggregate_cost is None:
        top_errors.append(
            StoryDiagnostic(
                "billing:UNAVAILABLE",
                "error",
                "Detector cost was unavailable or malformed.",
                retryable=True,
            )
        )
    trustworthy_pass = (
        bool(items)
        and passed is True
        and not malformed_rows
        and valid_model
        and aggregate_cost is not None
        and all(item.verdict == "PASS" for item in items)
    )
    has_unknown = any(item.verdict == "UNKNOWN" for item in items) or bool(top_errors)
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
            "contracts": [
                _portable_path(contract_files.get(path.resolve(), _contract_for(path)), project_root)
                if contract_files is not None
                else _portable_path(_contract_for(path), project_root)
                for path in story_files
            ],
            "prompts": [
                _portable_path(path, project_root)
                for path in (allowed_prompt_files or ())
            ],
        },
        "outcome": outcome,
        "all_pass": trustworthy_pass,
        "results": [asdict(item) for item in items],
        "warnings": [asdict(diagnostic) for diagnostic in top_warnings],
        "errors": [asdict(diagnostic) for diagnostic in top_errors],
        "usage": {
            "cost_usd": aggregate_cost,
            "cost_source": "actual" if aggregate_cost is not None else "unavailable",
            "model": normalized_model,
            "attempted_stories": len(raw_rows),
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
    safe_code = _safe_diagnostic_code(code, "internal:ERROR")
    return {
        "schema_version": SCHEMA_VERSION,
        "invocation_id": str(uuid.uuid4()),
        "scope": {},
        "outcome": outcome,
        "all_pass": False,
        "results": [],
        "warnings": [],
        "errors": [
            asdict(
                StoryDiagnostic(
                    safe_code, "error", _redact_message(message), retryable
                )
            )
        ],
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
        "stop_reason": safe_code,
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
