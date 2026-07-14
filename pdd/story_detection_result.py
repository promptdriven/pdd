"""Typed, versioned result objects for pdd detect --stories structured output.

These models are the single source of truth for the JSON schema emitted by the
--json / --json-output options. Internal callers (CLI renderer, evidence writer)
must consume these types; they must never independently recompute aggregate
status or cost from raw dictionaries.
"""
from __future__ import annotations

import uuid
from dataclasses import dataclass, field
from decimal import Decimal
from pathlib import Path
from typing import Literal, Optional, Tuple

SCHEMA_VERSION = "pdd.detect.stories.v1"
SCOPE_SCHEMA_VERSION = "pdd.detect.stories.scope.v1"

StoryVerdict = Literal["PASS", "FAIL", "UNKNOWN"]
DiagnosticSeverity = Literal["error", "warning", "info"]
CostSource = Literal["actual", "estimated", "unavailable"]

# Stable diagnostic codes for machine consumers.
DIAG_SCOPE_EMPTY = "scope:EMPTY"
DIAG_SCOPE_PATH_ESCAPE = "scope:PATH_ESCAPE"
DIAG_SCOPE_INVALID_DIR = "scope:INVALID_DIR"
DIAG_STORY_MISSING_CONTRACT = "story:MISSING_CONTRACT"
DIAG_STORY_STALE_CONTRACT_HASH = "story:STALE_CONTRACT_HASH"
DIAG_PROMPT_UNRESOLVED_LINK = "prompt:UNRESOLVED_LINK"
DIAG_PROMPT_OUTSIDE_SCOPE = "prompt:OUTSIDE_SCOPE"
DIAG_DETECTOR_INCOMPLETE_RESULT = "detector:INCOMPLETE_RESULT"
DIAG_DETECTOR_CONFLICTING_VERDICT = "detector:CONFLICTING_VERDICT"
DIAG_AUTH_NON_INTERACTIVE = "auth:NON_INTERACTIVE_CREDENTIALS_MISSING"
DIAG_PROVIDER_UNAVAILABLE = "provider:UNAVAILABLE"
DIAG_PROVIDER_TIMEOUT = "provider:TIMEOUT"
DIAG_INTERNAL_ERROR = "internal:UNEXPECTED_ERROR"

# Top-level outcome codes for the run as a whole.
StoryDetectionOutcome = Literal[
    "all_pass",
    "story_fail",
    "config_error",
    "auth_error",
    "provider_error",
    "internal_error",
]


@dataclass(frozen=True)
class StoryDiagnostic:
    """A structured diagnostic entry with a stable code and optional related paths."""

    code: str
    severity: DiagnosticSeverity
    message: str
    retryable: bool = False
    related_paths: Tuple[str, ...] = field(default_factory=tuple)

    def to_dict(self) -> dict:
        return {
            "code": self.code,
            "severity": self.severity,
            "message": self.message,
            "retryable": self.retryable,
            "related_paths": list(self.related_paths),
        }


@dataclass(frozen=True)
class StoryPromptChange:
    """A proposed change to a prompt file discovered during story validation."""

    prompt_name: str
    change_instructions: str

    def to_dict(self) -> dict:
        return {
            "prompt_name": self.prompt_name,
            "change_instructions": self.change_instructions,
        }


@dataclass(frozen=True)
class StoryDetectionItem:
    """Result for a single story evaluated during a detection run."""

    story_path: str
    contract_path: Optional[str]
    linked_prompt_paths: Tuple[str, ...]
    verdict: StoryVerdict
    changes: Tuple[StoryPromptChange, ...]
    warnings: Tuple[StoryDiagnostic, ...]
    errors: Tuple[StoryDiagnostic, ...]

    def to_dict(self) -> dict:
        return {
            "story_path": self.story_path,
            "contract_path": self.contract_path,
            "linked_prompt_paths": list(self.linked_prompt_paths),
            "verdict": self.verdict,
            "changes": [c.to_dict() for c in self.changes],
            "warnings": [w.to_dict() for w in self.warnings],
            "errors": [e.to_dict() for e in self.errors],
        }


@dataclass(frozen=True)
class StoryDetectionScope:
    """Normalized, validated scope used for a detection run."""

    stories_dir: Optional[str]
    prompts_dirs: Tuple[str, ...]
    story_paths: Tuple[str, ...]
    prompt_paths: Tuple[str, ...]
    manifest_path: Optional[str]
    include_llm: bool

    def to_dict(self) -> dict:
        return {
            "stories_dir": self.stories_dir,
            "prompts_dirs": list(self.prompts_dirs),
            "story_paths": list(self.story_paths),
            "prompt_paths": list(self.prompt_paths),
            "manifest_path": self.manifest_path,
            "include_llm": self.include_llm,
        }


@dataclass(frozen=True)
class StoryDetectionUsage:
    """Cost and provenance for the detection run."""

    total_cost: str  # Decimal-as-string to avoid float drift
    cost_source: CostSource
    model: str
    stories_attempted: int
    stories_completed: int

    def to_dict(self) -> dict:
        return {
            "total_cost": self.total_cost,
            "cost_source": self.cost_source,
            "model": self.model,
            "stories_attempted": self.stories_attempted,
            "stories_completed": self.stories_completed,
        }


@dataclass(frozen=True)
class StoryDetectionRun:
    """Complete structured result for one invocation of pdd detect --stories."""

    schema_version: str
    invocation_id: str
    outcome: StoryDetectionOutcome
    scope: StoryDetectionScope
    items: Tuple[StoryDetectionItem, ...]
    all_pass: bool
    usage: StoryDetectionUsage
    stop_reason: str
    diagnostics: Tuple[StoryDiagnostic, ...]

    def to_dict(self) -> dict:
        return {
            "schema_version": self.schema_version,
            "invocation_id": self.invocation_id,
            "outcome": self.outcome,
            "all_pass": self.all_pass,
            "stop_reason": self.stop_reason,
            "scope": self.scope.to_dict(),
            "items": [item.to_dict() for item in self.items],
            "usage": self.usage.to_dict(),
            "diagnostics": [d.to_dict() for d in self.diagnostics],
        }

    @classmethod
    def make_error_run(
        cls,
        *,
        outcome: StoryDetectionOutcome,
        code: str,
        message: str,
        invocation_id: Optional[str] = None,
        retryable: bool = False,
    ) -> "StoryDetectionRun":
        """Build a minimal failure run for infrastructure/auth/config errors."""
        diag = StoryDiagnostic(
            code=code,
            severity="error",
            message=message,
            retryable=retryable,
        )
        scope = StoryDetectionScope(
            stories_dir=None,
            prompts_dirs=(),
            story_paths=(),
            prompt_paths=(),
            manifest_path=None,
            include_llm=False,
        )
        usage = StoryDetectionUsage(
            total_cost="0",
            cost_source="unavailable",
            model="",
            stories_attempted=0,
            stories_completed=0,
        )
        return cls(
            schema_version=SCHEMA_VERSION,
            invocation_id=invocation_id or str(uuid.uuid4()),
            outcome=outcome,
            scope=scope,
            items=(),
            all_pass=False,
            usage=usage,
            stop_reason=message,
            diagnostics=(diag,),
        )


def build_run_from_legacy(
    *,
    passed: bool,
    results: list,
    total_cost: float,
    model_name: str,
    scope: StoryDetectionScope,
    invocation_id: str,
    fail_fast_triggered: bool = False,
    run_diagnostics: Tuple[StoryDiagnostic, ...] = (),
) -> StoryDetectionRun:
    """Convert the legacy Tuple[bool, List[Dict], float, str] into a StoryDetectionRun.

    This adapter keeps existing callers of run_user_story_tests working while
    allowing the CLI renderer and evidence writer to consume the typed object.
    """
    items: list[StoryDetectionItem] = []
    any_unknown = False

    for r in results:
        story_path = r.get("story", "")
        raw_passed = r.get("passed")
        changes_raw = r.get("changes") or []
        error_msg = r.get("error")

        if error_msg is not None:
            verdict: StoryVerdict = "FAIL"
            errors: Tuple[StoryDiagnostic, ...] = (
                StoryDiagnostic(
                    code=DIAG_PROMPT_UNRESOLVED_LINK,
                    severity="error",
                    message=error_msg,
                ),
            )
            changes: Tuple[StoryPromptChange, ...] = ()
        elif raw_passed is True:
            verdict = "PASS"
            errors = ()
            changes = ()
        elif raw_passed is False:
            verdict = "FAIL"
            errors = ()
            changes = tuple(
                StoryPromptChange(
                    prompt_name=c.get("prompt_name", ""),
                    change_instructions=c.get("change_instructions", ""),
                )
                for c in changes_raw
            )
        else:
            verdict = "UNKNOWN"
            any_unknown = True
            errors = ()
            changes = ()

        # Contract path is not returned by the legacy API; leave it None.
        item = StoryDetectionItem(
            story_path=story_path,
            contract_path=None,
            linked_prompt_paths=tuple(r.get("linked_prompt_paths") or []),
            verdict=verdict,
            changes=changes,
            warnings=(),
            errors=errors,
        )
        items.append(item)

    all_pass = passed and not any_unknown

    if fail_fast_triggered and not all_pass:
        stop_reason = "fail_fast"
    elif not all_pass:
        stop_reason = "story_fail"
    else:
        stop_reason = "completed"

    outcome: StoryDetectionOutcome = "all_pass" if all_pass else "story_fail"

    # Represent cost as a Decimal string to avoid float serialization drift.
    try:
        cost_str = str(Decimal(str(total_cost)).normalize())
    except Exception:  # pylint: disable=broad-except
        cost_str = str(total_cost)

    usage = StoryDetectionUsage(
        total_cost=cost_str,
        cost_source="actual",
        model=model_name,
        stories_attempted=len(results),
        stories_completed=sum(1 for r in results if r.get("passed") is not None),
    )

    return StoryDetectionRun(
        schema_version=SCHEMA_VERSION,
        invocation_id=invocation_id,
        outcome=outcome,
        scope=scope,
        items=tuple(items),
        all_pass=all_pass,
        usage=usage,
        stop_reason=stop_reason,
        diagnostics=run_diagnostics,
    )


def scope_from_dirs(
    *,
    stories_dir: Optional[str],
    prompts_dir: Optional[str],
    story_paths: Tuple[str, ...] = (),
    prompt_paths: Tuple[str, ...] = (),
    include_llm: bool = False,
) -> StoryDetectionScope:
    """Build a StoryDetectionScope from directory-discovery parameters."""
    return StoryDetectionScope(
        stories_dir=stories_dir,
        prompts_dirs=(prompts_dir,) if prompts_dir else (),
        story_paths=story_paths,
        prompt_paths=prompt_paths,
        manifest_path=None,
        include_llm=include_llm,
    )


def scope_from_manifest(
    *,
    manifest_path: str,
    resolved_story_paths: Tuple[str, ...],
    resolved_prompt_paths: Tuple[str, ...],
    include_llm: bool = False,
) -> StoryDetectionScope:
    """Build a StoryDetectionScope from a scope manifest file."""
    return StoryDetectionScope(
        stories_dir=None,
        prompts_dirs=(),
        story_paths=resolved_story_paths,
        prompt_paths=resolved_prompt_paths,
        manifest_path=manifest_path,
        include_llm=include_llm,
    )
