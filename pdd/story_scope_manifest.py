"""Scope manifest parsing for pdd detect --stories --scope-manifest.

A manifest gives hosted callers and CI an exact, authorized set of stories,
contracts, and prompts to evaluate without discovering extra repository content.
"""
from __future__ import annotations

import json
import os
import re
from pathlib import Path
from typing import Dict, List, Optional, Tuple

from .story_detection_result import (
    SCOPE_SCHEMA_VERSION,
    StoryDetectionScope,
    StoryDiagnostic,
    DIAG_SCOPE_PATH_ESCAPE,
    DIAG_SCOPE_INVALID_DIR,
    scope_from_manifest,
)

# Only allow relative paths (no leading / or .. components).
_DOTDOT_RE = re.compile(r"(?:^|/)\.\.(?:/|$)")


class ManifestError(ValueError):
    """Raised when a scope manifest is invalid."""


def _safe_relative_path(raw: str, root: Path) -> Path:
    """Resolve *raw* relative to *root*, rejecting path-escape and absolute paths.

    Raises ManifestError for any path that would escape the project root via
    absolute paths, ``..`` traversal, or symlink escape.
    """
    if os.path.isabs(raw):
        raise ManifestError(
            f"Absolute paths are not allowed in scope manifests: {raw!r}"
        )
    if _DOTDOT_RE.search(raw):
        raise ManifestError(
            f"Path traversal ('..') is not allowed in scope manifests: {raw!r}"
        )
    candidate = (root / raw).resolve()
    try:
        candidate.relative_to(root.resolve())
    except ValueError:
        raise ManifestError(
            f"Path {raw!r} resolves outside the project root {root}: {candidate}"
        ) from None
    return candidate


def load_scope_manifest(
    manifest_path: str,
    *,
    project_root: Optional[str] = None,
) -> Tuple[StoryDetectionScope, List[StoryDiagnostic]]:
    """Parse a scope manifest file and return a validated StoryDetectionScope.

    Returns (scope, diagnostics). Diagnostics are warnings about non-existent
    optional files; fatal problems raise ManifestError.

    Manifest format::

        {
          "schema_version": "pdd.detect.stories.scope.v1",
          "stories": [
            {
              "story": "user_stories/story__refund.md",
              "contract": "user_stories/contracts/refund.contract.md",   // optional
              "prompts": ["prompts/refund_python.prompt"]
            }
          ]
        }
    """
    manifest_path_obj = Path(manifest_path)
    if not manifest_path_obj.exists():
        raise ManifestError(f"Scope manifest not found: {manifest_path}")
    if not manifest_path_obj.is_file():
        raise ManifestError(f"Scope manifest path is not a file: {manifest_path}")

    try:
        raw = manifest_path_obj.read_text(encoding="utf-8")
        data = json.loads(raw)
    except json.JSONDecodeError as exc:
        raise ManifestError(f"Scope manifest is not valid JSON: {exc}") from exc

    schema_ver = data.get("schema_version", "")
    if schema_ver != SCOPE_SCHEMA_VERSION:
        raise ManifestError(
            f"Unsupported scope manifest schema_version {schema_ver!r}; "
            f"expected {SCOPE_SCHEMA_VERSION!r}"
        )

    stories_raw: List[Dict] = data.get("stories", [])
    if not isinstance(stories_raw, list):
        raise ManifestError("Scope manifest 'stories' must be a list.")

    root = Path(project_root).resolve() if project_root else manifest_path_obj.parent.resolve()

    diagnostics: List[StoryDiagnostic] = []
    seen_stories: set = set()
    resolved_story_paths: List[str] = []
    resolved_prompt_paths: List[str] = []
    seen_prompts: set = set()

    for idx, entry in enumerate(stories_raw):
        if not isinstance(entry, dict):
            raise ManifestError(f"stories[{idx}] must be a JSON object.")

        story_raw = entry.get("story")
        if not story_raw:
            raise ManifestError(f"stories[{idx}] is missing required 'story' field.")

        story_path = _safe_relative_path(str(story_raw), root)
        story_key = str(story_path)
        if story_key in seen_stories:
            raise ManifestError(
                f"Duplicate story path in scope manifest: {story_raw!r}"
            )
        seen_stories.add(story_key)

        if not story_path.exists():
            from .story_detection_result import DIAG_SCOPE_INVALID_DIR  # noqa: F401
            diagnostics.append(
                StoryDiagnostic(
                    code=DIAG_SCOPE_INVALID_DIR,
                    severity="warning",
                    message=f"Story file not found: {story_path}",
                    related_paths=(str(story_path),),
                )
            )
        resolved_story_paths.append(str(story_path))

        prompts_raw = entry.get("prompts", [])
        if not isinstance(prompts_raw, list):
            raise ManifestError(f"stories[{idx}].prompts must be a list.")
        for prompt_raw in prompts_raw:
            prompt_path = _safe_relative_path(str(prompt_raw), root)
            prompt_key = str(prompt_path)
            if prompt_key in seen_prompts:
                continue  # duplicates across entries are silently deduped
            seen_prompts.add(prompt_key)
            resolved_prompt_paths.append(str(prompt_path))

    scope = scope_from_manifest(
        manifest_path=manifest_path,
        resolved_story_paths=tuple(resolved_story_paths),
        resolved_prompt_paths=tuple(resolved_prompt_paths),
    )
    return scope, diagnostics
