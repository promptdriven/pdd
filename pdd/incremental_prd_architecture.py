"""Incrementally propagate PRD changes into architecture.json and prompts.

The LLM only proposes a structured patch. This module owns validation,
merge semantics, file writes, and prompt update orchestration.
"""
from __future__ import annotations

import copy
import difflib
import hashlib
import json
import os
import re
import subprocess
import tempfile
from contextlib import contextmanager
from dataclasses import dataclass, field
from datetime import datetime, timezone
from pathlib import Path
from typing import Any, Callable, Dict, Iterator, List, Optional, Sequence, Tuple

from pydantic import BaseModel, Field, StrictInt

from . import DEFAULT_STRENGTH, DEFAULT_TIME
from .architecture_registry import extract_modules
from .architecture_sync import generate_tags_from_architecture
from .change import change
from .detect_change import detect_change
from .json_atomic import atomic_write_json
from .llm_invoke import llm_invoke
from .load_prompt_template import load_prompt_template
from .preprocess import preprocess


_GITHUB_ISSUE_RE = re.compile(
    r"(?:https?://)?(?:www\.)?github\.com/([^/]+)/([^/]+)/issues/(\d+)"
)

# Marker embedded in pdd's own incremental status comments so they can be
# filtered out of any subsequent PRD-content read. Kept here as the source of
# truth; agentic_architecture imports it for posting.
INCREMENTAL_STATUS_MARKER = "<!-- PDD-INCREMENTAL-STATUS -->"


_ALLOWED_MODIFY_FIELDS = {
    "reason",
    "description",
    "interface",
    "filepath",
    "tags",
    "priority",
}

_SAFE_PATH_SEGMENT = r"[A-Za-z0-9_](?:[A-Za-z0-9._-]*[A-Za-z0-9_])?"
_SAFE_RELATIVE_PATH_PATTERN = re.compile(rf"{_SAFE_PATH_SEGMENT}(/{_SAFE_PATH_SEGMENT})*")
_CODE_UNAVAILABLE_MESSAGE = "No existing code file is available for this prompt yet."
_SENSITIVE_FILE_BASENAMES = {
    ".env",
    ".env.local",
    ".env.development",
    ".env.production",
    ".netrc",
    ".npmrc",
    ".pypirc",
    "credentials.json",
    "credentials.yaml",
    "credentials.yml",
    "id_dsa",
    "id_ecdsa",
    "id_ed25519",
    "id_rsa",
    "secret.json",
    "secret.yaml",
    "secret.yml",
    "secrets.json",
    "secrets.yaml",
    "secrets.yml",
    "service-account.json",
    "service_account.json",
}
_SENSITIVE_FILE_SUFFIXES = (".key", ".pem", ".p12", ".pfx")


class ModuleToAdd(BaseModel):
    """A complete architecture entry for a newly required module."""

    filename: str = Field(description="New prompt filename, e.g. audit_logger_python.prompt")
    reason: str = Field(description="Short reason for the module.")
    description: Optional[str] = Field(default=None, description="Longer module description.")
    dependencies: List[str] = Field(
        default_factory=list,
        description="Prompt filenames this module depends on.",
    )
    interface: Dict[str, Any] = Field(
        default_factory=dict,
        description="Architecture interface contract.",
    )
    filepath: Optional[str] = Field(default=None, description="Target code filepath when known.")
    tags: List[str] = Field(
        default_factory=list,
        description="Module tags such as module/python/api.",
    )
    priority: Optional[StrictInt] = Field(default=None, description="Optional architecture priority.")
    requirements: List[str] = Field(
        default_factory=list,
        description="Concrete Requirements bullets to seed the new prompt file.",
    )


class ModuleRemoval(BaseModel):
    """A module removal that must be justified by an explicit PRD removal."""

    filename: str
    justification: str = Field(
        description="Quote or explain the PRD removal requiring this module removal."
    )


class ModuleModification(BaseModel):
    """A selective update to an existing architecture entry."""

    filename: str
    changes: Dict[str, Any] = Field(
        default_factory=dict,
        description=(
            "Only changed architecture fields. Do not include dependencies here; "
            "use dependency_updates instead."
        ),
    )
    justification: str = Field(default="", description="Why this specific module must change.")


class DependencyUpdate(BaseModel):
    """A surgical dependency add/remove operation for one existing module."""

    source: str = Field(description="Architecture filename whose dependencies should change.")
    add: List[str] = Field(default_factory=list, description="Dependency prompt filenames to add.")
    remove: List[str] = Field(default_factory=list, description="Dependency prompt filenames to remove.")
    justification: str = Field(default="", description="Why this dependency update is needed.")


class PatchConflict(BaseModel):
    """A human-review item. Conflicts block automatic writes."""

    filename: Optional[str] = None
    field: Optional[str] = None
    reason: str


class ArchitecturePatch(BaseModel):
    """Structured LLM output for incremental PRD architecture propagation."""

    requires_full_regeneration: bool = Field(
        default=False,
        description="True when the PRD change is too broad for a targeted patch.",
    )
    rationale: str = Field(default="", description="Brief patch rationale.")
    modules_to_add: List[ModuleToAdd] = Field(default_factory=list)
    modules_to_remove: List[ModuleRemoval] = Field(default_factory=list)
    modules_to_modify: List[ModuleModification] = Field(default_factory=list)
    dependency_updates: List[DependencyUpdate] = Field(default_factory=list)
    conflicts: List[PatchConflict] = Field(default_factory=list)


@dataclass
class PatchApplication:
    """Result of deterministic patch validation/application."""

    raw_architecture: Any
    modules: List[Dict[str, Any]]
    changed_filenames: List[str]
    architecture_diff: str
    warnings: List[str] = field(default_factory=list)


@dataclass
class IncrementalPrdResult:
    """Top-level command result."""

    success: bool
    message: str
    cost: float
    model: str
    changed_files: List[str]
    architecture_diff: str = ""
    prompt_updates: List[str] = field(default_factory=list)
    warnings: List[str] = field(default_factory=list)


@dataclass
class _PromptPreview:
    """Proposed change to a prompt file. Used for dry-run reporting and writes."""

    path: Path
    kind: str  # "tags" | "created" | "requirements" | "deleted"
    before: str  # "" for newly created files
    after: str


def run_incremental_prd_propagation(
    prd_source: str,
    *,
    architecture_path: Path | str = "architecture.json",
    prompts_dir: Path | str = "prompts",
    project_root: Path | str | None = None,
    issue_content: Optional[str] = None,
    dry_run: bool = False,
    verbose: bool = False,
    quiet: bool = False,
    strength: float = DEFAULT_STRENGTH,
    temperature: float = 0.0,
    time: float = DEFAULT_TIME,
    max_patch_attempts: int = 3,
    update_prompt_requirements: bool = True,
    generate_new_prompts: bool = True,
) -> Tuple[bool, str, float, str, List[str]]:
    """Run the incremental PRD -> architecture -> prompt propagation workflow."""
    arch_path = Path(architecture_path).resolve()
    prompt_root = Path(prompts_dir).resolve()
    state_root = Path(project_root).resolve() if project_root else arch_path.parent

    source_key, current_prd = _read_prd_source(
        prd_source,
        state_root,
        issue_content=issue_content,
    )
    previous_prd = _previous_prd_content(
        source_key,
        prd_source,
        state_root,
        current_prd,
    )
    prd_diff = _build_prd_diff(previous_prd, current_prd, source_key)

    if not prd_diff.strip():
        message = f"No PRD changes detected for {source_key}."
        changed_files: List[str] = []
        if not dry_run and _prd_state_contains_raw_content(state_root):
            _save_prd_snapshot(state_root, source_key, current_prd)
            changed_files.append(".pdd/meta/prd_hashes.json")
            message += " Migrated PRD metadata to hash-only storage."
        return True, message, 0.0, "", changed_files

    # Atomic baseline capture (F14): read the architecture bytes ONCE and
    # parse from the same buffer. If we used `_load_architecture` followed by
    # a separate `read_bytes`, a concurrent committer could land between the
    # two reads — leaving us with parsed content from the old version and
    # baseline bytes from the new version, which would later let the
    # concurrent-modification guard pass while our patch was actually
    # computed against the stale parse.
    raw_architecture, arch_baseline_bytes = _load_architecture_with_bytes(arch_path)
    before_modules = copy.deepcopy(extract_modules(raw_architecture))
    if not before_modules:
        raise ValueError(f"No modules found in {arch_path}")

    cost = 0.0
    model = ""
    validation_errors: List[str] = []
    application: Optional[PatchApplication] = None
    patch: Optional[ArchitecturePatch] = None

    for attempt in range(1, max(1, max_patch_attempts) + 1):
        patch, patch_cost, patch_model = _ask_llm_for_patch(
            prd_source=source_key,
            prd_diff=prd_diff,
            architecture=raw_architecture,
            strength=strength,
            temperature=temperature,
            time=time,
            verbose=verbose,
            validation_errors=validation_errors,
        )
        cost += patch_cost
        if patch_model:
            model = patch_model

        if patch.requires_full_regeneration:
            return (
                False,
                "Incremental architecture patch declined: full regeneration recommended.",
                cost,
                model,
                [],
            )

        if patch.conflicts:
            conflict_text = "; ".join(conflict.reason for conflict in patch.conflicts)
            return (
                False,
                f"Incremental architecture patch has conflicts requiring review: {conflict_text}",
                cost,
                model,
                [],
            )

        try:
            application = apply_architecture_patch(raw_architecture, patch)
            break
        except ValueError as exc:
            validation_errors.append(str(exc))
            if verbose and not quiet:
                print(f"Patch attempt {attempt} rejected: {exc}")

    if application is None or patch is None:
        error_text = "; ".join(validation_errors) or "unknown validation failure"
        return (
            False,
            f"LLM patch failed validation after {max_patch_attempts} attempt(s): {error_text}",
            cost,
            model,
            [],
        )

    # ---- COMPUTE PHASE: build all proposed changes in memory ---------------
    # Failures raised here happen before any disk write, so the project is left
    # in its pre-run state (transactional commit phase below).
    all_previews: List[_PromptPreview] = []

    removed_previews = _delete_prompt_files_for_removed_modules(
        patch.modules_to_remove,
        prompt_root,
    )
    all_previews.extend(removed_previews)

    tag_previews = _sync_tags_for_changed_prompts(
        application.modules,
        application.changed_filenames,
        prompt_root,
    )
    all_previews.extend(tag_previews)

    created_previews: List[_PromptPreview] = []
    if generate_new_prompts:
        created_previews = _generate_prompt_files_for_new_modules(
            patch.modules_to_add,
            prompt_root,
            project_root=arch_path.parent,
        )
        all_previews.extend(created_previews)

    requirement_previews: List[_PromptPreview] = []
    if update_prompt_requirements and application.architecture_diff:
        try:
            requirement_previews, prompt_cost, prompt_model = _update_prompt_requirements(
                before_modules=before_modules,
                after_modules=application.modules,
                architecture_diff=application.architecture_diff,
                prompts_dir=prompt_root,
                strength=strength,
                temperature=temperature,
                time=time,
                verbose=verbose,
            )
        except Exception as exc:
            return (
                False,
                f"Prompt requirement update failed before any disk write: {exc}",
                cost,
                model,
                [],
            )
        cost += prompt_cost
        if prompt_model:
            model = prompt_model
        all_previews.extend(requirement_previews)

    # De-duplicate previews by (path, kind) keeping the LAST entry — later
    # 'requirements' previews supersede earlier 'tags' previews on the same path
    # because change()'s output already includes regenerated <pdd-*> tags.
    by_path: Dict[Path, _PromptPreview] = {}
    for preview in all_previews:
        existing = by_path.get(preview.path)
        if existing and existing.kind == "requirements" and preview.kind == "tags":
            # 'requirements' already covers tag changes; keep the requirements one
            continue
        by_path[preview.path] = preview
    deduped_previews = list(by_path.values())

    # ---- COMMIT PHASE: write everything (or print diffs in dry-run) --------
    def _rel(path: Path) -> str:
        """Render `path` relative to the project state root for user-facing
        output (CLI logs, GitHub status comment). Falls back to the absolute
        string if the path is not inside state_root, so we never silently
        leak something off-tree without context."""
        try:
            return path.resolve().relative_to(state_root.resolve()).as_posix()
        except ValueError:
            return str(path)

    changed_files: List[str] = []
    if application.architecture_diff:
        changed_files.append(_rel(arch_path))

    if dry_run:
        if not quiet and application.architecture_diff:
            print("--- architecture.json ---")
            print(application.architecture_diff)
        for preview in deduped_previews:
            changed_files.append(_rel(preview.path))
            if not quiet:
                print(_format_preview(preview))
    else:
        # Transactional commit under a single architecture-directory lock so
        # concurrent runs serialize across the entire architecture+prompts+
        # snapshot+rollback window. Without this, run B can succeed and write
        # its prompt+snapshot while run A is mid-commit and then rolls
        # architecture.json back, leaving B's prompt/snapshot orphaned.
        rollback_actions: List[Callable[[], None]] = []
        with _architecture_write_lock(arch_path.parent):
            # F13: lost-update guard. Re-read architecture.json under the lock
            # and confirm it still matches the baseline our patch was computed
            # against. If a concurrent run committed in between, our patch
            # would silently overwrite their changes — fail cleanly instead.
            current_arch_bytes_under_lock: Optional[bytes] = (
                arch_path.read_bytes() if arch_path.exists() else None
            )
            if current_arch_bytes_under_lock != arch_baseline_bytes:
                return (
                    False,
                    "Concurrent modification detected on architecture.json since this "
                    "run's compute phase began. Re-run `pdd generate --incremental` "
                    "to rebase against the current state.",
                    cost,
                    model,
                    [],
                )

            prompt_error = _validate_prompt_previews_current(deduped_previews)
            if prompt_error:
                return False, prompt_error, cost, model, []

            try:
                if application.architecture_diff:
                    original_arch_bytes = current_arch_bytes_under_lock
                    _backup_file(arch_path)
                    atomic_write_json(arch_path, application.raw_architecture)
                    if original_arch_bytes is None:
                        rollback_actions.append(
                            lambda p=arch_path: p.unlink(missing_ok=True)
                        )
                    else:
                        rollback_actions.append(
                            lambda p=arch_path, b=original_arch_bytes: p.write_bytes(b)
                        )

                for preview in deduped_previews:
                    changed_files.append(_rel(preview.path))
                    existed = preview.path.exists()
                    original_text = (
                        preview.path.read_text(encoding="utf-8") if existed else None
                    )
                    if preview.kind == "deleted":
                        preview.path.unlink()
                        rollback_actions.append(
                            lambda p=preview.path, t=original_text: p.write_text(
                                t or "", encoding="utf-8"
                            )
                        )
                    else:
                        preview.path.parent.mkdir(parents=True, exist_ok=True)
                        _atomic_write_text(preview.path, preview.after)
                        if not existed:
                            rollback_actions.append(
                                lambda p=preview.path: p.unlink(missing_ok=True)
                            )
                        else:
                            rollback_actions.append(
                                lambda p=preview.path, t=original_text: p.write_text(
                                    t or "", encoding="utf-8"
                                )
                            )

                _save_prd_snapshot(state_root, source_key, current_prd)
            except Exception as exc:
                for action in reversed(rollback_actions):
                    try:
                        action()
                    except Exception:
                        pass  # best-effort: keep restoring the rest
                return (
                    False,
                    f"Commit phase failed and rolled back: {exc}",
                    cost,
                    model,
                    [],
                )

    prompt_update_paths = [
        _rel(p.path) for p in deduped_previews if p.kind == "requirements"
    ]
    changed_files = sorted(dict.fromkeys(changed_files))
    mode = "Dry run" if dry_run else "Applied"
    message = (
        f"{mode} incremental PRD propagation: "
        f"{len(application.changed_filenames)} architecture entr"
        f"{'y' if len(application.changed_filenames) == 1 else 'ies'} affected, "
        f"{len(prompt_update_paths)} prompt requirement update"
        f"{'' if len(prompt_update_paths) == 1 else 's'}."
    )
    return True, message, cost, model, changed_files


def apply_architecture_patch(raw_architecture: Any, patch: ArchitecturePatch) -> PatchApplication:
    """Validate and apply a structured architecture patch without writing files."""
    modules = copy.deepcopy(extract_modules(raw_architecture))
    if not modules:
        raise ValueError("architecture.json contains no modules")

    before_text = _json_dumps(_replace_modules(raw_architecture, modules))
    before_cycles = _cycle_set(_detect_cycles(modules))

    by_filename = _index_modules(modules)
    changed: List[str] = []

    _validate_patch_shape(patch, by_filename)

    removed = {item.filename for item in patch.modules_to_remove}
    added = {item.filename for item in patch.modules_to_add}

    for item in patch.modules_to_remove:
        modules = [module for module in modules if module.get("filename") != item.filename]
        changed.append(item.filename)

    by_filename = _index_modules(modules)
    max_priority = max(
        (module.get("priority") for module in modules if isinstance(module.get("priority"), int)),
        default=0,
    )

    for item in _topologically_order_modules_to_add(patch.modules_to_add):
        max_priority += 1
        entry = item.model_dump(exclude_none=True)
        entry.pop("requirements", None)
        entry.setdefault("description", item.reason)
        entry.setdefault("dependencies", [])
        entry.setdefault("interface", {"type": "module"})
        entry.setdefault("tags", _infer_tags_from_filename(item.filename))
        # New-module priorities are deterministic and dependency-aware. Do not
        # trust LLM-provided add priorities: they can arrive out of dependency
        # order, so assign priorities after topologically ordering the added set.
        entry["priority"] = max_priority
        modules.append(entry)
        by_filename[item.filename] = entry
        changed.append(item.filename)

    for item in patch.modules_to_modify:
        entry = by_filename[item.filename]
        for field_name, value in item.changes.items():
            if isinstance(value, dict) and isinstance(entry.get(field_name), dict):
                entry[field_name] = _deep_merge_dicts(entry[field_name], value)
            else:
                entry[field_name] = copy.deepcopy(value)
        changed.append(item.filename)

    for item in patch.dependency_updates:
        if item.source in removed:
            raise ValueError(f"Cannot update dependencies for removed module: {item.source}")
        entry = by_filename[item.source]
        deps = [dep for dep in entry.get("dependencies", []) if isinstance(dep, str)]
        deps = [dep for dep in deps if dep not in set(item.remove)]
        for dep in item.add:
            if dep not in deps:
                deps.append(dep)
        entry["dependencies"] = deps
        changed.append(item.source)

    by_filename = _index_modules(modules)
    _validate_dependency_targets(patch, by_filename, added, removed)

    after_cycles = _cycle_set(_detect_cycles(modules))
    new_cycles = sorted(after_cycles - before_cycles)
    if new_cycles:
        formatted = "; ".join(" -> ".join(cycle) for cycle in new_cycles)
        raise ValueError(f"Patch introduces circular dependencies: {formatted}")

    _normalize_dependency_priorities(modules, changed)

    updated_raw = _replace_modules(raw_architecture, modules)
    after_text = _json_dumps(updated_raw)
    diff = "".join(
        difflib.unified_diff(
            before_text.splitlines(keepends=True),
            after_text.splitlines(keepends=True),
            fromfile="architecture.json.before",
            tofile="architecture.json.after",
        )
    )

    return PatchApplication(
        raw_architecture=updated_raw,
        modules=modules,
        changed_filenames=sorted(dict.fromkeys(changed)),
        architecture_diff=diff,
    )


def _ask_llm_for_patch(
    *,
    prd_source: str,
    prd_diff: str,
    architecture: Any,
    strength: float,
    temperature: float,
    time: float,
    verbose: bool,
    validation_errors: Sequence[str] = (),
) -> Tuple[ArchitecturePatch, float, str]:
    template = load_prompt_template("incremental_prd_architecture_patch_LLM")
    if not template:
        raise ValueError("Missing prompt template: incremental_prd_architecture_patch_LLM")

    processed = preprocess(
        template,
        recursive=False,
        double_curly_brackets=True,
        exclude_keys=[
            "PRD_SOURCE",
            "PRD_DIFF",
            "CURRENT_ARCHITECTURE",
            "VALIDATION_ERRORS",
        ],
    )
    response = llm_invoke(
        prompt=processed,
        input_json={
            "PRD_SOURCE": prd_source,
            "PRD_DIFF": prd_diff,
            "CURRENT_ARCHITECTURE": _json_dumps(architecture),
            "VALIDATION_ERRORS": "\n".join(f"- {error}" for error in validation_errors),
        },
        strength=strength,
        temperature=temperature,
        time=time,
        verbose=verbose,
        output_pydantic=ArchitecturePatch,
    )
    return response["result"], response.get("cost", 0.0), response.get("model_name", "")


def _validate_patch_shape(patch: ArchitecturePatch, existing: Dict[str, Dict[str, Any]]) -> None:
    seen_adds: set[str] = set()
    for item in patch.modules_to_add:
        _validate_prompt_filename(item.filename)
        _validate_filepath(item.filepath)
        for dep in item.dependencies:
            _validate_prompt_filename(dep)
        if item.priority is not None:
            _validate_priority_value(item.priority)
        if item.filename in existing:
            raise ValueError(f"Cannot add existing module: {item.filename}")
        if item.filename in seen_adds:
            raise ValueError(f"Duplicate module add: {item.filename}")
        seen_adds.add(item.filename)

    for item in patch.modules_to_remove:
        _validate_prompt_filename(item.filename)
        if item.filename not in existing:
            raise ValueError(f"Cannot remove unknown module: {item.filename}")
        if not item.justification.strip():
            raise ValueError(f"Removal requires justification: {item.filename}")

    for item in patch.modules_to_modify:
        _validate_prompt_filename(item.filename)
        if item.filename not in existing:
            raise ValueError(f"Cannot modify unknown module: {item.filename}")
        unknown_fields = sorted(set(item.changes) - _ALLOWED_MODIFY_FIELDS)
        if unknown_fields:
            raise ValueError(
                f"Unsupported field(s) for {item.filename}: {', '.join(unknown_fields)}. "
                "Use dependency_updates for dependencies."
            )
        for field, value in item.changes.items():
            try:
                _validate_modify_change_value(field, value)
            except ValueError as exc:
                raise ValueError(
                    f"Invalid value for {item.filename!r} change field '{field}': {exc}"
                ) from exc

    for item in patch.dependency_updates:
        _validate_prompt_filename(item.source)
        if item.source not in existing:
            raise ValueError(f"Cannot update dependencies for unknown module: {item.source}")
        for dep in item.add + item.remove:
            _validate_prompt_filename(dep)


def _validate_dependency_targets(
    patch: ArchitecturePatch,
    modules_by_filename: Dict[str, Dict[str, Any]],
    added: set[str],
    removed: set[str],
) -> None:
    affected = {item.filename for item in patch.modules_to_add}
    affected.update(item.filename for item in patch.modules_to_modify)
    affected.update(item.source for item in patch.dependency_updates)

    for filename in affected:
        entry = modules_by_filename.get(filename)
        if not entry:
            continue
        for dep in entry.get("dependencies", []):
            if dep not in modules_by_filename:
                if dep in added:
                    continue
                raise ValueError(f"{filename} depends on unknown module: {dep}")

    if removed:
        for filename, entry in modules_by_filename.items():
            for dep in entry.get("dependencies", []):
                if dep in removed:
                    raise ValueError(f"{filename} still depends on removed module: {dep}")


def _validate_relative_safe_path(path_str: Any, kind: str) -> None:
    """Reject unsafe LLM-controlled relative paths."""
    if not isinstance(path_str, str) or not path_str:
        raise ValueError(f"Invalid {kind}: empty or non-string")
    parts = Path(path_str).parts
    if (
        Path(path_str).is_absolute()
        or "\\" in path_str
        or ".." in parts
        or not _SAFE_RELATIVE_PATH_PATTERN.fullmatch(path_str)
    ):
        raise ValueError(f"Invalid {kind} (must be a safe relative path): {path_str!r}")


def _validate_prompt_filename(filename: str) -> None:
    _validate_relative_safe_path(filename, "architecture prompt filename")
    if not filename.endswith(".prompt"):
        raise ValueError(f"Invalid architecture prompt filename: {filename!r}")


def _validate_filepath(filepath: Any) -> None:
    """filepath is optional; when present it must be safe to read into an LLM."""
    if filepath is None or filepath == "":
        return
    _validate_relative_safe_path(filepath, "module filepath")
    if _has_hidden_or_sensitive_path(filepath):
        raise ValueError(
            "Invalid module filepath (must not reference hidden or secret-like "
            f"files): {filepath!r}"
        )


def _validate_modify_change_value(field: str, value: Any) -> None:
    """Type-check a value being written into a `modules_to_modify.changes` field.

    `_ALLOWED_MODIFY_FIELDS` only restricts which field NAMES the LLM may set;
    without per-field type validation a structured patch could still set
    e.g. tags="not-a-list" or priority="high" and we would dutifully serialize
    that into architecture.json, leaving the file structurally valid JSON but
    semantically broken for downstream consumers.
    """
    if field == "reason" or field == "description":
        if not isinstance(value, str):
            raise ValueError(
                f"Field '{field}' must be a string, got {type(value).__name__}"
            )
    elif field == "interface":
        if not isinstance(value, dict):
            raise ValueError(
                f"Field 'interface' must be an object, got {type(value).__name__}"
            )
    elif field == "filepath":
        # Reuses the safe-relative-path check. Empty/None is handled there.
        _validate_filepath(value)
    elif field == "tags":
        if not isinstance(value, list) or not all(isinstance(t, str) for t in value):
            raise ValueError(
                f"Field 'tags' must be a list of strings, got {type(value).__name__}"
            )
    elif field == "priority":
        _validate_priority_value(value)
    # Unknown fields are caught earlier by the _ALLOWED_MODIFY_FIELDS check.


def _validate_priority_value(value: Any) -> None:
    # bools are a subtype of int in Python, so reject them explicitly.
    if isinstance(value, bool) or not isinstance(value, int):
        raise ValueError(f"Field 'priority' must be an int, got {type(value).__name__}")


def _has_hidden_or_sensitive_path(path_str: str) -> bool:
    """Return True when a repo-relative path targets local config or secrets."""
    for part in Path(path_str).parts:
        lower = part.lower()
        if part.startswith(".") or lower in _SENSITIVE_FILE_BASENAMES:
            return True
        if lower.endswith(_SENSITIVE_FILE_SUFFIXES):
            return True
    return False


def _topologically_order_modules_to_add(items: Sequence[ModuleToAdd]) -> List[ModuleToAdd]:
    """Order newly added modules so dependencies inside the add set come first."""
    by_filename = {item.filename: item for item in items}
    ordered: List[ModuleToAdd] = []
    visiting: set[str] = set()
    visited: set[str] = set()

    def visit(item: ModuleToAdd) -> None:
        if item.filename in visited:
            return
        if item.filename in visiting:
            # Cycle validation runs after all modules are merged; stop recursion
            # here so we can still produce the merged graph and the canonical
            # cycle error.
            return
        visiting.add(item.filename)
        for dependency in item.dependencies:
            dependency_item = by_filename.get(dependency)
            if dependency_item is not None:
                visit(dependency_item)
        visiting.remove(item.filename)
        visited.add(item.filename)
        ordered.append(item)

    for item in items:
        visit(item)
    return ordered


def _normalize_dependency_priorities(modules: Sequence[Dict[str, Any]], changed: List[str]) -> None:
    """Ensure every dependency has a lower priority than its dependents.

    The LLM can add a module and then add an existing module's dependency on it.
    Since existing modules may already have low priorities, appending the new
    module at the end can violate the architecture ordering invariant. Bump only
    modules whose priority is too low, processing dependencies first.
    """
    by_filename = {
        module.get("filename"): module
        for module in modules
        if module.get("filename")
    }
    ordered_names: List[str] = []
    visiting: set[str] = set()
    visited: set[str] = set()

    def visit(filename: str) -> None:
        if filename in visited:
            return
        if filename in visiting:
            return
        visiting.add(filename)
        module = by_filename.get(filename, {})
        for dependency in module.get("dependencies", []) or []:
            if dependency in by_filename:
                visit(dependency)
        visiting.remove(filename)
        visited.add(filename)
        ordered_names.append(filename)

    for module in sorted(
        modules,
        key=lambda entry: (
            _priority_value(entry),
            str(entry.get("filename") or ""),
        ),
    ):
        filename = module.get("filename")
        if filename:
            visit(filename)

    for filename in ordered_names:
        module = by_filename[filename]
        required_priority = 1
        for dependency in module.get("dependencies", []) or []:
            dependency_module = by_filename.get(dependency)
            if dependency_module is not None:
                required_priority = max(
                    required_priority,
                    _priority_value(dependency_module) + 1,
                )
        current_priority = _priority_value(module)
        if current_priority < required_priority:
            module["priority"] = required_priority
            changed.append(filename)


def _priority_value(module: Dict[str, Any]) -> int:
    priority = module.get("priority")
    if isinstance(priority, bool) or not isinstance(priority, int):
        return 0
    return priority


def _detect_cycles(modules: Sequence[Dict[str, Any]]) -> List[List[str]]:
    graph = {
        module.get("filename"): [
            dep for dep in module.get("dependencies", [])
            if isinstance(dep, str)
        ]
        for module in modules
        if module.get("filename")
    }

    cycles: List[List[str]] = []
    visiting: set[str] = set()
    visited: set[str] = set()
    stack: List[str] = []

    def visit(node: str) -> None:
        if node in visiting:
            start = stack.index(node) if node in stack else 0
            cycles.append(stack[start:] + [node])
            return
        if node in visited:
            return
        visiting.add(node)
        stack.append(node)
        for dep in graph.get(node, []):
            if dep in graph:
                visit(dep)
        stack.pop()
        visiting.remove(node)
        visited.add(node)

    for filename in graph:
        visit(filename)

    return cycles


def _cycle_set(cycles: Sequence[Sequence[str]]) -> set[Tuple[str, ...]]:
    return {tuple(cycle) for cycle in cycles}


def _validate_prompt_previews_current(previews: Sequence[_PromptPreview]) -> Optional[str]:
    """Return an error if any prompt changed since its preview was computed."""
    for preview in previews:
        if preview.kind == "created":
            if preview.path.exists():
                return (
                    "Concurrent modification detected on prompt file "
                    f"{preview.path.name}: file was created after this run's "
                    "compute phase began. Re-run `pdd generate --incremental` "
                    "to rebase against the current state."
                )
            continue

        if not preview.path.exists():
            return (
                "Concurrent modification detected on prompt file "
                f"{preview.path.name}: file was removed after this run's "
                "compute phase began. Re-run `pdd generate --incremental` "
                "to rebase against the current state."
            )

        current = preview.path.read_text(encoding="utf-8")
        if current != preview.before:
            return (
                "Concurrent modification detected on prompt file "
                f"{preview.path.name} since this run's compute phase began. "
                "Re-run `pdd generate --incremental` to rebase against the "
                "current state."
            )
    return None


def _delete_prompt_files_for_removed_modules(
    modules_to_remove: Sequence[ModuleRemoval],
    prompts_dir: Path,
) -> List[_PromptPreview]:
    """Return previews that delete prompt files for removed architecture modules."""
    previews: List[_PromptPreview] = []
    for item in modules_to_remove:
        prompt_path = prompts_dir / item.filename
        if not prompt_path.exists():
            continue
        content = prompt_path.read_text(encoding="utf-8")
        previews.append(_PromptPreview(prompt_path, "deleted", content, ""))
    return previews


def _sync_tags_for_changed_prompts(
    modules: Sequence[Dict[str, Any]],
    changed_filenames: Sequence[str],
    prompts_dir: Path,
) -> List[_PromptPreview]:
    """Return previews for tag-only updates on existing prompts. No I/O."""
    changed = set(changed_filenames)
    by_filename = {
        module.get("filename"): module
        for module in modules
        if module.get("filename") in changed
    }
    previews: List[_PromptPreview] = []
    for filename, entry in by_filename.items():
        prompt_path = prompts_dir / filename
        if not prompt_path.exists():
            continue
        content = prompt_path.read_text(encoding="utf-8")
        updated = _replace_pdd_tags(content, generate_tags_from_architecture(entry))
        if updated != content:
            previews.append(_PromptPreview(prompt_path, "tags", content, updated))
    return previews


def _generate_prompt_files_for_new_modules(
    modules_to_add: Sequence[ModuleToAdd],
    prompts_dir: Path,
    *,
    project_root: Optional[Path] = None,
) -> List[_PromptPreview]:
    """Return previews for new prompt files to create. No I/O."""
    if project_root is None:
        prompts_dir_rel = prompts_dir.name or "prompts"
    else:
        try:
            prompts_dir_rel = prompts_dir.resolve().relative_to(project_root.resolve()).as_posix()
        except ValueError:
            prompts_dir_rel = prompts_dir.name or "prompts"

    previews: List[_PromptPreview] = []
    for module in modules_to_add:
        prompt_path = prompts_dir / module.filename
        if prompt_path.exists():
            continue
        previews.append(
            _PromptPreview(
                prompt_path,
                "created",
                "",
                _new_prompt_content(module, prompts_dir_rel=prompts_dir_rel),
            )
        )
    return previews


def _update_prompt_requirements(
    *,
    before_modules: Sequence[Dict[str, Any]],
    after_modules: Sequence[Dict[str, Any]],
    architecture_diff: str,
    prompts_dir: Path,
    strength: float,
    temperature: float,
    time: float,
    verbose: bool,
) -> Tuple[List[_PromptPreview], float, str]:
    """Return previews for Requirements-section updates plus cost/model. No I/O."""
    prompt_paths = [
        prompts_dir / module["filename"]
        for module in after_modules
        if isinstance(module.get("filename"), str)
        and (prompts_dir / module["filename"]).exists()
    ]
    if not prompt_paths:
        return [], 0.0, ""

    changes, detect_cost, model = detect_change(
        [str(path) for path in prompt_paths],
        architecture_diff,
        strength=strength,
        temperature=temperature,
        time=time,
        verbose=verbose,
    )
    if not changes:
        return [], detect_cost, model

    after_by_name = _index_modules(list(after_modules))
    before_by_name = _index_modules(list(before_modules))
    path_by_name = _prompt_path_lookup(prompt_paths)
    previews: List[_PromptPreview] = []
    seen_paths: set[Path] = set()
    total_cost = detect_cost
    final_model = model

    for item in changes:
        prompt_name = item.get("prompt_name", "")
        prompt_path = path_by_name.get(prompt_name) or path_by_name.get(Path(prompt_name).name)
        if not prompt_path or not prompt_path.exists() or prompt_path in seen_paths:
            continue
        filename = _architecture_filename_for_prompt(prompt_path, prompts_dir, after_by_name)
        entry = after_by_name.get(filename, before_by_name.get(filename, {}))
        code_content = _read_code_for_entry(entry, prompts_dir.parent)
        original_prompt = prompt_path.read_text(encoding="utf-8")
        modified_prompt, change_cost, change_model = change(
            input_prompt=original_prompt,
            input_code=code_content,
            change_prompt=item.get("change_instructions", ""),
            strength=strength,
            temperature=temperature,
            time=time,
            verbose=verbose,
        )
        total_cost += change_cost
        if change_model:
            final_model = change_model
        if entry:
            modified_prompt = _replace_pdd_tags(
                modified_prompt,
                generate_tags_from_architecture(entry),
            )
        if modified_prompt != original_prompt:
            previews.append(
                _PromptPreview(prompt_path, "requirements", original_prompt, modified_prompt)
            )
            seen_paths.add(prompt_path)

    return previews, total_cost, final_model


def _replace_pdd_tags(content: str, tags: str) -> str:
    stripped = content
    for tag_name in ("pdd-reason", "pdd-interface", "pdd-dependency"):
        stripped = re.sub(
            rf"\s*<{tag_name}>.*?</{tag_name}>\s*",
            "\n",
            stripped,
            flags=re.DOTALL,
        )
    return tags.rstrip() + "\n\n" + stripped.lstrip()


def _format_preview(preview: _PromptPreview) -> str:
    """Render a dry-run preview block for a single prompt change."""
    rel = preview.path.name
    if preview.kind == "created":
        return (
            f"--- {rel} (NEW FILE) ---\n"
            f"{preview.after.rstrip()}\n"
        )
    if preview.kind == "deleted":
        diff = "".join(
            difflib.unified_diff(
                preview.before.splitlines(keepends=True),
                [],
                fromfile=f"{rel}.before",
                tofile="/dev/null",
            )
        )
        return f"--- {rel} (DELETE FILE) ---\n{diff}"
    label = {
        "tags": f"{rel} (pdd-* tags only)",
        "requirements": f"{rel} (Requirements update)",
    }.get(preview.kind, rel)
    diff = "".join(
        difflib.unified_diff(
            preview.before.splitlines(keepends=True),
            preview.after.splitlines(keepends=True),
            fromfile=f"{rel}.before",
            tofile=f"{rel}.after",
        )
    )
    if not diff:
        diff = "(no textual change)\n"
    return f"--- {label} ---\n{diff}"


def _new_prompt_content(
    module: ModuleToAdd,
    prompts_dir_rel: str = "prompts",
) -> str:
    """Render a starter prompt for a newly added architecture module.

    Includes <pdd-*> metadata tags, an `<include>` line per declared dependency
    (so `pdd sync` resolves dependent prompt context at runtime), a Role section
    derived from architecture description/reason, the LLM-supplied Requirements
    bullets, an Interface Specification block transcribed from the architecture
    interface contract (when supplied), and a Dependencies section that names
    each dependent module so the LLM has explicit import targets at code-gen
    time.

    `prompts_dir_rel` is the prompts directory path relative to project root
    (e.g. ``"prompts"`` or ``"backend/prompts"``). It is used to build include
    paths that `pdd.preprocess` can resolve via the standard
    cwd / package_root / repo_root search order (`./` would only resolve when
    cwd is the prompts directory itself, which is not the normal invocation).

    This is intentionally lighter than the full agentic Step 9 generator
    (`agentic_arch_step9_prompts_LLM.prompt`); a follow-up may invoke that flow
    for incremental updates that need richer prompts. For now this produces a
    prompt that survives `pdd sync` round-trip and downstream code generation.
    """
    tags = generate_tags_from_architecture(
        module.model_dump(exclude_none=True, exclude={"requirements"})
    )
    requirements = module.requirements or [module.description or module.reason]
    requirement_bullets = "\n".join(f"- {item}" for item in requirements if item)

    prompts_prefix = prompts_dir_rel.strip("/") if prompts_dir_rel else ""
    include_prefix = f"{prompts_prefix}/" if prompts_prefix else ""
    include_lines = "\n".join(
        f"<include>{include_prefix}{dep}</include>" for dep in module.dependencies
    )

    interface_block = _format_interface_specification(module.interface)

    dependency_block = ""
    if module.dependencies:
        dep_bullets = "\n".join(f"- `{dep}`" for dep in module.dependencies)
        dependency_block = (
            "\n## Dependencies\n\n"
            "Import the public interfaces of each dependent module before "
            "implementing this one:\n\n"
            f"{dep_bullets}\n"
        )

    parts: List[str] = [tags]
    if include_lines:
        parts.append(include_lines)
    parts.append(f"% You are implementing `{module.filename}`.")
    parts.append("## Role\n\n" + (module.description or module.reason))
    parts.append("## Requirements\n\n" + requirement_bullets)
    if interface_block:
        parts.append(interface_block)
    if dependency_block:
        parts.append(dependency_block.lstrip())
    return "\n\n".join(parts).rstrip() + "\n"


def _format_interface_specification(interface: Dict[str, Any]) -> str:
    """Render an architecture interface contract as a Markdown spec block."""
    if not interface:
        return ""
    body_lines: List[str] = []
    iface_type = interface.get("type")
    if iface_type:
        body_lines.append(f"- type: `{iface_type}`")
    module_iface = interface.get("module") or {}
    functions = module_iface.get("functions") or []
    if functions:
        body_lines.append("- Functions:")
        for fn in functions:
            if not isinstance(fn, dict):
                continue
            name = fn.get("name") or ""
            signature = fn.get("signature") or ""
            returns = fn.get("returns") or ""
            line = f"  - `{name}{signature}`"
            if returns:
                line += f" -> `{returns}`"
            body_lines.append(line)
    classes = module_iface.get("classes") or []
    if classes:
        body_lines.append("- Classes:")
        for cls in classes:
            if isinstance(cls, dict) and cls.get("name"):
                body_lines.append(f"  - `{cls['name']}`")
            elif isinstance(cls, str):
                body_lines.append(f"  - `{cls}`")
    if not body_lines:
        return ""
    return "## Interface Specification\n\n" + "\n".join(body_lines)


def _read_prd_source(
    prd_source: str,
    project_root: Path,
    *,
    issue_content: Optional[str] = None,
) -> Tuple[str, str]:
    if _GITHUB_ISSUE_RE.search(prd_source):
        if issue_content is not None:
            return prd_source, issue_content
        return prd_source, _read_github_issue_prd(prd_source)

    source_path = Path(prd_source)
    if not source_path.is_absolute():
        source_path = project_root / source_path
    source_path = source_path.resolve()
    try:
        source_path.relative_to(project_root.resolve())
    except ValueError as exc:
        raise ValueError(f"PRD path must be inside project root: {source_path}") from exc
    if not source_path.exists() or source_path.is_dir():
        raise ValueError(f"PRD source does not exist or is not a file: {source_path}")
    return (
        source_path.relative_to(project_root.resolve()).as_posix(),
        source_path.read_text(encoding="utf-8"),
    )


def _read_github_issue_prd(issue_url: str) -> str:
    result = subprocess.run(
        ["gh", "issue", "view", issue_url, "--json", "title,body,comments"],
        capture_output=True,
        text=True,
        check=False,
    )
    if result.returncode != 0:
        raise ValueError(f"Failed to read GitHub issue PRD: {result.stderr.strip()}")
    payload = json.loads(result.stdout)
    parts = [f"# {payload.get('title', '').strip()}", payload.get("body", "")]
    for comment in payload.get("comments", []):
        body = comment.get("body")
        # Filter pdd's own incremental status comments so a previous run's
        # output never feeds back into the next run's PRD diff.
        if body and INCREMENTAL_STATUS_MARKER not in body:
            parts.append(body)
    return "\n\n".join(part for part in parts if part)


def _previous_prd_content(
    source_key: str,
    prd_source: str,
    project_root: Path,
    current_content: str,
) -> Optional[str]:
    state = _load_prd_state(project_root)
    source_state = state.get("sources", {}).get(source_key)
    current_hash = _content_hash(current_content)
    stored_hash = (
        source_state.get("hash")
        if isinstance(source_state, dict) and isinstance(source_state.get("hash"), str)
        else None
    )
    if stored_hash == current_hash:
        return current_content

    if isinstance(source_state, dict) and isinstance(source_state.get("content"), str):
        return source_state["content"]

    cached = _read_prd_snapshot_cache(project_root, source_key, stored_hash)
    if cached is not None:
        return cached

    if not _GITHUB_ISSUE_RE.search(prd_source):
        git_content = _read_git_head_file(source_key, project_root)
        if git_content is not None:
            return git_content

    return None


def _build_prd_diff(previous: Optional[str], current: str, source_key: str) -> str:
    if previous is None:
        return f"No previous PRD snapshot for {source_key}; treat the full PRD as new:\n\n{current}"
    if previous == current:
        return ""
    return "".join(
        difflib.unified_diff(
            previous.splitlines(keepends=True),
            current.splitlines(keepends=True),
            fromfile=f"{source_key}.previous",
            tofile=f"{source_key}.current",
        )
    )


def _load_prd_state(project_root: Path) -> Dict[str, Any]:
    path = project_root / ".pdd" / "meta" / "prd_hashes.json"
    if not path.exists():
        return {"version": 1, "sources": {}}
    try:
        data = json.loads(path.read_text(encoding="utf-8"))
    except (OSError, json.JSONDecodeError):
        return {"version": 1, "sources": {}}
    if isinstance(data, dict) and isinstance(data.get("sources"), dict):
        return data
    return {"version": 1, "sources": {}}


def _save_prd_snapshot(project_root: Path, source_key: str, content: str) -> None:
    cache_key = _prd_snapshot_cache_key(source_key)
    cache_dir = _prd_snapshot_cache_dir(project_root)
    _ensure_prd_snapshot_cache_ignored(cache_dir)
    _atomic_write_text(cache_dir / cache_key, content)

    state = _sanitize_prd_state(_load_prd_state(project_root))
    state["version"] = 2
    state.setdefault("sources", {})
    state["sources"][source_key] = {
        "hash": _content_hash(content),
        "source_type": (
            "github_issue" if _GITHUB_ISSUE_RE.search(source_key) else "local_file"
        ),
        "cache_key": cache_key,
        "updated_at": datetime.now(timezone.utc).isoformat(),
    }
    atomic_write_json(project_root / ".pdd" / "meta" / "prd_hashes.json", state)


def _content_hash(content: str) -> str:
    return hashlib.sha256(content.encode("utf-8")).hexdigest()


def _prd_snapshot_cache_dir(project_root: Path) -> Path:
    return project_root / ".pdd" / "cache" / "prd_snapshots"


def _prd_snapshot_cache_key(source_key: str) -> str:
    return hashlib.sha256(source_key.encode("utf-8")).hexdigest() + ".txt"


def _ensure_prd_snapshot_cache_ignored(cache_dir: Path) -> None:
    ignore_file = cache_dir.parent / ".gitignore"
    try:
        existing = ignore_file.read_text(encoding="utf-8")
    except OSError:
        existing = ""
    lines = [line.strip() for line in existing.splitlines()]
    if "*" in lines:
        return
    body = existing.rstrip()
    if body:
        body += "\n"
    body += "*\n!.gitignore\n"
    _atomic_write_text(ignore_file, body)


def _read_prd_snapshot_cache(
    project_root: Path,
    source_key: str,
    expected_hash: Optional[str],
) -> Optional[str]:
    candidates = [
        _prd_snapshot_cache_dir(project_root) / _prd_snapshot_cache_key(source_key)
    ]
    for path in candidates:
        try:
            content = path.read_text(encoding="utf-8")
        except OSError:
            continue
        if expected_hash and _content_hash(content) != expected_hash:
            continue
        return content
    return None


def _sanitize_prd_state(state: Dict[str, Any]) -> Dict[str, Any]:
    clean: Dict[str, Any] = {"version": state.get("version", 1), "sources": {}}
    sources = state.get("sources", {})
    if not isinstance(sources, dict):
        return clean

    for key, value in sources.items():
        if not isinstance(key, str) or not isinstance(value, dict):
            continue
        entry: Dict[str, Any] = {}
        for field_name in ("hash", "source_type", "cache_key", "updated_at"):
            field_value = value.get(field_name)
            if isinstance(field_value, str):
                entry[field_name] = field_value
        if entry:
            clean["sources"][key] = entry
    return clean


def _prd_state_contains_raw_content(project_root: Path) -> bool:
    sources = _load_prd_state(project_root).get("sources", {})
    if not isinstance(sources, dict):
        return False
    return any(
        isinstance(value, dict) and isinstance(value.get("content"), str)
        for value in sources.values()
    )


def _read_git_head_file(relative_path: str, project_root: Path) -> Optional[str]:
    result = subprocess.run(
        ["git", "show", f"HEAD:{relative_path}"],
        cwd=project_root,
        capture_output=True,
        text=True,
        check=False,
    )
    if result.returncode != 0:
        return None
    return result.stdout


def _load_architecture(path: Path) -> Any:
    if not path.exists():
        raise ValueError(f"Architecture file not found: {path}")
    try:
        return json.loads(path.read_text(encoding="utf-8"))
    except json.JSONDecodeError as exc:
        raise ValueError(f"Invalid architecture JSON in {path}: {exc}") from exc


def _load_architecture_with_bytes(path: Path) -> Tuple[Any, bytes]:
    """Read architecture.json with a single `read_bytes` and parse from the
    same buffer. Returns ``(parsed, raw_bytes)`` so callers can reuse the
    exact buffer as a concurrent-modification baseline without racing a
    second on-disk read.
    """
    if not path.exists():
        raise ValueError(f"Architecture file not found: {path}")
    raw = path.read_bytes()
    try:
        parsed = json.loads(raw.decode("utf-8"))
    except json.JSONDecodeError as exc:
        raise ValueError(f"Invalid architecture JSON in {path}: {exc}") from exc
    return parsed, raw


def _replace_modules(raw_architecture: Any, modules: List[Dict[str, Any]]) -> Any:
    if isinstance(raw_architecture, dict):
        updated = copy.deepcopy(raw_architecture)
        updated["modules"] = modules
        updated.setdefault("prd_files", [])
        return updated
    return modules


def _index_modules(modules: Sequence[Dict[str, Any]]) -> Dict[str, Dict[str, Any]]:
    result: Dict[str, Dict[str, Any]] = {}
    for module in modules:
        filename = module.get("filename")
        if isinstance(filename, str) and filename:
            if filename in result:
                raise ValueError(f"Duplicate architecture module filename: {filename}")
            result[filename] = module
    return result


def _prompt_path_lookup(prompt_paths: Sequence[Path]) -> Dict[str, Path]:
    lookup: Dict[str, Path] = {}
    for path in prompt_paths:
        lookup[path.name] = path
        lookup[path.as_posix()] = path
    return lookup


def _architecture_filename_for_prompt(
    prompt_path: Path,
    prompts_dir: Path,
    modules_by_filename: Dict[str, Dict[str, Any]],
) -> str:
    try:
        relative = prompt_path.relative_to(prompts_dir).as_posix()
    except ValueError:
        relative = prompt_path.name
    if relative in modules_by_filename:
        return relative
    return prompt_path.name


def _read_code_for_entry(entry: Dict[str, Any], project_root: Path) -> str:
    filepath = entry.get("filepath")
    if not isinstance(filepath, str) or not filepath:
        return _CODE_UNAVAILABLE_MESSAGE
    try:
        _validate_filepath(filepath)
    except ValueError:
        return _CODE_UNAVAILABLE_MESSAGE
    project_root_resolved = project_root.resolve()
    code_path = (project_root / filepath).resolve()
    try:
        code_path.relative_to(project_root_resolved)
    except ValueError:
        return _CODE_UNAVAILABLE_MESSAGE
    if code_path.exists() and code_path.is_file():
        return code_path.read_text(encoding="utf-8")
    return _CODE_UNAVAILABLE_MESSAGE


def _deep_merge_dicts(base: Dict[str, Any], patch: Dict[str, Any]) -> Dict[str, Any]:
    merged = copy.deepcopy(base)
    for key, value in patch.items():
        if isinstance(value, dict) and isinstance(merged.get(key), dict):
            merged[key] = _deep_merge_dicts(merged[key], value)
        else:
            merged[key] = copy.deepcopy(value)
    return merged


def _infer_tags_from_filename(filename: str) -> List[str]:
    tags = ["module"]
    lower = filename.lower()
    for language in ("python", "typescript", "javascript", "go", "rust"):
        if f"_{language}.prompt" in lower:
            tags.append(language)
    return tags


def _json_dumps(data: Any) -> str:
    return json.dumps(data, indent=2, ensure_ascii=False, sort_keys=False) + "\n"


@contextmanager
def _architecture_write_lock(lock_root: Path) -> Iterator[None]:
    """Best-effort advisory lock for architecture and prompt propagation writes."""
    lock_dir = lock_root / ".pdd" / "meta"
    lock_dir.mkdir(parents=True, exist_ok=True)
    lock_path = lock_dir / "incremental_prd_architecture.lock"
    fd: Optional[int] = None
    try:
        fd = os.open(str(lock_path), os.O_RDWR | os.O_CREAT, 0o644)
        try:
            import fcntl

            fcntl.flock(fd, fcntl.LOCK_EX)
        except (ImportError, OSError):
            pass
        yield
    finally:
        if fd is not None:
            try:
                import fcntl

                fcntl.flock(fd, fcntl.LOCK_UN)
            except (ImportError, OSError):
                pass
            os.close(fd)


def _backup_file(path: Path) -> Path:
    backup_path = path.with_suffix(path.suffix + ".bak")
    if path.exists():
        _atomic_write_text(backup_path, path.read_text(encoding="utf-8"))
    return backup_path


def _atomic_write_text(path: Path, content: str) -> None:
    path = path.resolve()
    path.parent.mkdir(parents=True, exist_ok=True)
    fd, tmp = tempfile.mkstemp(
        dir=str(path.parent),
        prefix=f".{path.name}.",
        suffix=".tmp",
    )
    try:
        with os.fdopen(fd, "w", encoding="utf-8") as handle:
            handle.write(content)
            handle.flush()
            os.fsync(handle.fileno())
        os.replace(tmp, path)
    except BaseException:
        try:
            os.unlink(tmp)
        except OSError:
            pass
        raise
