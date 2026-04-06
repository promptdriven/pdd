"""
Update architecture.json dependencies after auto-deps inserts new module <include> tags.

When ``pdd auto-deps`` adds includes that reference other module prompts (or example
paths that map to a module basename), append the corresponding architecture
``filename`` values to the current module's ``dependencies`` list.
"""
from __future__ import annotations

import json
import re
from pathlib import Path
from typing import Any, Dict, List, Optional, Set, Tuple

from .architecture_include_validation import _resolve_architecture_prompt_path
from .json_atomic import atomic_write_json
from .architecture_registry import find_architecture_for_project, find_project_root
from .sync_order import extract_module_from_include


def extract_include_paths_from_prompt_text(text: str) -> Set[str]:
    """Return paths inside ``<include>...</include>`` tags (supports attributes on the tag)."""
    pattern = r"<include[^>]*>(.*?)</include>"
    return {m.strip() for m in re.findall(pattern, text, re.DOTALL) if m.strip()}


def _find_architecture_record_for_prompt_file(
    project_root: Path, prompt_file_resolved: Path
) -> Optional[Tuple[Path, List[Dict[str, Any]], int]]:
    """
    Locate ``(architecture.json path, parsed list, entry index)`` for a prompt on disk.
    """
    target = prompt_file_resolved.resolve()
    for arch_path in find_architecture_for_project(project_root):
        try:
            raw = arch_path.read_text(encoding="utf-8")
            data = json.loads(raw)
        except (OSError, json.JSONDecodeError):
            continue
        if not isinstance(data, list):
            continue
        base = arch_path.parent
        for i, entry in enumerate(data):
            fn = entry.get("filename") or ""
            if not fn:
                continue
            candidate = _resolve_architecture_prompt_path(fn, base)
            try:
                if candidate.resolve() == target:
                    return arch_path, data, i
            except OSError:
                continue
    return None


def _architecture_filename_for_module_include(
    include_path: str,
    same_file_arch_entries: List[Dict[str, Any]],
) -> Optional[str]:
    """
    Map an include path to an architecture ``dependencies`` string (another entry's
    ``filename``), using module basename equality.
    """
    mod = extract_module_from_include(include_path)
    if not mod:
        return None
    for entry in same_file_arch_entries:
        efn = entry.get("filename") or ""
        if not efn:
            continue
        if extract_module_from_include(efn) == mod:
            return efn
    return None


def merge_auto_deps_includes_into_architecture(
    project_root: Path,
    written_prompt_path: Path,
    old_prompt_text: str,
    new_prompt_text: str,
    *,
    dry_run: bool = False,
) -> Dict[str, Any]:
    """
    Add architecture dependencies for **new** module includes between old and new text.

    Only updates the ``architecture.json`` that already contains an entry for
    ``written_prompt_path``. Does nothing if there is no such entry.

    Returns:
        Dict with keys: ``updated`` (bool), ``architecture_path`` (optional Path),
        ``added_dependencies`` (list[str]), ``messages`` (list[str]).
    """
    messages: List[str] = []
    added: List[str] = []

    rec = _find_architecture_record_for_prompt_file(
        project_root.resolve(), written_prompt_path.resolve()
    )
    if rec is None:
        return {
            "updated": False,
            "architecture_path": None,
            "added_dependencies": [],
            "messages": ["No architecture.json entry matches this prompt; skipping arch update."],
        }

    arch_path, arch_data, idx = rec
    entry = arch_data[idx]
    current_fn = entry.get("filename") or ""
    current_base = extract_module_from_include(current_fn) if current_fn else None

    old_inc = extract_include_paths_from_prompt_text(old_prompt_text)
    new_inc = extract_include_paths_from_prompt_text(new_prompt_text)
    fresh = new_inc - old_inc

    existing_deps = list(entry.get("dependencies") or [])
    existing_set = set(existing_deps)

    for inc in sorted(fresh):
        dep_fn = _architecture_filename_for_module_include(inc, arch_data)
        if not dep_fn:
            continue
        dep_base = extract_module_from_include(dep_fn)
        if current_base and dep_base == current_base:
            continue
        if dep_fn == current_fn:
            continue
        if dep_fn in existing_set:
            continue
        added.append(dep_fn)
        existing_deps.append(dep_fn)
        existing_set.add(dep_fn)

    if not added:
        return {
            "updated": False,
            "architecture_path": arch_path,
            "added_dependencies": [],
            "messages": messages
            or ["No new module includes required architecture.json dependency updates."],
        }

    entry["dependencies"] = existing_deps

    if not dry_run:
        atomic_write_json(arch_path, arch_data)

    messages.append(
        f"Updated {arch_path.name}: added dependencies {added!r} for {current_fn!r}."
    )
    return {
        "updated": True,
        "architecture_path": arch_path,
        "added_dependencies": added,
        "messages": messages,
    }


def merge_auto_deps_includes_from_cwd(
    written_prompt_path: Path,
    old_prompt_text: str,
    new_prompt_text: str,
    *,
    dry_run: bool = False,
) -> Dict[str, Any]:
    """Resolve project root from ``written_prompt_path`` and run :func:`merge_auto_deps_includes_into_architecture`."""
    root = find_project_root(written_prompt_path.parent)
    return merge_auto_deps_includes_into_architecture(
        root,
        written_prompt_path,
        old_prompt_text,
        new_prompt_text,
        dry_run=dry_run,
    )
