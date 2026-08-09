"""
Update architecture.json dependencies after auto-deps inserts new module <include> tags.

When ``pdd auto-deps`` adds includes that reference other module prompts (or example
paths that map to a module basename), append the corresponding architecture
``filename`` values to the current module's ``dependencies`` list.
"""
from __future__ import annotations

import json
import logging
import re
from pathlib import Path
from typing import Any, Dict, List, Optional, Set, Tuple

logger = logging.getLogger(__name__)

from .architecture_include_validation import resolve_architecture_prompt_path
from .architecture_registry import extract_modules, find_architecture_for_project, find_project_root
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
        modules = extract_modules(data)
        if not modules:
            continue
        base = arch_path.parent
        for i, entry in enumerate(modules):
            fn = entry.get("filename") or ""
            if not fn:
                continue
            candidate = resolve_architecture_prompt_path(fn, base)
            try:
                if candidate.resolve() == target:
                    return arch_path, modules, i
            except OSError:
                continue
    return None


def _find_modules_array_start(text: str) -> int:
    """Return the byte offset of the ``[`` that opens the modules array.

    Handles both on-disk shapes for ``architecture.json``:
      - bare array: ``[ {...}, {...} ]`` → offset of first ``[``
      - dict wrapper: ``{"prd_files": [...], "modules": [ {...} ]}`` → offset of ``[`` after ``"modules":``

    Returns ``-1`` when no recognizable shape is found.
    """
    pos = 0
    while pos < len(text) and text[pos].isspace():
        pos += 1
    if pos >= len(text):
        return -1
    if text[pos] == "[":
        return pos
    if text[pos] != "{":
        return -1
    m = re.search(r'"modules"\s*:\s*\[', text)
    if m is None:
        return -1
    return m.end() - 1


def _find_array_element_span(text: str, array_start: int, element_index: int) -> Tuple[int, int]:
    """Return ``(start, end)`` spans of the ``element_index``-th element of the JSON
    array that opens at ``array_start`` (position of ``[``)."""
    decoder = json.JSONDecoder()
    pos = array_start
    if pos >= len(text) or text[pos] != "[":
        raise ValueError("Expected JSON array at given position")
    pos += 1
    while pos < len(text) and text[pos].isspace():
        pos += 1
    for _ in range(element_index):
        if pos >= len(text):
            raise ValueError("Array index out of range")
        if text[pos] == "]":
            raise ValueError("Array index out of range")
        _, obj_end = decoder.raw_decode(text, pos)
        pos = obj_end
        while pos < len(text) and text[pos].isspace():
            pos += 1
        if pos < len(text) and text[pos] == ",":
            pos += 1
            while pos < len(text) and text[pos].isspace():
                pos += 1
    if pos >= len(text) or text[pos] == "]":
        raise ValueError("Array index out of range")
    start = pos
    _, end = decoder.raw_decode(text, pos)
    return start, end


def _find_top_level_array_element_span(text: str, element_index: int) -> Tuple[int, int]:
    """Return ``(start, end)`` character spans of the ``element_index``-th top-level array element."""
    pos = 0
    while pos < len(text) and text[pos].isspace():
        pos += 1
    if pos >= len(text) or text[pos] != "[":
        raise ValueError("Expected top-level JSON array")
    return _find_array_element_span(text, pos, element_index)


def _find_dependencies_value_span_in_object(text: str, obj_start: int, obj_end: int) -> Optional[Tuple[int, int]]:
    """Return absolute ``(start, end)`` span of the ``dependencies`` value (any JSON value)."""
    fragment = text[obj_start:obj_end]
    decoder = json.JSONDecoder()
    m = re.search(r'"dependencies"\s*:', fragment)
    if not m:
        return None
    val_start = m.end()
    while val_start < len(fragment) and fragment[val_start].isspace():
        val_start += 1
    if val_start >= len(fragment):
        return None
    _, val_end_rel = decoder.raw_decode(fragment, val_start)
    return obj_start + val_start, obj_start + val_end_rel


def _serialize_deps_array_like(old_fragment: str, deps: List[str]) -> str:
    """Fallback: replace entire array, matching compact vs multiline style."""
    inner = old_fragment.strip()
    if len(inner) >= 2 and inner[0] == "[" and inner[-1] == "]":
        inner_body = inner[1:-1].strip()
        compact = "\n" not in inner_body
    else:
        compact = "\n" not in old_fragment
    if compact:
        return json.dumps(deps, ensure_ascii=False, separators=(",", ": "))
    return json.dumps(deps, indent=2, ensure_ascii=False)


def _minimal_dependencies_array_patch(old_text: str, new_list: List[str]) -> Optional[str]:
    """
    If ``new_list`` is ``old_list + appended`` (merge only ever suffix-appends), insert
    only the new string tokens before the closing ``]`` so the rest of the slice is
    byte-stable. Otherwise return None (caller uses full serialize).
    """
    try:
        old_list = json.loads(old_text)
    except json.JSONDecodeError:
        return None
    if not isinstance(old_list, list):
        return None
    if len(new_list) < len(old_list):
        return None
    if new_list[: len(old_list)] != old_list:
        return None
    appended = new_list[len(old_list) :]
    if not appended:
        return old_text

    arr_start = old_text.find("[")
    if arr_start < 0:
        return None
    decoder = json.JSONDecoder()
    try:
        obj, end = decoder.raw_decode(old_text, arr_start)
    except json.JSONDecodeError:
        return None
    if obj != old_list:
        return None

    segment = old_text[arr_start:end]
    inner = segment[1:-1] if len(segment) >= 2 else ""
    compact = "\n" not in inner

    if len(obj) == 0:
        dumped = json.dumps(new_list, ensure_ascii=False, separators=(",", ": "))
        if not compact:
            dumped = json.dumps(new_list, indent=2, ensure_ascii=False)
        return old_text[:arr_start] + dumped + old_text[end:]

    inner = old_text[arr_start + 1 : end - 1]
    inner_stripped = inner.rstrip()
    tail = inner[len(inner_stripped) :]

    if compact:
        insert = ", " + ", ".join(json.dumps(x, ensure_ascii=False) for x in appended)
    else:
        elem_indent = "  "
        for line in segment.split("\n"):
            m = re.match(r"^(\s+)\"", line)
            if m:
                elem_indent = m.group(1)
                break
        insert = ",\n" + elem_indent + (",\n" + elem_indent).join(
            json.dumps(x, ensure_ascii=False) for x in appended
        )

    return old_text[: arr_start + 1 + len(inner_stripped)] + insert + tail + old_text[end - 1 :]


def _replace_dependencies_in_architecture_text(
    raw: str, entry_index: int, new_dependencies: List[str]
) -> Optional[str]:
    """
    Replace only the ``dependencies`` value for ``entry_index`` in the modules array.

    Works for both on-disk shapes: bare array ``[...]`` and dict wrapper
    ``{"prd_files": [...], "modules": [...]}``. Returns ``None`` if the file
    layout is not patchable (falls back to full rewrite).
    """
    array_start = _find_modules_array_start(raw)
    if array_start < 0:
        return None
    try:
        obj_start, obj_end = _find_array_element_span(raw, array_start, entry_index)
    except (ValueError, json.JSONDecodeError):
        return None
    span = _find_dependencies_value_span_in_object(raw, obj_start, obj_end)
    if span is None:
        return None
    dep_start, dep_end = span
    old_dep_text = raw[dep_start:dep_end]
    new_dep_text = _minimal_dependencies_array_patch(old_dep_text, new_dependencies)
    if new_dep_text is None:
        new_dep_text = _serialize_deps_array_like(old_dep_text, new_dependencies)
    updated = raw[:dep_start] + new_dep_text + raw[dep_end:]
    try:
        json.loads(updated)
    except json.JSONDecodeError:
        return None
    return updated


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

    deps_before_snapshot = list(entry.get("dependencies") or [])
    existing_deps = list(deps_before_snapshot)
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
        try:
            raw = arch_path.read_text(encoding="utf-8")
        except OSError as exc:
            logger.warning("Could not read %s for surgical arch update: %s", arch_path, exc)
            entry["dependencies"] = deps_before_snapshot
            return {
                "updated": False,
                "architecture_path": arch_path,
                "added_dependencies": added,
                "messages": messages
                + [
                    f"Could not read {arch_path.name} to update dependencies; file left unchanged. "
                    f"(Would have added {added!r} for {current_fn!r}.)"
                ],
            }

        patched = _replace_dependencies_in_architecture_text(raw, idx, existing_deps)
        if patched is None:
            entry["dependencies"] = deps_before_snapshot
            logger.warning(
                "Could not patch dependencies in place for %s index %s; skipping write (no full-file fallback)",
                arch_path,
                idx,
            )
            return {
                "updated": False,
                "architecture_path": arch_path,
                "added_dependencies": added,
                "messages": messages
                + [
                    f"Could not patch {arch_path.name} in place; file left unchanged. "
                    f"(Would have added {added!r} for {current_fn!r}.)"
                ],
            }

        if raw.endswith("\n"):
            if not patched.endswith("\n"):
                patched += "\n"
        else:
            patched = patched.rstrip("\n")
        try:
            arch_path.write_text(patched, encoding="utf-8")
        except OSError as exc:
            logger.warning("Could not write %s: %s", arch_path, exc)
            entry["dependencies"] = deps_before_snapshot
            return {
                "updated": False,
                "architecture_path": arch_path,
                "added_dependencies": added,
                "messages": messages
                + [
                    f"Could not write {arch_path.name}; file left unchanged. "
                    f"(Would have added {added!r} for {current_fn!r}.)"
                ],
            }

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
