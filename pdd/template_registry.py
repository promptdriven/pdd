from __future__ import annotations

import re
import shutil
from collections.abc import Iterable as IterableABC
from dataclasses import dataclass, field
from pathlib import Path
from typing import Any, Dict, Iterable, List, Optional, Tuple

from importlib.resources import as_file

try:
    from importlib.resources import files as pkg_files
except ImportError:  # pragma: no cover
    # Fallback for Python < 3.11 if needed.
    from importlib_resources import files as pkg_files  # type: ignore[attr-defined]


_FRONT_MATTER_PATTERN = re.compile(r"^---\s*\r?\n(.*?)\r?\n---\s*\r?\n?", re.DOTALL)
_SOURCE_PRIORITY = {"packaged": 0, "project": 1}


@dataclass
class TemplateMeta:
    name: str
    path: Path
    description: str = ""
    version: str = ""
    tags: List[str] = field(default_factory=list)
    language: str = ""
    output: str = ""
    variables: Dict[str, Any] = field(default_factory=dict)
    usage: Dict[str, Any] = field(default_factory=dict)
    discover: Dict[str, Any] = field(default_factory=dict)
    output_schema: Dict[str, Any] = field(default_factory=dict)
    notes: str = ""
    source: str = "packaged"

    @property
    def alias(self) -> str:
        return self.path.stem


def _safe_load_yaml(text: str) -> Optional[Dict[str, Any]]:
    try:
        import yaml  # type: ignore
    except ImportError as exc:  # pragma: no cover - PyYAML is an install requirement
        raise RuntimeError("PyYAML is required to parse template front matter") from exc

    try:
        data = yaml.safe_load(text) or {}
    except Exception:
        return None
    if not isinstance(data, dict):
        return None
    return data


def _parse_front_matter(text: str) -> Tuple[Optional[Dict[str, Any]], str]:
    match = _FRONT_MATTER_PATTERN.match(text)
    if not match:
        return None, text
    meta_text = match.group(1)
    rest = text[match.end():]
    meta = _safe_load_yaml(meta_text)
    return meta, rest


def _normalize_tags(tags: Any) -> List[str]:
    if tags is None:
        return []
    if isinstance(tags, str):
        return [tags.lower()]
    if isinstance(tags, IterableABC):
        normalized: List[str] = []
        for tag in tags:
            if tag is None:
                continue
            normalized.append(str(tag).lower())
        return normalized
    return []


def _ensure_mapping(value: Any) -> Dict[str, Any]:
    if isinstance(value, dict):
        return dict(value)
    return {}


def _normalize_meta(raw: Dict[str, Any], path: Path, source: str) -> TemplateMeta:
    name = str(raw.get("name") or path.stem)
    description = str(raw.get("description") or "")
    version = str(raw.get("version") or "")
    language = str(raw.get("language") or "")
    output = str(raw.get("output") or "")
    tags = _normalize_tags(raw.get("tags"))
    notes_raw = raw.get("notes")
    notes = "" if notes_raw is None else str(notes_raw)

    return TemplateMeta(
        name=name,
        path=path.resolve(),
        description=description,
        version=version,
        tags=tags,
        language=language,
        output=output,
        variables=_ensure_mapping(raw.get("variables")),
        usage=_ensure_mapping(raw.get("usage")),
        discover=_ensure_mapping(raw.get("discover")),
        output_schema=_ensure_mapping(raw.get("output_schema")),
        notes=notes,
        source=source,
    )


def _iter_project_templates() -> Iterable[Path]:
    root = Path.cwd() / "prompts"
    if not root.exists():
        return ()
    return (path for path in root.rglob("*.prompt") if path.is_file())


def _iter_packaged_templates() -> Iterable[Path]:
    try:
        pkg_root = pkg_files("pdd").joinpath("templates")
    except ModuleNotFoundError:  # pragma: no cover - package missing
        return ()
    if not pkg_root.is_dir():
        return ()

    resolved: List[Path] = []
    for entry in pkg_root.rglob("*.prompt"):  # type: ignore[attr-defined]
        try:
            with as_file(entry) as concrete:
                path = Path(concrete)
                if path.is_file():
                    resolved.append(path)
        except FileNotFoundError:
            continue
    return resolved


def _load_meta_from_path(path: Path, source: str) -> Optional[TemplateMeta]:
    try:
        text = path.read_text(encoding="utf-8")
    except OSError:
        return None
    front_matter, _ = _parse_front_matter(text)
    if not front_matter:
        return None
    return _normalize_meta(front_matter, path, source)


def _index_templates() -> Tuple[Dict[str, TemplateMeta], Dict[str, TemplateMeta]]:
    by_name: Dict[str, TemplateMeta] = {}
    priority: Dict[str, int] = {}

    def register(meta: TemplateMeta) -> None:
        current_priority = priority.get(meta.name, -1)
        new_priority = _SOURCE_PRIORITY.get(meta.source, 0)
        if new_priority < current_priority:
            return
        by_name[meta.name] = meta
        priority[meta.name] = new_priority

    for path in _iter_packaged_templates():
        meta = _load_meta_from_path(Path(path), "packaged")
        if meta:
            register(meta)

    for path in _iter_project_templates():
        meta = _load_meta_from_path(Path(path), "project")
        if meta:
            register(meta)

    lookup = dict(by_name)
    lookup_priority = priority.copy()

    for meta in by_name.values():
        alias = meta.alias
        alias_priority = lookup_priority.get(alias, -1)
        meta_priority = priority.get(meta.name, 0)
        if alias_priority <= meta_priority:
            lookup[alias] = meta
            lookup_priority[alias] = meta_priority

    return by_name, lookup


def _meta_to_payload(meta: TemplateMeta) -> Dict[str, Any]:
    return {
        "name": meta.name,
        "path": str(meta.path),
        "description": meta.description,
        "version": meta.version,
        "tags": list(meta.tags),
        "language": meta.language,
        "output": meta.output,
        "variables": dict(meta.variables),
        "usage": dict(meta.usage),
        "discover": dict(meta.discover),
        "output_schema": dict(meta.output_schema),
        "notes": meta.notes,
    }


def list_templates(filter_tag: Optional[str] = None) -> List[Dict[str, Any]]:
    by_name, _ = _index_templates()
    normalized_tag = filter_tag.lower() if filter_tag else None
    items: List[Dict[str, Any]] = []
    for meta in by_name.values():
        if normalized_tag and normalized_tag not in meta.tags:
            continue
        items.append({
            "name": meta.name,
            "path": str(meta.path),
            "description": meta.description,
            "version": meta.version,
            "tags": list(meta.tags),
        })
    items.sort(key=lambda item: item["name"].lower())
    return items


def load_template(name: str) -> Dict[str, Any]:
    _, lookup = _index_templates()
    meta = lookup.get(name)
    if not meta:
        raise FileNotFoundError(f"Template '{name}' not found.")
    return _meta_to_payload(meta)


def show_template(name: str) -> Dict[str, Any]:
    meta = load_template(name)
    summary = {
        "name": meta["name"],
        "path": meta["path"],
        "description": meta.get("description", ""),
        "version": meta.get("version", ""),
        "tags": meta.get("tags", []),
        "language": meta.get("language", ""),
        "output": meta.get("output", ""),
    }
    return {
        "summary": summary,
        "variables": meta.get("variables", {}),
        "usage": meta.get("usage", {}),
        "discover": meta.get("discover", {}),
        "output_schema": meta.get("output_schema", {}),
        "notes": meta.get("notes", ""),
    }


def copy_template(name: str, dest_dir: str) -> str:
    meta = load_template(name)
    src = Path(meta["path"])
    if not src.exists():
        raise FileNotFoundError(f"Template '{name}' file is missing at {src}")
    dest_root = Path(dest_dir)
    dest_root.mkdir(parents=True, exist_ok=True)
    dest_path = dest_root / src.name
    shutil.copy2(src, dest_path)
    return str(dest_path.resolve())
