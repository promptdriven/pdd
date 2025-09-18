from __future__ import annotations

import json
from dataclasses import dataclass
from pathlib import Path
from typing import Any, Dict, Iterable, List, Optional, Tuple

import yaml

try:
    # Python 3.11+
    from importlib.resources import files as pkg_files
except ImportError:  # pragma: no cover
    # Fallback for older Python, though project targets 3.12+
    from importlib_resources import files as pkg_files  # type: ignore


@dataclass
class TemplateMeta:
    name: str
    path: Path
    description: str = ""
    version: str = ""
    tags: List[str] = None  # type: ignore
    language: str = ""
    output: str = ""
    variables: Dict[str, Any] = None  # type: ignore
    usage: Dict[str, Any] = None  # type: ignore
    discover: Dict[str, Any] = None  # type: ignore
    output_schema: Dict[str, Any] = None  # type: ignore
    notes: str = ""


def _parse_front_matter(text: str) -> Tuple[Optional[Dict[str, Any]], str]:
    if not text.startswith("---\n"):
        return None, text
    end_idx = text.find("\n---", 4)
    if end_idx == -1:
        return None, text
    fm_body = text[4:end_idx]
    rest = text[end_idx + len("\n---"):]
    if rest.startswith("\n"):
        rest = rest[1:]
    try:
        meta = yaml.safe_load(fm_body) or {}
        if not isinstance(meta, dict):
            meta = {}
    except Exception:
        meta = {}
    return meta, rest


def _normalize_meta(meta: Dict[str, Any], path: Path) -> TemplateMeta:
    name = str(meta.get("name") or path.stem)
    description = str(meta.get("description") or "")
    version = str(meta.get("version") or "")
    language = str(meta.get("language") or "")
    output = str(meta.get("output") or "")
    tags_raw = meta.get("tags") or []
    if isinstance(tags_raw, str):
        tags = [tags_raw.lower()]
    else:
        tags = [str(t).lower() for t in (tags_raw or [])]
    return TemplateMeta(
        name=name,
        path=path.resolve(),
        description=description,
        version=version,
        tags=tags,
        language=language,
        output=output,
        variables=meta.get("variables") or {},
        usage=meta.get("usage") or {},
        discover=meta.get("discover") or {},
        output_schema=meta.get("output_schema") or {},
        notes=str(meta.get("notes") or ""),
    )


def _iter_project_templates() -> Iterable[Path]:
    root = Path.cwd() / "prompts"
    if not root.exists():
        return []
    return root.rglob("*.prompt")


def _iter_packaged_templates() -> Iterable[Path]:
    try:
        pkg_root = pkg_files("pdd").joinpath("templates")
        if not pkg_root.is_dir():
            return []
        return (Path(str(p)) for p in pkg_root.rglob("*.prompt"))
    except Exception:
        return []


def _load_meta_from_path(path: Path) -> Optional[TemplateMeta]:
    try:
        text = path.read_text(encoding="utf-8")
    except Exception:
        return None
    fm, _ = _parse_front_matter(text)
    if not fm:
        return None
    try:
        return _normalize_meta(fm, path)
    except Exception:
        return None


def _index_templates() -> Dict[str, TemplateMeta]:
    index: Dict[str, TemplateMeta] = {}
    # Project templates override packaged ones
    for p in _iter_packaged_templates():
        meta = _load_meta_from_path(p)
        if meta and meta.name not in index:
            index[meta.name] = meta
    for p in _iter_project_templates():
        meta = _load_meta_from_path(p)
        if meta:
            index[meta.name] = meta
    return index


def list_templates(filter_tag: Optional[str] = None) -> List[Dict[str, Any]]:
    idx = _index_templates()
    items: List[Dict[str, Any]] = []
    for meta in idx.values():
        if filter_tag and filter_tag.lower() not in (meta.tags or []):
            continue
        items.append({
            "name": meta.name,
            "path": str(meta.path),
            "description": meta.description,
            "version": meta.version,
            "tags": meta.tags or [],
        })
    # Sort by name for stable output
    items.sort(key=lambda d: d["name"])  # type: ignore
    return items


def load_template(name: str) -> Dict[str, Any]:
    idx = _index_templates()
    if name not in idx:
        raise FileNotFoundError(f"Template '{name}' not found.")
    meta = idx[name]
    return {
        "name": meta.name,
        "path": str(meta.path),
        "description": meta.description,
        "version": meta.version,
        "tags": meta.tags or [],
        "language": meta.language,
        "output": meta.output,
        "variables": meta.variables or {},
        "usage": meta.usage or {},
        "discover": meta.discover or {},
        "output_schema": meta.output_schema or {},
        "notes": meta.notes or "",
    }


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
    src = Path(meta["path"])  # absolute
    dest_root = Path(dest_dir)
    dest_root.mkdir(parents=True, exist_ok=True)
    dest = dest_root / src.name
    contents = src.read_text(encoding="utf-8")
    dest.write_text(contents, encoding="utf-8")
    return str(dest.resolve())

