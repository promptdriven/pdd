from __future__ import annotations
import os
from pathlib import Path
from typing import Optional

def _safe_is_subpath(child: Path, parent: Path) -> bool:
    try:
        child.resolve().relative_to(parent.resolve())
        return True
    except Exception:
        return False

_COMMON_FIXED_SUFFIXES = ("_fixed", ".fixed", "-fixed")

def _strip_common_suffixes(name: str) -> str:
    base, ext = os.path.splitext(name)
    for suf in _COMMON_FIXED_SUFFIXES:
        if base.endswith(suf):
            base = base[: -len(suf)]
            break
    return base + ext

def _find_existing_by_basename(project_root: Path, basename: str) -> Optional[Path]:
    try:
        for p in project_root.rglob(basename):
            if p.is_file():
                return p.resolve()
    except Exception:
        return None
    return None

def normalize_target_path(emitted_path: str, project_root: Path, primary_code_path: Path, allow_new: bool) -> Optional[Path]:
    p = Path(emitted_path)
    if not p.is_absolute():
        p = (project_root / emitted_path).resolve()

    if not _safe_is_subpath(p, project_root):
        return None

    if p.exists():
        return p

    emitted_base = Path(emitted_path).name
    primary_base = primary_code_path.name

    if emitted_base == primary_base:
        return primary_code_path

    if _strip_common_suffixes(emitted_base) == primary_base:
        return primary_code_path

    existing = _find_existing_by_basename(project_root, emitted_base)
    if existing:
        return existing

    if not allow_new:
        return None

    return p
