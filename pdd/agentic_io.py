from __future__ import annotations
from pathlib import Path
from typing import Dict, List

from .agentic_extract import normalize_code_text
from .agentic_logging import print_head
from .agentic_logging import verbose as _v

def print_diff(old: str, new: str, path: Path) -> None:
    import difflib
    old_lines = old.splitlines(keepends=True)
    new_lines = new.splitlines(keepends=True)
    diff = list(difflib.unified_diff(old_lines, new_lines, fromfile=f"{path} (before)", tofile=f"{path} (after)"))
    if not diff:
        return
    text = "".join(diff)
    print_head("Unified diff (first lines)", text)

def apply_file_map(file_map: Dict[str, str], project_root: Path, primary_code_path: Path, allow_new: bool, normalizer) -> List[Path]:
    from .agentic_paths import normalize_target_path
    applied: List[Path] = []
    for emitted, body in file_map.items():
        target = normalize_target_path(emitted, project_root, primary_code_path, allow_new)
        if target is None:
            continue
        body_to_write = normalizer(body)
        old = ""
        if target.exists():
            try:
                old = target.read_text(encoding="utf-8")
            except Exception:
                old = ""
        target.parent.mkdir(parents=True, exist_ok=True)
        target.write_text(body_to_write, encoding="utf-8")
        print_diff(old, body_to_write, target)
        applied.append(target)
    return applied
