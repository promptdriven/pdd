"""Atomic JSON file writes — avoid half-written architecture.json on failure."""
from __future__ import annotations

import json
import os
import tempfile
from pathlib import Path
from typing import Any


def atomic_write_json_leading(path: Path, data: Any, *, indent: int = 2) -> None:
    """Write JSON to ``path`` via a temp file in the same directory and ``os.replace``."""
    path = path.resolve()
    path.parent.mkdir(parents=True, exist_ok=True)
    fd, tmp = tempfile.mkstemp(
        dir=str(path.parent),
        prefix=f".{path.name}.",
        suffix=".tmp",
    )
    try:
        with os.fdopen(fd, "w", encoding="utf-8") as f:
            json.dump(data, f, indent=indent, ensure_ascii=False)
            f.write("\n")
            f.flush()
            os.fsync(f.fileno())
        os.replace(tmp, path)
    except BaseException:
        try:
            os.unlink(tmp)
        except OSError:
            pass
        raise


def atomic_write_text_leading(path: Path, text: str, *, encoding: str = "utf-8") -> None:
    """Write *text* to *path* via a temp file in the same directory and ``os.replace``.

    Flushes and fsyncs before renaming so a crash during the write cannot leave
    the target file in a partially-written state.  The caller is responsible for
    ensuring ``path.parent`` exists before calling.
    """
    fd, tmp = tempfile.mkstemp(
        dir=str(path.parent),
        prefix=f".{path.name}.",
        suffix=".tmp",
    )
    try:
        with os.fdopen(fd, "w", encoding=encoding) as f:
            f.write(text)
            f.flush()
            os.fsync(f.fileno())
        os.replace(tmp, path)
    except BaseException:
        try:
            os.unlink(tmp)
        except OSError:
            pass
        raise
