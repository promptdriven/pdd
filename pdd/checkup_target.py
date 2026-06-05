"""Classify ``pdd checkup`` CLI targets into prompt, issue, or unknown kinds."""
from __future__ import annotations

import re
from enum import Enum
from pathlib import Path
from typing import Optional

from .agentic_sync import _is_github_issue_url

_DEVUNIT_NAME_RE = re.compile(r"^[\w-]+$")


class CheckupTargetKind(str, Enum):
    """Supported high-level checkup target kinds."""

    PROMPT_FILE = "prompt_file"
    PROMPT_DIRECTORY = "prompt_directory"
    DEVUNIT = "devunit"
    GITHUB_ISSUE = "github_issue"
    UNKNOWN = "unknown"


def classify_checkup_target(
    target: Optional[str],
    *,
    project_root: Optional[Path] = None,
) -> CheckupTargetKind:
    """Return the target kind for a positional ``pdd checkup`` argument."""
    if not target or not str(target).strip():
        return CheckupTargetKind.UNKNOWN

    raw = str(target).strip()
    if _is_github_issue_url(raw):
        return CheckupTargetKind.GITHUB_ISSUE

    root = (project_root or Path.cwd()).resolve()
    candidate = Path(raw)

    if candidate.suffix.lower() == ".prompt":
        return CheckupTargetKind.PROMPT_FILE

    for path in (candidate, root / raw):
        if path.is_file() and path.suffix.lower() == ".prompt":
            return CheckupTargetKind.PROMPT_FILE
        if path.is_dir():
            return CheckupTargetKind.PROMPT_DIRECTORY

    if _DEVUNIT_NAME_RE.fullmatch(raw) and "/" not in raw and not raw.startswith("."):
        return CheckupTargetKind.DEVUNIT

    return CheckupTargetKind.UNKNOWN


def _devunit_prompts_exist(devunit: str, project_root: Path) -> bool:
    """Return True when *devunit* resolves to at least one prompt file."""
    basename = devunit.strip()
    if not basename:
        return False

    prompts_dir = project_root / "prompts"
    if any(
        path
        for path in prompts_dir.glob(f"{basename}_*.prompt")
        if not path.name.lower().endswith("_llm.prompt")
    ):
        return True

    from .evidence_store import resolve_prompt_path

    return resolve_prompt_path(project_root, basename) is not None


def is_prompt_shaped_target(
    target: Optional[str],
    *,
    project_root: Optional[Path] = None,
) -> bool:
    """Return True when *target* should run the unified prompt source-set report."""
    kind = classify_checkup_target(target, project_root=project_root)
    if kind in {
        CheckupTargetKind.PROMPT_FILE,
        CheckupTargetKind.PROMPT_DIRECTORY,
    }:
        return True
    if kind == CheckupTargetKind.DEVUNIT:
        root = (project_root or Path.cwd()).resolve()
        return _devunit_prompts_exist(str(target).strip(), root)
    return False
