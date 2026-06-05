"""Resolve prompt-shaped ``pdd checkup`` targets to concrete ``.prompt`` paths."""
from __future__ import annotations

from pathlib import Path
from typing import Optional

import click

from .checkup_target import CheckupTargetKind, classify_checkup_target
from .evidence_store import resolve_prompt_path


def _discover_prompt_files(target: Path) -> list[Path]:
    if target.is_file():
        if target.suffix.lower() != ".prompt":
            raise click.UsageError(f"Expected a .prompt file, got: {target}")
        return [target.resolve()]
    if not target.is_dir():
        raise click.UsageError(f"Target not found: {target}")
    prompts = sorted(
        path.resolve()
        for path in target.rglob("*.prompt")
        if not path.name.lower().endswith("_llm.prompt")
    )
    if not prompts:
        raise click.UsageError(f"No .prompt files found under {target}")
    return prompts


def resolve_devunit_prompts(devunit: str, project_root: Path) -> list[Path]:
    """Resolve ``prompts/<devunit>_*.prompt`` excluding ``*_LLM.prompt`` files."""
    basename = devunit.strip()
    if not basename:
        raise click.UsageError("Missing devunit name.")

    prompts_dir = project_root / "prompts"
    matches = sorted(
        path.resolve()
        for path in prompts_dir.glob(f"{basename}_*.prompt")
        if not path.name.lower().endswith("_llm.prompt")
    )
    if matches:
        return matches

    resolved = resolve_prompt_path(project_root, basename)
    if resolved is not None:
        return [resolved.resolve()]

    raise click.UsageError(
        f"Could not resolve devunit {devunit!r}. "
        f"Expected prompts/{basename}_*.prompt under {project_root}."
    )


def resolve_prompt_targets(
    target: str,
    *,
    project_root: Optional[Path] = None,
) -> list[Path]:
    """Resolve a file, directory, or devunit target to one or more prompt paths."""
    root = (project_root or Path.cwd()).resolve()
    raw = target.strip()
    if not raw:
        raise click.UsageError("Missing prompt TARGET.")

    kind = classify_checkup_target(raw, project_root=root)
    if kind == CheckupTargetKind.DEVUNIT:
        return resolve_devunit_prompts(raw, root)

    rooted = (root / raw).resolve()
    if rooted.exists():
        return _discover_prompt_files(rooted)

    candidate = Path(raw)
    if candidate.is_absolute() and candidate.exists():
        return _discover_prompt_files(candidate.resolve())
    if candidate.exists():
        return _discover_prompt_files(candidate.resolve())

    search_names = [raw]
    if not raw.endswith(".prompt"):
        search_names.extend(
            [
                f"{raw}_python.prompt",
                f"{raw}.prompt",
                f"prompts/{raw}_python.prompt",
                f"prompts/{raw}.prompt",
            ]
        )
    for name in search_names:
        path = Path(name)
        if path.is_file():
            return [path.resolve()]
        nested = root / name
        if nested.is_file():
            return [nested.resolve()]
        if nested.is_dir():
            return _discover_prompt_files(nested.resolve())

    if kind == CheckupTargetKind.DEVUNIT:
        return resolve_devunit_prompts(raw, root)

    raise click.UsageError(
        f"Could not resolve prompt target {target!r}. "
        "Use a path, directory, devunit basename, or `*_python.prompt` filename."
    )
