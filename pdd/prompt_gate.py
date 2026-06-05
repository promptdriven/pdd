"""Automatic prompt quality gate configuration and workflow hooks."""
from __future__ import annotations

import logging
from pathlib import Path
from typing import Optional, Sequence

import click

from .checkup_prompt_main import (
    render_automatic_gate_summary,
    run_checkup_prompt_paths,
)

logger = logging.getLogger(__name__)

_PROMPT_GATE_MODES = frozenset({"off", "warn", "strict"})
_DEFAULT_MODE = "warn"


def load_prompt_gate_config(project_root: Path) -> str:
    """Load ``checkup.prompt_gate`` from ``pyproject.toml`` ``[tool.pdd.checkup]``."""
    pyproject = project_root / "pyproject.toml"
    if not pyproject.is_file():
        return _DEFAULT_MODE
    try:
        import tomllib

        data = tomllib.loads(pyproject.read_text(encoding="utf-8"))
    except (OSError, ValueError, ImportError):
        return _DEFAULT_MODE

    checkup = data.get("tool", {}).get("pdd", {}).get("checkup", {})
    if not isinstance(checkup, dict):
        return _DEFAULT_MODE
    mode = str(checkup.get("prompt_gate", _DEFAULT_MODE)).strip().lower()
    if mode not in _PROMPT_GATE_MODES:
        logger.warning("Unknown checkup.prompt_gate value %r; using %r", mode, _DEFAULT_MODE)
        return _DEFAULT_MODE
    return mode


def resolve_prompt_gate_mode(
    *,
    cli_prompt_checkup: Optional[str],
    no_prompt_checkup: bool,
    project_root: Path,
) -> str:
    """Resolve effective gate mode: CLI overrides config."""
    if no_prompt_checkup:
        return "off"
    if cli_prompt_checkup is not None:
        mode = cli_prompt_checkup.strip().lower()
        if mode not in {"warn", "strict"}:
            raise click.BadParameter(
                "--prompt-checkup must be 'warn' or 'strict'.",
                param_hint="'--prompt-checkup'",
            )
        return mode
    return load_prompt_gate_config(project_root)


def filter_changed_prompt_paths(paths: Sequence[str | Path]) -> list[Path]:
    """Keep only changed ``.prompt`` files, excluding ``*_LLM.prompt``."""
    prompt_paths: list[Path] = []
    for raw in paths:
        path = Path(raw)
        if path.suffix.lower() != ".prompt":
            continue
        if path.name.lower().endswith("_llm.prompt"):
            continue
        prompt_paths.append(path.resolve())
    return prompt_paths


def run_automatic_prompt_gate(
    prompt_paths: Sequence[Path],
    *,
    mode: str,
    project_root: Path,
    quiet: bool = False,
    strict: bool = False,
) -> tuple[bool, int]:
    """
    Run automatic prompt checkup on changed prompt files.

    Returns ``(should_continue, exit_code)``. ``should_continue`` is False only
    when ``mode == 'strict'`` and deterministic checks fail.
    """
    if mode == "off" or not prompt_paths:
        return True, 0

    reports, exit_code = run_checkup_prompt_paths(
        prompt_paths,
        project_root=project_root,
        strict=strict or mode == "strict",
    )
    render_automatic_gate_summary(reports, mode=mode, quiet=quiet)

    if mode == "strict" and exit_code != 0:
        return False, exit_code
    return True, 0
