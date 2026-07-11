"""Resolve lint commands for a given source file based on its language.\n\nProvides deterministic lint-command resolution for Python files (ruff + mypy).\nReturns an empty list for non-Python languages, signaling the caller to fall\nback to agent-discovered commands (hybrid contract).\n"""
from __future__ import annotations

from dataclasses import dataclass, field
from pathlib import Path
from typing import Optional


@dataclass
class LintCommand:
    """A resolved lint command with an optional working directory.\n\n    Attributes:\n        command: The resolved lint command string.\n        cwd: The working directory where the config was found.\n             ``None`` means the caller decides.\n    """

    command: str
    cwd: Optional[Path] = field(default=None)


def _find_config(
    start: Path,
    filenames: list[str],
    max_levels: int = 10,
) -> Optional[Path]:
    """Walk up from *start* looking for any of the given config filenames.\n\n    Parameters:\n        start: The directory to begin searching from.\n        filenames: Config file names to look for (e.g. ``["pyproject.toml"]``).\n        max_levels: Maximum number of parent directories to traverse.\n\n    Returns:\n        The directory containing the first match, or ``None`` if not found.\n    """
    current = start if start.is_dir() else start.parent
    current = current.resolve()

    for _ in range(max_levels):
        for name in filenames:
            if (current / name).is_file():
                return current
        parent = current.parent
        if parent == current:
            # Reached filesystem root
            break
        current = parent

    return None


def get_lint_commands(file: Path) -> list[LintCommand]:
    """Return the lint commands appropriate for *file*.\n\n    **Hybrid contract**: returns an **empty list** for languages without a\n    deterministic implementation (non-Python files).  An empty list signals\n    the orchestrator to fall back to agent-discovered commands.\n\n    For Python files (``.py`` extension) two commands are returned:\n\n    1. ``ruff check <file>`` \u2014 *cwd* set to the directory containing the\n       nearest ``pyproject.toml``, or ``None`` if not found.\n    2. ``mypy <file>`` \u2014 *cwd* set to the directory containing the nearest\n       ``pyproject.toml`` or ``mypy.ini``, or ``None`` if not found.\n\n    Parameters:\n        file: Path to the source file to lint.\n\n    Returns:\n        A list of :class:`LintCommand` instances, or an empty list when the\n        file's language is not supported deterministically.\n    """
    file = Path(file)

    if file.suffix != ".py":
        return []

    commands: list[LintCommand] = []

    # --- ruff -----------------------------------------------------------
    ruff_cwd = _find_config(file, ["pyproject.toml", "ruff.toml", ".ruff.toml"])
    commands.append(
        LintCommand(
            command=f"ruff check {file}",
            cwd=ruff_cwd,
        )
    )

    # --- mypy -----------------------------------------------------------
    mypy_cwd = _find_config(file, ["pyproject.toml", "mypy.ini"])
    commands.append(
        LintCommand(
            command=f"mypy {file}",
            cwd=mypy_cwd,
        )
    )

    return commands