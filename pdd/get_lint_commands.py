"""Resolve lint commands for a given source file based on its language.

Provides deterministic lint-command resolution for Python, JavaScript, TypeScript, Ruby, and Go.
Returns an empty list for other languages, signaling the caller to fall back to agent-discovered
commands (hybrid contract).
"""
from __future__ import annotations

from dataclasses import dataclass, field
from pathlib import Path
from typing import Optional


@dataclass
class LintCommand:
    """A resolved lint command with an optional working directory.

    Attributes:
        command: The resolved lint command string.
        cwd: The working directory where the config was found.
             ``None`` means the caller decides.
    """

    command: str
    cwd: Optional[Path] = field(default=None)


def _find_config(
    start: Path,
    filenames: list[str],
    max_levels: int = 10,
) -> Optional[Path]:
    """Walk up from *start* looking for any of the given config filenames.

    Parameters:
        start: The directory to begin searching from.
        filenames: Config file names to look for (e.g. ``["pyproject.toml"]``).
        max_levels: Maximum number of parent directories to traverse.

    Returns:
        The directory containing the first match, or ``None`` if not found.
    """
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
    """Return the lint commands appropriate for *file*.

    **Hybrid contract**: returns an **empty list** for languages without a
    deterministic implementation. An empty list signals the orchestrator to
    fall back to agent-discovered commands.

    Supported languages:
    - Python (.py): py_compile, ruff, mypy
    - JavaScript/TypeScript (.js, .jsx, .ts, .tsx): eslint
    - Ruby (.rb): ruby -c, rubocop
    - Go (.go): go fmt, go vet

    Parameters:
        file: Path to the source file to lint.

    Returns:
        A list of :class:`LintCommand` instances, or an empty list when the
        file's language is not supported deterministically.
    """
    file = Path(file)
    suffix = file.suffix.lower()

    # --- Python ---------------------------------------------------------
    if suffix == ".py":
        commands: list[LintCommand] = []

        # py_compile (syntax check)
        commands.append(LintCommand(command=f"python -m py_compile {file}"))

        # ruff
        ruff_cwd = _find_config(file, ["pyproject.toml", "ruff.toml", ".ruff.toml", ".git"])
        commands.append(LintCommand(command=f"ruff check {file}", cwd=ruff_cwd))

        # mypy
        mypy_cwd = _find_config(file, ["pyproject.toml", "mypy.ini", ".git"])
        commands.append(LintCommand(command=f"mypy {file}", cwd=mypy_cwd))

        return commands

    # --- JS / TS --------------------------------------------------------
    if suffix in (".js", ".jsx", ".ts", ".tsx"):
        eslint_cwd = _find_config(
            file, ["package.json", ".eslintrc", "eslint.config.js", ".git"]
        )
        return [LintCommand(command=f"eslint {file}", cwd=eslint_cwd)]

    # --- Ruby -----------------------------------------------------------
    if suffix == ".rb":
        rubocop_cwd = _find_config(file, [".rubocop.yml", "Gemfile", ".git"])
        return [
            LintCommand(command=f"ruby -c {file}"),
            LintCommand(command=f"rubocop {file}", cwd=rubocop_cwd),
        ]

    # --- Go -------------------------------------------------------------
    if suffix == ".go":
        go_cwd = _find_config(file, ["go.mod", ".git"])
        return [
            LintCommand(command=f"go fmt {file}"),
            LintCommand(command=f"go vet {file}", cwd=go_cwd),
        ]

    return []
