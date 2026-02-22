from __future__ import annotations

import os
from pathlib import Path
from typing import Optional

from rich.console import Console
from rich.syntax import Syntax

console = Console()

# Language detection markers
PYTHON_MARKERS = ("setup.py", "pyproject.toml", "setup.cfg", "Pipfile", "requirements.txt")
TYPESCRIPT_MARKERS = ("package.json",)
GO_MARKERS = ("go.mod",)

# Path defaults per language
LANGUAGE_DEFAULTS: dict[str, dict[str, str]] = {
    "python": {
        "generate_output_path": "pdd/",
        "test_output_path": "tests/",
        "example_output_path": "context/",
    },
    "typescript": {
        "generate_output_path": "src/",
        "test_output_path": "__tests__/",
        "example_output_path": "examples/",
    },
    "go": {
        "generate_output_path": ".",
        "test_output_path": ".",
        "example_output_path": "examples/",
    },
}

# Standard defaults
STANDARD_DEFAULTS: dict[str, float | int] = {
    "strength": 0.818,
    "temperature": 0.0,
    "target_coverage": 80.0,
    "budget": 10.0,
    "max_attempts": 3,
}

PDDRC_FILENAME = ".pddrc"


def _detect_language(cwd: Path) -> Optional[str]:
    """Detect project language based on marker files in the current directory.

    Returns the detected language string or ``None`` if the project type
    cannot be determined automatically.
    """
    # Check Python markers
    for marker in PYTHON_MARKERS:
        if (cwd / marker).exists():
            return "python"

    # Check TypeScript – look for typescript in package.json dependencies
    package_json_path = cwd / "package.json"
    if package_json_path.exists():
        try:
            import json

            with open(package_json_path, "r", encoding="utf-8") as fh:
                pkg = json.load(fh)
            all_deps: dict[str, str] = {}
            all_deps.update(pkg.get("dependencies", {}))
            all_deps.update(pkg.get("devDependencies", {}))
            if "typescript" in all_deps:
                return "typescript"
        except (json.JSONDecodeError, OSError):
            pass

    # Check Go markers
    for marker in GO_MARKERS:
        if (cwd / marker).exists():
            return "go"

    return None


def _prompt_language() -> str:
    """Interactively ask the user to choose a project language."""
    console.print("\n[warning]Could not auto-detect project language.[/warning]")
    console.print("  [bold]1)[/bold] Python")
    console.print("  [bold]2)[/bold] TypeScript")
    console.print("  [bold]3)[/bold] Go")

    while True:
        choice = console.input("\nSelect language [1/2/3]: ").strip()
        if choice == "1":
            return "python"
        elif choice == "2":
            return "typescript"
        elif choice == "3":
            return "go"
        else:
            console.print("[error]Invalid choice. Please enter 1, 2, or 3.[/error]")


def _build_pddrc_content(language: str) -> str:
    """Build the YAML content for a ``.pddrc`` file.

    Parameters
    ----------
    language:
        One of ``"python"``, ``"typescript"``, or ``"go"``.

    Returns
    -------
    str
        The full YAML string ready to be written to disk.
    """
    paths = LANGUAGE_DEFAULTS.get(language, LANGUAGE_DEFAULTS["python"])

    lines: list[str] = [
        'version: "1.0"',
        "",
        "contexts:",
        "  default:",
        "    defaults:",
        f'      generate_output_path: "{paths["generate_output_path"]}"',
        f'      test_output_path: "{paths["test_output_path"]}"',
        f'      example_output_path: "{paths["example_output_path"]}"',
        f'      default_language: "{language}"',
    ]

    for key, value in STANDARD_DEFAULTS.items():
        # Format integers without trailing .0, floats with one decimal
        if isinstance(value, int):
            lines.append(f"      {key}: {value}")
        else:
            lines.append(f"      {key}: {value}")

    lines.append("")  # trailing newline
    return "\n".join(lines)


def offer_pddrc_init() -> bool:
    """Offer to create a ``.pddrc`` configuration file in the current directory.

    If a ``.pddrc`` already exists the user is informed and the function
    returns ``False``.  Otherwise a preview of sensible defaults is shown
    and the user is prompted to confirm creation.

    Returns
    -------
    bool
        ``True`` if the file was created, ``False`` otherwise.
    """
    cwd = Path.cwd()
    pddrc_path = cwd / PDDRC_FILENAME

    # ── Already exists ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
    if pddrc_path.exists():
        console.print(
            f"[info]A {PDDRC_FILENAME} file already exists in {cwd}.[/info]"
        )
        return False

    # ── Detect / prompt language ━━━━━━━━━━━━━━━━━━━━━━━━━━━━
    language = _detect_language(cwd)
    if language is None:
        language = _prompt_language()
    else:
        console.print(f"\n[success]Detected project language: {language}[/success]")

    # ── Build & preview ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
    content = _build_pddrc_content(language)

    console.print(f"\n[info]Proposed {PDDRC_FILENAME} contents:[/info]\n")
    syntax = Syntax(content, "yaml", theme="monokai", line_numbers=False)
    console.print(syntax)

    # ── Prompt for confirmation (Enter = yes) ━━━━━━━━━━━━━━━━━━━━━
    answer = console.input(f"\nCreate {PDDRC_FILENAME}? [Y/n] ").strip().lower()
    if answer in ("", "y", "yes"):
        try:
            pddrc_path.write_text(content, encoding="utf-8")
            console.print(
                f"[success]Created {PDDRC_FILENAME} in {cwd}[/success]"
            )
            return True
        except OSError as exc:
            console.print(
                f"[error]Failed to write {PDDRC_FILENAME}: {exc}[/error]"
            )
            return False
    else:
        console.print("[info]Skipped .pddrc creation.[/info]")
        return False