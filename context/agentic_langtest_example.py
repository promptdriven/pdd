"""Runnable example of the conservative language verification fallback."""

from __future__ import annotations

import csv
import os
import shlex
import tempfile
from pathlib import Path

from rich import print as rprint
from rich.panel import Panel


def _load_language_format_by_name() -> dict:
    """Load language_format.csv into a dict keyed by lowercase language name."""
    csv_path = Path(__file__).parents[1] / "pdd" / "data" / "language_format.csv"
    if not csv_path.exists():
        return {}
    result = {}
    try:
        with open(csv_path, "r", encoding="utf-8", newline="") as file_handle:
            reader = csv.DictReader(file_handle)
            for row in reader:
                lang_name = row.get("language", "").strip().lower()
                if lang_name:
                    result[lang_name] = row
    except (OSError, UnicodeError, csv.Error):
        return {}
    return result


def default_verify_cmd_for(lang: str, unit_test_file: str) -> str | None:
    """Return a configured command, a Python fallback, or ``None``."""
    lang = lang.lower()
    lang_formats = _load_language_format_by_name()
    if lang in lang_formats:
        csv_cmd = lang_formats[lang].get("run_test_command", "").strip()
        if csv_cmd:
            return csv_cmd.replace("{file}", shlex.quote(unit_test_file))
    if lang == "python":
        return f"{os.sys.executable} -m pytest {shlex.quote(unit_test_file)} -q"
    return None


def missing_tool_hints(
    lang: str, verify_cmd: str | None, project_root: Path
) -> str | None:
    """Preserve the compatibility API without probing or installing tools."""
    _ = lang, verify_cmd, project_root
    hint: str | None = None
    return hint


def main() -> None:
    """Display CSV and Python-fallback results without executing them."""
    with tempfile.TemporaryDirectory() as tmpdir:
        root = Path(tmpdir)
        paths = {
            "python": root / "quoted $(literal); test.py",
            "javascript": root / "quoted $(literal); test.js",
            "java": root / "Quoted Test.java",
        }
        for language, test_file in paths.items():
            command = default_verify_cmd_for(language, str(test_file))
            rprint(
                Panel(
                    str(command),
                    title=f"[green]{language}[/green]",
                    border_style="green" if command else "yellow",
                )
            )


if __name__ == "__main__":
    main()
