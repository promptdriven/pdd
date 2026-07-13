# pdd/agentic_langtest.py
"""
Language-specific test command utilities.

This module resolves configured language test commands, with a Python fallback.
"""
from __future__ import annotations

import csv
import os
import shlex
from pathlib import Path


def _load_language_format_by_name() -> dict:
    """Load language_format.csv into a dict keyed by lowercase language name."""
    csv_path = Path(__file__).parent / "data" / "language_format.csv"
    if not csv_path.exists():
        return {}
    result = {}
    try:
        with open(csv_path, 'r', encoding='utf-8', newline='') as file_handle:
            reader = csv.DictReader(file_handle)
            for row in reader:
                lang_name = row.get('language', '').strip().lower()
                if lang_name:
                    result[lang_name] = row
    except (OSError, UnicodeError, csv.Error):
        return {}
    return result


def default_verify_cmd_for(lang: str, unit_test_file: str) -> str | None:
    """
    Return a test command for the given language and test file.

    Resolution order:
    1. CSV run_test_command lookup by language name
    2. Hardcoded Python fallback (for robustness if CSV is missing)
    3. Return None (triggers agentic fallback)

    Users can override this behavior with PDD_AGENTIC_VERIFY_CMD environment variable.

    Args:
        lang: The programming language (e.g., "python", "javascript", "java").
        unit_test_file: Path to the unit test file.

    Returns:
        Test command string, or None for languages without a known test command.
    """
    lang = lang.lower()

    # 1. CSV lookup by language name
    lang_formats = _load_language_format_by_name()
    if lang in lang_formats:
        csv_cmd = lang_formats[lang].get('run_test_command', '').strip()
        if csv_cmd:
            return csv_cmd.replace('{file}', shlex.quote(unit_test_file))

    # 2. Hardcoded Python fallback
    if lang == "python":
        return f'{os.sys.executable} -m pytest {shlex.quote(unit_test_file)} -q'

    # 3. No command available — triggers agentic fallback
    return None


def missing_tool_hints(lang: str, verify_cmd: str | None, project_root: Path) -> str | None:
    """Return no hint while preserving the compatibility API.

    Args:
        lang: The programming language.
        verify_cmd: The verification command (if any).
        project_root: Path to the project root.

    Returns:
        Always None.
    """
    _ = lang, verify_cmd, project_root
    hint: str | None = None
    return hint
