# pdd/agentic_langtest.py
"""
Language-specific test command utilities.

This module provides the default_verify_cmd_for function which returns
test commands for different languages. It first checks the language_format.csv
for a run_test_command, then falls back to a hardcoded Python command,
and finally returns None to trigger agentic mode.
"""
from __future__ import annotations

import csv
import os
from pathlib import Path


def _load_language_format_by_name() -> dict:
    """Load language_format.csv into a dict keyed by lowercase language name."""
    csv_path = Path(__file__).parent / "data" / "language_format.csv"
    if not csv_path.exists():
        return {}
    result = {}
    with open(csv_path, 'r') as f:
        reader = csv.DictReader(f)
        for row in reader:
            lang_name = row.get('language', '').strip().lower()
            if lang_name:
                result[lang_name] = row
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
            return csv_cmd.replace('{file}', unit_test_file)

    # 2. Hardcoded Python fallback
    if lang == "python":
        return f'{os.sys.executable} -m pytest "{unit_test_file}" -q'

    # 3. No command available — triggers agentic fallback
    return None


def missing_tool_hints(lang: str, verify_cmd: str | None, project_root: Path) -> str | None:
    """
    Return guidance if required tools are missing.

    This function is kept for compatibility but currently returns None for all
    cases since non-Python languages are handled by agentic mode which can
    install dependencies dynamically.

    Args:
        lang: The programming language.
        verify_cmd: The verification command (if any).
        project_root: Path to the project root.

    Returns:
        None (agentic mode handles missing tools).
    """
    # Agentic mode handles tool installation for non-Python
    return None
