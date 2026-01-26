# pdd/agentic_langtest.py
"""
Language-specific test command utilities.

This module provides the default_verify_cmd_for function which returns
test commands for different languages. Non-Python languages now use
agentic mode for test discovery and execution.
"""
from __future__ import annotations

import os
from pathlib import Path


def default_verify_cmd_for(lang: str, unit_test_file: str) -> str | None:
    """
    Return a test command for the given language and test file.

    For Python, returns a pytest command. For all other languages, returns None
    to signal that agentic mode should handle test discovery and execution.
    The agent can explore the project structure and determine the appropriate
    test runner (Jest, JUnit, Go test, Cargo test, etc.) dynamically.

    Users can override this behavior with PDD_AGENTIC_VERIFY_CMD environment variable.

    Args:
        lang: The programming language (e.g., "python", "javascript", "java").
        unit_test_file: Path to the unit test file.

    Returns:
        Test command for Python, None for other languages (triggers agentic fallback).
    """
    lang = lang.lower()

    if lang == "python":
        return f'{os.sys.executable} -m pytest "{unit_test_file}" -q'

    # Non-Python languages: return None to indicate agentic mode should handle it.
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
