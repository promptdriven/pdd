# pdd/get_test_command.py
"""Get language-appropriate test commands.

This module provides functions to resolve the appropriate test command
for a given test file based on:
1. CSV run_test_command (if non-empty)
2. Smart detection via default_verify_cmd_for()
3. None (triggers agentic fallback)
"""
from pathlib import Path
from typing import Optional
import csv

from .agentic_langtest import default_verify_cmd_for
from .get_language import get_language


def _load_language_format() -> dict:
    """Load language_format.csv into a dict keyed by extension."""
    csv_path = Path(__file__).parent.parent / "data" / "language_format.csv"
    result = {}
    with open(csv_path, 'r') as f:
        reader = csv.DictReader(f)
        for row in reader:
            ext = row.get('extension', '')
            if ext:
                result[ext] = row
    return result


def get_test_command_for_file(test_file: str, language: Optional[str] = None) -> Optional[str]:
    """
    Get the appropriate test command for a test file.

    Resolution order:
    1. CSV run_test_command (if non-empty)
    2. Smart detection via default_verify_cmd_for()
    3. None (triggers agentic fallback)

    Args:
        test_file: Path to the test file
        language: Optional language override

    Returns:
        Test command string with {file} placeholder replaced, or None
    """
    test_path = Path(test_file)
    ext = test_path.suffix

    resolved_language = language
    if resolved_language is None:
        resolved_language = get_language(ext)

    # 1. Check CSV for run_test_command
    lang_formats = _load_language_format()
    if ext in lang_formats:
        csv_cmd = lang_formats[ext].get('run_test_command', '').strip()
        if csv_cmd:
            return csv_cmd.replace('{file}', str(test_file))

    # 2. Smart detection
    if resolved_language:
        smart_cmd = default_verify_cmd_for(resolved_language.lower(), str(test_file))
        if smart_cmd:
            return smart_cmd

    # 3. No command available
    return None
