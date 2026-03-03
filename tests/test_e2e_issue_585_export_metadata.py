"""Tests for Issue #585: Function calls generated without checking actual exports.

Verifies that auto_include enriches dependency summaries with actual export names
extracted via AST parsing, so the LLM can reference real function/class names.
"""
from __future__ import annotations

import os
import tempfile
import textwrap

import pytest

from pdd.auto_include import _extract_exports, _get_available_includes_from_csv


class TestExtractExportsFromPythonFile:
    """Tests for _extract_exports()."""

    def test_extract_exports_from_python_file(self, tmp_path):
        """Should return public function and class names from a Python file."""
        py_file = tmp_path / "module.py"
        py_file.write_text(textwrap.dedent("""\
            from __future__ import annotations

            MAX_RETRIES = 3

            class UserService:
                pass

            def fetch_with_auth(url: str) -> dict:
                pass

            async def send_notification(msg: str) -> None:
                pass
        """))
        exports = _extract_exports(str(py_file))
        assert "MAX_RETRIES" in exports
        assert "UserService" in exports
        assert "fetch_with_auth" in exports
        assert "send_notification" in exports

    def test_extract_exports_skips_private_names(self, tmp_path):
        """Names starting with _ should be excluded."""
        py_file = tmp_path / "internal.py"
        py_file.write_text(textwrap.dedent("""\
            def _private_helper():
                pass

            class _InternalCache:
                pass

            def public_api():
                pass
        """))
        exports = _extract_exports(str(py_file))
        assert "_private_helper" not in exports
        assert "_InternalCache" not in exports
        assert "public_api" in exports

    def test_extract_exports_handles_missing_file(self):
        """Should return empty list for non-existent files."""
        exports = _extract_exports("/no/such/file.py")
        assert exports == []

    def test_extract_exports_handles_non_python_files(self, tmp_path):
        """Should return empty list for .prompt/.json files."""
        prompt_file = tmp_path / "some.prompt"
        prompt_file.write_text("% This is a prompt")
        assert _extract_exports(str(prompt_file)) == []

        json_file = tmp_path / "config.json"
        json_file.write_text('{"key": "val"}')
        assert _extract_exports(str(json_file)) == []


class TestGetAvailableIncludesIncludesExports:
    """Tests for enriched _get_available_includes_from_csv() output."""

    def test_get_available_includes_includes_export_metadata(self, tmp_path):
        """CSV formatting should include 'Exports:' when Python file has exports."""
        py_file = tmp_path / "utils.py"
        py_file.write_text(textwrap.dedent("""\
            def helper_one():
                pass

            class HelperTwo:
                pass
        """))
        csv_output = f"full_path,file_summary,date\n{py_file},\"Utility functions\",2024-01-01"
        results = _get_available_includes_from_csv(csv_output)
        assert len(results) == 1
        assert "Exports:" in results[0]
        assert "helper_one" in results[0]
        assert "HelperTwo" in results[0]

    def test_get_available_includes_omits_exports_for_non_python(self, tmp_path):
        """No 'Exports:' line for non-Python files."""
        prompt_file = tmp_path / "template.prompt"
        prompt_file.write_text("% some prompt")
        csv_output = f"full_path,file_summary,date\n{prompt_file},\"A prompt template\",2024-01-01"
        results = _get_available_includes_from_csv(csv_output)
        assert len(results) == 1
        assert "Exports:" not in results[0]
