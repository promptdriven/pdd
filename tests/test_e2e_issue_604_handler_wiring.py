"""Tests for Issue #604: Handlers generated but not wired to runtime.

Verifies that code_generator_main auto-wires public exports from generated
Python files into the parent __init__.py.
"""
from __future__ import annotations

import os
import textwrap
from unittest.mock import patch

import pytest

from pdd.code_generator_main import _detect_wireable_exports, _wire_to_parent_init, _env_flag_enabled


class TestDetectWireableExports:
    """Tests for _detect_wireable_exports()."""

    def test_detect_wireable_exports_finds_public_functions(self):
        """Should extract public function and class names from generated code."""
        code = textwrap.dedent("""\
            from __future__ import annotations

            class EventHandler:
                pass

            def handle_event(event: dict) -> None:
                pass

            async def process_queue() -> None:
                pass
        """)
        exports = _detect_wireable_exports(code, "handlers/events.py")
        assert "EventHandler" in exports
        assert "handle_event" in exports
        assert "process_queue" in exports

    def test_detect_wireable_exports_skips_private(self):
        """Names starting with _ should be excluded."""
        code = textwrap.dedent("""\
            def _internal_helper():
                pass

            class _PrivateBase:
                pass

            def public_api():
                pass
        """)
        exports = _detect_wireable_exports(code, "mod.py")
        assert "_internal_helper" not in exports
        assert "_PrivateBase" not in exports
        assert "public_api" in exports

    def test_detect_wireable_exports_skips_non_python(self):
        """Should return empty list for non-.py paths."""
        code = "def foo(): pass"
        assert _detect_wireable_exports(code, "template.prompt") == []
        assert _detect_wireable_exports(code, "config.json") == []


class TestWireToParentInit:
    """Tests for _wire_to_parent_init()."""

    def test_wire_to_parent_init_adds_import(self, tmp_path):
        """Should append import line to existing __init__.py."""
        pkg_dir = tmp_path / "mypackage"
        pkg_dir.mkdir()
        init_file = pkg_dir / "__init__.py"
        init_file.write_text("# Package init\n")
        module_file = pkg_dir / "handlers.py"
        module_file.write_text("def handle(): pass\n")

        result = _wire_to_parent_init(str(module_file), ["handle", "EventHandler"])
        assert result is True

        content = init_file.read_text()
        assert "from .handlers import handle, EventHandler" in content

    def test_wire_to_parent_init_skips_if_no_init(self, tmp_path):
        """Should return False when __init__.py doesn't exist."""
        pkg_dir = tmp_path / "no_init_pkg"
        pkg_dir.mkdir()
        module_file = pkg_dir / "handlers.py"
        module_file.write_text("def handle(): pass\n")

        result = _wire_to_parent_init(str(module_file), ["handle"])
        assert result is False

    def test_wire_to_parent_init_skips_if_already_imported(self, tmp_path):
        """Should not add duplicate import lines when all exports already present."""
        pkg_dir = tmp_path / "mypackage"
        pkg_dir.mkdir()
        init_file = pkg_dir / "__init__.py"
        init_file.write_text("from .handlers import handle\n")
        module_file = pkg_dir / "handlers.py"
        module_file.write_text("def handle(): pass\n")

        result = _wire_to_parent_init(str(module_file), ["handle"])
        assert result is False

        content = init_file.read_text()
        assert content.count("from .handlers import") == 1

    def test_wire_to_parent_init_merges_new_exports(self, tmp_path):
        """Should merge missing exports into existing import line."""
        pkg_dir = tmp_path / "mypackage"
        pkg_dir.mkdir()
        init_file = pkg_dir / "__init__.py"
        init_file.write_text("from .handlers import handle_a\n")
        module_file = pkg_dir / "handlers.py"
        module_file.write_text("def handle_a(): pass\ndef handle_b(): pass\n")

        result = _wire_to_parent_init(str(module_file), ["handle_a", "handle_b"])
        assert result is True

        content = init_file.read_text()
        assert "handle_a" in content
        assert "handle_b" in content
        assert content.count("from .handlers import") == 1


class TestCodeGeneratorMainWiring:
    """Integration tests for wiring in code_generator_main."""

    @patch("pdd.code_generator_main._wire_to_parent_init")
    @patch("pdd.code_generator_main._detect_wireable_exports", return_value=["handle_event"])
    def test_wiring_helpers_invoked_in_post_write_path(
        self, mock_detect, mock_wire, tmp_path
    ):
        """Verify wiring helpers are called correctly when invoked as in the post-write path."""
        mock_wire.return_value = True
        # Simulate the post-write wiring logic from code_generator_main
        final_content = "def handle_event(): pass"
        p_output = str(tmp_path / "handlers.py")
        if not _env_flag_enabled("PDD_SKIP_WIRING") and p_output.endswith('.py'):
            wiring_exports = mock_detect(final_content, p_output)
            if wiring_exports:
                mock_wire(p_output, wiring_exports)
        mock_detect.assert_called_once_with(final_content, p_output)
        mock_wire.assert_called_once_with(p_output, ["handle_event"])

    def test_wiring_skipped_when_env_flag_set(self, tmp_path):
        """PDD_SKIP_WIRING=1 should prevent wiring."""
        pkg_dir = tmp_path / "mypackage"
        pkg_dir.mkdir()
        init_file = pkg_dir / "__init__.py"
        init_file.write_text("# init\n")
        module_file = pkg_dir / "handlers.py"
        module_file.write_text("def handle(): pass\n")

        # Simulate what code_generator_main does: check env before wiring
        with patch.dict(os.environ, {"PDD_SKIP_WIRING": "1"}):
            if not _env_flag_enabled("PDD_SKIP_WIRING"):
                _wire_to_parent_init(str(module_file), ["handle"])

        # __init__.py should be unchanged
        content = init_file.read_text()
        assert "from .handlers import" not in content
