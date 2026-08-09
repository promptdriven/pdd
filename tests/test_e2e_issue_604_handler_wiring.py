"""Tests for Issue #604: Handlers generated but not wired to runtime.

Verifies that code_generator_main auto-wires public exports from generated
Python files into the parent __init__.py.
"""
from __future__ import annotations

import os
import textwrap
from unittest.mock import patch

from pdd.code_generator_main import (
    _detect_wireable_exports,
    _should_wire_generated_exports,
    _wire_to_parent_init,
)


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
        assert not _detect_wireable_exports(code, "template.prompt")
        assert not _detect_wireable_exports(code, "config.json")


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

    def test_wiring_disabled_by_default(self, tmp_path):
        """Default generation must not mutate sibling __init__.py files."""
        pkg_dir = tmp_path / "mypackage"
        pkg_dir.mkdir()
        init_file = pkg_dir / "__init__.py"
        init_file.write_text("# init\n")
        module_file = pkg_dir / "handlers.py"
        module_file.write_text("def handle(): pass\n")

        with patch.dict(os.environ, {}, clear=True):
            if _should_wire_generated_exports(str(module_file)):
                _wire_to_parent_init(str(module_file), ["handle"])

        content = init_file.read_text()
        assert "from .handlers import" not in content

    def test_wiring_enabled_by_explicit_env_flag(self, tmp_path):
        """PDD_ENABLE_WIRING=1 opts into parent package wiring."""
        pkg_dir = tmp_path / "mypackage"
        pkg_dir.mkdir()
        init_file = pkg_dir / "__init__.py"
        init_file.write_text("# init\n")
        module_file = pkg_dir / "handlers.py"
        module_file.write_text("def handle(): pass\n")

        with patch.dict(os.environ, {"PDD_ENABLE_WIRING": "1"}, clear=True):
            if _should_wire_generated_exports(str(module_file)):
                _wire_to_parent_init(str(module_file), ["handle"])

        content = init_file.read_text()
        assert "from .handlers import handle" in content

    def test_skip_wiring_overrides_explicit_enable(self, tmp_path):
        """PDD_SKIP_WIRING remains a backward-compatible opt-out."""
        module_file = tmp_path / "handlers.py"

        with patch.dict(
            os.environ,
            {"PDD_ENABLE_WIRING": "1", "PDD_SKIP_WIRING": "1"},
            clear=True,
        ):
            assert _should_wire_generated_exports(str(module_file)) is False

    def test_wiring_opt_in_still_skips_non_python_outputs(self, tmp_path):
        """Explicit wiring only applies to Python module outputs."""
        output_file = tmp_path / "handlers.ts"

        with patch.dict(os.environ, {"PDD_ENABLE_WIRING": "1"}, clear=True):
            assert _should_wire_generated_exports(str(output_file)) is False

    def test_key_validator_regression_does_not_wire_parent_init_by_default(self, tmp_path):
        """Regression: generated service modules should not re-export themselves by default."""
        services_dir = tmp_path / "src" / "services"
        services_dir.mkdir(parents=True)
        init_file = services_dir / "__init__.py"
        init_file.write_text(
            textwrap.dedent("""\
                # Business logic services
                from src.services import secrets_dispatch
                from src.workers import pdd_executor

                __all__ = [
                    "pdd_executor",
                    "secrets_dispatch",
                ]
            """)
        )
        module_file = services_dir / "key_validator.py"
        module_file.write_text(
            textwrap.dedent("""\
                class KeyValidationResult:
                    pass

                def validate_user_keys():
                    pass
            """)
        )
        exports = _detect_wireable_exports(module_file.read_text(), str(module_file))

        with patch.dict(os.environ, {}, clear=True):
            if _should_wire_generated_exports(str(module_file)):
                _wire_to_parent_init(str(module_file), exports)

        content = init_file.read_text()
        assert "from .key_validator import" not in content
