"""Unit tests for pdd/split_validation.py's test_seam_resolution check.

This is the v2.1 safety net: statically verify that every string passed
to `patch("module.Symbol")` resolves to a defined or re-exported symbol
after an extraction. The oracle run on pdd_executor showed 17 tests
failing due to one missing re-export that this detector now catches.
"""
from __future__ import annotations

from pathlib import Path
from types import SimpleNamespace

import pytest

from pdd.split_validation import (
    _collect_patch_paths,
    _resolve_patch_path,
    _STDLIB_MODULES_COMMON,
    validate_extraction,
)


# ---------------------------------------------------------------------------
# _collect_patch_paths
# ---------------------------------------------------------------------------


class TestCollectPatchPaths:
    """Parses patch()/jest.mock()/mocker.patch() string args."""

    def test_simple_patch_call(self):
        content = '''
with patch("mymodule.MyClass") as mock_cls:
    pass
'''
        assert _collect_patch_paths(content) == ["mymodule.MyClass"]

    def test_patch_object_call(self):
        content = '''
with patch.object(mymodule, "my_func") as mock_fn:
    pass
'''
        # patch.object with attr name is NOT a dotted patch path
        # — we only collect the first string arg when it's dotted.
        # Here the first arg is `mymodule` (the module, not a string),
        # and "my_func" is just an attr name.
        # Our regex matches the first-string form only, which should miss this.
        # (Acceptable — we're not trying to cover every pattern.)
        result = _collect_patch_paths(content)
        # No dotted string, so empty
        assert result == []

    def test_multiple_patches_in_one_file(self):
        content = '''
with patch("mod_a.SymA"), patch("mod_b.SymB"):
    mocker.patch("mod_c.SymC")
    jest.mock('node_mod/file')
    jest.doMock("other/file")
'''
        paths = _collect_patch_paths(content)
        assert "mod_a.SymA" in paths
        assert "mod_b.SymB" in paths
        assert "mod_c.SymC" in paths
        # jest.mock paths don't contain dots → filtered out (we only
        # keep dotted paths that look like symbol references)
        # 'node_mod/file' has no dot → filtered

    def test_deduplicates_repeated_paths(self):
        content = '''
patch("mod.X")
patch("mod.X")
patch("mod.X")
'''
        assert _collect_patch_paths(content) == ["mod.X"]

    def test_skips_non_dotted_strings(self):
        content = 'patch("nodot")'
        assert _collect_patch_paths(content) == []

    def test_skips_leading_trailing_dots(self):
        # Paths that start/end with a dot are malformed
        content = 'patch(".leading") ; patch("trailing.")'
        assert _collect_patch_paths(content) == []

    def test_handles_single_and_double_quotes(self):
        content = '''
patch('single.Quote')
patch("double.Quote")
'''
        paths = _collect_patch_paths(content)
        assert "single.Quote" in paths
        assert "double.Quote" in paths


# ---------------------------------------------------------------------------
# _resolve_patch_path — basic
# ---------------------------------------------------------------------------


class TestResolvePatchPath:
    """Static resolution of dotted patch paths against a worktree."""

    def test_single_dot_path_skipped(self):
        # Paths with no dot are returned as resolved (not a module path)
        ok, reason = _resolve_patch_path("just_a_name", Path("/tmp"))
        assert ok is True

    def test_simple_path_with_definition(self, tmp_path):
        # Layout: pkg/mymod.py with `def my_func(): ...`
        pkg = tmp_path / "pkg"
        pkg.mkdir()
        (pkg / "mymod.py").write_text("def my_func():\n    return 1\n")
        ok, reason = _resolve_patch_path("pkg.mymod.my_func", tmp_path)
        assert ok is True, f"expected resolved, got: {reason}"

    def test_class_definition_resolves(self, tmp_path):
        (tmp_path / "m.py").write_text("class MyClass:\n    pass\n")
        ok, _ = _resolve_patch_path("m.MyClass", tmp_path)
        assert ok is True

    def test_module_constant_resolves(self, tmp_path):
        (tmp_path / "m.py").write_text("MY_CONSTANT = 42\n")
        ok, _ = _resolve_patch_path("m.MY_CONSTANT", tmp_path)
        assert ok is True

    def test_typed_constant_resolves(self, tmp_path):
        (tmp_path / "m.py").write_text("MY_CONST: int = 42\n")
        ok, _ = _resolve_patch_path("m.MY_CONST", tmp_path)
        assert ok is True

    def test_missing_symbol_is_unresolved(self, tmp_path):
        (tmp_path / "m.py").write_text("def other(): pass\n")
        ok, reason = _resolve_patch_path("m.missing", tmp_path)
        assert ok is False
        assert "missing" in reason

    def test_missing_module_is_unresolved(self, tmp_path):
        ok, reason = _resolve_patch_path("nonexistent.foo", tmp_path)
        assert ok is False
        assert "module file not found" in reason


# ---------------------------------------------------------------------------
# Multi-line import support
# ---------------------------------------------------------------------------


class TestMultilineImports:
    """Re-exports via parenthesized multi-line `from X import (..., Y, ...)`."""

    def test_multiline_reexport_resolves(self, tmp_path):
        # Package __init__.py re-exports HEARTBEAT via multi-line import
        pkg = tmp_path / "mypkg"
        pkg.mkdir()
        (pkg / "__init__.py").write_text('''
from .sub import (
    BILLABLE_API_KEYS,
    HEARTBEAT,
    STOP_SIGNAL,
)
''')
        (pkg / "sub.py").write_text("HEARTBEAT = 100\n")
        ok, _ = _resolve_patch_path("mypkg.HEARTBEAT", tmp_path)
        assert ok is True, "multi-line parenthesized import should resolve"

    def test_multiline_with_blank_lines(self, tmp_path):
        pkg = tmp_path / "mypkg"
        pkg.mkdir()
        (pkg / "__init__.py").write_text('''
from .sub import (

    FIRST_NAME,

    SECOND_NAME,

)
''')
        (pkg / "sub.py").write_text("FIRST_NAME = 1\nSECOND_NAME = 2\n")
        ok, _ = _resolve_patch_path("mypkg.SECOND_NAME", tmp_path)
        assert ok is True

    def test_single_line_import_still_works(self, tmp_path):
        pkg = tmp_path / "mypkg"
        pkg.mkdir()
        (pkg / "__init__.py").write_text("from .sub import X, Y\n")
        (pkg / "sub.py").write_text("X = 1\nY = 2\n")
        ok, _ = _resolve_patch_path("mypkg.X", tmp_path)
        assert ok is True


# ---------------------------------------------------------------------------
# Stdlib heuristic
# ---------------------------------------------------------------------------


class TestStdlibHeuristic:
    """Common-stdlib-attr patterns resolve optimistically."""

    def test_stdlib_attr_in_middle(self, tmp_path):
        # pattern: src.workers.pkg.os.getpgid — patches os.getpgid via target
        (tmp_path / "dummy.py").write_text("# placeholder\n")
        ok, reason = _resolve_patch_path(
            "src.workers.pkg.os.getpgid", tmp_path
        )
        assert ok is True
        assert "stdlib" in reason

    def test_stdlib_symbol_at_end(self, tmp_path):
        # pattern: src.workers.pkg.subprocess — patches the module attr
        ok, reason = _resolve_patch_path(
            "src.workers.pkg.subprocess", tmp_path
        )
        assert ok is True
        assert "stdlib" in reason

    def test_all_known_stdlibs_recognized(self):
        # Sanity check on the stdlib set — any test file will reference
        # some of these.
        assert "os" in _STDLIB_MODULES_COMMON
        assert "subprocess" in _STDLIB_MODULES_COMMON
        assert "asyncio" in _STDLIB_MODULES_COMMON
        assert "tempfile" in _STDLIB_MODULES_COMMON


# ---------------------------------------------------------------------------
# Star imports + dir-walk brute re-exports
# ---------------------------------------------------------------------------


class TestOptimisticReexports:
    """Star imports and dir-walk re-exports are accepted optimistically."""

    def test_star_import(self, tmp_path):
        pkg = tmp_path / "pkg"
        pkg.mkdir()
        (pkg / "__init__.py").write_text("from .sub import *\n")
        (pkg / "sub.py").write_text("MYSTERY_SYMBOL = 1\n")
        ok, reason = _resolve_patch_path("pkg.MYSTERY_SYMBOL", tmp_path)
        assert ok is True
        # Should be optimistic rather than strict
        assert "optimistic" in reason.lower() or reason == ""

    def test_dir_walk_reexport(self, tmp_path):
        """The `for _name in dir(_mod): globals()[_name] = getattr(_mod, _name)`
        brute-force re-export pattern used in the pdd_executor manual split."""
        pkg = tmp_path / "pkg"
        pkg.mkdir()
        (pkg / "__init__.py").write_text('''
from . import orchestrator as _orchestrator

for _name in dir(_orchestrator):
    if not _name.startswith("__") and _name not in globals():
        globals()[_name] = getattr(_orchestrator, _name)
''')
        (pkg / "orchestrator.py").write_text("SOME_SYMBOL = 1\n")
        ok, reason = _resolve_patch_path("pkg.SOME_SYMBOL", tmp_path)
        assert ok is True
        assert "optimistic" in reason.lower() or "re-export" in reason.lower()


# ---------------------------------------------------------------------------
# Integration: full validate_extraction with seam check
# ---------------------------------------------------------------------------


class TestValidateExtractionSeams:
    """End-to-end: validate_extraction flags real missing re-exports."""

    def _make_plan(self, children: list[dict]) -> SimpleNamespace:
        return SimpleNamespace(
            children=[SimpleNamespace(**c) for c in children]
        )

    def test_clean_split_no_seam_failures(self, tmp_path, monkeypatch):
        # Scenario: parent package with proper re-exports, test patches
        # resolve cleanly.
        monkeypatch.chdir(tmp_path)
        # Init git so validate_extraction's git sanity check passes
        import subprocess
        subprocess.run(["git", "init", "-q"], cwd=tmp_path, check=True)

        pkg = tmp_path / "pkg"
        pkg.mkdir()
        (pkg / "__init__.py").write_text("from .sub import MySym\n")
        (pkg / "sub.py").write_text("MySym = 42\n")
        tests = tmp_path / "tests"
        tests.mkdir()
        (tests / "test_pkg.py").write_text('''
from unittest.mock import patch
def test_foo():
    with patch("pkg.MySym", 99):
        pass
''')
        # Also create the test file co-located with the child so it's picked up
        child_test = pkg / "test_sub.py"
        child_test.write_text("")
        # example file (to satisfy that check)
        (tmp_path / "examples").mkdir()
        (tmp_path / "examples" / "sub_example.py").write_text("")

        plan = self._make_plan([
            {"name": "sub", "prompt_file": "pkg/sub.prompt",
             "code_file": "pkg/sub.py"},
        ])
        result = validate_extraction(plan, tmp_path)
        seam_fails = [
            f for f in result.failures if f.check == "test_seam_resolution"
        ]
        assert seam_fails == [], (
            f"expected 0 seam failures, got: {[f.message for f in seam_fails]}"
        )

    def test_missing_reexport_is_flagged(self, tmp_path):
        import subprocess
        subprocess.run(["git", "init", "-q"], cwd=tmp_path, check=True)

        pkg = tmp_path / "pkg"
        pkg.mkdir()
        # __init__.py does NOT re-export MissingSym
        (pkg / "__init__.py").write_text("from .sub import OtherSym\n")
        (pkg / "sub.py").write_text("OtherSym = 1\n")

        # Test patches a symbol that isn't re-exported
        tests = tmp_path / "tests"
        tests.mkdir()
        (tests / "test_pkg.py").write_text('''
from unittest.mock import patch
def test_foo():
    with patch("pkg.MissingSym", 99):
        pass
''')

        plan = self._make_plan([
            {"name": "sub", "prompt_file": "pkg/sub.prompt",
             "code_file": "pkg/sub.py"},
        ])
        result = validate_extraction(plan, tmp_path)
        seam_fails = [
            f for f in result.failures if f.check == "test_seam_resolution"
        ]
        assert len(seam_fails) >= 1
        assert any("MissingSym" in f.message for f in seam_fails)
        # Severity should be error so it blocks the improvement gate
        assert any(f.severity == "error" for f in seam_fails)
