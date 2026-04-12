"""Tests for pdd.path_resolution — focused on find_project_root_from_path.

These tests verify that the function correctly finds project roots from
both directory and file starting points, and returns None when no markers
exist.
"""

import os
from pathlib import Path

import pytest

from pdd.path_resolution import find_project_root_from_path, _has_project_marker


class TestFindProjectRootFromPath:
    """find_project_root_from_path should walk up from the start path
    looking for project markers."""

    def test_finds_root_from_directory(self, tmp_path):
        """Starting from a subdirectory that has a marker in a parent."""
        (tmp_path / ".git").mkdir()
        subdir = tmp_path / "src" / "pkg"
        subdir.mkdir(parents=True)

        result = find_project_root_from_path(str(subdir))
        assert result == str(tmp_path.resolve())

    def test_finds_root_from_file_path(self, tmp_path):
        """Starting from a file path — should use the file's parent directory
        and walk up from there.  This is the path used by
        include_query_extractor._project_relative_path."""
        (tmp_path / ".pddrc").touch()
        subdir = tmp_path / "pdd"
        subdir.mkdir()
        file_path = subdir / "utils.py"
        file_path.write_text("x = 1")

        result = find_project_root_from_path(str(file_path))
        assert result == str(tmp_path.resolve())

    def test_file_in_root_dir_finds_root(self, tmp_path):
        """A file sitting directly in the project root should find
        the root (its own parent directory)."""
        (tmp_path / "pyproject.toml").touch()
        file_path = tmp_path / "main.py"
        file_path.write_text("print('hi')")

        result = find_project_root_from_path(str(file_path))
        assert result == str(tmp_path.resolve())

    def test_nonexistent_file_path_still_resolves(self, tmp_path):
        """A path to a file that doesn't exist should still walk up
        from its would-be parent directory."""
        (tmp_path / ".git").mkdir()
        subdir = tmp_path / "src"
        subdir.mkdir()

        result = find_project_root_from_path(str(subdir / "nonexistent.py"))
        assert result == str(tmp_path.resolve())

    def test_returns_none_without_markers(self, tmp_path):
        """No markers anywhere in the tree → returns None."""
        deep = tmp_path / "a" / "b" / "c"
        deep.mkdir(parents=True)

        result = find_project_root_from_path(str(deep))
        assert result is None

    def test_respects_max_levels(self, tmp_path):
        """Should stop walking after max_levels parents."""
        (tmp_path / ".git").mkdir()
        # Create a deep directory 5 levels down
        deep = tmp_path / "a" / "b" / "c" / "d" / "e"
        deep.mkdir(parents=True)

        # With max_levels=3, it shouldn't reach tmp_path (5 levels up)
        result = find_project_root_from_path(str(deep), max_levels=3)
        assert result is None

        # With max_levels=6, it should find it
        result = find_project_root_from_path(str(deep), max_levels=6)
        assert result == str(tmp_path.resolve())

    def test_each_marker_type_is_recognized(self, tmp_path):
        """Each individual marker should be sufficient to identify a root."""
        markers = [
            (".git", "dir"),
            (".pddrc", "file"),
            ("pyproject.toml", "file"),
            ("data", "dir"),
            (".env", "file"),
        ]
        for marker, kind in markers:
            root = tmp_path / f"project_{marker.replace('.', '_')}"
            root.mkdir()
            if kind == "dir":
                (root / marker).mkdir()
            else:
                (root / marker).touch()
            subdir = root / "src"
            subdir.mkdir()

            result = find_project_root_from_path(str(subdir))
            assert result == str(root.resolve()), (
                f"Marker '{marker}' not recognized as project root indicator"
            )

    def test_file_path_vs_directory_path_same_result(self, tmp_path):
        """Passing a file vs its containing directory should find the
        same project root."""
        (tmp_path / ".git").mkdir()
        subdir = tmp_path / "lib"
        subdir.mkdir()
        file_path = subdir / "mod.py"
        file_path.write_text("# module")

        from_dir = find_project_root_from_path(str(subdir))
        from_file = find_project_root_from_path(str(file_path))
        assert from_dir == from_file
