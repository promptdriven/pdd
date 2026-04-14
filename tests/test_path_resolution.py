"""Tests for pdd.path_resolution — focused on find_project_root_from_path.

These tests verify that the function correctly finds project roots from
both directory and file starting points, and returns None when no markers
exist.
"""

import os
from pathlib import Path

import pytest

from pdd.path_resolution import find_project_root_from_path


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


class TestNestedMarkerPriority:
    """Weak markers (.pddrc, pyproject.toml, data/, .env) can legitimately
    appear multiple times in one project (a monorepo with per-module
    .pddrc files, a top-level pyproject.toml plus nested data/ dirs, etc.).
    .git is a stronger signal of the true project/repo boundary and should
    win over any nested weak marker. When there's no .git, the walk should
    land on the outermost weak marker — otherwise the same file resolves
    to different roots depending on which directory the scan started from,
    which was exactly the bug raised in PR #763's review.
    """

    def test_git_outside_pddrc_wins_over_pddrc(self, tmp_path):
        """Layout from the PR review:
            repo/.git
            repo/module/.pddrc
            repo/module/context/a.py
        The file should resolve to repo/, not repo/module/, so the path
        stays stable whether we scan repo/module/context or repo/.
        """
        (tmp_path / ".git").mkdir()
        module = tmp_path / "module"
        module.mkdir()
        (module / ".pddrc").touch()
        context = module / "context"
        context.mkdir()
        file_path = context / "a.py"
        file_path.write_text("x = 1")

        from_file = find_project_root_from_path(str(file_path))
        from_ctx = find_project_root_from_path(str(context))
        from_repo = find_project_root_from_path(str(tmp_path))
        assert from_file == str(tmp_path.resolve())
        assert from_ctx == str(tmp_path.resolve())
        assert from_repo == str(tmp_path.resolve())

    def test_nested_pddrc_without_git_returns_outermost(self, tmp_path):
        """No .git anywhere. Outer .pddrc at repo/, inner .pddrc at
        repo/module/. Without a strong marker, the walk should return
        the outer (highest) one so nested scans agree on the root.
        """
        (tmp_path / ".pddrc").touch()
        module = tmp_path / "module"
        module.mkdir()
        (module / ".pddrc").touch()
        context = module / "context"
        context.mkdir()
        file_path = context / "a.py"
        file_path.write_text("x = 1")

        assert find_project_root_from_path(str(file_path)) == str(tmp_path.resolve())
        assert find_project_root_from_path(str(context)) == str(tmp_path.resolve())
        assert find_project_root_from_path(str(module)) == str(tmp_path.resolve())

    def test_git_below_outer_pddrc_still_wins(self, tmp_path):
        """Layout:
            outer/.pddrc
            outer/repo/.git
            outer/repo/src/a.py
        .git is strong, so it should win even though outer/ has a weak
        marker sitting higher in the tree. This keeps git submodule /
        vendored-repo layouts resolving to the inner repo, which is
        almost always what the user wants.
        """
        (tmp_path / ".pddrc").touch()
        repo = tmp_path / "repo"
        repo.mkdir()
        (repo / ".git").mkdir()
        src = repo / "src"
        src.mkdir()
        file_path = src / "a.py"
        file_path.write_text("x = 1")

        assert find_project_root_from_path(str(file_path)) == str(repo.resolve())

    def test_mixed_weak_markers_highest_wins(self, tmp_path):
        """Different weak markers stacked at different levels: highest
        (outermost) should win regardless of marker type.
        """
        (tmp_path / "pyproject.toml").touch()
        mid = tmp_path / "mid"
        mid.mkdir()
        (mid / ".pddrc").touch()
        inner = mid / "inner"
        inner.mkdir()
        (inner / ".env").touch()
        leaf = inner / "leaf.py"
        leaf.write_text("# leaf")

        assert find_project_root_from_path(str(leaf)) == str(tmp_path.resolve())

    def test_max_levels_limits_walk_even_with_weak_markers(self, tmp_path):
        """When the outermost weak marker is beyond max_levels, the walk
        should return the highest weak marker it actually reached, not
        None. This documents behavior for very deep trees.
        """
        (tmp_path / "pyproject.toml").touch()
        mid = tmp_path / "a" / "b"
        mid.mkdir(parents=True)
        (mid / ".pddrc").touch()
        deep = mid / "c" / "d" / "e"
        deep.mkdir(parents=True)

        # max_levels=4 from `deep` checks deep, d, c, b — stops before tmp_path.
        # Highest weak marker seen is mid (b).
        result = find_project_root_from_path(str(deep), max_levels=4)
        assert result == str(mid.resolve())

        # max_levels=3 can't reach b → returns None despite the outer
        # pyproject.toml existing higher up.
        result_shallow = find_project_root_from_path(str(deep), max_levels=3)
        assert result_shallow is None

    def test_still_returns_none_when_no_markers_at_all(self, tmp_path):
        """With no strong or weak markers the function must still return
        None so the absolute-path fallback in summarize_directory kicks in.
        """
        deep = tmp_path / "a" / "b" / "c"
        deep.mkdir(parents=True)
        assert find_project_root_from_path(str(deep)) is None


class TestPathResolverProjectRootMarkerPriority:
    """PathResolver.resolve_project_root should use the same .git-wins /
    outermost-weak-marker rule as find_project_root_from_path, so every
    project-root consumer in the codebase (CSV keying, llm_invoke's
    model CSV lookup, firecrawl_cache's DB location) agrees on one root.
    Previously this method used nearest-wins, so in a monorepo with a
    nested .pddrc the CWD-anchored consumers could land on a sub-module
    while CSV keying landed on the .git repo.
    """

    def _make_resolver(self, cwd, package_root=None, repo_root=None):
        from pdd.path_resolution import PathResolver

        return PathResolver(
            cwd=Path(cwd).resolve(),
            pdd_path_env=None,
            package_root=Path(package_root or cwd).resolve(),
            repo_root=Path(repo_root).resolve() if repo_root else None,
        )

    def test_git_wins_over_nested_pddrc(self, tmp_path):
        """repo/.git, repo/module/.pddrc; CWD=repo/module — should return
        repo (the .git ancestor), not repo/module (the nearest weak marker).
        """
        (tmp_path / ".git").mkdir()
        module = tmp_path / "module"
        module.mkdir()
        (module / ".pddrc").touch()

        resolver = self._make_resolver(cwd=module)
        assert resolver.resolve_project_root() == tmp_path.resolve()

    def test_outermost_weak_wins_without_git(self, tmp_path):
        """Nested .pddrc at repo/ and repo/module/, no .git; CWD=repo/module
        — outer .pddrc should win so CWD-anchored lookups land on the same
        root as scans started from deeper in the tree.
        """
        (tmp_path / ".pddrc").touch()
        module = tmp_path / "module"
        module.mkdir()
        (module / ".pddrc").touch()

        resolver = self._make_resolver(cwd=module)
        assert resolver.resolve_project_root() == tmp_path.resolve()

    def test_no_marker_falls_back_to_cwd(self, tmp_path):
        """Unchanged behavior: if no marker is found within max_levels,
        return cwd. This keeps firecrawl_cache and llm_invoke working in
        scratch directories without crashing.
        """
        deep = tmp_path / "a" / "b"
        deep.mkdir(parents=True)

        resolver = self._make_resolver(cwd=deep)
        assert resolver.resolve_project_root() == deep.resolve()
