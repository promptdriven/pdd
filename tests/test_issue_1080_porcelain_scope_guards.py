"""Failing tests for issue #1080 — porcelain-rename handling in scope guards.

Bug summary
-----------
Several scope-guard / change-detection helpers consume text-mode
``git status --porcelain`` output with naive ``line[3:]`` slicing and
ad-hoc ``" -> "`` splitting. For staged renames this either:

* constructs a fake combined ``"old -> new"`` path (so
  ``git checkout HEAD -- <fake>`` fails and an out-of-scope rename
  survives the scope guard), or
* keeps only the new side, missing the case where the OLD side is the
  out-of-scope path.

The fix replaces these parsers with a structured
``git status --porcelain=v1 -z`` parser exposed by ``pdd.git_porcelain``
that surfaces ``status``, ``path``, and ``old_path``. Each caller then
chooses current-path-only, both-paths, or rename-aware semantics.

These tests exercise observable behavior (files on disk, return values,
HTTP response bodies). They fail on the buggy code and pass once the
structured parser is in place per call site.
"""
from __future__ import annotations

import os
import subprocess
from pathlib import Path
from typing import List
from unittest.mock import patch

import pytest


# ---------------------------------------------------------------------------
# Local helpers (kept self-contained — do not depend on other test modules)
# ---------------------------------------------------------------------------


def _git_env() -> dict:
    return {
        **os.environ,
        "GIT_AUTHOR_NAME": "Test",
        "GIT_AUTHOR_EMAIL": "t@t",
        "GIT_COMMITTER_NAME": "Test",
        "GIT_COMMITTER_EMAIL": "t@t",
        # Avoid hooks/external interactions on shared CI machines.
        "GIT_CONFIG_GLOBAL": "/dev/null",
        "GIT_CONFIG_SYSTEM": "/dev/null",
    }


def _git_init_with_files(repo: Path, files: dict[str, str]) -> None:
    """Initialize a git repo at *repo*, write *files*, commit them."""
    repo.mkdir(parents=True, exist_ok=True)
    env = _git_env()
    subprocess.run(["git", "init", str(repo)], check=True, capture_output=True, env=env)
    subprocess.run(
        ["git", "-C", str(repo), "config", "user.email", "t@t"],
        check=True, capture_output=True, env=env,
    )
    subprocess.run(
        ["git", "-C", str(repo), "config", "user.name", "Test"],
        check=True, capture_output=True, env=env,
    )
    for rel, content in files.items():
        target = repo / rel
        target.parent.mkdir(parents=True, exist_ok=True)
        target.write_text(content)
    subprocess.run(["git", "-C", str(repo), "add", "-A"], check=True, capture_output=True, env=env)
    subprocess.run(
        ["git", "-C", str(repo), "commit", "-m", "initial"],
        check=True, capture_output=True, env=env,
    )


def _git_run(repo: Path, *args: str) -> subprocess.CompletedProcess:
    return subprocess.run(
        ["git", "-C", str(repo), *args],
        check=True,
        capture_output=True,
        text=True,
        env=_git_env(),
    )


def _completed(stdout, returncode: int = 0, stderr=b""):
    return subprocess.CompletedProcess(
        args=["git"],
        returncode=returncode,
        stdout=stdout,
        stderr=stderr,
    )


# ===========================================================================
# Tests 3 & 4 — pdd.agentic_common._revert_out_of_scope_changes
# ===========================================================================


class TestRevertOutOfScopeRenames1080:
    """Issue #1080: scope guard must handle staged renames correctly."""

    def test_reverts_out_of_scope_staged_rename(self, tmp_path):
        """A staged rename of an out-of-scope file must be fully reverted.

        After ``git mv unrelated.py renamed_unrelated.py``:

        * The original ``unrelated.py`` must be restored from HEAD.
        * The renamed ``renamed_unrelated.py`` must no longer exist.
        * The returned list must contain real Path objects, never the
          fake ``Path("unrelated.py -> renamed_unrelated.py")`` literal
          that the buggy ``line[3:]`` parser produces.
        """
        from pdd.agentic_common import _revert_out_of_scope_changes

        proj = tmp_path / "repo"
        _git_init_with_files(proj, {
            "code.py": "def main(): pass\n",
            "unrelated.py": "def other(): pass\n",
        })

        # Stage a rename — porcelain (text mode) emits:
        #   R  unrelated.py -> renamed_unrelated.py
        _git_run(proj, "mv", "unrelated.py", "renamed_unrelated.py")

        allowed = {(proj / "code.py").resolve()}
        reverted: List[Path] = _revert_out_of_scope_changes(proj, allowed)

        # Behavioral check: the rename must be undone on disk.
        assert (proj / "unrelated.py").exists(), (
            "Out-of-scope rename survived: original file was not restored"
        )
        assert (proj / "unrelated.py").read_text() == "def other(): pass\n"
        assert not (proj / "renamed_unrelated.py").exists(), (
            "Out-of-scope rename survived: new-side file still exists"
        )

        # No fake combined-path literal in the return value.
        for p in reverted:
            assert " -> " not in str(p), (
                f"Fake combined path leaked into return value: {p!r}"
            )

    def test_preserves_allowed_rename(self, tmp_path):
        """An allowed rename (both sides in scope) must NOT be reverted."""
        from pdd.agentic_common import _revert_out_of_scope_changes

        proj = tmp_path / "repo"
        _git_init_with_files(proj, {
            "code.py": "def main(): pass\n",
            "other_in_scope.py": "x = 1\n",
        })

        _git_run(proj, "mv", "code.py", "code_renamed.py")

        # Both sides explicitly allowed.
        allowed = {
            (proj / "code.py").resolve(),
            (proj / "code_renamed.py").resolve(),
            (proj / "other_in_scope.py").resolve(),
        }
        reverted = _revert_out_of_scope_changes(proj, allowed)

        # The rename must remain in place.
        assert (proj / "code_renamed.py").exists(), (
            "Allowed rename was wrongly reverted: new-side file is gone"
        )
        assert not (proj / "code.py").exists(), (
            "Allowed rename was wrongly reverted: old-side file came back"
        )
        # No revert occurred.
        assert reverted == [], (
            f"Allowed rename should produce empty revert list, got {reverted!r}"
        )


# ===========================================================================
# Tests 5, 6, 7 — pdd.agentic_common_worktree.revert_out_of_scope_changes_with_dirs
# ===========================================================================


class TestRevertWithDirsRenames1080:
    """Issue #1080: ``revert_out_of_scope_changes_with_dirs`` must be
    rename-aware (consider BOTH old and new sides) and must never
    construct a fake combined ``"old -> new"`` path.
    """

    def test_reverts_when_old_side_is_out_of_scope(self, tmp_path):
        """Rename from out-of-scope OLD path into an in-scope NEW path
        is still out-of-scope and must be reverted."""
        from pdd.agentic_common_worktree import (
            revert_out_of_scope_changes_with_dirs,
        )

        # Build a real repo so the ``git checkout HEAD --`` call works.
        _git_init_with_files(tmp_path, {
            "scripts/external.py": "external original\n",
            "pdd/in_scope.py": "in_scope\n",
        })
        _git_run(tmp_path, "mv", "scripts/external.py", "pdd/legit.py")

        result = revert_out_of_scope_changes_with_dirs(
            tmp_path,
            allowed_dirs={"pdd/"},
            allowed_files=set(),
        )

        # Old side was out of scope → rename must be undone.
        assert (tmp_path / "scripts" / "external.py").exists(), (
            "Out-of-scope old side was not restored: rename escaped scope "
            "guard via new-side-only parsing"
        )
        assert (tmp_path / "scripts" / "external.py").read_text() == "external original\n"
        assert not (tmp_path / "pdd" / "legit.py").exists(), (
            "Out-of-scope rename survived in pdd/legit.py"
        )

        # Result must reflect a revert action.
        assert result, (
            f"Expected non-empty reverted list, got {result!r} — "
            "the guard did not detect the out-of-scope old side"
        )

    def test_reverts_purely_out_of_scope_rename_without_fake_path(self, tmp_path):
        """When both old and new sides are out of scope, the rename
        must be reverted and the returned list must never contain a
        ``Path("old -> new")`` literal."""
        from pdd.agentic_common_worktree import (
            revert_out_of_scope_changes_with_dirs,
        )

        _git_init_with_files(tmp_path, {
            "scripts/old.py": "scripts old\n",
            "pdd/keep.py": "keep\n",
        })
        _git_run(tmp_path, "mv", "scripts/old.py", "scripts/new.py")

        result = revert_out_of_scope_changes_with_dirs(
            tmp_path,
            allowed_dirs={"pdd/"},
            allowed_files=set(),
        )

        # Disk state: rename undone.
        assert (tmp_path / "scripts" / "old.py").exists()
        assert (tmp_path / "scripts" / "old.py").read_text() == "scripts old\n"
        assert not (tmp_path / "scripts" / "new.py").exists()

        # No fake combined path literal.
        for entry in result:
            text = str(entry)
            assert " -> " not in text, (
                f"Fake combined path leaked into reverted list: {entry!r}"
            )

    def test_handles_paths_with_arrow_substring(self, tmp_path):
        """An out-of-scope untracked path whose name literally contains
        ``" -> "`` must be REMOVED by the guard, using the file's real
        name. The buggy parser truncates on ``" -> "`` and then calls
        ``os.remove`` on the wrong (non-existent) path, so the
        out-of-scope file silently survives.
        """
        from pdd.agentic_common_worktree import (
            revert_out_of_scope_changes_with_dirs,
        )

        # Anchor file so the repo is non-empty; use core.quotePath=false
        # so the untracked path appears verbatim in porcelain output
        # (no surrounding C-quotes from git itself).
        _git_init_with_files(tmp_path, {
            "pdd/anchor.py": "x\n",
        })
        _git_run(tmp_path, "config", "core.quotePath", "false")

        # Place an untracked file with " -> " in its name at the repo
        # root — explicitly OUT of scope (no pdd/ prefix).
        weird = tmp_path / "bogus -> file.txt"
        weird.write_text("junk\n")

        result = revert_out_of_scope_changes_with_dirs(
            tmp_path,
            allowed_dirs={"pdd/"},
            allowed_files=set(),
        )

        # The out-of-scope untracked file MUST be removed. Under the
        # buggy parser, ``split(' -> ')[-1]`` reduces the path to
        # ``file.txt``; ``os.remove(repo/'file.txt')`` then fails because
        # no such file exists, leaving the real file in place.
        assert not weird.exists(), (
            "Out-of-scope untracked file with ' -> ' in its name was "
            "NOT removed — the parser truncated the path on ' -> '"
        )
        # The reverted list should mention the real path (no truncation).
        assert any(
            str(p).endswith("bogus -> file.txt") for p in result
        ), f"Reverted list missing real path: {result!r}"


# ===========================================================================
# Tests 8 & 9 — pdd.agentic_change_orchestrator._detect_worktree_changes
# ===========================================================================


class TestDetectWorktreeChangesRenames1080:
    """``_detect_worktree_changes`` documented behavior: return the
    CURRENT (new) path for a rename, verbatim. The structured-parser
    migration must preserve that contract and must not be fooled by
    paths containing the literal ``" -> "`` substring.
    """

    def test_returns_new_path_only_for_renamed_prompt(self, tmp_path):
        from pdd.agentic_change_orchestrator import _detect_worktree_changes

        _git_init_with_files(tmp_path, {
            "prompts/old.prompt": "alpha\n",
            "code.py": "x\n",
        })
        _git_run(tmp_path, "mv", "prompts/old.prompt", "prompts/new.prompt")

        files = _detect_worktree_changes(tmp_path)

        # New path appears, old path does not, no combined literal.
        assert "prompts/new.prompt" in files, (
            f"Renamed prompt's NEW path missing from {files!r}"
        )
        assert "prompts/old.prompt" not in files, (
            f"Renamed prompt's OLD path leaked into {files!r}"
        )
        for entry in files:
            assert " -> " not in entry, (
                f"Combined ' -> ' literal leaked into {entry!r}"
            )

    def test_handles_filename_with_arrow_substring(self, tmp_path):
        """An untracked prompt whose name contains ``" -> "`` must be
        returned verbatim, not naively truncated by ``split(' -> ')``."""
        from pdd.agentic_change_orchestrator import _detect_worktree_changes

        _git_init_with_files(tmp_path, {
            "anchor.txt": "x\n",
        })
        _git_run(tmp_path, "config", "core.quotePath", "false")
        prompts_dir = tmp_path / "prompts"
        prompts_dir.mkdir()
        weird_name = "weird -> name.prompt"
        (prompts_dir / weird_name).write_text("body\n")

        files = _detect_worktree_changes(tmp_path)

        expected = f"prompts/{weird_name}"
        assert expected in files, (
            f"Filename containing ' -> ' was mis-parsed; got {files!r}"
        )


# ===========================================================================
# Tests 10 & 11 — /prompts/changed endpoint
# ===========================================================================


class TestPromptsChangedEndpoint1080:
    """The ``/prompts/changed`` endpoint must report renamed prompt
    paths correctly — current (new) path only, verbatim, no quoting
    artifacts or ``" -> "`` literals.
    """

    @pytest.mark.asyncio
    async def test_returns_new_path_for_renamed_prompt(self, tmp_path):
        from pdd.server.routes.files import list_changed_prompt_files
        from pdd.server.security import PathValidator

        # Init repo on a "main" branch.
        _git_init_with_files(tmp_path, {
            "prompts/orig.prompt": "alpha\n",
            "README.md": "readme\n",
        })
        # Ensure branch is named "main" for the diff comparison.
        _git_run(tmp_path, "branch", "-M", "main")

        # Stage a rename.
        _git_run(tmp_path, "mv", "prompts/orig.prompt", "prompts/renamed.prompt")

        validator = PathValidator(project_root=tmp_path)
        result = await list_changed_prompt_files(
            base_branch="main", validator=validator,
        )

        changed = result["changed_prompts"]
        assert "prompts/renamed.prompt" in changed, (
            f"New-side prompt missing from {changed!r}"
        )
        # No fake combined path or quoting artifacts.
        for entry in changed:
            assert " -> " not in entry, (
                f"Combined path literal in response: {entry!r}"
            )
            assert not entry.startswith('"'), (
                f"Stray quote in path: {entry!r}"
            )
            assert not entry.endswith('"'), (
                f"Stray quote in path: {entry!r}"
            )

    @pytest.mark.asyncio
    async def test_handles_renamed_prompt_with_space_in_name(self, tmp_path):
        """When git C-quotes a renamed prompt path because of a space,
        the endpoint must still return the unquoted path verbatim."""
        from pdd.server.routes.files import list_changed_prompt_files
        from pdd.server.security import PathValidator

        _git_init_with_files(tmp_path, {
            "prompts/orig.prompt": "alpha\n",
            "README.md": "readme\n",
        })
        _git_run(tmp_path, "branch", "-M", "main")
        _git_run(tmp_path, "mv", "prompts/orig.prompt", "prompts/new name.prompt")

        validator = PathValidator(project_root=tmp_path)
        result = await list_changed_prompt_files(
            base_branch="main", validator=validator,
        )

        changed = result["changed_prompts"]
        assert "prompts/new name.prompt" in changed, (
            f"Renamed prompt with space missing from {changed!r}"
        )
        # No quoted variant.
        assert '"prompts/new name.prompt"' not in changed, (
            f"Quoted variant leaked into response: {changed!r}"
        )
