# tests/test_sync_code_main.py
"""
Tests for change-detection functions (formerly in pdd sync-code, now in pdd.update_main).

Covers:
- derive_basename_and_language: basename/language extraction
- is_code_changed: fingerprint primary, git fallback
- get_git_changed_files: git subprocess mocking
- update_main repo-mode with change detection: end-to-end orchestration
- CLI integration via CliRunner (pdd update --base-branch)
"""

import os
import pytest
from pathlib import Path
from unittest.mock import patch, MagicMock, call

import click
from click.testing import CliRunner

from pdd.update_main import (
    derive_basename_and_language,
    get_git_changed_files,
    is_code_changed,
    update_main,
)


# ---------------------------------------------------------------------------
# derive_basename_and_language
# ---------------------------------------------------------------------------


class TestDeriveBasenameAndLanguage:
    """Tests for basename and language extraction from code file paths."""

    @patch("pdd.update_main.get_language", return_value="Python")
    def test_python_file(self, mock_lang):
        """Extracts basename and lowercased language for a .py file."""
        basename, lang = derive_basename_and_language("/repo/src/my_module.py", "/repo")
        assert basename == "my_module"
        assert lang == "python"
        mock_lang.assert_called_once_with(".py")

    @patch("pdd.update_main.get_language", return_value="JavaScript")
    def test_javascript_file(self, mock_lang):
        """Extracts basename and lowercased language for a .js file."""
        basename, lang = derive_basename_and_language("/repo/app/index.js", "/repo")
        assert basename == "index"
        assert lang == "javascript"

    @patch("pdd.update_main.get_language", return_value="")
    def test_unknown_extension_returns_none(self, mock_lang):
        """Returns (None, None) for files with unknown extensions."""
        basename, lang = derive_basename_and_language("/repo/data.xyz", "/repo")
        assert basename is None
        assert lang is None

    @patch("pdd.update_main.get_language", return_value=None)
    def test_none_language_returns_none(self, mock_lang):
        """Returns (None, None) when get_language returns None."""
        basename, lang = derive_basename_and_language("/repo/file.bin", "/repo")
        assert basename is None
        assert lang is None

    @patch("pdd.update_main.get_language", return_value="Python")
    def test_nested_path(self, mock_lang):
        """Extracts only the filename stem, not the directory structure."""
        basename, lang = derive_basename_and_language(
            "/repo/a/b/c/deep_module.py", "/repo"
        )
        assert basename == "deep_module"
        assert lang == "python"


# ---------------------------------------------------------------------------
# is_code_changed
# ---------------------------------------------------------------------------


class TestIsCodeChanged:
    """Tests for change detection via fingerprint or git fallback."""

    @patch("pdd.update_main.derive_basename_and_language", return_value=(None, None))
    def test_unknown_extension_not_changed(self, mock_derive):
        """Files with unknown extensions are never considered changed."""
        changed, reason = is_code_changed("/repo/data.xyz", "/repo", set())
        assert changed is False
        assert "unknown extension" in reason

    @patch("pdd.update_main.calculate_sha256", return_value="aaa111")
    @patch("pdd.update_main.read_fingerprint")
    @patch("pdd.update_main.derive_basename_and_language", return_value=("mod", "python"))
    def test_fingerprint_hash_matches(self, mock_derive, mock_fp, mock_sha):
        """When fingerprint code_hash matches current hash, not changed."""
        fp = MagicMock()
        fp.code_hash = "aaa111"
        mock_fp.return_value = fp

        changed, reason = is_code_changed("/repo/mod.py", "/repo", set())
        assert changed is False
        assert "matches fingerprint" in reason

    @patch("pdd.update_main.calculate_sha256", return_value="bbb222")
    @patch("pdd.update_main.read_fingerprint")
    @patch("pdd.update_main.derive_basename_and_language", return_value=("mod", "python"))
    def test_fingerprint_hash_differs(self, mock_derive, mock_fp, mock_sha):
        """When fingerprint code_hash differs from current hash, changed."""
        fp = MagicMock()
        fp.code_hash = "aaa111"
        mock_fp.return_value = fp

        changed, reason = is_code_changed("/repo/mod.py", "/repo", set())
        assert changed is True
        assert "differs from fingerprint" in reason

    @patch("pdd.update_main.read_fingerprint")
    @patch("pdd.update_main.derive_basename_and_language", return_value=("mod", "python"))
    def test_fingerprint_no_code_hash(self, mock_derive, mock_fp):
        """When fingerprint exists but has no code_hash, consider changed."""
        fp = MagicMock()
        fp.code_hash = None
        mock_fp.return_value = fp

        changed, reason = is_code_changed("/repo/mod.py", "/repo", set())
        assert changed is True
        assert "no code_hash" in reason

    @patch("pdd.update_main.calculate_sha256", return_value=None)
    @patch("pdd.update_main.read_fingerprint")
    @patch("pdd.update_main.derive_basename_and_language", return_value=("mod", "python"))
    def test_fingerprint_cannot_compute_hash(self, mock_derive, mock_fp, mock_sha):
        """When current hash can't be computed, not changed."""
        fp = MagicMock()
        fp.code_hash = "aaa111"
        mock_fp.return_value = fp

        changed, reason = is_code_changed("/repo/mod.py", "/repo", set())
        assert changed is False
        assert "could not compute" in reason

    @patch("pdd.update_main.read_fingerprint", return_value=None)
    @patch("pdd.update_main.derive_basename_and_language", return_value=("mod", "python"))
    def test_no_fingerprint_in_git_set(self, mock_derive, mock_fp):
        """No fingerprint + file in git changed set -> changed."""
        git_set = {"/repo/mod.py"}
        changed, reason = is_code_changed("/repo/mod.py", "/repo", git_set)
        assert changed is True
        assert "git changed set" in reason

    @patch("pdd.update_main.read_fingerprint", return_value=None)
    @patch("pdd.update_main.derive_basename_and_language", return_value=("mod", "python"))
    def test_no_fingerprint_not_in_git_set(self, mock_derive, mock_fp):
        """No fingerprint + file not in git changed set -> not changed."""
        git_set = {"/repo/other.py"}
        changed, reason = is_code_changed("/repo/mod.py", "/repo", git_set)
        assert changed is False
        assert "not in git changed set" in reason


# ---------------------------------------------------------------------------
# get_git_changed_files
# ---------------------------------------------------------------------------


class TestGetGitChangedFiles:
    """Tests for git-based change detection."""

    @patch("pdd.update_main.subprocess.run")
    def test_all_three_sources(self, mock_run):
        """Combines committed, uncommitted, and untracked files."""
        repo_root = "/repo"

        def side_effect(cmd, **kwargs):
            result = MagicMock()
            result.stdout = ""
            if "merge-base" in cmd:
                result.stdout = "abc123\n"
            elif "diff" in cmd and "abc123" in cmd:
                # Committed changes
                result.stdout = "file1.py\nfile2.py\n"
            elif "diff" in cmd and "HEAD" in cmd:
                # Uncommitted changes
                result.stdout = "file3.py\n"
            elif "ls-files" in cmd:
                # Untracked
                result.stdout = "file4.py\n"
            return result

        mock_run.side_effect = side_effect

        result = get_git_changed_files(repo_root, "main")
        assert result == {
            "/repo/file1.py",
            "/repo/file2.py",
            "/repo/file3.py",
            "/repo/file4.py",
        }

    @patch("pdd.update_main.subprocess.run")
    def test_empty_when_all_fail(self, mock_run):
        """Returns empty set when all git commands fail."""
        import subprocess as sp

        mock_run.side_effect = sp.CalledProcessError(1, "git")

        result = get_git_changed_files("/repo", "main")
        assert result == set()

    @patch("pdd.update_main.subprocess.run")
    def test_deduplication(self, mock_run):
        """Same file from multiple sources is not duplicated."""
        def side_effect(cmd, **kwargs):
            result = MagicMock()
            result.stdout = ""
            if "merge-base" in cmd:
                result.stdout = "abc123\n"
            elif "diff" in cmd and "abc123" in cmd:
                result.stdout = "shared.py\n"
            elif "diff" in cmd and "HEAD" in cmd:
                result.stdout = "shared.py\n"
            elif "ls-files" in cmd:
                result.stdout = ""
            return result

        mock_run.side_effect = side_effect

        result = get_git_changed_files("/repo", "main")
        assert result == {"/repo/shared.py"}

    @patch("pdd.update_main.subprocess.run")
    def test_empty_output_lines(self, mock_run):
        """Empty stdout produces no entries."""
        def side_effect(cmd, **kwargs):
            result = MagicMock()
            result.stdout = ""
            if "merge-base" in cmd:
                result.stdout = "abc123\n"
            return result

        mock_run.side_effect = side_effect

        result = get_git_changed_files("/repo", "main")
        assert result == set()


# ---------------------------------------------------------------------------
# update_main repo-mode with change detection (replaces sync_code_main tests)
# ---------------------------------------------------------------------------


class TestUpdateMainRepoModeChangeDetection:
    """Tests for update_main repo-mode with change-detection filtering."""

    def _make_ctx(self, **obj_overrides):
        """Helper to create a Click context with defaults."""
        obj = {"quiet": False, "verbose": False, "strength": 0.5, "temperature": 0}
        obj.update(obj_overrides)
        ctx = click.Context(click.Command("update"), obj=obj)
        return ctx

    @patch("pdd.update_main.git.Repo")
    def test_not_a_git_repo(self, mock_repo_cls):
        """Returns None and prints error when not in a git repo."""
        import git as gitmod

        mock_repo_cls.side_effect = gitmod.InvalidGitRepositoryError("not a repo")
        ctx = self._make_ctx()
        result = update_main(
            ctx, input_prompt_file=None, modified_code_file=None,
            input_code_file=None, output=None, repo=True,
        )
        assert result is None

    @patch("pdd.update_main.find_and_resolve_all_pairs", return_value=[])
    @patch("pdd.update_main.git.Repo")
    def test_no_pairs_found(self, mock_repo_cls, mock_find):
        """Returns None when no code files are found."""
        mock_repo = MagicMock()
        mock_repo.working_tree_dir = "/repo"
        mock_repo_cls.return_value = mock_repo

        ctx = self._make_ctx()
        result = update_main(
            ctx, input_prompt_file=None, modified_code_file=None,
            input_code_file=None, output=None, repo=True,
        )
        assert result is None

    @patch("pdd.update_main.is_code_changed", return_value=(False, "matches"))
    @patch("pdd.update_main.get_git_changed_files", return_value=set())
    @patch("pdd.update_main.find_and_resolve_all_pairs", return_value=[
        ("/repo/prompts/mod_python.prompt", "/repo/mod.py"),
    ])
    @patch("pdd.update_main.git.Repo")
    def test_no_changed_files(self, mock_repo_cls, mock_find, mock_git, mock_changed):
        """Returns None when no code files have changed."""
        mock_repo = MagicMock()
        mock_repo.working_tree_dir = "/repo"
        mock_repo_cls.return_value = mock_repo

        ctx = self._make_ctx()
        result = update_main(
            ctx, input_prompt_file=None, modified_code_file=None,
            input_code_file=None, output=None, repo=True,
        )
        assert result is None

    @patch("pdd.architecture_sync.update_architecture_from_prompt", return_value={"success": False, "updated": False, "changes": {}})
    @patch("pdd.update_main.update_file_pair")
    @patch("pdd.update_main.is_code_changed")
    @patch("pdd.update_main.get_git_changed_files", return_value=set())
    @patch("pdd.update_main.find_and_resolve_all_pairs", return_value=[
        ("/repo/prompts/a_python.prompt", "/repo/a.py"),
        ("/repo/prompts/b_python.prompt", "/repo/b.py"),
    ])
    @patch("pdd.update_main.git.Repo")
    def test_processes_changed_pairs_only(
        self, mock_repo_cls, mock_find, mock_git, mock_changed, mock_update, mock_arch
    ):
        """Only changed files are passed to update_file_pair."""
        mock_repo = MagicMock()
        mock_repo.working_tree_dir = "/repo"
        mock_repo_cls.return_value = mock_repo

        # Only a.py is changed
        mock_changed.side_effect = [
            (True, "differs"),
            (False, "matches"),
        ]
        mock_update.return_value = {
            "prompt_file": "/repo/prompts/a_python.prompt",
            "status": "success",
            "cost": 0.01,
            "model": "test-model",
            "error": "",
        }

        ctx = self._make_ctx(quiet=True)
        result = update_main(
            ctx, input_prompt_file=None, modified_code_file=None,
            input_code_file=None, output=None, repo=True,
        )

        assert result is not None
        msg, cost, model = result
        assert cost == pytest.approx(0.01)
        mock_update.assert_called_once()

    @patch("pdd.architecture_sync.update_architecture_from_prompt", return_value={"success": False, "updated": False, "changes": {}})
    @patch("pdd.update_main.update_file_pair")
    @patch("pdd.update_main.is_code_changed", return_value=(True, "differs"))
    @patch("pdd.update_main.get_git_changed_files", return_value=set())
    @patch("pdd.update_main.find_and_resolve_all_pairs", return_value=[
        ("/repo/prompts/a_python.prompt", "/repo/a.py"),
    ])
    @patch("pdd.update_main.git.Repo")
    def test_passes_simple_flag(
        self, mock_repo_cls, mock_find, mock_git, mock_changed, mock_update, mock_arch
    ):
        """The simple flag is forwarded to update_file_pair."""
        mock_repo = MagicMock()
        mock_repo.working_tree_dir = "/repo"
        mock_repo_cls.return_value = mock_repo

        mock_update.return_value = {
            "prompt_file": "/repo/prompts/a_python.prompt",
            "status": "success",
            "cost": 0.0,
            "model": "",
            "error": "",
        }

        ctx = self._make_ctx(quiet=True)
        update_main(
            ctx, input_prompt_file=None, modified_code_file=None,
            input_code_file=None, output=None, repo=True, simple=True,
        )

        _, kwargs = mock_update.call_args
        assert kwargs.get("simple") is True or mock_update.call_args[0][4] is True

    @patch("pdd.architecture_sync.update_architecture_from_prompt", return_value={"success": False, "updated": False, "changes": {}})
    @patch("pdd.update_main.update_file_pair")
    @patch("pdd.update_main.is_code_changed", return_value=(True, "differs"))
    @patch("pdd.update_main.get_git_changed_files", return_value=set())
    @patch("pdd.update_main.find_and_resolve_all_pairs", return_value=[
        ("/repo/prompts/a_python.prompt", "/repo/a.py"),
        ("/repo/prompts/b_python.prompt", "/repo/b.py"),
    ])
    @patch("pdd.update_main.git.Repo")
    def test_accumulates_cost(
        self, mock_repo_cls, mock_find, mock_git, mock_changed, mock_update, mock_arch
    ):
        """Total cost accumulates across all processed pairs."""
        mock_repo = MagicMock()
        mock_repo.working_tree_dir = "/repo"
        mock_repo_cls.return_value = mock_repo

        mock_update.side_effect = [
            {"prompt_file": "/repo/prompts/a_python.prompt", "status": "ok", "cost": 0.05, "model": "m1", "error": ""},
            {"prompt_file": "/repo/prompts/b_python.prompt", "status": "ok", "cost": 0.03, "model": "m2", "error": ""},
        ]

        ctx = self._make_ctx(quiet=True)
        result = update_main(
            ctx, input_prompt_file=None, modified_code_file=None,
            input_code_file=None, output=None, repo=True,
        )

        assert result is not None
        _, cost, models = result
        assert cost == pytest.approx(0.08)
        assert "m1" in models
        assert "m2" in models

    @patch("pdd.update_main.find_and_resolve_all_pairs", return_value=[
        ("/repo/prompts/a_python.prompt", "/repo/src/a.py"),
    ])
    @patch("pdd.update_main.git.Repo")
    @patch("pdd.update_main.is_code_changed", return_value=(False, "no change"))
    @patch("pdd.update_main.get_git_changed_files", return_value=set())
    def test_directory_passed_to_find_pairs(
        self, mock_git, mock_changed, mock_repo_cls, mock_find
    ):
        """When directory is specified, it is used as the scan root."""
        mock_repo = MagicMock()
        mock_repo.working_tree_dir = "/repo"
        mock_repo_cls.return_value = mock_repo

        ctx = self._make_ctx(quiet=True)
        update_main(
            ctx, input_prompt_file=None, modified_code_file=None,
            input_code_file=None, output=None, repo=True,
            directory="/repo/src",
        )

        mock_find.assert_called_once_with("/repo/src", True, None, None)


# ---------------------------------------------------------------------------
# CLI integration — pdd update with --base-branch
# ---------------------------------------------------------------------------


class TestUpdateCommandBaseBranch:
    """Tests for the --base-branch option on pdd update."""

    @patch("pdd.commands.modify.update_main", return_value=("done", 0.5, "model"))
    def test_base_branch_passed_through(self, mock_main):
        """CLI --base-branch option is forwarded to update_main."""
        from pdd.cli import cli

        runner = CliRunner()
        result = runner.invoke(
            cli,
            ["update", "--base-branch", "develop"],
            catch_exceptions=False,
        )

        assert result.exit_code == 0
        _, kwargs = mock_main.call_args
        assert kwargs["base_branch"] == "develop"

    def test_help_text_includes_base_branch(self):
        """The update command shows --base-branch in help text."""
        from pdd.cli import cli

        runner = CliRunner()
        result = runner.invoke(cli, ["update", "--help"])
        assert result.exit_code == 0
        assert "--base-branch" in result.output
