"""Tests for pdd.agentic_common_worktree module.

Test Plan (mapped to spec requirements):
=========================================
1.  get_git_root — returns Path on success, None on failure, None on timeout
2.  worktree_exists — True when path in porcelain output, False when not, False when no git root
3.  branch_exists — True on rc=0, False on rc!=0, False on timeout
4.  remove_worktree — (True, "") on success, (False, stderr) on failure, (False, msg) on timeout/OSError
5.  delete_branch — (True, "") on success, (False, stderr) on failure, (False, msg) on timeout/OSError
6.  resolve_main_ref — returns hash for first resolvable ref, "HEAD" fallback, tries all 4 refs in order
7.  setup_worktree — success path, git root failure, worktree naming with custom prefixes,
    cleanup of existing worktree/dir, resume_existing=True reuses branch, undeletable branch resets,
    quiet=True suppresses output, quiet=False prints, worktree add failure returns error
8.  get_modified_and_untracked — combines diff + ls-files, empty on failure, handles empty outputs
9.  check_target_file_unchanged — baseline (None sha), same sha, different sha, git failure fail-open,
    rev-parse failure returns (True, None)
10. revert_out_of_scope_changes_with_dirs — reverts tracked out-of-scope, removes untracked out-of-scope,
    keeps in-scope (dir prefix), keeps in-scope (allowed_files), handles renames, handles git status failure,
    handles timeout, handles os.remove failure
11. extract_block_marker — extracts content, case-insensitive, returns "" when no markers, multiline content,
    strips whitespace
"""
from __future__ import annotations

import os
import subprocess
from pathlib import Path
from typing import List
from unittest.mock import MagicMock, call, patch

import pytest

from pdd.agentic_common_worktree import (
    get_git_root,
    worktree_exists,
    branch_exists,
    remove_worktree,
    delete_branch,
    resolve_main_ref,
    setup_worktree,
    get_modified_and_untracked,
    check_target_file_unchanged,
    revert_out_of_scope_changes_with_dirs,
    extract_block_marker,
)

MODULE = "pdd.agentic_common_worktree"


def _cp(returncode: int = 0, stdout: str = "", stderr: str = "") -> subprocess.CompletedProcess:
    """Helper to build CompletedProcess."""
    return subprocess.CompletedProcess(args=["git"], returncode=returncode, stdout=stdout, stderr=stderr)


# =========================================================================
# 1. get_git_root
# =========================================================================

class TestGetGitRoot:
    def test_returns_path_on_success(self):
        with patch(f"{MODULE}.subprocess.run", return_value=_cp(stdout="/repo\n")):
            assert get_git_root(Path("/repo/sub")) == Path("/repo")

    def test_returns_none_on_failure(self):
        with patch(f"{MODULE}.subprocess.run", return_value=_cp(returncode=128)):
            assert get_git_root(Path("/tmp")) is None

    def test_returns_none_on_empty_stdout(self):
        with patch(f"{MODULE}.subprocess.run", return_value=_cp(stdout="")):
            assert get_git_root(Path("/tmp")) is None

    def test_returns_none_on_timeout(self):
        with patch(f"{MODULE}.subprocess.run", side_effect=subprocess.TimeoutExpired("git", 30)):
            assert get_git_root(Path("/tmp")) is None

    def test_returns_none_on_os_error(self):
        with patch(f"{MODULE}.subprocess.run", side_effect=OSError("no git")):
            assert get_git_root(Path("/tmp")) is None


# =========================================================================
# 2. worktree_exists
# =========================================================================

class TestWorktreeExists:
    def test_true_when_path_in_output(self):
        porcelain = "worktree /repo\nHEAD abc\n\nworktree /repo/.pdd/wt\nHEAD def\n\n"
        with patch(f"{MODULE}.subprocess.run") as mock_run:
            mock_run.side_effect = [
                _cp(stdout="/repo\n"),
                _cp(stdout=porcelain),
            ]
            assert worktree_exists(Path("/repo"), Path("/repo/.pdd/wt")) is True

    def test_false_when_path_not_in_output(self):
        porcelain = "worktree /repo\nHEAD abc\n\n"
        with patch(f"{MODULE}.subprocess.run") as mock_run:
            mock_run.side_effect = [
                _cp(stdout="/repo\n"),
                _cp(stdout=porcelain),
            ]
            assert worktree_exists(Path("/repo"), Path("/repo/.pdd/wt")) is False

    def test_false_when_no_git_root(self):
        with patch(f"{MODULE}.subprocess.run", return_value=_cp(returncode=128)):
            assert worktree_exists(Path("/tmp"), Path("/tmp/wt")) is False

    def test_false_on_porcelain_failure(self):
        with patch(f"{MODULE}.subprocess.run") as mock_run:
            mock_run.side_effect = [
                _cp(stdout="/repo\n"),
                _cp(returncode=1),
            ]
            assert worktree_exists(Path("/repo"), Path("/repo/.pdd/wt")) is False

    def test_false_on_timeout(self):
        with patch(f"{MODULE}.subprocess.run") as mock_run:
            mock_run.side_effect = [
                _cp(stdout="/repo\n"),
                subprocess.TimeoutExpired("git", 30),
            ]
            assert worktree_exists(Path("/repo"), Path("/repo/.pdd/wt")) is False


# =========================================================================
# 3. branch_exists
# =========================================================================

class TestBranchExists:
    def test_true_on_success(self):
        with patch(f"{MODULE}.subprocess.run", return_value=_cp(returncode=0)):
            assert branch_exists(Path("/repo"), "fix/issue-1") is True

    def test_false_on_failure(self):
        with patch(f"{MODULE}.subprocess.run", return_value=_cp(returncode=1)):
            assert branch_exists(Path("/repo"), "no-branch") is False

    def test_uses_correct_ref(self):
        with patch(f"{MODULE}.subprocess.run", return_value=_cp(returncode=0)) as mock_run:
            branch_exists(Path("/repo"), "fix/issue-99")
            args = mock_run.call_args[0][0]
            assert args == ["git", "show-ref", "--verify", "refs/heads/fix/issue-99"]

    def test_false_on_timeout(self):
        with patch(f"{MODULE}.subprocess.run", side_effect=subprocess.TimeoutExpired("git", 30)):
            assert branch_exists(Path("/repo"), "x") is False


# =========================================================================
# 4. remove_worktree
# =========================================================================

class TestRemoveWorktree:
    def test_success(self):
        with patch(f"{MODULE}.subprocess.run", return_value=_cp(returncode=0)):
            ok, err = remove_worktree(Path("/repo"), Path("/repo/.pdd/wt"))
            assert ok is True
            assert err == ""

    def test_failure_returns_stderr(self):
        with patch(f"{MODULE}.subprocess.run", return_value=_cp(returncode=1, stderr="bad worktree")):
            ok, err = remove_worktree(Path("/repo"), Path("/repo/.pdd/wt"))
            assert ok is False
            assert "bad worktree" in err

    def test_timeout(self):
        with patch(f"{MODULE}.subprocess.run", side_effect=subprocess.TimeoutExpired("git", 60)):
            ok, err = remove_worktree(Path("/repo"), Path("/repo/.pdd/wt"))
            assert ok is False
            assert "Timed out" in err

    def test_os_error(self):
        with patch(f"{MODULE}.subprocess.run", side_effect=OSError("perm denied")):
            ok, err = remove_worktree(Path("/repo"), Path("/repo/.pdd/wt"))
            assert ok is False
            assert "perm denied" in err

    def test_uses_force_flag(self):
        with patch(f"{MODULE}.subprocess.run", return_value=_cp()) as mock_run:
            remove_worktree(Path("/repo"), Path("/wt"))
            args = mock_run.call_args[0][0]
            assert "--force" in args


# =========================================================================
# 5. delete_branch
# =========================================================================

class TestDeleteBranch:
    def test_success(self):
        with patch(f"{MODULE}.subprocess.run", return_value=_cp(returncode=0)):
            ok, err = delete_branch(Path("/repo"), "fix/issue-1")
            assert ok is True
            assert err == ""

    def test_failure(self):
        with patch(f"{MODULE}.subprocess.run", return_value=_cp(returncode=1, stderr="not found")):
            ok, err = delete_branch(Path("/repo"), "nope")
            assert ok is False
            assert "not found" in err

    def test_timeout(self):
        with patch(f"{MODULE}.subprocess.run", side_effect=subprocess.TimeoutExpired("git", 30)):
            ok, err = delete_branch(Path("/repo"), "x")
            assert ok is False
            assert "Timed out" in err

    def test_uses_dash_D(self):
        with patch(f"{MODULE}.subprocess.run", return_value=_cp()) as mock_run:
            delete_branch(Path("/repo"), "br")
            args = mock_run.call_args[0][0]
            assert args == ["git", "branch", "-D", "br"]


# =========================================================================
# 6. resolve_main_ref
# =========================================================================

class TestResolveMainRef:
    def test_returns_first_resolved(self):
        with patch(f"{MODULE}.subprocess.run") as mock_run:
            mock_run.side_effect = [
                _cp(returncode=1),  # origin/main fails
                _cp(returncode=0, stdout="hash123\n"),  # origin/master succeeds
            ]
            assert resolve_main_ref(Path("/repo")) == "hash123"

    def test_fallback_to_head(self):
        with patch(f"{MODULE}.subprocess.run", return_value=_cp(returncode=1)):
            assert resolve_main_ref(Path("/repo")) == "HEAD"

    def test_tries_all_four_refs(self):
        with patch(f"{MODULE}.subprocess.run", return_value=_cp(returncode=1)) as mock_run:
            resolve_main_ref(Path("/repo"))
            assert mock_run.call_count == 4
            refs_tried = [c[0][0][3] for c in mock_run.call_args_list]
            assert refs_tried == ["origin/main", "origin/master", "main", "master"]

    def test_origin_main_first(self):
        with patch(f"{MODULE}.subprocess.run", return_value=_cp(returncode=0, stdout="abc\n")):
            assert resolve_main_ref(Path("/repo")) == "abc"


# =========================================================================
# 7. setup_worktree
# =========================================================================

class TestSetupWorktree:
    def test_success_returns_path_and_none(self, tmp_path):
        git_root = tmp_path / "repo"
        git_root.mkdir()
        with patch(f"{MODULE}.get_git_root", return_value=git_root), \
             patch(f"{MODULE}.worktree_exists", return_value=False), \
             patch(f"{MODULE}.branch_exists", return_value=False), \
             patch(f"{MODULE}.resolve_main_ref", return_value="abc"), \
             patch(f"{MODULE}.subprocess.run", return_value=_cp()):
            wt, err = setup_worktree(git_root, 42, quiet=True)
            assert wt is not None
            assert err is None
            assert "fix-issue-42" in str(wt)

    def test_no_git_root(self):
        with patch(f"{MODULE}.get_git_root", return_value=None):
            wt, err = setup_worktree(Path("/tmp"), 1, quiet=True)
            assert wt is None
            assert err is not None

    def test_custom_prefixes(self, tmp_path):
        git_root = tmp_path / "repo"
        git_root.mkdir()
        with patch(f"{MODULE}.get_git_root", return_value=git_root), \
             patch(f"{MODULE}.worktree_exists", return_value=False), \
             patch(f"{MODULE}.branch_exists", return_value=False), \
             patch(f"{MODULE}.resolve_main_ref", return_value="abc"), \
             patch(f"{MODULE}.subprocess.run", return_value=_cp()) as mock_run:
            wt, err = setup_worktree(git_root, 7, quiet=True, branch_prefix="change", worktree_prefix="change")
            assert "change-issue-7" in str(wt)
            # Check branch name in the git command
            cmd_args = mock_run.call_args[0][0]
            assert "change/issue-7" in cmd_args

    def test_cleanup_existing_worktree(self, tmp_path):
        git_root = tmp_path / "repo"
        git_root.mkdir()
        with patch(f"{MODULE}.get_git_root", return_value=git_root), \
             patch(f"{MODULE}.worktree_exists", return_value=True), \
             patch(f"{MODULE}.remove_worktree", return_value=(True, "")) as mock_remove, \
             patch(f"{MODULE}.branch_exists", return_value=False), \
             patch(f"{MODULE}.resolve_main_ref", return_value="abc"), \
             patch(f"{MODULE}.subprocess.run", return_value=_cp()):
            wt, err = setup_worktree(git_root, 1, quiet=True)
            mock_remove.assert_called_once()
            assert wt is not None

    def test_resume_existing_reuses_branch(self, tmp_path):
        git_root = tmp_path / "repo"
        git_root.mkdir()
        with patch(f"{MODULE}.get_git_root", return_value=git_root), \
             patch(f"{MODULE}.worktree_exists", return_value=False), \
             patch(f"{MODULE}.branch_exists", return_value=True), \
             patch(f"{MODULE}.resolve_main_ref", return_value="abc"), \
             patch(f"{MODULE}.subprocess.run", return_value=_cp()) as mock_run:
            wt, err = setup_worktree(git_root, 5, quiet=True, resume_existing=True)
            assert wt is not None
            cmd = mock_run.call_args[0][0]
            assert "--force" in cmd
            assert "-b" not in cmd

    def test_undeletable_branch_resets(self, tmp_path):
        git_root = tmp_path / "repo"
        git_root.mkdir()
        with patch(f"{MODULE}.get_git_root", return_value=git_root), \
             patch(f"{MODULE}.worktree_exists", return_value=False), \
             patch(f"{MODULE}.branch_exists", return_value=True), \
             patch(f"{MODULE}.delete_branch", return_value=(False, "checked out")), \
             patch(f"{MODULE}.resolve_main_ref", return_value="abc123"), \
             patch(f"{MODULE}.subprocess.run") as mock_run:
            # First call: worktree add --force, second call: git reset --hard
            mock_run.return_value = _cp()
            wt, err = setup_worktree(git_root, 3, quiet=True, resume_existing=False)
            assert wt is not None
            # Should have called git reset --hard
            assert mock_run.call_count == 2
            reset_cmd = mock_run.call_args_list[1][0][0]
            assert "reset" in reset_cmd
            assert "--hard" in reset_cmd

    def test_quiet_false_prints(self, tmp_path, capsys):
        git_root = tmp_path / "repo"
        git_root.mkdir()
        with patch(f"{MODULE}.get_git_root", return_value=git_root), \
             patch(f"{MODULE}.worktree_exists", return_value=False), \
             patch(f"{MODULE}.branch_exists", return_value=False), \
             patch(f"{MODULE}.resolve_main_ref", return_value="abc"), \
             patch(f"{MODULE}.subprocess.run", return_value=_cp()), \
             patch(f"{MODULE}.console") as mock_console:
            setup_worktree(git_root, 1, quiet=False)
            mock_console.print.assert_called_once()

    def test_quiet_true_no_print(self, tmp_path):
        git_root = tmp_path / "repo"
        git_root.mkdir()
        with patch(f"{MODULE}.get_git_root", return_value=git_root), \
             patch(f"{MODULE}.worktree_exists", return_value=False), \
             patch(f"{MODULE}.branch_exists", return_value=False), \
             patch(f"{MODULE}.resolve_main_ref", return_value="abc"), \
             patch(f"{MODULE}.subprocess.run", return_value=_cp()), \
             patch(f"{MODULE}.console") as mock_console:
            setup_worktree(git_root, 1, quiet=True)
            mock_console.print.assert_not_called()

    def test_worktree_add_failure(self, tmp_path):
        git_root = tmp_path / "repo"
        git_root.mkdir()
        with patch(f"{MODULE}.get_git_root", return_value=git_root), \
             patch(f"{MODULE}.worktree_exists", return_value=False), \
             patch(f"{MODULE}.branch_exists", return_value=False), \
             patch(f"{MODULE}.resolve_main_ref", return_value="abc"), \
             patch(f"{MODULE}.subprocess.run", return_value=_cp(returncode=1, stderr="fatal error")):
            wt, err = setup_worktree(git_root, 1, quiet=True)
            assert wt is None
            assert "fatal error" in err

    def test_timeout_during_creation(self, tmp_path):
        git_root = tmp_path / "repo"
        git_root.mkdir()
        with patch(f"{MODULE}.get_git_root", return_value=git_root), \
             patch(f"{MODULE}.worktree_exists", return_value=False), \
             patch(f"{MODULE}.branch_exists", return_value=False), \
             patch(f"{MODULE}.resolve_main_ref", return_value="abc"), \
             patch(f"{MODULE}.subprocess.run", side_effect=subprocess.TimeoutExpired("git", 120)):
            wt, err = setup_worktree(git_root, 1, quiet=True)
            assert wt is None
            assert "Timed out" in err


# =========================================================================
# 8. get_modified_and_untracked
# =========================================================================

class TestGetModifiedAndUntracked:
    def test_combines_diff_and_ls_files(self):
        with patch(f"{MODULE}.subprocess.run") as mock_run:
            mock_run.side_effect = [
                _cp(stdout="a.py\nb.py\n"),
                _cp(stdout="c.txt\n"),
            ]
            result = get_modified_and_untracked(Path("/repo"))
            assert result == ["a.py", "b.py", "c.txt"]

    def test_empty_on_failure(self):
        with patch(f"{MODULE}.subprocess.run", side_effect=subprocess.TimeoutExpired("git", 30)):
            assert get_modified_and_untracked(Path("/repo")) == []

    def test_handles_empty_diff(self):
        with patch(f"{MODULE}.subprocess.run") as mock_run:
            mock_run.side_effect = [
                _cp(stdout=""),
                _cp(stdout="new.txt\n"),
            ]
            assert get_modified_and_untracked(Path("/repo")) == ["new.txt"]

    def test_handles_empty_untracked(self):
        with patch(f"{MODULE}.subprocess.run") as mock_run:
            mock_run.side_effect = [
                _cp(stdout="mod.py\n"),
                _cp(stdout=""),
            ]
            assert get_modified_and_untracked(Path("/repo")) == ["mod.py"]

    def test_handles_both_empty(self):
        with patch(f"{MODULE}.subprocess.run") as mock_run:
            mock_run.side_effect = [_cp(stdout=""), _cp(stdout="")]
            assert get_modified_and_untracked(Path("/repo")) == []


# =========================================================================
# 9. check_target_file_unchanged
# =========================================================================

class TestCheckTargetFileUnchanged:
    """Tests mock resolve_main_ref() to return 'origin/main' so the
    subprocess call sequence stays at 2 (fetch + rev-parse)."""

    def test_baseline_no_sha(self):
        with patch(f"{MODULE}.subprocess.run") as mock_run, \
             patch(f"{MODULE}.resolve_main_ref", return_value="origin/main"):
            mock_run.side_effect = [
                _cp(),  # fetch
                _cp(stdout="sha_abc\n"),  # rev-parse
            ]
            unchanged, sha = check_target_file_unchanged(Path("/repo"), "f.py")
            assert unchanged is True
            assert sha == "sha_abc"

    def test_same_sha_unchanged(self):
        with patch(f"{MODULE}.subprocess.run") as mock_run, \
             patch(f"{MODULE}.resolve_main_ref", return_value="origin/main"):
            mock_run.side_effect = [_cp(), _cp(stdout="sha_abc\n")]
            unchanged, sha = check_target_file_unchanged(Path("/repo"), "f.py", baseline_sha="sha_abc")
            assert unchanged is True
            assert sha == "sha_abc"

    def test_different_sha_changed(self):
        with patch(f"{MODULE}.subprocess.run") as mock_run, \
             patch(f"{MODULE}.resolve_main_ref", return_value="origin/main"):
            mock_run.side_effect = [_cp(), _cp(stdout="sha_new\n")]
            unchanged, sha = check_target_file_unchanged(Path("/repo"), "f.py", baseline_sha="sha_old")
            assert unchanged is False
            assert sha == "sha_new"

    def test_git_failure_fail_open(self):
        with patch(f"{MODULE}.subprocess.run", side_effect=subprocess.TimeoutExpired("git", 60)), \
             patch(f"{MODULE}.resolve_main_ref", return_value="origin/main"):
            unchanged, sha = check_target_file_unchanged(Path("/repo"), "f.py", baseline_sha="x")
            assert unchanged is True
            assert sha is None

    def test_rev_parse_failure_returns_true_none(self):
        with patch(f"{MODULE}.subprocess.run") as mock_run, \
             patch(f"{MODULE}.resolve_main_ref", return_value="origin/main"):
            mock_run.side_effect = [_cp(), _cp(returncode=1)]
            unchanged, sha = check_target_file_unchanged(Path("/repo"), "f.py", baseline_sha="x")
            assert unchanged is True
            assert sha is None

    def test_fetches_origin_first(self):
        with patch(f"{MODULE}.subprocess.run") as mock_run, \
             patch(f"{MODULE}.resolve_main_ref", return_value="origin/main"):
            mock_run.side_effect = [_cp(), _cp(stdout="sha\n")]
            check_target_file_unchanged(Path("/repo"), "f.py")
            fetch_cmd = mock_run.call_args_list[0][0][0]
            assert fetch_cmd == ["git", "fetch", "origin"]


# =========================================================================
# 10. revert_out_of_scope_changes_with_dirs
# =========================================================================

class TestRevertOutOfScopeChanges:
    def test_reverts_tracked_out_of_scope(self):
        porcelain = " M outside.py\n"
        with patch(f"{MODULE}.subprocess.run") as mock_run:
            mock_run.side_effect = [
                _cp(stdout=porcelain),
                _cp(),  # checkout
            ]
            result = revert_out_of_scope_changes_with_dirs(
                Path("/repo"), allowed_dirs={"pdd/"}, allowed_files=set()
            )
            assert Path("outside.py") in result

    def test_removes_untracked_out_of_scope(self, tmp_path):
        junk = tmp_path / "junk.txt"
        junk.write_text("x")
        porcelain = "?? junk.txt\n"
        with patch(f"{MODULE}.subprocess.run", return_value=_cp(stdout=porcelain)):
            result = revert_out_of_scope_changes_with_dirs(
                tmp_path, allowed_dirs={"pdd/"}, allowed_files=set()
            )
            assert Path("junk.txt") in result
            assert not junk.exists()

    def test_keeps_in_scope_by_dir_prefix(self):
        porcelain = " M pdd/module.py\n"
        with patch(f"{MODULE}.subprocess.run", return_value=_cp(stdout=porcelain)):
            result = revert_out_of_scope_changes_with_dirs(
                Path("/repo"), allowed_dirs={"pdd/"}, allowed_files=set()
            )
            assert result == []

    def test_keeps_in_scope_by_allowed_files(self, tmp_path):
        porcelain = " M setup.cfg\n"
        allowed = {(tmp_path / "setup.cfg").resolve()}
        with patch(f"{MODULE}.subprocess.run", return_value=_cp(stdout=porcelain)):
            result = revert_out_of_scope_changes_with_dirs(
                tmp_path, allowed_dirs=set(), allowed_files=allowed
            )
            assert result == []

    def test_handles_renames(self):
        porcelain = "R  old.py -> new.py\n"
        with patch(f"{MODULE}.subprocess.run") as mock_run:
            mock_run.side_effect = [
                _cp(stdout=porcelain),
                _cp(),  # checkout
            ]
            result = revert_out_of_scope_changes_with_dirs(
                Path("/repo"), allowed_dirs=set(), allowed_files=set()
            )
            assert Path("new.py") in result

    def test_handles_git_status_failure(self):
        with patch(f"{MODULE}.subprocess.run", return_value=_cp(returncode=1)):
            result = revert_out_of_scope_changes_with_dirs(
                Path("/repo"), allowed_dirs=set(), allowed_files=set()
            )
            assert result == []

    def test_handles_timeout(self):
        with patch(f"{MODULE}.subprocess.run", side_effect=subprocess.TimeoutExpired("git", 30)):
            result = revert_out_of_scope_changes_with_dirs(
                Path("/repo"), allowed_dirs=set(), allowed_files=set()
            )
            assert result == []

    def test_handles_os_error_on_remove(self, tmp_path):
        porcelain = "?? ghost.txt\n"
        with patch(f"{MODULE}.subprocess.run", return_value=_cp(stdout=porcelain)), \
             patch(f"{MODULE}.os.remove", side_effect=OSError("perm")):
            result = revert_out_of_scope_changes_with_dirs(
                tmp_path, allowed_dirs=set(), allowed_files=set()
            )
            # File couldn't be removed, so not in reverted list
            assert result == []

    def test_skips_short_lines(self):
        porcelain = "X\n M valid.py\n"
        with patch(f"{MODULE}.subprocess.run") as mock_run:
            mock_run.side_effect = [
                _cp(stdout=porcelain),
                _cp(),  # checkout for valid.py
            ]
            result = revert_out_of_scope_changes_with_dirs(
                Path("/repo"), allowed_dirs=set(), allowed_files=set()
            )
            assert Path("valid.py") in result


# =========================================================================
# 11. extract_block_marker
# =========================================================================

class TestExtractBlockMarker:
    def test_extracts_content(self):
        output = "stuff\nBEGIN_PLAN\nStep 1\nStep 2\nEND_PLAN\nmore"
        assert extract_block_marker(output, "PLAN") == "Step 1\nStep 2"

    def test_case_insensitive(self):
        output = "begin_code\nprint('hi')\nend_code"
        assert extract_block_marker(output, "CODE") == "print('hi')"

    def test_returns_empty_when_no_markers(self):
        assert extract_block_marker("no markers here", "MISSING") == ""

    def test_multiline_content(self):
        output = "BEGIN_FIX\nline1\nline2\nline3\nEND_FIX"
        result = extract_block_marker(output, "FIX")
        assert "line1" in result
        assert "line3" in result

    def test_strips_whitespace(self):
        output = "BEGIN_DATA\n   hello   \nEND_DATA"
        assert extract_block_marker(output, "DATA") == "hello"

    def test_first_pair_only(self):
        output = "BEGIN_X\nfirst\nEND_X\nBEGIN_X\nsecond\nEND_X"
        assert extract_block_marker(output, "X") == "first"

    def test_empty_content_between_markers(self):
        output = "BEGIN_EMPTY\nEND_EMPTY"
        assert extract_block_marker(output, "EMPTY") == ""

    def test_special_regex_chars_in_name(self):
        output = "BEGIN_A.B\ncontent\nEND_A.B"
        assert extract_block_marker(output, "A.B") == "content"
