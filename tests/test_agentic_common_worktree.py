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
        # Structured ``--porcelain=v1 -z`` format: NUL-separated bytes.
        porcelain = b" M outside.py\x00"
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
        porcelain = b"?? junk.txt\x00"
        with patch(f"{MODULE}.subprocess.run", return_value=_cp(stdout=porcelain)):
            result = revert_out_of_scope_changes_with_dirs(
                tmp_path, allowed_dirs={"pdd/"}, allowed_files=set()
            )
            assert Path("junk.txt") in result
            assert not junk.exists()

    def test_keeps_in_scope_by_dir_prefix(self):
        porcelain = b" M pdd/module.py\x00"
        with patch(f"{MODULE}.subprocess.run", return_value=_cp(stdout=porcelain)):
            result = revert_out_of_scope_changes_with_dirs(
                Path("/repo"), allowed_dirs={"pdd/"}, allowed_files=set()
            )
            assert result == []

    def test_keeps_in_scope_by_allowed_files(self, tmp_path):
        porcelain = b" M setup.cfg\x00"
        allowed = {(tmp_path / "setup.cfg").resolve()}
        with patch(f"{MODULE}.subprocess.run", return_value=_cp(stdout=porcelain)):
            result = revert_out_of_scope_changes_with_dirs(
                tmp_path, allowed_dirs=set(), allowed_files=allowed
            )
            assert result == []

    def test_handles_renames(self):
        # ``-z`` emits the NEW path first, then the OLD path as a
        # separate NUL-terminated record (see issue #1080 fix).
        porcelain = b"R  new.py\x00old.py\x00"
        with patch(f"{MODULE}.subprocess.run") as mock_run:
            mock_run.side_effect = [
                _cp(stdout=porcelain),  # status
                _cp(),                  # reset HEAD -- ...
                _cp(),                  # checkout HEAD -- old.py
            ]
            result = revert_out_of_scope_changes_with_dirs(
                Path("/repo"), allowed_dirs=set(), allowed_files=set()
            )
            # Rename-aware guard surfaces BOTH old and new sides.
            assert Path("new.py") in result
            assert Path("old.py") in result

    def test_handles_git_status_failure(self):
        with patch(f"{MODULE}.subprocess.run", return_value=_cp(returncode=1, stderr=b"boom")):
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
        porcelain = b"?? ghost.txt\x00"
        with patch(f"{MODULE}.subprocess.run", return_value=_cp(stdout=porcelain)), \
             patch(f"{MODULE}.os.remove", side_effect=OSError("perm")):
            result = revert_out_of_scope_changes_with_dirs(
                tmp_path, allowed_dirs=set(), allowed_files=set()
            )
            # File couldn't be removed, so not in reverted list
            assert result == []

    def test_skips_short_lines(self):
        # Malformed first record (< 4 bytes) is defensively skipped by
        # the structured parser; the second record parses normally.
        porcelain = b"X\x00 M valid.py\x00"
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


# =========================================================================
# Issue #1080: rename-aware scope guard via structured -z porcelain parser
# =========================================================================


def _git_env_1080() -> dict:
    return {
        **os.environ,
        "GIT_AUTHOR_NAME": "Test",
        "GIT_AUTHOR_EMAIL": "t@t",
        "GIT_COMMITTER_NAME": "Test",
        "GIT_COMMITTER_EMAIL": "t@t",
        "GIT_CONFIG_GLOBAL": "/dev/null",
        "GIT_CONFIG_SYSTEM": "/dev/null",
    }


def _init_repo_1080(repo: Path, files: dict) -> None:
    repo.mkdir(parents=True, exist_ok=True)
    env = _git_env_1080()
    subprocess.run(["git", "init", str(repo)], check=True, capture_output=True, env=env)
    subprocess.run(["git", "-C", str(repo), "config", "user.email", "t@t"],
                   check=True, capture_output=True, env=env)
    subprocess.run(["git", "-C", str(repo), "config", "user.name", "Test"],
                   check=True, capture_output=True, env=env)
    for rel, content in files.items():
        tgt = repo / rel
        tgt.parent.mkdir(parents=True, exist_ok=True)
        tgt.write_text(content)
    subprocess.run(["git", "-C", str(repo), "add", "-A"],
                   check=True, capture_output=True, env=env)
    subprocess.run(["git", "-C", str(repo), "commit", "-m", "init"],
                   check=True, capture_output=True, env=env)


def _git_1080(repo: Path, *args: str) -> None:
    subprocess.run(["git", "-C", str(repo), *args], check=True,
                   capture_output=True, text=True, env=_git_env_1080())


class TestRevertWithDirsRename1080:
    """``revert_out_of_scope_changes_with_dirs`` must consider BOTH old
    and new sides of a rename via ``parse_porcelain_z``, and must never
    construct a fake ``"old -> new"`` literal path.
    """

    def test_reverts_when_old_side_is_out_of_scope(self, tmp_path):
        """Rename from out-of-scope old path into an in-scope new path
        is still out-of-scope — the guard must undo it."""
        _init_repo_1080(tmp_path, {
            "scripts/external.py": "external original\n",
            "pdd/in_scope.py": "in_scope\n",
        })
        _git_1080(tmp_path, "mv", "scripts/external.py", "pdd/legit.py")

        result = revert_out_of_scope_changes_with_dirs(
            tmp_path,
            allowed_dirs={"pdd/"},
            allowed_files=set(),
        )

        assert (tmp_path / "scripts" / "external.py").exists(), (
            "Out-of-scope old side was not restored: new-side-only parsing"
        )
        assert not (tmp_path / "pdd" / "legit.py").exists(), (
            "Out-of-scope rename survived in pdd/legit.py"
        )
        assert result, (
            f"Expected non-empty revert list, got {result!r} — guard "
            "did not detect the out-of-scope old side"
        )

    def test_handles_paths_with_arrow_substring(self, tmp_path):
        """An out-of-scope untracked path with ``" -> "`` in its name
        must be removed by the guard. The buggy ``split(' -> ')``
        truncates the name and ``os.remove`` fails on the wrong path."""
        _init_repo_1080(tmp_path, {"pdd/anchor.py": "x\n"})
        _git_1080(tmp_path, "config", "core.quotePath", "false")
        weird = tmp_path / "bogus -> file.txt"
        weird.write_text("junk\n")

        result = revert_out_of_scope_changes_with_dirs(
            tmp_path,
            allowed_dirs={"pdd/"},
            allowed_files=set(),
        )

        assert not weird.exists(), (
            "Out-of-scope untracked file with ' -> ' in name not removed"
        )
        assert any(
            str(p).endswith("bogus -> file.txt") for p in result
        ), f"Reverted list missing real path: {result!r}"


# =========================================================================
# Issue #1123: pre-snapshot skip in revert_out_of_scope_changes_with_dirs
#
# Round 3 contract: pre-snapshot is a Mapping[rel_path,
# (porcelain_status, content_sha256_hex_or_None)]. The helper skips an
# entry only when BOTH the status AND the content hash match. Status-only
# matches with a changed hash (e.g. Step 8.5 staged ` M`, Step 9 modified
# the same file again) MUST fall through to the allowlist enforcement.
# =========================================================================


def test_revert_out_of_scope_changes_with_dirs_pre_snapshot_skips_when_status_and_hash_match(
    tmp_path,
):
    """When the caller supplies a pre-snapshot, entries whose
    ``(status, content_sha256)`` tuple matches the baseline must be skipped.
    Only NEW, status-CHANGED, or content-CHANGED entries are subject to the
    allowlist enforcement.

    This is how the Step 9 scope guard distinguishes Step 8.5 drift-heal
    mutations (in the snapshot) from Step 9 LLM mutations (not in the
    snapshot or with a different status/hash).
    """
    # Two out-of-scope entries: one in the snapshot (heal artifact),
    # one fresh (Step 9 leak). Only the fresh one should be reverted.
    import hashlib

    meta_dir = tmp_path / ".pdd" / "meta"
    meta_dir.mkdir(parents=True)
    snapshotted = meta_dir / "x.json"
    snapshotted.write_text("{}")
    snapshotted_hash = hashlib.sha256(snapshotted.read_bytes()).hexdigest()

    leak_dir = tmp_path / "tests"
    leak_dir.mkdir()
    (leak_dir / "leak.py").write_text("x")

    porcelain = b"?? .pdd/meta/x.json\x00?? tests/leak.py\x00"
    pre_snapshot = {".pdd/meta/x.json": ("??", snapshotted_hash)}
    with patch(f"{MODULE}.subprocess.run") as mock_run, \
         patch(f"{MODULE}.os.remove") as mock_remove:
        mock_run.side_effect = [_cp(stdout=porcelain)]
        result = revert_out_of_scope_changes_with_dirs(
            tmp_path,
            allowed_dirs=set(),
            allowed_files=set(),
            pre_snapshot=pre_snapshot,
        )
        # The snapshotted entry is skipped; only the new leak is removed.
        assert result == [Path("tests/leak.py")]
        mock_remove.assert_called_once()
        removed_arg = mock_remove.call_args[0][0]
        assert removed_arg.endswith("tests/leak.py")


def test_revert_out_of_scope_changes_with_dirs_pre_snapshot_does_not_skip_when_content_changed(
    tmp_path,
):
    """Status matches but the file's content was modified after the
    snapshot was taken: this is a Step-9 mutation on top of Step-8.5's
    work and MUST be enforced against the allowlist."""
    # Snapshot recorded the file at some prior hash; the file on disk
    # now has different content (Step 9 modified it).
    outside = tmp_path / "outside.py"
    outside.write_text("step9 modified me\n")

    porcelain = b" M outside.py\x00"
    pre_snapshot = {"outside.py": (" M", "deadbeef" * 8)}  # status matches, hash does not
    with patch(f"{MODULE}.subprocess.run") as mock_run:
        mock_run.side_effect = [
            _cp(stdout=porcelain),
            _cp(),  # checkout
        ]
        result = revert_out_of_scope_changes_with_dirs(
            tmp_path,
            allowed_dirs={"pdd/"},
            allowed_files=set(),
            pre_snapshot=pre_snapshot,
        )
        assert Path("outside.py") in result


def test_revert_out_of_scope_changes_with_dirs_reverts_when_status_changed(tmp_path):
    """A snapshotted entry whose status CHANGED since the snapshot is a
    new mutation and must still be subject to the allowlist."""
    # In the snapshot the file was ``A`` (added/untracked-staged) with
    # some hash; post-snapshot git reports ``M`` — Step 9 modified the
    # file further. Even if content matched (it doesn't here), the
    # status difference alone forces enforcement.
    outside = tmp_path / "outside.py"
    outside.write_text("modified content\n")

    porcelain = b" M outside.py\x00"
    pre_snapshot = {"outside.py": ("A ", "deadbeef" * 8)}
    with patch(f"{MODULE}.subprocess.run") as mock_run:
        mock_run.side_effect = [
            _cp(stdout=porcelain),
            _cp(),  # checkout
        ]
        result = revert_out_of_scope_changes_with_dirs(
            tmp_path,
            allowed_dirs={"pdd/"},
            allowed_files=set(),
            pre_snapshot=pre_snapshot,
        )
        assert Path("outside.py") in result


def test_revert_out_of_scope_changes_with_dirs_existing_two_arg_callers_unchanged():
    """The new params are optional with safe defaults. Existing two-arg
    call sites must continue to enforce the allowlist over every entry."""
    porcelain = b"?? leak.py\x00"
    with patch(f"{MODULE}.subprocess.run", return_value=_cp(stdout=porcelain)), \
         patch(f"{MODULE}.os.remove") as mock_remove:
        result = revert_out_of_scope_changes_with_dirs(
            Path("/repo"), allowed_dirs=set(), allowed_files=set()
        )
        assert Path("leak.py") in result
        mock_remove.assert_called_once()


# -------------------------------------------------------------------------
# Round-3 deletion detection: pre-snapshot files absent from post-status
# must be treated as out-of-scope mutations unless they're allowlisted.
# Tracked deletions restore via `git checkout HEAD --`; untracked
# deletions cannot be auto-restored and are surfaced as violations so
# the orchestrator stops the workflow.
# -------------------------------------------------------------------------


def test_revert_out_of_scope_changes_with_dirs_detects_deletion_of_tracked_pre_snapshot_file(
    tmp_path,
):
    """A tracked file present in pre_snapshot but absent from post-status
    was deleted by Step 9. The guard must restore it via
    ``git checkout HEAD -- <file>`` and report it in the reverted list."""
    # Post status: empty (no entries) — the Step-8.5-modified file was
    # deleted by Step 9 and no other changes remain.
    porcelain = b""
    pre_snapshot = {"foo.txt": (" M", "deadbeef" * 8)}
    with patch(f"{MODULE}.subprocess.run") as mock_run:
        mock_run.side_effect = [
            _cp(stdout=porcelain),  # status
            _cp(),                  # checkout HEAD -- foo.txt
        ]
        result = revert_out_of_scope_changes_with_dirs(
            tmp_path,
            allowed_dirs=set(),
            allowed_files=set(),
            pre_snapshot=pre_snapshot,
        )
        assert Path("foo.txt") in result
        # Second call was the restore.
        assert mock_run.call_count == 2
        restore_cmd = mock_run.call_args_list[1][0][0]
        assert restore_cmd[:4] == ["git", "checkout", "HEAD", "--"]
        assert "foo.txt" in restore_cmd


def test_revert_out_of_scope_changes_with_dirs_flags_untracked_deletion_unrecoverable(
    tmp_path,
):
    """An untracked file (pre-status ``??``) present in pre_snapshot but
    absent from post-status was deleted by Step 9. We have no stored
    content so we cannot auto-restore. The guard must still add the path
    to the reverted list so the orchestrator's SCOPE_VIOLATION path
    fires; Step 8.5 is idempotent and will recreate the file on the next
    invocation."""
    porcelain = b""
    pre_snapshot = {".pdd/meta/x.json": ("??", "abc123")}
    with patch(f"{MODULE}.subprocess.run") as mock_run:
        mock_run.side_effect = [_cp(stdout=porcelain)]  # only status, no restore
        result = revert_out_of_scope_changes_with_dirs(
            tmp_path,
            allowed_dirs=set(),
            allowed_files=set(),
            pre_snapshot=pre_snapshot,
        )
        # Reverted list MUST include the deleted path so the workflow stops.
        assert Path(".pdd/meta/x.json") in result
        # No git restore was attempted (untracked: no HEAD content).
        assert mock_run.call_count == 1


# -------------------------------------------------------------------------
# Round-4 content-revert detection: a pre-snapshot file present on disk but
# absent from post-status means it is now clean vs HEAD. If the snapshot
# said it was dirty (modified or untracked), Step 9 has overwritten the
# Step-8.5 mutation back to HEAD content — unrecoverable because we have
# no stored pre-content. The helper must flag it as a scope violation so
# the orchestrator's SCOPE_VIOLATION path fires and resume re-runs Step 8.5.
# -------------------------------------------------------------------------


def test_revert_out_of_scope_changes_with_dirs_flags_step9_revert_of_tracked_pre_snapshot_to_head(
    tmp_path,
):
    """Pre snapshot has `architecture.json` with ` M` and Step-8.5-time
    content hash. Step 9 writes the file back to its HEAD bytes, so the
    post `git status` no longer lists it (clean vs HEAD). The main loop
    sees nothing, and round-3's deletion pass would also miss it (the
    file still exists on disk). Round-4 must surface it as a reverted
    out-of-scope path so the orchestrator stops the workflow.
    """
    arch = tmp_path / "architecture.json"
    arch.write_text('{"modules": []}\n')  # back to HEAD content
    pre_snapshot = {"architecture.json": (" M", "deadbeef" * 8)}  # snapshot hash != current
    porcelain = b""  # post-status is empty: file is clean
    with patch(f"{MODULE}.subprocess.run") as mock_run:
        mock_run.side_effect = [_cp(stdout=porcelain)]  # only status, no restore attempt
        result = revert_out_of_scope_changes_with_dirs(
            tmp_path,
            allowed_dirs=set(),
            allowed_files=set(),
            pre_snapshot=pre_snapshot,
        )
        # Path must surface as reverted so SCOPE_VIOLATION fires.
        assert Path("architecture.json") in result
        # No git restore attempted — we have no pre content to re-apply.
        assert mock_run.call_count == 1


def test_revert_out_of_scope_changes_with_dirs_skips_in_scope_step9_revert_of_pre_snapshot(
    tmp_path,
):
    """If the pre-snapshot path is in scope, a Step-9 revert to HEAD is
    allowed (in-scope mutations are by definition fine). The helper must
    NOT flag it as a violation."""
    prompt_dir = tmp_path / "prompts"
    prompt_dir.mkdir()
    (prompt_dir / "foo.prompt").write_text("HEAD content\n")
    pre_snapshot = {"prompts/foo.prompt": (" M", "cafebabe" * 8)}
    porcelain = b""
    with patch(f"{MODULE}.subprocess.run") as mock_run:
        mock_run.side_effect = [_cp(stdout=porcelain)]
        result = revert_out_of_scope_changes_with_dirs(
            tmp_path,
            allowed_dirs={"prompts/"},
            allowed_files=set(),
            pre_snapshot=pre_snapshot,
        )
        # In-scope: not flagged.
        assert result == []


def test_revert_out_of_scope_changes_with_dirs_skips_empty_status_with_matching_hash(
    tmp_path,
):
    """Edge case: pre-snapshot somehow recorded a path with empty status and
    a hash equal to the current on-disk hash. That means the file was
    already clean at snapshot time and is still clean now — a true no-op,
    not a Step-9-induced revert. The helper must skip it.
    """
    import hashlib

    target = tmp_path / "noop.txt"
    target.write_text("same bytes\n")
    current_hash = hashlib.sha256(target.read_bytes()).hexdigest()
    pre_snapshot = {"noop.txt": ("", current_hash)}
    porcelain = b""
    with patch(f"{MODULE}.subprocess.run") as mock_run:
        mock_run.side_effect = [_cp(stdout=porcelain)]
        result = revert_out_of_scope_changes_with_dirs(
            tmp_path,
            allowed_dirs=set(),
            allowed_files=set(),
            pre_snapshot=pre_snapshot,
        )
        assert result == []


# -------------------------------------------------------------------------
# Round-3 strict mode: internal failures raise instead of returning [].
# Default (strict=False) preserves existing silent-fail semantics for
# callers like e2e_fix.
# -------------------------------------------------------------------------


def test_revert_out_of_scope_changes_with_dirs_strict_raises_on_git_status_failure():
    """``strict=True`` causes a non-zero ``git status`` to raise OSError
    instead of silently returning ``[]``. Default ``strict=False`` keeps
    the silent-fail behavior."""
    # Non-zero return:
    with patch(f"{MODULE}.subprocess.run", return_value=_cp(returncode=1, stderr=b"boom")):
        # Default: silent fail.
        result = revert_out_of_scope_changes_with_dirs(
            Path("/repo"), allowed_dirs=set(), allowed_files=set()
        )
        assert result == []
        # Strict: raises.
        with pytest.raises(OSError):
            revert_out_of_scope_changes_with_dirs(
                Path("/repo"),
                allowed_dirs=set(),
                allowed_files=set(),
                strict=True,
            )


def test_revert_out_of_scope_changes_with_dirs_strict_raises_on_git_status_timeout():
    """``strict=True`` propagates a subprocess timeout instead of returning ``[]``."""
    with patch(f"{MODULE}.subprocess.run", side_effect=subprocess.TimeoutExpired("git", 30)):
        # Default: silent fail.
        result = revert_out_of_scope_changes_with_dirs(
            Path("/repo"), allowed_dirs=set(), allowed_files=set()
        )
        assert result == []
        # Strict: raises.
        with pytest.raises(subprocess.TimeoutExpired):
            revert_out_of_scope_changes_with_dirs(
                Path("/repo"),
                allowed_dirs=set(),
                allowed_files=set(),
                strict=True,
            )


def test_revert_out_of_scope_changes_with_dirs_strict_raises_on_remove_failure(tmp_path):
    """``strict=True`` causes an ``os.remove`` PermissionError to propagate."""
    junk = tmp_path / "junk.txt"
    junk.write_text("x")
    porcelain = b"?? junk.txt\x00"
    with patch(f"{MODULE}.subprocess.run", return_value=_cp(stdout=porcelain)), \
         patch(f"{MODULE}.os.remove", side_effect=PermissionError("denied")):
        # Default: silent fail (returns [] because remove failed).
        result = revert_out_of_scope_changes_with_dirs(
            tmp_path, allowed_dirs=set(), allowed_files=set()
        )
        assert result == []
        # Strict: raises.
        with pytest.raises(PermissionError):
            revert_out_of_scope_changes_with_dirs(
                tmp_path,
                allowed_dirs=set(),
                allowed_files=set(),
                strict=True,
            )


def test_revert_out_of_scope_changes_with_dirs_reverts_staged_addition(tmp_path):
    """Regression for round-8: staged new out-of-scope files (A ) must be
    unstaged and removed rather than hitting ``git checkout HEAD --`` which
    fails for paths not in HEAD."""
    # Set up a real git repo so git reset/unlink actually work.
    subprocess.run(["git", "init"], cwd=str(tmp_path), capture_output=True, check=True)
    subprocess.run(
        ["git", "commit", "--allow-empty", "-m", "init"],
        cwd=str(tmp_path),
        capture_output=True,
        check=True,
        env={**__import__("os").environ, "GIT_AUTHOR_NAME": "t", "GIT_AUTHOR_EMAIL": "t@t",
             "GIT_COMMITTER_NAME": "t", "GIT_COMMITTER_EMAIL": "t@t"},
    )
    leak = tmp_path / "tests" / "leak.py"
    leak.parent.mkdir(parents=True, exist_ok=True)
    leak.write_text("# out of scope\n")
    subprocess.run(["git", "add", str(leak)], cwd=str(tmp_path), check=True, capture_output=True)

    # Confirm it is staged as A  before the guard runs.
    status = subprocess.run(
        ["git", "status", "--porcelain=v1", "-z", "-u"],
        cwd=str(tmp_path),
        capture_output=True,
        check=True,
    ).stdout
    assert b"A  tests/leak.py" in status or b"A tests/leak.py" in status

    result = revert_out_of_scope_changes_with_dirs(
        tmp_path, allowed_dirs=set(), allowed_files=set(), strict=True
    )

    assert Path("tests/leak.py") in result
    assert not leak.exists()
    # Nothing staged after revert.
    post_status = subprocess.run(
        ["git", "status", "--porcelain=v1", "-z", "-u"],
        cwd=str(tmp_path),
        capture_output=True,
        check=True,
    ).stdout
    assert b"leak.py" not in post_status


def test_revert_out_of_scope_changes_with_dirs_reverts_staged_addition_am(tmp_path):
    """AM (staged add + unstaged modification) is also a staged addition and
    must be handled via reset+remove, not git checkout HEAD --."""
    import os as _os
    subprocess.run(["git", "init"], cwd=str(tmp_path), capture_output=True, check=True)
    subprocess.run(
        ["git", "commit", "--allow-empty", "-m", "init"],
        cwd=str(tmp_path),
        capture_output=True,
        check=True,
        env={**_os.environ, "GIT_AUTHOR_NAME": "t", "GIT_AUTHOR_EMAIL": "t@t",
             "GIT_COMMITTER_NAME": "t", "GIT_COMMITTER_EMAIL": "t@t"},
    )
    leak = tmp_path / "out.py"
    leak.write_text("# v1\n")
    subprocess.run(["git", "add", str(leak)], cwd=str(tmp_path), check=True, capture_output=True)
    # Modify after staging to produce AM status.
    leak.write_text("# v2\n")

    result = revert_out_of_scope_changes_with_dirs(
        tmp_path, allowed_dirs=set(), allowed_files=set(), strict=True
    )

    assert Path("out.py") in result
    assert not leak.exists()


def test_revert_out_of_scope_changes_with_dirs_staged_addition_reset_failure_strict(tmp_path):
    """If git reset fails for a staged addition under strict=True, raise and
    do NOT unlink (the blob may still be staged — unlinking would leave the
    index pointing at a missing file rather than actually reverting the add)."""
    porcelain = b"A  leak.py\x00"

    def fake_run(cmd, **kwargs):
        if cmd[:2] == ["git", "reset"]:
            return _cp(returncode=1, stderr=b"reset failed")
        return _cp(stdout=porcelain)

    with patch(f"{MODULE}.subprocess.run", side_effect=fake_run):
        with pytest.raises(OSError, match="git reset HEAD"):
            revert_out_of_scope_changes_with_dirs(
                tmp_path, allowed_dirs=set(), allowed_files=set(), strict=True
            )


def test_revert_out_of_scope_changes_with_dirs_copy_reset_failure_strict(tmp_path):
    """Same reset-return check applies to copy-destination revert."""
    porcelain = b"C100 src.py\x00dest.py\x00"

    def fake_run(cmd, **kwargs):
        if cmd[:2] == ["git", "reset"]:
            return _cp(returncode=1, stderr=b"reset failed")
        return _cp(stdout=porcelain)

    with patch(f"{MODULE}.subprocess.run", side_effect=fake_run):
        with pytest.raises(OSError, match="git reset HEAD"):
            revert_out_of_scope_changes_with_dirs(
                tmp_path, allowed_dirs=set(), allowed_files=set(), strict=True
            )


def test_revert_out_of_scope_changes_with_dirs_rename_reset_failure_strict(tmp_path):
    """If git reset fails for a rename under strict=True, raise immediately
    and do NOT proceed to checkout/unlink — leaves the index consistent."""
    porcelain = b"R100 old.py\x00new.py\x00"

    def fake_run(cmd, **kwargs):
        if cmd[:2] == ["git", "reset"]:
            return _cp(returncode=1, stderr=b"reset failed")
        return _cp(stdout=porcelain)

    with patch(f"{MODULE}.subprocess.run", side_effect=fake_run):
        with pytest.raises(OSError, match="git reset HEAD"):
            revert_out_of_scope_changes_with_dirs(
                tmp_path, allowed_dirs=set(), allowed_files=set(), strict=True
            )
