"""Example usage of pdd.agentic_common_worktree module.

Demonstrates all 11 public functions with mocked git subprocess calls
so the example runs standalone without a real git repository.
"""
from __future__ import annotations

import os
import sys

sys.path.insert(0, os.path.join(os.path.dirname(__file__), ".."))

import subprocess
from pathlib import Path
from tempfile import TemporaryDirectory
from unittest.mock import MagicMock, patch, call

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


def _make_completed(returncode: int = 0, stdout: str = "", stderr: str = "") -> subprocess.CompletedProcess:
    """Helper to build a CompletedProcess."""
    return subprocess.CompletedProcess(args=["git"], returncode=returncode, stdout=stdout, stderr=stderr)


def example_get_git_root() -> None:
    """Show get_git_root returning the repo root path."""
    print("=== get_git_root ===")
    with patch("pdd.agentic_common_worktree.subprocess.run") as mock_run:
        mock_run.return_value = _make_completed(stdout="/home/user/repo\n")
        result = get_git_root(Path("/home/user/repo/subdir"))
    print(f"Git root: {result}")
    print()

    # Failure case
    with patch("pdd.agentic_common_worktree.subprocess.run") as mock_run:
        mock_run.return_value = _make_completed(returncode=128, stderr="not a git repo")
        result = get_git_root(Path("/tmp/not-a-repo"))
    print(f"Non-repo returns: {result}")
    print()


def example_worktree_exists() -> None:
    """Show worktree_exists checking porcelain output."""
    print("=== worktree_exists ===")
    porcelain_output = (
        "worktree /home/user/repo\n"
        "HEAD abc123\n"
        "branch refs/heads/main\n"
        "\n"
        "worktree /home/user/repo/.pdd/worktrees/fix-issue-42\n"
        "HEAD def456\n"
        "branch refs/heads/fix/issue-42\n"
        "\n"
    )
    with patch("pdd.agentic_common_worktree.subprocess.run") as mock_run:
        # First call: get_git_root, second call: worktree list
        mock_run.side_effect = [
            _make_completed(stdout="/home/user/repo\n"),
            _make_completed(stdout=porcelain_output),
        ]
        found = worktree_exists(
            Path("/home/user/repo"),
            Path("/home/user/repo/.pdd/worktrees/fix-issue-42"),
        )
    print(f"Worktree exists: {found}")
    print()


def example_branch_exists() -> None:
    """Show branch_exists checking a local branch."""
    print("=== branch_exists ===")
    with patch("pdd.agentic_common_worktree.subprocess.run") as mock_run:
        mock_run.return_value = _make_completed(returncode=0)
        exists = branch_exists(Path("/home/user/repo"), "fix/issue-42")
    print(f"Branch 'fix/issue-42' exists: {exists}")

    with patch("pdd.agentic_common_worktree.subprocess.run") as mock_run:
        mock_run.return_value = _make_completed(returncode=1)
        exists = branch_exists(Path("/home/user/repo"), "no-such-branch")
    print(f"Branch 'no-such-branch' exists: {exists}")
    print()


def example_remove_worktree() -> None:
    """Show remove_worktree success and failure."""
    print("=== remove_worktree ===")
    with patch("pdd.agentic_common_worktree.subprocess.run") as mock_run:
        mock_run.return_value = _make_completed(returncode=0)
        ok, err = remove_worktree(Path("/home/user/repo"), Path("/home/user/repo/.pdd/worktrees/fix-issue-42"))
    print(f"Success: {ok}, Error: '{err}'")

    with patch("pdd.agentic_common_worktree.subprocess.run") as mock_run:
        mock_run.return_value = _make_completed(returncode=1, stderr="not a valid worktree")
        ok, err = remove_worktree(Path("/home/user/repo"), Path("/tmp/bad"))
    print(f"Success: {ok}, Error: '{err}'")
    print()


def example_delete_branch() -> None:
    """Show delete_branch success and failure."""
    print("=== delete_branch ===")
    with patch("pdd.agentic_common_worktree.subprocess.run") as mock_run:
        mock_run.return_value = _make_completed(returncode=0, stdout="Deleted branch fix/issue-42\n")
        ok, err = delete_branch(Path("/repo"), "fix/issue-42")
    print(f"Deleted: {ok}, Error: '{err}'")
    print()


def example_resolve_main_ref() -> None:
    """Show resolve_main_ref trying refs in order."""
    print("=== resolve_main_ref ===")
    with patch("pdd.agentic_common_worktree.subprocess.run") as mock_run:
        # origin/main fails, origin/master succeeds
        mock_run.side_effect = [
            _make_completed(returncode=1),
            _make_completed(returncode=0, stdout="abc123def456\n"),
        ]
        ref = resolve_main_ref(Path("/home/user/repo"))
    print(f"Resolved main ref: {ref}")

    # Fallback to HEAD when nothing resolves
    with patch("pdd.agentic_common_worktree.subprocess.run") as mock_run:
        mock_run.return_value = _make_completed(returncode=1)
        ref = resolve_main_ref(Path("/home/user/repo"))
    print(f"Fallback ref: {ref}")
    print()


def example_setup_worktree() -> None:
    """Show setup_worktree creating a worktree for an issue."""
    print("=== setup_worktree ===")
    with TemporaryDirectory() as tmp:
        tmp_path = Path(tmp)
        git_root = tmp_path / "repo"
        git_root.mkdir()

        with patch("pdd.agentic_common_worktree.get_git_root", return_value=git_root), \
             patch("pdd.agentic_common_worktree.worktree_exists", return_value=False), \
             patch("pdd.agentic_common_worktree.branch_exists", return_value=False), \
             patch("pdd.agentic_common_worktree.resolve_main_ref", return_value="abc123"), \
             patch("pdd.agentic_common_worktree.subprocess.run") as mock_run:
            mock_run.return_value = _make_completed(returncode=0)
            wt_path, err = setup_worktree(git_root, 42, quiet=False, branch_prefix="change", worktree_prefix="change")

        print(f"Worktree path: {wt_path}")
        print(f"Error: {err}")
        print(f"Expected dir name: change-issue-42")
    print()


def example_get_modified_and_untracked() -> None:
    """Show get_modified_and_untracked returning file lists."""
    print("=== get_modified_and_untracked ===")
    with patch("pdd.agentic_common_worktree.subprocess.run") as mock_run:
        mock_run.side_effect = [
            _make_completed(stdout="src/main.py\nsrc/utils.py\n"),
            _make_completed(stdout="new_file.txt\n"),
        ]
        files = get_modified_and_untracked(Path("/repo"))
    print(f"Modified & untracked files: {files}")
    print()


def example_check_target_file_unchanged() -> None:
    """Show check_target_file_unchanged for baseline and comparison."""
    print("=== check_target_file_unchanged ===")
    # Establish baseline (no baseline_sha)
    with patch("pdd.agentic_common_worktree.subprocess.run") as mock_run:
        mock_run.side_effect = [
            _make_completed(returncode=0),  # git fetch
            _make_completed(returncode=0, stdout="sha_abc123\n"),  # rev-parse
        ]
        unchanged, sha = check_target_file_unchanged(Path("/repo"), "pdd/module.py")
    print(f"Baseline — unchanged: {unchanged}, sha: {sha}")

    # Compare with same SHA (unchanged)
    with patch("pdd.agentic_common_worktree.subprocess.run") as mock_run:
        mock_run.side_effect = [
            _make_completed(returncode=0),  # git fetch
            _make_completed(returncode=0, stdout="sha_abc123\n"),  # rev-parse
        ]
        unchanged, sha = check_target_file_unchanged(Path("/repo"), "pdd/module.py", baseline_sha="sha_abc123")
    print(f"Same SHA — unchanged: {unchanged}, sha: {sha}")

    # Compare with different SHA (changed)
    with patch("pdd.agentic_common_worktree.subprocess.run") as mock_run:
        mock_run.side_effect = [
            _make_completed(returncode=0),  # git fetch
            _make_completed(returncode=0, stdout="sha_def456\n"),  # rev-parse
        ]
        unchanged, sha = check_target_file_unchanged(Path("/repo"), "pdd/module.py", baseline_sha="sha_abc123")
    print(f"Different SHA — unchanged: {unchanged}, sha: {sha}")
    print()


def example_revert_out_of_scope_changes() -> None:
    """Show revert_out_of_scope_changes_with_dirs reverting out-of-scope files."""
    print("=== revert_out_of_scope_changes_with_dirs ===")
    with TemporaryDirectory() as tmp:
        cwd = Path(tmp)
        # Create an untracked out-of-scope file
        out_of_scope = cwd / "random.txt"
        out_of_scope.write_text("junk")

        porcelain = (
            " M pdd/module.py\n"       # in-scope (allowed dir)
            " M setup.cfg\n"            # out-of-scope tracked
            "?? random.txt\n"           # out-of-scope untracked
        )

        with patch("pdd.agentic_common_worktree.subprocess.run") as mock_run:
            mock_run.side_effect = [
                _make_completed(returncode=0, stdout=porcelain),  # git status
                _make_completed(returncode=0),                     # git checkout for setup.cfg
            ]
            reverted = revert_out_of_scope_changes_with_dirs(
                cwd,
                allowed_dirs={"pdd/"},
                allowed_files=set(),
            )
    print(f"Reverted/removed paths: {[str(p) for p in reverted]}")
    print()


def example_extract_block_marker() -> None:
    """Show extract_block_marker parsing agent output."""
    print("=== extract_block_marker ===")
    agent_output = """
Some preamble text...
BEGIN_PLAN
Step 1: Analyze the bug
Step 2: Write the fix
Step 3: Run tests
END_PLAN
Some trailing text...
"""
    plan = extract_block_marker(agent_output, "PLAN")
    print(f"Extracted plan:\n{plan}")
    print()

    # Case-insensitive matching
    mixed_case = "begin_code\nprint('hello')\nend_code"
    code = extract_block_marker(mixed_case, "CODE")
    print(f"Case-insensitive extract: {code}")
    print()

    # Missing markers
    empty = extract_block_marker("no markers here", "MISSING")
    print(f"Missing markers returns: '{empty}'")
    print()


def main() -> None:
    """Run all examples."""
    example_get_git_root()
    example_worktree_exists()
    example_branch_exists()
    example_remove_worktree()
    example_delete_branch()
    example_resolve_main_ref()
    example_setup_worktree()
    example_get_modified_and_untracked()
    example_check_target_file_unchanged()
    example_revert_out_of_scope_changes()
    example_extract_block_marker()
    print("All examples completed successfully.")


if __name__ == "__main__":
    main()
