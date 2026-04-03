"""E2E tests for issue #894: pdd fix agent writes to main repo instead of worktree.

These tests exercise the real _run_with_provider code path with a fake CLI
binary that reports its received environment. Unlike the unit tests (which
mock _subprocess_run), these tests let the real subprocess spawn happen and
verify GIT_WORK_TREE reaches the child process.
"""

import json
import os
import stat
import textwrap
from pathlib import Path
import pytest

from pdd.agentic_common import _run_with_provider


@pytest.fixture()
def fake_claude_cli(tmp_path: Path) -> Path:
    """Create a fake 'claude' CLI script that dumps its environment as JSON.

    The script outputs JSON in the format _parse_provider_json expects for
    the anthropic provider, embedding the received GIT_WORK_TREE value and
    actual cwd so the test can verify them.
    """
    script = tmp_path / "fake_claude"
    script.write_text(
        textwrap.dedent("""\
            #!/usr/bin/env python3
            import json, os, sys
            # Consume stdin (prompt content) to avoid broken pipe
            sys.stdin.read()
            payload = {
                "result": json.dumps({
                    "GIT_WORK_TREE": os.environ.get("GIT_WORK_TREE", ""),
                    "cwd": os.getcwd(),
                    "TERM": os.environ.get("TERM", ""),
                    "NO_COLOR": os.environ.get("NO_COLOR", ""),
                    "CI": os.environ.get("CI", ""),
                }),
                "total_cost_usd": 0.01,
            }
            print(json.dumps(payload))
        """),
        encoding="utf-8",
    )
    script.chmod(script.stat().st_mode | stat.S_IEXEC)
    return script


@pytest.fixture()
def worktree_dir(tmp_path: Path) -> Path:
    """Create a directory that mimics a git worktree structure.

    A real worktree has a .git *file* (not directory) that points back to
    the main repo. This is what causes CLI agents to resolve the wrong root.
    """
    wt = tmp_path / "fake-worktree"
    wt.mkdir()
    # Simulate a worktree .git file (pointer, not a directory)
    (wt / ".git").write_text(
        "gitdir: /some/main/repo/.git/worktrees/fake-worktree\n",
        encoding="utf-8",
    )
    return wt


@pytest.fixture()
def prompt_file(tmp_path: Path) -> Path:
    """Create a minimal prompt file for _run_with_provider."""
    p = tmp_path / ".agentic_prompt_test.txt"
    p.write_text("Test prompt for E2E issue 894", encoding="utf-8")
    return p


class TestWorktreeIsolationE2E:
    """E2E tests verifying GIT_WORK_TREE is propagated to spawned CLI agents."""

    def test_subprocess_receives_git_work_tree_matching_cwd(
        self,
        fake_claude_cli: Path,
        worktree_dir: Path,
        prompt_file: Path,
    ) -> None:
        """The spawned CLI process must receive GIT_WORK_TREE set to the worktree path.

        This is the primary E2E test for issue #894. It exercises the real
        _run_with_provider → _subprocess_run → subprocess.Popen path with a
        fake CLI binary. The fake CLI reports its environment, and we verify
        GIT_WORK_TREE was set to the worktree cwd.
        """
        success, output, cost = _run_with_provider(
            provider="anthropic",
            prompt_path=prompt_file,
            cwd=worktree_dir,
            timeout=30,
            cli_path=str(fake_claude_cli),
        )

        assert success, f"Fake CLI failed: {output}"
        assert cost > 0, "Expected non-zero cost from fake CLI"

        # Parse the environment info the subprocess reported back
        env_report = json.loads(output)
        received_git_work_tree = env_report.get("GIT_WORK_TREE", "")

        assert received_git_work_tree == str(worktree_dir), (
            f"GIT_WORK_TREE not set in subprocess environment. "
            f"Expected '{worktree_dir}', got '{received_git_work_tree!r}'. "
            f"This is the bug from issue #894: CLI agents in worktrees don't "
            f"receive GIT_WORK_TREE and follow .git pointers back to main repo."
        )

    def test_subprocess_cwd_and_git_work_tree_agree(
        self,
        fake_claude_cli: Path,
        worktree_dir: Path,
        prompt_file: Path,
    ) -> None:
        """GIT_WORK_TREE and the process cwd must point to the same worktree.

        If they diverge, git operations will use the wrong root for file
        resolution, which is the exact symptom described in issue #894.
        """
        success, output, cost = _run_with_provider(
            provider="anthropic",
            prompt_path=prompt_file,
            cwd=worktree_dir,
            timeout=30,
            cli_path=str(fake_claude_cli),
        )

        assert success, f"Fake CLI failed: {output}"

        env_report = json.loads(output)
        received_cwd = env_report.get("cwd", "")
        received_git_work_tree = env_report.get("GIT_WORK_TREE", "")

        # The process should be running in the worktree directory
        assert os.path.realpath(received_cwd) == os.path.realpath(str(worktree_dir)), (
            f"Subprocess cwd mismatch: expected '{worktree_dir}', got '{received_cwd}'"
        )

        # GIT_WORK_TREE must match cwd
        assert received_git_work_tree == str(worktree_dir), (
            f"GIT_WORK_TREE ('{received_git_work_tree}') does not match "
            f"cwd ('{received_cwd}'). Issue #894: worktree isolation is broken."
        )

    def test_git_work_tree_overrides_parent_env(
        self,
        fake_claude_cli: Path,
        worktree_dir: Path,
        prompt_file: Path,
        monkeypatch: pytest.MonkeyPatch,
    ) -> None:
        """A stale GIT_WORK_TREE from the parent process must be overwritten.

        If the parent process has GIT_WORK_TREE pointing elsewhere (e.g., to
        the main repo), _run_with_provider must replace it with the worktree
        path for proper isolation.
        """
        # Simulate a parent process with GIT_WORK_TREE pointing to main repo
        monkeypatch.setenv("GIT_WORK_TREE", "/some/main/repo")

        success, output, cost = _run_with_provider(
            provider="anthropic",
            prompt_path=prompt_file,
            cwd=worktree_dir,
            timeout=30,
            cli_path=str(fake_claude_cli),
        )

        assert success, f"Fake CLI failed: {output}"

        env_report = json.loads(output)
        received_git_work_tree = env_report.get("GIT_WORK_TREE", "")

        assert received_git_work_tree == str(worktree_dir), (
            f"GIT_WORK_TREE was not overridden. "
            f"Expected '{worktree_dir}', got '{received_git_work_tree}'. "
            f"Parent env leaked through instead of being replaced with worktree path."
        )
        assert received_git_work_tree != "/some/main/repo", (
            "GIT_WORK_TREE still points to the main repo from parent env"
        )
