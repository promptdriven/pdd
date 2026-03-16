"""Tests for the agentic E2E fix entry point."""

from __future__ import annotations

import json
import subprocess
from pathlib import Path
from unittest.mock import MagicMock, patch

import pytest

from pdd import agentic_e2e_fix


@pytest.mark.parametrize(
    ("url", "expected"),
    [
        ("https://github.com/owner/repo/issues/123", ("owner", "repo", 123)),
        ("http://github.com/owner/repo/issues/123", ("owner", "repo", 123)),
        ("github.com/owner/repo/issues/123", ("owner", "repo", 123)),
        ("https://www.github.com/owner/repo/issues/123/", ("owner", "repo", 123)),
        ("https://github.com/owner/repo/issues/123?tab=comments", ("owner", "repo", 123)),
        ("https://github.com/owner/repo/issues/123#issuecomment-1", ("owner", "repo", 123)),
    ],
)
def test_parse_github_url_valid(url: str, expected: tuple[str, str, int]) -> None:
    """Valid issue URLs should parse into owner, repo, and number."""
    assert agentic_e2e_fix._parse_github_url(url) == expected


@pytest.mark.parametrize(
    "url",
    [
        "https://github.com/owner/repo/pull/123",
        "https://github.com/owner/repo",
        "https://gitlab.com/owner/repo/issues/123",
        "not-a-url",
        "https://github.com/owner/repo/issues/not-a-number",
    ],
)
def test_parse_github_url_invalid(url: str) -> None:
    """Invalid issue URLs should be rejected."""
    assert agentic_e2e_fix._parse_github_url(url) is None


def test_extract_branch_from_comments_prefers_latest_hint() -> None:
    """The latest branch hint in the comments should win."""
    comments = "\n".join(
        [
            "Created branch 'fix-issue-11'",
            "Switched to branch 'change-issue-11'",
            "Branch: bug-issue-11",
        ]
    )

    assert agentic_e2e_fix._extract_branch_from_comments(comments) == "bug-issue-11"


def test_fetch_issue_comments_uses_pagination_and_formats_output() -> None:
    """Comment fetching should flatten paginated responses and format author markers."""
    payload = [
        [{"user": {"login": "alice"}, "body": "First comment"}],
        [{"user": {"login": "bob"}, "body": "Second comment"}],
    ]

    with patch("pdd.agentic_e2e_fix.subprocess.run") as mock_run:
        mock_run.return_value = MagicMock(stdout=json.dumps(payload))

        comments = agentic_e2e_fix._fetch_issue_comments(
            "https://api.github.com/repos/owner/repo/issues/123/comments"
        )

    assert "--- Comment by alice ---" in comments
    assert "Second comment" in comments
    command = mock_run.call_args.args[0]
    assert command[:3] == [
        "gh",
        "api",
        "https://api.github.com/repos/owner/repo/issues/123/comments",
    ]
    assert "--paginate" in command
    assert "--slurp" in command


def test_find_worktree_for_issue_walks_up_to_repo_root(
    tmp_path: Path,
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    """Worktree lookup should find `.pdd/worktrees` from a nested repo path."""
    repo_root = tmp_path / "repo"
    nested_cwd = repo_root / "src" / "pkg"
    worktree = repo_root / ".pdd" / "worktrees" / "change-issue-42"
    nested_cwd.mkdir(parents=True)
    worktree.mkdir(parents=True)
    (worktree / ".git").write_text("gitdir: mock\n", encoding="utf-8")

    monkeypatch.chdir(nested_cwd)

    assert agentic_e2e_fix._find_worktree_for_issue(42) == worktree.resolve()


def test_find_working_directory_aborts_on_branch_mismatch(tmp_path: Path) -> None:
    """A branch mismatch should abort unless `force` is set."""
    with patch("pdd.agentic_e2e_fix._find_worktree_for_issue", return_value=None), \
        patch("pdd.agentic_e2e_fix.Path.cwd", return_value=tmp_path), \
        patch("pdd.agentic_e2e_fix._get_current_branch", return_value="main"):
        cwd, warning, should_abort = agentic_e2e_fix._find_working_directory(
            99,
            "Switched to branch 'change-issue-99'",
            quiet=True,
            force=False,
        )

    assert cwd == tmp_path
    assert should_abort is True
    assert warning is not None
    assert "git checkout change-issue-99" in warning


def test_run_agentic_e2e_fix_returns_error_when_gh_is_missing() -> None:
    """The entry point should fail fast when the GitHub CLI is unavailable."""
    with patch("pdd.agentic_e2e_fix._check_gh_cli", return_value=False):
        success, message, cost, model, changed_files = agentic_e2e_fix.run_agentic_e2e_fix(
            "https://github.com/owner/repo/issues/1",
            quiet=True,
        )

    assert success is False
    assert "gh CLI not found" in message
    assert cost == 0.0
    assert model == ""
    assert changed_files == []


def test_run_agentic_e2e_fix_forwards_issue_context_and_ci_options(
    tmp_path: Path,
) -> None:
    """The entry point should assemble issue content and forward all orchestration options."""
    issue_data = {
        "title": "Fix flaky login flow",
        "body": "The retry logic fails after a timeout.",
        "user": {"login": "octocat"},
        "comments_url": "https://api.github.com/repos/owner/repo/issues/1/comments",
    }

    with patch("pdd.agentic_e2e_fix._check_gh_cli", return_value=True), \
        patch("pdd.agentic_e2e_fix._fetch_issue_data", return_value=(issue_data, None)), \
        patch(
            "pdd.agentic_e2e_fix._fetch_issue_comments",
            return_value="--- Comment by octocat ---\nSwitched to branch 'change-issue-1'",
        ), \
        patch(
            "pdd.agentic_e2e_fix._find_working_directory",
            return_value=(tmp_path, None, False),
        ), \
        patch(
            "pdd.agentic_e2e_fix.run_agentic_e2e_fix_orchestrator",
            return_value=(True, "ok", 1.5, "gpt-4.1", ["src/login.py"]),
        ) as mock_orchestrator:
        result = agentic_e2e_fix.run_agentic_e2e_fix(
            "https://github.com/owner/repo/issues/1",
            quiet=True,
            timeout_adder=3.0,
            max_cycles=2,
            resume=False,
            use_github_state=False,
            protect_tests=True,
            ci_retries=4,
            skip_ci=True,
        )

    assert result == (True, "ok", 1.5, "gpt-4.1", ["src/login.py"])
    kwargs = mock_orchestrator.call_args.kwargs
    assert kwargs["issue_number"] == 1
    assert kwargs["issue_author"] == "octocat"
    assert "Fix flaky login flow" in kwargs["issue_content"]
    assert "retry logic fails" in kwargs["issue_content"]
    assert "Switched to branch 'change-issue-1'" in kwargs["issue_content"]
    assert kwargs["cwd"] == tmp_path
    assert kwargs["timeout_adder"] == 3.0
    assert kwargs["max_cycles"] == 2
    assert kwargs["resume"] is False
    assert kwargs["use_github_state"] is False
    assert kwargs["protect_tests"] is True
    assert kwargs["ci_retries"] == 4
    assert kwargs["skip_ci"] is True


def test_run_agentic_e2e_fix_stops_on_branch_safety_abort(tmp_path: Path) -> None:
    """A branch safety abort should return a failure tuple without invoking the orchestrator."""
    issue_data = {
        "title": "Fix flaky login flow",
        "body": "The retry logic fails after a timeout.",
        "user": {"login": "octocat"},
        "comments_url": "https://api.github.com/repos/owner/repo/issues/1/comments",
    }

    with patch("pdd.agentic_e2e_fix._check_gh_cli", return_value=True), \
        patch("pdd.agentic_e2e_fix._fetch_issue_data", return_value=(issue_data, None)), \
        patch(
            "pdd.agentic_e2e_fix._fetch_issue_comments",
            return_value="Switched to branch 'change-issue-1'",
        ), \
        patch(
            "pdd.agentic_e2e_fix._find_working_directory",
            return_value=(
                tmp_path,
                "Expected branch 'change-issue-1' but current branch is 'main'.",
                True,
            ),
        ), \
        patch("pdd.agentic_e2e_fix.run_agentic_e2e_fix_orchestrator") as mock_orchestrator:
        success, message, cost, model, changed_files = agentic_e2e_fix.run_agentic_e2e_fix(
            "https://github.com/owner/repo/issues/1",
            quiet=True,
        )

    assert success is False
    assert "Expected branch" in message
    assert cost == 0.0
    assert model == ""
    assert changed_files == []
    mock_orchestrator.assert_not_called()


def test_fetch_issue_data_reports_api_errors() -> None:
    """GitHub API failures should surface as a clean error tuple."""
    with patch("pdd.agentic_e2e_fix.subprocess.run") as mock_run:
        mock_run.side_effect = subprocess.CalledProcessError(
            1,
            ["gh", "api", "repos/owner/repo/issues/1"],
            stderr="Not Found",
        )

        payload, error = agentic_e2e_fix._fetch_issue_data("owner", "repo", 1)

    assert payload is None
    assert error == "Failed to fetch issue: Not Found"
