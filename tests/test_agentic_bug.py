"""
Test Plan for pdd.agentic_bug

1. **Happy Path Execution**:
   - Verify that `run_agentic_bug` correctly parses a valid GitHub URL.
   - Verify that it calls the `gh` CLI to fetch issue data and comments.
   - Verify that it attempts to clone the repo if needed.
   - Verify that it constructs the full content string correctly.
   - Verify that it calls `run_agentic_bug_orchestrator` with the correct arguments.
   - Verify that it returns the success result from the orchestrator.

2. **Legacy Manual Mode**:
   - Verify that providing `manual_args` triggers the legacy `bug_main` logic.
   - Verify that the return values are adapted correctly from `bug_main` to the expected 5-tuple.
   - Verify error handling if `bug_main` raises an exception.

3. **Error Handling & Edge Cases**:
   - **Missing CLI**: Verify behavior when `gh` CLI is not found (mock `shutil.which` returning None).
   - **Invalid URL**: Verify behavior when an invalid GitHub URL is provided.
   - **API Failure**: Verify behavior when `gh api` fails (subprocess error).
   - **JSON Parse Error**: Verify behavior when `gh api` returns invalid JSON.
   - **Clone Failure**: Verify behavior when `git clone` fails.
   - **Orchestrator Failure**: Verify behavior when the orchestrator raises an unhandled exception.

4. **URL Parsing Logic**:
   - Test various URL formats (https, http, www, no protocol).

"""

import json
import subprocess
from pathlib import Path
from typing import Tuple, List, Any
from unittest.mock import MagicMock, patch

import pytest

# Import the module under test
from pdd.agentic_bug import run_agentic_bug


# --- Fixtures ---

@pytest.fixture
def mock_dependencies():
    """
    Mocks external dependencies:
    - shutil.which (for checking gh CLI)
    - subprocess.run (for gh api calls and git clone)
    - run_agentic_bug_orchestrator (the core logic being delegated to)
    - bug_main (for legacy mode)
    - console (to suppress output)
    """
    with patch("pdd.agentic_bug.shutil.which") as mock_which, \
         patch("pdd.agentic_bug.subprocess.run") as mock_subprocess, \
         patch("pdd.agentic_bug.run_agentic_bug_orchestrator") as mock_orchestrator, \
         patch("pdd.agentic_bug.bug_main") as mock_bug_main, \
         patch("pdd.agentic_bug.console") as mock_console:

        # Default: gh is installed
        mock_which.return_value = "/usr/bin/gh"

        # Default: subprocess returns success
        mock_subprocess.return_value = MagicMock(
            stdout='{"title": "Test Issue", "body": "Body", "user": {"login": "author"}, "comments_url": "url"}',
            returncode=0
        )

        # Default: orchestrator succeeds
        mock_orchestrator.return_value = (True, "Success", 1.0, "gpt-4", ["file.py"])

        yield mock_which, mock_subprocess, mock_orchestrator, mock_bug_main, mock_console


# --- Tests ---

def test_happy_path_execution(mock_dependencies: Tuple[Any, ...], tmp_path: Path, monkeypatch: pytest.MonkeyPatch) -> None:
    """
    Test the standard flow: valid URL -> fetch data -> clone -> run orchestrator.
    """
    _, mock_subprocess, mock_orchestrator, _, _ = mock_dependencies

    # Ensure we are in a clean directory so .git does not exist, forcing a clone attempt
    monkeypatch.chdir(tmp_path)

    # Setup mock for issue fetch and comments fetch
    issue_json = json.dumps({
        "title": "Bug in calculation",
        "body": "It fails when x=0",
        "user": {"login": "dev_user"},
        "comments_url": "https://api.github.com/repos/owner/repo/issues/1/comments"
    })

    comments_json = json.dumps([
        {"user": {"login": "helper"}, "body": "Did you try turning it off and on?"}
    ])

    # Configure subprocess to handle issue fetch, comments fetch, and git clone
    def side_effect(cmd, **kwargs):
        cmd_str = " ".join(str(x) for x in cmd)
        if "issues/1" in cmd_str and "comments" not in cmd_str:
            return MagicMock(stdout=issue_json, returncode=0)
        if "comments" in cmd_str:
            return MagicMock(stdout=comments_json, returncode=0)
        if "git clone" in cmd_str:
            return MagicMock(returncode=0)
        return MagicMock(returncode=0)

    mock_subprocess.side_effect = side_effect

    url = "https://github.com/owner/repo/issues/1"

    success, msg, cost, model, files = run_agentic_bug(url, verbose=True)

    assert success is True
    assert msg == "Success"
    assert cost == 1.0
    assert model == "gpt-4"
    assert files == ["file.py"]

    # Verify orchestrator was called with correct accumulated content
    mock_orchestrator.assert_called_once()
    call_kwargs = mock_orchestrator.call_args.kwargs
    assert call_kwargs["issue_url"] == url
    assert call_kwargs["repo_owner"] == "owner"
    assert call_kwargs["repo_name"] == "repo"
    assert call_kwargs["issue_number"] == 1
    assert "Title: Bug in calculation" in call_kwargs["issue_content"]
    assert "--- Comment by helper ---" in call_kwargs["issue_content"]


def test_gh_cli_missing(mock_dependencies: Tuple[Any, ...]) -> None:
    """
    Test that the function fails gracefully if 'gh' CLI is not found.
    """
    mock_which, _, mock_orchestrator, _, _ = mock_dependencies

    # Simulate gh not found
    mock_which.return_value = None

    success, msg, _, _, _ = run_agentic_bug("https://github.com/o/r/issues/1")

    assert success is False
    assert "gh CLI not found" in msg
    mock_orchestrator.assert_not_called()


def test_invalid_url_format(mock_dependencies: Tuple[Any, ...]) -> None:
    """
    Test that invalid URLs are rejected before making API calls.
    """
    _, mock_subprocess, mock_orchestrator, _, _ = mock_dependencies

    invalid_urls = [
        "https://gitlab.com/owner/repo/issues/1",
        "github.com/owner/repo",  # missing issue number
        "just a string"
    ]

    for url in invalid_urls:
        success, msg, _, _, _ = run_agentic_bug(url)
        assert success is False
        assert "Invalid GitHub URL" in msg
        mock_subprocess.assert_not_called()
        mock_orchestrator.assert_not_called()


def test_api_fetch_failure(mock_dependencies: Tuple[Any, ...]) -> None:
    """
    Test handling of subprocess errors when fetching issue data.
    """
    _, mock_subprocess, mock_orchestrator, _, _ = mock_dependencies

    # Simulate subprocess error (e.g., 404 Not Found or network error)
    mock_subprocess.side_effect = subprocess.CalledProcessError(
        returncode=1, cmd="gh api ...", stderr="Not Found"
    )

    success, msg, _, _, _ = run_agentic_bug("https://github.com/owner/repo/issues/1")

    assert success is False
    assert "Failed to fetch issue" in msg
    assert "Not Found" in msg
    mock_orchestrator.assert_not_called()


def test_json_decode_error(mock_dependencies: Tuple[Any, ...]) -> None:
    """
    Test handling of invalid JSON response from GitHub API.
    """
    _, mock_subprocess, mock_orchestrator, _, _ = mock_dependencies

    mock_subprocess.return_value = MagicMock(stdout="Invalid JSON", returncode=0)

    success, msg, _, _, _ = run_agentic_bug("https://github.com/owner/repo/issues/1")

    assert success is False
    assert "Failed to parse GitHub API response" in msg
    mock_orchestrator.assert_not_called()


def test_legacy_manual_mode_success(mock_dependencies: Tuple[Any, ...]) -> None:
    """
    Test that passing manual_args triggers the legacy path via bug_main.
    """
    _, _, mock_orchestrator, mock_bug_main, _ = mock_dependencies

    # Mock bug_main return: (unit_test_content, cost, model)
    mock_bug_main.return_value = ("def test_foo(): pass", 0.5, "gpt-3.5")

    manual_args = ("prompt.txt", "code.py", "prog.py", "curr.txt", "des.txt")

    success, msg, cost, model, files = run_agentic_bug(
        "ignored_url",
        manual_args=manual_args
    )

    assert success is True
    assert "Manual test generation successful" in msg
    assert cost == 0.5
    assert model == "gpt-3.5"

    # Ensure orchestrator was NOT called
    mock_orchestrator.assert_not_called()

    # Ensure bug_main WAS called with correct args
    mock_bug_main.assert_called_once()
    call_kwargs = mock_bug_main.call_args.kwargs
    assert call_kwargs["prompt_file"] == "prompt.txt"
    assert call_kwargs["code_file"] == "code.py"


def test_legacy_manual_mode_failure(mock_dependencies: Tuple[Any, ...]) -> None:
    """
    Test error handling in legacy manual mode.
    """
    _, _, _, mock_bug_main, _ = mock_dependencies

    mock_bug_main.side_effect = Exception("Something went wrong")

    manual_args = ("p", "c", "pr", "cu", "d")

    success, msg, _, _, _ = run_agentic_bug("url", manual_args=manual_args)

    assert success is False
    assert "Manual mode failed" in msg
    assert "Something went wrong" in msg


def test_orchestrator_exception_handling(mock_dependencies: Tuple[Any, ...]) -> None:
    """
    Test that exceptions raised within the orchestrator are caught and reported.
    """
    _, mock_subprocess, mock_orchestrator, _, _ = mock_dependencies

    # Ensure subprocess calls succeed so we reach orchestrator
    mock_subprocess.return_value = MagicMock(
        stdout='{"title": "T", "body": "B", "user": {"login": "u"}}',
        returncode=0
    )

    mock_orchestrator.side_effect = Exception("Unexpected crash")

    success, msg, _, _, _ = run_agentic_bug("https://github.com/owner/repo/issues/1")

    assert success is False
    assert "Orchestrator failed" in msg
    assert "Unexpected crash" in msg


def test_comments_fetch_failure_is_non_fatal(mock_dependencies: Tuple[Any, ...]) -> None:
    """
    Test that if fetching comments fails, the process continues with just the issue body.
    """
    _, mock_subprocess, mock_orchestrator, _, _ = mock_dependencies

    issue_json = json.dumps({
        "title": "Title",
        "body": "Body",
        "user": {"login": "user"},
        "comments_url": "http://api/comments"
    })

    # First call (issue) succeeds, second call (comments) fails, third (clone) succeeds
    def side_effect(cmd, **kwargs):
        cmd_str = " ".join(str(x) for x in cmd)
        if "issues/1" in cmd_str:
            return MagicMock(stdout=issue_json, returncode=0)
        if "comments" in cmd_str:
            raise subprocess.CalledProcessError(1, cmd)
        if "git clone" in cmd_str:
            return MagicMock(returncode=0)
        return MagicMock(returncode=0)

    mock_subprocess.side_effect = side_effect

    success, _, _, _, _ = run_agentic_bug("https://github.com/owner/repo/issues/1")

    assert success is True

    # Check that orchestrator was called
    mock_orchestrator.assert_called_once()
    content = mock_orchestrator.call_args.kwargs["issue_content"]
    # Should contain body but no comments section (or empty comments)
    assert "Description:\nBody" in content
    # The implementation appends "Comments:\n" even if empty string returned
    assert "Comments:\n" in content
    # But no actual comment text
    assert "--- Comment by" not in content


def test_url_parsing_variations(mock_dependencies: Tuple[Any, ...]) -> None:
    """
    Test that different valid URL formats are parsed correctly.
    """
    _, mock_subprocess, mock_orchestrator, _, _ = mock_dependencies

    # We just need the subprocess to return valid JSON so we can verify the orchestrator call args
    mock_subprocess.return_value = MagicMock(
        stdout='{"title": "T", "body": "B", "user": {"login": "u"}}',
        returncode=0
    )

    variations = [
        ("https://github.com/owner/repo/issues/123", "owner", "repo", 123),
        ("http://github.com/user/project/issues/42", "user", "project", 42),
        ("www.github.com/org/tool/issues/999", "org", "tool", 999),
        ("github.com/a/b/issues/1", "a", "b", 1)
    ]

    for url, expected_owner, expected_repo, expected_num in variations:
        mock_orchestrator.reset_mock()
        run_agentic_bug(url)

        assert mock_orchestrator.called
        kwargs = mock_orchestrator.call_args.kwargs
        assert kwargs["repo_owner"] == expected_owner
        assert kwargs["repo_name"] == expected_repo
        assert kwargs["issue_number"] == expected_num


def test_clone_failure(mock_dependencies: Tuple[Any, ...], tmp_path: Path, monkeypatch: pytest.MonkeyPatch) -> None:
    """
    Test handling of git clone failure.
    """
    _, mock_subprocess, mock_orchestrator, _, _ = mock_dependencies

    # Ensure we are in a clean directory so .git does not exist, forcing a clone attempt
    monkeypatch.chdir(tmp_path)

    issue_json = json.dumps({
        "title": "Bug", "body": "Desc", "user": {"login": "me"},
        "comments_url": "http://api/comments"
    })

    def side_effect(cmd, **kwargs):
        cmd_str = " ".join(str(x) for x in cmd)
        if "issues/1" in cmd_str:
            return MagicMock(stdout=issue_json, returncode=0)
        if "comments" in cmd_str:
            return MagicMock(stdout="[]", returncode=0)
        if "git clone" in cmd_str:
            raise subprocess.CalledProcessError(128, cmd, stderr="Permission denied")
        return MagicMock()

    mock_subprocess.side_effect = side_effect

    success, msg, _, _, _ = run_agentic_bug("https://github.com/owner/repo/issues/1")

    assert success is False
    assert "Failed to clone repository" in msg
    mock_orchestrator.assert_not_called()