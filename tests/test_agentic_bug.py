"""
Test Plan for pdd.agentic_bug

1. **Prerequisites Check**:
   - Verify that the function returns early with an error if the `gh` CLI is not installed (mock `shutil.which`).

2. **URL Parsing Validation**:
   - Verify that invalid GitHub URLs result in an early failure.
   - Verify that valid URLs (http, https, no protocol) are parsed correctly to extract owner, repo, and issue number.

3. **GitHub API Interaction**:
   - **Issue Fetching**: Verify that `gh api` is called with the correct endpoint. Handle success (JSON return) and failure (subprocess error or invalid JSON).
   - **Comments Fetching**: Verify that comments are fetched and appended to the issue content.
   - **Resilience**: Verify that if fetching comments fails, the workflow proceeds with just the issue body (soft failure for comments).

4. **Repository Cloning**:
   - Verify that `git clone` is called with the correct URL and target directory.
   - Verify that failure to clone results in an error return.

5. **Orchestrator Invocation (Happy Path)**:
   - Verify that `run_agentic_bug_orchestrator` is called with the correctly aggregated data (issue content, author, repo details, etc.).
   - Verify that the return values from the orchestrator are passed back to the caller.

6. **Error Handling**:
   - Verify that exceptions raised within the orchestrator are caught and returned as a failure tuple, not crashing the program.

Note: Z3 formal verification is not applied here as the logic is primarily procedural integration of external CLI tools and string parsing, which is better suited for unit tests with mocking.
"""

import json
import subprocess
from unittest.mock import MagicMock, patch

import pytest

# Import the module under test
from pdd.agentic_bug import run_agentic_bug


# --- Fixtures ---


@pytest.fixture
def mock_dependencies():
    """
    Mocks external dependencies:
    - shutil.which (for gh CLI check)
    - subprocess.run (for gh api and git clone)
    - run_agentic_bug_orchestrator (the core logic being wrapped)
    - console (to suppress output)
    """
    with patch("pdd.agentic_bug.shutil.which") as mock_which, \
         patch("pdd.agentic_bug.subprocess.run") as mock_run, \
         patch("pdd.agentic_bug.run_agentic_bug_orchestrator") as mock_orch, \
         patch("pdd.agentic_bug.console") as mock_console:

        # Default: gh is present
        mock_which.return_value = "/usr/bin/gh"

        # Default: subprocess calls succeed
        # We need to handle different calls (issue fetch, comments fetch, git clone)
        # This will be refined in specific tests, but setting a default return helps
        mock_run.return_value = MagicMock(
            stdout='{"title": "Test Issue", "body": "Body", "user": {"login": "tester"}, "comments_url": "url"}',
            returncode=0
        )

        # Default: Orchestrator succeeds
        mock_orch.return_value = (True, "Success", 1.0, "gpt-4", ["file.py"])

        yield mock_which, mock_run, mock_orch, mock_console


# --- Tests ---


def test_gh_cli_missing(mock_dependencies):
    """Test that the function fails gracefully if 'gh' CLI is not found."""
    mock_which, _, _, _ = mock_dependencies
    mock_which.return_value = None  # Simulate missing CLI

    success, msg, cost, _, _ = run_agentic_bug("https://github.com/o/r/issues/1")

    assert success is False
    assert "gh CLI not found" in msg
    assert cost == 0.0


def test_invalid_url_format(mock_dependencies):
    """Test that invalid URLs are rejected."""
    # Dependencies are set to defaults (gh exists), so this tests the URL parsing logic

    invalid_urls = [
        "https://gitlab.com/owner/repo/issues/1",
        "just_a_string",
        "https://github.com/owner/repo/pull/1",  # Pull request, not issue
        "https://github.com/owner/repo"
    ]

    for url in invalid_urls:
        success, msg, _, _, _ = run_agentic_bug(url)
        assert success is False
        assert "Invalid GitHub URL" in msg


def test_issue_fetch_failure(mock_dependencies):
    """Test handling of failures when fetching issue data via gh api."""
    _, mock_run, _, _ = mock_dependencies

    # Simulate subprocess error for the first call (issue fetch)
    mock_run.side_effect = subprocess.CalledProcessError(1, ["gh", "api"], stderr="Not Found")

    success, msg, _, _, _ = run_agentic_bug("https://github.com/owner/repo/issues/1")

    assert success is False
    assert "Issue not found" in msg
    assert "Not Found" in msg


def test_issue_fetch_invalid_json(mock_dependencies):
    """Test handling of invalid JSON response from gh api."""
    _, mock_run, _, _ = mock_dependencies

    # Simulate valid subprocess execution but invalid JSON output
    mock_run.return_value.stdout = "Not JSON"

    success, msg, _, _, _ = run_agentic_bug("https://github.com/owner/repo/issues/1")

    assert success is False
    assert "Failed to parse GitHub API response" in msg


def test_clone_failure(mock_dependencies):
    """Test handling of git clone failure."""
    _, mock_run, _, _ = mock_dependencies

    # Setup sequence of subprocess calls:
    # 1. Fetch Issue -> Success
    # 2. Fetch Comments -> Success (or skipped if no url)
    # 3. Git Clone -> Failure

    issue_json = json.dumps({
        "title": "Bug", "body": "Desc", "user": {"login": "me"},
        "comments_url": "http://api/comments"
    })
    comments_json = json.dumps([])

    def side_effect(cmd, **kwargs):
        cmd_str = " ".join(cmd)
        if "gh api" in cmd_str and "comments" not in cmd_str:
            return MagicMock(stdout=issue_json, returncode=0)
        if "gh api" in cmd_str and "comments" in cmd_str:
            return MagicMock(stdout=comments_json, returncode=0)
        if "git clone" in cmd_str:
            raise subprocess.CalledProcessError(128, cmd, stderr="Permission denied")
        return MagicMock()

    mock_run.side_effect = side_effect

    success, msg, _, _, _ = run_agentic_bug("https://github.com/owner/repo/issues/1")

    assert success is False
    assert "Failed to clone repository" in msg


def test_happy_path_orchestrator_call(mock_dependencies):
    """
    Verify the happy path:
    1. Parse URL
    2. Fetch Issue & Comments
    3. Clone Repo
    4. Call Orchestrator with correct context
    """
    _, mock_run, mock_orch, _ = mock_dependencies

    # Mock Data
    issue_data = {
        "title": "Critical Bug",
        "body": "It crashes.",
        "user": {"login": "bug_reporter"},
        "comments_url": "https://api.github.com/repos/owner/repo/issues/1/comments"
    }

    comments_data = [
        {"user": {"login": "dev1"}, "body": "Can you reproduce?"},
        {"user": {"login": "bug_reporter"}, "body": "Yes, always."}
    ]

    # Mock subprocess responses
    def side_effect(cmd, **kwargs):
        cmd_str = " ".join(cmd)
        if "gh api" in cmd_str and "comments" not in cmd_str:
            return MagicMock(stdout=json.dumps(issue_data), returncode=0)
        if "gh api" in cmd_str and "comments" in cmd_str:
            return MagicMock(stdout=json.dumps(comments_data), returncode=0)
        if "git clone" in cmd_str:
            return MagicMock(returncode=0)
        return MagicMock()

    mock_run.side_effect = side_effect

    # Run
    url = "https://github.com/owner/repo/issues/1"
    success, msg, cost, model, files = run_agentic_bug(url, verbose=True)

    # Assertions
    assert success is True
    assert msg == "Success"

    # Verify Orchestrator Arguments
    mock_orch.assert_called_once()
    call_kwargs = mock_orch.call_args.kwargs

    assert call_kwargs["issue_url"] == url
    assert call_kwargs["repo_owner"] == "owner"
    assert call_kwargs["repo_name"] == "repo"
    assert call_kwargs["issue_number"] == 1
    assert call_kwargs["issue_author"] == "bug_reporter"
    assert call_kwargs["issue_title"] == "Critical Bug"
    assert call_kwargs["verbose"] is True

    # Verify Content Assembly
    content = call_kwargs["issue_content"]
    assert "Title: Critical Bug" in content
    assert "Author: bug_reporter" in content
    assert "Description:\nIt crashes." in content
    assert "--- Comment by dev1 ---" in content
    assert "Can you reproduce?" in content
    assert "--- Comment by bug_reporter ---" in content


def test_comments_fetch_resilience(mock_dependencies):
    """
    Verify that if fetching comments fails, the process continues
    with just the issue body.
    """
    _, mock_run, mock_orch, _ = mock_dependencies

    issue_data = {
        "title": "Bug", "body": "Body", "user": {"login": "me"},
        "comments_url": "http://api/comments"
    }

    def side_effect(cmd, **kwargs):
        cmd_str = " ".join(cmd)
        if "gh api" in cmd_str and "comments" not in cmd_str:
            return MagicMock(stdout=json.dumps(issue_data), returncode=0)
        if "gh api" in cmd_str and "comments" in cmd_str:
            # Simulate failure fetching comments
            raise subprocess.CalledProcessError(1, cmd)
        if "git clone" in cmd_str:
            return MagicMock(returncode=0)
        return MagicMock()

    mock_run.side_effect = side_effect

    success, _, _, _, _ = run_agentic_bug("https://github.com/owner/repo/issues/1")

    assert success is True

    # Check content passed to orchestrator
    call_kwargs = mock_orch.call_args.kwargs
    content = call_kwargs["issue_content"]
    assert "Description:\nBody" in content
    # Should not have comments section populated or just empty
    assert "Comments:\n" in content or content.endswith("Comments:\n")


def test_orchestrator_exception_handling(mock_dependencies):
    """Test that exceptions raised by the orchestrator are caught gracefully."""
    _, mock_run, mock_orch, _ = mock_dependencies

    # Setup successful pre-requisites
    mock_run.return_value.stdout = json.dumps({"title": "T", "body": "B"})

    # Orchestrator raises unexpected exception
    mock_orch.side_effect = Exception("Unexpected crash")

    success, msg, _, _, _ = run_agentic_bug("https://github.com/owner/repo/issues/1")

    assert success is False
    assert "Orchestrator failed with exception" in msg
    assert "Unexpected crash" in msg


def test_url_parsing_variations(mock_dependencies):
    """Test various valid URL formats."""
    _, mock_run, mock_orch, _ = mock_dependencies

    # Mock minimal success for all calls
    mock_run.return_value.stdout = json.dumps({})

    valid_urls = [
        ("https://github.com/owner/repo/issues/1", "owner", "repo", 1),
        ("http://github.com/owner/repo/issues/2", "owner", "repo", 2),
        ("github.com/owner/repo/issues/3", "owner", "repo", 3),
        ("https://www.github.com/owner/repo/issues/4", "owner", "repo", 4),
    ]

    for url, expected_owner, expected_repo, expected_num in valid_urls:
        run_agentic_bug(url)

        # Check the last call arguments to orchestrator
        call_kwargs = mock_orch.call_args.kwargs
        assert call_kwargs["repo_owner"] == expected_owner
        assert call_kwargs["repo_name"] == expected_repo
        assert call_kwargs["issue_number"] == expected_num

        mock_orch.reset_mock()
