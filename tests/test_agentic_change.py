"""
Test Plan for pdd.agentic_change

1. **Dependency Check**:
   - Verify that the function returns early with an error if the `gh` CLI is not installed.

2. **URL Parsing**:
   - Verify that invalid GitHub URLs result in an early exit with an error message.
   - Verify that valid URLs (standard, www, no-protocol) are parsed correctly.

3. **API Interaction (Issue Fetching)**:
   - Verify handling of `gh api` failures (non-zero return code).
   - Verify handling of invalid JSON responses from the API.
   - Verify correct extraction of issue metadata (title, body, author, comments_url).

4. **API Interaction (Comments Fetching)**:
   - Verify that comments are fetched and appended to the issue content.
   - Verify that failure to fetch comments (or invalid JSON) does not crash the workflow, but logs a warning and proceeds with just the issue body.

5. **Repository Setup**:
   - **Scenario A (Clone)**: Verify that if the current directory is not the target repository, a temporary directory is created and `gh repo clone` is executed.
   - **Scenario B (Current Dir)**: Verify that if the current directory matches the target repository (via `git remote`), no cloning occurs and the current directory is used.

6. **Orchestrator Invocation**:
   - Verify that `run_agentic_change_orchestrator` is called with the correctly aggregated arguments (content, paths, metadata).
   - Verify that the return values from the orchestrator are passed back to the caller.

Note: Z3 formal verification is not applied here. The logic under test is primarily procedural integration code (calling subprocesses, parsing JSON, file system operations). It does not involve complex algorithmic constraints or state space exploration where Z3 would provide value over standard unit tests with mocking.
"""

import json
import pytest
from unittest.mock import MagicMock, patch, call
from pathlib import Path

# Import the module under test
from pdd.agentic_change import run_agentic_change

# --- Fixtures ---

@pytest.fixture
def mock_dependencies():
    """
    Mocks external dependencies:
    - shutil.which (to simulate gh installed)
    - subprocess.run (to simulate gh/git commands)
    - run_agentic_change_orchestrator (to simulate the core logic)
    - tempfile.mkdtemp (to simulate temp dir creation)
    - console (to suppress output)
    """
    with patch("pdd.agentic_change.shutil.which") as mock_which, \
         patch("pdd.agentic_change.subprocess.run") as mock_subprocess, \
         patch("pdd.agentic_change.run_agentic_change_orchestrator") as mock_orch, \
         patch("pdd.agentic_change.tempfile.mkdtemp") as mock_mkdtemp, \
         patch("pdd.agentic_change.console"):
        
        # Default: gh is installed
        mock_which.return_value = "/usr/bin/gh"
        
        # Default: subprocess calls succeed
        mock_subprocess.return_value.returncode = 0
        mock_subprocess.return_value.stdout = ""
        mock_subprocess.return_value.stderr = ""
        
        # Default: temp dir
        mock_mkdtemp.return_value = "/tmp/pdd_test_repo"
        
        # Default: orchestrator success
        mock_orch.return_value = (True, "Success", 1.0, "gpt-4", ["file.py"])
        
        yield mock_which, mock_subprocess, mock_orch, mock_mkdtemp

# --- Tests ---

def test_gh_cli_missing(mock_dependencies):
    """Test that the function fails gracefully if 'gh' is not installed."""
    mock_which, _, _, _ = mock_dependencies
    mock_which.return_value = None  # Simulate missing gh
    
    success, msg, _, _, _ = run_agentic_change("https://github.com/owner/repo/issues/1")
    
    assert success is False
    assert "gh CLI not found" in msg

def test_invalid_url(mock_dependencies):
    """Test that invalid URLs are rejected."""
    
    invalid_urls = [
        "https://gitlab.com/owner/repo/issues/1",
        "just_a_string",
        "https://github.com/owner/repo",  # Missing issue number
    ]
    
    for url in invalid_urls:
        success, msg, _, _, _ = run_agentic_change(url)
        assert success is False
        assert "Invalid GitHub URL" in msg

def test_issue_fetch_failure(mock_dependencies):
    """Test handling of failures when fetching the issue via gh api."""
    _, mock_subprocess, _, _ = mock_dependencies
    
    # Simulate gh api failure
    mock_subprocess.return_value.returncode = 1
    mock_subprocess.return_value.stderr = "Not Found"
    
    success, msg, _, _, _ = run_agentic_change("https://github.com/owner/repo/issues/1")
    
    assert success is False
    assert "Issue not found" in msg
    assert "Not Found" in msg

def test_issue_json_decode_error(mock_dependencies):
    """Test handling of invalid JSON response from gh api."""
    _, mock_subprocess, _, _ = mock_dependencies
    
    # Simulate success return code but bad JSON
    mock_subprocess.return_value.returncode = 0
    mock_subprocess.return_value.stdout = "{ invalid json"
    
    success, msg, _, _, _ = run_agentic_change("https://github.com/owner/repo/issues/1")
    
    assert success is False
    assert "Failed to parse issue JSON" in msg

def test_happy_path_clone_repo(mock_dependencies):
    """
    Test the full happy path where the repo needs to be cloned.
    Verifies API calls, content aggregation, and orchestrator invocation.
    """
    _, mock_subprocess, mock_orch, mock_mkdtemp = mock_dependencies
    
    # Setup mock responses for subprocess calls
    # 1. Issue API
    issue_data = {
        "title": "Fix Bug",
        "body": "Bug description",
        "user": {"login": "author"},
        "comments_url": "https://api.github.com/repos/owner/repo/issues/1/comments"
    }
    
    # 2. Comments API
    comments_data = [
        {"user": {"login": "commenter"}, "body": "I agree"}
    ]
    
    # 3. Git remote check (simulating we are NOT in the repo)
    # We need to mock Path.cwd() to return a path where .git does not exist
    # or ensure the subprocess check fails/returns mismatch.
    # The code checks `(Path.cwd() / ".git").exists()`.
    
    def subprocess_side_effect(args, **kwargs):
        cmd = args if isinstance(args, list) else []

        # Comments API (check BEFORE Issue API since comments URL contains "issues/1" too)
        if "api" in cmd and any("comments" in arg for arg in cmd):
            m = MagicMock()
            m.returncode = 0
            m.stdout = json.dumps(comments_data)
            return m

        # Issue API
        if "api" in cmd and any("issues/1" in arg for arg in cmd):
            m = MagicMock()
            m.returncode = 0
            m.stdout = json.dumps(issue_data)
            return m

        # Clone command
        if "repo" in cmd and "clone" in cmd:
            m = MagicMock()
            m.returncode = 0
            return m

        # Default fallback
        m = MagicMock()
        m.returncode = 1  # Fail other commands (like git remote) to force clone path
        return m

    mock_subprocess.side_effect = subprocess_side_effect

    # Mock Path.cwd() to ensure we don't accidentally trigger "current dir is repo" logic
    with patch("pdd.agentic_change.Path.cwd") as mock_cwd:
        # Make .git NOT exist
        mock_cwd.return_value.__truediv__.return_value.exists.return_value = False
        
        success, msg, cost, model, files = run_agentic_change(
            "https://github.com/owner/repo/issues/1",
            verbose=True
        )

    assert success is True
    assert msg == "Success"
    
    # Verify Orchestrator Call
    mock_orch.assert_called_once()
    call_kwargs = mock_orch.call_args[1]
    
    assert call_kwargs["issue_title"] == "Fix Bug"
    assert call_kwargs["issue_author"] == "author"
    assert call_kwargs["repo_owner"] == "owner"
    assert call_kwargs["repo_name"] == "repo"
    
    # Verify content aggregation
    content = call_kwargs["issue_content"]
    assert "Title: Fix Bug" in content
    assert "Bug description" in content
    assert "--- Comment by commenter ---" in content
    assert "I agree" in content
    
    # Verify CWD was the temp dir
    assert str(call_kwargs["cwd"]) == "/tmp/pdd_test_repo"

def test_happy_path_current_directory(mock_dependencies):
    """
    Test the scenario where the current directory is already the target repository.
    Verifies that cloning is skipped.
    """
    _, mock_subprocess, mock_orch, _ = mock_dependencies
    
    issue_data = {"title": "T", "body": "B", "user": {"login": "u"}, "comments_url": ""}
    
    def subprocess_side_effect(args, **kwargs):
        cmd = args if isinstance(args, list) else []
        
        if "api" in cmd:
            m = MagicMock()
            m.returncode = 0
            m.stdout = json.dumps(issue_data)
            return m
            
        # Git remote check
        if "git" in cmd and "remote" in cmd:
            m = MagicMock()
            m.returncode = 0
            # Return a matching remote URL
            m.stdout = "https://github.com/owner/repo.git" 
            return m
            
        m = MagicMock()
        m.returncode = 0
        return m

    mock_subprocess.side_effect = subprocess_side_effect

    # Create a mock that behaves like Path("/local/repo")
    mock_path = MagicMock()
    mock_path.__truediv__ = MagicMock(return_value=MagicMock(exists=MagicMock(return_value=True)))
    mock_path.__eq__ = lambda self, other: other == Path("/local/repo")
    mock_path.__str__ = lambda self: "/local/repo"
    mock_path.__fspath__ = lambda self: "/local/repo"

    # Mock Path.cwd() to simulate we are in a repo
    with patch("pdd.agentic_change.Path.cwd") as mock_cwd:
        mock_cwd.return_value = mock_path
        run_agentic_change("https://github.com/owner/repo/issues/1")

    # Verify orchestrator called with local path (the mock_path)
    call_kwargs = mock_orch.call_args[1]
    assert call_kwargs["cwd"] == mock_path
    
    # Verify NO clone command was issued
    for call_obj in mock_subprocess.call_args_list:
        args = call_obj[0][0]
        assert "clone" not in args

def test_comments_fetch_failure_resilience(mock_dependencies):
    """
    Test that if fetching comments fails, the workflow proceeds with just the issue body.
    """
    _, mock_subprocess, mock_orch, _ = mock_dependencies
    
    issue_data = {"title": "T", "body": "BodyOnly", "user": {"login": "u"}, "comments_url": "http://bad.url"}
    
    def subprocess_side_effect(args, **kwargs):
        cmd = args if isinstance(args, list) else []
        
        # Issue API succeeds
        if "api" in cmd and any("issues/1" in arg for arg in cmd):
            m = MagicMock()
            m.returncode = 0
            m.stdout = json.dumps(issue_data)
            return m
            
        # Comments API fails
        if "api" in cmd and any("bad.url" in arg for arg in cmd):
            m = MagicMock()
            m.returncode = 1
            m.stderr = "Error"
            return m
            
        # Clone succeeds
        m = MagicMock()
        m.returncode = 0
        return m

    mock_subprocess.side_effect = subprocess_side_effect
    
    with patch("pdd.agentic_change.Path.cwd") as mock_cwd:
        mock_cwd.return_value.__truediv__.return_value.exists.return_value = False
        
        success, _, _, _, _ = run_agentic_change("https://github.com/owner/repo/issues/1")
    
    assert success is True
    
    # Verify content has body but no comments section
    call_kwargs = mock_orch.call_args[1]
    content = call_kwargs["issue_content"]
    assert "BodyOnly" in content
    assert "Comments:" not in content

def test_clone_failure(mock_dependencies):
    """Test handling of git clone failure."""
    _, mock_subprocess, _, _ = mock_dependencies

    issue_data = {"title": "T", "body": "B", "user": {"login": "u"}, "comments_url": ""}

    def subprocess_side_effect(args, **kwargs):
        cmd = args if isinstance(args, list) else []

        if "api" in cmd:
            m = MagicMock()
            m.returncode = 0
            m.stdout = json.dumps(issue_data)
            return m

        # Clone fails
        if "repo" in cmd and "clone" in cmd:
            m = MagicMock()
            m.returncode = 1
            m.stderr = "Permission denied"
            return m

        m = MagicMock()
        m.returncode = 1 # Force clone path
        return m

    mock_subprocess.side_effect = subprocess_side_effect

    with patch("pdd.agentic_change.Path.cwd") as mock_cwd:
        mock_cwd.return_value.__truediv__.return_value.exists.return_value = False

        success, msg, _, _, _ = run_agentic_change("https://github.com/owner/repo/issues/1")

    assert success is False
    assert "Failed to clone repository" in msg
    assert "Permission denied" in msg


def test_issue_content_curly_braces_escaped(mock_dependencies):
    """
    Test that curly braces in issue content are escaped to prevent
    Python's .format() from interpreting them as placeholders.

    Reproduces bug: KeyError when issue contains code like { setError("coming soon") }
    """
    _, mock_subprocess, mock_orch, _ = mock_dependencies

    # Issue body contains JavaScript code with curly braces
    issue_data = {
        "title": "Fix error handling",
        "body": "The function does this:\n```javascript\nfunction handleClick() { setError(\"coming soon\") }\n```",
        "user": {"login": "author"},
        "comments_url": "https://api.github.com/repos/owner/repo/issues/248/comments"
    }

    # Comment also contains code with curly braces
    comments_data = [
        {"user": {"login": "reviewer"}, "body": "You should use: `const obj = { key: value }`"}
    ]

    def subprocess_side_effect(args, **kwargs):
        cmd = args if isinstance(args, list) else []

        # Comments API
        if "api" in cmd and any("comments" in arg for arg in cmd):
            m = MagicMock()
            m.returncode = 0
            m.stdout = json.dumps(comments_data)
            return m

        # Issue API
        if "api" in cmd and any("issues/248" in arg for arg in cmd):
            m = MagicMock()
            m.returncode = 0
            m.stdout = json.dumps(issue_data)
            return m

        # Clone command
        if "repo" in cmd and "clone" in cmd:
            m = MagicMock()
            m.returncode = 0
            return m

        # Default
        m = MagicMock()
        m.returncode = 1
        return m

    mock_subprocess.side_effect = subprocess_side_effect

    with patch("pdd.agentic_change.Path.cwd") as mock_cwd:
        mock_cwd.return_value.__truediv__.return_value.exists.return_value = False

        success, msg, _, _, _ = run_agentic_change(
            "https://github.com/owner/repo/issues/248"
        )

    assert success is True

    # Verify the orchestrator was called
    mock_orch.assert_called_once()
    call_kwargs = mock_orch.call_args[1]
    content = call_kwargs["issue_content"]

    # Curly braces should be ESCAPED (doubled) to prevent .format() errors
    # { becomes {{ and } becomes }}
    #
    # The BUG: When issue content contains { setError("coming soon") },
    # calling prompt_template.format(**context) fails with:
    #   KeyError: ' setError("coming soon") '
    # because Python interprets { ... } as a format placeholder.

    # The FIX: Escape all curly braces in issue_content so { becomes {{
    # After escaping, .format() will convert {{ back to { in the output,
    # but won't try to substitute them as placeholders.

    # Verify that the content can be safely used in .format() without KeyError
    # This is the actual bug reproduction - if braces aren't escaped, this raises KeyError
    try:
        # Simulate what the orchestrator does: call .format() with the content
        # The content should have {issue_content} placeholder escaped, so when
        # we format a template containing this escaped content, it works.
        test_template = "Issue content: {content}"
        test_template.format(content=content)
        # If we get here, the content itself is safe
    except KeyError as e:
        pytest.fail(f"Content contains unescaped braces that cause KeyError: {e}")

    # Additionally verify the escaping is correct:
    # The original "{ setError" should now be "{{ setError" (two opening braces)
    # Count opening braces before "setError" - should be 2 (escaped), not 1 (raw)
    import re
    # Find pattern: one or more { followed by space and "setError"
    match = re.search(r'(\{+)\s*setError', content)
    assert match is not None, "Should find braces before setError"
    braces = match.group(1)
    assert len(braces) == 2, f"Expected 2 opening braces (escaped), got {len(braces)}: '{braces}'"