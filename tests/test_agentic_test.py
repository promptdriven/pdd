"""
Test plan for pdd.agentic_test

1. URL Parsing Tests:
   - Verify extraction of owner, repo, issue number from various URL formats.
   - Verify rejection of invalid URLs.

2. GitHub CLI Check Tests:
   - Verify behavior when 'gh' is present vs absent.

3. Issue Fetching Tests:
   - Mock 'gh api' calls.
   - Verify composition of issue body + comments.
   - Verify error handling for API failures.

4. Repo Context Tests:
   - Verify detection of current repo via 'git remote'.
   - Verify cloning logic when not in repo.
   - Verify cleanup of temp dirs.

5. Main Workflow Tests (run_agentic_test):
   - Integration-style tests mocking the subprocess calls and orchestrator.
   - Verify parameter passing.
   - Verify error propagation.

6. CLI Entry Point Tests:
   - Verify argument parsing and delegation.
"""

import sys
import json
import subprocess
import pytest
from unittest.mock import MagicMock, patch, ANY
from pathlib import Path

# Import the module under test
# We need to make sure the import works based on the file structure provided in the prompt context
# Assuming pdd package structure
from pdd import agentic_test

# ==============================================================================
# Fixtures
# ==============================================================================

@pytest.fixture
def mock_subprocess():
    with patch("pdd.agentic_test.subprocess.run") as mock:
        yield mock

@pytest.fixture
def mock_shutil_which():
    with patch("pdd.agentic_test.shutil.which") as mock:
        yield mock

@pytest.fixture
def mock_orchestrator():
    with patch("pdd.agentic_test.run_agentic_test_orchestrator") as mock:
        # Default return: success, msg, cost, model, files
        mock.return_value = (True, "Success", 0.5, "gpt-4", ["file.py"])
        yield mock

@pytest.fixture
def mock_console():
    with patch("pdd.agentic_test.console") as mock:
        yield mock

# ==============================================================================
# URL Parsing Tests
# ==============================================================================

@pytest.mark.parametrize("url, expected", [
    ("https://github.com/owner/repo/issues/123", ("owner", "repo", 123)),
    ("http://github.com/owner/repo/issues/123", ("owner", "repo", 123)),
    ("github.com/owner/repo/issues/123", ("owner", "repo", 123)),
    ("https://www.github.com/owner/repo/issues/123", ("owner", "repo", 123)),
    ("https://github.com/owner/repo/issues/123/", ("owner", "repo", 123)), # Trailing slash
    ("https://github.com/owner/repo/issues/123#comment-1", ("owner", "repo", 123)), # Fragment
    ("https://github.com/owner/repo/issues/123?q=1", ("owner", "repo", 123)), # Query
])
def test_parse_github_url_valid(url, expected):
    """Test parsing of valid GitHub issue URLs."""
    # Accessing internal function for direct testing as per prompt instructions to test functionality
    # Since the prompt asks to test ACTUAL functions, and _parse_github_url is internal but critical logic,
    # we test it directly or via the public API. Here we test directly for precision.
    assert agentic_test._parse_github_url(url) == expected

@pytest.mark.parametrize("url", [
    "https://github.com/owner/repo/pull/123", # Pull request
    "https://github.com/owner/repo", # Repo root
    "https://google.com", # Wrong domain (though logic is path-based, so strictly it checks structure)
    "invalid-url",
    "https://github.com/owner/repo/issues/notanumber", # Non-integer issue
])
def test_parse_github_url_invalid(url):
    """Test parsing of invalid GitHub URLs."""
    assert agentic_test._parse_github_url(url) is None

# ==============================================================================
# GitHub CLI Check Tests
# ==============================================================================

def test_check_gh_cli_installed(mock_shutil_which):
    mock_shutil_which.return_value = "/usr/bin/gh"
    assert agentic_test._check_gh_cli() is True

def test_check_gh_cli_missing(mock_shutil_which):
    mock_shutil_which.return_value = None
    assert agentic_test._check_gh_cli() is False

# ==============================================================================
# Issue Fetching Tests
# ==============================================================================

def test_fetch_issue_data_success(mock_subprocess):
    """Test successful fetching of issue data and comments."""
    # Mock issue response
    issue_json = {
        "title": "Test Issue",
        "body": "This is a bug.",
        "state": "open",
        "labels": [{"name": "bug"}],
        "comments_url": "https://api.github.com/repos/o/r/issues/1/comments",
        "user": {"login": "tester"}
    }
    
    # Mock comments response
    comments_json = [
        {"user": {"login": "dev"}, "body": "Fixing it."}
    ]

    # Setup mock side effects for subprocess.run
    def side_effect(cmd, **kwargs):
        # Check if it's the issue fetch or comment fetch
        if "issues/123" in cmd[2]:
            return MagicMock(stdout=json.dumps(issue_json), returncode=0)
        if "comments" in cmd[2]:
            return MagicMock(stdout=json.dumps(comments_json), returncode=0)
        raise ValueError(f"Unexpected command: {cmd}")

    mock_subprocess.side_effect = side_effect

    data, error = agentic_test._fetch_issue_data("owner", "repo", 123)
    
    assert error is None
    assert data["title"] == "Test Issue"
    assert "This is a bug." in data["full_content_with_comments"]
    assert "User: dev" in data["full_content_with_comments"]
    assert "Fixing it." in data["full_content_with_comments"]
    assert "Labels: bug" in data["full_content_with_comments"]

def test_fetch_issue_data_api_failure(mock_subprocess):
    """Test handling of gh api failure."""
    mock_subprocess.side_effect = subprocess.CalledProcessError(1, ["gh"], stderr="Not Found")
    
    data, error = agentic_test._fetch_issue_data("owner", "repo", 999)
    
    assert data is None
    assert "GitHub API call failed" in error
    assert "Not Found" in error

def test_fetch_issue_data_json_error(mock_subprocess):
    """Test handling of invalid JSON response."""
    mock_subprocess.return_value = MagicMock(stdout="Invalid JSON", returncode=0)
    
    data, error = agentic_test._fetch_issue_data("owner", "repo", 123)
    
    assert data is None
    assert "Failed to parse" in error

# ==============================================================================
# Repo Context Tests
# ==============================================================================

def test_ensure_repo_context_already_in_repo(mock_subprocess):
    """Test when current directory is already the correct repo."""
    # Mock git remote get-url
    mock_subprocess.return_value = MagicMock(
        returncode=0, 
        stdout="https://github.com/owner/repo.git\n"
    )
    
    cwd = Path("/path/to/repo")
    success, path = agentic_test._ensure_repo_context("owner", "repo", cwd, quiet=True)
    
    assert success is True
    assert path == str(cwd)
    # Verify no clone attempted
    calls = [c for c in mock_subprocess.call_args_list if "clone" in c[0][0]]
    assert len(calls) == 0

def test_ensure_repo_context_needs_clone(mock_subprocess):
    """Test cloning when not in the correct repo."""
    # Mock git remote failure or mismatch
    mock_subprocess.side_effect = [
        # First call: git remote (fails or mismatch)
        MagicMock(returncode=1), 
        # Second call: git clone (success)
        MagicMock(returncode=0)
    ]
    
    with patch("pdd.agentic_test.tempfile.mkdtemp", return_value="/tmp/pdd_test_repo_123"):
        cwd = Path("/some/other/dir")
        success, path = agentic_test._ensure_repo_context("owner", "repo", cwd, quiet=True)
        
        assert success is True
        assert path == "/tmp/pdd_test_repo_123"
        
        # Verify clone was called
        clone_call = mock_subprocess.call_args_list[1]
        assert "git" in clone_call[0][0]
        assert "clone" in clone_call[0][0]
        assert "https://github.com/owner/repo.git" in clone_call[0][0]

def test_ensure_repo_context_clone_fails(mock_subprocess):
    """Test failure during git clone."""
    mock_subprocess.side_effect = [
        MagicMock(returncode=1), # remote check fails
        subprocess.CalledProcessError(1, ["git", "clone"], stderr="Auth failed") # clone fails
    ]
    
    with patch("pdd.agentic_test.tempfile.mkdtemp", return_value="/tmp/fail_repo"):
        with patch("pdd.agentic_test.shutil.rmtree") as mock_rm:
            cwd = Path("/dir")
            success, msg = agentic_test._ensure_repo_context("owner", "repo", cwd, quiet=True)
            
            assert success is False
            assert "Failed to clone" in msg
            # Verify cleanup
            mock_rm.assert_called_with(Path("/tmp/fail_repo"), ignore_errors=True)

# ==============================================================================
# Run Agentic Test (Main Entry Point) Tests
# ==============================================================================

def test_run_agentic_test_gh_missing(mock_shutil_which, mock_console):
    """Test failure when gh CLI is missing."""
    mock_shutil_which.return_value = None
    
    success, msg, _, _, _ = agentic_test.run_agentic_test("https://github.com/o/r/issues/1")
    
    assert success is False
    assert "gh CLI not found" in msg
    mock_console.print.assert_called()

def test_run_agentic_test_invalid_url(mock_shutil_which, mock_console):
    """Test failure with invalid URL."""
    mock_shutil_which.return_value = "/bin/gh"
    
    success, msg, _, _, _ = agentic_test.run_agentic_test("not-a-url")
    
    assert success is False
    assert "Invalid GitHub URL" in msg

def test_run_agentic_test_issue_fetch_fail(mock_shutil_which, mock_subprocess):
    """Test failure when issue cannot be fetched."""
    mock_shutil_which.return_value = "/bin/gh"
    # Mock API failure
    mock_subprocess.side_effect = subprocess.CalledProcessError(1, ["gh"], stderr="Not Found")
    
    success, msg, _, _, _ = agentic_test.run_agentic_test("https://github.com/o/r/issues/1")
    
    assert success is False
    assert "Issue not found" in msg

def test_run_agentic_test_success_flow(
    mock_shutil_which, 
    mock_subprocess, 
    mock_orchestrator
):
    """Test successful end-to-end flow."""
    mock_shutil_which.return_value = "/bin/gh"
    
    # Mock API responses and git commands
    issue_json = {"title": "T", "body": "B", "user": {"login": "U"}, "state": "open"}
    
    def side_effect(cmd, **kwargs):
        cmd_str = " ".join(cmd) if isinstance(cmd, list) else cmd
        if "api" in cmd and "issues/1" in str(cmd):
            return MagicMock(stdout=json.dumps(issue_json), returncode=0)
        if "api" in cmd: # comments
            return MagicMock(stdout="[]", returncode=0)
        if "git remote" in str(cmd_str):
            return MagicMock(stdout="https://github.com/owner/repo.git", returncode=0)
        return MagicMock(returncode=0)

    mock_subprocess.side_effect = side_effect
    
    success, msg, cost, model, files = agentic_test.run_agentic_test(
        "https://github.com/owner/repo/issues/1",
        verbose=True,
        timeout_adder=10.0
    )
    
    assert success is True
    assert msg == "Success"
    
    # Verify orchestrator call
    mock_orchestrator.assert_called_once()
    call_kwargs = mock_orchestrator.call_args[1]
    assert call_kwargs["issue_number"] == 1
    assert call_kwargs["repo_owner"] == "owner"
    assert call_kwargs["timeout_adder"] == 10.0
    assert call_kwargs["verbose"] is True

def test_run_agentic_test_orchestrator_exception(
    mock_shutil_which, 
    mock_subprocess, 
    mock_orchestrator
):
    """Test handling of exception in orchestrator."""
    mock_shutil_which.return_value = "/bin/gh"
    
    # Setup minimal success for pre-checks
    mock_subprocess.side_effect = lambda *args, **kwargs: MagicMock(stdout="{}", returncode=0)
    
    # Orchestrator throws
    mock_orchestrator.side_effect = Exception("Boom")
    
    success, msg, _, _, _ = agentic_test.run_agentic_test("https://github.com/o/r/issues/1")
    
    assert success is False
    assert "Orchestrator failed" in msg
    assert "Boom" in msg

def test_run_agentic_test_cleanup(
    mock_shutil_which, 
    mock_subprocess, 
    mock_orchestrator
):
    """Test that temp directory is cleaned up."""
    mock_shutil_which.return_value = "/bin/gh"
    
    # Force clone path
    mock_subprocess.side_effect = [
        MagicMock(stdout="{}", returncode=0), # issue
        MagicMock(stdout="[]", returncode=0), # comments
        MagicMock(returncode=1), # git remote fails -> trigger clone
        MagicMock(returncode=0), # git clone succeeds
    ]
    
    with patch("pdd.agentic_test.tempfile.mkdtemp", return_value="/tmp/pdd_cleanup_test") as mock_mkdtemp:
        with patch("pdd.agentic_test.shutil.rmtree") as mock_rmtree:
            with patch("pathlib.Path.exists", return_value=True): # Ensure it tries to delete
                agentic_test.run_agentic_test("https://github.com/o/r/issues/1")
                
                mock_rmtree.assert_called_with(Path("/tmp/pdd_cleanup_test"))

# ==============================================================================
# CLI Main Tests
# ==============================================================================

def test_main_manual_mode():
    """Test delegation to manual mode."""
    with patch("sys.argv", ["pdd", "--manual", "prompt.txt"]):
        with patch("pdd.cmd_test_main.main") as mock_legacy_main:
            agentic_test.main()
            mock_legacy_main.assert_called_once()

def test_main_agentic_mode_success(mock_orchestrator):
    """Test agentic mode success via CLI."""
    with patch("sys.argv", ["pdd", "https://github.com/o/r/issues/1"]):
        with patch("pdd.agentic_test.run_agentic_test") as mock_run:
            mock_run.return_value = (True, "OK", 0.0, "m", [])
            
            # Should not exit with error
            try:
                agentic_test.main()
            except SystemExit:
                pytest.fail("Should not exit on success")
            
            mock_run.assert_called_once()
            assert mock_run.call_args[1]["use_github_state"] is True

def test_main_agentic_mode_failure():
    """Test agentic mode failure via CLI."""
    with patch("sys.argv", ["pdd", "https://github.com/o/r/issues/1"]):
        with patch("pdd.agentic_test.run_agentic_test") as mock_run:
            mock_run.return_value = (False, "Fail", 0.0, "m", [])
            
            with pytest.raises(SystemExit) as exc:
                agentic_test.main()
            assert exc.value.code == 1

def test_main_no_args(mock_console):
    """Test CLI with no arguments."""
    with patch("sys.argv", ["pdd"]):
        with pytest.raises(SystemExit) as exc:
            agentic_test.main()
        assert exc.value.code == 1
        mock_console.print.assert_called_with("[red]Error: Issue URL required[/red]")

"""
Test plan for pdd.agentic_test

1. URL Parsing Tests:
   - Verify extraction of owner, repo, issue number from various URL formats.
   - Verify rejection of invalid URLs.

2. GitHub CLI Check Tests:
   - Verify behavior when 'gh' is present vs absent.

3. Issue Fetching Tests:
   - Mock 'gh api' calls.
   - Verify composition of issue body + comments.
   - Verify error handling for API failures.

4. Repo Context Tests:
   - Verify detection of current repo via 'git remote'.
   - Verify cloning logic when not in repo.
   - Verify cleanup of temp dirs.

5. Main Workflow Tests (run_agentic_test):
   - Integration-style tests mocking the subprocess calls and orchestrator.
   - Verify parameter passing.
   - Verify error propagation.

6. CLI Entry Point Tests:
   - Verify argument parsing and delegation.
"""

import sys
import json
import subprocess
import pytest
from unittest.mock import MagicMock, patch, ANY
from pathlib import Path

# Import the module under test
# We need to make sure the import works based on the file structure provided in the prompt context
# Assuming pdd package structure
from pdd import agentic_test

# ==============================================================================
# Fixtures
# ==============================================================================

@pytest.fixture
def mock_subprocess():
    with patch("pdd.agentic_test.subprocess.run") as mock:
        yield mock

@pytest.fixture
def mock_shutil_which():
    with patch("pdd.agentic_test.shutil.which") as mock:
        yield mock

@pytest.fixture
def mock_orchestrator():
    with patch("pdd.agentic_test.run_agentic_test_orchestrator") as mock:
        # Default return: success, msg, cost, model, files
        mock.return_value = (True, "Success", 0.5, "gpt-4", ["file.py"])
        yield mock

@pytest.fixture
def mock_console():
    with patch("pdd.agentic_test.console") as mock:
        yield mock

# ==============================================================================
# URL Parsing Tests
# ==============================================================================

@pytest.mark.parametrize("url, expected", [
    ("https://github.com/owner/repo/issues/123", ("owner", "repo", 123)),
    ("http://github.com/owner/repo/issues/123", ("owner", "repo", 123)),
    ("github.com/owner/repo/issues/123", ("owner", "repo", 123)),
    ("https://www.github.com/owner/repo/issues/123", ("owner", "repo", 123)),
    ("https://github.com/owner/repo/issues/123/", ("owner", "repo", 123)), # Trailing slash
    ("https://github.com/owner/repo/issues/123#comment-1", ("owner", "repo", 123)), # Fragment
    ("https://github.com/owner/repo/issues/123?q=1", ("owner", "repo", 123)), # Query
])
def test_parse_github_url_valid(url, expected):
    """Test parsing of valid GitHub issue URLs."""
    # Accessing internal function for direct testing as per prompt instructions to test functionality
    # Since the prompt asks to test ACTUAL functions, and _parse_github_url is internal but critical logic,
    # we test it directly or via the public API. Here we test directly for precision.
    assert agentic_test._parse_github_url(url) == expected

@pytest.mark.parametrize("url", [
    "https://github.com/owner/repo/pull/123", # Pull request
    "https://github.com/owner/repo", # Repo root
    "https://google.com", # Wrong domain (though logic is path-based, so strictly it checks structure)
    "invalid-url",
    "https://github.com/owner/repo/issues/notanumber", # Non-integer issue
])
def test_parse_github_url_invalid(url):
    """Test parsing of invalid GitHub URLs."""
    assert agentic_test._parse_github_url(url) is None

# ==============================================================================
# GitHub CLI Check Tests
# ==============================================================================

def test_check_gh_cli_installed(mock_shutil_which):
    mock_shutil_which.return_value = "/usr/bin/gh"
    assert agentic_test._check_gh_cli() is True

def test_check_gh_cli_missing(mock_shutil_which):
    mock_shutil_which.return_value = None
    assert agentic_test._check_gh_cli() is False

# ==============================================================================
# Issue Fetching Tests
# ==============================================================================

def test_fetch_issue_data_success(mock_subprocess):
    """Test successful fetching of issue data and comments."""
    # Mock issue response
    issue_json = {
        "title": "Test Issue",
        "body": "This is a bug.",
        "state": "open",
        "labels": [{"name": "bug"}],
        "comments_url": "https://api.github.com/repos/o/r/issues/1/comments",
        "user": {"login": "tester"}
    }
    
    # Mock comments response
    comments_json = [
        {"user": {"login": "dev"}, "body": "Fixing it."}
    ]

    # Setup mock side effects for subprocess.run
    def side_effect(cmd, **kwargs):
        # Check if it's the issue fetch or comment fetch
        if "issues/123" in cmd[2]:
            return MagicMock(stdout=json.dumps(issue_json), returncode=0)
        if "comments" in cmd[2]:
            return MagicMock(stdout=json.dumps(comments_json), returncode=0)
        raise ValueError(f"Unexpected command: {cmd}")

    mock_subprocess.side_effect = side_effect

    data, error = agentic_test._fetch_issue_data("owner", "repo", 123)
    
    assert error is None
    assert data["title"] == "Test Issue"
    assert "This is a bug." in data["full_content_with_comments"]
    assert "User: dev" in data["full_content_with_comments"]
    assert "Fixing it." in data["full_content_with_comments"]
    assert "Labels: bug" in data["full_content_with_comments"]

def test_fetch_issue_data_api_failure(mock_subprocess):
    """Test handling of gh api failure."""
    mock_subprocess.side_effect = subprocess.CalledProcessError(1, ["gh"], stderr="Not Found")
    
    data, error = agentic_test._fetch_issue_data("owner", "repo", 999)
    
    assert data is None
    assert "GitHub API call failed" in error
    assert "Not Found" in error

def test_fetch_issue_data_json_error(mock_subprocess):
    """Test handling of invalid JSON response."""
    mock_subprocess.return_value = MagicMock(stdout="Invalid JSON", returncode=0)
    
    data, error = agentic_test._fetch_issue_data("owner", "repo", 123)
    
    assert data is None
    assert "Failed to parse" in error

# ==============================================================================
# Repo Context Tests
# ==============================================================================

def test_ensure_repo_context_already_in_repo(mock_subprocess):
    """Test when current directory is already the correct repo."""
    # Mock git remote get-url
    mock_subprocess.return_value = MagicMock(
        returncode=0, 
        stdout="https://github.com/owner/repo.git\n"
    )
    
    cwd = Path("/path/to/repo")
    success, path = agentic_test._ensure_repo_context("owner", "repo", cwd, quiet=True)
    
    assert success is True
    assert path == str(cwd)
    # Verify no clone attempted
    calls = [c for c in mock_subprocess.call_args_list if "clone" in c[0][0]]
    assert len(calls) == 0

def test_ensure_repo_context_needs_clone(mock_subprocess):
    """Test cloning when not in the correct repo."""
    # Mock git remote failure or mismatch
    mock_subprocess.side_effect = [
        # First call: git remote (fails or mismatch)
        MagicMock(returncode=1), 
        # Second call: git clone (success)
        MagicMock(returncode=0)
    ]
    
    with patch("pdd.agentic_test.tempfile.mkdtemp", return_value="/tmp/pdd_test_repo_123"):
        cwd = Path("/some/other/dir")
        success, path = agentic_test._ensure_repo_context("owner", "repo", cwd, quiet=True)
        
        assert success is True
        assert path == "/tmp/pdd_test_repo_123"
        
        # Verify clone was called
        clone_call = mock_subprocess.call_args_list[1]
        assert "git" in clone_call[0][0]
        assert "clone" in clone_call[0][0]
        assert "https://github.com/owner/repo.git" in clone_call[0][0]

def test_ensure_repo_context_clone_fails(mock_subprocess):
    """Test failure during git clone."""
    mock_subprocess.side_effect = [
        MagicMock(returncode=1), # remote check fails
        subprocess.CalledProcessError(1, ["git", "clone"], stderr="Auth failed") # clone fails
    ]
    
    with patch("pdd.agentic_test.tempfile.mkdtemp", return_value="/tmp/fail_repo"):
        with patch("pdd.agentic_test.shutil.rmtree") as mock_rm:
            cwd = Path("/dir")
            success, msg = agentic_test._ensure_repo_context("owner", "repo", cwd, quiet=True)
            
            assert success is False
            assert "Failed to clone" in msg
            # Verify cleanup
            mock_rm.assert_called_with(Path("/tmp/fail_repo"), ignore_errors=True)

# ==============================================================================
# Run Agentic Test (Main Entry Point) Tests
# ==============================================================================

def test_run_agentic_test_gh_missing(mock_shutil_which, mock_console):
    """Test failure when gh CLI is missing."""
    mock_shutil_which.return_value = None
    
    success, msg, _, _, _ = agentic_test.run_agentic_test("https://github.com/o/r/issues/1")
    
    assert success is False
    assert "gh CLI not found" in msg
    mock_console.print.assert_called()

def test_run_agentic_test_invalid_url(mock_shutil_which, mock_console):
    """Test failure with invalid URL."""
    mock_shutil_which.return_value = "/bin/gh"
    
    success, msg, _, _, _ = agentic_test.run_agentic_test("not-a-url")
    
    assert success is False
    assert "Invalid GitHub URL" in msg

def test_run_agentic_test_issue_fetch_fail(mock_shutil_which, mock_subprocess):
    """Test failure when issue cannot be fetched."""
    mock_shutil_which.return_value = "/bin/gh"
    # Mock API failure
    mock_subprocess.side_effect = subprocess.CalledProcessError(1, ["gh"], stderr="Not Found")
    
    success, msg, _, _, _ = agentic_test.run_agentic_test("https://github.com/o/r/issues/1")
    
    assert success is False
    assert "Issue not found" in msg

def test_run_agentic_test_success_flow(
    mock_shutil_which, 
    mock_subprocess, 
    mock_orchestrator
):
    """Test successful end-to-end flow."""
    mock_shutil_which.return_value = "/bin/gh"
    
    # Mock API responses and git commands
    issue_json = {"title": "T", "body": "B", "user": {"login": "U"}, "state": "open"}
    
    def side_effect(cmd, **kwargs):
        cmd_str = " ".join(cmd) if isinstance(cmd, list) else cmd
        if "api" in cmd and "issues/1" in str(cmd):
            return MagicMock(stdout=json.dumps(issue_json), returncode=0)
        if "api" in cmd: # comments
            return MagicMock(stdout="[]", returncode=0)
        if "git remote" in str(cmd_str):
            return MagicMock(stdout="https://github.com/owner/repo.git", returncode=0)
        return MagicMock(returncode=0)

    mock_subprocess.side_effect = side_effect
    
    success, msg, cost, model, files = agentic_test.run_agentic_test(
        "https://github.com/owner/repo/issues/1",
        verbose=True,
        timeout_adder=10.0
    )
    
    assert success is True
    assert msg == "Success"
    
    # Verify orchestrator call
    mock_orchestrator.assert_called_once()
    call_kwargs = mock_orchestrator.call_args[1]
    assert call_kwargs["issue_number"] == 1
    assert call_kwargs["repo_owner"] == "owner"
    assert call_kwargs["timeout_adder"] == 10.0
    assert call_kwargs["verbose"] is True

def test_run_agentic_test_orchestrator_exception(
    mock_shutil_which, 
    mock_subprocess, 
    mock_orchestrator
):
    """Test handling of exception in orchestrator."""
    mock_shutil_which.return_value = "/bin/gh"
    
    # Setup minimal success for pre-checks
    mock_subprocess.side_effect = lambda *args, **kwargs: MagicMock(stdout="{}", returncode=0)
    
    # Orchestrator throws
    mock_orchestrator.side_effect = Exception("Boom")
    
    success, msg, _, _, _ = agentic_test.run_agentic_test("https://github.com/o/r/issues/1")
    
    assert success is False
    assert "Orchestrator failed" in msg
    assert "Boom" in msg

def test_run_agentic_test_cleanup(
    mock_shutil_which, 
    mock_subprocess, 
    mock_orchestrator
):
    """Test that temp directory is cleaned up."""
    mock_shutil_which.return_value = "/bin/gh"
    
    # Force clone path
    mock_subprocess.side_effect = [
        MagicMock(stdout="{}", returncode=0), # issue
        MagicMock(stdout="[]", returncode=0), # comments
        MagicMock(returncode=1), # git remote fails -> trigger clone
        MagicMock(returncode=0), # git clone succeeds
    ]
    
    with patch("pdd.agentic_test.tempfile.mkdtemp", return_value="/tmp/pdd_cleanup_test") as mock_mkdtemp:
        with patch("pdd.agentic_test.shutil.rmtree") as mock_rmtree:
            with patch("pathlib.Path.exists", return_value=True): # Ensure it tries to delete
                agentic_test.run_agentic_test("https://github.com/o/r/issues/1")
                
                mock_rmtree.assert_called_with(Path("/tmp/pdd_cleanup_test"))

# ==============================================================================
# CLI Main Tests
# ==============================================================================

def test_main_manual_mode():
    """Test delegation to manual mode."""
    with patch("sys.argv", ["pdd", "--manual", "prompt.txt"]):
        with patch("pdd.cmd_test_main.main") as mock_legacy_main:
            agentic_test.main()
            mock_legacy_main.assert_called_once()

def test_main_agentic_mode_success(mock_orchestrator):
    """Test agentic mode success via CLI."""
    with patch("sys.argv", ["pdd", "https://github.com/o/r/issues/1"]):
        with patch("pdd.agentic_test.run_agentic_test") as mock_run:
            mock_run.return_value = (True, "OK", 0.0, "m", [])
            
            # Should not exit with error
            try:
                agentic_test.main()
            except SystemExit:
                pytest.fail("Should not exit on success")
            
            mock_run.assert_called_once()
            assert mock_run.call_args[1]["use_github_state"] is True

def test_main_agentic_mode_failure():
    """Test agentic mode failure via CLI."""
    with patch("sys.argv", ["pdd", "https://github.com/o/r/issues/1"]):
        with patch("pdd.agentic_test.run_agentic_test") as mock_run:
            mock_run.return_value = (False, "Fail", 0.0, "m", [])
            
            with pytest.raises(SystemExit) as exc:
                agentic_test.main()
            assert exc.value.code == 1

def test_main_no_args(mock_console):
    """Test CLI with no arguments."""
    with patch("sys.argv", ["pdd"]):
        with pytest.raises(SystemExit) as exc:
            agentic_test.main()
        assert exc.value.code == 1
        mock_console.print.assert_called_with("[red]Error: Issue URL required[/red]")