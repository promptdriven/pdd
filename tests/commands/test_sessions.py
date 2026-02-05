"""
Test Plan for pdd.commands.sessions

1. **sessions command group**:
   - Should be a Click group with name "sessions"
   - Should have docstring "Manage remote PDD sessions."

2. **sessions list**:
   - **Case 1: Not authenticated**: Should show error message.
   - **Case 2: No sessions**: Should show "No active remote sessions found."
   - **Case 3: With sessions**: Should display table with SESSION ID, PROJECT, CLOUD URL, STATUS, LAST SEEN.
   - **Case 4: With --json flag**: Should output JSON array.
   - **Case 5: API error**: Should show error message.

3. **sessions info**:
   - **Case 1: Not authenticated**: Should show error message.
   - **Case 2: Session found**: Should display key-value table.
   - **Case 3: Session not found**: Should show "Session not found."
   - **Case 4: API error**: Should show error message.

4. **sessions cleanup**:
   - **Case 1: Not authenticated**: Should show error message.
   - **Case 2: No sessions**: Should show "No active remote sessions found."
   - **Case 3: With --all --force**: Should cleanup all sessions without prompt.
   - **Case 4: With --stale --force**: Should cleanup only stale sessions.
   - **Case 5: Partial failure**: Should report success/failure counts.
"""

import json
from dataclasses import dataclass
from datetime import datetime
from pathlib import Path
from unittest.mock import AsyncMock, MagicMock, patch

import pytest
from click.testing import CliRunner

from pdd.commands.sessions import sessions


# --- Mock Data ---

@dataclass
class MockSessionInfo:
    """Mock session info for testing."""
    session_id: str
    project_name: str
    cloud_url: str
    status: str
    last_heartbeat: str
    created_at: str = "2024-01-01T00:00:00Z"
    project_path: str = "/test/path"
    metadata: dict = None

    def __post_init__(self):
        if self.metadata is None:
            self.metadata = {}


@pytest.fixture
def mock_sessions():
    """Fixture providing sample session data."""
    return [
        MockSessionInfo(
            session_id="abc12345-6789-def0-1234-567890abcdef",
            project_name="test-project",
            cloud_url="https://pdd.dev/connect/abc12345",
            status="active",
            last_heartbeat="2024-01-01T10:00:00Z",
        ),
        MockSessionInfo(
            session_id="xyz98765-4321-fedc-ba98-7654321fedcba",
            project_name="another-project",
            cloud_url="https://pdd.dev/connect/xyz98765",
            status="stale",
            last_heartbeat="2024-01-01T08:00:00Z",
        ),
    ]


@pytest.fixture
def runner():
    """Fixture to provide a CliRunner for testing Click commands."""
    return CliRunner()


# --- sessions list Tests ---

@patch("pdd.commands.sessions.CloudConfig")
def test_list_sessions_not_authenticated(mock_cloud_config, runner):
    """Should show error when not authenticated."""
    mock_cloud_config.get_jwt_token.return_value = None

    result = runner.invoke(sessions, ["list"])

    assert result.exit_code == 0
    assert "Not authenticated" in result.output
    assert "pdd auth login" in result.output


@patch("pdd.commands.sessions.RemoteSessionManager")
@patch("pdd.commands.sessions.CloudConfig")
def test_list_sessions_empty(mock_cloud_config, mock_manager, runner):
    """Should show message when no sessions found."""
    mock_cloud_config.get_jwt_token.return_value = "test-jwt-token"
    mock_manager.list_sessions = AsyncMock(return_value=[])

    result = runner.invoke(sessions, ["list"])

    assert result.exit_code == 0
    assert "No active remote sessions found" in result.output


@patch("pdd.commands.sessions.RemoteSessionManager")
@patch("pdd.commands.sessions.CloudConfig")
def test_list_sessions_with_sessions(mock_cloud_config, mock_manager, runner, mock_sessions):
    """Should display table with sessions."""
    mock_cloud_config.get_jwt_token.return_value = "test-jwt-token"
    mock_manager.list_sessions = AsyncMock(return_value=mock_sessions)

    result = runner.invoke(sessions, ["list"])

    assert result.exit_code == 0
    # Check table headers or content
    assert "abc12345" in result.output  # Truncated session ID
    assert "test-project" in result.output
    assert "active" in result.output.lower() or "Active" in result.output
    assert "xyz98765" in result.output
    assert "another-project" in result.output


@patch("pdd.commands.sessions.RemoteSessionManager")
@patch("pdd.commands.sessions.CloudConfig")
def test_list_sessions_json_output(mock_cloud_config, mock_manager, runner, mock_sessions):
    """Should output JSON when --json flag is used."""
    mock_cloud_config.get_jwt_token.return_value = "test-jwt-token"
    mock_manager.list_sessions = AsyncMock(return_value=mock_sessions)

    result = runner.invoke(sessions, ["list", "--json"])

    assert result.exit_code == 0
    # Output should be valid JSON
    try:
        data = json.loads(result.output)
        assert isinstance(data, list)
        assert len(data) == 2
        assert data[0]["session_id"] == mock_sessions[0].session_id
    except json.JSONDecodeError:
        pytest.fail(f"Output is not valid JSON: {result.output}")


@patch("pdd.commands.sessions.RemoteSessionManager")
@patch("pdd.commands.sessions.CloudConfig")
def test_list_sessions_api_error(mock_cloud_config, mock_manager, runner):
    """Should show error when API call fails."""
    mock_cloud_config.get_jwt_token.return_value = "test-jwt-token"
    mock_manager.list_sessions = AsyncMock(side_effect=Exception("Network error"))

    result = runner.invoke(sessions, ["list"])

    assert result.exit_code == 0
    assert "Error listing sessions" in result.output
    assert "Network error" in result.output


# --- sessions info Tests ---

@patch("pdd.commands.sessions.CloudConfig")
def test_info_not_authenticated(mock_cloud_config, runner):
    """Should show error when not authenticated."""
    mock_cloud_config.get_jwt_token.return_value = None

    result = runner.invoke(sessions, ["info", "test-session-id"])

    assert result.exit_code == 0
    assert "Not authenticated" in result.output


@patch("pdd.commands.sessions.RemoteSessionManager")
@patch("pdd.commands.sessions.CloudConfig")
def test_info_session_found(mock_cloud_config, mock_manager, runner, mock_sessions):
    """Should display session info when found."""
    mock_cloud_config.get_jwt_token.return_value = "test-jwt-token"
    mock_manager.get_session = AsyncMock(return_value=mock_sessions[0])

    result = runner.invoke(sessions, ["info", "abc12345"])

    assert result.exit_code == 0
    assert "Session Information" in result.output
    assert "test-project" in result.output


@patch("pdd.commands.sessions.RemoteSessionManager")
@patch("pdd.commands.sessions.CloudConfig")
def test_info_session_not_found(mock_cloud_config, mock_manager, runner):
    """Should show error when session not found."""
    mock_cloud_config.get_jwt_token.return_value = "test-jwt-token"
    mock_manager.get_session = AsyncMock(return_value=None)

    result = runner.invoke(sessions, ["info", "nonexistent"])

    assert result.exit_code == 0
    assert "not found" in result.output.lower()


@patch("pdd.commands.sessions.RemoteSessionManager")
@patch("pdd.commands.sessions.CloudConfig")
def test_info_api_error(mock_cloud_config, mock_manager, runner):
    """Should show error when API call fails."""
    mock_cloud_config.get_jwt_token.return_value = "test-jwt-token"
    mock_manager.get_session = AsyncMock(side_effect=Exception("Network error"))

    result = runner.invoke(sessions, ["info", "test-session"])

    assert result.exit_code == 0
    assert "Error fetching session" in result.output


# --- sessions cleanup Tests ---

@patch("pdd.commands.sessions.CloudConfig")
def test_cleanup_not_authenticated(mock_cloud_config, runner):
    """Should show error when not authenticated."""
    mock_cloud_config.get_jwt_token.return_value = None

    result = runner.invoke(sessions, ["cleanup", "--all", "--force"])

    assert result.exit_code == 0
    assert "Not authenticated" in result.output


@patch("pdd.commands.sessions.RemoteSessionManager")
@patch("pdd.commands.sessions.CloudConfig")
def test_cleanup_no_sessions(mock_cloud_config, mock_manager, runner):
    """Should show message when no sessions to cleanup."""
    mock_cloud_config.get_jwt_token.return_value = "test-jwt-token"
    mock_manager.list_sessions = AsyncMock(return_value=[])

    result = runner.invoke(sessions, ["cleanup", "--all", "--force"])

    assert result.exit_code == 0
    assert "No active remote sessions found" in result.output


@patch("pdd.commands.sessions.RemoteSessionManager")
@patch("pdd.commands.sessions.CloudConfig")
def test_cleanup_all_force(mock_cloud_config, mock_manager_class, runner, mock_sessions):
    """Should cleanup all sessions with --all --force."""
    mock_cloud_config.get_jwt_token.return_value = "test-jwt-token"
    mock_manager_class.list_sessions = AsyncMock(return_value=mock_sessions)

    # Mock the instance created for deregister
    mock_instance = MagicMock()
    mock_instance.deregister = AsyncMock(return_value=None)
    mock_manager_class.return_value = mock_instance

    result = runner.invoke(sessions, ["cleanup", "--all", "--force"])

    assert result.exit_code == 0
    assert "Successfully cleaned up" in result.output
    assert "2" in result.output  # 2 sessions


@patch("pdd.commands.sessions.RemoteSessionManager")
@patch("pdd.commands.sessions.CloudConfig")
def test_cleanup_stale_only(mock_cloud_config, mock_manager_class, runner, mock_sessions):
    """Should cleanup only stale sessions with --stale --force."""
    mock_cloud_config.get_jwt_token.return_value = "test-jwt-token"
    mock_manager_class.list_sessions = AsyncMock(return_value=mock_sessions)

    # Mock the instance created for deregister
    mock_instance = MagicMock()
    mock_instance.deregister = AsyncMock(return_value=None)
    mock_manager_class.return_value = mock_instance

    result = runner.invoke(sessions, ["cleanup", "--stale", "--force"])

    assert result.exit_code == 0
    assert "Successfully cleaned up" in result.output
    assert "1" in result.output  # Only 1 stale session


@patch("pdd.commands.sessions.RemoteSessionManager")
@patch("pdd.commands.sessions.CloudConfig")
def test_cleanup_no_stale_sessions(mock_cloud_config, mock_manager, runner):
    """Should show message when no stale sessions to cleanup."""
    mock_cloud_config.get_jwt_token.return_value = "test-jwt-token"
    # All sessions are active
    active_sessions = [
        MockSessionInfo(
            session_id="active-1",
            project_name="project1",
            cloud_url="https://pdd.dev/connect/active-1",
            status="active",
            last_heartbeat="2024-01-01T10:00:00Z",
        ),
    ]
    mock_manager.list_sessions = AsyncMock(return_value=active_sessions)

    result = runner.invoke(sessions, ["cleanup", "--stale", "--force"])

    assert result.exit_code == 0
    assert "No stale sessions found" in result.output


@patch("pdd.commands.sessions.RemoteSessionManager")
@patch("pdd.commands.sessions.CloudConfig")
def test_cleanup_partial_failure(mock_cloud_config, mock_manager_class, runner, mock_sessions):
    """Should report both success and failure counts."""
    mock_cloud_config.get_jwt_token.return_value = "test-jwt-token"
    mock_manager_class.list_sessions = AsyncMock(return_value=mock_sessions)

    # Mock deregister to fail for second session
    call_count = 0

    async def mock_deregister():
        nonlocal call_count
        call_count += 1
        if call_count == 2:
            raise Exception("Failed to deregister")

    mock_instance = MagicMock()
    mock_instance.deregister = mock_deregister
    mock_manager_class.return_value = mock_instance

    result = runner.invoke(sessions, ["cleanup", "--all", "--force"])

    assert result.exit_code == 0
    # Should show at least one success and one failure
    assert "Successfully cleaned up" in result.output or "Failed to cleanup" in result.output


@patch("pdd.commands.sessions.RemoteSessionManager")
@patch("pdd.commands.sessions.CloudConfig")
def test_cleanup_interactive_cancel(mock_cloud_config, mock_manager, runner, mock_sessions):
    """Should allow cancellation in interactive mode."""
    mock_cloud_config.get_jwt_token.return_value = "test-jwt-token"
    mock_manager.list_sessions = AsyncMock(return_value=mock_sessions)

    # Simulate user pressing Enter (empty input) to cancel
    result = runner.invoke(sessions, ["cleanup"], input="\n")

    assert result.exit_code == 0
    assert "Cancelled" in result.output


# --- Bug #470: Incorrect auth command reference in error messages ---

@patch("pdd.commands.sessions.CloudConfig")
def test_cleanup_not_authenticated_shows_correct_command(mock_cloud_config, runner):
    """
    Test for Issue #470: Verify cleanup command shows correct auth command.

    The cleanup command should reference 'pdd auth login', not 'pdd login'.
    This test will FAIL on the buggy code (line 159 has 'pdd login')
    and PASS once fixed to match lines 33 and 107.
    """
    mock_cloud_config.get_jwt_token.return_value = None

    result = runner.invoke(sessions, ["cleanup", "--all", "--force"])

    assert result.exit_code == 0
    assert "Not authenticated" in result.output
    # This assertion will FAIL on buggy code because it says 'pdd login'
    assert "pdd auth login" in result.output, (
        "Error message should reference 'pdd auth login', not 'pdd login'. "
        "See issue #470 for details."
    )


@patch("pdd.commands.sessions.CloudConfig")
def test_info_not_authenticated_shows_correct_command(mock_cloud_config, runner):
    """
    Strengthen the info command test to verify correct auth command reference.

    This ensures consistency with the list and cleanup commands.
    Should reference 'pdd auth login', not 'pdd login'.
    """
    mock_cloud_config.get_jwt_token.return_value = None

    result = runner.invoke(sessions, ["info", "test-session-id"])

    assert result.exit_code == 0
    assert "Not authenticated" in result.output
    assert "pdd auth login" in result.output, (
        "Error message should reference 'pdd auth login' for consistency"
    )


@pytest.mark.parametrize("subcommand,args", [
    ("list", []),
    ("info", ["test-session-id"]),
    ("cleanup", ["--all", "--force"]),
])
@patch("pdd.commands.sessions.CloudConfig")
def test_all_subcommands_show_consistent_auth_command(mock_cloud_config, subcommand, args, runner):
    """
    Regression test for Issue #470: Ensure ALL sessions subcommands consistently
    reference 'pdd auth login' when not authenticated.

    This parametrized test covers list, info, and cleanup commands.
    It will FAIL for the cleanup command on buggy code.
    """
    mock_cloud_config.get_jwt_token.return_value = None

    result = runner.invoke(sessions, [subcommand] + args)

    assert result.exit_code == 0
    assert "Not authenticated" in result.output
    # All subcommands must consistently reference the correct command
    assert "pdd auth login" in result.output, (
        f"The '{subcommand}' subcommand should reference 'pdd auth login', not 'pdd login'. "
        "All auth error messages must be consistent. See issue #470."
    )
    # Ensure the wrong command is NOT present
    assert "pdd login" not in result.output or "pdd auth login" in result.output, (
        f"The '{subcommand}' subcommand should not reference the non-existent 'pdd login' command"
    )
