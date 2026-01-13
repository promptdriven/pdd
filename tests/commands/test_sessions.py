# Test Plan for pdd/commands/sessions.py
#
# 1. Analysis of Code Under Test:
#    - The module implements a Click command group `sessions` with two subcommands: `list` and `info`.
#    - It interacts with `CloudConfig` for authentication (JWT token).
#    - It interacts with `RemoteSessionManager` (async) to fetch data.
#    - It uses `rich.console` and `rich.table` for output formatting.
#    - It handles exceptions using a utility `handle_error`.
#
# 2. Logic & Edge Cases:
#    - Authentication: Token missing -> Error message.
#    - API Errors: `RemoteSessionManager` raises exception -> `handle_error` called.
#    - `list` command:
#      - Empty list -> Specific warning message.
#      - JSON output -> Calls `console.print_json` with serialized data.
#      - Table output -> Calls `console.print` with a Table object.
#      - Status coloring -> "active" is green, "stale" is yellow.
#    - `info` command:
#      - Session not found -> Error message.
#      - Session found -> Displays metadata table.
#
# 3. Z3 Formal Verification:
#    - This module is primarily a CLI presentation layer (IO-bound, formatting, orchestration).
#    - The logic consists of simple conditional branches (if auth, if json, if active/stale).
#    - There are no complex algorithms, constraint satisfaction problems, or state machines suitable for SMT solving.
#    - Therefore, Z3 tests are omitted in favor of comprehensive unit tests using mocks.
#
# 4. Unit Test Strategy:
#    - Use `click.testing.CliRunner` to invoke commands.
#    - Mock `CloudConfig.get_jwt_token`.
#    - Mock `RemoteSessionManager` methods (`list_sessions`, `get_session`) using `AsyncMock` because they are called via `asyncio.run`.
#    - Mock `console` to verify output calls (print, print_json).
#    - Mock `handle_error` to verify exception handling delegation.
#    - Create dummy session objects to test serialization logic (model_dump vs dict vs __dict__).

import sys
from unittest.mock import MagicMock, AsyncMock

# -----------------------------------------------------------------------------
# Pre-import Mocking
# -----------------------------------------------------------------------------
# We must mock missing dependencies BEFORE importing the module under test
# to avoid ModuleNotFoundError during test collection if the environment is incomplete.

# Mock pdd.utils
if "pdd.utils" not in sys.modules:
    mock_utils = MagicMock()
    sys.modules["pdd.utils"] = mock_utils

# Mock pdd.core.cloud
if "pdd.core.cloud" not in sys.modules:
    mock_cloud_mod = MagicMock()
    sys.modules["pdd.core.cloud"] = mock_cloud_mod

# Mock pdd.remote_session
if "pdd.remote_session" not in sys.modules:
    mock_remote_mod = MagicMock()
    sys.modules["pdd.remote_session"] = mock_remote_mod

import pytest
from unittest.mock import patch
from click.testing import CliRunner
from rich.table import Table

# Import the actual module
# Renamed from sessions_group to sessions to match __init__.py expectations
from pdd.commands.sessions import sessions

# -----------------------------------------------------------------------------
# Fixtures
# -----------------------------------------------------------------------------

@pytest.fixture
def runner():
    return CliRunner()

@pytest.fixture
def mock_cloud_config():
    with patch("pdd.commands.sessions.CloudConfig") as mock:
        yield mock

@pytest.fixture
def mock_remote_session_manager():
    with patch("pdd.commands.sessions.RemoteSessionManager") as mock:
        yield mock

@pytest.fixture
def mock_console():
    with patch("pdd.commands.sessions.console") as mock:
        yield mock

@pytest.fixture
def mock_handle_error():
    with patch("pdd.commands.sessions.handle_error") as mock:
        yield mock

# Helper class to simulate session objects with different serialization methods
class MockSession:
    def __init__(self, **kwargs):
        for k, v in kwargs.items():
            setattr(self, k, v)
        self._data = kwargs

    def dict(self):
        return self._data

class MockSessionPydanticV2:
    def __init__(self, **kwargs):
        for k, v in kwargs.items():
            setattr(self, k, v)
        self._data = kwargs

    def model_dump(self):
        return self._data

class MockSessionPlain:
    def __init__(self, **kwargs):
        for k, v in kwargs.items():
            setattr(self, k, v)

# -----------------------------------------------------------------------------
# Tests for 'list' command
# -----------------------------------------------------------------------------

def test_list_sessions_no_auth(runner, mock_cloud_config, mock_console):
    """Test that list command fails gracefully when not authenticated."""
    mock_cloud_config.get_jwt_token.return_value = None

    result = runner.invoke(sessions, ["list"])

    assert result.exit_code == 0
    mock_console.print.assert_called_with("[red]Error: Not authenticated. Please run 'pdd auth login'.[/red]")

def test_list_sessions_api_error(runner, mock_cloud_config, mock_remote_session_manager, mock_handle_error):
    """Test that list command handles API exceptions."""
    mock_cloud_config.get_jwt_token.return_value = "fake_token"
    mock_remote_session_manager.list_sessions = AsyncMock(side_effect=Exception("API Boom"))

    result = runner.invoke(sessions, ["list"])

    assert result.exit_code == 0
    mock_handle_error.assert_called_once()
    args, _ = mock_handle_error.call_args
    assert str(args[0]) == "API Boom"

def test_list_sessions_empty(runner, mock_cloud_config, mock_remote_session_manager, mock_console):
    """Test list command with no active sessions."""
    mock_cloud_config.get_jwt_token.return_value = "fake_token"
    mock_remote_session_manager.list_sessions = AsyncMock(return_value=[])

    result = runner.invoke(sessions, ["list"])

    assert result.exit_code == 0
    mock_console.print.assert_called_with("[yellow]No active remote sessions found.[/yellow]")

def test_list_sessions_table_output(runner, mock_cloud_config, mock_remote_session_manager, mock_console):
    """Test list command displays a table with correct data and formatting."""
    mock_cloud_config.get_jwt_token.return_value = "fake_token"

    # Create mock sessions - using new API field names
    s1 = MockSession(session_id="1234567890", project_name="proj1", cloud_url="https://pdd.dev/connect/1234", status="active", last_heartbeat="now")
    s2 = MockSession(session_id="abc", project_name="proj2", cloud_url="https://pdd.dev/connect/abc", status="stale", last_heartbeat="yesterday")
    s3 = MockSession(session_id="xyz", project_name="proj3", cloud_url="https://pdd.dev/connect/xyz", status="unknown", last_heartbeat="never")

    mock_remote_session_manager.list_sessions = AsyncMock(return_value=[s1, s2, s3])

    result = runner.invoke(sessions, ["list"])

    assert result.exit_code == 0

    # Verify a table was printed
    assert mock_console.print.called
    args, _ = mock_console.print.call_args
    printed_obj = args[0]
    assert isinstance(printed_obj, Table)

    # We can't easily inspect the rows of a Rich Table object directly via public API in a stable way for unit tests
    # without accessing internal structures, but we can verify the call happened.
    # We can verify the columns though.
    assert len(printed_obj.columns) == 5
    assert printed_obj.columns[0].header == "SESSION ID"

def test_list_sessions_json_output(runner, mock_cloud_config, mock_remote_session_manager, mock_console):
    """Test list command with --json flag handles different object types."""
    mock_cloud_config.get_jwt_token.return_value = "fake_token"
    
    # Test handling of .model_dump(), .dict(), and __dict__
    s1 = MockSessionPydanticV2(id="1", type="v2")
    s2 = MockSession(id="2", type="v1")
    s3 = MockSessionPlain(id="3", type="plain")
    
    mock_remote_session_manager.list_sessions = AsyncMock(return_value=[s1, s2, s3])

    result = runner.invoke(sessions, ["list", "--json"])

    assert result.exit_code == 0
    
    # Verify print_json was called with correct list
    mock_console.print_json.assert_called_once()
    _, kwargs = mock_console.print_json.call_args
    data = kwargs.get('data')
    
    assert len(data) == 3
    assert data[0] == {"id": "1", "type": "v2"}
    assert data[1] == {"id": "2", "type": "v1"}
    assert data[2] == {"id": "3", "type": "plain"}

# -----------------------------------------------------------------------------
# Tests for 'info' command
# -----------------------------------------------------------------------------

def test_session_info_no_auth(runner, mock_cloud_config, mock_console):
    """Test info command fails when not authenticated."""
    mock_cloud_config.get_jwt_token.return_value = None

    result = runner.invoke(sessions, ["info", "sess_123"])

    assert result.exit_code == 0
    mock_console.print.assert_called_with("[red]Error: Not authenticated. Please run 'pdd auth login'.[/red]")

def test_session_info_api_error(runner, mock_cloud_config, mock_remote_session_manager, mock_handle_error):
    """Test info command handles API exceptions."""
    mock_cloud_config.get_jwt_token.return_value = "fake_token"
    mock_remote_session_manager.get_session = AsyncMock(side_effect=Exception("Fetch Failed"))

    result = runner.invoke(sessions, ["info", "sess_123"])

    assert result.exit_code == 0
    mock_handle_error.assert_called_once()

def test_session_info_not_found(runner, mock_cloud_config, mock_remote_session_manager, mock_console):
    """Test info command when session is not found (returns None)."""
    mock_cloud_config.get_jwt_token.return_value = "fake_token"
    mock_remote_session_manager.get_session = AsyncMock(return_value=None)

    result = runner.invoke(sessions, ["info", "sess_missing"])

    assert result.exit_code == 0
    mock_console.print.assert_called_with("[red]Session 'sess_missing' not found.[/red]")

def test_session_info_success(runner, mock_cloud_config, mock_remote_session_manager, mock_console):
    """Test info command displays session details."""
    mock_cloud_config.get_jwt_token.return_value = "fake_token"
    
    # Mock session with some data
    session_data = {"session_id": "sess_123", "status": "active", "created_at": "2023-01-01"}
    session = MockSession(**session_data)
    
    mock_remote_session_manager.get_session = AsyncMock(return_value=session)

    result = runner.invoke(sessions, ["info", "sess_123"])

    assert result.exit_code == 0
    
    # Verify calls
    # 1. Header print
    mock_console.print.assert_any_call("[bold blue]Session Information: sess_123[/bold blue]")
    
    # 2. Table print
    # The last call should be the table
    args, _ = mock_console.print.call_args
    printed_obj = args[0]
    assert isinstance(printed_obj, Table)
    
    # Verify table structure (Field, Value)
    assert len(printed_obj.columns) == 2
    assert printed_obj.columns[0].header == "Field"
    assert printed_obj.columns[1].header == "Value"