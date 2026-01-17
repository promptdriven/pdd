import pytest
import asyncio
import datetime
from pathlib import Path
from unittest.mock import MagicMock, patch, AsyncMock
import httpx

# Import the code under test
from pdd.remote_session import (
    RemoteSessionManager,
    SessionInfo,
    CommandInfo,
    RemoteSessionError,
    get_active_session_manager,
    set_active_session_manager,
)
from pdd.core.cloud import CloudConfig

# --- Fixtures ---

@pytest.fixture
def mock_cloud_config():
    """Mock CloudConfig to return predictable URLs."""
    with patch("pdd.remote_session.CloudConfig") as MockConfig:
        MockConfig.get_endpoint_url.side_effect = lambda endpoint: f"https://api.pdd.dev/{endpoint}"
        yield MockConfig

@pytest.fixture
def manager():
    """Fixture for a RemoteSessionManager instance."""
    return RemoteSessionManager(jwt_token="fake-jwt-token", project_path=Path("/app"))

@pytest.fixture
def mock_httpx_client():
    """Mock httpx.AsyncClient context manager."""
    with patch("httpx.AsyncClient") as MockClient:
        mock_instance = AsyncMock()
        MockClient.return_value.__aenter__.return_value = mock_instance
        MockClient.return_value.__aexit__.return_value = None
        yield mock_instance

# --- Global State Tests ---

def test_global_session_manager_accessors():
    """Test get and set active session manager."""
    # Ensure clean state
    original_manager = get_active_session_manager()
    set_active_session_manager(None)

    try:
        assert get_active_session_manager() is None

        mgr = RemoteSessionManager("token", Path("/test"))
        set_active_session_manager(mgr)
        assert get_active_session_manager() is mgr

        set_active_session_manager(None)
        assert get_active_session_manager() is None
    finally:
        # Restore state
        set_active_session_manager(original_manager)

# --- SessionInfo Tests ---

def test_session_info_from_dict_valid():
    """Test parsing a valid dictionary into SessionInfo."""
    data = {
        "sessionId": "sess-123",
        "cloudUrl": "https://pdd.dev/connect/sess-123",
        "projectName": "My Project",
        "projectPath": "/path/to/proj",
        "createdAt": "2023-01-01T12:00:00+00:00",
        "lastHeartbeat": "2023-01-01T12:05:00Z",  # Test Z handling
        "status": "active",
        "metadata": {"os": "linux"}
    }

    info = SessionInfo.from_dict(data)

    assert info.session_id == "sess-123"
    assert info.cloud_url == "https://pdd.dev/connect/sess-123"
    assert info.project_name == "My Project"
    assert info.project_path == "/path/to/proj"
    assert info.created_at.year == 2023
    assert info.last_heartbeat.tzinfo is not None
    assert info.metadata["os"] == "linux"


def test_command_info_from_dict():
    """Test parsing a valid dictionary into CommandInfo."""
    data = {
        "commandId": "cmd-456",
        "type": "generate",
        "payload": {"target": "tests"},
        "status": "pending",
        "createdAt": "2023-01-01T12:00:00Z",
        "response": None
    }

    info = CommandInfo.from_dict(data)

    assert info.command_id == "cmd-456"
    assert info.type == "generate"
    assert info.payload == {"target": "tests"}
    assert info.status == "pending"
    assert info.response is None

def test_session_info_from_dict_defaults():
    """Test parsing a dictionary with missing fields uses defaults."""
    data = {} # Empty dict
    
    info = SessionInfo.from_dict(data)
    
    assert info.session_id == ""
    assert info.project_name == "Unknown Project"
    assert isinstance(info.created_at, datetime.datetime)
    assert info.status == "unknown"
    assert info.metadata == {}

# --- RemoteSessionManager Registration Tests ---

@pytest.mark.asyncio
async def test_register_success(manager, mock_cloud_config, mock_httpx_client):
    """Test successful session registration."""
    # Setup mock response
    mock_response = MagicMock()
    mock_response.status_code = 200
    mock_response.json.return_value = {
        "sessionId": "new-session-id",
        "cloudUrl": "https://pdd.dev/connect/new-session-id"
    }
    mock_httpx_client.post.return_value = mock_response

    # Call register - new API: no public_url, host, port needed
    cloud_url = await manager.register(session_name="Test Session")

    # Assertions
    assert cloud_url == "https://pdd.dev/connect/new-session-id"
    assert manager.session_id == "new-session-id"
    assert manager.cloud_url == "https://pdd.dev/connect/new-session-id"

    # Verify API call
    mock_httpx_client.post.assert_called_once()
    args, kwargs = mock_httpx_client.post.call_args
    assert args[0] == "https://api.pdd.dev/registerSession"
    assert "projectPath" in kwargs["json"]
    assert "metadata" in kwargs["json"]
    assert "Authorization" in kwargs["headers"]

@pytest.mark.asyncio
async def test_register_api_error(manager, mock_cloud_config, mock_httpx_client):
    """Test registration failure due to API error."""
    mock_response = MagicMock()
    mock_response.status_code = 400
    mock_response.text = "Bad Request"
    mock_httpx_client.post.return_value = mock_response

    with pytest.raises(RemoteSessionError) as excinfo:
        await manager.register()

    assert "Failed to register session" in str(excinfo.value)
    assert excinfo.value.status_code == 400


@pytest.mark.asyncio
async def test_register_network_error(manager, mock_cloud_config, mock_httpx_client):
    """Test registration failure due to network exception."""
    mock_httpx_client.post.side_effect = httpx.RequestError("Connection failed")

    with pytest.raises(RemoteSessionError) as excinfo:
        await manager.register()

    assert "Network error" in str(excinfo.value)

# --- RemoteSessionManager Heartbeat Tests ---

@pytest.mark.asyncio
async def test_heartbeat_lifecycle(manager, mock_cloud_config, mock_httpx_client):
    """Test starting and stopping the heartbeat task."""
    manager.session_id = "sess-1"
    
    # Mock wait_for to simulate time passing or event triggering
    # We want the loop to run at least once, then we stop it.
    
    # We'll use a side effect on the client.post to verify it's called
    mock_response = MagicMock()
    mock_response.status_code = 200
    mock_httpx_client.post.return_value = mock_response

    # Start heartbeat
    manager.start_heartbeat()
    assert manager._heartbeat_task is not None
    assert not manager._heartbeat_task.done()

    # Allow the loop to run briefly (asyncio.sleep(0) yields control)
    # Since the loop waits for 60s, we need to ensure we don't actually wait 60s in test.
    # The code uses `asyncio.wait_for(self._stop_event.wait(), timeout=60.0)`.
    # We can trigger the stop event immediately to exit the wait, but that exits the loop.
    # To test the heartbeat logic inside the loop, we rely on the fact that `wait_for` 
    # raises TimeoutError if timeout occurs.
    
    # However, mocking asyncio.wait_for is tricky. 
    # Instead, we can verify that `stop_heartbeat` cancels the task or sets the event.
    
    await manager.stop_heartbeat()
    assert manager._heartbeat_task is None

@pytest.mark.asyncio
async def test_heartbeat_execution_logic(manager, mock_cloud_config, mock_httpx_client):
    """
    Test the internal logic of _heartbeat_loop by invoking it directly
    (or mocking the wait mechanism).
    """
    manager.session_id = "sess-1"
    mock_response = MagicMock()
    mock_response.status_code = 200
    mock_httpx_client.post.return_value = mock_response

    # Create a minimal mock event class that won't produce unawaited coroutine warnings
    class MockEvent:
        def __init__(self):
            self._call_count = 0

        def is_set(self):
            return False  # Always return False so loop continues

        async def wait(self):
            pass

    manager._stop_event = MockEvent()

    # Track iterations
    iteration = [0]
    async def mock_wait_for(coro, timeout):
        coro.close()  # Properly close the coroutine to avoid warnings
        iteration[0] += 1
        if iteration[0] == 1:
            raise asyncio.TimeoutError()  # First: timeout, send heartbeat
        raise asyncio.CancelledError()  # Second: cancel, exit loop

    with patch("asyncio.wait_for", side_effect=mock_wait_for):
        try:
            # Run the loop, it should send one heartbeat then crash/stop on second iteration
            await manager._heartbeat_loop()
        except asyncio.CancelledError:
            pass

    # Verify heartbeat was sent
    mock_httpx_client.post.assert_called()
    args, kwargs = mock_httpx_client.post.call_args
    assert kwargs["json"]["sessionId"] == "sess-1"

@pytest.mark.asyncio
async def test_heartbeat_error_handling(manager, mock_cloud_config, mock_httpx_client):
    """Test that heartbeat errors are logged but don't crash the loop."""
    manager.session_id = "sess-1"

    # First call raises exception, second call works (simulated by stopping loop)
    mock_httpx_client.post.side_effect = Exception("Network blip")

    # Create a minimal mock event class that won't produce unawaited coroutine warnings
    class MockEvent:
        def __init__(self):
            self._call_count = 0

        def is_set(self):
            self._call_count += 1
            # First call returns False (loop continues), second returns True (loop exits)
            return self._call_count > 1

        async def wait(self):
            # This coroutine will be properly awaited or closed by our mock_wait_for
            pass

    manager._stop_event = MockEvent()

    # Patch wait_for to timeout immediately (simulates the 60s wait expiring)
    async def mock_wait_for(coro, timeout):
        # Properly close the coroutine to avoid warnings
        coro.close()
        raise asyncio.TimeoutError()

    with patch("asyncio.wait_for", side_effect=mock_wait_for):
        await manager._heartbeat_loop()

    # Should have attempted post
    mock_httpx_client.post.assert_called()

# --- RemoteSessionManager Deregistration Tests ---

@pytest.mark.asyncio
async def test_deregister_success(manager, mock_cloud_config, mock_httpx_client):
    """Test successful deregistration."""
    manager.session_id = "sess-1"
    manager.start_heartbeat() # Start it so we can verify it stops

    mock_response = MagicMock()
    mock_response.status_code = 200
    mock_httpx_client.post.return_value = mock_response

    await manager.deregister()

    assert manager.session_id is None
    assert manager._heartbeat_task is None # Should be stopped

    mock_httpx_client.post.assert_called_once()
    args, kwargs = mock_httpx_client.post.call_args
    assert args[0] == "https://api.pdd.dev/deregisterSession"
    assert kwargs["json"]["sessionId"] == "sess-1"

@pytest.mark.asyncio
async def test_deregister_idempotent(manager, mock_cloud_config, mock_httpx_client):
    """Test deregister handles errors gracefully (idempotency)."""
    manager.session_id = "sess-1"

    # Simulate API error
    mock_response = MagicMock()
    mock_response.status_code = 500
    mock_httpx_client.post.return_value = mock_response

    # Should not raise exception
    await manager.deregister()

    assert manager.session_id is None # Should still clear local ID

    # Test when session_id is already None
    manager.session_id = None
    mock_httpx_client.post.reset_mock()
    await manager.deregister()
    mock_httpx_client.post.assert_not_called()

# --- RemoteSessionManager List Sessions Tests ---

@pytest.mark.asyncio
async def test_list_sessions_success(mock_cloud_config, mock_httpx_client):
    """Test listing sessions successfully."""
    mock_response = MagicMock()
    mock_response.status_code = 200
    mock_response.json.return_value = {
        "sessions": [
            {
                "sessionId": "s1",
                "cloudUrl": "https://pdd.dev/connect/s1",
                "projectName": "test-project",
                "status": "active"
            }
        ]
    }
    mock_httpx_client.get.return_value = mock_response

    sessions = await RemoteSessionManager.list_sessions("token")

    assert len(sessions) == 1
    assert isinstance(sessions[0], SessionInfo)
    assert sessions[0].session_id == "s1"
    assert sessions[0].cloud_url == "https://pdd.dev/connect/s1"

@pytest.mark.asyncio
async def test_list_sessions_error(mock_cloud_config, mock_httpx_client):
    """Test listing sessions handles API errors."""
    mock_response = MagicMock()
    mock_response.status_code = 401
    mock_response.text = "Unauthorized"
    mock_httpx_client.get.return_value = mock_response

    with pytest.raises(RemoteSessionError) as excinfo:
        await RemoteSessionManager.list_sessions("token")
    
    assert excinfo.value.status_code == 401

# --- Additional Tests for New API ---

@pytest.mark.asyncio
async def test_register_missing_session_id(manager, mock_cloud_config, mock_httpx_client):
    """Test registration fails when cloud response is missing sessionId."""
    mock_response = MagicMock()
    mock_response.status_code = 200
    mock_response.json.return_value = {"cloudUrl": "https://pdd.dev/connect/test"}
    mock_httpx_client.post.return_value = mock_response

    with pytest.raises(RemoteSessionError) as excinfo:
        await manager.register()

    assert "missing sessionId" in str(excinfo.value)


@pytest.mark.asyncio
async def test_register_missing_cloud_url(manager, mock_cloud_config, mock_httpx_client):
    """Test registration fails when cloud response is missing cloudUrl."""
    mock_response = MagicMock()
    mock_response.status_code = 200
    mock_response.json.return_value = {"sessionId": "test-id"}
    mock_httpx_client.post.return_value = mock_response

    with pytest.raises(RemoteSessionError) as excinfo:
        await manager.register()

    assert "missing cloudUrl" in str(excinfo.value)


# --- Tests for Stringified List Parsing ---

class TestStringifiedListParsing:
    """Tests for defensive parsing of stringified arrays in remote commands."""

    def test_parse_stringified_list_basic(self):
        """Test parsing a basic stringified Python list."""
        import ast

        # Replicate the parsing logic from remote_session.py
        def parse_if_stringified_list(value):
            if isinstance(value, str):
                stripped = value.strip()
                if stripped.startswith('[') and stripped.endswith(']'):
                    try:
                        parsed = ast.literal_eval(stripped)
                        if isinstance(parsed, list):
                            return parsed
                    except (ValueError, SyntaxError):
                        pass
            return value

        # Test basic list parsing
        result = parse_if_stringified_list("['PRD_FILE=PRD.md', 'APP_NAME=test']")
        assert result == ['PRD_FILE=PRD.md', 'APP_NAME=test']

    def test_parse_stringified_list_with_whitespace(self):
        """Test parsing stringified list with surrounding whitespace."""
        import ast

        def parse_if_stringified_list(value):
            if isinstance(value, str):
                stripped = value.strip()
                if stripped.startswith('[') and stripped.endswith(']'):
                    try:
                        parsed = ast.literal_eval(stripped)
                        if isinstance(parsed, list):
                            return parsed
                    except (ValueError, SyntaxError):
                        pass
            return value

        result = parse_if_stringified_list("  ['a', 'b']  ")
        assert result == ['a', 'b']

    def test_parse_stringified_list_returns_original_on_invalid(self):
        """Test that invalid strings are returned unchanged."""
        import ast

        def parse_if_stringified_list(value):
            if isinstance(value, str):
                stripped = value.strip()
                if stripped.startswith('[') and stripped.endswith(']'):
                    try:
                        parsed = ast.literal_eval(stripped)
                        if isinstance(parsed, list):
                            return parsed
                    except (ValueError, SyntaxError):
                        pass
            return value

        # Invalid JSON/Python literal
        result = parse_if_stringified_list("[invalid syntax")
        assert result == "[invalid syntax"

        # Not a list at all
        result = parse_if_stringified_list("just a string")
        assert result == "just a string"

        # Empty brackets but malformed
        result = parse_if_stringified_list("[}")
        assert result == "[}"

    def test_parse_stringified_list_non_string_passthrough(self):
        """Test that non-string values pass through unchanged."""
        import ast

        def parse_if_stringified_list(value):
            if isinstance(value, str):
                stripped = value.strip()
                if stripped.startswith('[') and stripped.endswith(']'):
                    try:
                        parsed = ast.literal_eval(stripped)
                        if isinstance(parsed, list):
                            return parsed
                    except (ValueError, SyntaxError):
                        pass
            return value

        # Already a list
        result = parse_if_stringified_list(['a', 'b'])
        assert result == ['a', 'b']

        # Integer
        result = parse_if_stringified_list(42)
        assert result == 42

        # None
        result = parse_if_stringified_list(None)
        assert result is None


# --- Tests for CLI Command Building with Lists ---

class TestCLICommandBuildingWithLists:
    """Tests for CLI command string building with list values."""

    def test_build_cli_with_list_options(self):
        """Test that list values produce multiple --flag entries."""
        # Simulate the CLI building logic from remote_session.py
        cmd_options = {
            'env': ['PRD_FILE=PRD.md', 'APP_NAME=test'],
            'output': 'architecture.json',
            'verbose': True,
        }

        cli_parts = ["pdd", "generate"]
        for key, value in cmd_options.items():
            if isinstance(value, bool):
                if value:
                    cli_parts.append(f"--{key}")
            elif isinstance(value, (list, tuple)):
                for v in value:
                    cli_parts.append(f"--{key} {v}")
            else:
                cli_parts.append(f"--{key} {value}")

        cli_command = " ".join(cli_parts)

        # Should have --env for each item
        assert "--env PRD_FILE=PRD.md" in cli_command
        assert "--env APP_NAME=test" in cli_command
        assert "--output architecture.json" in cli_command
        assert "--verbose" in cli_command

    def test_build_cli_with_empty_list(self):
        """Test that empty lists produce no flags."""
        cmd_options = {
            'env': [],
            'output': 'test.json',
        }

        cli_parts = ["pdd", "generate"]
        for key, value in cmd_options.items():
            if isinstance(value, bool):
                if value:
                    cli_parts.append(f"--{key}")
            elif isinstance(value, (list, tuple)):
                for v in value:
                    cli_parts.append(f"--{key} {v}")
            else:
                cli_parts.append(f"--{key} {value}")

        cli_command = " ".join(cli_parts)

        # Should not have --env at all
        assert "--env" not in cli_command
        assert "--output test.json" in cli_command

    def test_build_cli_with_tuple_options(self):
        """Test that tuple values also work like lists."""
        cmd_options = {
            'env': ('KEY1=val1', 'KEY2=val2'),
        }

        cli_parts = ["pdd", "generate"]
        for key, value in cmd_options.items():
            if isinstance(value, bool):
                if value:
                    cli_parts.append(f"--{key}")
            elif isinstance(value, (list, tuple)):
                for v in value:
                    cli_parts.append(f"--{key} {v}")
            else:
                cli_parts.append(f"--{key} {value}")

        cli_command = " ".join(cli_parts)

        assert "--env KEY1=val1" in cli_command
        assert "--env KEY2=val2" in cli_command