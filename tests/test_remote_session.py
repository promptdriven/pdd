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

    # We patch asyncio.wait_for to raise TimeoutError immediately, simulating the 60s timer expiring
    with patch("asyncio.wait_for", side_effect=[asyncio.TimeoutError(), asyncio.CancelledError()]):
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

    # Initialize the stop event before patching
    manager._stop_event = asyncio.Event()

    # We want the loop to run once (fail) then stop.
    # We can set the stop event from within the side effect or just run one iteration logic.

    # Let's just test the inner logic block manually to avoid infinite loops in tests
    # if we can't easily control the while loop.
    # Alternatively, we can patch `_stop_event.is_set` to return False once then True.

    with patch.object(manager._stop_event, "is_set", side_effect=[False, True]):
        with patch("asyncio.wait_for", side_effect=asyncio.TimeoutError()):
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