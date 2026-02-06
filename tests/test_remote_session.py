import os
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
def manager_custom_port():
    """Fixture for a RemoteSessionManager instance with custom port."""
    return RemoteSessionManager(jwt_token="fake-jwt-token", project_path=Path("/app"), server_port=9999)

@pytest.fixture
def mock_httpx_client():
    """Mock httpx.AsyncClient context manager."""
    with patch("httpx.AsyncClient") as MockClient:
        mock_instance = AsyncMock()
        # Properly mock the async context manager
        mock_client_cm = MagicMock()
        mock_client_cm.__aenter__ = AsyncMock(return_value=mock_instance)
        mock_client_cm.__aexit__ = AsyncMock(return_value=None)
        MockClient.return_value = mock_client_cm
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
    """Test successful deregistration returns True."""
    manager.session_id = "sess-1"
    manager.start_heartbeat() # Start it so we can verify it stops

    mock_response = MagicMock()
    mock_response.status_code = 200
    mock_httpx_client.post.return_value = mock_response

    result = await manager.deregister()

    assert result is True
    assert manager.session_id is None
    assert manager._heartbeat_task is None # Should be stopped

    mock_httpx_client.post.assert_called_once()
    args, kwargs = mock_httpx_client.post.call_args
    assert args[0] == "https://api.pdd.dev/deregisterSession"
    assert kwargs["json"]["sessionId"] == "sess-1"

@pytest.mark.asyncio
async def test_deregister_http_error_returns_false(manager, mock_cloud_config, mock_httpx_client):
    """Test deregister returns False on HTTP error status (e.g. 500).

    See: https://github.com/promptdriven/pdd/issues/469
    """
    manager.session_id = "sess-1"

    mock_response = MagicMock()
    mock_response.status_code = 500
    mock_httpx_client.post.return_value = mock_response

    result = await manager.deregister()

    assert result is False
    assert manager.session_id is None  # Still clears local ID

@pytest.mark.asyncio
async def test_deregister_network_exception_returns_false(manager, mock_cloud_config, mock_httpx_client):
    """Test deregister returns False on network exception without raising.

    See: https://github.com/promptdriven/pdd/issues/469
    """
    manager.session_id = "sess-1"

    mock_httpx_client.post.side_effect = Exception("Connection refused")

    result = await manager.deregister()

    assert result is False
    assert manager.session_id is None  # Still clears local ID

@pytest.mark.asyncio
async def test_deregister_no_session_returns_true(manager, mock_cloud_config, mock_httpx_client):
    """Test deregister returns True when no session_id is set (no-op)."""
    manager.session_id = None
    mock_httpx_client.post.reset_mock()

    result = await manager.deregister()

    assert result is True
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


# --- Tests for Server Port Configuration ---

class TestServerPortConfiguration:
    """Tests for configurable server port in RemoteSessionManager."""

    def test_default_port(self, manager):
        """Test that default port is 9876."""
        assert manager.server_port == 9876

    def test_custom_port(self, manager_custom_port):
        """Test that custom port is correctly set."""
        assert manager_custom_port.server_port == 9999

    @pytest.mark.asyncio
    async def test_do_execute_uses_custom_port(self, manager_custom_port, mock_cloud_config, mock_httpx_client):
        """Test that _do_execute uses the configured port."""
        # Setup mock response for command submission
        mock_submit_response = MagicMock()
        mock_submit_response.status_code = 200
        mock_submit_response.json.return_value = {"job_id": "test-job-123"}

        # Setup mock response for job status polling
        mock_status_response = MagicMock()
        mock_status_response.status_code = 200
        mock_status_response.json.return_value = {
            "status": "completed",
            "result": {"stdout": "test output", "stderr": "", "exit_code": 0}
        }

        # Setup mock responses in order: submit, status poll
        mock_httpx_client.post.return_value = mock_submit_response
        mock_httpx_client.get.return_value = mock_status_response

        # Create a test command
        cmd = CommandInfo(
            command_id="cmd-123",
            type="generate",
            payload={"args": {"prompt_file": "test.prompt"}, "options": {}},
            status="pending",
            created_at=datetime.datetime.now(datetime.timezone.utc),
        )

        # Mock _is_cancelled to return False
        with patch.object(manager_custom_port, '_is_cancelled', new_callable=AsyncMock) as mock_cancelled:
            mock_cancelled.return_value = False

            # Execute the command
            job_id, response = await manager_custom_port._do_execute(cmd)

        # Verify the submit call was made to the custom port
        submit_call = mock_httpx_client.post.call_args_list[0]
        assert "http://127.0.0.1:9999" in submit_call[0][0]

    @pytest.mark.asyncio
    async def test_cancel_local_job_uses_custom_port(self, manager_custom_port, mock_httpx_client):
        """Test that _cancel_local_job uses the configured port."""
        mock_response = MagicMock()
        mock_response.status_code = 200
        mock_response.json.return_value = {"cancelled": True}
        mock_httpx_client.post.return_value = mock_response

        result = await manager_custom_port._cancel_local_job("test-job-123")

        # Verify the cancel call was made to the custom port
        cancel_call = mock_httpx_client.post.call_args
        assert "http://127.0.0.1:9999" in cancel_call[0][0]
        assert result is True

    def test_manager_initialization_with_all_params(self):
        """Test RemoteSessionManager initializes correctly with all parameters."""
        mgr = RemoteSessionManager(
            jwt_token="test-token",
            project_path=Path("/test/path"),
            server_port=8080
        )
        assert mgr.jwt_token == "test-token"
        assert mgr.project_path == Path("/test/path")
        assert mgr.server_port == 8080
        assert mgr.session_id is None
        assert mgr.cloud_url is None


# --- Tests for Heartbeat Bug Fixes (Issue #363) ---

class TestHeartbeatImmediateFirstBeat:
    """
    Tests for Bug Fix #1: First heartbeat should be sent immediately on startup,
    not after a 60-second delay which could cause the cloud session to timeout.
    """

    @pytest.mark.asyncio
    async def test_first_heartbeat_sent_immediately(self, manager, mock_cloud_config, mock_httpx_client):
        """
        Test that the first heartbeat is sent immediately when the loop starts,
        before waiting for any interval.
        """
        manager.session_id = "sess-1"
        mock_response = MagicMock()
        mock_response.status_code = 200
        mock_httpx_client.post.return_value = mock_response

        # Track when heartbeats are sent
        heartbeat_times = []

        async def tracking_post(*args, **kwargs):
            heartbeat_times.append(asyncio.get_event_loop().time())
            return mock_response

        mock_httpx_client.post.side_effect = tracking_post

        # Create stop event that will be set after first heartbeat
        manager._stop_event = asyncio.Event()

        iteration = [0]

        async def mock_wait_for(coro, timeout):
            coro.close()
            iteration[0] += 1
            if iteration[0] == 1:
                # After first heartbeat, stop the loop
                raise asyncio.CancelledError()
            raise asyncio.TimeoutError()

        with patch("asyncio.wait_for", side_effect=mock_wait_for):
            try:
                await manager._heartbeat_loop()
            except asyncio.CancelledError:
                pass

        # Verify heartbeat was called (first call should be immediate, before wait_for)
        assert mock_httpx_client.post.call_count >= 1

    @pytest.mark.asyncio
    async def test_heartbeat_interval_is_30_seconds(self, manager, mock_cloud_config):
        """
        Test that heartbeat interval is 30 seconds (not 60) after the first heartbeat.
        """
        manager.session_id = "sess-1"
        manager._stop_event = asyncio.Event()

        captured_timeouts = []

        async def capture_wait_for(coro, timeout):
            captured_timeouts.append(timeout)
            coro.close()
            if len(captured_timeouts) >= 2:
                raise asyncio.CancelledError()
            raise asyncio.TimeoutError()

        with patch("asyncio.wait_for", side_effect=capture_wait_for):
            with patch("httpx.AsyncClient") as MockClient:
                mock_instance = AsyncMock()
                mock_response = MagicMock()
                mock_response.status_code = 200
                mock_instance.post.return_value = mock_response
                MockClient.return_value.__aenter__.return_value = mock_instance
                MockClient.return_value.__aexit__.return_value = None

                try:
                    await manager._heartbeat_loop()
                except asyncio.CancelledError:
                    pass

        # First interval should be 5 seconds (quick establishment)
        # Second interval should be 30 seconds (normal interval)
        assert len(captured_timeouts) >= 1
        assert captured_timeouts[0] == 5.0  # First interval is short
        if len(captured_timeouts) >= 2:
            assert captured_timeouts[1] == 30.0  # Subsequent intervals are 30s


class TestHeartbeatRetryLogic:
    """
    Tests for Bug Fix #2: Heartbeat should retry on failure with exponential backoff,
    not silently skip the heartbeat which could cause session disconnection.
    """

    @pytest.mark.asyncio
    async def test_heartbeat_retries_on_network_error(self, manager, mock_cloud_config, mock_httpx_client):
        """
        Test that heartbeat retries up to 3 times on network errors.
        """
        manager.session_id = "sess-1"
        manager._stop_event = asyncio.Event()

        # Track retry attempts
        attempt_count = [0]

        async def failing_post(*args, **kwargs):
            attempt_count[0] += 1
            if attempt_count[0] < 3:
                raise Exception("Network error")
            # Third attempt succeeds
            mock_response = MagicMock()
            mock_response.status_code = 200
            return mock_response

        mock_httpx_client.post = AsyncMock(side_effect=failing_post)

        iteration = [0]

        async def mock_wait_for(coro, timeout):
            coro.close()
            iteration[0] += 1
            if iteration[0] >= 1:
                raise asyncio.CancelledError()
            raise asyncio.TimeoutError()

        with patch("asyncio.wait_for", side_effect=mock_wait_for):
            try:
                await manager._heartbeat_loop()
            except asyncio.CancelledError:
                pass

        # Should have retried 3 times
        assert attempt_count[0] == 3

    @pytest.mark.asyncio
    async def test_heartbeat_exponential_backoff(self, manager, mock_cloud_config, mock_httpx_client):
        """
        Test that heartbeat uses exponential backoff between retries.
        """
        manager.session_id = "sess-1"
        manager._stop_event = asyncio.Event()

        sleep_times = []

        original_sleep = asyncio.sleep

        async def tracking_sleep(delay):
            sleep_times.append(delay)
            # Don't actually sleep in tests

        # Make all attempts fail to trigger retries
        mock_httpx_client.post = AsyncMock(side_effect=Exception("Network error"))

        iteration = [0]

        async def mock_wait_for(coro, timeout):
            coro.close()
            iteration[0] += 1
            if iteration[0] >= 1:
                raise asyncio.CancelledError()
            raise asyncio.TimeoutError()

        with patch("asyncio.wait_for", side_effect=mock_wait_for):
            with patch("asyncio.sleep", side_effect=tracking_sleep):
                try:
                    await manager._heartbeat_loop()
                except asyncio.CancelledError:
                    pass

        # Should have sleep times with exponential backoff: 1.0, 2.0
        # (3 attempts = 2 sleeps between them)
        assert len(sleep_times) == 2
        assert sleep_times[0] == 1.0
        assert sleep_times[1] == 2.0


class TestJWTTokenRefresh:
    """
    Tests for Bug Fix #3: Automatic JWT token refresh on 401 errors.
    This prevents session disconnection when the JWT token expires (~1 hour).
    """

    @pytest.mark.asyncio
    async def test_heartbeat_refreshes_token_on_401(self, manager, mock_cloud_config, mock_httpx_client):
        """
        Test that heartbeat attempts to refresh token when receiving 401.
        """
        manager.session_id = "sess-1"
        manager._stop_event = asyncio.Event()

        call_count = [0]

        async def mock_post(*args, **kwargs):
            call_count[0] += 1
            mock_response = MagicMock()
            if call_count[0] == 1:
                # First call returns 401 (token expired)
                mock_response.status_code = 401
            else:
                # After refresh, succeed
                mock_response.status_code = 200
            return mock_response

        mock_httpx_client.post.side_effect = mock_post

        # Mock successful token refresh
        refresh_called = [False]

        async def mock_refresh_token():
            refresh_called[0] = True
            manager.jwt_token = "new-token"
            return True

        manager._refresh_token = AsyncMock(side_effect=mock_refresh_token)

        iteration = [0]

        async def mock_wait_for(coro, timeout):
            coro.close()
            iteration[0] += 1
            if iteration[0] >= 1:
                raise asyncio.CancelledError()
            raise asyncio.TimeoutError()

        with patch("asyncio.wait_for", side_effect=mock_wait_for):
            try:
                await manager._heartbeat_loop()
            except asyncio.CancelledError:
                pass

        # Token refresh should have been called
        assert refresh_called[0] is True
        # Should have retried after refresh
        assert call_count[0] >= 2

    @pytest.mark.asyncio
    async def test_heartbeat_only_refreshes_once_per_cycle(self, manager, mock_cloud_config, mock_httpx_client):
        """
        Test that heartbeat only attempts token refresh once per heartbeat cycle,
        not repeatedly if refresh fails.
        """
        manager.session_id = "sess-1"
        manager._stop_event = asyncio.Event()

        # Always return 401
        mock_response = MagicMock()
        mock_response.status_code = 401
        mock_httpx_client.post.return_value = mock_response

        refresh_count = [0]

        async def mock_refresh_token():
            refresh_count[0] += 1
            return False  # Refresh fails

        manager._refresh_token = AsyncMock(side_effect=mock_refresh_token)

        iteration = [0]

        async def mock_wait_for(coro, timeout):
            coro.close()
            iteration[0] += 1
            if iteration[0] >= 1:
                raise asyncio.CancelledError()
            raise asyncio.TimeoutError()

        with patch("asyncio.wait_for", side_effect=mock_wait_for):
            try:
                await manager._heartbeat_loop()
            except asyncio.CancelledError:
                pass

        # Token refresh should only be called once per heartbeat cycle
        assert refresh_count[0] == 1

    @pytest.mark.asyncio
    async def test_refresh_token_updates_jwt(self, manager):
        """
        Test that _refresh_token method correctly updates the jwt_token.
        """
        import os

        original_token = manager.jwt_token
        new_token = "new-refreshed-token"

        # Mock the Firebase authenticator
        with patch.dict(os.environ, {"NEXT_PUBLIC_FIREBASE_API_KEY": "test-api-key"}):
            with patch("pdd.remote_session.KEYRING_AVAILABLE", True):
                with patch("pdd.remote_session.FirebaseAuthenticator") as MockAuth:
                    mock_auth_instance = MagicMock()
                    mock_auth_instance._get_stored_refresh_token.return_value = "refresh-token"
                    mock_auth_instance._refresh_firebase_token = AsyncMock(return_value=new_token)
                    MockAuth.return_value = mock_auth_instance

                    with patch("pdd.remote_session._get_cached_jwt", return_value=None):
                        with patch("pdd.get_jwt_token._cache_jwt"):
                            result = await manager._refresh_token()

        assert result is True
        assert manager.jwt_token == new_token

    @pytest.mark.asyncio
    async def test_refresh_token_returns_false_on_failure(self, manager):
        """
        Test that _refresh_token returns False when refresh fails.
        """
        import os

        with patch.dict(os.environ, {"NEXT_PUBLIC_FIREBASE_API_KEY": "test-api-key"}):
            with patch("pdd.remote_session.KEYRING_AVAILABLE", True):
                with patch("pdd.remote_session.FirebaseAuthenticator") as MockAuth:
                    mock_auth_instance = MagicMock()
                    mock_auth_instance._get_stored_refresh_token.return_value = "refresh-token"
                    mock_auth_instance._refresh_firebase_token = AsyncMock(
                        side_effect=Exception("Refresh failed")
                    )
                    MockAuth.return_value = mock_auth_instance

                    with patch("pdd.remote_session._get_cached_jwt", return_value=None):
                        result = await manager._refresh_token()

        assert result is False

    @pytest.mark.asyncio
    async def test_refresh_token_uses_cached_token_if_available(self, manager):
        """
        Test that _refresh_token uses cached token if another coroutine already refreshed.
        """
        original_token = manager.jwt_token
        cached_new_token = "already-refreshed-token"

        with patch("pdd.remote_session._get_cached_jwt", return_value=cached_new_token):
            result = await manager._refresh_token()

        assert result is True
        assert manager.jwt_token == cached_new_token


class TestGetPendingCommands401Handling:
    """
    Tests for get_pending_commands 401 handling with automatic token refresh.
    """

    @pytest.mark.asyncio
    async def test_get_pending_commands_refreshes_token_on_401(
        self, manager, mock_cloud_config, mock_httpx_client
    ):
        """
        Test that get_pending_commands refreshes token on 401 and retries.
        """
        manager.session_id = "sess-1"

        call_count = [0]

        async def mock_get(*args, **kwargs):
            call_count[0] += 1
            mock_response = MagicMock()
            if call_count[0] == 1:
                mock_response.status_code = 401
            else:
                mock_response.status_code = 200
                mock_response.json.return_value = {"commands": []}
            return mock_response

        mock_httpx_client.get = AsyncMock(side_effect=mock_get)

        refresh_called = [False]

        async def mock_refresh_token():
            refresh_called[0] = True
            manager.jwt_token = "new-token"
            return True

        manager._refresh_token = mock_refresh_token

        commands = await manager.get_pending_commands()

        assert refresh_called[0] is True
        assert call_count[0] == 2
        assert commands == []

    @pytest.mark.asyncio
    async def test_get_pending_commands_returns_empty_on_refresh_failure(
        self, manager, mock_cloud_config, mock_httpx_client
    ):
        """
        Test that get_pending_commands returns empty list if refresh fails.
        """
        manager.session_id = "sess-1"

        mock_response = MagicMock()
        mock_response.status_code = 401
        mock_httpx_client.get = AsyncMock(return_value=mock_response)

        async def mock_refresh_token():
            return False  # Refresh fails

        manager._refresh_token = mock_refresh_token

        commands = await manager.get_pending_commands()

        assert commands == []

    @pytest.mark.asyncio
    async def test_get_pending_commands_only_refreshes_once(
        self, manager, mock_cloud_config, mock_httpx_client
    ):
        """
        Test that get_pending_commands only attempts refresh once per call.
        """
        manager.session_id = "sess-1"

        # Always return 401
        mock_response = MagicMock()
        mock_response.status_code = 401
        mock_httpx_client.get = AsyncMock(return_value=mock_response)

        refresh_count = [0]

        async def mock_refresh_token():
            refresh_count[0] += 1
            manager.jwt_token = "new-token"
            return True

        manager._refresh_token = mock_refresh_token

        commands = await manager.get_pending_commands()

        # Should only refresh once, even if second attempt also returns 401
        assert refresh_count[0] == 1
        assert commands == []


class TestUpdateCommand401Handling:
    """
    Tests for update_command 401 handling with automatic token refresh.
    This is the root cause of the "stuck running" bug - update_command
    doesn't refresh token on 401, so final status update fails.
    """

    @pytest.mark.asyncio
    async def test_update_command_refreshes_token_on_401(
        self, manager, mock_cloud_config, mock_httpx_client
    ):
        """
        Test that update_command refreshes token on 401 and retries.
        """
        manager.session_id = "sess-1"

        call_count = [0]

        async def mock_post(*args, **kwargs):
            call_count[0] += 1
            mock_response = MagicMock()
            if call_count[0] == 1:
                mock_response.status_code = 401
            else:
                mock_response.status_code = 200
                mock_response.json.return_value = {"success": True}
            return mock_response

        mock_httpx_client.post = AsyncMock(side_effect=mock_post)

        refresh_called = [False]

        async def mock_refresh_token():
            refresh_called[0] = True
            manager.jwt_token = "new-token"
            return True

        manager._refresh_token = mock_refresh_token

        await manager.update_command("cmd-123", status="completed")

        assert refresh_called[0] is True
        assert call_count[0] == 2

    @pytest.mark.asyncio
    async def test_update_command_raises_on_refresh_failure(
        self, manager, mock_cloud_config, mock_httpx_client
    ):
        """
        Test that update_command raises RuntimeError if token refresh fails.
        """
        manager.session_id = "sess-1"

        mock_response = MagicMock()
        mock_response.status_code = 401
        mock_response.text = "Unauthorized"
        mock_httpx_client.post = AsyncMock(return_value=mock_response)

        async def mock_refresh_token():
            return False  # Refresh fails

        manager._refresh_token = mock_refresh_token

        with pytest.raises(RuntimeError, match="token expired"):
            await manager.update_command("cmd-123", status="completed")

    @pytest.mark.asyncio
    async def test_update_command_raises_if_401_persists_after_refresh(
        self, manager, mock_cloud_config, mock_httpx_client
    ):
        """
        Test that update_command raises if 401 persists after token refresh.
        """
        manager.session_id = "sess-1"

        # Always return 401
        mock_response = MagicMock()
        mock_response.status_code = 401
        mock_response.text = "Unauthorized"
        mock_httpx_client.post = AsyncMock(return_value=mock_response)

        async def mock_refresh_token():
            manager.jwt_token = "new-token"
            return True  # Refresh succeeds but 401 persists

        manager._refresh_token = mock_refresh_token

        with pytest.raises(RuntimeError, match="after token refresh"):
            await manager.update_command("cmd-123", status="completed")

    @pytest.mark.asyncio
    async def test_update_command_only_refreshes_once(
        self, manager, mock_cloud_config, mock_httpx_client
    ):
        """
        Test that update_command only attempts refresh once per call.
        """
        manager.session_id = "sess-1"

        mock_response = MagicMock()
        mock_response.status_code = 401
        mock_response.text = "Unauthorized"
        mock_httpx_client.post = AsyncMock(return_value=mock_response)

        refresh_count = [0]

        async def mock_refresh_token():
            refresh_count[0] += 1
            manager.jwt_token = "new-token"
            return True

        manager._refresh_token = mock_refresh_token

        with pytest.raises(RuntimeError):
            await manager.update_command("cmd-123", status="completed")

        assert refresh_count[0] == 1


# --- Bug #470: Incorrect auth command reference in error messages ---

class TestIssue470AuthCommandReferences:
    """
    Tests for Issue #470: Verify all auth error messages in remote_session.py
    reference 'pdd auth login', not the non-existent 'pdd login'.
    """

    @pytest.mark.asyncio
    async def test_refresh_token_no_refresh_token_shows_correct_command(
        self, manager
    ):
        """
        Test that _refresh_token references 'pdd auth login' when no refresh token
        is stored. This covers remote_session.py line 199.
        """
        with patch("pdd.remote_session._get_cached_jwt", return_value=None), \
             patch.dict(os.environ, {"NEXT_PUBLIC_FIREBASE_API_KEY": "test-key"}), \
             patch("pdd.remote_session.KEYRING_AVAILABLE", True), \
             patch("pdd.remote_session.FirebaseAuthenticator") as mock_auth, \
             patch("pdd.remote_session.console") as mock_console:
            mock_instance = MagicMock()
            mock_instance._get_stored_refresh_token.return_value = None
            mock_auth.return_value = mock_instance

            result = await manager._refresh_token()

            assert result is False
            # Check that at least one console.print call contains 'pdd auth login'
            printed = " ".join(str(c) for c in mock_console.print.call_args_list)
            assert "pdd auth login" in printed, (
                "refresh_token error should reference 'pdd auth login', "
                f"not 'pdd login'. Got: {printed}"
            )

    @pytest.mark.asyncio
    async def test_heartbeat_token_refresh_failure_shows_correct_command(
        self, manager, mock_cloud_config, mock_httpx_client
    ):
        """
        Test that heartbeat loop references 'pdd auth login' when token refresh
        fails. This covers remote_session.py line 317.
        """
        manager.session_id = "sess-1"

        mock_response = MagicMock()
        mock_response.status_code = 401
        mock_response.text = "Unauthorized"
        mock_httpx_client.post = AsyncMock(return_value=mock_response)

        async def mock_refresh_fail():
            return False

        manager._refresh_token = mock_refresh_fail

        # Set up stop event so heartbeat exits after one iteration
        manager._stop_event = asyncio.Event()

        with patch("pdd.remote_session.console") as mock_console:
            # Run heartbeat in a task with a timeout
            try:
                await asyncio.wait_for(manager._heartbeat_loop(), timeout=5.0)
            except (asyncio.TimeoutError, Exception):
                pass

            printed = " ".join(str(c) for c in mock_console.print.call_args_list)
            assert "pdd auth login" in printed, (
                "Heartbeat token refresh failure should reference 'pdd auth login', "
                f"not 'pdd login'. Got: {printed}"
            )

    @pytest.mark.asyncio
    async def test_update_command_token_refresh_failure_shows_correct_command(
        self, manager, mock_cloud_config, mock_httpx_client
    ):
        """
        Test that update_command references 'pdd auth login' when token refresh
        fails. This covers remote_session.py line 509.
        """
        manager.session_id = "sess-1"

        mock_response = MagicMock()
        mock_response.status_code = 401
        mock_response.text = "Unauthorized"
        mock_httpx_client.post = AsyncMock(return_value=mock_response)

        async def mock_refresh_fail():
            return False

        manager._refresh_token = mock_refresh_fail

        with patch("pdd.remote_session.console") as mock_console:
            with pytest.raises(RuntimeError):
                await manager.update_command("cmd-123", status="completed")

            printed = " ".join(str(c) for c in mock_console.print.call_args_list)
            assert "pdd auth login" in printed, (
                "update_command token refresh failure should reference 'pdd auth login', "
                f"not 'pdd login'. Got: {printed}"
            )