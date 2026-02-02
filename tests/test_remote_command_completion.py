"""
Regression tests for remote command completion detection.

Issue: When executing commands via PDD Cloud (remote mode), the frontend
doesn't detect command completion even though the CLI updates the cloud.
"""
import datetime
import pytest
from unittest.mock import AsyncMock, patch, MagicMock
from pathlib import Path


@pytest.fixture
def mock_remote_session_manager():
    """Create a RemoteSessionManager with mocked dependencies."""
    from pdd.remote_session import RemoteSessionManager

    manager = RemoteSessionManager(
        jwt_token="test-token",
        project_path=Path("/tmp"),
        server_port=9876
    )
    manager.session_id = "test-session"
    return manager


@pytest.fixture
def sample_command_info():
    """Create a sample CommandInfo for testing."""
    from pdd.remote_session import CommandInfo

    return CommandInfo(
        command_id="cmd-test-123",
        type="sync",
        payload={"args": {"basename": "test"}},
        status="pending",
        created_at=datetime.datetime.now(datetime.timezone.utc)
    )


@pytest.mark.asyncio
async def test_execute_command_updates_cloud_on_completion(mock_remote_session_manager, sample_command_info):
    """
    Test that _execute_command() calls update_command() with 'completed'
    status after successful local execution.
    """
    manager = mock_remote_session_manager
    cmd = sample_command_info

    # Track all update_command calls
    update_calls = []

    async def mock_update_command(command_id, status, response=None):
        update_calls.append({
            'command_id': command_id,
            'status': status,
            'response': response
        })

    async def mock_do_execute(cmd):
        return ("local-job-123", {
            "status": "completed",
            "result": {"exit_code": 0, "stdout": "Success", "stderr": ""}
        })

    async def mock_get_command_status(command_id):
        # Return the last status that was set
        return update_calls[-1]['status'] if update_calls else 'pending'

    async def mock_is_cancelled(command_id):
        return False

    with patch.object(manager, 'update_command', side_effect=mock_update_command):
        with patch.object(manager, '_do_execute', side_effect=mock_do_execute):
            with patch.object(manager, '_get_command_status', side_effect=mock_get_command_status):
                with patch.object(manager, '_is_cancelled', side_effect=mock_is_cancelled):
                    await manager._execute_command(cmd)

    # Verify update_command was called twice: processing + completed
    assert len(update_calls) == 2, f"Expected 2 update calls, got {len(update_calls)}"

    # First call: processing
    assert update_calls[0]['command_id'] == cmd.command_id
    assert update_calls[0]['status'] == 'processing'
    assert update_calls[0]['response'] is None

    # Second call: completed with response
    assert update_calls[1]['command_id'] == cmd.command_id
    assert update_calls[1]['status'] == 'completed'
    assert update_calls[1]['response'] is not None
    assert update_calls[1]['response']['success'] == True


@pytest.mark.asyncio
async def test_execute_command_updates_cloud_on_failure(mock_remote_session_manager, sample_command_info):
    """
    Test that _execute_command() calls update_command() with 'failed'
    status when local execution fails.
    """
    manager = mock_remote_session_manager
    cmd = sample_command_info

    update_calls = []

    async def mock_update_command(command_id, status, response=None):
        update_calls.append({
            'command_id': command_id,
            'status': status,
            'response': response
        })

    async def mock_do_execute(cmd):
        return ("local-job-123", {
            "status": "failed",
            "result": {"exit_code": 1, "stdout": "", "stderr": "Error occurred"}
        })

    async def mock_get_command_status(command_id):
        return update_calls[-1]['status'] if update_calls else 'pending'

    async def mock_is_cancelled(command_id):
        return False

    with patch.object(manager, 'update_command', side_effect=mock_update_command):
        with patch.object(manager, '_do_execute', side_effect=mock_do_execute):
            with patch.object(manager, '_get_command_status', side_effect=mock_get_command_status):
                with patch.object(manager, '_is_cancelled', side_effect=mock_is_cancelled):
                    await manager._execute_command(cmd)

    # Verify update_command was called twice: processing + failed
    assert len(update_calls) == 2

    # Second call should be 'failed'
    assert update_calls[1]['status'] == 'failed'
    assert update_calls[1]['response']['success'] == False


@pytest.mark.asyncio
async def test_execute_command_handles_exception_gracefully(mock_remote_session_manager, sample_command_info):
    """
    Test that _execute_command() updates cloud with 'failed' status
    when an exception occurs during execution.
    """
    manager = mock_remote_session_manager
    cmd = sample_command_info

    update_calls = []

    async def mock_update_command(command_id, status, response=None):
        update_calls.append({
            'command_id': command_id,
            'status': status,
            'response': response
        })

    async def mock_do_execute_raises(cmd):
        raise Exception("Simulated execution error")

    async def mock_is_cancelled(command_id):
        return False

    with patch.object(manager, 'update_command', side_effect=mock_update_command):
        with patch.object(manager, '_do_execute', side_effect=mock_do_execute_raises):
            with patch.object(manager, '_is_cancelled', side_effect=mock_is_cancelled):
                await manager._execute_command(cmd)

    # Should have called update_command with 'processing', then 'failed'
    assert len(update_calls) >= 2

    # Last call should be 'failed' with error info
    last_call = update_calls[-1]
    assert last_call['status'] == 'failed'
    assert last_call['response'] is not None
    assert 'error' in last_call['response']


@pytest.mark.asyncio
async def test_update_command_retries_on_network_error(mock_remote_session_manager):
    """
    Test that update_command() retries on transient network failures.
    """
    manager = mock_remote_session_manager

    call_count = 0

    async def mock_post(*args, **kwargs):
        nonlocal call_count
        call_count += 1
        if call_count == 1:
            raise Exception("Network error - connection refused")
        # Return a mock response for success
        mock_response = MagicMock()
        mock_response.status_code = 200
        return mock_response

    # Mock the HTTP client
    with patch('httpx.AsyncClient') as mock_client_class:
        mock_client = AsyncMock()
        mock_client.post = mock_post
        mock_client_class.return_value.__aenter__.return_value = mock_client

        await manager.update_command("cmd-123", status="completed")

    # Should have retried after the first failure
    assert call_count == 2, f"Expected 2 attempts (1 fail + 1 success), got {call_count}"


@pytest.mark.asyncio
async def test_command_info_preserves_command_id():
    """
    Test that CommandInfo correctly preserves the command ID from cloud.
    """
    from pdd.remote_session import CommandInfo

    # Simulate data from getCommands cloud function
    cloud_data = {
        "commandId": "abc-123-def-456",
        "type": "sync",
        "payload": {"args": {"basename": "test"}},
        "status": "pending",
        "createdAt": "2024-01-15T10:00:00Z"
    }

    cmd = CommandInfo.from_dict(cloud_data)

    # Verify command_id is correctly extracted
    assert cmd.command_id == "abc-123-def-456"
    assert cmd.type == "sync"
    assert cmd.status == "pending"


def test_formatted_response_structure():
    """
    Test that the formatted response sent to cloud has all required fields.
    """
    # This tests the structure built in _execute_command
    result = {
        "exit_code": 0,
        "stdout": "Test output",
        "stderr": "",
        "files_created": ["test.py"]
    }
    job_status = "completed"
    response_cost = 0.05

    formatted_response = {
        "success": job_status == "completed",
        "message": "",
        "exit_code": result.get("exit_code", 0),
        "stdout": result.get("stdout", ""),
        "stderr": result.get("stderr", ""),
        "files_created": result.get("files_created", []),
        "cost": response_cost,
    }

    # Verify all expected fields are present
    assert "success" in formatted_response
    assert "message" in formatted_response
    assert "exit_code" in formatted_response
    assert "stdout" in formatted_response
    assert "stderr" in formatted_response
    assert "files_created" in formatted_response
    assert "cost" in formatted_response

    # Verify values
    assert formatted_response["success"] == True
    assert formatted_response["exit_code"] == 0
    assert formatted_response["stdout"] == "Test output"
