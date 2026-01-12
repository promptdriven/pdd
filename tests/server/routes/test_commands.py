"""
Tests for pdd.server.routes.commands module.

This test file uses fixtures from conftest.py to set up mocks.
NO module-level sys.modules modifications to avoid polluting other tests.
"""

import sys
import pytest
from datetime import datetime, timedelta, timezone
from unittest.mock import MagicMock, AsyncMock
from fastapi import FastAPI
from fastapi.testclient import TestClient

# Import Z3 for formal verification
try:
    import z3
    HAS_Z3 = True
except ImportError:
    HAS_Z3 = False

# Import model classes directly from pdd.server.models
from pdd.server.models import (
    CommandRequest,
    JobHandle,
    JobResult,
    JobStatus,
)


# ============================================================================
# Fixture to import code under test (after mocks are set up by conftest)
# ============================================================================

@pytest.fixture(scope="module")
def commands_module(route_test_environment):
    """
    Import the commands module after mocks are set up.
    This fixture explicitly depends on route_test_environment from conftest.py.
    """
    # Clear any cached imports
    for mod_name in list(sys.modules.keys()):
        if "pdd.server.routes.commands" in mod_name:
            del sys.modules[mod_name]

    # Now import - mocks should be in place from conftest
    from pdd.server.routes.commands import (
        router,
        execute_command,
        get_job_status,
        cancel_job,
        get_job_history,
        get_available_commands,
        get_job_manager,
        set_job_manager,
        ALLOWED_COMMANDS,
    )

    return {
        "router": router,
        "execute_command": execute_command,
        "get_job_status": get_job_status,
        "cancel_job": cancel_job,
        "get_job_history": get_job_history,
        "get_available_commands": get_available_commands,
        "get_job_manager": get_job_manager,
        "set_job_manager": set_job_manager,
        "ALLOWED_COMMANDS": ALLOWED_COMMANDS,
    }


# ============================================================================
# Test Fixtures
# ============================================================================

@pytest.fixture
def mock_job_manager():
    """Create a mock JobManager."""
    manager = MagicMock()
    manager.submit = AsyncMock()
    manager.cancel = AsyncMock()
    manager.get_job = MagicMock()
    manager.get_all_jobs = MagicMock(return_value={})
    return manager


@pytest.fixture
def sample_job():
    """Create a sample job object."""
    job = MagicMock()
    job.id = "job-123"
    job.status = JobStatus.QUEUED
    job.created_at = datetime.now(timezone.utc)
    job.started_at = None
    job.completed_at = None
    job.result = None
    job.error = None
    job.cost = 0.0
    return job


@pytest.fixture(autouse=True)
def reset_job_manager(commands_module):
    """Reset the global job manager before/after tests."""
    commands_module["set_job_manager"](None)
    yield
    commands_module["set_job_manager"](None)


@pytest.fixture
def client(commands_module, mock_job_manager):
    """Create a test client with the commands router."""
    app = FastAPI()
    app.include_router(commands_module["router"])

    # Override the dependency
    app.dependency_overrides[commands_module["get_job_manager"]] = lambda: mock_job_manager

    return TestClient(app)


# ============================================================================
# MockJob helper class for tests
# ============================================================================

class MockJob:
    """Helper class to create mock job objects with all required attributes."""
    def __init__(self, id, status, created_at, started_at=None, completed_at=None,
                 result=None, error=None, cost=0.0):
        self.id = id
        self.status = status
        self.created_at = created_at
        self.started_at = started_at
        self.completed_at = completed_at
        self.result = result
        self.error = error
        self.cost = cost


# ============================================================================
# Dependency Injection Tests
# ============================================================================

def test_get_job_manager_uninitialized(commands_module):
    """Test that get_job_manager raises RuntimeError if not set."""
    commands_module["set_job_manager"](None)
    with pytest.raises(RuntimeError, match="JobManager not configured"):
        commands_module["get_job_manager"]()


def test_set_job_manager(commands_module, mock_job_manager):
    """Test setting the job manager."""
    commands_module["set_job_manager"](mock_job_manager)
    assert commands_module["get_job_manager"]() is mock_job_manager


# ============================================================================
# Execute Command Tests
# ============================================================================

@pytest.mark.asyncio
async def test_execute_command_success(commands_module, mock_job_manager, sample_job):
    """Test successful command execution."""
    request = CommandRequest(command="generate", args={"prompt": "hello"}, options={})
    mock_job_manager.submit.return_value = sample_job

    response = await commands_module["execute_command"](request, manager=mock_job_manager)

    assert isinstance(response, JobHandle)
    assert response.job_id == sample_job.id
    assert response.status == sample_job.status
    mock_job_manager.submit.assert_called_once_with(
        command="generate", args={"prompt": "hello"}, options={}
    )


@pytest.mark.asyncio
async def test_execute_command_invalid_command(commands_module, mock_job_manager):
    """Test that invalid commands raise 400."""
    from fastapi import HTTPException
    request = CommandRequest(command="rm -rf /", args={}, options={})

    with pytest.raises(HTTPException) as exc:
        await commands_module["execute_command"](request, manager=mock_job_manager)

    assert exc.value.status_code == 400
    assert "Unknown command" in exc.value.detail


def test_execute_valid_command_via_client(client, mock_job_manager):
    """Test submitting a valid command via HTTP client."""
    mock_job = MockJob(
        id="job-123",
        status=JobStatus.QUEUED,
        created_at=datetime.now(timezone.utc)
    )
    mock_job_manager.submit.return_value = mock_job

    payload = {
        "command": "generate",
        "args": {"prompt": "hello"},
        "options": {"model": "gpt-4"}
    }

    response = client.post("/api/v1/commands/execute", json=payload)

    assert response.status_code == 200
    data = response.json()
    assert data["job_id"] == "job-123"
    assert data["status"] == "queued"


def test_execute_invalid_command_via_client(client, mock_job_manager):
    """Test submitting a command not in the whitelist via HTTP client."""
    payload = {
        "command": "rm -rf /",
        "args": {}
    }

    response = client.post("/api/v1/commands/execute", json=payload)

    assert response.status_code == 400
    assert "Unknown command" in response.json()["detail"]
    mock_job_manager.submit.assert_not_called()


# ============================================================================
# Get Job Status Tests
# ============================================================================

@pytest.mark.asyncio
async def test_get_job_status_found(commands_module, mock_job_manager, sample_job):
    """Test retrieving status for an existing job."""
    mock_job_manager.get_job.return_value = sample_job

    result = await commands_module["get_job_status"]("job-123", manager=mock_job_manager)

    assert isinstance(result, JobResult)
    assert result.job_id == "job-123"
    mock_job_manager.get_job.assert_called_once_with("job-123")


@pytest.mark.asyncio
async def test_get_job_status_not_found(commands_module, mock_job_manager):
    """Test retrieving status for a non-existent job."""
    from fastapi import HTTPException
    mock_job_manager.get_job.return_value = None

    with pytest.raises(HTTPException) as exc:
        await commands_module["get_job_status"]("missing-id", manager=mock_job_manager)

    assert exc.value.status_code == 404


@pytest.mark.asyncio
async def test_get_job_status_duration_calculation(commands_module, mock_job_manager):
    """Test duration calculation for completed and running jobs."""
    # Case 1: Completed job
    job_done = MagicMock()
    job_done.id = "done"
    job_done.status = JobStatus.COMPLETED
    start = datetime.now(timezone.utc) - timedelta(seconds=10)
    end = datetime.now(timezone.utc)
    job_done.started_at = start
    job_done.completed_at = end
    job_done.result = {}
    job_done.error = None
    job_done.cost = 0.0

    mock_job_manager.get_job.return_value = job_done
    result_done = await commands_module["get_job_status"]("done", manager=mock_job_manager)
    assert abs(result_done.duration_seconds - 10.0) < 0.1

    # Case 2: Running job
    job_running = MagicMock()
    job_running.id = "running"
    job_running.status = JobStatus.RUNNING
    start_run = datetime.now(timezone.utc) - timedelta(seconds=5)
    job_running.started_at = start_run
    job_running.completed_at = None
    job_running.result = None
    job_running.error = None
    job_running.cost = 0.0

    mock_job_manager.get_job.return_value = job_running
    result_running = await commands_module["get_job_status"]("running", manager=mock_job_manager)
    assert result_running.duration_seconds >= 5.0


def test_get_job_status_found_via_client(client, mock_job_manager):
    """Test retrieving status for an existing job via HTTP client."""
    now = datetime.now(timezone.utc)
    mock_job = MockJob(
        id="job-123",
        status=JobStatus.COMPLETED,
        created_at=now - timedelta(seconds=10),
        started_at=now - timedelta(seconds=5),
        completed_at=now,
        result={"foo": "bar"},
        cost=0.05
    )
    mock_job_manager.get_job.return_value = mock_job

    response = client.get("/api/v1/commands/jobs/job-123")

    assert response.status_code == 200
    data = response.json()
    assert data["job_id"] == "job-123"
    assert data["status"] == "completed"
    assert data["result"] == {"foo": "bar"}
    assert data["duration_seconds"] == 5.0


def test_get_job_status_not_found_via_client(client, mock_job_manager):
    """Test retrieving status for a non-existent job via HTTP client."""
    mock_job_manager.get_job.return_value = None

    response = client.get("/api/v1/commands/jobs/job-999")

    assert response.status_code == 404
    assert "Job not found" in response.json()["detail"]


def test_get_job_status_running_duration_via_client(client, mock_job_manager):
    """Test duration calculation for a running job via HTTP client."""
    now = datetime.now(timezone.utc)
    start_time = now - timedelta(seconds=10)

    mock_job = MockJob(
        id="job-running",
        status=JobStatus.RUNNING,
        created_at=start_time,
        started_at=start_time,
        completed_at=None
    )
    mock_job_manager.get_job.return_value = mock_job

    response = client.get("/api/v1/commands/jobs/job-running")

    assert response.status_code == 200
    data = response.json()
    # Duration should be approx 10 seconds
    assert 9.0 <= data["duration_seconds"] <= 11.0


# ============================================================================
# Cancel Job Tests
# ============================================================================

@pytest.mark.asyncio
async def test_cancel_job_success(commands_module, mock_job_manager, sample_job):
    """Test successful job cancellation."""
    sample_job.status = JobStatus.RUNNING
    mock_job_manager.get_job.return_value = sample_job
    mock_job_manager.cancel.return_value = True

    response = await commands_module["cancel_job"]("job-123", manager=mock_job_manager)

    assert response["cancelled"] is True
    mock_job_manager.cancel.assert_called_once_with("job-123")


@pytest.mark.asyncio
async def test_cancel_job_not_found(commands_module, mock_job_manager):
    """Test cancelling a non-existent job."""
    from fastapi import HTTPException
    mock_job_manager.get_job.return_value = None

    with pytest.raises(HTTPException) as exc:
        await commands_module["cancel_job"]("missing", manager=mock_job_manager)

    assert exc.value.status_code == 404


@pytest.mark.asyncio
async def test_cancel_job_already_finished(commands_module, mock_job_manager, sample_job):
    """Test cancelling a job that is already finished."""
    from fastapi import HTTPException
    sample_job.status = JobStatus.COMPLETED
    mock_job_manager.get_job.return_value = sample_job

    with pytest.raises(HTTPException) as exc:
        await commands_module["cancel_job"]("job-123", manager=mock_job_manager)

    assert exc.value.status_code == 409
    assert "Job already finished" in exc.value.detail


def test_cancel_job_success_via_client(client, mock_job_manager):
    """Test cancelling a running job via HTTP client."""
    mock_job = MockJob(id="job-1", status=JobStatus.RUNNING, created_at=datetime.now())
    mock_job_manager.get_job.return_value = mock_job
    mock_job_manager.cancel.return_value = True

    response = client.post("/api/v1/commands/jobs/job-1/cancel")

    assert response.status_code == 200
    assert response.json()["cancelled"] is True
    mock_job_manager.cancel.assert_awaited_once_with("job-1")


def test_cancel_job_not_found_via_client(client, mock_job_manager):
    """Test cancelling a non-existent job via HTTP client."""
    mock_job_manager.get_job.return_value = None

    response = client.post("/api/v1/commands/jobs/job-999/cancel")

    assert response.status_code == 404


def test_cancel_job_already_finished_via_client(client, mock_job_manager):
    """Test cancelling a completed job returns 409 via HTTP client."""
    mock_job = MockJob(id="job-1", status=JobStatus.COMPLETED, created_at=datetime.now())
    mock_job_manager.get_job.return_value = mock_job

    response = client.post("/api/v1/commands/jobs/job-1/cancel")

    assert response.status_code == 409
    assert "already finished" in response.json()["detail"]
    mock_job_manager.cancel.assert_not_called()


# ============================================================================
# Job History Tests
# ============================================================================

@pytest.mark.asyncio
async def test_get_job_history_pagination_and_sorting(commands_module, mock_job_manager):
    """Test history pagination and sorting."""
    now = datetime.now(timezone.utc)
    job1 = MagicMock(
        id="1",
        created_at=now - timedelta(hours=3),
        status=JobStatus.COMPLETED,
        started_at=None,
        completed_at=None,
        result={},
        error=None,
        cost=0.0
    )
    job2 = MagicMock(
        id="2",
        created_at=now - timedelta(hours=1),
        status=JobStatus.FAILED,
        started_at=None,
        completed_at=None,
        result=None,
        error="Failed",
        cost=0.0
    )
    job3 = MagicMock(
        id="3",
        created_at=now - timedelta(hours=2),
        status=JobStatus.QUEUED,
        started_at=None,
        completed_at=None,
        result=None,
        error=None,
        cost=0.0
    )

    mock_job_manager.get_all_jobs.return_value = {
        "1": job1, "2": job2, "3": job3
    }

    # Test default sort (newest first: 2, 3, 1)
    results = await commands_module["get_job_history"](limit=10, offset=0, status=None, manager=mock_job_manager)
    assert len(results) == 3
    assert results[0].job_id == "2"
    assert results[1].job_id == "3"
    assert results[2].job_id == "1"

    # Test pagination (limit 1, offset 1 -> should get job 3)
    results_page = await commands_module["get_job_history"](limit=1, offset=1, status=None, manager=mock_job_manager)
    assert len(results_page) == 1
    assert results_page[0].job_id == "3"


@pytest.mark.asyncio
async def test_get_job_history_filtering(commands_module, mock_job_manager):
    """Test history filtering by status."""
    job1 = MagicMock(
        id="1",
        status=JobStatus.COMPLETED,
        created_at=datetime.now(),
        started_at=None,
        completed_at=None,
        result={},
        error=None,
        cost=0.0
    )
    job2 = MagicMock(
        id="2",
        status=JobStatus.FAILED,
        created_at=datetime.now(),
        started_at=None,
        completed_at=None,
        result=None,
        error="Error",
        cost=0.0
    )

    mock_job_manager.get_all_jobs.return_value = {"1": job1, "2": job2}

    results = await commands_module["get_job_history"](limit=10, offset=0, status=JobStatus.COMPLETED, manager=mock_job_manager)
    assert len(results) == 1
    assert results[0].job_id == "1"


def test_get_history_pagination_via_client(client, mock_job_manager):
    """Test history endpoint sorting and pagination via HTTP client."""
    now = datetime.now(timezone.utc)
    job1 = MockJob(id="1", status=JobStatus.QUEUED, created_at=now - timedelta(hours=1))
    job2 = MockJob(id="2", status=JobStatus.QUEUED, created_at=now - timedelta(hours=2))
    job3 = MockJob(id="3", status=JobStatus.QUEUED, created_at=now)  # Newest

    mock_job_manager.get_all_jobs.return_value = {
        "1": job1, "2": job2, "3": job3
    }

    # Request limit 2, offset 0 -> Should get job3, job1
    response = client.get("/api/v1/commands/history?limit=2&offset=0")
    data = response.json()

    assert len(data) == 2
    assert data[0]["job_id"] == "3"  # Newest first
    assert data[1]["job_id"] == "1"

    # Request limit 2, offset 2 -> Should get job2
    response = client.get("/api/v1/commands/history?limit=2&offset=2")
    data = response.json()

    assert len(data) == 1
    assert data[0]["job_id"] == "2"


def test_get_history_status_filter_via_client(client, mock_job_manager):
    """Test filtering history by status via HTTP client."""
    job1 = MockJob(id="1", status=JobStatus.COMPLETED, created_at=datetime.now())
    job2 = MockJob(id="2", status=JobStatus.FAILED, created_at=datetime.now())

    mock_job_manager.get_all_jobs.return_value = {"1": job1, "2": job2}

    response = client.get(f"/api/v1/commands/history?status={JobStatus.COMPLETED.value}")
    data = response.json()

    assert len(data) == 1
    assert data[0]["job_id"] == "1"
    assert data[0]["status"] == JobStatus.COMPLETED.value


# ============================================================================
# Available Commands Tests
# ============================================================================

@pytest.mark.asyncio
async def test_get_available_commands(commands_module):
    """Test retrieving available commands."""
    commands = await commands_module["get_available_commands"]()
    assert isinstance(commands, list)
    assert len(commands) == len(commands_module["ALLOWED_COMMANDS"])

    names = [c["name"] for c in commands]
    assert "generate" in names
    assert "test" in names


def test_get_available_commands_via_client(client, commands_module):
    """Test retrieving available commands via HTTP client."""
    response = client.get("/api/v1/commands/available")

    assert response.status_code == 200
    data = response.json()

    assert isinstance(data, list)
    assert len(data) == len(commands_module["ALLOWED_COMMANDS"])

    # Check structure
    first = data[0]
    assert "name" in first
    assert "description" in first

    # Check content matches whitelist
    names = [cmd["name"] for cmd in data]
    assert "sync" in names
    assert "generate" in names


# ============================================================================
# Z3 Formal Verification Tests
# ============================================================================

@pytest.mark.skipif(not HAS_Z3, reason="z3-solver not installed")
def test_z3_pagination_logic():
    """
    Verify the pagination logic used in get_job_history.
    Logic: slice = list[offset : offset + limit]
    We want to prove that the resulting size is always min(limit, max(0, total - offset))
    assuming limit >= 0 and offset >= 0.
    """
    s = z3.Solver()

    # Inputs
    total_items = z3.Int('total_items')
    offset = z3.Int('offset')
    limit = z3.Int('limit')

    # Output: actual number of items returned
    result_size = z3.Int('result_size')

    # Constraints (Preconditions)
    s.add(total_items >= 0)
    s.add(offset >= 0)
    s.add(limit >= 0)

    # Logic model of Python slicing: list[start:end]
    start = offset
    end = offset + limit

    actual_start = z3.If(start < total_items, start, total_items)
    actual_end = z3.If(end < total_items, end, total_items)

    # Python slice size logic
    calculated_size = z3.If(actual_end > actual_start, actual_end - actual_start, 0)

    # Expected logic: min(limit, max(0, total_items - offset))
    remaining = z3.If(total_items - offset > 0, total_items - offset, 0)
    expected_size = z3.If(limit < remaining, limit, remaining)

    # We want to prove that calculated_size == expected_size is ALWAYS true.
    # So we check if Not(calculated_size == expected_size) is satisfiable.
    s.add(z3.Not(calculated_size == expected_size))

    # If UNSAT, it means no counter-example exists -> logic is correct.
    assert s.check() == z3.unsat


@pytest.mark.skipif(not HAS_Z3, reason="z3-solver not installed")
def test_z3_duration_logic():
    """
    Verify the duration calculation logic.
    Logic:
      if completed_at: duration = completed_at - started_at
      else: duration = now - started_at

    We want to ensure duration is non-negative provided the timestamps are chronological.
    """
    s = z3.Solver()

    started_at = z3.Int('started_at')
    completed_at = z3.Int('completed_at')
    now = z3.Int('now')

    # Boolean flag: is the job completed?
    is_completed = z3.Int('is_completed')  # 1 for true, 0 for false
    s.add(z3.Or(is_completed == 0, is_completed == 1))

    # Logic from code
    duration = z3.Int('duration')

    # Model the conditional logic
    s.add(
        z3.If(is_completed == 1,
           duration == completed_at - started_at,
           duration == now - started_at
        )
    )

    # Preconditions (Chronological order)
    s.add(started_at <= now)
    s.add(z3.Implies(is_completed == 1, z3.And(started_at <= completed_at)))

    # Verification Goal: Prove duration >= 0
    s.add(z3.Not(duration >= 0))

    # If UNSAT, then duration is always >= 0 given the preconditions
    assert s.check() == z3.unsat


# ============================================================================
# Tests for crash and verify commands
# ============================================================================

def test_crash_command_in_allowed_list(commands_module):
    """Test that crash command is in the allowed commands list."""
    assert "crash" in commands_module["ALLOWED_COMMANDS"]


def test_verify_command_in_allowed_list(commands_module):
    """Test that verify command is in the allowed commands list."""
    assert "verify" in commands_module["ALLOWED_COMMANDS"]


def test_execute_crash_command_via_client(client, mock_job_manager):
    """Test submitting a crash command via HTTP client."""
    mock_job = MockJob(
        id="job-crash-1",
        status=JobStatus.QUEUED,
        created_at=datetime.now(timezone.utc)
    )
    mock_job_manager.submit.return_value = mock_job

    payload = {
        "command": "crash",
        "args": {
            "prompt_file": "prompts/foo.prompt",
            "code_file": "src/foo.py",
            "program_file": "main.py",
            "error_file": "error.log"
        },
        "options": {}
    }

    response = client.post("/api/v1/commands/execute", json=payload)

    assert response.status_code == 200
    data = response.json()
    assert data["job_id"] == "job-crash-1"


def test_execute_verify_command_via_client(client, mock_job_manager):
    """Test submitting a verify command via HTTP client."""
    mock_job = MockJob(
        id="job-verify-1",
        status=JobStatus.QUEUED,
        created_at=datetime.now(timezone.utc)
    )
    mock_job_manager.submit.return_value = mock_job

    payload = {
        "command": "verify",
        "args": {
            "prompt_file": "prompts/foo.prompt",
            "code_file": "src/foo.py",
            "verification_program": "verify.py"
        },
        "options": {}
    }

    response = client.post("/api/v1/commands/execute", json=payload)

    assert response.status_code == 200
    data = response.json()
    assert data["job_id"] == "job-verify-1"


# ============================================================================
# Z3 Formal Verification Tests
# ============================================================================

@pytest.mark.skipif(not HAS_Z3, reason="z3-solver not installed")
def test_z3_duration_logic_extended():
    """
    Formal verification of the duration calculation logic found in get_job_status.

    Logic to verify:
    if completed_at and started_at: duration = completed - started
    elif started_at: duration = now - started
    else: duration = 0
    """
    s = z3.Solver()

    # Inputs
    started_at = z3.Int('started_at')  # Represented as timestamp
    completed_at = z3.Int('completed_at')
    now = z3.Int('now')

    # Flags for existence (simulating None)
    has_started = z3.Bool('has_started')
    has_completed = z3.Bool('has_completed')

    # The calculated duration variable
    duration = z3.Int('duration')

    # Constraints:
    # 1. If completed, it must have started
    # 2. started <= completed <= now
    s.add(z3.Implies(has_completed, has_started))
    s.add(z3.Implies(has_started, started_at <= now))
    s.add(z3.Implies(z3.And(has_started, has_completed), started_at <= completed_at))
    s.add(z3.Implies(has_completed, completed_at <= now))

    # The Logic Implementation from the code
    logic_model = z3.If(
        z3.And(has_started, has_completed),
        completed_at - started_at,
        z3.If(
            has_started,
            now - started_at,
            0
        )
    )

    s.add(duration == logic_model)

    # Verification Goal 1: Duration should never be negative given valid timestamps
    s.push()
    s.add(duration < 0)
    result = s.check()
    assert result == z3.unsat, "Duration can be negative!"
    s.pop()

    # Verification Goal 2: If not started, duration is 0
    s.push()
    s.add(z3.Not(has_started))
    s.add(duration != 0)
    result = s.check()
    assert result == z3.unsat, "Duration should be 0 if not started"
    s.pop()

    # Verification Goal 3: If completed, duration is fixed (independent of now)
    s.push()
    s.add(has_started, has_completed)
    s.add(duration != (completed_at - started_at))
    result = s.check()
    assert result == z3.unsat, "Duration incorrect for completed job"
    s.pop()


# ============================================================================
# Tests for Spawned Job Terminal Port Bug (TDD - should FAIL initially)
# ============================================================================

from pathlib import Path
from unittest.mock import patch


class TestSpawnTerminalPortBug:
    """Tests that expose the server_port bug in spawn_terminal_command."""

    def test_spawn_terminal_should_pass_server_port_to_spawner(self, commands_module, mock_job_manager):
        """
        FAILING TEST: Exposes the bug.
        TerminalSpawner.spawn should receive server_port parameter.
        Currently fails because spawn is called without server_port.
        """
        from pdd.server.routes.commands import router, get_job_manager, get_project_root
        from pdd.server.terminal_spawner import TerminalSpawner

        app = FastAPI()
        app.include_router(router)

        app.dependency_overrides[get_job_manager] = lambda: mock_job_manager
        app.dependency_overrides[get_project_root] = lambda: Path("/tmp/test")

        with patch.object(TerminalSpawner, 'spawn', return_value=True) as mock_spawn:
            client = TestClient(app)
            response = client.post("/api/v1/commands/spawn-terminal", json={
                "command": "generate",
                "args": {"prompt_file": "test.prompt"},
                "options": {}
            })

            assert response.status_code == 200
            mock_spawn.assert_called_once()

            # THIS ASSERTION WILL FAIL - current code doesn't pass server_port
            call_kwargs = mock_spawn.call_args.kwargs
            assert "server_port" in call_kwargs, "server_port must be passed to TerminalSpawner.spawn"

    def test_spawn_terminal_should_use_configured_port(self, commands_module, mock_job_manager):
        """
        FAILING TEST: When server is on port 8000, spawn should use that port.
        """
        from pdd.server.routes.commands import router, get_job_manager, get_project_root
        from pdd.server.terminal_spawner import TerminalSpawner

        app = FastAPI()
        app.include_router(router)

        app.dependency_overrides[get_job_manager] = lambda: mock_job_manager
        app.dependency_overrides[get_project_root] = lambda: Path("/tmp/test")
        # After fix: app.dependency_overrides[get_server_port] = lambda: 8000

        captured_port = []

        def capture_spawn(*args, **kwargs):
            captured_port.append(kwargs.get('server_port'))
            return True

        with patch.object(TerminalSpawner, 'spawn', side_effect=capture_spawn):
            client = TestClient(app)
            client.post("/api/v1/commands/spawn-terminal", json={
                "command": "generate",
                "args": {"prompt_file": "test.prompt"},
                "options": {}
            })

            # THIS WILL FAIL until fix is implemented
            assert len(captured_port) == 1
            assert captured_port[0] is not None, "server_port should not be None"


# ============================================================================
# Tests for Spawned Job Complete Endpoint
# ============================================================================


class TestSpawnedJobCompleteEndpoint:
    """Tests for /spawned-jobs/{job_id}/complete endpoint."""

    def test_complete_spawned_job_success(self, commands_module, mock_job_manager):
        """Test completing a spawned job with success."""
        from pdd.server.routes.commands import router, get_job_manager, get_project_root
        from pdd.server.terminal_spawner import TerminalSpawner

        app = FastAPI()
        app.include_router(router)
        app.dependency_overrides[get_job_manager] = lambda: mock_job_manager
        app.dependency_overrides[get_project_root] = lambda: Path("/tmp/test")

        client = TestClient(app)

        with patch.object(TerminalSpawner, 'spawn', return_value=True):
            spawn_resp = client.post("/api/v1/commands/spawn-terminal", json={
                "command": "generate",
                "args": {"prompt_file": "test.prompt"},
                "options": {}
            })
            job_id = spawn_resp.json()["job_id"]

        # Complete the job
        complete_resp = client.post(
            f"/api/v1/commands/spawned-jobs/{job_id}/complete",
            json={"success": True, "exit_code": 0}
        )

        assert complete_resp.status_code == 200
        assert complete_resp.json()["updated"] is True
        assert complete_resp.json()["job_id"] == job_id

    def test_complete_spawned_job_failure(self, commands_module, mock_job_manager):
        """Test completing a spawned job with failure status."""
        from pdd.server.routes.commands import router, get_job_manager, get_project_root
        from pdd.server.terminal_spawner import TerminalSpawner

        app = FastAPI()
        app.include_router(router)
        app.dependency_overrides[get_job_manager] = lambda: mock_job_manager
        app.dependency_overrides[get_project_root] = lambda: Path("/tmp/test")

        client = TestClient(app)

        with patch.object(TerminalSpawner, 'spawn', return_value=True):
            spawn_resp = client.post("/api/v1/commands/spawn-terminal", json={
                "command": "generate",
                "args": {"prompt_file": "test.prompt"},
                "options": {}
            })
            job_id = spawn_resp.json()["job_id"]

        # Complete the job with failure
        complete_resp = client.post(
            f"/api/v1/commands/spawned-jobs/{job_id}/complete",
            json={"success": False, "exit_code": 1}
        )

        assert complete_resp.status_code == 200
        assert complete_resp.json()["updated"] is True

        # Verify status was updated to failed
        status_resp = client.get(f"/api/v1/commands/spawned-jobs/{job_id}/status")
        assert status_resp.json()["status"] == "failed"
        assert status_resp.json()["exit_code"] == 1

    def test_complete_unknown_job_returns_not_updated(self, commands_module, mock_job_manager):
        """Test completing a job that doesn't exist returns updated=False."""
        from pdd.server.routes.commands import router, get_job_manager, get_project_root

        app = FastAPI()
        app.include_router(router)
        app.dependency_overrides[get_job_manager] = lambda: mock_job_manager
        app.dependency_overrides[get_project_root] = lambda: Path("/tmp/test")

        client = TestClient(app)

        response = client.post(
            "/api/v1/commands/spawned-jobs/nonexistent-job/complete",
            json={"success": True, "exit_code": 0}
        )

        assert response.status_code == 200
        assert response.json()["updated"] is False


# ============================================================================
# Tests for Spawned Job Status Endpoint
# ============================================================================


class TestSpawnedJobStatusEndpoint:
    """Tests for /spawned-jobs/{job_id}/status endpoint."""

    def test_get_running_job_status(self, commands_module, mock_job_manager):
        """Test getting status of a running spawned job."""
        from pdd.server.routes.commands import router, get_job_manager, get_project_root
        from pdd.server.terminal_spawner import TerminalSpawner

        app = FastAPI()
        app.include_router(router)
        app.dependency_overrides[get_job_manager] = lambda: mock_job_manager
        app.dependency_overrides[get_project_root] = lambda: Path("/tmp/test")

        client = TestClient(app)

        with patch.object(TerminalSpawner, 'spawn', return_value=True):
            spawn_resp = client.post("/api/v1/commands/spawn-terminal", json={
                "command": "generate",
                "args": {"prompt_file": "test.prompt"},
                "options": {}
            })
            job_id = spawn_resp.json()["job_id"]

        status_resp = client.get(f"/api/v1/commands/spawned-jobs/{job_id}/status")
        assert status_resp.status_code == 200
        assert status_resp.json()["status"] == "running"
        assert status_resp.json()["command"] == "generate"
        assert status_resp.json()["job_id"] == job_id

    def test_get_completed_job_status(self, commands_module, mock_job_manager):
        """Test getting status after job completes successfully."""
        from pdd.server.routes.commands import router, get_job_manager, get_project_root
        from pdd.server.terminal_spawner import TerminalSpawner

        app = FastAPI()
        app.include_router(router)
        app.dependency_overrides[get_job_manager] = lambda: mock_job_manager
        app.dependency_overrides[get_project_root] = lambda: Path("/tmp/test")

        client = TestClient(app)

        with patch.object(TerminalSpawner, 'spawn', return_value=True):
            spawn_resp = client.post("/api/v1/commands/spawn-terminal", json={
                "command": "generate",
                "args": {"prompt_file": "test.prompt"},
                "options": {}
            })
            job_id = spawn_resp.json()["job_id"]

        # Complete the job
        client.post(
            f"/api/v1/commands/spawned-jobs/{job_id}/complete",
            json={"success": True, "exit_code": 0}
        )

        status_resp = client.get(f"/api/v1/commands/spawned-jobs/{job_id}/status")
        assert status_resp.json()["status"] == "completed"
        assert status_resp.json()["exit_code"] == 0
        assert status_resp.json()["completed_at"] is not None

    def test_get_unknown_job_status(self, commands_module, mock_job_manager):
        """Test getting status of unknown job returns unknown status."""
        from pdd.server.routes.commands import router, get_job_manager, get_project_root

        app = FastAPI()
        app.include_router(router)
        app.dependency_overrides[get_job_manager] = lambda: mock_job_manager
        app.dependency_overrides[get_project_root] = lambda: Path("/tmp/test")

        client = TestClient(app)

        resp = client.get("/api/v1/commands/spawned-jobs/nonexistent/status")
        assert resp.status_code == 200
        assert resp.json()["status"] == "unknown"


# ============================================================================
# Tests for WebSocket Notification on Spawned Job Completion
# ============================================================================


class TestSpawnedJobWebSocketNotification:
    """Tests for WebSocket notifications on spawned job completion."""

    @pytest.mark.asyncio
    async def test_complete_spawned_job_broadcasts_to_all_clients(self, commands_module, mock_job_manager):
        """
        Test that completing a spawned job broadcasts to ALL WebSocket clients.

        Spawned jobs don't have specific subscribers (no one connects to /ws/jobs/{job_id}/stream),
        so we must broadcast to all connected clients using emit_spawned_job_complete.
        """
        from pdd.server.routes.commands import router, get_job_manager, get_project_root
        from pdd.server.terminal_spawner import TerminalSpawner

        # Create a mock for emit_spawned_job_complete
        mock_emit = AsyncMock()

        # Patch the websocket module's emit_spawned_job_complete at the point where commands imports it
        with patch.dict('sys.modules', {'pdd.server.routes.websocket': MagicMock(emit_spawned_job_complete=mock_emit)}):
            app = FastAPI()
            app.include_router(router)
            app.dependency_overrides[get_job_manager] = lambda: mock_job_manager
            app.dependency_overrides[get_project_root] = lambda: Path("/tmp/test")

            client = TestClient(app)

            with patch.object(TerminalSpawner, 'spawn', return_value=True):
                spawn_resp = client.post("/api/v1/commands/spawn-terminal", json={
                    "command": "generate",
                    "args": {"prompt_file": "test.prompt"},
                    "options": {}
                })
                job_id = spawn_resp.json()["job_id"]

            # Complete the job
            client.post(
                f"/api/v1/commands/spawned-jobs/{job_id}/complete",
                json={"success": True, "exit_code": 0}
            )

            # Verify WebSocket broadcast was called
            mock_emit.assert_called_once()
            call_kwargs = mock_emit.call_args.kwargs
            assert call_kwargs["job_id"] == job_id
            assert call_kwargs["success"] is True
            assert call_kwargs["exit_code"] == 0
            assert call_kwargs["command"] == "generate"


# ============================================================================
# Tests for Curl Callback Format (Integer Booleans)
# ============================================================================


class TestCurlCallbackFormat:
    """
    Tests to verify the callback endpoint accepts the exact format sent by curl.

    The bash script sends JSON with integer booleans:
    - Success: {"success": 1, "exit_code": 0}
    - Failure: {"success": 0, "exit_code": 1}

    Pydantic must accept these integer values as booleans.
    """

    def test_complete_with_integer_boolean_success(self, commands_module, mock_job_manager):
        """
        Test that endpoint accepts success=1 (integer) as True.
        This is the exact format sent by: $((EXIT_CODE == 0))
        """
        from pdd.server.routes.commands import router, get_job_manager, get_project_root
        from pdd.server.terminal_spawner import TerminalSpawner

        app = FastAPI()
        app.include_router(router)
        app.dependency_overrides[get_job_manager] = lambda: mock_job_manager
        app.dependency_overrides[get_project_root] = lambda: Path("/tmp/test")

        client = TestClient(app)

        # First spawn a job
        with patch.object(TerminalSpawner, 'spawn', return_value=True):
            spawn_resp = client.post("/api/v1/commands/spawn-terminal", json={
                "command": "generate",
                "args": {"prompt_file": "test.prompt"},
                "options": {}
            })
            job_id = spawn_resp.json()["job_id"]

        # Complete with INTEGER boolean (1 = true) - exactly what curl sends
        complete_resp = client.post(
            f"/api/v1/commands/spawned-jobs/{job_id}/complete",
            json={"success": 1, "exit_code": 0}  # Integer, not bool!
        )

        assert complete_resp.status_code == 200
        assert complete_resp.json()["updated"] is True

        # Verify status was updated to "completed"
        status_resp = client.get(f"/api/v1/commands/spawned-jobs/{job_id}/status")
        assert status_resp.json()["status"] == "completed"

    def test_complete_with_integer_boolean_failure(self, commands_module, mock_job_manager):
        """
        Test that endpoint accepts success=0 (integer) as False.
        This is the exact format sent by: $((EXIT_CODE == 0)) when EXIT_CODE != 0
        """
        from pdd.server.routes.commands import router, get_job_manager, get_project_root
        from pdd.server.terminal_spawner import TerminalSpawner

        app = FastAPI()
        app.include_router(router)
        app.dependency_overrides[get_job_manager] = lambda: mock_job_manager
        app.dependency_overrides[get_project_root] = lambda: Path("/tmp/test")

        client = TestClient(app)

        # First spawn a job
        with patch.object(TerminalSpawner, 'spawn', return_value=True):
            spawn_resp = client.post("/api/v1/commands/spawn-terminal", json={
                "command": "generate",
                "args": {"prompt_file": "test.prompt"},
                "options": {}
            })
            job_id = spawn_resp.json()["job_id"]

        # Complete with INTEGER boolean (0 = false) - exactly what curl sends
        complete_resp = client.post(
            f"/api/v1/commands/spawned-jobs/{job_id}/complete",
            json={"success": 0, "exit_code": 1}  # Integer, not bool!
        )

        assert complete_resp.status_code == 200
        assert complete_resp.json()["updated"] is True

        # Verify status was updated to "failed"
        status_resp = client.get(f"/api/v1/commands/spawned-jobs/{job_id}/status")
        assert status_resp.json()["status"] == "failed"

    def test_complete_with_raw_curl_json_format(self, commands_module, mock_job_manager):
        """
        Test with the exact raw JSON string that curl would send.
        Simulates: -d '{"success": 1, "exit_code": 0}'
        """
        from pdd.server.routes.commands import router, get_job_manager, get_project_root
        from pdd.server.terminal_spawner import TerminalSpawner

        app = FastAPI()
        app.include_router(router)
        app.dependency_overrides[get_job_manager] = lambda: mock_job_manager
        app.dependency_overrides[get_project_root] = lambda: Path("/tmp/test")

        client = TestClient(app)

        # First spawn a job
        with patch.object(TerminalSpawner, 'spawn', return_value=True):
            spawn_resp = client.post("/api/v1/commands/spawn-terminal", json={
                "command": "generate",
                "args": {"prompt_file": "test.prompt"},
                "options": {}
            })
            job_id = spawn_resp.json()["job_id"]

        # Send raw content like curl would
        complete_resp = client.post(
            f"/api/v1/commands/spawned-jobs/{job_id}/complete",
            content='{"success": 1, "exit_code": 0}',
            headers={"Content-Type": "application/json"}
        )

        assert complete_resp.status_code == 200
        assert complete_resp.json()["updated"] is True


# ============================================================================
# Tests for _spawned_jobs Dictionary Persistence
# ============================================================================


class TestSpawnedJobsDictPersistence:
    """
    Tests to verify that _spawned_jobs dict persists correctly across requests.
    """

    def test_spawned_jobs_dict_persists_between_spawn_and_complete(self, commands_module, mock_job_manager):
        """
        Test that a job spawned in one request can be completed in another.
        """
        from pdd.server.routes.commands import router, get_job_manager, get_project_root, _spawned_jobs
        from pdd.server.terminal_spawner import TerminalSpawner

        # Clear any existing jobs
        _spawned_jobs.clear()

        app = FastAPI()
        app.include_router(router)
        app.dependency_overrides[get_job_manager] = lambda: mock_job_manager
        app.dependency_overrides[get_project_root] = lambda: Path("/tmp/test")

        client = TestClient(app)

        # Spawn a job
        with patch.object(TerminalSpawner, 'spawn', return_value=True):
            spawn_resp = client.post("/api/v1/commands/spawn-terminal", json={
                "command": "generate",
                "args": {"prompt_file": "test.prompt"},
                "options": {}
            })
            job_id = spawn_resp.json()["job_id"]

        # Verify job is in _spawned_jobs dict
        assert job_id in _spawned_jobs, f"Job {job_id} should be in _spawned_jobs"
        assert _spawned_jobs[job_id]["status"] == "running"

        # Complete the job in a separate request
        complete_resp = client.post(
            f"/api/v1/commands/spawned-jobs/{job_id}/complete",
            json={"success": True, "exit_code": 0}
        )

        assert complete_resp.status_code == 200
        assert complete_resp.json()["updated"] is True

        # Verify job status was updated
        assert _spawned_jobs[job_id]["status"] == "completed"

    def test_multiple_spawned_jobs_tracked_independently(self, commands_module, mock_job_manager):
        """
        Test that multiple spawned jobs are tracked independently.
        """
        from pdd.server.routes.commands import router, get_job_manager, get_project_root, _spawned_jobs
        from pdd.server.terminal_spawner import TerminalSpawner

        # Clear any existing jobs
        _spawned_jobs.clear()

        app = FastAPI()
        app.include_router(router)
        app.dependency_overrides[get_job_manager] = lambda: mock_job_manager
        app.dependency_overrides[get_project_root] = lambda: Path("/tmp/test")

        client = TestClient(app)

        # Spawn multiple jobs
        job_ids = []
        with patch.object(TerminalSpawner, 'spawn', return_value=True):
            for i in range(3):
                spawn_resp = client.post("/api/v1/commands/spawn-terminal", json={
                    "command": "generate",
                    "args": {"prompt_file": f"test{i}.prompt"},
                    "options": {}
                })
                job_ids.append(spawn_resp.json()["job_id"])

        # All jobs should be tracked
        assert len(_spawned_jobs) >= 3
        for job_id in job_ids:
            assert job_id in _spawned_jobs
            assert _spawned_jobs[job_id]["status"] == "running"

        # Complete first job with success
        client.post(
            f"/api/v1/commands/spawned-jobs/{job_ids[0]}/complete",
            json={"success": 1, "exit_code": 0}
        )

        # Complete second job with failure
        client.post(
            f"/api/v1/commands/spawned-jobs/{job_ids[1]}/complete",
            json={"success": 0, "exit_code": 1}
        )

        # Third job still running
        assert _spawned_jobs[job_ids[0]]["status"] == "completed"
        assert _spawned_jobs[job_ids[1]]["status"] == "failed"
        assert _spawned_jobs[job_ids[2]]["status"] == "running"

    def test_job_id_format_matches_expected_pattern(self, commands_module, mock_job_manager):
        """
        Test that spawned job IDs match the expected format.
        Format: spawned-{timestamp}-{uuid8}
        """
        from pdd.server.routes.commands import router, get_job_manager, get_project_root
        from pdd.server.terminal_spawner import TerminalSpawner
        import re

        app = FastAPI()
        app.include_router(router)
        app.dependency_overrides[get_job_manager] = lambda: mock_job_manager
        app.dependency_overrides[get_project_root] = lambda: Path("/tmp/test")

        client = TestClient(app)

        with patch.object(TerminalSpawner, 'spawn', return_value=True):
            spawn_resp = client.post("/api/v1/commands/spawn-terminal", json={
                "command": "generate",
                "args": {"prompt_file": "test.prompt"},
                "options": {}
            })
            job_id = spawn_resp.json()["job_id"]

        # Job ID should match pattern: spawned-{13-digit-timestamp}-{8-char-hex}
        pattern = r'^spawned-\d{13}-[a-f0-9]{8}$'
        assert re.match(pattern, job_id), f"Job ID {job_id} doesn't match expected pattern"
