"""
Tests for pdd.server.jobs module.

This test file uses fixture-based mocking to avoid polluting sys.modules
during pytest collection.
"""

import asyncio
import sys
import types
from datetime import datetime, timedelta, timezone
from unittest.mock import MagicMock, AsyncMock
import pytest


# ============================================================================
# Fixture to set up mocks and import code under test
# ============================================================================

@pytest.fixture(scope="module")
def jobs_module():
    """
    Set up mock for click_executor and import the jobs module.
    This ensures mocking happens at test execution time, not collection time.
    """
    # Clear any cached imports
    for mod_name in list(sys.modules.keys()):
        if "pdd.server.jobs" in mod_name or "pdd.server.click_executor" in mod_name:
            del sys.modules[mod_name]

    # Mock click_executor - it's not available in all environments
    mock_click_exec = types.ModuleType("pdd.server.click_executor")
    mock_click_exec.ClickCommandExecutor = MagicMock()
    mock_click_exec.get_pdd_command = MagicMock(return_value=True)
    sys.modules["pdd.server.click_executor"] = mock_click_exec

    # Now import the module under test
    from pdd.server.jobs import Job, JobManager, JobCallbacks
    from pdd.server.models import JobStatus

    return {
        "Job": Job,
        "JobManager": JobManager,
        "JobCallbacks": JobCallbacks,
        "JobStatus": JobStatus,
        "mock_click_exec": mock_click_exec,
    }


# ============================================================================
# Tests
# ============================================================================

class TestJobModel:
    def test_job_initialization(self, jobs_module):
        """Test default values and initialization of Job dataclass."""
        Job = jobs_module["Job"]
        JobStatus = jobs_module["JobStatus"]

        job = Job(command="test_cmd")
        assert job.id is not None
        assert job.command == "test_cmd"
        assert job.status == JobStatus.QUEUED
        assert isinstance(job.created_at, datetime)
        assert job.args == {}
        assert job.options == {}

    def test_job_serialization(self, jobs_module):
        """Test to_dict method for JSON serialization."""
        Job = jobs_module["Job"]
        JobStatus = jobs_module["JobStatus"]

        job = Job(
            command="sync",
            args={"force": True},
            status=JobStatus.COMPLETED,
            result={"files": 5},
            cost=0.02
        )
        now = datetime.now(timezone.utc)
        job.created_at = now
        job.started_at = now
        job.completed_at = now

        data = job.to_dict()

        assert data["command"] == "sync"
        assert data["args"] == {"force": True}
        assert data["status"] == "completed"
        assert data["result"] == {"files": 5}
        assert data["cost"] == 0.02
        assert data["created_at"] == now.isoformat()


@pytest.mark.asyncio
class TestJobManagerLifecycle:
    async def test_submit_job(self, jobs_module):
        """Test submitting a job adds it to the registry."""
        JobManager = jobs_module["JobManager"]
        JobStatus = jobs_module["JobStatus"]

        manager = JobManager()
        manager._custom_executor = AsyncMock(return_value={})

        job = await manager.submit("generate", args={"prompt": "hi"})

        assert job.id in manager._jobs
        assert manager.get_job(job.id) == job
        assert job.status in [JobStatus.QUEUED, JobStatus.RUNNING, JobStatus.COMPLETED]

    async def test_execution_success(self, jobs_module):
        """Test successful job execution flow."""
        JobManager = jobs_module["JobManager"]
        JobStatus = jobs_module["JobStatus"]

        async def success_executor(job):
            await asyncio.sleep(0.01)
            return {"success": True, "cost": 0.5}

        manager = JobManager(executor=success_executor)
        job = await manager.submit("test")

        while job.status in (JobStatus.QUEUED, JobStatus.RUNNING):
            await asyncio.sleep(0.01)

        assert job.status == JobStatus.COMPLETED
        assert job.result == {"success": True, "cost": 0.5}
        assert job.cost == 0.5
        assert job.started_at is not None
        assert job.completed_at is not None
        assert job.started_at >= job.created_at
        assert job.completed_at >= job.started_at

    async def test_execution_failure(self, jobs_module):
        """Test job failure handling."""
        JobManager = jobs_module["JobManager"]
        JobStatus = jobs_module["JobStatus"]

        async def failing_executor(job):
            raise ValueError("Something went wrong")

        manager = JobManager(executor=failing_executor)
        job = await manager.submit("fail_test")

        while job.status in (JobStatus.QUEUED, JobStatus.RUNNING):
            await asyncio.sleep(0.01)

        assert job.status == JobStatus.FAILED
        assert "Something went wrong" in job.error
        assert job.completed_at is not None

    async def test_concurrency_limit(self, jobs_module):
        """Test that max_concurrent limits active jobs."""
        JobManager = jobs_module["JobManager"]
        JobStatus = jobs_module["JobStatus"]

        manager = JobManager(max_concurrent=1)

        release_job1 = asyncio.Event()
        job1_running = asyncio.Event()

        async def blocking_executor(job):
            job1_running.set()
            await release_job1.wait()
            return {}

        manager._custom_executor = blocking_executor

        job1 = await manager.submit("job1")

        await asyncio.wait_for(job1_running.wait(), timeout=1.0)
        assert job1.status == JobStatus.RUNNING

        job2 = await manager.submit("job2")

        await asyncio.sleep(0.05)

        assert job2.status == JobStatus.QUEUED

        release_job1.set()

        while job2.status == JobStatus.QUEUED:
            await asyncio.sleep(0.01)

        assert job1.status == JobStatus.COMPLETED
        assert job2.status in (JobStatus.RUNNING, JobStatus.COMPLETED)


@pytest.mark.asyncio
class TestJobCancellation:
    async def test_cancel_queued_job(self, jobs_module):
        """Test cancelling a job before it starts running."""
        JobManager = jobs_module["JobManager"]
        JobStatus = jobs_module["JobStatus"]

        manager = JobManager(max_concurrent=1)

        blocker = asyncio.Event()

        async def blocking_exec(job):
            await blocker.wait()
            return {}

        manager._custom_executor = blocking_exec

        await manager.submit("blocker")

        job_to_cancel = await manager.submit("victim")
        assert job_to_cancel.status == JobStatus.QUEUED

        success = await manager.cancel(job_to_cancel.id)
        assert success is True

        blocker.set()

        await asyncio.sleep(0.1)

        assert job_to_cancel.status == JobStatus.CANCELLED

    async def test_cancel_running_job(self, jobs_module):
        """Test cancelling a job while it is running."""
        JobManager = jobs_module["JobManager"]
        JobStatus = jobs_module["JobStatus"]

        manager = JobManager()

        async def long_running_exec(job):
            for _ in range(10):
                await asyncio.sleep(0.05)
            return {}

        manager._custom_executor = long_running_exec

        job = await manager.submit("long_job")

        while job.status != JobStatus.RUNNING:
            await asyncio.sleep(0.01)

        await manager.cancel(job.id)

        while job.status == JobStatus.RUNNING:
            await asyncio.sleep(0.01)

        assert job.status == JobStatus.CANCELLED

    async def test_cancel_nonexistent_or_completed(self, jobs_module):
        """Test cancelling invalid job IDs."""
        JobManager = jobs_module["JobManager"]
        JobStatus = jobs_module["JobStatus"]

        manager = JobManager()
        assert await manager.cancel("fake-id") is False

        manager._custom_executor = AsyncMock(return_value={})
        job = await manager.submit("fast")
        while job.status != JobStatus.COMPLETED:
            await asyncio.sleep(0.01)

        assert await manager.cancel(job.id) is False


@pytest.mark.asyncio
class TestJobCallbacks:
    async def test_callbacks_trigger(self, jobs_module):
        """Test that lifecycle callbacks are invoked."""
        JobManager = jobs_module["JobManager"]
        JobStatus = jobs_module["JobStatus"]

        manager = JobManager()
        manager._custom_executor = AsyncMock(return_value={"cost": 0.1})

        on_start = AsyncMock()
        on_complete = AsyncMock()

        manager.callbacks.on_start(on_start)
        manager.callbacks.on_complete(on_complete)

        job = await manager.submit("callback_test")

        while job.status != JobStatus.COMPLETED:
            await asyncio.sleep(0.01)

        on_start.assert_called_once_with(job)
        on_complete.assert_called_once_with(job)

    async def test_output_callback_integration(self, jobs_module):
        """Test manual emission of output events."""
        Job = jobs_module["Job"]
        JobCallbacks = jobs_module["JobCallbacks"]

        callbacks = JobCallbacks()
        mock_cb = AsyncMock()
        callbacks.on_output(mock_cb)

        job = Job()
        await callbacks.emit_output(job, "stdout", "hello")

        mock_cb.assert_called_once_with(job, "stdout", "hello")


class TestCleanup:
    def test_cleanup_old_jobs(self, jobs_module):
        """Test removal of old completed jobs."""
        Job = jobs_module["Job"]
        JobManager = jobs_module["JobManager"]
        JobStatus = jobs_module["JobStatus"]

        manager = JobManager()

        now = datetime.now(timezone.utc)

        job_new = Job(id="new", status=JobStatus.COMPLETED)
        job_new.completed_at = now

        job_old = Job(id="old", status=JobStatus.COMPLETED)
        job_old.completed_at = now - timedelta(hours=2)

        job_active = Job(id="active", status=JobStatus.RUNNING)

        manager._jobs["new"] = job_new
        manager._jobs["old"] = job_old
        manager._jobs["active"] = job_active

        removed_count = manager.cleanup_old_jobs(max_age_seconds=3600)

        assert removed_count == 1
        assert "old" not in manager._jobs
        assert "new" in manager._jobs
        assert "active" in manager._jobs


@pytest.mark.asyncio
class TestShutdown:
    async def test_shutdown(self, jobs_module):
        """Test graceful shutdown cancels active jobs."""
        JobManager = jobs_module["JobManager"]
        JobStatus = jobs_module["JobStatus"]

        manager = JobManager()

        started = asyncio.Event()

        async def hanging_exec(job):
            started.set()
            await asyncio.sleep(10)
            return {}

        manager._custom_executor = hanging_exec
        job = await manager.submit("hang")

        await started.wait()
        assert job.status == JobStatus.RUNNING

        await manager.shutdown()

        await asyncio.sleep(0.1)
        assert job.status == JobStatus.CANCELLED


@pytest.mark.asyncio
class TestClickExecutorIntegration:
    async def test_run_click_command_success(self, jobs_module):
        """Test the _run_click_command logic with mocked subprocess."""
        from unittest.mock import patch
        Job = jobs_module["Job"]
        JobManager = jobs_module["JobManager"]

        manager = JobManager()

        # Mock subprocess.Popen to simulate successful command execution
        mock_process = MagicMock()
        mock_process.stdout.readline.side_effect = ["output\n", ""]
        mock_process.stderr.readline.side_effect = [""]
        mock_process.wait.return_value = 0
        mock_process.returncode = 0

        with patch("pdd.server.jobs.subprocess.Popen", return_value=mock_process):
            job = Job(command="test_click")

            result = await manager._run_click_command(job)

            assert "output" in result["stdout"]
            assert result["exit_code"] == 0

    async def test_run_click_command_failure(self, jobs_module):
        """Test _run_click_command raises RuntimeError on non-zero exit code."""
        from unittest.mock import patch
        Job = jobs_module["Job"]
        JobManager = jobs_module["JobManager"]

        manager = JobManager()

        # Mock subprocess.Popen to simulate failed command execution
        mock_process = MagicMock()
        mock_process.stdout.readline.side_effect = [""]
        mock_process.stderr.readline.side_effect = ["error occurred\n", ""]
        mock_process.wait.return_value = 1
        mock_process.returncode = 1

        with patch("pdd.server.jobs.subprocess.Popen", return_value=mock_process):
            job = Job(command="fail_click")

            with pytest.raises(RuntimeError, match="error occurred"):
                await manager._run_click_command(job)
