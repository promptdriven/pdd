"""
Job Queue Manager Example for PDD Server.

This example demonstrates how to manage async job execution with:
- Job submission and queuing
- Concurrent execution with limits
- Job status tracking
- Cancellation support
- Result storage

Documentation references:
- asyncio: https://docs.python.org/3/library/asyncio.html
- concurrent.futures: https://docs.python.org/3/library/concurrent.futures.html
- Threading in Python: https://docs.python.org/3/library/threading.html
"""

import asyncio
from concurrent.futures import ThreadPoolExecutor
from dataclasses import dataclass, field
from datetime import datetime, timezone
from enum import Enum
from typing import Any, Callable, Dict, Optional, Awaitable
from uuid import uuid4


# ============================================================================
# Job Status and Models
# ============================================================================

class JobStatus(str, Enum):
    """Job execution status."""
    QUEUED = "queued"
    RUNNING = "running"
    COMPLETED = "completed"
    FAILED = "failed"
    CANCELLED = "cancelled"


@dataclass
class Job:
    """Represents a queued or executing job."""
    id: str = field(default_factory=lambda: str(uuid4()))
    command: str = ""
    args: Dict[str, Any] = field(default_factory=dict)
    options: Dict[str, Any] = field(default_factory=dict)
    status: JobStatus = JobStatus.QUEUED
    result: Optional[Any] = None
    error: Optional[str] = None
    cost: float = 0.0
    created_at: datetime = field(default_factory=lambda: datetime.now(timezone.utc))
    started_at: Optional[datetime] = None
    completed_at: Optional[datetime] = None

    def to_dict(self) -> Dict[str, Any]:
        """Convert job to dictionary for JSON serialization."""
        return {
            "id": self.id,
            "command": self.command,
            "args": self.args,
            "options": self.options,
            "status": self.status.value,
            "result": self.result,
            "error": self.error,
            "cost": self.cost,
            "created_at": self.created_at.isoformat(),
            "started_at": self.started_at.isoformat() if self.started_at else None,
            "completed_at": self.completed_at.isoformat() if self.completed_at else None,
        }


# ============================================================================
# Job Manager
# ============================================================================

class JobManager:
    """
    Manages job submission, execution, and tracking.

    This class provides:
    - Async job submission
    - Concurrent execution with configurable limits
    - Job status tracking and history
    - Cancellation support

    Usage:
        manager = JobManager(max_concurrent=2)

        # Submit a job
        job = await manager.submit("sync", args={"basename": "hello"})

        # Check status
        status = manager.get_job(job.id)

        # Cancel if needed
        await manager.cancel(job.id)
    """

    def __init__(
        self,
        max_concurrent: int = 1,
        executor: Callable[[Job], Awaitable[Dict[str, Any]]] = None,
    ):
        """
        Initialize the job manager.

        Args:
            max_concurrent: Maximum number of concurrent jobs
            executor: Async function to execute jobs
        """
        self.max_concurrent = max_concurrent
        self._executor = executor or self._default_executor
        self._jobs: Dict[str, Job] = {}
        self._semaphore = asyncio.Semaphore(max_concurrent)
        self._cancel_events: Dict[str, asyncio.Event] = {}
        self._thread_pool = ThreadPoolExecutor(max_workers=max_concurrent)

    async def submit(
        self,
        command: str,
        args: Dict[str, Any] = None,
        options: Dict[str, Any] = None,
    ) -> Job:
        """
        Submit a new job for execution.

        Args:
            command: PDD command name (e.g., "sync", "generate")
            args: Positional arguments for the command
            options: Optional flags/options

        Returns:
            Job object with id and status
        """
        job = Job(
            command=command,
            args=args or {},
            options=options or {},
        )

        self._jobs[job.id] = job
        self._cancel_events[job.id] = asyncio.Event()

        # Start execution in background
        asyncio.create_task(self._execute_job(job))

        return job

    async def _execute_job(self, job: Job) -> None:
        """Execute a job with semaphore control."""
        async with self._semaphore:
            job.status = JobStatus.RUNNING
            job.started_at = datetime.now(timezone.utc)

            try:
                # Check for cancellation before starting
                if self._cancel_events[job.id].is_set():
                    job.status = JobStatus.CANCELLED
                    return

                # Execute the job
                result = await self._executor(job)

                # Check for cancellation after execution
                if self._cancel_events[job.id].is_set():
                    job.status = JobStatus.CANCELLED
                else:
                    job.result = result
                    job.cost = result.get("cost", 0.0)
                    job.status = JobStatus.COMPLETED

            except asyncio.CancelledError:
                job.status = JobStatus.CANCELLED
            except Exception as e:
                job.error = str(e)
                job.status = JobStatus.FAILED
            finally:
                job.completed_at = datetime.now(timezone.utc)

    async def _default_executor(self, job: Job) -> Dict[str, Any]:
        """
        Default executor that simulates job execution.

        In real implementation, this would call the actual PDD command.
        """
        # Simulate some work
        await asyncio.sleep(1.0)

        return {
            "success": True,
            "message": f"Executed {job.command}",
            "cost": 0.01,
        }

    def get_job(self, job_id: str) -> Optional[Job]:
        """Get a job by ID."""
        return self._jobs.get(job_id)

    def get_all_jobs(self) -> Dict[str, Job]:
        """Get all jobs."""
        return self._jobs.copy()

    def get_active_jobs(self) -> Dict[str, Job]:
        """Get all running or queued jobs."""
        return {
            job_id: job
            for job_id, job in self._jobs.items()
            if job.status in (JobStatus.QUEUED, JobStatus.RUNNING)
        }

    async def cancel(self, job_id: str) -> bool:
        """
        Cancel a job.

        Args:
            job_id: The job ID to cancel

        Returns:
            True if job was cancelled, False if not found or already complete
        """
        job = self._jobs.get(job_id)
        if not job:
            return False

        if job.status in (JobStatus.COMPLETED, JobStatus.FAILED, JobStatus.CANCELLED):
            return False

        # Signal cancellation
        if job_id in self._cancel_events:
            self._cancel_events[job_id].set()

        return True

    def cleanup_old_jobs(self, max_age_seconds: float = 3600) -> int:
        """
        Remove completed jobs older than max_age_seconds.

        Returns:
            Number of jobs removed
        """
        now = datetime.now(timezone.utc)
        to_remove = []

        for job_id, job in self._jobs.items():
            if job.completed_at:
                age = (now - job.completed_at).total_seconds()
                if age > max_age_seconds:
                    to_remove.append(job_id)

        for job_id in to_remove:
            del self._jobs[job_id]
            if job_id in self._cancel_events:
                del self._cancel_events[job_id]

        return len(to_remove)

    async def shutdown(self) -> None:
        """Shutdown the job manager, cancelling all active jobs."""
        # Cancel all active jobs
        for job_id in list(self.get_active_jobs().keys()):
            await self.cancel(job_id)

        # Shutdown thread pool
        self._thread_pool.shutdown(wait=False)


# ============================================================================
# Job Callbacks (for integration)
# ============================================================================

class JobCallbacks:
    """
    Callback handlers for job lifecycle events.

    Use this to integrate with WebSocket streaming.
    """

    def __init__(self):
        self._on_start: list[Callable[[Job], Awaitable[None]]] = []
        self._on_output: list[Callable[[Job, str, str], Awaitable[None]]] = []
        self._on_progress: list[Callable[[Job, int, int, str], Awaitable[None]]] = []
        self._on_complete: list[Callable[[Job], Awaitable[None]]] = []

    def on_start(self, callback: Callable[[Job], Awaitable[None]]) -> None:
        """Register callback for job start."""
        self._on_start.append(callback)

    def on_output(self, callback: Callable[[Job, str, str], Awaitable[None]]) -> None:
        """Register callback for job output (stream_type, text)."""
        self._on_output.append(callback)

    def on_progress(
        self, callback: Callable[[Job, int, int, str], Awaitable[None]]
    ) -> None:
        """Register callback for progress (current, total, message)."""
        self._on_progress.append(callback)

    def on_complete(self, callback: Callable[[Job], Awaitable[None]]) -> None:
        """Register callback for job completion."""
        self._on_complete.append(callback)

    async def emit_start(self, job: Job) -> None:
        """Emit job start event."""
        for callback in self._on_start:
            await callback(job)

    async def emit_output(self, job: Job, stream_type: str, text: str) -> None:
        """Emit output event."""
        for callback in self._on_output:
            await callback(job, stream_type, text)

    async def emit_progress(
        self, job: Job, current: int, total: int, message: str = ""
    ) -> None:
        """Emit progress event."""
        for callback in self._on_progress:
            await callback(job, current, total, message)

    async def emit_complete(self, job: Job) -> None:
        """Emit completion event."""
        for callback in self._on_complete:
            await callback(job)


# ============================================================================
# Example Usage
# ============================================================================

async def main():
    """
    Example demonstrating job manager usage.
    """
    print("Job Manager Example")
    print("=" * 40)

    # Create manager
    manager = JobManager(max_concurrent=2)

    # Custom executor that simulates PDD commands
    async def pdd_executor(job: Job) -> Dict[str, Any]:
        print(f"Executing: {job.command} with args={job.args}")

        # Simulate different commands
        if job.command == "sync":
            await asyncio.sleep(2.0)
            return {"success": True, "cost": 0.05, "tests_passed": 5}
        elif job.command == "generate":
            await asyncio.sleep(1.0)
            return {"success": True, "cost": 0.02, "lines_generated": 100}
        else:
            await asyncio.sleep(0.5)
            return {"success": True, "cost": 0.01}

    manager._executor = pdd_executor

    # Submit multiple jobs
    jobs = []
    for i, cmd in enumerate(["generate", "sync", "generate"]):
        job = await manager.submit(cmd, args={"basename": f"module_{i}"})
        jobs.append(job)
        print(f"Submitted job {job.id[:8]}... for '{cmd}'")

    # Wait for completion
    print("\nWaiting for jobs to complete...")
    while manager.get_active_jobs():
        await asyncio.sleep(0.5)
        for job in jobs:
            current = manager.get_job(job.id)
            print(f"  {job.id[:8]}... status={current.status.value}")

    # Show results
    print("\nResults:")
    for job in jobs:
        final = manager.get_job(job.id)
        print(f"  {final.command}: {final.status.value}, cost=${final.cost:.4f}")
        if final.result:
            print(f"    result: {final.result}")

    await manager.shutdown()


if __name__ == "__main__":
    asyncio.run(main())
