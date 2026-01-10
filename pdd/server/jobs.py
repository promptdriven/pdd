from __future__ import annotations

import asyncio
import logging
from concurrent.futures import ThreadPoolExecutor
from dataclasses import dataclass, field
from datetime import datetime, timezone
from typing import Any, Awaitable, Callable, Dict, List, Optional
from uuid import uuid4

# Robust import for rich console
try:
    from rich.console import Console
    console = Console()
except ImportError:
    class Console:
        def print(self, *args, **kwargs):
            import builtins
            builtins.print(*args)
    console = Console()

# Robust import for internal dependencies
try:
    from .click_executor import ClickCommandExecutor, get_pdd_command
except ImportError:
    class ClickCommandExecutor:
        def __init__(self, base_context_obj=None, output_callback=None):
            pass
        def execute(self, *args, **kwargs):
            raise NotImplementedError("ClickCommandExecutor not available")

    def get_pdd_command(name):
        return None

from .models import JobStatus

logger = logging.getLogger(__name__)


@dataclass
class Job:
    """
    Internal representation of a queued or executing job.
    """
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


class JobCallbacks:
    """Async callback handlers for job lifecycle events."""

    def __init__(self):
        self._on_start: List[Callable[[Job], Awaitable[None]]] = []
        self._on_output: List[Callable[[Job, str, str], Awaitable[None]]] = []
        self._on_progress: List[Callable[[Job, int, int, str], Awaitable[None]]] = []
        self._on_complete: List[Callable[[Job], Awaitable[None]]] = []

    def on_start(self, callback: Callable[[Job], Awaitable[None]]) -> None:
        self._on_start.append(callback)

    def on_output(self, callback: Callable[[Job, str, str], Awaitable[None]]) -> None:
        self._on_output.append(callback)

    def on_progress(self, callback: Callable[[Job, int, int, str], Awaitable[None]]) -> None:
        self._on_progress.append(callback)

    def on_complete(self, callback: Callable[[Job], Awaitable[None]]) -> None:
        self._on_complete.append(callback)

    async def emit_start(self, job: Job) -> None:
        for callback in self._on_start:
            try:
                await callback(job)
            except Exception as e:
                console.print(f"[red]Error in on_start callback: {e}[/red]")

    async def emit_output(self, job: Job, stream_type: str, text: str) -> None:
        for callback in self._on_output:
            try:
                await callback(job, stream_type, text)
            except Exception as e:
                console.print(f"[red]Error in on_output callback: {e}[/red]")

    async def emit_progress(self, job: Job, current: int, total: int, message: str = "") -> None:
        for callback in self._on_progress:
            try:
                await callback(job, current, total, message)
            except Exception as e:
                console.print(f"[red]Error in on_progress callback: {e}[/red]")

    async def emit_complete(self, job: Job) -> None:
        for callback in self._on_complete:
            try:
                await callback(job)
            except Exception as e:
                console.print(f"[red]Error in on_complete callback: {e}[/red]")


class JobManager:
    """
    Manages async job execution, queuing, and lifecycle tracking.
    """

    def __init__(
        self,
        max_concurrent: int = 1,
        executor: Optional[Callable[[Job], Awaitable[Dict[str, Any]]]] = None,
    ):
        self.max_concurrent = max_concurrent
        self.callbacks = JobCallbacks()
        
        self._jobs: Dict[str, Job] = {}
        self._tasks: Dict[str, asyncio.Task] = {}
        self._semaphore = asyncio.Semaphore(max_concurrent)
        self._cancel_events: Dict[str, asyncio.Event] = {}
        
        self._thread_pool = ThreadPoolExecutor(
            max_workers=max_concurrent, 
            thread_name_prefix="pdd_job_worker"
        )
        
        self._custom_executor = executor

    async def submit(
        self,
        command: str,
        args: Dict[str, Any] = None,
        options: Dict[str, Any] = None,
    ) -> Job:
        job = Job(
            command=command,
            args=args or {},
            options=options or {},
        )

        self._jobs[job.id] = job
        self._cancel_events[job.id] = asyncio.Event()

        console.print(f"[blue]Job submitted:[/blue] {job.id} ({command})")
        
        task = asyncio.create_task(self._execute_wrapper(job))
        self._tasks[job.id] = task

        # Callback to handle cleanup and edge-case cancellation (cancelled before start)
        def _on_task_done(t: asyncio.Task):
            if job.id in self._tasks:
                del self._tasks[job.id]
            
            # If task was cancelled but job status wasn't updated (e.g. never started running)
            if t.cancelled() and job.status == JobStatus.QUEUED:
                job.status = JobStatus.CANCELLED
                if not job.completed_at:
                    job.completed_at = datetime.now(timezone.utc)
                console.print(f"[yellow]Job cancelled (Task Done):[/yellow] {job.id}")

        task.add_done_callback(_on_task_done)

        return job

    async def _execute_wrapper(self, job: Job) -> None:
        try:
            async with self._semaphore:
                await self._execute_job(job)
        except asyncio.CancelledError:
            # Handle cancellation while waiting for semaphore
            if job.status == JobStatus.QUEUED:
                job.status = JobStatus.CANCELLED
                job.completed_at = datetime.now(timezone.utc)
                console.print(f"[yellow]Job cancelled (Queue):[/yellow] {job.id}")
            raise # Re-raise to ensure task is marked as cancelled for the callback

    async def _execute_job(self, job: Job) -> None:
        try:
            # 1. Check cancellation before starting
            if self._cancel_events[job.id].is_set():
                job.status = JobStatus.CANCELLED
                console.print(f"[yellow]Job cancelled (Queued):[/yellow] {job.id}")
                return

            # 2. Update status and notify
            job.status = JobStatus.RUNNING
            job.started_at = datetime.now(timezone.utc)
            await self.callbacks.emit_start(job)

            # 3. Execute
            result = None
            
            if self._custom_executor:
                result = await self._custom_executor(job)
            else:
                result = await self._run_click_command(job)

            # 4. Handle Result
            if self._cancel_events[job.id].is_set():
                job.status = JobStatus.CANCELLED
                console.print(f"[yellow]Job cancelled:[/yellow] {job.id}")
            else:
                job.result = result
                job.cost = float(result.get("cost", 0.0)) if isinstance(result, dict) else 0.0
                job.status = JobStatus.COMPLETED
                console.print(f"[green]Job completed:[/green] {job.id}")

        except asyncio.CancelledError:
            job.status = JobStatus.CANCELLED
            console.print(f"[yellow]Job cancelled (Task):[/yellow] {job.id}")
            raise # Re-raise to propagate cancellation
            
        except Exception as e:
            job.error = str(e)
            job.status = JobStatus.FAILED
            console.print(f"[red]Job failed:[/red] {job.id} - {e}")
            
        finally:
            # 5. Cleanup and Notify
            if not job.completed_at:
                job.completed_at = datetime.now(timezone.utc)
            await self.callbacks.emit_complete(job)
            
            if job.id in self._cancel_events:
                del self._cancel_events[job.id]

    async def _run_click_command(self, job: Job) -> Dict[str, Any]:
        click_cmd = get_pdd_command(job.command)
        if not click_cmd:
            raise ValueError(f"Unknown command: {job.command}")

        loop = asyncio.get_running_loop()

        def sync_output_callback(stream: str, text: str):
            if job.status == JobStatus.RUNNING:
                asyncio.run_coroutine_threadsafe(
                    self.callbacks.emit_output(job, stream, text),
                    loop
                )

        executor = ClickCommandExecutor(
            base_context_obj=job.options,
            output_callback=sync_output_callback
        )

        captured = await loop.run_in_executor(
            self._thread_pool,
            executor.execute,
            click_cmd,
            job.args,
            job.options
        )

        if captured.exit_code != 0:
            error_msg = captured.stderr or captured.stdout or "Command failed with non-zero exit code"
            raise RuntimeError(error_msg)

        return {
            "stdout": captured.stdout,
            "stderr": captured.stderr,
            "exit_code": captured.exit_code,
            "cost": 0.0 
        }

    def get_job(self, job_id: str) -> Optional[Job]:
        return self._jobs.get(job_id)

    def get_all_jobs(self) -> Dict[str, Job]:
        return self._jobs.copy()

    def get_active_jobs(self) -> Dict[str, Job]:
        return {
            job_id: job
            for job_id, job in self._jobs.items()
            if job.status in (JobStatus.QUEUED, JobStatus.RUNNING)
        }

    async def cancel(self, job_id: str) -> bool:
        job = self._jobs.get(job_id)
        if not job:
            return False

        if job.status in (JobStatus.COMPLETED, JobStatus.FAILED, JobStatus.CANCELLED):
            return False

        if job_id in self._cancel_events:
            self._cancel_events[job_id].set()
            
        if job_id in self._tasks:
            self._tasks[job_id].cancel()
            
        console.print(f"[yellow]Cancellation requested for job:[/yellow] {job_id}")
        return True

    def cleanup_old_jobs(self, max_age_seconds: float = 3600) -> int:
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
            if job_id in self._tasks:
                del self._tasks[job_id]

        if to_remove:
            console.print(f"[dim]Cleaned up {len(to_remove)} old jobs[/dim]")
            
        return len(to_remove)

    async def shutdown(self) -> None:
        console.print("[bold red]Shutting down JobManager...[/bold red]")
        
        active_jobs = list(self.get_active_jobs().keys())
        for job_id in active_jobs:
            await self.cancel(job_id)

        if active_jobs:
            await asyncio.sleep(0.1)

        self._thread_pool.shutdown(wait=False)