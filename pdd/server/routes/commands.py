"""
REST API endpoints for PDD command execution.

Provides endpoints for submitting, monitoring, and canceling CLI commands
through asynchronous job management.
"""

from __future__ import annotations

from datetime import datetime, timezone
from typing import Dict, List, Optional

from fastapi import APIRouter, Depends, HTTPException, Query

try:
    from rich.console import Console
    console = Console()
except ImportError:
    class Console:
        def print(self, *args, **kwargs):
            import builtins
            builtins.print(*args)
    console = Console()

from ..models import CommandRequest, JobHandle, JobResult, JobStatus
from ..jobs import JobManager

# Allowed commands whitelist
ALLOWED_COMMANDS = {
    "sync": "Synchronize prompts with code and tests",
    "update": "Update prompts based on code changes",
    "bug": "Generate unit test from bug (agentic mode)",
    "generate": "Generate code from prompt",
    "test": "Generate unit tests",
    "fix": "Fix code based on test errors",
}

router = APIRouter(prefix="/api/v1/commands", tags=["commands"])

# Dependency injection placeholder - will be overridden by app
_job_manager: Optional[JobManager] = None


def get_job_manager() -> JobManager:
    """Dependency to get the JobManager instance."""
    if _job_manager is None:
        raise RuntimeError("JobManager not configured")
    return _job_manager


def set_job_manager(manager: JobManager) -> None:
    """Configure the JobManager instance."""
    global _job_manager
    _job_manager = manager


@router.post("/execute", response_model=JobHandle)
async def execute_command(
    request: CommandRequest,
    manager: JobManager = Depends(get_job_manager),
):
    """
    Submit a command for execution.

    Returns immediately with a job handle. Use /jobs/{job_id} to check status.
    """
    # Validate command is allowed
    if request.command not in ALLOWED_COMMANDS:
        raise HTTPException(
            status_code=400,
            detail=f"Unknown command: {request.command}. Allowed: {list(ALLOWED_COMMANDS.keys())}"
        )

    # Submit job
    job = await manager.submit(
        command=request.command,
        args=request.args,
        options=request.options,
    )

    return JobHandle(
        job_id=job.id,
        status=job.status,
        created_at=job.created_at,
    )


@router.get("/jobs/{job_id}", response_model=JobResult)
async def get_job_status(
    job_id: str,
    manager: JobManager = Depends(get_job_manager),
):
    """
    Get the status and result of a job.
    """
    job = manager.get_job(job_id)
    if not job:
        raise HTTPException(status_code=404, detail=f"Job not found: {job_id}")

    duration = 0.0
    if job.started_at and job.completed_at:
        duration = (job.completed_at - job.started_at).total_seconds()
    elif job.started_at:
        # Use timezone-aware UTC now
        now = datetime.now(timezone.utc)
        # Handle case where job.started_at might be naive (from legacy code or DB)
        if job.started_at.tzinfo is None:
            now = now.replace(tzinfo=None)
        duration = (now - job.started_at).total_seconds()

    return JobResult(
        job_id=job.id,
        status=job.status,
        result=job.result,
        error=job.error,
        cost=job.cost,
        duration_seconds=duration,
        completed_at=job.completed_at,
    )


@router.post("/jobs/{job_id}/cancel")
async def cancel_job(
    job_id: str,
    manager: JobManager = Depends(get_job_manager),
):
    """
    Attempt to cancel a running job.
    """
    job = manager.get_job(job_id)
    if not job:
        raise HTTPException(status_code=404, detail=f"Job not found: {job_id}")

    if job.status in (JobStatus.COMPLETED, JobStatus.FAILED, JobStatus.CANCELLED):
        raise HTTPException(
            status_code=409,
            detail=f"Job already finished with status: {job.status.value}"
        )

    cancelled = await manager.cancel(job_id)
    return {
        "cancelled": cancelled,
        "message": "Cancellation requested" if cancelled else "Could not cancel job"
    }


@router.get("/history", response_model=List[JobResult])
async def get_job_history(
    limit: int = Query(50, description="Maximum number of jobs to return", ge=1, le=200),
    offset: int = Query(0, description="Offset for pagination", ge=0),
    status: Optional[JobStatus] = Query(None, description="Filter by status"),
    manager: JobManager = Depends(get_job_manager),
):
    """
    Get job history.

    Returns jobs ordered by creation time (newest first).
    """
    all_jobs = manager.get_all_jobs()

    # Filter by status if specified
    if status:
        jobs = [j for j in all_jobs.values() if j.status == status]
    else:
        jobs = list(all_jobs.values())

    # Sort by created_at descending
    jobs.sort(key=lambda j: j.created_at, reverse=True)

    # Apply pagination
    jobs = jobs[offset:offset + limit]

    results = []
    for job in jobs:
        duration = 0.0
        if job.started_at and job.completed_at:
            duration = (job.completed_at - job.started_at).total_seconds()
        elif job.started_at:
             # Use timezone-aware UTC now
            now = datetime.now(timezone.utc)
            # Handle case where job.started_at might be naive
            if job.started_at.tzinfo is None:
                now = now.replace(tzinfo=None)
            duration = (now - job.started_at).total_seconds()

        results.append(JobResult(
            job_id=job.id,
            status=job.status,
            result=job.result,
            error=job.error,
            cost=job.cost,
            duration_seconds=duration,
            completed_at=job.completed_at,
        ))

    return results


@router.get("/available")
async def get_available_commands():
    """
    Get list of available commands with descriptions.
    """
    return [
        {"name": name, "description": desc}
        for name, desc in ALLOWED_COMMANDS.items()
    ]
