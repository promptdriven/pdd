"""
REST API endpoints for PDD command execution.

Provides endpoints for submitting, monitoring, and canceling CLI commands
through asynchronous job management.
"""

from __future__ import annotations

import asyncio
import os
import signal
import subprocess
import sys
import threading
import time
import uuid
from datetime import datetime, timezone
from typing import Any, Dict, List, Optional, Tuple

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

from pydantic import BaseModel

from ..models import CommandRequest, JobHandle, JobResult, JobStatus
from ..jobs import JobManager
from ..click_executor import ClickCommandExecutor, get_pdd_command


class RunResult(BaseModel):
    """Result of running a command in terminal mode."""
    success: bool
    message: str
    exit_code: int = 0
    stdout: Optional[str] = None
    stderr: Optional[str] = None
    error_details: Optional[str] = None


class CancelResult(BaseModel):
    """Result of cancelling a command."""
    cancelled: bool
    message: str


# Track current running process for cancellation
class ProcessTracker:
    """Thread-safe tracker for the currently running command process."""

    def __init__(self):
        self._process: Optional[subprocess.Popen] = None
        self._lock = threading.Lock()
        self._command_info: Optional[str] = None

    def set_process(self, process: subprocess.Popen, command_info: str):
        with self._lock:
            self._process = process
            self._command_info = command_info

    def clear_process(self):
        with self._lock:
            self._process = None
            self._command_info = None

    def cancel(self) -> Tuple[bool, str]:
        """Cancel the current process if running. Returns (success, message)."""
        with self._lock:
            if self._process is None:
                return False, "No command is currently running"

            try:
                # Try graceful termination first
                self._process.terminate()

                # Give it a moment to terminate gracefully
                try:
                    self._process.wait(timeout=2)
                except subprocess.TimeoutExpired:
                    # Force kill if it doesn't respond
                    self._process.kill()

                cmd_info = self._command_info or "unknown command"
                self._process = None
                self._command_info = None
                return True, f"Cancelled: {cmd_info}"

            except Exception as e:
                return False, f"Failed to cancel: {str(e)}"

    def is_running(self) -> bool:
        with self._lock:
            return self._process is not None and self._process.poll() is None

    def get_command_info(self) -> Optional[str]:
        with self._lock:
            return self._command_info


# Global process tracker instance
_process_tracker = ProcessTracker()

# Allowed commands whitelist
ALLOWED_COMMANDS = {
    "sync": "Synchronize prompts with code and tests",
    "update": "Update prompts based on code changes",
    "bug": "Generate unit test from bug (agentic mode)",
    "generate": "Generate code from prompt",
    "test": "Generate unit tests",
    "example": "Generate example code",
    "fix": "Fix code based on test errors",
    "crash": "Fix code based on crash errors",
    "verify": "Verify code against prompt requirements",
    # Advanced operations
    "split": "Split large prompt files into smaller ones",
    "change": "Modify prompts based on change instructions",
    "detect": "Detect which prompts need changes",
    "auto-deps": "Analyze project dependencies and update prompt",
    "conflicts": "Check for conflicts between prompt files",
    "preprocess": "Preprocess prompt file for LLM use",
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


def _find_pdd_executable() -> Optional[str]:
    """Find the pdd executable path."""
    import shutil
    from pathlib import Path

    # First try to find 'pdd' in PATH
    pdd_path = shutil.which("pdd")
    if pdd_path:
        return pdd_path

    # Try to find 'pdd' in the same directory as the Python interpreter
    # This handles virtual environments and conda environments
    python_dir = Path(sys.executable).parent
    pdd_in_python_dir = python_dir / "pdd"
    if pdd_in_python_dir.exists():
        return str(pdd_in_python_dir)

    # Fallback: None means we need to use the module approach
    return None


# Commands where specific args should be positional (not --options)
# Order matters! Arguments are added in this order.
POSITIONAL_ARGS = {
    "sync": ["basename"],
    "generate": ["prompt_file"],
    "test": ["prompt_file", "code_file"],
    "example": ["prompt_file", "code_file"],
    "fix": ["prompt_file", "code_file", "unit_test_files", "error_file"],  # pdd fix PROMPT CODE TEST... ERROR
    "bug": ["args"],  # Special: 'args' contains the positional arguments
    "update": ["args"],  # Special: 'args' contains the positional arguments
    "crash": ["prompt_file", "code_file", "program_file", "error_file"],  # pdd crash PROMPT CODE PROGRAM ERROR
    "verify": ["prompt_file", "code_file", "verification_program"],  # pdd verify PROMPT CODE VERIFICATION_PROGRAM
    # Advanced operations
    "split": ["input_prompt", "input_code", "example_code"],  # pdd split INPUT_PROMPT INPUT_CODE EXAMPLE_CODE
    "change": ["change_prompt_file", "input_code", "input_prompt_file"],  # pdd change CHANGE_PROMPT INPUT_CODE [INPUT_PROMPT]
    "detect": ["args"],  # Special: 'args' contains [PROMPT_FILES..., CHANGE_FILE]
    "auto-deps": ["prompt_file", "directory_path"],  # pdd auto-deps PROMPT DIRECTORY
    "conflicts": ["prompt_file", "prompt2"],  # pdd conflicts PROMPT1 PROMPT2
    "preprocess": ["prompt_file"],  # pdd preprocess PROMPT
}


# Global options that must be placed BEFORE the subcommand (defined on cli group)
GLOBAL_OPTIONS = {
    "force", "strength", "temperature", "time", "verbose", "quiet",
    "output_cost", "review_examples", "local", "context", "list_contexts", "core_dump"
}


def _build_pdd_command_args(command: str, args: Optional[Dict], options: Optional[Dict]) -> List[str]:
    """Build command line arguments for pdd subprocess.

    Global options (--force, --strength, etc.) are placed BEFORE the subcommand.
    Command-specific options are placed AFTER the subcommand and positional args.
    """
    pdd_exe = _find_pdd_executable()

    # Start with just the executable - we'll add global options, then command
    if pdd_exe:
        cmd_args = [pdd_exe]
    else:
        # Fallback: use runpy to run the CLI module with proper argument handling
        cmd_args = [
            sys.executable, "-c",
            "import sys; from pdd.cli import cli; sys.exit(cli())"
        ]

    # Separate global options from command-specific options
    global_opts: Dict[str, Any] = {}
    cmd_opts: Dict[str, Any] = {}

    if options:
        for key, value in options.items():
            # Normalize key for comparison (replace hyphens with underscores)
            normalized_key = key.replace("-", "_")
            if normalized_key in GLOBAL_OPTIONS:
                global_opts[key] = value
            else:
                cmd_opts[key] = value

    # Add global options BEFORE the command
    for key, value in global_opts.items():
        if isinstance(value, bool):
            if value:
                cmd_args.append(f"--{key.replace('_', '-')}")
        elif isinstance(value, (list, tuple)):
            for v in value:
                cmd_args.extend([f"--{key.replace('_', '-')}", str(v)])
        elif value is not None:
            cmd_args.extend([f"--{key.replace('_', '-')}", str(value)])

    # Now add the command
    cmd_args.append(command)

    # Get positional arg names for this command
    positional_names = POSITIONAL_ARGS.get(command, [])

    if args:
        # First, add positional arguments in order
        for pos_name in positional_names:
            if pos_name in args:
                value = args[pos_name]
                if pos_name == "args" and isinstance(value, (list, tuple)):
                    # Special case: 'args' is a list of positional args
                    cmd_args.extend(str(v) for v in value)
                elif value is not None:
                    cmd_args.append(str(value))

        # Then, add remaining args as options (--key value)
        for key, value in args.items():
            if key in positional_names:
                continue  # Already handled as positional
            if isinstance(value, bool):
                if value:
                    cmd_args.append(f"--{key.replace('_', '-')}")
            elif isinstance(value, (list, tuple)):
                for v in value:
                    cmd_args.extend([f"--{key.replace('_', '-')}", str(v)])
            elif value is not None:
                cmd_args.extend([f"--{key.replace('_', '-')}", str(value)])

    # Add command-specific options (global options were already added before the command)
    if cmd_opts:
        for key, value in cmd_opts.items():
            if isinstance(value, bool):
                if value:
                    cmd_args.append(f"--{key.replace('_', '-')}")
            elif isinstance(value, (list, tuple)):
                # Handle array options (e.g., multiple -e KEY=VALUE flags)
                for v in value:
                    cmd_args.extend([f"--{key.replace('_', '-')}", str(v)])
            elif value is not None:
                cmd_args.extend([f"--{key.replace('_', '-')}", str(value)])

    return cmd_args


def _parse_error_details(exit_code: int) -> str:
    """Parse exit code and return user-friendly error details."""
    error_messages = {
        1: "Command failed - check the terminal output above for details",
        2: "Command line usage error - invalid arguments or options",
        126: "Command not executable - permission denied",
        127: "Command not found - pdd may not be properly installed",
        128: "Invalid exit argument",
        130: "Command terminated by Ctrl+C",
        137: "Command killed (SIGKILL) - possibly out of memory",
        139: "Segmentation fault",
        143: "Command terminated (SIGTERM)",
    }

    # Check for specific PDD exit codes
    if exit_code == 1:
        return "Command failed - this may indicate missing files, authentication issues, or other errors. Check the terminal for details."

    return error_messages.get(exit_code, f"Command exited with code {exit_code}")


@router.post("/run", response_model=RunResult)
async def run_command_in_terminal(request: CommandRequest):
    """
    Execute a command in terminal mode as a subprocess.

    Output goes directly to the terminal where the server is running.
    This endpoint blocks until the command completes or is cancelled.

    Use POST /commands/cancel to stop a running command.
    """
    # Validate command is allowed
    if request.command not in ALLOWED_COMMANDS:
        raise HTTPException(
            status_code=400,
            detail=f"Unknown command: {request.command}. Allowed: {list(ALLOWED_COMMANDS.keys())}"
        )

    # Check if a command is already running
    if _process_tracker.is_running():
        raise HTTPException(
            status_code=409,
            detail=f"A command is already running: {_process_tracker.get_command_info()}"
        )

    # Build command arguments
    cmd_args = _build_pdd_command_args(request.command, request.args, request.options)
    command_str = f"pdd {request.command}"

    # Build display command (just 'pdd <cmd> <args>' without full path)
    display_args = cmd_args[1:] if cmd_args[0].endswith('pdd') else cmd_args[3:]  # Skip python -c wrapper
    display_cmd = f"pdd {' '.join(display_args)}"

    # Print separator for visibility in terminal
    console.print(f"\n[bold cyan]{'='*60}[/bold cyan]")
    console.print(f"[bold cyan]Running: {display_cmd}[/bold cyan]")
    console.print(f"[cyan]{'='*60}[/cyan]\n")

    try:
        # Set environment to disable TUI and enable headless mode
        env = os.environ.copy()
        env['CI'] = '1'  # Triggers headless mode in sync
        env['PDD_FORCE'] = '1'  # Skip confirmation prompts
        env['TERM'] = 'dumb'  # Disable fancy terminal features

        # Start subprocess - output goes directly to terminal (inherit stdio)
        process = subprocess.Popen(
            cmd_args,
            stdout=None,  # Inherit from parent (terminal)
            stderr=None,  # Inherit from parent (terminal)
            stdin=None,
            cwd=os.getcwd(),
            env=env,
        )

        # Track the process for cancellation
        _process_tracker.set_process(process, command_str)

        # Wait for completion in a way that allows async cancellation
        def wait_for_process():
            return process.wait()

        loop = asyncio.get_event_loop()
        exit_code = await loop.run_in_executor(None, wait_for_process)

    except Exception as e:
        console.print(f"\n[bold red]{'='*60}[/bold red]")
        console.print(f"[bold red]Failed to start command: {str(e)}[/bold red]")
        console.print(f"[red]{'='*60}[/red]\n")
        return RunResult(
            success=False,
            message=f"Failed to start command: {str(e)}",
            exit_code=1,
        )
    finally:
        _process_tracker.clear_process()

    # Print completion message
    if exit_code == 0:
        console.print(f"\n[bold green]{'='*60}[/bold green]")
        console.print(f"[bold green]Command completed successfully[/bold green]")
        console.print(f"[green]{'='*60}[/green]\n")
    elif exit_code == -signal.SIGTERM or exit_code == -signal.SIGKILL:
        console.print(f"\n[bold yellow]{'='*60}[/bold yellow]")
        console.print(f"[bold yellow]Command was cancelled[/bold yellow]")
        console.print(f"[yellow]{'='*60}[/yellow]\n")
        return RunResult(
            success=False,
            message="Command was cancelled",
            exit_code=exit_code,
        )
    else:
        console.print(f"\n[bold red]{'='*60}[/bold red]")
        console.print(f"[bold red]Command failed (exit code: {exit_code})[/bold red]")
        console.print(f"[red]{'='*60}[/red]\n")

        # Parse common error patterns based on exit code
        error_details = _parse_error_details(exit_code)

        return RunResult(
            success=False,
            message=f"Command failed with exit code {exit_code}",
            exit_code=exit_code,
            error_details=error_details,
        )

    return RunResult(
        success=True,
        message="Command completed successfully",
        exit_code=0,
    )


@router.post("/cancel", response_model=CancelResult)
async def cancel_current_command():
    """
    Cancel the currently running command.

    Returns success if a command was cancelled, failure if no command was running.
    """
    cancelled, message = _process_tracker.cancel()

    if cancelled:
        console.print(f"\n[bold yellow]{'='*60}[/bold yellow]")
        console.print(f"[bold yellow]{message}[/bold yellow]")
        console.print(f"[yellow]{'='*60}[/yellow]\n")

    return CancelResult(cancelled=cancelled, message=message)


@router.get("/status")
async def get_command_status():
    """
    Get the status of the current running command.

    Returns whether a command is running and its info.
    """
    is_running = _process_tracker.is_running()
    command_info = _process_tracker.get_command_info()

    return {
        "running": is_running,
        "command": command_info,
    }


# ============================================================================
# Terminal Spawning - Run commands in separate terminal windows
# ============================================================================

from ..terminal_spawner import TerminalSpawner


class SpawnTerminalResponse(BaseModel):
    """Response from spawning a terminal."""
    success: bool
    message: str
    command: str
    platform: str
    job_id: Optional[str] = None


class SpawnedJobCompleteRequest(BaseModel):
    """Request body for completing a spawned job."""
    success: bool
    exit_code: int = 0


class SpawnedJobCompleteResponse(BaseModel):
    """Response from completing a spawned job."""
    updated: bool
    job_id: str


class SpawnedJobStatus(BaseModel):
    """Status of a spawned job."""
    job_id: str
    command: str
    status: str
    started_at: str
    completed_at: Optional[str] = None
    exit_code: Optional[int] = None


# Track spawned jobs in memory
# Key: job_id, Value: dict with job info
_spawned_jobs: Dict[str, dict] = {}


@router.post("/spawned-jobs/{job_id}/complete", response_model=SpawnedJobCompleteResponse)
async def complete_spawned_job(job_id: str, request: SpawnedJobCompleteRequest):
    """
    Called by spawned terminal script when command completes.

    The shell script in the terminal calls this endpoint via curl
    when the command finishes to report success/failure.
    """
    if job_id in _spawned_jobs:
        _spawned_jobs[job_id]["status"] = "completed" if request.success else "failed"
        _spawned_jobs[job_id]["exit_code"] = request.exit_code
        _spawned_jobs[job_id]["completed_at"] = datetime.now(timezone.utc).isoformat()

        status_str = "completed" if request.success else "failed"
        console.print(f"[cyan]Spawned job {job_id[:16]}... {status_str} (exit code: {request.exit_code})[/cyan]")

        return SpawnedJobCompleteResponse(updated=True, job_id=job_id)

    return SpawnedJobCompleteResponse(updated=False, job_id=job_id)


@router.get("/spawned-jobs/{job_id}/status", response_model=SpawnedJobStatus)
async def get_spawned_job_status(job_id: str):
    """
    Get the status of a spawned job.

    Frontend polls this endpoint to check if spawned jobs have completed.
    """
    if job_id in _spawned_jobs:
        job = _spawned_jobs[job_id]
        return SpawnedJobStatus(
            job_id=job_id,
            command=job.get("command", "unknown"),
            status=job.get("status", "unknown"),
            started_at=job.get("started_at", ""),
            completed_at=job.get("completed_at"),
            exit_code=job.get("exit_code"),
        )

    return SpawnedJobStatus(
        job_id=job_id,
        command="unknown",
        status="unknown",
        started_at="",
    )


@router.post("/spawn-terminal", response_model=SpawnTerminalResponse)
async def spawn_terminal_command(request: CommandRequest):
    """
    Spawn a PDD command in a new terminal window.

    The command runs in complete isolation from the server.
    User sees output directly in the new terminal window.

    This is safer than running commands in the server process because:
    - Each command runs in its own terminal process
    - No risk of WebSocket/subprocess conflicts
    - User can manage terminal windows directly

    The spawned terminal script will call back to report completion status.
    """
    # Validate command is allowed
    if request.command not in ALLOWED_COMMANDS:
        raise HTTPException(
            status_code=400,
            detail=f"Unknown command: {request.command}. Allowed: {list(ALLOWED_COMMANDS.keys())}"
        )

    # Generate unique job ID
    job_id = f"spawned-{int(time.time() * 1000)}-{uuid.uuid4().hex[:8]}"

    # Build full command
    cmd_args = _build_pdd_command_args(request.command, request.args, request.options)
    cmd_str = " ".join(cmd_args)

    # Get working directory
    cwd = os.getcwd()

    # Track the job before spawning
    _spawned_jobs[job_id] = {
        "job_id": job_id,
        "command": request.command,
        "status": "running",
        "started_at": datetime.now(timezone.utc).isoformat(),
        "completed_at": None,
        "exit_code": None,
    }

    # Spawn terminal with job_id for callback
    success = TerminalSpawner.spawn(cmd_str, working_dir=cwd, job_id=job_id)

    if success:
        console.print(f"\n[bold cyan]{'='*60}[/bold cyan]")
        console.print(f"[bold cyan]Spawned terminal: pdd {request.command}[/bold cyan]")
        console.print(f"[cyan]Job ID: {job_id}[/cyan]")
        console.print(f"[cyan]{'='*60}[/cyan]\n")
    else:
        console.print(f"\n[bold red]Failed to spawn terminal for: pdd {request.command}[/bold red]")
        # Remove from tracking if spawn failed
        del _spawned_jobs[job_id]

    return SpawnTerminalResponse(
        success=success,
        message="Terminal window opened" if success else "Failed to open terminal",
        command=request.command,
        platform=sys.platform,
        job_id=job_id if success else None,
    )
