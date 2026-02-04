from __future__ import annotations

import asyncio
import logging
import os
import signal
import subprocess
import sys
import threading
from concurrent.futures import ThreadPoolExecutor
from dataclasses import dataclass, field
from datetime import datetime, timezone
from pathlib import Path
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


# Global options that must be placed BEFORE the subcommand (defined on cli group)
GLOBAL_OPTIONS = {
    "force", "strength", "temperature", "time", "verbose", "quiet",
    "output_cost", "review_examples", "local", "context", "list_contexts", "core_dump"
}

# Commands where specific args should be positional (not --options)
POSITIONAL_ARGS = {
    "sync": ["basename"],
    "generate": ["prompt_file"],
    "test": ["prompt_file", "code_file"],
    "example": ["prompt_file", "code_file"],
    "fix": ["args"],  # Always uses variadic "args" (both agentic and manual modes)
    "bug": ["args"],
    "update": ["args"],
    "crash": ["prompt_file", "code_file", "program_file", "error_file"],
    "verify": ["prompt_file", "code_file", "verification_program"],
    "split": ["input_prompt", "input_code", "example_code"],
    "change": ["args"],  # Always uses variadic "args" (both agentic and manual modes)
    "detect": ["args"],
    "auto-deps": ["prompt_file", "directory_path"],
    "conflicts": ["prompt_file", "prompt2"],
    "preprocess": ["prompt_file"],
}

# Manual mode file key mappings for fix/change commands
# These commands use variadic "args" for BOTH modes, but the frontend sends semantic keys
# for manual mode which we need to convert to ordered positional arguments
MANUAL_MODE_FILE_KEYS = {
    "fix": ["prompt_file", "code_file", "unit_test_files", "error_file"],
    "change": ["change_prompt_file", "input_code", "input_prompt_file"],
}

logger = logging.getLogger(__name__)


def _find_pdd_executable() -> Optional[str]:
    """Find the pdd executable path."""
    import shutil

    # First try to find 'pdd' in PATH
    pdd_path = shutil.which("pdd")
    if pdd_path:
        return pdd_path

    # Try to find 'pdd' in the same directory as the Python interpreter
    python_dir = Path(sys.executable).parent
    pdd_in_python_dir = python_dir / "pdd"
    if pdd_in_python_dir.exists():
        return str(pdd_in_python_dir)

    return None


def _build_subprocess_command_args(
    command: str,
    args: Optional[Dict[str, Any]],
    options: Optional[Dict[str, Any]]
) -> List[str]:
    """
    Build command line arguments for pdd subprocess.

    Global options (--force, --strength, etc.) are placed BEFORE the subcommand.
    Command-specific options are placed AFTER the subcommand and positional args.
    """
    pdd_exe = _find_pdd_executable()

    if pdd_exe:
        cmd_args = [pdd_exe]
    else:
        # Fallback: use runpy to run the CLI module
        cmd_args = [
            sys.executable, "-c",
            "import sys; from pdd.cli import cli; sys.exit(cli())"
        ]

    # Separate global options from command-specific options
    global_opts: Dict[str, Any] = {}
    cmd_opts: Dict[str, Any] = {}

    if options:
        for key, value in options.items():
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

    # Add the command
    cmd_args.append(command)

    # Handle fix/change manual mode: convert semantic file keys to positional args
    # and add --manual flag. Both modes use variadic "args" parameter.
    if command in MANUAL_MODE_FILE_KEYS and args and "args" not in args:
        # Manual mode detected: has file keys but no "args" key
        file_keys = MANUAL_MODE_FILE_KEYS[command]
        # Check if any file keys are present
        if any(k in args for k in file_keys):
            # Convert file keys to ordered positional args list (order matters!)
            positional_values = []
            for key in file_keys:
                if key in args and args[key] is not None:
                    positional_values.append(str(args[key]))
            # Collect remaining args that aren't file keys (e.g., verification_program)
            remaining_args = {k: v for k, v in args.items() if k not in file_keys}
            # Build new args with positional values
            args = {"args": positional_values}
            # Move remaining args to cmd_opts (they should be options like --verification-program)
            for key, value in remaining_args.items():
                cmd_opts[key] = value
            # Add --manual flag to command-specific options
            cmd_opts["manual"] = True

    # Get positional arg names for this command
    positional_names = POSITIONAL_ARGS.get(command, [])

    if args:
        # First, add positional arguments in order
        for pos_name in positional_names:
            if pos_name in args:
                value = args[pos_name]
                if pos_name == "args" and isinstance(value, (list, tuple)):
                    cmd_args.extend(str(v) for v in value)
                elif value is not None:
                    cmd_args.append(str(value))

        # Then, add remaining args as options
        for key, value in args.items():
            if key in positional_names:
                continue
            if isinstance(value, bool):
                if value:
                    cmd_args.append(f"--{key.replace('_', '-')}")
            elif isinstance(value, (list, tuple)):
                for v in value:
                    cmd_args.extend([f"--{key.replace('_', '-')}", str(v)])
            elif value is not None:
                cmd_args.extend([f"--{key.replace('_', '-')}", str(value)])

    # Add command-specific options
    if cmd_opts:
        for key, value in cmd_opts.items():
            if isinstance(value, bool):
                if value:
                    cmd_args.append(f"--{key.replace('_', '-')}")
            elif isinstance(value, (list, tuple)):
                for v in value:
                    cmd_args.extend([f"--{key.replace('_', '-')}", str(v)])
            elif value is not None:
                cmd_args.extend([f"--{key.replace('_', '-')}", str(value)])

    return cmd_args


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
    # Live output during execution (updated in real-time)
    live_stdout: str = ""
    live_stderr: str = ""

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
            "live_stdout": self.live_stdout,
            "live_stderr": self.live_stderr,
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
        project_root: Optional[Path] = None,
    ):
        self.max_concurrent = max_concurrent
        self.callbacks = JobCallbacks()
        self.project_root = project_root or Path.cwd()

        self._jobs: Dict[str, Job] = {}
        self._tasks: Dict[str, asyncio.Task] = {}
        self._semaphore = asyncio.Semaphore(max_concurrent)
        self._cancel_events: Dict[str, asyncio.Event] = {}

        # Track running subprocesses for cancellation
        self._processes: Dict[str, subprocess.Popen] = {}
        self._process_lock = threading.Lock()

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
            # Preserve captured output for debugging (live_stdout is updated by read_stream)
            if job.live_stdout or job.live_stderr:
                job.result = {
                    "stdout": job.live_stdout,
                    "stderr": job.live_stderr,
                    "exit_code": None,
                }
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
        """
        Run a PDD command as a subprocess with output streaming and cancellation support.

        This uses subprocess execution instead of direct Click invocation to enable:
        - Proper cancellation via SIGTERM/SIGKILL
        - Process isolation
        - Output streaming
        """
        loop = asyncio.get_running_loop()

        # Build command args - add --force to skip confirmation prompts
        options_with_force = dict(job.options) if job.options else {}
        options_with_force['force'] = True  # Skip all confirmation prompts
        cmd_args = _build_subprocess_command_args(job.command, job.args, options_with_force)

        # Set up environment for headless execution
        env = os.environ.copy()
        env['CI'] = '1'
        env['PDD_FORCE'] = '1'
        env['TERM'] = 'dumb'
        env['PDD_SKIP_UPDATE_CHECK'] = '1'  # Skip update prompts

        stdout_lines = []
        stderr_lines = []

        def run_subprocess():
            """Run subprocess in thread with output streaming."""
            try:
                process = subprocess.Popen(
                    cmd_args,
                    stdout=subprocess.PIPE,
                    stderr=subprocess.PIPE,
                    stdin=subprocess.DEVNULL,
                    cwd=str(self.project_root),
                    env=env,
                    text=True,
                    bufsize=1,  # Line buffered
                )

                # Track process for cancellation
                with self._process_lock:
                    self._processes[job.id] = process

                # Read output in real-time
                def read_stream(stream, stream_type, lines_list):
                    try:
                        for line in iter(stream.readline, ''):
                            if line:
                                lines_list.append(line)
                                # Update live output on the job for polling
                                if stream_type == "stdout":
                                    job.live_stdout += line
                                else:
                                    job.live_stderr += line
                                # Emit output callback
                                if job.status == JobStatus.RUNNING:
                                    asyncio.run_coroutine_threadsafe(
                                        self.callbacks.emit_output(job, stream_type, line),
                                        loop
                                    )
                    except Exception:
                        pass
                    finally:
                        stream.close()

                # Start threads to read stdout and stderr
                stdout_thread = threading.Thread(
                    target=read_stream,
                    args=(process.stdout, "stdout", stdout_lines)
                )
                stderr_thread = threading.Thread(
                    target=read_stream,
                    args=(process.stderr, "stderr", stderr_lines)
                )

                stdout_thread.start()
                stderr_thread.start()

                # Wait for process to complete
                exit_code = process.wait()

                # Wait for output threads to finish
                stdout_thread.join(timeout=5)
                stderr_thread.join(timeout=5)

                return exit_code

            finally:
                # Clean up process tracking
                with self._process_lock:
                    self._processes.pop(job.id, None)

        # Run in thread pool
        exit_code = await loop.run_in_executor(self._thread_pool, run_subprocess)

        # Check if cancelled
        if self._cancel_events.get(job.id) and self._cancel_events[job.id].is_set():
            raise asyncio.CancelledError("Job was cancelled")

        stdout_text = ''.join(stdout_lines)
        stderr_text = ''.join(stderr_lines)

        # For sync command, check stdout for failure indicators even if exit_code is 0
        # This handles the case where sync returns 0 but actually failed
        if exit_code == 0 and job.command == "sync":
            # Look for the summary line printed by sync_main.py
            # It prints: "Overall status: [red]Failed[/red]" or "Overall status: [green]Success[/green]"
            # Check "Failed" only on the "Overall status:" line itself, not anywhere in stdout,
            # since other code (e.g. get_jwt_token.py keyring warnings) may print "Failed" elsewhere.
            for line in stdout_text.splitlines():
                if "Overall status:" in line and "Failed" in line:
                    raise RuntimeError("Sync operation failed (see output for details)")

        if exit_code != 0:
            # Combine stdout and stderr for complete error context
            # Filter out INFO/DEBUG logs to find the actual error message
            all_output = stdout_text + "\n" + stderr_text if stderr_text else stdout_text

            # Try to find actual error lines (not INFO/DEBUG logs)
            error_lines = []
            for line in all_output.split('\n'):
                line_stripped = line.strip()
                if not line_stripped:
                    continue
                # Skip common log prefixes
                if ' - INFO - ' in line or ' - DEBUG - ' in line:
                    continue
                # Skip lines that are just timestamps with INFO
                if line_stripped.startswith('202') and ' INFO ' in line:
                    continue
                error_lines.append(line)

            if error_lines:
                error_msg = '\n'.join(error_lines[-50:])  # Last 50 non-INFO lines
            else:
                # No non-INFO lines found, use all output
                error_msg = all_output or f"Command failed with exit code {exit_code}"

            raise RuntimeError(error_msg)

        return {
            "stdout": stdout_text,
            "stderr": stderr_text,
            "exit_code": exit_code,
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
        """
        Cancel a running job by terminating its subprocess.

        This method:
        1. Sets the cancel event to signal cancellation
        2. Terminates the subprocess (SIGTERM, then SIGKILL if needed)
        3. Cancels the async task

        Returns True if cancellation was initiated, False if job already finished.
        """
        job = self._jobs.get(job_id)
        if not job:
            return False

        if job.status in (JobStatus.COMPLETED, JobStatus.FAILED, JobStatus.CANCELLED):
            return False

        # Set cancel event first
        if job_id in self._cancel_events:
            self._cancel_events[job_id].set()

        # Terminate the subprocess if running
        with self._process_lock:
            process = self._processes.get(job_id)
            if process and process.poll() is None:
                console.print(f"[yellow]Terminating subprocess for job:[/yellow] {job_id}")
                try:
                    # Try graceful termination first
                    process.terminate()

                    # Give it a moment to terminate
                    try:
                        process.wait(timeout=2)
                    except subprocess.TimeoutExpired:
                        # Force kill if it doesn't respond
                        console.print(f"[yellow]Force killing subprocess for job:[/yellow] {job_id}")
                        process.kill()
                        process.wait(timeout=2)
                except Exception as e:
                    console.print(f"[red]Error terminating subprocess: {e}[/red]")

        # Cancel the async task
        if job_id in self._tasks:
            self._tasks[job_id].cancel()

        # Update job status
        job.status = JobStatus.CANCELLED
        job.completed_at = datetime.now(timezone.utc)

        console.print(f"[yellow]Cancellation completed for job:[/yellow] {job_id}")
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