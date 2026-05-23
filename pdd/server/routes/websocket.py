from __future__ import annotations

import asyncio
import json
import re
import time
from datetime import datetime, timezone
from pathlib import Path
from typing import Dict, List, Optional, Set, Any, Union

from fastapi import APIRouter, WebSocket, WebSocketDisconnect, Depends, status
from rich.console import Console
from watchdog.observers import Observer
from watchdog.events import FileSystemEventHandler, FileSystemEvent

# Relative imports
from ..models import (
    WSMessage,
    StdoutMessage,
    StderrMessage,
    ProgressMessage,
    JobStatus,
    BudgetExceededMessage,
)
from ..jobs import JobManager, Job, JobStatus as JobStatusEnum

# Initialize console for logging
console = Console()

# Regex for stripping ANSI codes (CSI sequences)
ANSI_ESCAPE = re.compile(r'\x1b\[[0-9;]*m')

# Global constants
DEBOUNCE_SECONDS = 0.1

router = APIRouter(tags=["websocket"])


# ============================================================================
# Utilities
# ============================================================================

def clean_ansi(text: str) -> str:
    """Remove ANSI escape sequences from text."""
    return ANSI_ESCAPE.sub('', text)


class ConnectionManager:
    """
    Manages WebSocket connections for job streaming and file watching.
    """

    def __init__(self):
        # All active connections
        self.active_connections: List[WebSocket] = []
        # Map job_id -> list of WebSockets watching that job
        self.job_subscriptions: Dict[str, List[WebSocket]] = {}
        # List of WebSockets watching file changes
        self.watch_subscriptions: List[WebSocket] = []

    async def connect(self, websocket: WebSocket):
        """Accept a new connection."""
        await websocket.accept()
        self.active_connections.append(websocket)

    def disconnect(self, websocket: WebSocket, job_id: Optional[str] = None):
        """Remove a connection."""
        if websocket in self.active_connections:
            self.active_connections.remove(websocket)
        
        if job_id and job_id in self.job_subscriptions:
            if websocket in self.job_subscriptions[job_id]:
                self.job_subscriptions[job_id].remove(websocket)
            if not self.job_subscriptions[job_id]:
                del self.job_subscriptions[job_id]

        if websocket in self.watch_subscriptions:
            self.watch_subscriptions.remove(websocket)

    async def subscribe_to_job(self, websocket: WebSocket, job_id: str):
        """Subscribe a websocket to a specific job's events."""
        if job_id not in self.job_subscriptions:
            self.job_subscriptions[job_id] = []
        self.job_subscriptions[job_id].append(websocket)

    async def subscribe_to_watch(self, websocket: WebSocket):
        """Subscribe a websocket to file watcher events."""
        if websocket not in self.watch_subscriptions:
            self.watch_subscriptions.append(websocket)

    async def broadcast_job_message(self, job_id: str, message: WSMessage):
        """Send a message to all clients watching a specific job."""
        if job_id not in self.job_subscriptions:
            return

        # Serialize once
        data = message.model_dump_json()
        
        # Broadcast
        to_remove = []
        for connection in self.job_subscriptions[job_id]:
            try:
                await connection.send_text(data)
            except Exception:
                to_remove.append(connection)
        
        # Cleanup dead connections
        for connection in to_remove:
            self.disconnect(connection, job_id)

    async def broadcast_file_change(self, message: WSMessage):
        """Send a file change event to all watchers."""
        data = message.model_dump_json()
        to_remove = []
        for connection in self.watch_subscriptions:
            try:
                await connection.send_text(data)
            except Exception:
                to_remove.append(connection)

        for connection in to_remove:
            self.disconnect(connection)

    async def broadcast_to_all(self, message: WSMessage):
        """Send a message to ALL connected clients."""
        data = message.model_dump_json()
        to_remove = []
        for connection in self.active_connections:
            try:
                await connection.send_text(data)
            except Exception:
                to_remove.append(connection)

        for connection in to_remove:
            self.disconnect(connection)


# Global manager instance
manager = ConnectionManager()


# ============================================================================
# File Watcher Logic
# ============================================================================

class AsyncFileEventHandler(FileSystemEventHandler):
    """
    Watchdog handler that bridges file system events to an asyncio queue.
    """

    def __init__(self, loop: asyncio.AbstractEventLoop, queue: asyncio.Queue):
        self.loop = loop
        self.queue = queue
        self.last_events: Dict[str, float] = {}

    def _process_event(self, event: FileSystemEvent, event_type: str):
        if event.is_directory:
            return

        # Debounce
        now = time.time()
        path = str(event.src_path)
        last_time = self.last_events.get(path, 0)
        
        if now - last_time < DEBOUNCE_SECONDS:
            return
        
        self.last_events[path] = now

        # Create message
        msg = WSMessage(
            type="file_change",
            data={
                "path": path,
                "event": event_type,
                "timestamp": datetime.now(timezone.utc).isoformat()
            }
        )

        # Schedule putting into queue on the main loop
        self.loop.call_soon_threadsafe(self.queue.put_nowait, msg)

    def on_modified(self, event: FileSystemEvent):
        self._process_event(event, "modified")

    def on_created(self, event: FileSystemEvent):
        self._process_event(event, "created")

    def on_deleted(self, event: FileSystemEvent):
        self._process_event(event, "deleted")


# ============================================================================
# Dependencies
# ============================================================================

# Placeholder for dependency injection. 
# In a real app, this would be imported from ..dependencies or ..main
async def get_job_manager():
    """
    Dependency to retrieve the JobManager instance.
    This should be overridden by the app's dependency_overrides.
    """
    raise NotImplementedError("JobManager dependency not configured")


async def get_project_root():
    """
    Dependency to retrieve the project root path.
    """
    raise NotImplementedError("Project root dependency not configured")


# ============================================================================
# Endpoints
# ============================================================================

@router.websocket("/ws/jobs/{job_id}/stream")
async def websocket_job_stream(
    websocket: WebSocket,
    job_id: str,
    job_manager: JobManager = Depends(get_job_manager)
):
    """
    WebSocket endpoint for streaming job output and interaction.
    """
    await manager.connect(websocket)
    
    try:
        job = job_manager.get_job(job_id)
        if not job:
            await websocket.close(code=status.WS_1008_POLICY_VIOLATION, reason="Job not found")
            return

        await manager.subscribe_to_job(websocket, job_id)
        console.print(f"[cyan]WS:[/cyan] Client connected to stream for job {job_id}")

        # If job is already in a terminal state, send the result immediately.
        # BUDGET_EXCEEDED is terminal too — without it here a client
        # reconnecting after the watcher tripped the cap would hang
        # waiting for input, since the input loop below does not
        # treat the job as finished.
        if job.status in [
            JobStatus.COMPLETED,
            JobStatus.FAILED,
            JobStatus.CANCELLED,
            JobStatus.BUDGET_EXCEEDED,
        ]:
            # For BUDGET_EXCEEDED, send the typed budget_exceeded
            # message FIRST so a reconnecting client can render the
            # cap-trip UI without an extra REST round-trip. Then
            # send the standard `complete` summary and close.
            if job.status == JobStatus.BUDGET_EXCEEDED:
                try:
                    # Recompute the real effective cap from the job's
                    # budget fields. The earlier version used
                    # `job.cost` as `effective_cap`, which produced
                    # spent==effective_cap on the reconnect payload
                    # (e.g. cap $400 with spend $401.23 was reported
                    # as effective_cap=$401.23) — clients then had no
                    # way to know what the active cap was at the
                    # moment of crossing. Falling back to job.cost is
                    # only used if the budget_settings module is
                    # unavailable.
                    cap_value: float = float(job.cost or 0.0)
                    try:
                        from pdd.server.budget_settings import (
                            effective_cap as _effective_cap_fn,
                        )
                        real_cap = _effective_cap_fn(
                            job.command,
                            budget_cap=job.budget_cap,
                            node_budget=job.node_budget,
                            max_total_cap=job.max_total_cap,
                            node_count=job.node_count,
                        )
                        if real_cap is not None:
                            cap_value = float(real_cap)
                    except Exception:  # noqa: BLE001
                        pass
                    budget_msg = BudgetExceededMessage(
                        job_id=job.id,
                        command=job.command,
                        spent=float(job.cost or 0.0),
                        effective_cap=cap_value,
                        node_budget=job.node_budget,
                        max_total_cap=job.max_total_cap,
                        node_count=job.node_count,
                    )
                    await websocket.send_text(budget_msg.model_dump_json())
                except Exception:  # noqa: BLE001
                    pass
            result_msg = WSMessage(
                type="complete",
                data={
                    "success": job.status == JobStatus.COMPLETED,
                    "result": job.result,
                    "cost": job.cost,
                    "status": job.status.value
                }
            )
            await websocket.send_text(result_msg.model_dump_json())
            await websocket.close()
            return

        # Listen for client messages (input/cancel). The loop races
        # `receive_text()` against a poll of `job.status` so the
        # WebSocket closes when the job reaches a terminal state —
        # otherwise a live stream would keep waiting on client input
        # indefinitely after the job completed.
        _terminal_statuses = {
            JobStatus.COMPLETED,
            JobStatus.FAILED,
            JobStatus.CANCELLED,
            JobStatus.BUDGET_EXCEEDED,
        }

        async def _watch_for_terminal():
            while True:
                current = job_manager.get_job(job_id)
                if current is None or current.status in _terminal_statuses:
                    return current
                await asyncio.sleep(0.25)

        while True:
            receive_task = asyncio.create_task(websocket.receive_text())
            done_task = asyncio.create_task(_watch_for_terminal())
            done, pending = await asyncio.wait(
                [receive_task, done_task],
                return_when=asyncio.FIRST_COMPLETED,
            )
            for t in pending:
                t.cancel()
                try:
                    await t
                except (asyncio.CancelledError, Exception):
                    pass

            if done_task in done:
                try:
                    await websocket.close()
                except Exception:  # noqa: BLE001
                    pass
                return

            try:
                data = receive_task.result()
            except Exception:  # noqa: BLE001
                return
            try:
                message = json.loads(data)
                msg_type = message.get("type")

                if msg_type == "cancel":
                    console.print(f"[cyan]WS:[/cyan] Cancel request for job {job_id}")
                    await job_manager.cancel(job_id)

                elif msg_type == "input":
                    # In a real implementation, this would pipe data to the job's stdin
                    user_input = message.get("data", "")
                    console.print(f"[cyan]WS:[/cyan] Input received for job {job_id}: {len(user_input)} chars")
                    # TODO: Implement stdin piping in JobManager

            except json.JSONDecodeError:
                error_msg = WSMessage(
                    type="error",
                    data={"message": "Invalid JSON format"}
                )
                await websocket.send_text(error_msg.model_dump_json())

    except WebSocketDisconnect:
        console.print(f"[cyan]WS:[/cyan] Client disconnected from job {job_id}")
    except Exception as e:
        console.print(f"[bold red]WS Error:[/bold red] {e}")
    finally:
        manager.disconnect(websocket, job_id)


@router.websocket("/ws/watch")
async def websocket_watch(
    websocket: WebSocket,
    project_root: Path = Depends(get_project_root)
):
    """
    WebSocket endpoint for watching file system changes.
    """
    await manager.connect(websocket)
    
    observer = Observer()
    queue: asyncio.Queue = asyncio.Queue()
    loop = asyncio.get_running_loop()
    
    try:
        # 1. Wait for subscription message
        # Client must send: {"paths": ["src", "public"]}
        data = await websocket.receive_text()
        subscription = json.loads(data)
        paths_to_watch = subscription.get("paths", [])
        
        if not paths_to_watch:
            # Default to watching root if nothing specified
            paths_to_watch = ["."]

        # 2. Setup Watchdog
        handler = AsyncFileEventHandler(loop, queue)
        
        for path_str in paths_to_watch:
            watch_path = (project_root / path_str).resolve()
            if watch_path.exists() and watch_path.is_dir():
                observer.schedule(handler, str(watch_path), recursive=True)
                console.print(f"[cyan]WS:[/cyan] Watching path: {watch_path}")
            else:
                console.print(f"[yellow]WS Warning:[/yellow] Path not found or not a directory: {watch_path}")

        observer.start()
        await manager.subscribe_to_watch(websocket)

        # 3. Event Loop
        # We need to handle both incoming messages (ping/close) and outgoing events
        while True:
            # Create tasks for receiving from WS and reading from Queue
            receive_task = asyncio.create_task(websocket.receive_text())
            queue_task = asyncio.create_task(queue.get())

            done, pending = await asyncio.wait(
                [receive_task, queue_task],
                return_when=asyncio.FIRST_COMPLETED
            )

            # Handle File Events
            if queue_task in done:
                msg = queue_task.result()
                await websocket.send_text(msg.model_dump_json())
                # Cancel receive task to restart loop cleanly
                receive_task.cancel()
            else:
                queue_task.cancel()

            # Handle Client Disconnect/Messages
            if receive_task in done:
                try:
                    _ = receive_task.result()
                    # We ignore client messages after subscription, but keep connection alive
                except WebSocketDisconnect:
                    raise
                except Exception:
                    # If receive failed, connection is likely dead
                    raise WebSocketDisconnect()

    except WebSocketDisconnect:
        console.print("[cyan]WS:[/cyan] Watcher disconnected")
    except Exception as e:
        console.print(f"[bold red]WS Watch Error:[/bold red] {e}")
    finally:
        if observer.is_alive():
            observer.stop()
            observer.join()
        manager.disconnect(websocket)


# ============================================================================
# Job Event Integration
# ============================================================================

async def emit_job_output(job_id: str, stream: str, text: str):
    """
    Helper to emit stdout/stderr messages to subscribers.
    To be called by the Job Executor.
    """
    msg_type = "stdout" if stream == "stdout" else "stderr"
    
    # Create specific message model
    if stream == "stdout":
        msg = StdoutMessage(
            data=clean_ansi(text),
            raw=text,
            timestamp=datetime.now(timezone.utc)
        )
    else:
        msg = StderrMessage(
            data=clean_ansi(text),
            raw=text,
            timestamp=datetime.now(timezone.utc)
        )
        
    await manager.broadcast_job_message(job_id, msg)


async def emit_job_progress(job_id: str, current: int, total: int, message: str):
    """
    Helper to emit progress messages.
    """
    msg = ProgressMessage(
        current=current,
        total=total,
        message=message,
        timestamp=datetime.now(timezone.utc)
    )
    await manager.broadcast_job_message(job_id, msg)


async def emit_job_complete(job_id: str, result: Any, success: bool, cost: float = 0.0):
    """
    Helper to emit completion messages.
    """
    msg = WSMessage(
        type="complete",
        data={
            "success": success,
            "result": result,
            "cost": cost,
            "timestamp": datetime.now(timezone.utc).isoformat()
        }
    )
    await manager.broadcast_job_message(job_id, msg)


async def emit_job_budget_exceeded(job: Job, spent: float, effective_cap: float):
    """Broadcast a typed ``BudgetExceededMessage`` to the job's subscribers.

    Fires exactly once when the watcher trips the active cap; the message
    carries enough context (job_id, command, spent, effective_cap, plus
    pdd-issue specifics) for clients to render the budget-exceeded UI
    without an extra REST round-trip.
    """
    msg = BudgetExceededMessage(
        job_id=job.id,
        command=job.command,
        spent=float(spent),
        effective_cap=float(effective_cap),
        node_budget=job.node_budget,
        max_total_cap=job.max_total_cap,
        node_count=job.node_count,
    )
    await manager.broadcast_job_message(job.id, msg)


async def emit_spawned_job_complete(job_id: str, command: str, success: bool, exit_code: int):
    """
    Helper to emit spawned job completion to ALL connected clients.

    Spawned terminal jobs don't have WebSocket subscriptions, so we broadcast
    to all connected clients. The frontend dashboard can filter by job_id.
    """
    msg = WSMessage(
        type="spawned_job_complete",
        data={
            "job_id": job_id,
            "command": command,
            "success": success,
            "exit_code": exit_code,
            "status": "completed" if success else "failed",
            "timestamp": datetime.now(timezone.utc).isoformat()
        }
    )
    await manager.broadcast_to_all(msg)


# ============================================================================
# App Integration
# ============================================================================

def create_websocket_routes(app, connection_manager: ConnectionManager, job_manager: JobManager = None):
    """
    Register WebSocket routes with the FastAPI application.

    Args:
        app: FastAPI application instance.
        connection_manager: ConnectionManager instance for handling WebSocket connections.
        job_manager: JobManager instance for registering output callbacks.
    """
    global manager
    manager = connection_manager
    app.include_router(router)

    # Register callbacks to stream job output to WebSocket clients
    if job_manager:
        async def on_job_output(job: Job, stream_type: str, text: str):
            """Callback to broadcast job output to WebSocket subscribers."""
            await emit_job_output(job.id, stream_type, text)

        async def on_job_complete(job: Job):
            """Callback to broadcast job completion to WebSocket subscribers."""
            success = job.status == JobStatusEnum.COMPLETED
            await emit_job_complete(job.id, job.result, success, job.cost)

        async def on_job_budget_exceeded(job_id: str, spent: float, cap: float):
            """Broadcast the typed ``BudgetExceededMessage`` once the watcher
            trips. Without this registration the JobManager emits the event
            internally but no client ever sees it, so a UI watching a
            capped run would only learn about the cap crossing from the
            subsequent ``complete`` message — and would have no way to
            distinguish a successful completion from a budget abort.
            """
            job = job_manager.get_job(job_id)
            if job is None:
                return
            await emit_job_budget_exceeded(job, spent, cap)

        job_manager.callbacks.on_output(on_job_output)
        job_manager.callbacks.on_complete(on_job_complete)
        job_manager.callbacks.on_budget_exceeded(on_job_budget_exceeded)
