"""
WebSocket Handler Example for PDD Server.

This example demonstrates how to implement WebSocket connections with:
- Connection management (multiple clients)
- Bidirectional messaging (server push, client input)
- Streaming stdout/stderr from subprocess
- JSON message protocol
- Graceful disconnection handling

Documentation references:
- FastAPI WebSockets: https://fastapi.tiangolo.com/advanced/websockets/
- Starlette WebSockets: https://www.starlette.io/websockets/
- WebSocket Protocol: https://developer.mozilla.org/en-US/docs/Web/API/WebSockets_API
- asyncio subprocess: https://docs.python.org/3/library/asyncio-subprocess.html
"""

import asyncio
import json
from dataclasses import dataclass, field
from datetime import datetime
from enum import Enum
from typing import Optional, Set, Dict, Any, Callable, Awaitable
from uuid import uuid4

from fastapi import FastAPI, WebSocket, WebSocketDisconnect
from pydantic import BaseModel


# ============================================================================
# Message Types (Protocol)
# ============================================================================

class MessageType(str, Enum):
    """WebSocket message types for the protocol."""
    # Server -> Client
    STDOUT = "stdout"
    STDERR = "stderr"
    PROGRESS = "progress"
    STATUS = "status"
    COMPLETE = "complete"
    ERROR = "error"
    INPUT_REQUEST = "input_request"
    FILE_CHANGE = "file_change"

    # Client -> Server
    CANCEL = "cancel"
    INPUT = "input"


class WSMessage(BaseModel):
    """Base WebSocket message format."""
    type: str
    timestamp: datetime = None
    data: Optional[Any] = None

    def __init__(self, **kwargs):
        if kwargs.get("timestamp") is None:
            kwargs["timestamp"] = datetime.utcnow()
        super().__init__(**kwargs)


class StdoutMessage(WSMessage):
    """Terminal output message."""
    type: str = MessageType.STDOUT
    data: str
    raw: Optional[str] = None  # With ANSI codes


class ProgressMessage(WSMessage):
    """Progress update message."""
    type: str = MessageType.PROGRESS
    current: int
    total: int
    message: Optional[str] = None


class InputRequestMessage(WSMessage):
    """Request input from client."""
    type: str = MessageType.INPUT_REQUEST
    prompt: str
    password: bool = False


class CompleteMessage(WSMessage):
    """Job completion message."""
    type: str = MessageType.COMPLETE
    success: bool
    result: Optional[Dict[str, Any]] = None
    cost: float = 0.0


# ============================================================================
# Connection Manager
# ============================================================================

@dataclass
class WebSocketConnection:
    """Represents a single WebSocket connection."""
    websocket: WebSocket
    id: str = field(default_factory=lambda: str(uuid4()))
    job_id: Optional[str] = None
    connected_at: datetime = field(default_factory=datetime.utcnow)


class ConnectionManager:
    """
    Manages WebSocket connections and broadcasting.

    Usage:
        manager = ConnectionManager()

        @app.websocket("/ws/jobs/{job_id}")
        async def job_stream(websocket: WebSocket, job_id: str):
            conn = await manager.connect(websocket, job_id)
            try:
                await manager.send_message(conn, StdoutMessage(data="Hello"))
                # ... handle messages
            finally:
                manager.disconnect(conn)
    """

    def __init__(self):
        self._connections: Dict[str, WebSocketConnection] = {}
        self._job_connections: Dict[str, Set[str]] = {}  # job_id -> set of conn_ids

    async def connect(
        self, websocket: WebSocket, job_id: Optional[str] = None
    ) -> WebSocketConnection:
        """Accept a WebSocket connection."""
        await websocket.accept()

        conn = WebSocketConnection(websocket=websocket, job_id=job_id)
        self._connections[conn.id] = conn

        if job_id:
            if job_id not in self._job_connections:
                self._job_connections[job_id] = set()
            self._job_connections[job_id].add(conn.id)

        return conn

    def disconnect(self, conn: WebSocketConnection) -> None:
        """Remove a connection."""
        if conn.id in self._connections:
            del self._connections[conn.id]

        if conn.job_id and conn.job_id in self._job_connections:
            self._job_connections[conn.job_id].discard(conn.id)
            if not self._job_connections[conn.job_id]:
                del self._job_connections[conn.job_id]

    async def send_message(self, conn: WebSocketConnection, message: WSMessage) -> None:
        """Send a message to a specific connection."""
        try:
            await conn.websocket.send_json(message.model_dump(mode="json"))
        except Exception:
            self.disconnect(conn)

    async def broadcast_to_job(self, job_id: str, message: WSMessage) -> None:
        """Broadcast a message to all connections watching a job."""
        conn_ids = self._job_connections.get(job_id, set()).copy()
        for conn_id in conn_ids:
            conn = self._connections.get(conn_id)
            if conn:
                await self.send_message(conn, message)

    async def receive_message(self, conn: WebSocketConnection) -> Optional[Dict]:
        """Receive a message from a connection."""
        try:
            return await conn.websocket.receive_json()
        except WebSocketDisconnect:
            self.disconnect(conn)
            return None


# ============================================================================
# Output Streaming (for subprocess)
# ============================================================================

class OutputStreamer:
    """
    Streams subprocess output to WebSocket connections.

    This adapts the subprocess output capture pattern from pdd/core/cli.py
    for WebSocket streaming.
    """

    def __init__(
        self,
        manager: ConnectionManager,
        job_id: str,
        strip_ansi: bool = True,
    ):
        self.manager = manager
        self.job_id = job_id
        self.strip_ansi = strip_ansi
        self._buffer = ""

    async def write_stdout(self, text: str) -> None:
        """Stream stdout to connected clients."""
        clean_text = self._strip_ansi_codes(text) if self.strip_ansi else text
        message = StdoutMessage(data=clean_text, raw=text)
        await self.manager.broadcast_to_job(self.job_id, message)

    async def write_stderr(self, text: str) -> None:
        """Stream stderr to connected clients."""
        clean_text = self._strip_ansi_codes(text) if self.strip_ansi else text
        message = WSMessage(type=MessageType.STDERR, data=clean_text)
        await self.manager.broadcast_to_job(self.job_id, message)

    async def send_progress(self, current: int, total: int, message: str = None) -> None:
        """Send progress update."""
        msg = ProgressMessage(current=current, total=total, message=message)
        await self.manager.broadcast_to_job(self.job_id, msg)

    async def send_complete(self, success: bool, result: Dict = None, cost: float = 0.0) -> None:
        """Send completion message."""
        msg = CompleteMessage(success=success, result=result, cost=cost)
        await self.manager.broadcast_to_job(self.job_id, msg)

    def _strip_ansi_codes(self, text: str) -> str:
        """Remove ANSI escape codes from text."""
        import re
        ansi_escape = re.compile(r'\x1b\[[0-9;]*m')
        return ansi_escape.sub('', text)


# ============================================================================
# Input Handler (for interactive prompts)
# ============================================================================

class WebSocketInputHandler:
    """
    Handles interactive input requests over WebSocket.

    This adapts the TUIStdinRedirector pattern from pdd/sync_tui.py
    for WebSocket-based input.
    """

    def __init__(
        self,
        manager: ConnectionManager,
        conn: WebSocketConnection,
        timeout: float = 300.0,  # 5 minutes
    ):
        self.manager = manager
        self.conn = conn
        self.timeout = timeout
        self._input_queue: asyncio.Queue = asyncio.Queue()

    async def request_input(self, prompt: str, password: bool = False) -> str:
        """
        Request input from the client.

        Sends an input_request message and waits for the response.
        """
        # Send request
        message = InputRequestMessage(prompt=prompt, password=password)
        await self.manager.send_message(self.conn, message)

        # Wait for response
        try:
            response = await asyncio.wait_for(
                self._input_queue.get(),
                timeout=self.timeout,
            )
            return response
        except asyncio.TimeoutError:
            raise EOFError(f"Input timeout after {self.timeout}s")

    async def handle_message(self, message: Dict) -> bool:
        """
        Handle incoming message from client.

        Returns True if message was handled, False otherwise.
        """
        msg_type = message.get("type")

        if msg_type == MessageType.INPUT:
            await self._input_queue.put(message.get("data", ""))
            return True

        return False


# ============================================================================
# FastAPI WebSocket Routes
# ============================================================================

def create_websocket_routes(app: FastAPI, manager: ConnectionManager):
    """
    Add WebSocket routes to the FastAPI app.

    Args:
        app: FastAPI application
        manager: ConnectionManager instance
    """

    @app.websocket("/api/v1/ws/jobs/{job_id}/stream")
    async def job_stream(websocket: WebSocket, job_id: str):
        """
        Stream job output via WebSocket.

        Protocol:
        - Server sends: stdout, stderr, progress, complete, error, input_request
        - Client sends: cancel, input
        """
        conn = await manager.connect(websocket, job_id)
        input_handler = WebSocketInputHandler(manager, conn)

        try:
            while True:
                message = await manager.receive_message(conn)
                if message is None:
                    break

                # Handle client messages
                msg_type = message.get("type")

                if msg_type == MessageType.CANCEL:
                    # Signal job cancellation
                    await manager.send_message(
                        conn,
                        WSMessage(type=MessageType.STATUS, data="cancelling"),
                    )
                    # In real implementation, cancel the job here
                    break

                elif msg_type == MessageType.INPUT:
                    await input_handler.handle_message(message)

        except WebSocketDisconnect:
            pass
        finally:
            manager.disconnect(conn)

    @app.websocket("/api/v1/ws/watch")
    async def file_watch(websocket: WebSocket):
        """
        Watch for file changes and broadcast updates.

        Client sends: {"paths": ["path1", "path2"]} to subscribe
        Server sends: {"type": "file_change", "path": "...", "event": "modified"}
        """
        conn = await manager.connect(websocket)

        try:
            # Receive subscription request
            subscription = await manager.receive_message(conn)
            if subscription is None:
                return

            paths = subscription.get("paths", [])

            # In real implementation, set up file watchers here
            # For now, just keep connection alive
            while True:
                message = await manager.receive_message(conn)
                if message is None:
                    break

        except WebSocketDisconnect:
            pass
        finally:
            manager.disconnect(conn)


# ============================================================================
# Example Usage
# ============================================================================

def main():
    """
    Example demonstrating WebSocket streaming.

    This creates a simple FastAPI app with WebSocket support
    and simulates streaming output from a job.
    """
    import uvicorn

    app = FastAPI(title="WebSocket Example")
    manager = ConnectionManager()
    create_websocket_routes(app, manager)

    # Add a test endpoint that simulates a job
    @app.post("/api/v1/test/simulate-job/{job_id}")
    async def simulate_job(job_id: str):
        """Simulate a job that streams output."""
        streamer = OutputStreamer(manager, job_id)

        # Simulate some output
        await streamer.write_stdout("Starting job...\n")
        await asyncio.sleep(0.5)

        for i in range(5):
            await streamer.send_progress(i + 1, 5, f"Step {i + 1}")
            await streamer.write_stdout(f"Processing step {i + 1}...\n")
            await asyncio.sleep(0.3)

        await streamer.write_stdout("Job complete!\n")
        await streamer.send_complete(success=True, result={"message": "Done"})

        return {"status": "completed"}

    print("Starting WebSocket example server...")
    print("Test with: wscat -c ws://127.0.0.1:9876/api/v1/ws/jobs/test-job/stream")
    print("Then POST to: http://127.0.0.1:9876/api/v1/test/simulate-job/test-job")

    uvicorn.run(app, host="127.0.0.1", port=9876)


if __name__ == "__main__":
    main()
