"""
Remote Session Management for PDD Connect.

This module handles remote session management for PDD Connect. It enables users to run
`pdd connect` on any machine and access it remotely via PDD Cloud. The cloud acts as a
message bus - it relays commands from the browser to the CLI via Firestore.
No external tunnel (ngrok) is required - the cloud hosts everything.
"""

from __future__ import annotations

import asyncio
import datetime
import platform
import socket
import sys
from dataclasses import dataclass
from pathlib import Path
from typing import Any, Callable, Dict, List, Optional

import httpx
from rich.console import Console

from .core.cloud import CloudConfig

console = Console()

# Global state for the active session manager
_active_session_manager: Optional[RemoteSessionManager] = None


def get_active_session_manager() -> Optional[RemoteSessionManager]:
    """Get the currently active remote session manager."""
    return _active_session_manager


def set_active_session_manager(manager: Optional[RemoteSessionManager]) -> None:
    """Set the currently active remote session manager."""
    global _active_session_manager
    _active_session_manager = manager


class RemoteSessionError(Exception):
    """Custom exception for remote session operations."""

    def __init__(self, message: str, status_code: Optional[int] = None):
        self.message = message
        self.status_code = status_code
        super().__init__(f"{message} (Status: {status_code})" if status_code else message)


@dataclass
class SessionInfo:
    """
    Represents a remote PDD session discovered from the cloud.

    The cloud_url is the URL users can access in their browser to interact
    with this session (e.g., https://pdd.dev/connect/{session_id}).
    """
    session_id: str
    cloud_url: str
    project_name: str
    project_path: str
    created_at: datetime.datetime
    last_heartbeat: datetime.datetime
    status: str
    metadata: Dict[str, Any]

    @classmethod
    def from_dict(cls, data: Dict[str, Any]) -> SessionInfo:
        """Factory method to create SessionInfo from cloud API response."""
        def parse_dt(dt_str: Optional[str]) -> datetime.datetime:
            if not dt_str:
                return datetime.datetime.now(datetime.timezone.utc)
            # Handle 'Z' for UTC which fromisoformat didn't handle before 3.11
            if dt_str.endswith('Z'):
                dt_str = dt_str[:-1] + '+00:00'
            return datetime.datetime.fromisoformat(dt_str)

        return cls(
            session_id=data.get("sessionId", ""),
            cloud_url=data.get("cloudUrl", ""),
            project_name=data.get("projectName", "Unknown Project"),
            project_path=data.get("projectPath", ""),
            created_at=parse_dt(data.get("createdAt")),
            last_heartbeat=parse_dt(data.get("lastHeartbeat")),
            status=data.get("status", "unknown"),
            metadata=data.get("metadata", {})
        )


@dataclass
class CommandInfo:
    """
    Represents a command from the Firestore message bus.

    Commands are created by the browser and picked up by the CLI for execution.
    """
    command_id: str
    type: str  # "generate" | "fix" | "sync" | "custom"
    payload: Dict[str, Any]
    status: str  # "pending" | "processing" | "completed" | "failed"
    created_at: datetime.datetime
    response: Optional[Dict[str, Any]] = None

    @classmethod
    def from_dict(cls, data: Dict[str, Any]) -> CommandInfo:
        """Factory method to create CommandInfo from cloud API response."""
        def parse_dt(dt_str: Optional[str]) -> datetime.datetime:
            if not dt_str:
                return datetime.datetime.now(datetime.timezone.utc)
            if dt_str.endswith('Z'):
                dt_str = dt_str[:-1] + '+00:00'
            return datetime.datetime.fromisoformat(dt_str)

        return cls(
            command_id=data.get("commandId", ""),
            type=data.get("type", "custom"),
            payload=data.get("payload", {}),
            status=data.get("status", "pending"),
            created_at=parse_dt(data.get("createdAt")),
            response=data.get("response"),
        )


class RemoteSessionManager:
    """
    Manages the lifecycle of a remote session: registration, heartbeats, and deregistration.

    The cloud acts as a message bus - commands from the browser are relayed via Firestore.
    No external tunnel is required; the cloud generates the access URL.
    """

    def __init__(self, jwt_token: str, project_path: Path):
        self.jwt_token = jwt_token
        self.project_path = project_path
        self.session_id: Optional[str] = None
        self.cloud_url: Optional[str] = None
        self._heartbeat_task: Optional[asyncio.Task] = None
        self._command_polling_task: Optional[asyncio.Task] = None
        self._stop_event: Optional[asyncio.Event] = None
        self._client_timeout = 30.0

    def _get_headers(self) -> Dict[str, str]:
        return {
            "Authorization": f"Bearer {self.jwt_token}",
            "Content-Type": "application/json",
        }

    def _get_metadata(self) -> Dict[str, Any]:
        return {
            "hostname": socket.gethostname(),
            "platform": platform.system(),
            "platformRelease": platform.release(),
            "pythonVersion": sys.version.split()[0],
        }

    async def register(self, session_name: Optional[str] = None) -> str:
        """
        Register the session with the cloud.

        No public URL is required - the cloud generates the access URL.

        Args:
            session_name: Optional custom name for the session.

        Returns:
            str: The cloud access URL (e.g., https://pdd.dev/connect/{session_id}).

        Raises:
            RemoteSessionError: If registration fails.
        """
        endpoint = CloudConfig.get_endpoint_url("registerSession")

        payload = {
            "projectPath": str(self.project_path),
            "metadata": self._get_metadata()
        }
        if session_name:
            payload["sessionName"] = session_name

        async with httpx.AsyncClient(timeout=self._client_timeout) as client:
            try:
                response = await client.post(
                    endpoint,
                    json=payload,
                    headers=self._get_headers()
                )

                if response.status_code >= 400:
                    raise RemoteSessionError(
                        f"Failed to register session: {response.text}",
                        status_code=response.status_code
                    )

                data = response.json()
                self.session_id = data.get("sessionId")
                self.cloud_url = data.get("cloudUrl")

                if not self.session_id:
                    raise RemoteSessionError("Cloud response missing sessionId")
                if not self.cloud_url:
                    raise RemoteSessionError("Cloud response missing cloudUrl")

                return self.cloud_url

            except httpx.RequestError as e:
                raise RemoteSessionError(f"Network error during registration: {str(e)}")

    async def _heartbeat_loop(self) -> None:
        """Internal loop to send heartbeats every 60 seconds."""
        endpoint = CloudConfig.get_endpoint_url("heartbeatSession")

        # Ensure stop event is initialized
        if self._stop_event is None:
            self._stop_event = asyncio.Event()

        while not self._stop_event.is_set():
            try:
                # Wait for 60 seconds or until stop event is set
                try:
                    await asyncio.wait_for(self._stop_event.wait(), timeout=60.0)
                    break  # Stop event was set
                except asyncio.TimeoutError:
                    pass  # Timeout reached, send heartbeat

                if not self.session_id:
                    continue

                async with httpx.AsyncClient(timeout=10.0) as client:
                    response = await client.post(
                        endpoint,
                        json={"sessionId": self.session_id},
                        headers=self._get_headers()
                    )
                    
                    if response.status_code >= 400:
                        console.print(f"[yellow]Warning: Heartbeat failed (Status: {response.status_code})[/yellow]")

            except Exception as e:
                # We don't want to crash the server loop due to a heartbeat failure
                console.print(f"[yellow]Warning: Heartbeat error: {str(e)}[/yellow]")

    def start_heartbeat(self) -> None:
        """Start the background heartbeat task."""
        if self._heartbeat_task is not None:
            return

        # Initialize stop event if needed (must have event loop running)
        if self._stop_event is None:
            self._stop_event = asyncio.Event()
        else:
            self._stop_event.clear()

        self._heartbeat_task = asyncio.create_task(self._heartbeat_loop())

    async def stop_heartbeat(self) -> None:
        """Stop the heartbeat task gracefully."""
        if self._heartbeat_task:
            if self._stop_event:
                self._stop_event.set()
            try:
                await self._heartbeat_task
            except asyncio.CancelledError:
                pass
            self._heartbeat_task = None

    async def deregister(self) -> None:
        """
        Deregister the session from the cloud.
        Should be called on application shutdown.
        """
        if not self.session_id:
            return

        endpoint = CloudConfig.get_endpoint_url("deregisterSession")

        # Stop heartbeat and command polling first to prevent race conditions
        await self.stop_heartbeat()
        await self.stop_command_polling()

        async with httpx.AsyncClient(timeout=5.0) as client:
            try:
                # Server expects POST method for deregisterSession
                response = await client.post(
                    endpoint,
                    json={"sessionId": self.session_id},
                    headers=self._get_headers()
                )
                
                if response.status_code < 400:
                    console.print("[dim]Session deregistered from cloud.[/dim]")
                else:
                    console.print(f"[yellow]Warning: Failed to deregister session (Status: {response.status_code})[/yellow]")
            
            except Exception as e:
                # Idempotent: don't raise on failure during shutdown
                console.print(f"[yellow]Warning: Error deregistering session: {str(e)}[/yellow]")
            finally:
                self.session_id = None

    async def get_pending_commands(self) -> List[CommandInfo]:
        """
        Retrieve pending commands from the cloud for this session.

        Returns:
            List[CommandInfo]: List of pending commands to execute.

        Raises:
            RemoteSessionError: If fetching commands fails.
        """
        if not self.session_id:
            return []

        endpoint = CloudConfig.get_endpoint_url("getCommands")

        async with httpx.AsyncClient(timeout=10.0) as client:
            try:
                response = await client.get(
                    endpoint,
                    params={"sessionId": self.session_id},
                    headers=self._get_headers()
                )

                if response.status_code >= 400:
                    console.print(f"[yellow]Warning: Failed to get commands (Status: {response.status_code})[/yellow]")
                    return []

                data = response.json()
                commands_data = data.get("commands", [])

                return [CommandInfo.from_dict(c) for c in commands_data]

            except httpx.RequestError as e:
                console.print(f"[yellow]Warning: Network error getting commands: {str(e)}[/yellow]")
                return []
            except Exception as e:
                console.print(f"[yellow]Warning: Error parsing commands: {str(e)}[/yellow]")
                return []

    async def update_command(
        self,
        command_id: str,
        status: str,
        response: Optional[Dict[str, Any]] = None
    ) -> None:
        """
        Update the status of a command in the cloud.

        Args:
            command_id: The command ID to update.
            status: New status ("processing", "completed", "failed").
            response: Optional response data (for completed/failed status).

        Raises:
            RemoteSessionError: If update fails.
        """
        if not self.session_id:
            return

        endpoint = CloudConfig.get_endpoint_url("updateCommand")

        payload = {
            "sessionId": self.session_id,
            "commandId": command_id,
            "status": status
        }
        if response is not None:
            payload["response"] = response

        async with httpx.AsyncClient(timeout=10.0) as client:
            try:
                result = await client.post(
                    endpoint,
                    json=payload,
                    headers=self._get_headers()
                )

                if result.status_code >= 400:
                    console.print(f"[yellow]Warning: Failed to update command status (Status: {result.status_code})[/yellow]")

            except Exception as e:
                console.print(f"[yellow]Warning: Error updating command: {str(e)}[/yellow]")

    async def _execute_command(self, cmd: CommandInfo) -> None:
        """
        Execute a command locally and report results back to the cloud.

        Args:
            cmd: The command to execute.
        """
        try:
            # 1. Update status to "processing"
            await self.update_command(cmd.command_id, status="processing")
            console.print(f"[cyan]Executing remote command: {cmd.type}[/cyan]")

            # 2. Execute via local FastAPI endpoint
            # The local server is running on 127.0.0.1:9876 by default
            local_url = "http://127.0.0.1:9876"

            # Map command type to local API endpoint
            endpoint_map = {
                "generate": "/api/v1/commands/generate",
                "fix": "/api/v1/commands/fix",
                "test": "/api/v1/commands/test",
                "crash": "/api/v1/commands/crash",
            }

            endpoint = endpoint_map.get(cmd.type)
            if not endpoint:
                raise ValueError(f"Unknown command type: {cmd.type}")

            async with httpx.AsyncClient(timeout=300.0) as client:
                result = await client.post(
                    f"{local_url}{endpoint}",
                    json=cmd.payload
                )

                if result.status_code >= 400:
                    # Command failed
                    await self.update_command(
                        cmd.command_id,
                        status="failed",
                        response={"error": result.text}
                    )
                    console.print(f"[red]Command failed: {result.text}[/red]")
                else:
                    # Command succeeded
                    response_data = result.json()
                    await self.update_command(
                        cmd.command_id,
                        status="completed",
                        response=response_data
                    )
                    console.print(f"[green]Command completed successfully[/green]")

        except Exception as e:
            # Execution error
            console.print(f"[red]Error executing command: {str(e)}[/red]")
            await self.update_command(
                cmd.command_id,
                status="failed",
                response={"error": str(e)}
            )

    async def _command_polling_loop(self) -> None:
        """
        Background task that polls for pending commands and executes them.
        Runs every 5 seconds until stopped.
        """
        if self._stop_event is None:
            self._stop_event = asyncio.Event()

        console.print("[dim]Command polling started[/dim]")

        while not self._stop_event.is_set():
            try:
                # Wait for 5 seconds or until stop event is set
                try:
                    await asyncio.wait_for(self._stop_event.wait(), timeout=5.0)
                    break  # Stop event was set
                except asyncio.TimeoutError:
                    pass  # Timeout reached, poll for commands

                # Get pending commands
                commands = await self.get_pending_commands()

                # Execute each command sequentially
                for cmd in commands:
                    if self._stop_event.is_set():
                        break
                    await self._execute_command(cmd)

            except Exception as e:
                console.print(f"[yellow]Warning: Command polling error: {str(e)}[/yellow]")

        console.print("[dim]Command polling stopped[/dim]")

    def start_command_polling(self) -> None:
        """Start the background command polling task."""
        if self._command_polling_task is not None:
            return

        # Initialize stop event if needed
        if self._stop_event is None:
            self._stop_event = asyncio.Event()
        else:
            self._stop_event.clear()

        self._command_polling_task = asyncio.create_task(self._command_polling_loop())

    async def stop_command_polling(self) -> None:
        """Stop the command polling task gracefully."""
        if self._command_polling_task:
            if self._stop_event:
                self._stop_event.set()
            try:
                await self._command_polling_task
            except asyncio.CancelledError:
                pass
            self._command_polling_task = None

    @staticmethod
    async def list_sessions(jwt_token: str) -> List[SessionInfo]:
        """
        List all active sessions available to the user.

        Args:
            jwt_token: The user's JWT authentication token.

        Returns:
            List[SessionInfo]: A list of active sessions.

        Raises:
            RemoteSessionError: If the listing fails.
        """
        endpoint = CloudConfig.get_endpoint_url("listSessions")
        headers = {
            "Authorization": f"Bearer {jwt_token}",
            "Content-Type": "application/json",
        }

        async with httpx.AsyncClient(timeout=30.0) as client:
            try:
                response = await client.get(endpoint, headers=headers)

                if response.status_code >= 400:
                    raise RemoteSessionError(
                        f"Failed to list sessions: {response.text}",
                        status_code=response.status_code
                    )

                data = response.json()
                sessions_data = data.get("sessions", [])

                return [SessionInfo.from_dict(s) for s in sessions_data]

            except httpx.RequestError as e:
                raise RemoteSessionError(f"Network error listing sessions: {str(e)}")
            except ValueError as e:
                raise RemoteSessionError(f"Invalid response format: {str(e)}")