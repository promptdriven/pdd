"""
Remote Session Management for PDD Connect.

This module handles remote session management for PDD Connect. It enables users to run
`pdd connect` on any machine and access it remotely via PDD Cloud. The cloud acts as a
message bus - it relays commands from the browser to the CLI via Firestore.
No external tunnel (ngrok) is required - the cloud hosts everything.

Key features for session reliability:
- Immediate first heartbeat on startup (prevents early session timeout)
- 30-second heartbeat interval with 3 retries and exponential backoff
- Automatic JWT token refresh on 401 errors (handles token expiration)
- Graceful handling of network errors during long-running operations
"""

from __future__ import annotations

import ast
import asyncio
import datetime
import platform
import socket
import sys
from dataclasses import dataclass
from pathlib import Path
from typing import Any, Callable, Dict, List, Optional, Tuple

import httpx
from rich.console import Console

from .core.cloud import CloudConfig
from .get_jwt_token import _get_cached_jwt, FirebaseAuthenticator, KEYRING_AVAILABLE

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

    Session reliability features:
    - Heartbeats are sent immediately on startup, then every 30 seconds
    - Heartbeat failures trigger 3 retries with exponential backoff (1s, 2s, 4s)
    - 401 errors (token expiration) trigger automatic JWT token refresh
    - Command polling also handles 401 errors with automatic token refresh
    """

    def __init__(self, jwt_token: str, project_path: Path, server_port: int = 9876):
        self.jwt_token = jwt_token
        self.project_path = project_path
        self.server_port = server_port
        self.session_id: Optional[str] = None
        self.cloud_url: Optional[str] = None
        self._heartbeat_task: Optional[asyncio.Task] = None
        self._command_polling_task: Optional[asyncio.Task] = None
        self._stop_event: Optional[asyncio.Event] = None
        self._client_timeout = 30.0
        self._token_refresh_lock = asyncio.Lock()

    def _get_headers(self) -> Dict[str, str]:
        return {
            "Authorization": f"Bearer {self.jwt_token}",
            "Content-Type": "application/json",
        }

    async def _refresh_token(self) -> bool:
        """
        Attempt to refresh the JWT token using the stored refresh token.

        Returns:
            bool: True if token was successfully refreshed, False otherwise.
        """
        import os
        from .get_jwt_token import _cache_jwt

        async with self._token_refresh_lock:
            # First check if another coroutine already refreshed the token
            cached_jwt = _get_cached_jwt()
            if cached_jwt and cached_jwt != self.jwt_token:
                self.jwt_token = cached_jwt
                console.print("[green]JWT token refreshed from cache[/green]")
                return True

            # Try to refresh using the Firebase refresh token
            firebase_api_key = os.environ.get("NEXT_PUBLIC_FIREBASE_API_KEY")
            if not firebase_api_key:
                console.print("[yellow]Cannot refresh token: NEXT_PUBLIC_FIREBASE_API_KEY not set[/yellow]")
                return False

            if not KEYRING_AVAILABLE:
                console.print("[yellow]Cannot refresh token: keyring not available[/yellow]")
                return False

            try:
                firebase_auth = FirebaseAuthenticator(firebase_api_key, "PDD Code Generator")
                refresh_token = firebase_auth._get_stored_refresh_token()

                if not refresh_token:
                    console.print("[yellow]Cannot refresh token: no refresh token stored. Please run 'pdd login' again.[/yellow]")
                    return False

                # Refresh the token
                new_id_token = await firebase_auth._refresh_firebase_token(refresh_token)
                if new_id_token:
                    self.jwt_token = new_id_token
                    _cache_jwt(new_id_token)
                    console.print("[green]JWT token refreshed successfully[/green]")
                    return True
                else:
                    console.print("[yellow]Token refresh returned empty token[/yellow]")
                    return False

            except Exception as e:
                console.print(f"[yellow]Failed to refresh JWT token: {e}[/yellow]")
                return False

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
        """Internal loop to send heartbeats every 30 seconds.

        Sends the first heartbeat immediately upon startup, then continues
        at regular intervals. Uses retry logic with exponential backoff to
        handle transient network failures during long-running operations.
        Automatically refreshes JWT token on 401 errors.
        """
        endpoint = CloudConfig.get_endpoint_url("heartbeatSession")

        # Ensure stop event is initialized
        if self._stop_event is None:
            self._stop_event = asyncio.Event()

        first_heartbeat = True

        while not self._stop_event.is_set():
            # Send heartbeat first (immediate on startup, then after each interval)
            if self.session_id:
                max_retries = 3
                retry_delay = 1.0  # Start with 1 second
                token_refreshed = False

                for attempt in range(max_retries):
                    try:
                        async with httpx.AsyncClient(timeout=10.0) as client:
                            response = await client.post(
                                endpoint,
                                json={"sessionId": self.session_id},
                                headers=self._get_headers()
                            )

                            if response.status_code == 401:
                                # Token expired - try to refresh
                                if not token_refreshed:
                                    console.print("[yellow]JWT token expired, attempting refresh...[/yellow]")
                                    if await self._refresh_token():
                                        token_refreshed = True
                                        continue  # Retry with new token
                                    else:
                                        console.print("[red]Token refresh failed. Please run 'pdd login' to re-authenticate.[/red]")
                                        break
                                else:
                                    console.print("[red]Heartbeat still failing after token refresh (Status: 401)[/red]")
                                    break
                            elif response.status_code >= 400:
                                console.print(f"[yellow]Warning: Heartbeat failed (Status: {response.status_code})[/yellow]")

                            break  # Success or non-retryable error, exit retry loop

                    except Exception as e:
                        if attempt == max_retries - 1:
                            # Final attempt failed - log but don't crash
                            console.print(f"[yellow]Warning: Heartbeat failed after {max_retries} attempts: {str(e)}[/yellow]")
                        else:
                            # Retry with exponential backoff
                            await asyncio.sleep(retry_delay)
                            retry_delay *= 2

            # For first heartbeat, use a short initial delay (5 seconds) to quickly
            # establish connection, then switch to normal 30-second intervals
            interval = 5.0 if first_heartbeat else 30.0
            first_heartbeat = False

            # Wait for interval or until stop event is set
            try:
                await asyncio.wait_for(self._stop_event.wait(), timeout=interval)
                break  # Stop event was set
            except asyncio.TimeoutError:
                pass  # Timeout reached, continue to next heartbeat

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
        token_refreshed = False

        for attempt in range(2):  # Allow one retry after token refresh
            async with httpx.AsyncClient(timeout=10.0) as client:
                try:
                    response = await client.get(
                        endpoint,
                        params={"sessionId": self.session_id},
                        headers=self._get_headers()
                    )

                    if response.status_code == 401:
                        # Token expired - try to refresh once
                        if not token_refreshed:
                            if await self._refresh_token():
                                token_refreshed = True
                                continue  # Retry with new token
                        console.print(f"[yellow]Warning: Failed to get commands (Status: {response.status_code})[/yellow]")
                        return []
                    elif response.status_code >= 400:
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

        return []

    async def update_command(
        self,
        command_id: str,
        status: str,
        response: Optional[Dict[str, Any]] = None
    ) -> None:
        """
        Update the status of a command in the cloud with retry logic.

        Args:
            command_id: The command ID to update.
            status: New status ("processing", "completed", "failed").
            response: Optional response data (for completed/failed status).

        Raises:
            RemoteSessionError: If update fails after all retries.
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

        # Retry logic with exponential backoff
        max_retries = 3
        retry_delay = 1  # Start with 1 second
        token_refreshed = False

        for attempt in range(max_retries):
            try:
                async with httpx.AsyncClient(timeout=10.0) as client:
                    result = await client.post(
                        endpoint,
                        json=payload,
                        headers=self._get_headers()
                    )

                    if result.status_code == 401:
                        # Token expired - try to refresh once
                        if not token_refreshed:
                            console.print("[yellow]JWT token expired during command update, attempting refresh...[/yellow]")
                            if await self._refresh_token():
                                token_refreshed = True
                                continue  # Retry with new token
                            else:
                                console.print("[red]Token refresh failed. Please run 'pdd login' to re-authenticate.[/red]")
                                raise RuntimeError("Authentication failed: token expired and refresh failed")
                        else:
                            console.print("[red]Command update still failing after token refresh (Status: 401)[/red]")
                            raise RuntimeError("Authentication failed after token refresh")

                    elif result.status_code >= 400:
                        error_msg = f"Failed to update command status: {result.text}"
                        console.print(f"[red]{error_msg}[/red]")
                        raise RuntimeError(error_msg)

                    # Success - return immediately
                    return

            except Exception as e:
                if attempt == max_retries - 1:
                    # Final attempt failed - raise error
                    console.print(f"[red]Failed to update command after {max_retries} attempts: {e}[/red]")
                    raise
                # Retry with exponential backoff
                console.print(f"[yellow]Cloud update failed (attempt {attempt + 1}/{max_retries}), retrying in {retry_delay}s...[/yellow]")
                await asyncio.sleep(retry_delay)
                retry_delay *= 2  # Exponential backoff

    async def _get_command_status(self, command_id: str) -> str:
        """
        Get current status of a command from cloud.

        Uses the getCommandStatus endpoint which returns any command regardless
        of status (unlike getCommands which only returns pending commands).

        Args:
            command_id: The command ID to check.

        Returns:
            str: Current status ('pending', 'processing', 'completed', 'failed', 'cancelled', or 'unknown').
        """
        if not self.session_id:
            return "unknown"

        endpoint = CloudConfig.get_endpoint_url("getCommandStatus")

        try:
            async with httpx.AsyncClient(timeout=10.0) as client:
                result = await client.get(
                    endpoint,
                    params={
                        "sessionId": self.session_id,
                        "commandId": command_id
                    },
                    headers=self._get_headers()
                )

                if result.status_code == 200:
                    data = result.json()
                    command = data.get("command", {})
                    return command.get("status", "unknown")
                elif result.status_code == 404:
                    # Command not found
                    return "unknown"
                return "unknown"

        except Exception as e:
            console.print(f"[yellow]Failed to check command status: {e}[/yellow]")
            return "unknown"

    async def _is_cancelled(self, command_id: str) -> bool:
        """
        Check if command was cancelled.

        Args:
            command_id: The command ID to check.

        Returns:
            bool: True if command status is 'cancelled', False otherwise.
        """
        status = await self._get_command_status(command_id)
        return status == "cancelled"

    async def _do_execute(self, cmd: CommandInfo) -> Tuple[str, dict]:
        """
        Actually execute the command via local FastAPI endpoint with log streaming.

        Args:
            cmd: The command to execute.

        Returns:
            Tuple[str, dict]: (job_id, response) from the local server.

        Raises:
            Exception: If execution fails.
            asyncio.CancelledError: If the command was cancelled.
        """
        local_url = f"http://127.0.0.1:{self.server_port}"
        execute_endpoint = "/api/v1/commands/execute"

        # Build request payload in CommandRequest format
        cmd_args = cmd.payload.get("args", {})
        cmd_options = cmd.payload.get("options", {})

        # Defensive parsing: handle cases where arrays might arrive as stringified JSON
        # This can happen if the cloud/Firestore serializes arrays incorrectly
        def parse_if_stringified_list(value):
            """Parse value if it looks like a stringified Python list."""
            if isinstance(value, str):
                stripped = value.strip()
                if stripped.startswith('[') and stripped.endswith(']'):
                    try:
                        # Try to parse as Python literal (e.g., "['a', 'b']")
                        parsed = ast.literal_eval(stripped)
                        if isinstance(parsed, list):
                            return parsed
                    except (ValueError, SyntaxError):
                        pass
            return value

        # Apply defensive parsing to args and options
        for key in list(cmd_args.keys()):
            cmd_args[key] = parse_if_stringified_list(cmd_args[key])
        for key in list(cmd_options.keys()):
            cmd_options[key] = parse_if_stringified_list(cmd_options[key])

        request_payload = {
            "command": cmd.type,
            "args": cmd_args,
            "options": cmd_options
        }

        # Build CLI command string for display
        cli_parts = ["pdd", cmd.type]
        # Handle positional args first (special 'args' key contains positional arguments)
        if "args" in cmd_args:
            args_value = cmd_args["args"]
            if isinstance(args_value, (list, tuple)):
                cli_parts.extend(str(v) for v in args_value)
            elif args_value is not None:
                cli_parts.append(str(args_value))
        # Then handle other args as named options
        for key, value in cmd_args.items():
            if key == "args":
                continue  # Already handled above
            if isinstance(value, bool):
                if value:
                    cli_parts.append(f"--{key}")
            elif isinstance(value, (list, tuple)):
                # Handle list values (e.g., multiple --env flags)
                for v in value:
                    cli_parts.append(f"--{key} {v}")
            elif isinstance(value, str) and " " in value:
                cli_parts.append(f'--{key} "{value}"')
            else:
                cli_parts.append(f"--{key} {value}")
        for key, value in cmd_options.items():
            if isinstance(value, bool):
                if value:
                    cli_parts.append(f"--{key}")
            elif isinstance(value, (list, tuple)):
                # Handle list values (e.g., multiple --env flags)
                for v in value:
                    cli_parts.append(f"--{key} {v}")
            else:
                cli_parts.append(f"--{key} {value}")
        cli_command = " ".join(cli_parts)

        # Log command details
        console.print(f"\n[bold cyan]{'═' * 60}[/bold cyan]")
        console.print(f"[bold cyan]REMOTE COMMAND RECEIVED[/bold cyan]")
        console.print(f"[bold cyan]{'═' * 60}[/bold cyan]")
        console.print(f"[bold]Command:[/bold] [green]{cli_command}[/green]")
        console.print(f"[dim]{'─' * 60}[/dim]")
        console.print(f"[bold]Output:[/bold]")

        async with httpx.AsyncClient(timeout=300.0) as client:
            # Submit the job
            submit_result = await client.post(
                f"{local_url}{execute_endpoint}",
                json=request_payload
            )

            if submit_result.status_code >= 400:
                raise Exception(submit_result.text)

            submit_data = submit_result.json()
            job_id = submit_data.get("job_id")

            if not job_id:
                raise Exception("No job_id in response")

            # Poll for job completion with log streaming and cancellation checks
            status_endpoint = f"/api/v1/commands/jobs/{job_id}"
            last_update_time = asyncio.get_event_loop().time()
            update_interval = 2.0  # Send updates every 2 seconds (was 3)
            last_stdout_len = 0
            last_stderr_len = 0

            while True:
                # Check for cancellation BEFORE polling - this is critical for responsiveness
                if await self._is_cancelled(cmd.command_id):
                    console.print(f"[yellow]Cancellation detected during job execution[/yellow]")
                    # Cancel the local job
                    await self._cancel_local_job(job_id)
                    # Return cancelled status
                    return job_id, {"status": "cancelled", "result": {}}

                status_result = await client.get(f"{local_url}{status_endpoint}")
                if status_result.status_code >= 400:
                    raise Exception(status_result.text)

                status_data = status_result.json()
                job_status = status_data.get("status")

                # Get current output and display new content
                result = status_data.get("result", {})
                if isinstance(result, dict):
                    stdout = result.get("stdout", "")
                    stderr = result.get("stderr", "")

                    # Print incremental stdout (raw, preserving formatting)
                    if stdout and len(stdout) > last_stdout_len:
                        new_stdout = stdout[last_stdout_len:]
                        # Print raw output directly to preserve formatting
                        print(new_stdout, end="", flush=True)
                        last_stdout_len = len(stdout)

                    # Send periodic output updates to cloud
                    current_time = asyncio.get_event_loop().time()
                    if current_time - last_update_time >= update_interval:
                        if stdout or stderr:
                            try:
                                await self._update_command_output(
                                    cmd.command_id,
                                    stdout=stdout,
                                    stderr=stderr
                                )
                                last_update_time = current_time
                            except Exception:
                                pass  # Don't clutter output with cloud update errors

                if job_status in ("completed", "failed", "cancelled"):
                    # Get final output
                    final_result = status_data.get("result", {})
                    final_stdout = final_result.get("stdout", "") if isinstance(final_result, dict) else ""
                    final_stderr = final_result.get("stderr", "") if isinstance(final_result, dict) else ""
                    exit_code = final_result.get("exit_code", 0) if isinstance(final_result, dict) else 0

                    # Print final summary
                    console.print(f"\n[dim]{'─' * 60}[/dim]")
                    console.print(f"[bold]Exit code:[/bold] {exit_code}")
                    if final_stdout:
                        console.print(f"[bold]Stdout ({len(final_stdout)} chars)[/bold]")
                    if final_stderr:
                        console.print(f"[bold yellow]Stderr ({len(final_stderr)} chars):[/bold yellow]")
                        # Print stderr since we didn't stream it
                        for line in final_stderr.splitlines():
                            console.print(f"[yellow]{line}[/yellow]")
                    console.print(f"[dim]{'─' * 60}[/dim]")
                    if job_status == "completed":
                        console.print(f"[bold green]✓ COMMAND COMPLETED[/bold green]")
                    elif job_status == "failed":
                        console.print(f"[bold red]✗ COMMAND FAILED[/bold red]")
                    elif job_status == "cancelled":
                        console.print(f"[bold yellow]⊘ COMMAND CANCELLED[/bold yellow]")
                    console.print(f"[bold cyan]{'═' * 60}[/bold cyan]\n")
                    return job_id, status_data

                # Short sleep to be responsive to cancellation
                await asyncio.sleep(0.5)

    async def _update_command_output(
        self,
        command_id: str,
        stdout: str = "",
        stderr: str = ""
    ) -> None:
        """
        Update cloud with intermediate command output for log streaming.

        Args:
            command_id: The command ID to update.
            stdout: Current stdout output.
            stderr: Current stderr output.
        """
        if not self.session_id:
            return

        endpoint = CloudConfig.get_endpoint_url("updateCommand")

        payload = {
            "sessionId": self.session_id,
            "commandId": command_id,
            "status": "processing",  # Keep status as processing
            "response": {
                "stdout": stdout,
                "stderr": stderr,
                "streaming": True,  # Indicate this is a streaming update
            }
        }

        try:
            async with httpx.AsyncClient(timeout=5.0) as client:
                await client.post(
                    endpoint,
                    json=payload,
                    headers=self._get_headers()
                )
        except Exception:
            pass  # Don't fail on streaming updates

    async def _cancel_local_job(self, job_id: str) -> bool:
        """
        Cancel a job running on the local server.

        Args:
            job_id: The local job ID to cancel.

        Returns:
            bool: True if cancellation was successful.
        """
        local_url = f"http://127.0.0.1:{self.server_port}"
        cancel_endpoint = f"/api/v1/commands/jobs/{job_id}/cancel"

        try:
            async with httpx.AsyncClient(timeout=10.0) as client:
                result = await client.post(f"{local_url}{cancel_endpoint}")
                if result.status_code < 400:
                    data = result.json()
                    return data.get("cancelled", False)
                return False
        except Exception as e:
            console.print(f"[yellow]Failed to cancel local job: {e}[/yellow]")
            return False

    async def _execute_command(self, cmd: CommandInfo) -> None:
        """
        Execute a command locally and report results back to the cloud.

        Supports cancellation during execution - cancellation is now checked
        inside _do_execute() for faster response times.

        Args:
            cmd: The command to execute.
        """
        try:
            # 1. Update status to "processing"
            await self.update_command(cmd.command_id, status="processing")

            # 2. Check if command was cancelled before starting execution
            if await self._is_cancelled(cmd.command_id):
                console.print(f"[yellow]Command cancelled before execution[/yellow]")
                await self.update_command(cmd.command_id, status="cancelled")
                return

            # 3. Execute the command - cancellation is checked inside _do_execute()
            local_job_id, response_data = await self._do_execute(cmd)

            # 4. Check if the local job was cancelled
            job_status = response_data.get("status", "")
            if job_status == "cancelled":
                await self.update_command(cmd.command_id, status="cancelled")
                console.print(f"[yellow]Command was cancelled[/yellow]")
                return

            # 5. Map to expected structure for frontend
            result = response_data.get("result", {})
            error_msg = ""
            if job_status == "failed":
                # Capture error from response or from stderr
                error_msg = response_data.get("error", "")
                if not error_msg and isinstance(result, dict):
                    error_msg = result.get("stderr", "") or result.get("stdout", "")

            formatted_response = {
                "success": job_status == "completed",
                "message": error_msg,
                "exit_code": result.get("exit_code", 0) if isinstance(result, dict) else 0,
                "stdout": result.get("stdout", "") if isinstance(result, dict) else "",
                "stderr": result.get("stderr", "") if isinstance(result, dict) else "",
                "files_created": result.get("files_created", []) if isinstance(result, dict) else [],
                "cost": response_data.get("cost", 0.0),
            }

            final_status = "completed" if job_status == "completed" else "failed"
            await self.update_command(
                cmd.command_id,
                status=final_status,
                response=formatted_response
            )

        except asyncio.CancelledError:
            # Task was cancelled externally
            console.print(f"[yellow]Command execution cancelled[/yellow]")
            await self.update_command(cmd.command_id, status="cancelled")

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