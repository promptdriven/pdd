from __future__ import annotations

import asyncio
import json
from typing import Any, Dict, List, Optional

import click
from rich.console import Console
from rich.table import Table

from ..core.cloud import CloudConfig
from ..core.errors import handle_error
from ..remote_session import RemoteSessionManager, RemoteSessionError

console = Console()


@click.group(name="sessions")
def sessions() -> None:
    """Manage remote PDD sessions."""
    pass


@sessions.command(name="list")
@click.option("--json", "json_output", is_flag=True, help="Output as JSON.")
def list_sessions(json_output: bool) -> None:
    """List active remote sessions.

    Retrieves a list of active remote sessions associated with the current
    authenticated user and displays them in a table or as JSON.
    """
    jwt_token = CloudConfig.get_jwt_token()
    if not jwt_token:
        console.print("[red]Error: Not authenticated. Please run 'pdd auth login'.[/red]")
        return

    try:
        sessions_list = asyncio.run(RemoteSessionManager.list_sessions(jwt_token))
    except Exception as e:
        handle_error(e)
        return

    if json_output:
        output_data = []
        for s in sessions_list:
            # Handle Pydantic v1/v2 or dataclasses
            if hasattr(s, "model_dump"):
                output_data.append(s.model_dump())
            elif hasattr(s, "dict"):
                output_data.append(s.dict())
            else:
                output_data.append(s.__dict__)
        console.print_json(data=output_data)
        return

    if not sessions_list:
        console.print("[yellow]No active remote sessions found.[/yellow]")
        return

    table = Table(show_header=True, header_style="bold magenta")
    table.add_column("SESSION ID", style="dim", width=12)
    table.add_column("PROJECT")
    table.add_column("CLOUD URL", style="blue")
    table.add_column("STATUS")
    table.add_column("LAST SEEN")

    for session in sessions_list:
        # Safely access attributes with defaults
        s_id = getattr(session, "session_id", "unknown")
        project = getattr(session, "project_name", "default")
        url = getattr(session, "cloud_url", "")
        status = getattr(session, "status", "unknown")
        last_seen = getattr(session, "last_heartbeat", "never")

        # Truncate ID for display
        display_id = s_id[:8] if len(s_id) > 8 else s_id

        # Colorize status
        status_str = str(status)
        if status_str.lower() == "active":
            status_render = f"[green]{status_str}[/green]"
        elif status_str.lower() == "stale":
            status_render = f"[yellow]{status_str}[/yellow]"
        else:
            status_render = status_str

        table.add_row(
            display_id,
            str(project),
            str(url),
            status_render,
            str(last_seen)
        )

    console.print(table)


@sessions.command(name="info")
@click.argument("session_id")
def session_info(session_id: str) -> None:
    """Display detailed info about a specific session.

    Args:
        session_id: The unique identifier of the session to inspect.
    """
    jwt_token = CloudConfig.get_jwt_token()
    if not jwt_token:
        console.print("[red]Error: Not authenticated. Please run 'pdd auth login'.[/red]")
        return

    try:
        # Attempt to fetch specific session details
        # Note: Assuming get_session exists on RemoteSessionManager
        session = asyncio.run(RemoteSessionManager.get_session(jwt_token, session_id))
    except Exception as e:
        handle_error(e)
        return

    if not session:
        console.print(f"[red]Session '{session_id}' not found.[/red]")
        return

    console.print(f"[bold blue]Session Information: {session_id}[/bold blue]")

    # Convert session object to dictionary for iteration
    if hasattr(session, "model_dump"):
        data = session.model_dump()
    elif hasattr(session, "dict"):
        data = session.dict()
    else:
        data = session.__dict__

    # Display metadata in a clean table
    table = Table(show_header=False, box=None, padding=(0, 2))
    table.add_column("Field", style="bold cyan", justify="right")
    table.add_column("Value", style="white")

    # Sort keys for consistent display
    for key in sorted(data.keys()):
        value = data[key]
        # Format key for display (snake_case to Title Case)
        display_key = key.replace("_", " ").title()
        table.add_row(display_key, str(value))

    console.print(table)