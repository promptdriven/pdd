from __future__ import annotations

import asyncio
import json
from typing import Any, Dict, List, Optional

import click
from rich.console import Console
from rich.table import Table

from ..core.cloud import CloudConfig
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
        console.print(f"[red]Error listing sessions: {e}[/red]")
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
        console.print(f"[red]Error fetching session: {e}[/red]")
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


@sessions.command(name="cleanup")
@click.option("--all", "cleanup_all", is_flag=True, help="Cleanup all sessions (including active).")
@click.option("--stale", "cleanup_stale", is_flag=True, help="Cleanup only stale sessions.")
@click.option("--force", is_flag=True, help="Skip confirmation prompt.")
def cleanup_sessions(cleanup_all: bool, cleanup_stale: bool, force: bool) -> None:
    """Cleanup (deregister) remote sessions.

    By default, lists sessions and prompts for cleanup.
    Use --all to cleanup all sessions, or --stale to cleanup only stale sessions.
    """
    jwt_token = CloudConfig.get_jwt_token()
    if not jwt_token:
        console.print("[red]Error: Not authenticated. Please run 'pdd login'.[/red]")
        return

    try:
        sessions_list = asyncio.run(RemoteSessionManager.list_sessions(jwt_token))
    except Exception as e:
        console.print(f"[red]Error listing sessions: {e}[/red]")
        return

    if not sessions_list:
        console.print("[yellow]No active remote sessions found.[/yellow]")
        return

    # Filter sessions based on flags
    if cleanup_stale:
        sessions_to_cleanup = [s for s in sessions_list if getattr(s, "status", "").lower() == "stale"]
        if not sessions_to_cleanup:
            console.print("[yellow]No stale sessions found.[/yellow]")
            return
    elif cleanup_all:
        sessions_to_cleanup = sessions_list
    else:
        # Interactive mode - show sessions and ask which to cleanup
        console.print("[bold]Current remote sessions:[/bold]")
        table = Table(show_header=True, header_style="bold magenta")
        table.add_column("#", style="dim", width=3)
        table.add_column("SESSION ID", style="dim", width=12)
        table.add_column("PROJECT")
        table.add_column("STATUS")
        table.add_column("LAST SEEN")

        for idx, session in enumerate(sessions_list, 1):
            s_id = getattr(session, "session_id", "unknown")
            project = getattr(session, "project_name", "default")
            status = getattr(session, "status", "unknown")
            last_seen = getattr(session, "last_heartbeat", "never")

            display_id = s_id[:8] if len(s_id) > 8 else s_id

            status_str = str(status)
            if status_str.lower() == "active":
                status_render = f"[green]{status_str}[/green]"
            elif status_str.lower() == "stale":
                status_render = f"[yellow]{status_str}[/yellow]"
            else:
                status_render = status_str

            table.add_row(
                str(idx),
                display_id,
                str(project),
                status_render,
                str(last_seen)
            )

        console.print(table)
        console.print("\n[bold]Options:[/bold]")
        console.print("  - Enter session numbers (comma-separated) to cleanup specific sessions")
        console.print("  - Enter 'stale' to cleanup all stale sessions")
        console.print("  - Enter 'all' to cleanup all sessions")
        console.print("  - Press Enter to cancel")

        choice = click.prompt("\nYour choice", default="", show_default=False)

        if not choice:
            console.print("[yellow]Cancelled.[/yellow]")
            return

        if choice.lower() == "all":
            sessions_to_cleanup = sessions_list
        elif choice.lower() == "stale":
            sessions_to_cleanup = [s for s in sessions_list if getattr(s, "status", "").lower() == "stale"]
            if not sessions_to_cleanup:
                console.print("[yellow]No stale sessions found.[/yellow]")
                return
        else:
            # Parse comma-separated numbers
            try:
                indices = [int(x.strip()) - 1 for x in choice.split(",")]
                sessions_to_cleanup = [sessions_list[i] for i in indices if 0 <= i < len(sessions_list)]
                if not sessions_to_cleanup:
                    console.print("[red]Invalid selection.[/red]")
                    return
            except (ValueError, IndexError):
                console.print("[red]Invalid input. Please enter numbers separated by commas.[/red]")
                return

    # Confirm cleanup
    if not force:
        console.print(f"\n[bold yellow]About to cleanup {len(sessions_to_cleanup)} session(s):[/bold yellow]")
        for session in sessions_to_cleanup:
            s_id = getattr(session, "session_id", "unknown")
            project = getattr(session, "project_name", "default")
            console.print(f"  - {s_id[:8]} ({project})")

        if not click.confirm("\nProceed with cleanup?", default=False):
            console.print("[yellow]Cancelled.[/yellow]")
            return

    # Perform cleanup
    success_count = 0
    fail_count = 0

    async def cleanup_session(session_id: str) -> bool:
        """Helper to deregister a single session."""
        from pathlib import Path
        manager = RemoteSessionManager(jwt_token, project_path=Path.cwd())
        manager.session_id = session_id
        try:
            await manager.deregister()
            return True
        except Exception as e:
            console.print(f"[red]Failed to cleanup {session_id[:8]}: {e}[/red]")
            return False

    with console.status("[bold green]Cleaning up sessions..."):
        for session in sessions_to_cleanup:
            s_id = getattr(session, "session_id", "unknown")
            if asyncio.run(cleanup_session(s_id)):
                success_count += 1
            else:
                fail_count += 1

    console.print(f"\n[bold green]✓[/bold green] Successfully cleaned up {success_count} session(s)")
    if fail_count > 0:
        console.print(f"[bold red]✗[/bold red] Failed to cleanup {fail_count} session(s)")
