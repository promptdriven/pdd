"""
PDD Connect Command.

This module provides the `pdd connect` CLI command which launches a local
REST server to enable the web frontend to interact with PDD.
"""

from __future__ import annotations

import asyncio
import errno
import os
import socket
import webbrowser
from pathlib import Path
from typing import Optional

import click


# Default port and range for auto-assignment
DEFAULT_PORT = 9876
PORT_RANGE_START = 9876
PORT_RANGE_END = 9899  # Try up to 24 ports


def is_port_available(port: int, host: str = "127.0.0.1") -> bool:
    """Check if a port is available for binding."""
    try:
        with socket.socket(socket.AF_INET, socket.SOCK_STREAM) as s:
            s.setsockopt(socket.SOL_SOCKET, socket.SO_REUSEADDR, 1)
            s.bind((host, port))
            return True
    except OSError as exc:
        # If we lack permission to bind (common in sandboxed environments),
        # treat availability as unknown and allow the caller to proceed.
        if exc.errno in (errno.EACCES, errno.EPERM):
            return True
        return False


def find_available_port(start_port: int, end_port: int, host: str = "127.0.0.1") -> Optional[int]:
    """Find an available port in the given range."""
    for port in range(start_port, end_port + 1):
        if is_port_available(port, host):
            return port
    return None

# Handle optional dependencies - uvicorn may not be installed
try:
    import uvicorn
except ImportError:
    uvicorn = None

# Internal imports
# We wrap this in a try/except block to allow the module to be imported
# even if the server dependencies are not present (e.g. in partial environments)
try:
    from ..server.app import create_app
except (ImportError, ValueError):
    def create_app(*args, **kwargs):
        raise ImportError("Could not import pdd.server.app.create_app. Ensure server dependencies are installed.")


@click.command("connect")
@click.option(
    "--port",
    default=9876,
    help="Port to listen on",
    show_default=True,
    type=int,
)
@click.option(
    "--host",
    default="127.0.0.1",
    help="Host to bind to",
    show_default=True,
)
@click.option(
    "--allow-remote",
    is_flag=True,
    help="Allow non-localhost connections",
)
@click.option(
    "--token",
    help="Bearer token for authentication",
    default=None,
)
@click.option(
    "--no-browser",
    is_flag=True,
    help="Don't open browser automatically",
)
@click.option(
    "--frontend-url",
    help="Custom frontend URL",
    default=None,
)
@click.option(
    "--local-only",
    is_flag=True,
    help="Skip cloud registration (local access only)",
)
@click.option(
    "--session-name",
    help="Custom session name for identification",
    default=None,
)
@click.pass_context
def connect(
    ctx: click.Context,
    port: int,
    host: str,
    allow_remote: bool,
    token: Optional[str],
    no_browser: bool,
    frontend_url: Optional[str],
    local_only: bool,
    session_name: Optional[str],
) -> None:
    """
    Launch the local REST server for the PDD web frontend.

    This command starts a FastAPI server that exposes the PDD functionality
    via a REST API. It automatically opens the web interface in your default
    browser unless --no-browser is specified.

    For authenticated users, the session is automatically registered with
    PDD Cloud for remote access. Use --local-only to skip cloud registration.
    """
    # Check uvicorn is available
    if uvicorn is None:
        click.echo(click.style("Error: 'uvicorn' is not installed. Please install it to use the connect command.", fg="red"))
        ctx.exit(1)

    # 1. Determine Project Root
    # We assume the current working directory is the project root
    project_root = Path.cwd()

    # 2. Security Checks & Configuration
    if allow_remote:
        if not token:
            click.echo(click.style(
                "SECURITY WARNING: You are allowing remote connections without an authentication token.",
                fg="red", bold=True
            ))
            click.echo("Anyone with access to your network could execute code on your machine.")
            if not click.confirm("Do you want to proceed?"):
                ctx.exit(1)

        # If user explicitly asked for remote but left host as localhost,
        # bind to all interfaces to actually allow remote connections.
        if host == "127.0.0.1":
            host = "0.0.0.0"
            click.echo(click.style("Binding to 0.0.0.0 to allow remote connections.", fg="yellow"))
    else:
        # Warn if binding to non-localhost without explicit allow-remote
        if host not in ("127.0.0.1", "localhost"):
            click.echo(click.style(
                f"Warning: Binding to {host} without --allow-remote flag. "
                "External connections may be blocked or insecure.",
                fg="yellow"
            ))

    # 2.5 Smart Port Detection
    # Check if user explicitly specified a port
    port_source = ctx.get_parameter_source("port")
    user_specified_port = port_source == click.core.ParameterSource.COMMANDLINE

    # For port checking, use the effective bind host
    check_host = "0.0.0.0" if host == "0.0.0.0" else "127.0.0.1"

    if not is_port_available(port, check_host):
        if user_specified_port:
            # User explicitly requested this port, show error
            click.echo(click.style(
                f"Error: Port {port} is already in use.",
                fg="red", bold=True
            ))
            click.echo("Please specify a different port with --port or stop the process using this port.")
            ctx.exit(1)
        else:
            # Auto-detect an available port
            click.echo(click.style(
                f"Port {port} is in use, looking for an available port...",
                fg="yellow"
            ))
            available_port = find_available_port(PORT_RANGE_START, PORT_RANGE_END, check_host)
            if available_port is None:
                click.echo(click.style(
                    f"Error: No available ports found in range {PORT_RANGE_START}-{PORT_RANGE_END}.",
                    fg="red", bold=True
                ))
                click.echo("Please specify a port manually with --port or free up a port in this range.")
                ctx.exit(1)
            port = available_port
            click.echo(click.style(
                f"Using port {port} instead.",
                fg="green"
            ))

    # 3. Determine URLs
    # The server URL is where the API lives
    server_url = f"http://{host}:{port}"

    # The frontend URL is what we open in the browser
    # If binding to 0.0.0.0, we still use localhost for the local browser
    browser_host = "localhost" if host == "0.0.0.0" else host
    target_url = frontend_url if frontend_url else f"http://{browser_host}:{port}"

    # 4. Configure CORS
    # We need to allow the frontend to talk to the backend
    allowed_origins = [
        "http://localhost:3000",
        "http://127.0.0.1:3000",
        "http://localhost:5173",
        "http://127.0.0.1:5173",
        f"http://localhost:{port}",
        f"http://127.0.0.1:{port}",
        # PDD Cloud frontend
        "https://pdd.dev",
        "https://www.pdd.dev",
    ]
    if frontend_url:
        allowed_origins.append(frontend_url)

    # 4.5 Cloud Session Registration (automatic for authenticated users)
    session_manager = None
    cloud_url = None
    if not local_only:
        try:
            from ..core.cloud import CloudConfig
            from ..remote_session import (
                RemoteSessionManager,
                RemoteSessionError,
                set_active_session_manager,
            )

            # Check if user is authenticated
            jwt_token = CloudConfig.get_jwt_token(verbose=False)
            if not jwt_token:
                click.echo(click.style(
                    "Not authenticated. Running in local-only mode.",
                    dim=True
                ))
                click.echo(click.style(
                    "Run 'pdd login' to enable remote access via cloud.",
                    dim=True
                ))
            else:
                click.echo("Registering session with PDD Cloud...")
                session_manager = RemoteSessionManager(jwt_token, project_root, server_port=port)
                try:
                    # Register with cloud - no public URL needed, cloud hosts everything
                    cloud_url = asyncio.run(session_manager.register(
                        session_name=session_name,
                    ))
                    # Heartbeat will be started by the app's lifespan manager
                    set_active_session_manager(session_manager)

                    click.echo(click.style(
                        "Session registered with PDD Cloud!", fg="green", bold=True
                    ))
                    # TODO: Re-enable when production /connect page is deployed
                    # click.echo(f"  Access URL: {click.style(cloud_url, fg='cyan', underline=True)}")
                    # click.echo(click.style(
                    #     "  Share this URL to access your PDD session from any browser.",
                    #     dim=True
                    # ))
                except RemoteSessionError as e:
                    click.echo(click.style(
                        f"Warning: Failed to register with cloud: {e.message}",
                        fg="yellow"
                    ))
                    click.echo(click.style(
                        "Running in local-only mode.",
                        dim=True
                    ))
                    session_manager = None
        except ImportError as e:
            click.echo(click.style(
                f"Running in local-only mode (cloud dependencies not available).",
                dim=True
            ))
    else:
        click.echo(click.style(
            "Running in local-only mode (--local-only flag set).",
            dim=True
        ))

    # 5. Initialize Server App
    try:
        # Pass token via environment variable if provided, as create_app might not take it directly
        if token:
            os.environ["PDD_ACCESS_TOKEN"] = token

        app = create_app(project_root, allowed_origins=allowed_origins)
    except Exception as e:
        click.echo(click.style(f"Failed to initialize server: {e}", fg="red", bold=True))
        ctx.exit(1)

    # 6. Print Status Messages
    click.echo(click.style(f"Starting PDD server on {server_url}", fg="green", bold=True))
    click.echo(f"Project Root: {click.style(str(project_root), fg='blue')}")
    click.echo(f"API Documentation: {click.style(f'{server_url}/docs', underline=True)}")
    click.echo(f"Local Frontend: {click.style(target_url, underline=True)}")
    # TODO: Re-enable when production /connect page is deployed
    # if cloud_url:
    #     click.echo(f"Remote Access: {click.style(cloud_url, fg='cyan', underline=True)}")
    click.echo(click.style("Press Ctrl+C to stop the server", dim=True))

    # 7. Open Browser
    if not no_browser:
        # Import remote session detection
        from ..core.remote_session import is_remote_session

        is_remote, reason = is_remote_session()
        if is_remote:
            click.echo(click.style(f"Note: {reason}", fg="yellow"))
            click.echo("Opening browser may not work in remote sessions. Use the URL above to connect manually.")

        click.echo("Opening browser...")
        try:
            webbrowser.open(target_url)
        except Exception as e:
            click.echo(click.style(f"Could not open browser: {e}", fg="yellow"))
            click.echo(f"Please open {target_url} manually in your browser.")

    # 8. Run Server
    try:
        # Run uvicorn
        # Disable access_log to avoid noisy polling logs - custom middleware handles important logging
        uvicorn.run(
            app,
            host=host,
            port=port,
            log_level="warning",  # Only show warnings and errors from uvicorn
            access_log=False  # Custom middleware handles request logging
        )
    except KeyboardInterrupt:
        click.echo(click.style("\nServer stopping...", fg="yellow", bold=True))
    except Exception as e:
        click.echo(click.style(f"\nServer error: {e}", fg="red", bold=True))
        ctx.exit(1)
    finally:
        # Clean up cloud session if registered
        if session_manager is not None:
            click.echo("Deregistering from PDD Cloud...")
            try:
                from ..remote_session import set_active_session_manager
                asyncio.run(session_manager.stop_heartbeat())
                asyncio.run(session_manager.deregister())
                set_active_session_manager(None)
                click.echo(click.style("Session deregistered.", fg="green"))
            except Exception as e:
                click.echo(click.style(f"Warning: Error during session cleanup: {e}", fg="yellow"))

        click.echo(click.style("Goodbye!", fg="blue"))
