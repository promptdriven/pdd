"""
PDD Connect Command.

This module provides the `pdd connect` CLI command which launches a local
REST server to enable the web frontend to interact with PDD.
"""

from __future__ import annotations

import os
import webbrowser
from pathlib import Path
from typing import Optional

import click

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
@click.pass_context
def connect(
    ctx: click.Context,
    port: int,
    host: str,
    allow_remote: bool,
    token: Optional[str],
    no_browser: bool,
    frontend_url: Optional[str],
) -> None:
    """
    Launch the local REST server for the PDD web frontend.

    This command starts a FastAPI server that exposes the PDD functionality
    via a REST API. It automatically opens the web interface in your default
    browser unless --no-browser is specified.
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
    ]
    if frontend_url:
        allowed_origins.append(frontend_url)

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
    click.echo(f"Frontend: {click.style(target_url, underline=True)}")
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
        # We use log_level="info" to show access logs, but suppress excessive debug info
        uvicorn.run(
            app,
            host=host,
            port=port,
            log_level="info",
            access_log=True
        )
    except KeyboardInterrupt:
        click.echo(click.style("\nServer stopping...", fg="yellow", bold=True))
    except Exception as e:
        click.echo(click.style(f"\nServer error: {e}", fg="red", bold=True))
        ctx.exit(1)
    finally:
        click.echo(click.style("Goodbye!", fg="blue"))