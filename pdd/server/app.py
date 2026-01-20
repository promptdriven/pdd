from __future__ import annotations

import asyncio
from contextlib import asynccontextmanager
from datetime import datetime, timezone
from pathlib import Path
from typing import Optional, List, Union

import uvicorn
from fastapi import FastAPI, Request, status
from fastapi.responses import JSONResponse, FileResponse, HTMLResponse
from fastapi.exceptions import RequestValidationError
from fastapi.staticfiles import StaticFiles
from rich.console import Console

from .models import ServerStatus, ServerConfig
from .security import (
    PathValidator,
    SecurityError,
    configure_cors,
    SecurityLoggingMiddleware,
)
from .jobs import JobManager
from .routes.websocket import ConnectionManager, create_websocket_routes
from .routes import architecture, auth, files, commands, prompts
from .routes import websocket as ws_routes
from .routes.config import router as config_router

# Initialize Rich console
console = Console()

# ============================================================================
# Application State
# ============================================================================

class AppState:
    """
    Application state container for dependency injection.
    Holds thread-safe references to shared managers and configuration.
    """

    def __init__(self, project_root: Path, config: Optional[ServerConfig] = None):
        self.project_root = project_root.resolve()
        self.start_time = datetime.now(timezone.utc)
        self.version = "0.1.0"  # In a real app, load from package metadata

        # Store server config for port access
        self.config = config or ServerConfig()

        # Initialize managers
        self.path_validator = PathValidator(self.project_root)
        # SAFETY: Limit concurrent jobs to 3 - LLM calls are resource-intensive
        # Running too many in parallel can exhaust memory/CPU and crash the system
        self.job_manager = JobManager(max_concurrent=3, project_root=self.project_root)
        self.connection_manager = ConnectionManager()

    @property
    def server_port(self) -> int:
        """Get the configured server port."""
        return self.config.port

    @property
    def uptime_seconds(self) -> float:
        return (datetime.now(timezone.utc) - self.start_time).total_seconds()


# Global state instance (set during app creation)
_app_state: Optional[AppState] = None


def get_app_state() -> AppState:
    """Dependency to get the global application state."""
    if _app_state is None:
        raise RuntimeError("Application state not initialized. Call create_app() first.")
    return _app_state


def get_path_validator() -> PathValidator:
    """Dependency to get the path validator."""
    return get_app_state().path_validator


def get_job_manager() -> JobManager:
    """Dependency to get the job manager."""
    return get_app_state().job_manager


def get_connection_manager() -> ConnectionManager:
    """Dependency to get the WebSocket connection manager."""
    return get_app_state().connection_manager


def get_server_port() -> int:
    """Dependency to get the configured server port."""
    return get_app_state().server_port


# ============================================================================
# Exception Handlers
# ============================================================================

async def security_exception_handler(request: Request, exc: SecurityError):
    """Handle security violations (403)."""
    # Log the full error with code for server-side debugging
    console.print(f"[bold red]Security Violation:[/bold red] {exc.message} ({exc.code})")
    
    # Return only the message to the client to match expected log output behavior
    return JSONResponse(
        status_code=status.HTTP_403_FORBIDDEN,
        content={"detail": exc.message},
    )


async def validation_exception_handler(request: Request, exc: RequestValidationError):
    """Handle Pydantic validation errors (422)."""
    return JSONResponse(
        status_code=status.HTTP_422_UNPROCESSABLE_ENTITY,
        content={"detail": exc.errors(), "body": str(exc.body)},
    )


async def generic_exception_handler(request: Request, exc: Exception):
    """Handle unexpected exceptions (500)."""
    console.print(f"[bold red]Server Error:[/bold red] {str(exc)}")
    return JSONResponse(
        status_code=status.HTTP_500_INTERNAL_SERVER_ERROR,
        content={"detail": "Internal server error"},
    )


# ============================================================================
# App Factory & Lifespan
# ============================================================================

@asynccontextmanager
async def lifespan(app: FastAPI):
    """
    Application lifespan manager.
    Handles startup initialization and shutdown cleanup.
    """
    state = get_app_state()

    # Startup
    console.print(f"[green]PDD Server starting...[/green]")
    console.print(f"Project Root: [bold]{state.project_root}[/bold]")

    # Start remote session heartbeat and command polling if configured
    from ..remote_session import get_active_session_manager
    session_manager = get_active_session_manager()
    if session_manager:
        session_manager.start_heartbeat()
        session_manager.start_command_polling()
        console.print("[dim]Remote session heartbeat and command polling started[/dim]")

    yield

    # Shutdown
    console.print("[yellow]Shutting down PDD Server...[/yellow]")

    # Stop remote session heartbeat and command polling
    if session_manager:
        try:
            await session_manager.stop_heartbeat()
            await session_manager.stop_command_polling()
            console.print("[dim]Remote session heartbeat and command polling stopped[/dim]")
        except Exception as e:
            console.print(f"[yellow]Warning: Error stopping remote session tasks: {e}[/yellow]")

    # Cancel active jobs
    try:
        active_jobs = state.job_manager.get_active_jobs()
        if active_jobs:
            console.print(f"Cancelling {len(active_jobs)} active jobs...")
            await state.job_manager.shutdown()
    except Exception as e:
        console.print(f"[red]Error during job manager shutdown: {e}[/red]")

    console.print("[green]Shutdown complete.[/green]")


def create_app(
    project_root: Path, 
    config: Optional[ServerConfig] = None,
    allowed_origins: Optional[List[str]] = None
) -> FastAPI:
    """
    Create and configure the FastAPI application.

    Args:
        project_root: The project directory to serve.
        config: Server configuration object (preferred).
        allowed_origins: List of allowed CORS origins (legacy/fallback).

    Returns:
        Configured FastAPI application.
    """
    global _app_state
    _app_state = AppState(project_root, config=config)

    # Determine configuration with proper fallback
    origins = None
    if config:
        origins = config.allowed_origins
    
    if origins is None:
        origins = allowed_origins

    app = FastAPI(
        title="PDD Server",
        description="Local REST server for Prompt Driven Development (PDD) web frontend",
        version=_app_state.version,
        lifespan=lifespan,
        docs_url="/docs",
        redoc_url="/redoc",
    )

    # 1. Configure Middleware
    app.add_middleware(SecurityLoggingMiddleware)
    configure_cors(app, origins)

    # 2. Register Exception Handlers
    app.add_exception_handler(SecurityError, security_exception_handler)
    app.add_exception_handler(RequestValidationError, validation_exception_handler)
    app.add_exception_handler(Exception, generic_exception_handler)

    # 3. Register Routes
    @app.get("/api/v1/status", response_model=ServerStatus, tags=["status"])
    async def get_status():
        state = get_app_state()
        return ServerStatus(
            version=state.version,
            project_root=str(state.project_root),
            uptime_seconds=state.uptime_seconds,
            active_jobs=len(state.job_manager.get_active_jobs()),
            connected_clients=len(state.connection_manager.active_connections),
        )

    app.dependency_overrides[files.get_path_validator] = get_path_validator
    app.dependency_overrides[commands.get_job_manager] = get_job_manager
    app.dependency_overrides[commands.get_project_root] = lambda: get_app_state().project_root
    app.dependency_overrides[commands.get_server_port] = get_server_port
    app.dependency_overrides[ws_routes.get_job_manager] = get_job_manager
    app.dependency_overrides[ws_routes.get_project_root] = lambda: get_app_state().project_root
    app.dependency_overrides[prompts.get_path_validator] = get_path_validator

    app.include_router(architecture.router)
    app.include_router(auth.router)
    app.include_router(config_router)
    app.include_router(files.router)
    app.include_router(commands.router)
    app.include_router(prompts.router)

    create_websocket_routes(app, _app_state.connection_manager, _app_state.job_manager)

    # 4. Serve Frontend Static Files
    # Look for frontend dist in the pdd package directory
    frontend_dist = Path(__file__).parent.parent / "frontend" / "dist"
    if frontend_dist.exists():
        console.print(f"[green]Serving frontend from:[/green] {frontend_dist}")

        # Serve static assets (JS, CSS, etc.)
        app.mount("/assets", StaticFiles(directory=frontend_dist / "assets"), name="assets")

        # Serve index.html for the root and any non-API routes (SPA fallback)
        @app.get("/", response_class=HTMLResponse)
        async def serve_frontend():
            index_file = frontend_dist / "index.html"
            if index_file.exists():
                return FileResponse(index_file)
            return HTMLResponse("<h1>Frontend not found</h1>", status_code=404)

        # Catch-all for SPA routing (must be last)
        @app.get("/{path:path}")
        async def serve_spa_fallback(path: str):
            # Don't intercept API, docs, or WebSocket routes
            if path.startswith(("api/", "docs", "redoc", "openapi.json", "ws/")):
                return JSONResponse({"detail": "Not found"}, status_code=404)

            # Try to serve the file directly first
            file_path = frontend_dist / path
            if file_path.exists() and file_path.is_file():
                return FileResponse(file_path)

            # Fall back to index.html for SPA routing
            index_file = frontend_dist / "index.html"
            if index_file.exists():
                return FileResponse(index_file)
            return JSONResponse({"detail": "Not found"}, status_code=404)
    else:
        console.print(f"[yellow]Frontend not found at {frontend_dist}[/yellow]")
        console.print("[yellow]Run 'npm run build' in pdd/frontend to build the frontend[/yellow]")

    return app


# ============================================================================
# Server Runner
# ============================================================================

def run_server(
    project_root: Optional[Path] = None,
    host: str = "127.0.0.1",
    port: int = 9876,
    log_level: str = "info",
    allowed_origins: Optional[List[str]] = None,
    app: Optional[FastAPI] = None,
    config: Optional[ServerConfig] = None
) -> None:
    """
    Run the PDD server using Uvicorn.
    """
    if config:
        final_host = config.host
        final_port = config.port
        final_log_level = config.log_level
    else:
        final_host = host
        final_port = port
        final_log_level = log_level

    if app is None:
        if project_root is None:
            raise ValueError("Must provide either 'app' or 'project_root'.")
        app = create_app(project_root, config=config, allowed_origins=allowed_origins)

    console.print(f"[bold green]PDD Server running on http://{final_host}:{final_port}[/bold green]")
    console.print(f"API Documentation: http://{final_host}:{final_port}/docs")

    uvicorn.run(
        app,
        host=final_host,
        port=final_port,
        log_level=final_log_level,
        access_log=False,
    )