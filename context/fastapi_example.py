"""
FastAPI Application Example for PDD Server.

This example demonstrates how to create a FastAPI application with:
- App factory pattern
- CORS middleware
- Route organization
- Pydantic models for request/response
- Dependency injection
- Exception handling

Documentation references:
- FastAPI: https://fastapi.tiangolo.com/
- Pydantic v2: https://docs.pydantic.dev/latest/
- Starlette (underlying ASGI): https://www.starlette.io/
- Uvicorn (ASGI server): https://www.uvicorn.org/
"""

from contextlib import asynccontextmanager
from datetime import datetime
from pathlib import Path
from typing import Optional

from fastapi import FastAPI, HTTPException, Query, Depends
from fastapi.middleware.cors import CORSMiddleware
from pydantic import BaseModel, Field


# ============================================================================
# Pydantic Models (Request/Response)
# ============================================================================

class ServerStatus(BaseModel):
    """Server status response model."""
    version: str
    project_root: str
    uptime_seconds: float
    active_jobs: int = 0


class FileMetadata(BaseModel):
    """File metadata model."""
    path: str
    exists: bool
    size: Optional[int] = None
    mtime: Optional[datetime] = None
    is_directory: bool = False


class FileContent(BaseModel):
    """File content response model."""
    path: str
    content: str
    encoding: str = "utf-8"
    size: int
    is_binary: bool = False


class CommandRequest(BaseModel):
    """Command execution request model."""
    command: str = Field(..., description="PDD command name (e.g., 'sync', 'generate')")
    args: dict = Field(default_factory=dict, description="Positional arguments")
    options: dict = Field(default_factory=dict, description="Command options/flags")


class JobHandle(BaseModel):
    """Job handle returned after command submission."""
    job_id: str
    status: str = "queued"
    created_at: datetime = Field(default_factory=datetime.utcnow)


# ============================================================================
# Application State (Dependency Injection)
# ============================================================================

class AppState:
    """Application state container for dependency injection."""

    def __init__(self, project_root: Path):
        self.project_root = project_root
        self.start_time = datetime.utcnow()
        self.version = "0.1.0"

    @property
    def uptime_seconds(self) -> float:
        return (datetime.utcnow() - self.start_time).total_seconds()


# Global state instance (set during app creation)
_app_state: Optional[AppState] = None


def get_app_state() -> AppState:
    """Dependency to get application state."""
    if _app_state is None:
        raise RuntimeError("Application state not initialized")
    return _app_state


# ============================================================================
# Route Handlers
# ============================================================================

def create_status_router():
    """Create status routes."""
    from fastapi import APIRouter

    router = APIRouter(prefix="/api/v1", tags=["status"])

    @router.get("/status", response_model=ServerStatus)
    async def get_status(state: AppState = Depends(get_app_state)):
        """Get server status."""
        return ServerStatus(
            version=state.version,
            project_root=str(state.project_root),
            uptime_seconds=state.uptime_seconds,
            active_jobs=0,
        )

    return router


def create_files_router():
    """Create file operation routes."""
    from fastapi import APIRouter

    router = APIRouter(prefix="/api/v1/files", tags=["files"])

    @router.get("/content", response_model=FileContent)
    async def get_file_content(
        path: str = Query(..., description="File path relative to project root"),
        state: AppState = Depends(get_app_state),
    ):
        """Read file content."""
        file_path = state.project_root / path

        # Security: Validate path is within project root
        try:
            file_path.resolve().relative_to(state.project_root.resolve())
        except ValueError:
            raise HTTPException(status_code=403, detail="Path traversal not allowed")

        if not file_path.exists():
            raise HTTPException(status_code=404, detail=f"File not found: {path}")

        if not file_path.is_file():
            raise HTTPException(status_code=400, detail=f"Not a file: {path}")

        content = file_path.read_text(encoding="utf-8")
        return FileContent(
            path=path,
            content=content,
            encoding="utf-8",
            size=len(content),
            is_binary=False,
        )

    @router.get("/metadata", response_model=FileMetadata)
    async def get_file_metadata(
        path: str = Query(..., description="File path"),
        state: AppState = Depends(get_app_state),
    ):
        """Get file metadata."""
        file_path = state.project_root / path

        if not file_path.exists():
            return FileMetadata(path=path, exists=False)

        stat = file_path.stat()
        return FileMetadata(
            path=path,
            exists=True,
            size=stat.st_size,
            mtime=datetime.fromtimestamp(stat.st_mtime),
            is_directory=file_path.is_dir(),
        )

    return router


def create_commands_router():
    """Create command execution routes."""
    from fastapi import APIRouter
    import uuid

    router = APIRouter(prefix="/api/v1/commands", tags=["commands"])

    @router.post("/execute", response_model=JobHandle)
    async def execute_command(request: CommandRequest):
        """Submit a command for execution."""
        job_id = str(uuid.uuid4())
        # In real implementation, this would queue the job
        return JobHandle(
            job_id=job_id,
            status="queued",
        )

    @router.get("/jobs/{job_id}")
    async def get_job_status(job_id: str):
        """Get job status."""
        # In real implementation, this would look up the job
        return {"job_id": job_id, "status": "completed"}

    return router


# ============================================================================
# App Factory
# ============================================================================

@asynccontextmanager
async def lifespan(app: FastAPI):
    """Application lifespan manager for startup/shutdown."""
    # Startup
    print(f"Server starting, project root: {_app_state.project_root}")
    yield
    # Shutdown
    print("Server shutting down")


def create_app(project_root: Path, allowed_origins: list[str] = None) -> FastAPI:
    """
    Create and configure the FastAPI application.

    Args:
        project_root: The project directory to serve
        allowed_origins: List of allowed CORS origins

    Returns:
        Configured FastAPI application
    """
    global _app_state
    _app_state = AppState(project_root)

    app = FastAPI(
        title="PDD Server",
        description="Local REST server for PDD web frontend",
        version="0.1.0",
        lifespan=lifespan,
    )

    # Configure CORS
    origins = allowed_origins or [
        "http://localhost:3000",
        "http://127.0.0.1:3000",
        "http://localhost:5173",
        "http://127.0.0.1:5173",
    ]

    app.add_middleware(
        CORSMiddleware,
        allow_origins=origins,
        allow_credentials=True,
        allow_methods=["GET", "POST", "PUT", "DELETE"],
        allow_headers=["*"],
    )

    # Register routes
    app.include_router(create_status_router())
    app.include_router(create_files_router())
    app.include_router(create_commands_router())

    return app


# ============================================================================
# Example Usage
# ============================================================================

def main():
    """
    Example demonstrating how to create and run the FastAPI app.

    In production, this would be called from the `pdd connect` command.
    """
    import uvicorn

    # Create app with current directory as project root
    project_root = Path.cwd()
    app = create_app(project_root)

    print(f"Starting PDD server...")
    print(f"Project root: {project_root}")
    print(f"API docs: http://127.0.0.1:9876/docs")

    # Run with uvicorn
    uvicorn.run(
        app,
        host="127.0.0.1",
        port=9876,
        log_level="info",
    )


if __name__ == "__main__":
    main()
