from __future__ import annotations

import fnmatch
import time
from pathlib import Path
from typing import Callable, List, Optional, Union

from fastapi import FastAPI, HTTPException, Request, status, Depends
from fastapi.middleware.cors import CORSMiddleware
from fastapi.security import HTTPBearer, HTTPAuthorizationCredentials
from starlette.middleware.base import BaseHTTPMiddleware
from rich.console import Console

# Initialize Rich console for logging
console = Console()

# Default blacklist patterns
DEFAULT_BLACKLIST = [
    ".git", ".git/**",
    ".env", ".env.*",
    "node_modules", "node_modules/**",
    "__pycache__", "*.pyc",
    ".DS_Store",
    "credentials*", "*secret*", "*.key", "*.pem",
    "id_rsa*",
]

class SecurityError(Exception):
    """
    Custom exception for security violations.
    """
    def __init__(self, code: str, message: str):
        self.code = code
        self.message = message
        super().__init__(message)


class PathValidator:
    """
    Validates filesystem paths to prevent directory traversal and access to sensitive files.
    """

    def __init__(self, project_root: Path, blacklist_patterns: Optional[List[str]] = None):
        """
        Initialize the validator.

        Args:
            project_root: The absolute root directory of the project.
            blacklist_patterns: Optional list of glob patterns to block.
                                If None, uses DEFAULT_BLACKLIST.
        """
        self.project_root = project_root.resolve()
        self.blacklist = blacklist_patterns if blacklist_patterns is not None else DEFAULT_BLACKLIST

    def validate(self, path: Union[str, Path]) -> Path:
        """
        Resolve and validate that a path is safe to access.

        Args:
            path: The relative or absolute path to validate.

        Returns:
            Path: The resolved, absolute path.

        Raises:
            SecurityError: If the path is invalid, blocked, or traverses outside root.
        """
        try:
            # 1. Construct the full candidate path
            path_obj = Path(path)
            
            if path_obj.is_absolute():
                # If absolute, we must ensure it starts with project_root before resolving
                # to catch simple string mismatches, but the real check is relative_to below.
                candidate_path = path_obj
            else:
                # If relative, join with project root
                candidate_path = self.project_root / path_obj

            # 2. Resolve symlinks and '..' components
            # strict=False allows validating paths for files that don't exist yet (e.g. for writing)
            resolved_path = candidate_path.resolve()

            # 3. Check for Directory Traversal
            # This raises ValueError if resolved_path is not inside project_root
            try:
                relative_path = resolved_path.relative_to(self.project_root)
            except ValueError:
                console.print(f"[bold red]Security Alert:[/bold red] Path traversal attempt: {path}")
                raise SecurityError(
                    code="PATH_TRAVERSAL",
                    message="Access denied: Path is outside the project root."
                )

            # 4. Check Blacklist
            # We check the relative path parts against patterns
            path_str = str(relative_path)
            parts = relative_path.parts

            for pattern in self.blacklist:
                # Check the full relative path string
                if fnmatch.fnmatch(path_str, pattern):
                    self._raise_blacklist_error(path_str, pattern)
                
                # Check individual path components (e.g., blocking 'node_modules' anywhere in tree)
                # This handles cases like 'src/node_modules/foo' matching 'node_modules'
                for part in parts:
                    if fnmatch.fnmatch(part, pattern):
                        self._raise_blacklist_error(path_str, pattern)

            return resolved_path

        except SecurityError:
            raise
        except Exception as e:
            console.print(f"[bold red]Error:[/bold red] Invalid path processing: {e}")
            raise SecurityError(code="INVALID_PATH", message=f"Invalid path: {str(e)}")

    def _raise_blacklist_error(self, path: str, pattern: str):
        console.print(f"[bold red]Security Alert:[/bold red] Blocked access to blacklisted resource: {path} (matched {pattern})")
        raise SecurityError(
            code="BLACKLISTED_PATH",
            message="Access denied: Resource is blacklisted."
        )


def configure_cors(app: FastAPI, allowed_origins: Optional[List[str]] = None) -> None:
    """
    Configure CORS middleware for the FastAPI application.

    Args:
        app: The FastAPI application instance.
        allowed_origins: List of allowed origins. Defaults to standard local dev ports.
    """
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
        allow_methods=["*"],
        allow_headers=["*"],
        expose_headers=["X-Job-Id", "X-Total-Chunks"],
    )
    console.print(f"[green]CORS configured for origins:[/green] {origins}")


def create_token_dependency(token: Optional[str]) -> Callable:
    """
    Creates a FastAPI dependency for Bearer token authentication.

    Args:
        token: The expected secret token. If None, authentication is disabled.

    Returns:
        A dependency function to be used with Depends().
    """
    security = HTTPBearer(auto_error=False)

    async def verify_token(credentials: Optional[HTTPAuthorizationCredentials] = Depends(security)):
        if token is None:
            return None
        
        if not credentials:
            raise HTTPException(
                status_code=status.HTTP_401_UNAUTHORIZED,
                detail="Missing authentication credentials",
                headers={"WWW-Authenticate": "Bearer"},
            )
        
        if credentials.credentials != token:
            console.print("[bold red]Auth Failed:[/bold red] Invalid token provided.")
            raise HTTPException(
                status_code=status.HTTP_401_UNAUTHORIZED,
                detail="Invalid authentication token",
                headers={"WWW-Authenticate": "Bearer"},
            )
        
        return credentials

    return verify_token


class SecurityLoggingMiddleware(BaseHTTPMiddleware):
    """
    Middleware to log requests and provide basic request validation/monitoring.
    """

    # Endpoints that are polled frequently and should be quiet
    QUIET_ENDPOINTS = [
        "/api/v1/commands/jobs/",  # Job status polling
        "/api/v1/commands/spawned-jobs/",  # Spawned job status polling
        "/api/v1/prompts",  # Prompt listing
        "/api/v1/status",  # Health checks
        "/api/v1/auth/jwt-token",  # JWT token polling
        "/api/v1/auth/status",  # Auth status
        "/api/v1/files/",  # File operations
        "/api/v1/config/",  # Config endpoints
        "/assets/",  # Static assets
    ]

    # Also skip root and static files
    QUIET_EXACT = ["/", "/index.html", "/favicon.ico"]

    def _should_log(self, path: str) -> bool:
        """Check if we should log this request (skip noisy polling endpoints)."""
        # Check exact matches first
        if path in self.QUIET_EXACT:
            return False
        # Check prefix/substring matches
        for quiet_path in self.QUIET_ENDPOINTS:
            if quiet_path in path:
                return False
        return True

    async def dispatch(self, request: Request, call_next):
        start_time = time.time()
        client_host = request.client.host if request.client else "unknown"
        path = request.url.path
        should_log = self._should_log(path)

        # Log incoming request (skip noisy polling endpoints)
        if should_log:
            console.print(f"[dim]Request:[/dim] {request.method} {path} [dim]from {client_host}[/dim]")

        response = await call_next(request)

        process_time = (time.time() - start_time) * 1000

        # Log response (skip noisy endpoints, but always log errors)
        if should_log or response.status_code >= 400:
            status_color = "green" if response.status_code < 400 else "red"
            console.print(
                f"[dim]Response:[/dim] [{status_color}]{response.status_code}[/{status_color}] "
                f"took {process_time:.2f}ms"
            )

        return response