"""
PDD Server Package.

This package provides the REST API server, job management, and command execution
infrastructure for the PDD tool. It enables the web frontend to interact with
the local project environment securely.
"""

from __future__ import annotations

from .app import create_app, run_server
from .executor import execute_pdd_command
from .jobs import Job, JobManager
from .models import ServerConfig, ServerStatus
from .routes.websocket import ConnectionManager
from .security import PathValidator, SecurityError

# Global Constants
DEFAULT_HOST = "127.0.0.1"
DEFAULT_PORT = 9876
API_VERSION = "v1"

__version__ = "0.1.0"

__all__ = [
    # App
    "create_app",
    "run_server",
    
    # Models
    "ServerConfig",
    "ServerStatus",
    
    # Jobs
    "Job",
    "JobManager",
    
    # Security
    "PathValidator",
    "SecurityError",
    
    # Websockets
    "ConnectionManager",
    
    # Executor
    "execute_pdd_command",
    
    # Constants
    "DEFAULT_HOST",
    "DEFAULT_PORT",
    "API_VERSION",
]