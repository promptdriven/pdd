"""
Pydantic v2 models for the PDD Server REST API.

This module defines the data structures for request and response bodies used
in file operations, command execution, job management, and WebSocket messaging.
"""

from __future__ import annotations

from datetime import datetime, timezone
from enum import Enum
from typing import Any, Dict, List, Literal, Optional, Union

from pydantic import BaseModel, Field, field_validator

__all__ = [
    "FileMetadata",
    "FileTreeNode",
    "FileContent",
    "WriteFileRequest",
    "WriteResult",
    "CommandRequest",
    "JobHandle",
    "JobStatus",
    "JobResult",
    "WSMessage",
    "StdoutMessage",
    "StderrMessage",
    "ProgressMessage",
    "InputRequestMessage",
    "CompleteMessage",
    "FileChangeMessage",
    "ServerStatus",
    "ServerConfig",
    "RemoteSessionInfo",
    "SessionListItem",
]


# ============================================================================
# File Models
# ============================================================================

class FileMetadata(BaseModel):
    """Metadata for a single file or directory."""
    path: str = Field(..., description="Relative path from project root")
    exists: bool = Field(..., description="Whether the file exists on disk")
    size: Optional[int] = Field(None, description="File size in bytes")
    mtime: Optional[datetime] = Field(None, description="Last modification time")
    is_directory: bool = Field(False, description="True if path is a directory")

    @field_validator("path")
    @classmethod
    def validate_path(cls, v: str) -> str:
        if ".." in v:
            raise ValueError("Path traversal ('..') is not allowed")
        return v


class FileTreeNode(BaseModel):
    """Recursive tree structure for file system navigation."""
    name: str = Field(..., description="Base name of the file/directory")
    path: str = Field(..., description="Relative path from project root")
    type: Literal["file", "directory"] = Field(..., description="Node type")
    children: Optional[List[FileTreeNode]] = Field(None, description="Child nodes if directory")
    size: Optional[int] = Field(None, description="File size in bytes")
    mtime: Optional[datetime] = Field(None, description="Last modification time")


class FileContent(BaseModel):
    """Content of a file, potentially encoded."""
    path: str = Field(..., description="Relative path from project root")
    content: str = Field(..., description="File content (text or base64)")
    encoding: Literal["utf-8", "base64"] = Field("utf-8", description="Content encoding")
    size: int = Field(..., description="Size of content in bytes")
    is_binary: bool = Field(False, description="True if content is binary data")
    chunk_index: Optional[int] = Field(None, description="Index if chunked transfer")
    total_chunks: Optional[int] = Field(None, description="Total chunks if chunked transfer")
    checksum: Optional[str] = Field(None, description="SHA-256 checksum of content")


class WriteFileRequest(BaseModel):
    """Request to write content to a file."""
    path: str = Field(..., description="Relative path from project root")
    content: str = Field(..., description="Content to write")
    encoding: Literal["utf-8", "base64"] = Field("utf-8", description="Content encoding")
    create_parents: bool = Field(True, description="Create parent directories if missing")

    @field_validator("path")
    @classmethod
    def validate_path(cls, v: str) -> str:
        if ".." in v:
            raise ValueError("Path traversal ('..') is not allowed")
        return v


class WriteResult(BaseModel):
    """Result of a file write operation."""
    success: bool = Field(..., description="Whether the write succeeded")
    path: str = Field(..., description="Path written to")
    mtime: Optional[datetime] = Field(None, description="New modification time")
    error: Optional[str] = Field(None, description="Error message if failed")


# ============================================================================
# Command & Job Models
# ============================================================================

class CommandRequest(BaseModel):
    """Request to execute a PDD command."""
    command: str = Field(..., description="PDD command name (e.g., 'sync', 'generate')")
    args: Dict[str, Any] = Field(default_factory=dict, description="Positional arguments")
    options: Dict[str, Any] = Field(default_factory=dict, description="Command options/flags")


class JobStatus(str, Enum):
    """Enumeration of possible job statuses."""
    QUEUED = "queued"
    RUNNING = "running"
    COMPLETED = "completed"
    FAILED = "failed"
    CANCELLED = "cancelled"


class JobHandle(BaseModel):
    """Initial response after submitting a command."""
    job_id: str = Field(..., description="Unique identifier for the job")
    status: JobStatus = Field(JobStatus.QUEUED, description="Current status")
    created_at: datetime = Field(default_factory=lambda: datetime.now(timezone.utc), description="Submission timestamp")


class JobResult(BaseModel):
    """Final result of a completed job."""
    job_id: str = Field(..., description="Unique identifier for the job")
    status: JobStatus = Field(..., description="Final status")
    result: Optional[Any] = Field(None, description="Command return value")
    error: Optional[str] = Field(None, description="Error message if failed")
    cost: float = Field(0.0, description="Estimated cost of operation")
    duration_seconds: float = Field(0.0, description="Execution duration")
    completed_at: Optional[datetime] = Field(None, description="Completion timestamp")


# ============================================================================
# WebSocket Message Models
# ============================================================================

class WSMessage(BaseModel):
    """Base model for all WebSocket messages."""
    type: str = Field(..., description="Message type discriminator")
    timestamp: datetime = Field(default_factory=lambda: datetime.now(timezone.utc), description="Message timestamp")
    data: Optional[Any] = Field(None, description="Generic payload")


class StdoutMessage(WSMessage):
    """Message containing standard output from a process."""
    type: Literal["stdout"] = "stdout"
    data: str = Field(..., description="Text content")
    raw: Optional[str] = Field(None, description="Raw content with ANSI codes")


class StderrMessage(WSMessage):
    """Message containing standard error from a process."""
    type: Literal["stderr"] = "stderr"
    data: str = Field(..., description="Text content")
    raw: Optional[str] = Field(None, description="Raw content with ANSI codes")


class ProgressMessage(WSMessage):
    """Message indicating progress of a long-running task."""
    type: Literal["progress"] = "progress"
    current: int = Field(..., description="Current progress value")
    total: int = Field(..., description="Total progress value")
    message: Optional[str] = Field(None, description="Progress description")


class InputRequestMessage(WSMessage):
    """Message requesting input from the client."""
    type: Literal["input_request"] = "input_request"
    prompt: str = Field(..., description="Prompt text to display")
    password: bool = Field(False, description="Whether input should be masked")


class CompleteMessage(WSMessage):
    """Message indicating job completion."""
    type: Literal["complete"] = "complete"
    success: bool = Field(..., description="Whether the job succeeded")
    result: Optional[Dict[str, Any]] = Field(None, description="Result data")
    cost: float = Field(0.0, description="Total cost incurred")


class FileChangeMessage(WSMessage):
    """Message indicating a file system event."""
    type: Literal["file_change"] = "file_change"
    path: str = Field(..., description="Path of the changed file")
    event: Literal["created", "modified", "deleted"] = Field(..., description="Type of change")


# ============================================================================
# Server Configuration Models
# ============================================================================

class ServerStatus(BaseModel):
    """General status information about the server."""
    version: str = Field(..., description="Server version")
    project_root: str = Field(..., description="Absolute path to project root")
    uptime_seconds: float = Field(..., description="Server uptime in seconds")
    active_jobs: int = Field(0, description="Number of currently running jobs")
    connected_clients: int = Field(0, description="Number of active WebSocket connections")


class ServerConfig(BaseModel):
    """Configuration settings for the server instance."""
    host: str = Field("127.0.0.1", description="Bind host")
    port: int = Field(9876, description="Bind port")
    token: Optional[str] = Field(None, description="Authentication token if enabled")
    allow_remote: bool = Field(False, description="Allow remote connections")
    allowed_origins: Optional[List[str]] = Field(None, description="CORS allowed origins")
    log_level: str = Field("info", description="Logging level")


# ============================================================================
# Remote Session Models
# ============================================================================

class RemoteSessionInfo(BaseModel):
    """Information about the current server's remote session registration."""
    session_id: Optional[str] = Field(None, description="Session ID if registered")
    cloud_url: Optional[str] = Field(None, description="Cloud access URL (e.g., https://pdd.dev/connect/{session_id})")
    registered: bool = Field(False, description="Whether session is registered with cloud")
    registered_at: Optional[datetime] = Field(None, description="When session was registered")


class SessionListItem(BaseModel):
    """Session item for list display."""
    session_id: str = Field(..., description="Unique session identifier")
    cloud_url: str = Field(..., description="Cloud access URL for remote access")
    project_name: str = Field(..., description="Project directory name")
    created_at: datetime = Field(..., description="When session was created")
    last_heartbeat: datetime = Field(..., description="Last heartbeat timestamp")
    status: Literal["active", "stale"] = Field(..., description="Session status")
    metadata: Dict[str, Any] = Field(default_factory=dict, description="Additional metadata")