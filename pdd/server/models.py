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
    "BudgetExceededMessage",
    "BudgetSettings",
    "BudgetUpdateRequest",
    "SlashCommandResult",
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
    budget_cap: Optional[float] = Field(None, description="Optional total cap (non-issue commands)")
    node_budget: Optional[float] = Field(None, description="Optional per-node budget (pdd-issue)")
    max_total_cap: Optional[float] = Field(None, description="Optional tree-wide ceiling (pdd-issue)")

    @field_validator("budget_cap", "node_budget", "max_total_cap", mode="before")
    @classmethod
    def _coerce_budget_amount(cls, v: Any) -> Optional[float]:
        """Validate initial budget fields with the same rules as
        :class:`BudgetUpdateRequest` so a malformed amount can never enter
        the system through ``POST /commands/execute`` and bypass the
        ``update_budget`` validation gate.
        """
        if v is None:
            return None
        if isinstance(v, bool):
            raise ValueError(f"Invalid budget amount: {v!r}")
        if isinstance(v, str):
            stripped = v.strip().lstrip("$").strip()
            if not stripped:
                raise ValueError("Empty budget amount")
            try:
                value = float(stripped)
            except ValueError as exc:
                raise ValueError(f"Non-numeric budget amount: {v!r}") from exc
        else:
            value = float(v)
        if value != value or value in (float("inf"), float("-inf")):
            raise ValueError(f"Budget amount must be finite: {v!r}")
        if value <= 0:
            raise ValueError(f"Budget amount must be > 0: {v!r}")
        if value > 10000:
            raise ValueError(f"Budget amount {value} exceeds hard ceiling $10000")
        return value


class JobStatus(str, Enum):
    """Enumeration of possible job statuses."""
    QUEUED = "queued"
    RUNNING = "running"
    COMPLETED = "completed"
    FAILED = "failed"
    CANCELLED = "cancelled"
    BUDGET_EXCEEDED = "budget_exceeded"


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


class BudgetExceededMessage(WSMessage):
    """Emitted exactly once when the cost watcher trips the active cap."""
    type: Literal["budget_exceeded"] = "budget_exceeded"
    job_id: str = Field(..., description="Identifier of the job that hit the cap")
    command: str = Field(..., description="Command field of the job (e.g. 'issue', 'bug')")
    spent: float = Field(..., description="Cumulative spend in USD at the moment of crossing")
    effective_cap: float = Field(..., description="Active effective cap at the moment of crossing")
    node_budget: Optional[float] = Field(None, description="Per-node budget if applicable")
    max_total_cap: Optional[float] = Field(None, description="Tree-wide ceiling if applicable")
    node_count: Optional[int] = Field(None, description="Current solving-tree node count")


# ============================================================================
# Budget Control Models
# ============================================================================

class BudgetSettings(BaseModel):
    """Per-job budget settings snapshot.

    ``effective_cap`` is the single USD ceiling the watcher enforces:
    for ``pdd-issue`` (``command == "issue"``), it is
    ``min(node_budget * max(node_count or 1, 1), max_total_cap)`` when both
    are set (the ``node_count or 1`` guard handles ``node_count is None``
    before the tree has expanded); for any other command, it is
    ``budget_cap``. ``None`` for ``effective_cap`` means "no cap".
    """
    command: str = Field(..., description="Job command (e.g. 'issue', 'bug', 'change')")
    node_budget: Optional[float] = Field(None, description="Per-node USD budget for pdd-issue")
    max_total_cap: Optional[float] = Field(None, description="Tree-wide USD ceiling for pdd-issue")
    budget_cap: Optional[float] = Field(None, description="Total USD cap for non-issue commands")
    effective_cap: Optional[float] = Field(None, description="Computed effective cap; None means no cap")
    spent_so_far: float = Field(0.0, description="Cumulative spend in USD")
    status: JobStatus = Field(JobStatus.RUNNING, description="Current job status")
    node_count: Optional[int] = Field(None, description="Current solving-tree node count")


class BudgetUpdateRequest(BaseModel):
    """Request body for POST /commands/jobs/{job_id}/budget.

    At least one of ``budget_cap`` / ``node_budget`` / ``max_total_cap`` MUST
    be provided. Each numeric field is validated ``> 0`` and ``<= 10000``;
    string forms (``"$30"``, ``"30.00"``, ``"30"``) are coerced to ``float``.
    """
    budget_cap: Optional[float] = Field(None, description="Total cap for non-issue commands")
    node_budget: Optional[float] = Field(None, description="Per-node budget for pdd-issue")
    max_total_cap: Optional[float] = Field(None, description="Tree-wide ceiling for pdd-issue")

    @field_validator("budget_cap", "node_budget", "max_total_cap", mode="before")
    @classmethod
    def _coerce_amount(cls, v: Any) -> Optional[float]:
        if v is None:
            return None
        if isinstance(v, bool):
            raise ValueError(f"Invalid budget amount: {v!r}")
        if isinstance(v, str):
            stripped = v.strip().lstrip("$").strip()
            if not stripped:
                raise ValueError("Empty budget amount")
            try:
                value = float(stripped)
            except ValueError as exc:
                raise ValueError(f"Non-numeric budget amount: {v!r}") from exc
        else:
            value = float(v)
        if value != value or value in (float("inf"), float("-inf")):
            raise ValueError(f"Budget amount must be finite: {v!r}")
        if value <= 0:
            raise ValueError(f"Budget amount must be > 0: {v!r}")
        if value > 10000:
            raise ValueError(f"Budget amount {value} exceeds hard ceiling $10000")
        return value

    @field_validator("max_total_cap")
    @classmethod
    def _at_least_one(cls, v: Optional[float], info: Any) -> Optional[float]:
        # Pydantic v2: this validator runs last on max_total_cap; check the
        # combined dict to enforce "at least one set".
        data = info.data if hasattr(info, "data") else {}
        if v is None and data.get("budget_cap") is None and data.get("node_budget") is None:
            raise ValueError(
                "At least one of budget_cap, node_budget, or max_total_cap must be set"
            )
        return v


class SlashCommandResult(BaseModel):
    """Result returned by ``slash_command_parser.parse_comment``.

    The ``metadata`` field is a concrete ``Dict[str, Any]`` (never ``None``)
    so callers can rely on ``result.metadata.get("amount")`` without
    extra ``None`` checks. The parser sets ``metadata["amount"]`` for
    budget-mutating kinds (``budget_set`` / ``budget_node_set`` /
    ``budget_max_set``) and leaves it empty for the rest.
    """
    kind: Literal[
        "budget_set",
        "budget_node_set",
        "budget_max_set",
        "settings",
        "stop",
        "invalid",
        "ignored",
    ] = Field(..., description="Parsed verb classification")
    message: str = Field("", description="Pre-rendered reply body (caller may render via budget_comments)")
    settings: Optional[BudgetSettings] = Field(None, description="Optional snapshot, e.g. for an ack echo")
    original_comment_id: Optional[int] = Field(None, description="GitHub comment id for dedupe")
    metadata: Dict[str, Any] = Field(default_factory=dict, description="Per-kind data, e.g. {'amount': 30.0}")


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