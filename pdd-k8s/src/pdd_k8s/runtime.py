"""Thin, auditable wrappers around docker, kind and kubectl.

Every external command is routed through :func:`run` so that failures surface
as structured results instead of exceptions, and so callers can log exactly
what was executed against the user's machine.
"""

from __future__ import annotations

import shutil
import subprocess
from dataclasses import dataclass
from pathlib import Path

DEFAULT_TIMEOUT = 120.0


@dataclass(frozen=True)
class CommandResult:
    """Outcome of one external command invocation."""

    command: list[str]
    returncode: int
    stdout: str
    stderr: str

    @property
    def ok(self) -> bool:
        return self.returncode == 0

    @property
    def display(self) -> str:
        return " ".join(self.command)

    def error_text(self) -> str:
        """Best available human-readable failure text."""
        return (self.stderr.strip() or self.stdout.strip() or f"exit code {self.returncode}")


class ToolMissingError(Exception):
    """Raised when a required CLI is not installed."""

    def __init__(self, tool: str) -> None:
        super().__init__(f"{tool} is not installed or not on PATH.")
        self.tool = tool


def tool_path(tool: str) -> str | None:
    """Absolute path of an external CLI, or None when unavailable."""
    return shutil.which(tool)


def run(
    command: list[str],
    *,
    cwd: Path | None = None,
    timeout: float = DEFAULT_TIMEOUT,
    stdin: str | None = None,
) -> CommandResult:
    """Execute a command, capturing output and never raising on failure.

    A missing binary or a timeout is reported as a non-zero
    :class:`CommandResult` so that callers handle one failure shape.
    """
    try:
        completed = subprocess.run(
            command,
            cwd=str(cwd) if cwd else None,
            input=stdin,
            capture_output=True,
            text=True,
            timeout=timeout,
            check=False,
        )
    except FileNotFoundError:
        return CommandResult(command, 127, "", f"{command[0]} is not installed or not on PATH.")
    except subprocess.TimeoutExpired:
        return CommandResult(command, 124, "", f"{command[0]} did not finish within {timeout:g}s.")
    return CommandResult(command, completed.returncode, completed.stdout, completed.stderr)


def docker_available() -> tuple[bool, str]:
    """Check that the Docker daemon is reachable, not just installed."""
    if tool_path("docker") is None:
        return False, "docker is not installed."
    result = run(["docker", "info", "--format", "{{.ServerVersion}}"], timeout=20)
    if not result.ok:
        return False, "Docker is installed but the daemon is not running."
    return True, f"Docker daemon {result.stdout.strip()} is running."


def kind_clusters() -> list[str]:
    """Names of every kind cluster on this machine."""
    result = run(["kind", "get", "clusters"], timeout=20)
    if not result.ok:
        return []
    return [line.strip() for line in result.stdout.splitlines() if line.strip()]


def kubectl_context_exists(context: str) -> bool:
    """True when kubectl knows about the given context."""
    result = run(["kubectl", "config", "get-contexts", "--output", "name"], timeout=20)
    return result.ok and context in {line.strip() for line in result.stdout.splitlines()}


def kubectl(
    args: list[str],
    *,
    context: str,
    timeout: float = DEFAULT_TIMEOUT,
    stdin: str | None = None,
) -> CommandResult:
    """Run kubectl pinned to one context so other clusters are never touched."""
    return run(["kubectl", "--context", context, *args], timeout=timeout, stdin=stdin)
