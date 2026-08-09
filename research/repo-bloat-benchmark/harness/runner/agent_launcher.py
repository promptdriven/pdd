"""First-class agent launch paths for command-arm runs.

The default launcher executes the agent as a local subprocess. The container
hard tier uses a shared-filesystem worker protocol instead: the runner writes
one launch request into a directory visible to the isolated ``agent``
container, the worker executes it there, and the runner waits for the result.
That keeps the actual Codex process inside the agent namespace without
requiring Docker socket access from the runner.
"""

from __future__ import annotations

import json
import os
import subprocess
import time
import uuid
from dataclasses import dataclass
from pathlib import Path


class AgentLaunchError(RuntimeError):
    """The configured launch path could not execute the request."""


@dataclass(frozen=True)
class AgentLaunchResult:
    command: list[str]
    returncode: int | None
    stdout: str | None
    stderr: str | None
    timed_out: bool
    launcher: str


def _write_json_atomic(path: Path, payload: dict) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    temp_path = path.with_suffix(path.suffix + ".tmp")
    temp_path.write_text(json.dumps(payload, indent=2) + "\n", encoding="utf-8")
    temp_path.replace(path)


def launch_local_subprocess(
    *,
    command: list[str],
    cwd: Path,
    env: dict[str, str],
    timeout_seconds: float,
) -> AgentLaunchResult:
    try:
        completed = subprocess.run(
            command,
            cwd=str(cwd),
            env=env,
            capture_output=True,
            text=True,
            timeout=timeout_seconds,
        )
        return AgentLaunchResult(
            command=command,
            returncode=completed.returncode,
            stdout=completed.stdout,
            stderr=completed.stderr,
            timed_out=False,
            launcher="local",
        )
    except subprocess.TimeoutExpired as exc:
        return AgentLaunchResult(
            command=command,
            returncode=None,
            stdout=exc.stdout,
            stderr=exc.stderr,
            timed_out=True,
            launcher="local",
        )


class FileAgentLauncher:
    """Dispatch command-arm runs to an isolated worker via shared files."""

    def __init__(self, request_dir: str | Path, poll_interval_seconds: float = 0.1) -> None:
        self.request_dir = Path(request_dir)
        self.poll_interval_seconds = poll_interval_seconds
        self.requests_dir = self.request_dir / "requests"
        self.results_dir = self.request_dir / "results"

    def launch(
        self,
        *,
        run_id: str,
        command: list[str],
        cwd: Path,
        env: dict[str, str],
        timeout_seconds: float,
    ) -> AgentLaunchResult:
        request_id = f"{run_id}.{uuid.uuid4().hex}"
        request_path = self.requests_dir / f"{request_id}.json"
        result_path = self.results_dir / f"{request_id}.json"
        deadline = time.monotonic() + timeout_seconds + 30.0
        payload = {
            "request_id": request_id,
            "run_id": run_id,
            "command": command,
            "cwd": str(cwd),
            "env": env,
            "timeout_seconds": timeout_seconds,
        }
        _write_json_atomic(request_path, payload)
        try:
            while time.monotonic() < deadline:
                if result_path.is_file():
                    data = json.loads(result_path.read_text(encoding="utf-8"))
                    return AgentLaunchResult(
                        command=list(data["command"]),
                        returncode=data.get("returncode"),
                        stdout=data.get("stdout"),
                        stderr=data.get("stderr"),
                        timed_out=bool(data.get("timed_out")),
                        launcher="container_worker",
                    )
                time.sleep(self.poll_interval_seconds)
        finally:
            if request_path.exists():
                request_path.unlink()
        raise AgentLaunchError(
            f"timed out waiting for isolated-agent result: {result_path}"
        )


def run_worker_loop(
    request_dir: str | Path,
    *,
    poll_interval_seconds: float = 0.1,
    once: bool = False,
) -> int:
    """Run the isolated-agent worker loop.

    The agent container keeps this loop running; tests may use ``once=True`` to
    process one queued request synchronously.
    """
    root = Path(request_dir)
    requests_dir = root / "requests"
    claims_dir = root / "claims"
    results_dir = root / "results"
    requests_dir.mkdir(parents=True, exist_ok=True)
    claims_dir.mkdir(parents=True, exist_ok=True)
    results_dir.mkdir(parents=True, exist_ok=True)

    processed = 0
    while True:
        claimed_path: Path | None = None
        for request_path in sorted(requests_dir.glob("*.json")):
            candidate = claims_dir / request_path.name
            try:
                request_path.replace(candidate)
            except FileNotFoundError:
                continue
            claimed_path = candidate
            break
        if claimed_path is None:
            if once and processed:
                return processed
            if once:
                time.sleep(poll_interval_seconds)
                continue
            time.sleep(poll_interval_seconds)
            continue

        request = json.loads(claimed_path.read_text(encoding="utf-8"))
        result = {
            "command": request["command"],
            "returncode": None,
            "stdout": None,
            "stderr": None,
            "timed_out": False,
            "worker_pid": os.getpid(),
        }
        try:
            completed = subprocess.run(
                list(request["command"]),
                cwd=request["cwd"],
                env=request["env"],
                capture_output=True,
                text=True,
                timeout=float(request["timeout_seconds"]),
            )
            result.update(
                {
                    "returncode": completed.returncode,
                    "stdout": completed.stdout,
                    "stderr": completed.stderr,
                }
            )
        except subprocess.TimeoutExpired as exc:
            result.update(
                {
                    "stdout": exc.stdout,
                    "stderr": exc.stderr,
                    "timed_out": True,
                }
            )
        finally:
            _write_json_atomic(results_dir / claimed_path.name, result)
            claimed_path.unlink(missing_ok=True)
        processed += 1
        if once:
            return processed
