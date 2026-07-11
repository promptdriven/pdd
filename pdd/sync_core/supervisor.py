"""Fail-closed OS sandbox and complete process-group supervision."""

from __future__ import annotations

import os
import shutil
import signal
import subprocess
import sys
import tempfile
import threading
import time
import uuid
from pathlib import Path


def _supervised_descendants(token: str) -> set[int]:
    """Find descendants carrying the unforgeable per-run environment marker."""
    found: set[int] = set()
    if sys.platform.startswith("linux"):
        for entry in Path("/proc").iterdir():
            if not entry.name.isdigit():
                continue
            try:
                environment = (entry / "environ").read_bytes()
            except (OSError, PermissionError):
                continue
            if f"PDD_SUPERVISION_TOKEN={token}".encode() in environment.split(b"\0"):
                found.add(int(entry.name))
        return found
    listing = subprocess.run(
        ["ps", "eww", "-axo", "pid=,command="], capture_output=True,
        text=True, check=False,
    )
    marker = f"PDD_SUPERVISION_TOKEN={token}"
    for line in listing.stdout.splitlines():
        if marker not in line:
            continue
        try:
            found.add(int(line.strip().split(None, 1)[0]))
        except (ValueError, IndexError):
            continue
    return found


def _process_descendants(root_pid: int) -> set[int]:
    """Return the current transitive process tree without trusting child state."""
    listing = subprocess.run(
        ["ps", "-axo", "pid=,ppid="], capture_output=True, text=True, check=False,
    )
    children: dict[int, set[int]] = {}
    for line in listing.stdout.splitlines():
        try:
            pid, parent = (int(value) for value in line.split())
        except (ValueError, TypeError):
            continue
        children.setdefault(parent, set()).add(pid)
    found: set[int] = set()
    pending = [root_pid]
    while pending:
        parent = pending.pop()
        for child in children.get(parent, ()):
            if child not in found:
                found.add(child)
                pending.append(child)
    return found


def _live_processes(pids: set[int]) -> set[int]:
    """Filter historical observations to processes that still exist."""
    live = set()
    for pid in pids:
        try:
            os.kill(pid, 0)
        except (ProcessLookupError, PermissionError):
            continue
        live.add(pid)
    return live


def _sandbox_command(
    command: list[str], writable_roots: tuple[Path, ...]
) -> tuple[list[str], Path | None]:
    """Return an explicitly detected macOS/Linux sandbox command."""
    if sys.platform == "darwin" and shutil.which("sandbox-exec"):
        rules = ["(version 1)", "(allow default)", "(deny network*)", "(deny file-write*)",
                 '(allow file-write* (literal "/dev/null"))']
        for item in writable_roots:
            rules.append(f'(allow file-write* (subpath "{item.resolve()}"))')
        descriptor, name = tempfile.mkstemp(prefix="pdd-sandbox-", suffix=".sb")
        os.close(descriptor)
        profile = Path(name)
        profile.write_text("\n".join(rules), encoding="utf-8")
        return ["sandbox-exec", "-f", str(profile), *command], profile
    if (sys.platform.startswith("linux") and shutil.which("bwrap")
            and shutil.which("unshare")):
        # util-linux creates the network namespace but does not configure its
        # loopback device, avoiding the RTM_NEWADDR operation denied by hosted
        # GitHub runners. Bubblewrap supplies the mount and PID containment.
        argv = ["unshare", "--user", "--map-root-user", "--net", "--",
                "bwrap", "--unshare-pid", "--unshare-ipc", "--unshare-uts",
                "--die-with-parent", "--new-session", "--ro-bind", "/", "/",
                "--dev", "/dev", "--proc", "/proc"]
        for item in writable_roots:
            resolved = str(item.resolve())
            argv.extend(("--bind", resolved, resolved))
        return [*argv, "--", *command], None
    raise RuntimeError("unsupported sandbox platform or mechanism")


def run_supervised(
    command: list[str], *, cwd: Path, timeout: int, env: dict[str, str],
    writable_roots: tuple[Path, ...],
) -> tuple[subprocess.CompletedProcess[str], bool]:
    """Run sandboxed and terminate marked descendants across session changes."""
    # pylint: disable=consider-using-with,too-many-locals,too-many-branches,too-many-statements
    try:
        argv, profile = _sandbox_command(command, writable_roots)
    except RuntimeError as exc:
        return subprocess.CompletedProcess(command, 125, "", str(exc)), False
    token = uuid.uuid4().hex
    process = subprocess.Popen(
        argv, cwd=cwd, stdout=subprocess.PIPE, stderr=subprocess.PIPE, text=True,
        env=env | {"PYTHONDONTWRITEBYTECODE": "1",
                   "PDD_SUPERVISION_TOKEN": token,
                   "TMPDIR": str(writable_roots[0].resolve()),
                   "TEMP": str(writable_roots[0].resolve()),
                   "TMP": str(writable_roots[0].resolve())},
        start_new_session=True,
    )
    timed_out = False
    surviving = False
    tracked: set[int] = set()
    tracking_done = threading.Event()

    def track_process_tree() -> None:
        while not tracking_done.wait(0.005):
            tracked.update(_process_descendants(process.pid))

    tracker = threading.Thread(target=track_process_tree, daemon=True)
    tracker.start()
    deadline = time.monotonic() + timeout
    while True:
        try:
            stdout, stderr = process.communicate(
                timeout=max(0.01, min(0.1, deadline - time.monotonic()))
            )
            break
        except subprocess.TimeoutExpired:
            descendants = _supervised_descendants(token) - {process.pid}
            if process.poll() is not None and descendants:
                surviving = True
                for pid in descendants:
                    try:
                        os.kill(pid, signal.SIGKILL)
                    except ProcessLookupError:
                        pass
            if time.monotonic() >= deadline:
                timed_out = True
                try:
                    os.killpg(process.pid, signal.SIGKILL)
                except ProcessLookupError:
                    pass
                for pid in _supervised_descendants(token) - {process.pid}:
                    try:
                        os.kill(pid, signal.SIGKILL)
                    except ProcessLookupError:
                        pass
                stdout, stderr = process.communicate()
                break
    tracking_done.set()
    tracker.join(timeout=1)
    if not timed_out and os.name != "nt":
        try:
            os.killpg(process.pid, 0)
            surviving = True
            os.killpg(process.pid, signal.SIGKILL)
        except ProcessLookupError:
            pass
    descendants = _live_processes(
        (_supervised_descendants(token) | tracked) - {process.pid}
    )
    if descendants:
        surviving = True
        for pid in descendants:
            try:
                os.kill(pid, signal.SIGKILL)
            except ProcessLookupError:
                pass
    if profile is not None:
        profile.unlink(missing_ok=True)
    return subprocess.CompletedProcess(command, 124 if timed_out else process.returncode,
                                       stdout, stderr), surviving
