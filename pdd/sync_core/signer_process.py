"""Bounded process-tree execution for protected signer adapters."""

from __future__ import annotations

import os
import shutil
import signal
import subprocess
import sys
import tempfile
import time
import uuid
from pathlib import Path


_LINUX_CONTAINMENT = r"""
import ctypes, os, pathlib, signal, subprocess, sys, time
ctypes.CDLL(None, use_errno=True).prctl(36, 1, 0, 0, 0)
child = None
def descendants(root):
    children = {}
    for name in os.listdir('/proc'):
        if not name.isdigit(): continue
        try:
            fields = open('/proc/' + name + '/stat').read().rsplit(')', 1)[1].split()
            children.setdefault(int(fields[1]), set()).add(int(name))
        except (OSError, ValueError, IndexError): pass
    found, pending = set(), [root]
    while pending:
        for pid in children.get(pending.pop(), ()):
            if pid not in found: found.add(pid); pending.append(pid)
    return found
def cleanup():
    deadline = time.monotonic() + .4
    while time.monotonic() < deadline:
        pids = descendants(os.getpid())
        if child is not None and child.poll() is None: pids.add(child.pid)
        if not pids: return
        for pid in pids:
            try: os.kill(pid, signal.SIGKILL)
            except ProcessLookupError: pass
        time.sleep(.01)
def stop(_signum, _frame):
    cleanup()
    raise SystemExit(124)
signal.signal(signal.SIGTERM, stop)
ready_path = os.environ.pop('PDD_SIGNER_READY_PATH', '')
child = subprocess.Popen(sys.argv[1:], stdin=subprocess.PIPE, stdout=subprocess.PIPE,
                         stderr=subprocess.PIPE, start_new_session=True)
if ready_path:
    pathlib.Path(ready_path).touch(exist_ok=False)
try:
    stdout, stderr = child.communicate(sys.stdin.buffer.read())
    sys.stdout.buffer.write(stdout); sys.stderr.buffer.write(stderr)
    status = child.returncode
finally:
    cleanup()
raise SystemExit(status)
"""


def _marked_processes(token: str) -> set[int]:
    """Return signer descendants carrying the per-call inherited marker."""
    marker = f"PDD_SIGNER_PROCESS_TOKEN={token}".encode()
    found: set[int] = set()
    if sys.platform.startswith("linux"):
        entries = Path("/proc").iterdir()
        for entry in entries:
            if not entry.name.isdigit():
                continue
            try:
                values = (entry / "environ").read_bytes().split(b"\0")
            except (OSError, PermissionError):
                continue
            if marker in values:
                found.add(int(entry.name))
        return found
    result = subprocess.run(["ps", "eww", "-axo", "pid=,command="],
                            capture_output=True, text=True, check=False)
    text_marker = marker.decode()
    for line in result.stdout.splitlines():
        raw_pid, _separator, command_line = line.strip().partition(" ")
        if text_marker not in command_line:
            continue
        try:
            found.add(int(raw_pid))
        except ValueError:
            continue
    return found


def _terminate_marked(token: str, leader: int, timeout: float = 0.5) -> None:
    """Kill marked descendants across process groups within a fixed bound."""
    deadline = time.monotonic() + timeout
    while time.monotonic() < deadline:
        pids = _marked_processes(token) - {os.getpid()}
        if not pids:
            return
        for pid in pids:
            try:
                os.kill(pid, signal.SIGKILL)
            except ProcessLookupError:
                pass
        time.sleep(0.01)
    try:
        os.kill(leader, signal.SIGKILL)
    except ProcessLookupError:
        pass


def _linux_contained_command(command: tuple[str, ...]) -> tuple[str, ...]:
    """Place the signer behind a PID namespace whose init owns all descendants."""
    bwrap = shutil.which("bwrap")
    if bwrap is None:
        raise RuntimeError("protected Linux signer requires bubblewrap PID containment")
    sudo = shutil.which("sudo")
    elevated = bool(sudo) and subprocess.run(
        [sudo, "-n", "true"], capture_output=True, check=False
    ).returncode == 0
    prefix = (sudo, "-n", "-E") if elevated and sudo is not None else ()
    return (*prefix,
        bwrap, "--unshare-pid", "--die-with-parent", "--new-session",
        "--ro-bind", "/", "/", "--proc", "/proc", "--dev", "/dev",
        "--tmpfs", "/tmp", "--", sys.executable, "-c", _LINUX_CONTAINMENT,
        *command,
    )


def _kill_bounded(process: subprocess.Popen[bytes], token: str) -> None:
    """Hard-kill the containment leader and inherited escapees within a bound."""
    try:
        os.killpg(process.pid, signal.SIGKILL)
    except ProcessLookupError:
        pass
    _terminate_marked(token, process.pid)
    try:
        process.wait(timeout=0.5)
    except subprocess.TimeoutExpired:
        process.kill()
        process.wait(timeout=0.5)


def _wait_for_signer_start(
    process: subprocess.Popen[bytes], ready_path: Path, command: tuple[str, ...],
    timeout: float, token: str,
) -> None:
    """Wait briefly for the containment init to launch the signer child."""
    deadline = time.monotonic() + 0.5
    while not ready_path.exists():
        if process.poll() is not None or time.monotonic() >= deadline:
            _kill_bounded(process, token)
            raise subprocess.TimeoutExpired(command, timeout)
        time.sleep(0.005)


def run_signer(
    command: tuple[str, ...], payload: bytes, *, timeout: float
) -> subprocess.CompletedProcess[bytes]:
    """Run a signer in a new process group and reap the complete group on timeout."""
    token = uuid.uuid4().hex
    contained_command = (
        _linux_contained_command(command) if sys.platform.startswith("linux") else command
    )
    # The Linux signer scope replaces /tmp, so keep the checker-owned marker
    # under its home directory, which the signer PID namespace bind-mounts.
    with tempfile.TemporaryDirectory(prefix="pdd-signer-", dir=Path.home()) as directory:
        ready_path = Path(directory) / "started"
        environment = os.environ | {"PDD_SIGNER_PROCESS_TOKEN": token}
        if sys.platform.startswith("linux"):
            environment["PDD_SIGNER_READY_PATH"] = str(ready_path)
        process = subprocess.Popen(  # pylint: disable=consider-using-with
            contained_command,
            stdin=subprocess.PIPE,
            stdout=subprocess.PIPE,
            stderr=subprocess.PIPE,
            start_new_session=True,
            env=environment,
        )
        try:
            if process.stdin is not None:
                process.stdin.write(payload)
                process.stdin.close()
                process.stdin = None
        except BrokenPipeError:
            pass
        if sys.platform.startswith("linux"):
            _wait_for_signer_start(process, ready_path, command, timeout, token)
        try:
            stdout, stderr = process.communicate(timeout=timeout)
        except subprocess.TimeoutExpired as exc:
            if sys.platform.startswith("linux"):
                process.terminate()
                try:
                    stdout, stderr = process.communicate(timeout=0.4)
                except subprocess.TimeoutExpired:
                    _kill_bounded(process, token)
                    stdout, stderr = b"", b""
            else:
                _kill_bounded(process, token)
                stdout, stderr = b"", b""
            raise subprocess.TimeoutExpired(
                command, timeout, output=stdout, stderr=stderr
            ) from exc
    return subprocess.CompletedProcess(command, process.returncode, stdout, stderr)
