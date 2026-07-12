"""Bounded process-tree execution for protected signer adapters."""

from __future__ import annotations

import os
import signal
import subprocess
import sys
import time
import uuid
from pathlib import Path


_LINUX_CONTAINMENT = r"""
import ctypes, os, signal, subprocess, sys, time
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
def stop(_signum, _frame):
    if child is not None:
        deadline = time.monotonic() + .4
        while time.monotonic() < deadline:
            pids = descendants(os.getpid()) | {child.pid}
            if not pids: break
            for pid in pids:
                try: os.kill(pid, signal.SIGKILL)
                except ProcessLookupError: pass
            time.sleep(.01)
        try: child.wait(timeout=.1)
        except (subprocess.TimeoutExpired, ChildProcessError): pass
    raise SystemExit(124)
signal.signal(signal.SIGTERM, stop)
child = subprocess.Popen(sys.argv[1:], stdin=subprocess.PIPE, stdout=subprocess.PIPE,
                         stderr=subprocess.PIPE, start_new_session=True)
stdout, stderr = child.communicate(sys.stdin.buffer.read())
sys.stdout.buffer.write(stdout); sys.stderr.buffer.write(stderr)
raise SystemExit(child.returncode)
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
    result = subprocess.run(
        ["ps", "eww", "-axo", "pid=,command="],
        capture_output=True, text=True, check=False,
    )
    text_marker = marker.decode()
    for line in result.stdout.splitlines():
        if text_marker not in line:
            continue
        try:
            found.add(int(line.strip().split(None, 1)[0]))
        except (ValueError, IndexError):
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


def run_signer(
    command: tuple[str, ...], payload: bytes, *, timeout: float
) -> subprocess.CompletedProcess[bytes]:
    """Run a signer in a new process group and reap the complete group on timeout."""
    token = uuid.uuid4().hex
    contained_command = command
    if sys.platform.startswith("linux"):
        contained_command = (sys.executable, "-c", _LINUX_CONTAINMENT, *command)
    process = subprocess.Popen(  # pylint: disable=consider-using-with
        contained_command,
        stdin=subprocess.PIPE,
        stdout=subprocess.PIPE,
        stderr=subprocess.PIPE,
        start_new_session=True,
        env=os.environ | {"PDD_SIGNER_PROCESS_TOKEN": token},
    )
    try:
        stdout, stderr = process.communicate(payload, timeout=timeout)
    except subprocess.TimeoutExpired as exc:
        if sys.platform.startswith("linux"):
            process.terminate()
        else:
            try:
                os.killpg(process.pid, signal.SIGKILL)
            except ProcessLookupError:
                pass
            _terminate_marked(token, process.pid)
        try:
            stdout, stderr = process.communicate(timeout=0.5)
        except subprocess.TimeoutExpired:
            if process.stdout is not None:
                process.stdout.close()
            if process.stderr is not None:
                process.stderr.close()
            process.wait(timeout=0.5)
            stdout, stderr = b"", b""
        raise subprocess.TimeoutExpired(
            command, timeout, output=stdout, stderr=stderr
        ) from exc
    return subprocess.CompletedProcess(command, process.returncode, stdout, stderr)
