"""Bounded process-tree execution for protected signer adapters."""

from __future__ import annotations

import os
import signal
import subprocess


def run_signer(
    command: tuple[str, ...], payload: bytes, *, timeout: float
) -> subprocess.CompletedProcess[bytes]:
    """Run a signer in a new process group and reap the complete group on timeout."""
    process = subprocess.Popen(  # pylint: disable=consider-using-with
        command,
        stdin=subprocess.PIPE,
        stdout=subprocess.PIPE,
        stderr=subprocess.PIPE,
        start_new_session=True,
    )
    try:
        stdout, stderr = process.communicate(payload, timeout=timeout)
    except subprocess.TimeoutExpired as exc:
        try:
            os.killpg(process.pid, signal.SIGKILL)
        except ProcessLookupError:
            pass
        stdout, stderr = process.communicate()
        raise subprocess.TimeoutExpired(
            command, timeout, output=stdout, stderr=stderr
        ) from exc
    return subprocess.CompletedProcess(command, process.returncode, stdout, stderr)
