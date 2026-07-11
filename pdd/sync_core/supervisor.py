"""Fail-closed OS sandbox and complete process-group supervision."""

from __future__ import annotations

import os
import shutil
import signal
import subprocess
import sys
import tempfile
from pathlib import Path


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
    if sys.platform.startswith("linux") and shutil.which("bwrap"):
        argv = ["bwrap", "--unshare-all", "--die-with-parent", "--new-session",
                "--ro-bind", "/", "/", "--dev", "/dev", "--proc", "/proc"]
        for item in writable_roots:
            resolved = str(item.resolve())
            argv.extend(("--bind", resolved, resolved))
        return [*argv, "--", *command], None
    raise RuntimeError("unsupported sandbox platform or mechanism")


def run_supervised(
    command: list[str], *, cwd: Path, timeout: int, env: dict[str, str],
    writable_roots: tuple[Path, ...],
) -> tuple[subprocess.CompletedProcess[str], bool]:
    """Run inside a supported networkless sandbox and kill the whole process group."""
    # pylint: disable=consider-using-with
    try:
        argv, profile = _sandbox_command(command, writable_roots)
    except RuntimeError as exc:
        return subprocess.CompletedProcess(command, 125, "", str(exc)), False
    process = subprocess.Popen(
        argv, cwd=cwd, stdout=subprocess.PIPE, stderr=subprocess.PIPE, text=True,
        env=env | {"PYTHONDONTWRITEBYTECODE": "1",
                   "TMPDIR": str(writable_roots[0].resolve()),
                   "TEMP": str(writable_roots[0].resolve()),
                   "TMP": str(writable_roots[0].resolve())},
        start_new_session=True,
    )
    timed_out = False
    try:
        stdout, stderr = process.communicate(timeout=timeout)
    except subprocess.TimeoutExpired:
        timed_out = True
        os.killpg(process.pid, signal.SIGKILL)
        stdout, stderr = process.communicate()
    surviving = False
    if not timed_out and os.name != "nt":
        try:
            os.killpg(process.pid, 0)
            surviving = True
            os.killpg(process.pid, signal.SIGKILL)
        except ProcessLookupError:
            pass
    if profile is not None:
        profile.unlink(missing_ok=True)
    return subprocess.CompletedProcess(command, 124 if timed_out else process.returncode,
                                       stdout, stderr), surviving
