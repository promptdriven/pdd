"""Fail-closed OS sandbox and complete process-group supervision."""
# pylint: disable=too-many-arguments

from __future__ import annotations

import os
import json
import shutil
import signal
import subprocess
import sys
import tempfile
import threading
import time
import uuid
from dataclasses import dataclass
from pathlib import Path


@dataclass(frozen=True)
class SupervisorLimits:
    """Hard limits applied to every untrusted validator process tree."""

    max_output_bytes: int = 16 * 1024 * 1024
    max_writable_bytes: int = 512 * 1024 * 1024
    max_memory_bytes: int = 2 * 1024 * 1024 * 1024
    max_cpu_seconds: int = 300
    max_processes: int = 128


def _runtime_roots(command: list[str], cwd: Path) -> tuple[Path, ...]:
    """Return the minimal host trees needed to start the configured interpreter."""
    roots = {cwd.resolve(), Path(sys.prefix).resolve()}
    executable = shutil.which(command[0]) or command[0]
    roots.add(Path(executable).resolve().parent)
    for candidate in ("/bin", "/usr", "/lib", "/lib64"):
        path = Path(candidate)
        if path.exists():
            roots.add(path.resolve())
    return tuple(sorted(roots, key=lambda item: (len(item.parts), str(item))))


def _limited_command(command: list[str], limits: SupervisorLimits) -> list[str]:
    """Apply non-raiseable POSIX limits after the namespace uid drop."""
    script = (
        "import os,resource,sys;"
        "v=[int(x) for x in sys.argv[1:6]];"
        "resource.setrlimit(resource.RLIMIT_AS,(v[0],v[0]));"
        "resource.setrlimit(resource.RLIMIT_CPU,(v[1],v[1]));"
        "resource.setrlimit(resource.RLIMIT_NPROC,(v[2],v[2]));"
        "resource.setrlimit(resource.RLIMIT_FSIZE,(v[3],v[3]));"
        "resource.setrlimit(resource.RLIMIT_NOFILE,(v[4],v[4]));"
        "os.execvpe(sys.argv[6],sys.argv[6:],os.environ)"
    )
    return [sys.executable, "-c", script, str(limits.max_memory_bytes),
            str(limits.max_cpu_seconds), str(limits.max_processes),
            str(limits.max_writable_bytes), "256", *command]


def _staged_bwrap(argv: list[str], sources: list[Path]) -> list[str]:
    """Stage exact bind mounts before replacing the namespace root."""
    helper = "\n".join((
        "import json,os,pathlib,shutil,subprocess,sys,tempfile",
        "argv=json.loads(sys.argv[1]); paths=json.loads(sys.argv[2])",
        "base=pathlib.Path(tempfile.mkdtemp(prefix='pdd-binds-',dir='/run'))",
        "os.chmod(base,0o755); staged=[]",
        "try:",
        " for index,source in enumerate(paths):",
        "  source=pathlib.Path(source); target=base/str(index)",
        "  target.mkdir() if source.is_dir() else target.touch()",
        "  subprocess.run(['mount','--bind',str(source),str(target)],check=True)",
        "  staged.append(target)",
        " argv=[str(staged[int(x[4:-1])]) if x.startswith('@FD:') else x for x in argv]",
        " result=subprocess.run(argv,check=False)",
        "finally:",
        " for target in reversed(staged):",
        "  subprocess.run(['umount',str(target)],check=False)",
        " shutil.rmtree(base,ignore_errors=True)",
        "raise SystemExit(result.returncode)",
    ))
    return ["sudo", "-n", "-E", sys.executable, "-c", helper,
            json.dumps(argv), json.dumps([str(path) for path in sources])]

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
    command: list[str], writable_roots: tuple[Path, ...], *, cwd: Path | None = None,
    writable_files: tuple[Path, ...] = (), limits: SupervisorLimits = SupervisorLimits(),
) -> tuple[list[str], Path | None]:
    """Return an explicitly detected macOS/Linux sandbox command."""
    if sys.platform == "darwin":
        raise RuntimeError(
            "unsupported protected sandbox: macOS cannot prove process lifetime isolation"
        )
    if sys.platform.startswith("linux") and shutil.which("bwrap"):
        elevated = bool(shutil.which("sudo")) and subprocess.run(
            ["sudo", "-n", "true"], capture_output=True, check=False,
        ).returncode == 0
        if not elevated:
            raise RuntimeError("protected sandbox requires privileged bind staging")
        setpriv = shutil.which("setpriv") if elevated else None
        if elevated and setpriv is None:
            raise RuntimeError("protected sandbox requires setpriv for post-mount uid drop")
        workdir = (cwd or Path.cwd()).resolve()
        argv = ["bwrap", "--unshare-all", "--die-with-parent", "--new-session",
                "--tmpfs", "/", "--proc", "/proc", "--dir", "/tmp"]
        sources: list[Path] = []
        def bind(option: str, source: Path) -> None:
            sources.append(source)
            argv.extend((option, f"@FD:{len(sources) - 1}@", str(source)))
        for item in _runtime_roots(command, workdir):
            bind("--ro-bind", item)
        argv.extend(("--dev", "/dev"))
        for item in writable_roots:
            bind("--bind", item.resolve())
        for item in writable_files:
            bind("--bind", item.resolve())
        argv.extend(("--chdir", str(workdir)))
        drop = (
            [setpriv, "--reuid", str(os.getuid()), "--regid", str(os.getgid()),
             "--clear-groups", "--"] if setpriv else []
        )
        argv.extend(("--", *drop, *_limited_command(command, limits)))
        return _staged_bwrap(argv, sources), None
    raise RuntimeError("unsupported sandbox platform or mechanism")


def run_supervised(
    command: list[str], *, cwd: Path, timeout: int, env: dict[str, str],
    writable_roots: tuple[Path, ...], writable_files: tuple[Path, ...] = (),
    limits: SupervisorLimits = SupervisorLimits(),
) -> tuple[subprocess.CompletedProcess[str], bool]:
    """Run sandboxed and terminate marked descendants across session changes."""
    # pylint: disable=consider-using-with,too-many-locals,too-many-branches,too-many-statements
    try:
        argv, profile = _sandbox_command(
            command, writable_roots, cwd=cwd, writable_files=writable_files,
            limits=limits,
        )
    except RuntimeError as exc:
        return subprocess.CompletedProcess(command, 125, "", str(exc)), False
    token = uuid.uuid4().hex
    stdout_file = tempfile.TemporaryFile(mode="w+", encoding="utf-8")
    stderr_file = tempfile.TemporaryFile(mode="w+", encoding="utf-8")
    process = subprocess.Popen(
        argv, cwd=cwd, stdout=stdout_file, stderr=stderr_file, text=True,
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
    output_limited = False
    while True:
        try:
            process.communicate(
                timeout=max(0.01, min(0.1, deadline - time.monotonic()))
            )
            break
        except subprocess.TimeoutExpired:
            writable_size = sum(
                path.stat().st_size for root in writable_roots
                for path in root.rglob("*") if path.is_file()
            )
            if writable_size > limits.max_writable_bytes:
                output_limited = True
                os.killpg(process.pid, signal.SIGKILL)
                process.communicate()
                break
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
                process.communicate()
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
    stdout_file.seek(0)
    stderr_file.seek(0)
    stdout = stdout_file.read(limits.max_output_bytes + 1)
    stderr = stderr_file.read(limits.max_output_bytes + 1)
    stdout_file.close()
    stderr_file.close()
    encoded = stdout.encode()
    if len(encoded) > limits.max_output_bytes:
        stdout = encoded[:limits.max_output_bytes].decode("utf-8", errors="replace")
        output_limited = True
    encoded = stderr.encode()
    if len(encoded) > limits.max_output_bytes:
        stderr = encoded[:limits.max_output_bytes].decode("utf-8", errors="replace")
        output_limited = True
    return subprocess.CompletedProcess(
        command, 125 if output_limited else (124 if timed_out else process.returncode),
        stdout, stderr,
    ), surviving
