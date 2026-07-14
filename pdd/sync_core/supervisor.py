"""Fail-closed OS sandbox and complete process-group supervision."""
# pylint: disable=too-many-arguments

from __future__ import annotations

import os
import json
import base64
import re
import shutil
import signal
import subprocess
import sys
import tempfile
import threading
import time
import uuid
from functools import lru_cache
from dataclasses import dataclass
from pathlib import Path
import sysconfig


# Capture the executable that loaded this trusted module. Tests and callers may
# replace ``sys.executable`` to model argv-prefix portability; that synthetic
# spelling must never become a measured file or sandbox mount source.
_SUPERVISOR_EXECUTABLE = Path(sys.executable)


@dataclass(frozen=True)
class SupervisorLimits:
    """Hard limits applied to every untrusted validator process tree."""

    max_output_bytes: int = 16 * 1024 * 1024
    max_writable_bytes: int = 512 * 1024 * 1024
    max_memory_bytes: int = 2 * 1024 * 1024 * 1024
    max_cpu_seconds: int = 300
    max_processes: int = 128


def _linked_libraries(path: Path) -> tuple[Path, ...]:
    """Resolve loader-visible and physical paths for ELF dependencies."""
    if not sys.platform.startswith("linux"):
        return ()
    result = subprocess.run(
        ["ldd", str(path)], capture_output=True, text=True, check=False
    )
    libraries: set[Path] = set()
    for line in result.stdout.splitlines():
        fields = line.strip().split()
        candidates = (
            fields[2:3] if len(fields) >= 3 and fields[1:2] == ["=>"] else fields[:1]
        )
        for value in candidates:
            candidate = Path(value)
            if candidate.is_absolute() and candidate.is_file():
                libraries.add(candidate)
                # The dynamic loader may retain the /lib alias while the host
                # mount operation follows it to /usr/lib.  Bind both spellings
                # so the empty namespace contains the loader's lookup path and
                # the resolved dependency used by the host mount.
                libraries.add(candidate.resolve())
    return tuple(sorted(libraries))


def _runtime_directories() -> tuple[tuple[str, Path], ...]:
    """Return Python directories whose complete readable contents are mounted."""
    locations = sysconfig.get_paths()
    labels = {
        "stdlib": locations.get("stdlib"),
        "platstdlib": locations.get("platstdlib"),
        "purelib": locations.get("purelib"),
        "platlib": locations.get("platlib"),
    }
    candidates = []
    for label, value in labels.items():
        if not value:
            continue
        path = Path(value).resolve()
        if path.is_dir() and path not in {item[1] for item in candidates}:
            candidates.append((label, path))
    result = []
    for label, path in sorted(candidates, key=lambda item: len(item[1].parts)):
        if any(path.is_relative_to(parent) for _parent_label, parent in result):
            continue
        result.append((label, path))
    result = [
        (f"python-runtime/{label}", path) for label, path in result
    ]
    return tuple(result)


@lru_cache(maxsize=1)
def released_runtime_closure_paths() -> tuple[tuple[str, Path], ...]:
    """Return every regular file exposed by the sandbox with logical names."""
    entries: dict[str, Path] = {}
    native: set[Path] = {_SUPERVISOR_EXECUTABLE.resolve()}
    for label, directory in _runtime_directories():
        for path in sorted(directory.rglob("*")):
            if path.is_file() and not path.is_symlink():
                entries[f"{label}/{path.relative_to(directory).as_posix()}"] = path
                if path.suffix in {".so", ".dylib"}:
                    native.add(path)
    sandbox_commands = {
        "bwrap": shutil.which("bwrap"),
        "setpriv": shutil.which("setpriv"),
        "sudo": shutil.which("sudo"),
        "mount": shutil.which("mount"),
        "umount": shutil.which("umount"),
    }
    for name, value in sandbox_commands.items():
        if value:
            path = Path(value).resolve()
            entries[f"sandbox/{name}"] = path
            native.add(path)
    entries["interpreter/python"] = _SUPERVISOR_EXECUTABLE.resolve()
    for path in sorted(native):
        for library in _linked_libraries(path):
            entries.setdefault(
                f"native/{library.as_posix().lstrip('/')}", library
            )
    return tuple(sorted(entries.items()))


def _runtime_roots(command: list[str], cwd: Path) -> tuple[Path, ...]:
    """Return the measured runtime closure plus the checker working directory."""
    roots: set[Path] = {cwd.resolve()}
    directories = tuple(directory for _label, directory in _runtime_directories())
    roots.update(directories)
    executables = (
        _SUPERVISOR_EXECUTABLE, Path(shutil.which(command[0]) or command[0]),
    )
    for executable in executables:
        resolved_executable = executable.resolve()
        if not executable.is_relative_to(cwd):
            roots.add(executable)
        if not resolved_executable.is_relative_to(cwd):
            roots.add(resolved_executable)
    for _label, path in released_runtime_closure_paths():
        if path.name in {"bwrap", "setpriv", "sudo", "mount", "umount"} or any(
            path.is_relative_to(directory) for directory in directories
        ):
            continue
        roots.add(path)
    return tuple(sorted(roots, key=lambda item: (len(item.parts), str(item))))


def _sandbox_library_path(environment: dict[str, str]) -> str:
    """Return loader search directories derived only from the measured closure."""
    directories = []
    for label, path in released_runtime_closure_paths():
        if label.startswith("native/"):
            directories.append(str(path.parent))
    directories.append(str(Path(sys.prefix) / "lib"))
    directories.extend(
        item for item in environment.get("LD_LIBRARY_PATH", "").split(os.pathsep)
        if item
    )
    return os.pathsep.join(dict.fromkeys(directories))


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
    return [str(_SUPERVISOR_EXECUTABLE), "-c", script, str(limits.max_memory_bytes),
            str(limits.max_cpu_seconds), str(limits.max_processes),
            str(limits.max_output_bytes), "256", *command]


def _staged_bwrap(
    argv: list[str], sources: list[Path], path_tokens: list[str],
    data: tuple[bytes, ...] = (), data_tokens: tuple[str, ...] = (),
) -> list[str]:
    """Stage exact bind mounts and anonymous immutable data for Bubblewrap."""
    if len(data) != len(data_tokens):
        raise RuntimeError("protected sandbox has invalid anonymous data staging")
    if any(len(item) > _MAX_STAGED_DATA_BYTES for item in data) or sum(
        len(item) for item in data
    ) > _MAX_STAGED_DATA_BYTES:
        raise RuntimeError("protected sandbox anonymous data exceeds 64 KiB limit")
    helper = "\n".join((
        "import base64,json,os,pathlib,shutil,subprocess,sys,tempfile",
        "data=json.loads(sys.argv[1]); path_tokens=json.loads(sys.argv[2])",
        ("data_tokens=json.loads(sys.argv[3]); argv=json.loads(sys.argv[4]); "
         "paths=json.loads(sys.argv[5])"),
        "base=pathlib.Path(tempfile.mkdtemp(prefix='pdd-binds-',dir='/run'))",
        "os.chmod(base,0o755); staged=[]; data_fds=[]; result=None",
        "try:",
        " for index,source in enumerate(paths):",
        "  source=pathlib.Path(source); target=base/str(index)",
        "  target.mkdir() if source.is_dir() else target.touch()",
        "  subprocess.run(['mount','--bind',str(source),str(target)],check=True)",
        "  staged.append(target)",
        " path_map={token:str(staged[index]) for index,token in enumerate(path_tokens)}",
        " argv=[path_map.get(value,value) for value in argv]",
        " for index,encoded in enumerate(data):",
        "  fd=os.memfd_create('pdd-sandbox-data-'+str(index),os.MFD_CLOEXEC)",
        "  content=base64.b64decode(encoded,validate=True); view=memoryview(content)",
        "  while view:",
        "   written=os.write(fd,view)",
        "   if written <= 0: raise OSError('short memfd write')",
        "   view=view[written:]",
        "  os.lseek(fd,0,os.SEEK_SET)",
        "  data_fds.append(fd)",
        " data_map={token:str(data_fds[index]) for index,token in enumerate(data_tokens)}",
        " argv=[data_map.get(value,value) for value in argv]",
        " result=subprocess.run(argv,check=False,pass_fds=tuple(data_fds))",
        "finally:",
        " for fd in data_fds: os.close(fd)",
        " for target in reversed(staged):",
        "  subprocess.run(['umount',str(target)],check=False)",
        " shutil.rmtree(base,ignore_errors=True)",
        "raise SystemExit(result.returncode if result is not None else 1)",
    ))
    return ["sudo", "-n", "-E", str(_SUPERVISOR_EXECUTABLE), "-c", helper,
            json.dumps([base64.b64encode(item).decode("ascii") for item in data]),
            json.dumps(path_tokens),
            json.dumps(data_tokens),
            json.dumps(argv),
            json.dumps([str(path) for path in sources])]


_BWRAP_OVERLAY_MIN_VERSION = (0, 11, 1)
_MAX_STAGED_DATA_BYTES = 64 * 1024


def _bwrap_probe(bwrap: str, option: str) -> subprocess.CompletedProcess[str]:
    """Run one required Bubblewrap capability probe or fail closed."""
    try:
        return subprocess.run(
            [bwrap, option], capture_output=True, text=True, check=False
        )
    except OSError as exc:
        raise RuntimeError(
            "protected sandbox cannot execute Bubblewrap capability probe"
        ) from exc


def _bwrap_overlay_capability(bwrap: str) -> str | None:
    """Return why Bubblewrap cannot safely create private overlay data mounts."""
    version = _bwrap_probe(bwrap, "--version")
    if version.returncode != 0:
        return "protected sandbox cannot determine Bubblewrap version"
    match = re.search(r"(\d+)\.(\d+)\.(\d+)", version.stdout)
    if match is None:
        return "protected sandbox cannot parse Bubblewrap version"
    parsed = tuple(int(value) for value in match.groups())
    if parsed < _BWRAP_OVERLAY_MIN_VERSION:
        required = ".".join(str(value) for value in _BWRAP_OVERLAY_MIN_VERSION)
        return f"protected sandbox requires Bubblewrap {required} for private overlays"
    help_result = _bwrap_probe(bwrap, "--help")
    required_flags = (
        "--overlay-src", "--tmp-overlay", "--ro-bind-data", "--remount-ro",
    )
    if help_result.returncode != 0 or any(
        flag not in help_result.stdout for flag in required_flags
    ):
        return "protected sandbox Bubblewrap lacks private overlay data-mount support"
    return None


def _private_result_command(
    command: list[str], result_fifo: Path, result_fd: int,
) -> list[str]:
    """Open and unlink a checker FIFO before candidate code can execute."""
    script = (
        "import os,sys;"
        "path=sys.argv[1];target=int(sys.argv[2]);"
        "source=os.open(path,os.O_WRONLY);os.unlink(path);"
        "os.dup2(source,target);"
        "os.close(source) if source!=target else None;"
        "os.execvpe(sys.argv[3],sys.argv[3:],os.environ)"
    )
    return [str(_SUPERVISOR_EXECUTABLE), "-c", script,
            str(result_fifo), str(result_fd), *command]

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


def _process_identity(pid: int) -> str | None:
    """Return a stable Linux process identity, including kernel start time."""
    if sys.platform.startswith("linux"):
        try:
            stat_fields = Path(f"/proc/{pid}/stat").read_text(
                encoding="utf-8"
            ).rsplit(")", 1)[1].split()
            return stat_fields[19]
        except (OSError, IndexError):
            return None
    return None


def _live_processes(pids: dict[int, str | None]) -> set[int]:
    """Return only observations whose stable process identity still matches."""
    live = set()
    for pid, identity in pids.items():
        if identity is None or _process_identity(pid) != identity:
            continue
        try:
            os.kill(pid, 0)
        except (ProcessLookupError, PermissionError):
            continue
        live.add(pid)
    return live


def _writable_size(roots: tuple[Path, ...]) -> int:
    """Measure a concurrently mutable tree without allowing races to escape."""
    total = 0
    for root in roots:
        try:
            paths = root.rglob("*")
            for path in paths:
                try:
                    if path.is_file() and not path.is_symlink():
                        total += path.stat().st_size
                except OSError:
                    continue
        except OSError:
            continue
    return total


def _sandbox_command(
    command: list[str], writable_roots: tuple[Path, ...], *, cwd: Path | None = None,
    writable_files: tuple[Path, ...] = (), limits: SupervisorLimits = SupervisorLimits(),
    readable_roots: tuple[Path, ...] = (),
    readable_bindings: tuple[tuple[Path, Path], ...] = (),
    private_overlays: tuple[tuple[Path, Path], ...] = (),
    readable_data: tuple[tuple[bytes, Path], ...] = (),
    writable_bindings: tuple[tuple[Path, Path], ...] = (),
    result_fifo: Path | None = None,
    result_fd: int = 198,
) -> tuple[list[str], Path | None]:
    # pylint: disable=too-many-locals,too-many-branches,too-many-statements
    """Return an explicitly detected macOS/Linux sandbox command."""
    if sys.platform == "darwin":
        raise RuntimeError(
            "unsupported protected sandbox: macOS cannot prove process lifetime isolation"
        )
    if sys.platform.startswith("linux") and (bwrap := shutil.which("bwrap")):
        if os.getuid() == 0:
            raise RuntimeError(
                "protected sandbox requires a non-root caller so process limits "
                "remain kernel-enforced"
            )
        if not (bool(shutil.which("sudo")) and subprocess.run(
                ["sudo", "-n", "true"], capture_output=True, check=False,
        ).returncode == 0):
            raise RuntimeError("protected sandbox requires privileged bind staging")
        setpriv = shutil.which("setpriv")
        if setpriv is None:
            raise RuntimeError("protected sandbox requires setpriv for post-mount uid drop")
        if private_overlays or readable_data:
            capability_error = _bwrap_overlay_capability(bwrap)
            if capability_error is not None:
                raise RuntimeError(capability_error)
        workdir = (cwd or Path.cwd()).resolve()
        argv = [bwrap, "--unshare-ipc", "--unshare-pid", "--unshare-net",
                "--unshare-uts", "--unshare-cgroup", "--die-with-parent", "--new-session",
                "--tmpfs", "/", "--proc", "/proc", "--dir", "/tmp"]
        sources: list[Path] = []
        path_tokens: list[str] = []
        destination_dirs = {Path("/tmp")}
        mounted: dict[Path, tuple[str, Path]] = {}

        def stage_source(source: Path) -> str:
            token = f"@PDD-PATH-{uuid.uuid4().hex}@"
            sources.append(source)
            path_tokens.append(token)
            return token

        def ensure_destination_parent(destination: Path) -> None:
            missing = []
            parent = destination.parent
            while parent != Path("/") and parent not in destination_dirs:
                missing.append(parent)
                parent = parent.parent
            for directory in reversed(missing):
                argv.extend(("--dir", str(directory)))
                destination_dirs.add(directory)

        def bind(option: str, source: Path, destination: Path | None = None) -> None:
            destination = destination or source
            binding = (option, source.resolve())
            previous = mounted.get(destination)
            if previous == binding:
                return
            if previous is not None and previous[1] != binding[1]:
                raise RuntimeError(
                    f"protected sandbox has conflicting bindings for {destination}"
                )
            mounted[destination] = binding
            ensure_destination_parent(destination)
            argv.extend((option, stage_source(source), str(destination)))
            if destination.is_dir():
                destination_dirs.add(destination)

        def private_overlay(source: Path, destination: Path) -> None:
            if not destination.is_absolute():
                raise RuntimeError("protected sandbox overlay destination must be absolute")
            try:
                source = source.resolve(strict=True)
            except OSError as exc:
                raise RuntimeError("protected sandbox overlay source is unavailable") from exc
            if not source.is_dir():
                raise RuntimeError("protected sandbox overlay source must be a directory")
            if destination in mounted:
                raise RuntimeError(
                    f"protected sandbox has conflicting bindings for {destination}"
                )
            ensure_destination_parent(destination)
            argv.extend(("--dir", str(destination)))
            destination_dirs.add(destination)
            argv.extend((
                "--overlay-src", stage_source(source),
                "--tmp-overlay", str(destination),
            ))
            mounted[destination] = ("--tmp-overlay", source)

        data: list[bytes] = []
        data_tokens: list[str] = []

        def bind_data(content: bytes, destination: Path) -> None:
            if not destination.is_absolute():
                raise RuntimeError("protected sandbox data destination must be absolute")
            if destination in mounted:
                raise RuntimeError(
                    f"protected sandbox has conflicting bindings for {destination}"
                )
            ensure_destination_parent(destination)
            mounted[destination] = ("--ro-bind-data", Path("/dev/null"))
            data.append(content)
            token = f"@PDD-DATA-{uuid.uuid4().hex}@"
            data_tokens.append(token)
            argv.extend(("--perms", "0444", "--ro-bind-data", token, str(destination)))

        for source, destination in writable_bindings:
            bind("--bind", source.resolve(), destination)
        for source, destination in private_overlays:
            private_overlay(source, destination)
        for item in _runtime_roots(command, workdir):
            existing_mount = mounted.get(item)
            if existing_mount is not None and existing_mount[0] == "--tmp-overlay":
                continue
            # A host bind follows symlinks, but the process command and ELF
            # loader retain their original spellings in the new namespace.
            bind("--ro-bind", item.resolve(), item)
        # ``setpriv`` executes after the namespace root is installed, so bind
        # it and its ELF closure directly even when PATH resolution differs.
        if setpriv is not None:
            setpriv_path = Path(setpriv)
            for item in (setpriv_path, *_linked_libraries(setpriv_path)):
                bind("--ro-bind", item.resolve(), item)
        for item in readable_roots:
            bind("--ro-bind", item.resolve())
        for source, destination in readable_bindings:
            bind("--ro-bind", source.resolve(), destination)
        argv.extend(("--dev", "/dev"))
        for item in writable_roots:
            bind("--bind", item.resolve())
        for item in writable_files:
            bind("--bind", item.resolve())
        if result_fifo is not None:
            # The coordinator wrapper opens and unlinks the FIFO before it
            # executes any candidate-controlled code.  Binding only its
            # dedicated directory keeps the reporter and toolchain immutable.
            bind("--bind", result_fifo.parent.resolve())
        for content, destination in readable_data:
            bind_data(content, destination)
        for _source, destination in private_overlays:
            argv.extend(("--remount-ro", str(destination)))
        argv.extend(("--chdir", str(workdir)))
        drop = (
            [setpriv, "--reuid", str(os.getuid()), "--regid", str(os.getgid()),
             "--clear-groups", "--"] if setpriv else []
        )
        sandboxed = _limited_command(command, limits)
        if result_fifo is not None:
            sandboxed = _private_result_command(sandboxed, result_fifo, result_fd)
        argv.extend(("--", *drop, *sandboxed))
        return _staged_bwrap(
            argv, sources, path_tokens, tuple(data), tuple(data_tokens)
        ), None
    raise RuntimeError("unsupported sandbox platform or mechanism")


def run_supervised(
    command: list[str], *, cwd: Path, timeout: int, env: dict[str, str],
    writable_roots: tuple[Path, ...], writable_files: tuple[Path, ...] = (),
    limits: SupervisorLimits = SupervisorLimits(),
    readable_roots: tuple[Path, ...] = (),
    readable_bindings: tuple[tuple[Path, Path], ...] = (),
    private_overlays: tuple[tuple[Path, Path], ...] = (),
    readable_data: tuple[tuple[bytes, Path], ...] = (),
    writable_bindings: tuple[tuple[Path, Path], ...] = (),
    temp_directory: Path | None = None,
    result_fifo: Path | None = None,
    result_fd: int = 198,
) -> tuple[subprocess.CompletedProcess[str], bool]:
    """Run sandboxed and terminate marked descendants across session changes."""
    # pylint: disable=consider-using-with,too-many-locals,too-many-branches,too-many-statements
    try:
        argv, profile = _sandbox_command(
            command, writable_roots, cwd=cwd, writable_files=writable_files,
            limits=limits, readable_roots=readable_roots,
            readable_bindings=readable_bindings,
            private_overlays=private_overlays, readable_data=readable_data,
            writable_bindings=writable_bindings,
            result_fifo=result_fifo, result_fd=result_fd,
        )
    except RuntimeError as exc:
        return subprocess.CompletedProcess(command, 125, "", str(exc)), False
    token = uuid.uuid4().hex
    stdout_file = tempfile.TemporaryFile(mode="w+b")
    stderr_file = tempfile.TemporaryFile(mode="w+b")
    sandbox_environment = env | {
        "PYTHONDONTWRITEBYTECODE": "1",
        "PDD_SUPERVISION_TOKEN": token,
        "TMPDIR": str(temp_directory or writable_roots[0].resolve()),
        "TEMP": str(temp_directory or writable_roots[0].resolve()),
        "TMP": str(temp_directory or writable_roots[0].resolve()),
    }
    library_path = _sandbox_library_path(env)
    if library_path:
        sandbox_environment["LD_LIBRARY_PATH"] = library_path
    process = subprocess.Popen(
        argv, cwd=cwd, stdout=stdout_file, stderr=stderr_file,
        env=sandbox_environment,
        start_new_session=True,
    )
    timed_out = False
    surviving = False
    tracked: dict[int, str | None] = {}
    tracking_done = threading.Event()

    def track_process_tree() -> None:
        while not tracking_done.wait(0.005):
            for pid in _process_descendants(process.pid):
                tracked.setdefault(pid, _process_identity(pid))

    tracker = threading.Thread(target=track_process_tree, daemon=True)
    tracker.start()
    deadline = time.monotonic() + timeout
    output_limited = False
    try:
        while process.poll() is None:
            if time.monotonic() >= deadline:
                timed_out = True
                break
            if _writable_size(writable_roots) > limits.max_writable_bytes:
                output_limited = True
                break
            if stdout_file.tell() + stderr_file.tell() > limits.max_output_bytes:
                output_limited = True
                break
            time.sleep(0.01)
    finally:
        tracking_done.set()
        tracker.join(timeout=1)
        if process.poll() is None:
            try:
                os.killpg(process.pid, signal.SIGKILL)
            except ProcessLookupError:
                pass
        process.wait()
        observed = _supervised_descendants(token) - {process.pid}
        for pid in observed:
            tracked.setdefault(pid, _process_identity(pid))
        descendants = _live_processes(tracked)
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
    remaining = limits.max_output_bytes
    stdout_bytes = stdout_file.read(remaining)
    remaining -= len(stdout_bytes)
    stderr_bytes = stderr_file.read(remaining)
    if stdout_file.read(1) or stderr_file.read(1):
        output_limited = True
    stdout_file.close()
    stderr_file.close()
    stdout = stdout_bytes.decode("utf-8", errors="replace")
    stderr = stderr_bytes.decode("utf-8", errors="replace")
    return subprocess.CompletedProcess(
        command, 125 if output_limited else (124 if timed_out else process.returncode),
        stdout, stderr,
    ), surviving
