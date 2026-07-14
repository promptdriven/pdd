"""Fail-closed OS sandbox and complete process-group supervision."""
# pylint: disable=too-many-arguments

from __future__ import annotations

import hashlib
import json
import os
import shutil
import signal
import stat
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


@dataclass(frozen=True)
class _ExecutableIdentity:
    """Immutable identity for one executable admitted across the root boundary."""

    path: Path
    stat_identity: tuple[int, int, int, int, int, int]
    sha256: str
    require_root: bool = True

    def payload(self) -> dict[str, object]:
        """Return a strict JSON representation for root-side revalidation."""
        device, inode, mode, uid, size, mtime_ns = self.stat_identity
        return {
            "path": str(self.path), "device": device, "inode": inode,
            "mode": mode, "uid": uid, "size": size,
            "mtime_ns": mtime_ns, "sha256": self.sha256,
        }


def _executable_identity(
    path: Path, *, require_root: bool = True,
) -> _ExecutableIdentity:
    """Measure one exact regular executable and reject unsafe ownership/mode."""
    try:
        resolved = path.resolve(strict=True)
        metadata = resolved.stat()
        executable = os.access(resolved, os.X_OK)
    except OSError as exc:
        raise RuntimeError("protected sandbox requires a trusted root-owned executable") from exc
    if (
        not stat.S_ISREG(metadata.st_mode)
        or not executable
        or (require_root and metadata.st_uid != 0)
        or metadata.st_mode & 0o022
    ):
        raise RuntimeError("protected sandbox requires a trusted root-owned executable")
    digest = hashlib.sha256()
    try:
        with resolved.open("rb") as stream:
            for chunk in iter(lambda: stream.read(1024 * 1024), b""):
                digest.update(chunk)
    except OSError as exc:
        raise RuntimeError("protected sandbox requires a trusted root-owned executable") from exc
    return _ExecutableIdentity(
        resolved,
        (
            metadata.st_dev, metadata.st_ino, stat.S_IMODE(metadata.st_mode),
            metadata.st_uid, metadata.st_size, metadata.st_mtime_ns,
        ),
        digest.hexdigest(), require_root,
    )


def _revalidate_executable(expected: _ExecutableIdentity) -> None:
    """Fail if an admitted executable changed since its trust measurement."""
    try:
        current = _executable_identity(expected.path, require_root=expected.require_root)
    except RuntimeError as exc:
        raise RuntimeError("protected executable identity changed") from exc
    if current != expected:
        raise RuntimeError("protected executable identity changed")


def _trusted_tool(name: str) -> _ExecutableIdentity:
    """Resolve one tool once and bind its root-owned executable identity."""
    value = shutil.which(name)
    if value is None:
        raise RuntimeError("protected sandbox requires a trusted root-owned executable")
    return _executable_identity(Path(value))


def _trusted_helper_python() -> _ExecutableIdentity:
    """Select a system Python whose ownership is independent of the candidate."""
    candidates = (Path("/usr/bin/python3"), Path("/bin/python3"))
    for candidate in candidates:
        if candidate.exists():
            try:
                return _executable_identity(candidate)
            except RuntimeError:
                continue
    return _trusted_tool("python3")


def _privileged_helper_environment(
    _candidate_environment: dict[str, str],
) -> dict[str, str]:
    """Return a constant environment that cannot load candidate Python hooks."""
    return {
        "HOME": "/root", "LANG": "C", "LC_ALL": "C",
        "PATH": "/usr/sbin:/usr/bin:/sbin:/bin",
    }


def _revalidate_privileged_command(argv: list[str]) -> None:
    """Revalidate every bound executable immediately before sudo execution."""
    try:
        manifest = json.loads(argv[-3])
        expected_names = {
            "sudo", "unshare", "python", "mount", "umount", "bwrap", "setpriv",
        }
        if not isinstance(manifest, dict) or set(manifest) != expected_names:
            raise ValueError("invalid executable manifest")
        for payload in manifest.values():
            identity = _ExecutableIdentity(
                Path(payload["path"]),
                (
                    payload["device"], payload["inode"], payload["mode"],
                    payload["uid"], payload["size"], payload["mtime_ns"],
                ),
                payload["sha256"], True,
            )
            _revalidate_executable(identity)
    except (KeyError, TypeError, ValueError, json.JSONDecodeError) as exc:
        raise RuntimeError("protected executable identity manifest is invalid") from exc


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
        "unshare": shutil.which("unshare"),
        "mount": shutil.which("mount"),
        "umount": shutil.which("umount"),
    }
    for name, value in sandbox_commands.items():
        if value:
            path = Path(value).resolve()
            entries[f"sandbox/{name}"] = path
            native.add(path)
    if sys.platform.startswith("linux"):
        try:
            helper_python = _trusted_helper_python().path
        except RuntimeError:
            helper_python = None
        if helper_python is not None:
            entries["sandbox/python-helper"] = helper_python
            native.add(helper_python)
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
    for label, path in released_runtime_closure_paths():
        if label.startswith("sandbox/") or any(
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
    argv: list[str], sources: list[Path],
    tools: dict[str, _ExecutableIdentity],
) -> list[str]:
    """Stage exact bind mounts wholly inside a private mount namespace."""
    helper = "\n".join((
        "import hashlib,json,os,pathlib,shutil,stat,subprocess,sys,tempfile",
        "helper_env={'HOME':'/root','LANG':'C','LC_ALL':'C',"
        "'PATH':'/usr/sbin:/usr/bin:/sbin:/bin'}",
        "os.environ.clear(); os.environ.update(helper_env)",
        "manifest=json.loads(sys.argv[1]); argv=json.loads(sys.argv[2]); "
        "paths=json.loads(sys.argv[3])",
        "def verify(name):",
        " expected=manifest[name]; path=pathlib.Path(expected['path'])",
        " metadata=path.stat()",
        " digest=hashlib.sha256(path.read_bytes()).hexdigest()",
        " actual={'path':str(path.resolve(strict=True)),'device':metadata.st_dev,"
        "'inode':metadata.st_ino,'mode':stat.S_IMODE(metadata.st_mode),"
        "'uid':metadata.st_uid,'size':metadata.st_size,"
        "'mtime_ns':metadata.st_mtime_ns,'sha256':digest}",
        " if actual!=expected or metadata.st_uid!=0 or metadata.st_mode&0o022 "
        "or not stat.S_ISREG(metadata.st_mode): "
        "raise RuntimeError(f'protected executable identity changed: {name}')",
        " return str(path)",
        "candidate_env=json.load(sys.stdin)",
        "for name in manifest: verify(name)",
        "mount=verify('mount'); umount=verify('umount'); bwrap=verify('bwrap')",
        "base=pathlib.Path(tempfile.mkdtemp(prefix='pdd-binds-',dir='/run'))",
        "os.chmod(base,0o755); staged=[]; result=None",
        "try:",
        " for index,source in enumerate(paths):",
        "  source=pathlib.Path(source); target=base/str(index)",
        "  target.mkdir() if source.is_dir() else target.touch()",
        "  mount=verify('mount')",
        "  subprocess.run([mount,'--bind',str(source),str(target)],check=True)",
        "  staged.append(target)",
        " argv=[str(staged[int(x[4:-1])]) if x.startswith('@FD:') else x for x in argv]",
        " if argv[0]!=bwrap: raise RuntimeError('protected bwrap identity mismatch')",
        " verify('bwrap')",
        " result=subprocess.run(argv,check=False,env=candidate_env)",
        "finally:",
        " for target in reversed(staged):",
        "  umount=verify('umount')",
        "  subprocess.run([umount,str(target)],check=False)",
        " shutil.rmtree(base,ignore_errors=True)",
        "raise SystemExit(result.returncode if result is not None else 1)",
    ))
    manifest = json.dumps({name: identity.payload() for name, identity in tools.items()})
    return [
        str(tools["sudo"].path), "-n", "--", str(tools["unshare"].path),
        "--mount", "--propagation", "private", "--wd", "/",
        str(tools["python"].path), "-I", "-S", "-c", helper, manifest,
        json.dumps(argv), json.dumps([str(path) for path in sources]),
    ]


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
    result_fifo: Path | None = None,
    result_fd: int = 198,
) -> tuple[list[str], Path | None]:
    # pylint: disable=too-many-locals,too-many-branches
    """Return an explicitly detected macOS/Linux sandbox command."""
    if sys.platform == "darwin":
        raise RuntimeError(
            "unsupported protected sandbox: macOS cannot prove process lifetime isolation"
        )
    if sys.platform.startswith("linux"):
        if os.getuid() == 0:
            raise RuntimeError(
                "protected sandbox requires a non-root caller so process limits "
                "remain kernel-enforced"
            )
        tools = {
            "sudo": _trusted_tool("sudo"),
            "unshare": _trusted_tool("unshare"),
            "python": _trusted_helper_python(),
            "mount": _trusted_tool("mount"),
            "umount": _trusted_tool("umount"),
            "bwrap": _trusted_tool("bwrap"),
            "setpriv": _trusted_tool("setpriv"),
        }
        if subprocess.run(
            [str(tools["sudo"].path), "-n", "true"],
            capture_output=True, check=False,
        ).returncode != 0:
            raise RuntimeError("protected sandbox requires privileged bind staging")
        setpriv = str(tools["setpriv"].path)
        workdir = (cwd or Path.cwd()).resolve()
        argv = [str(tools["bwrap"].path),
                "--unshare-ipc", "--unshare-pid", "--unshare-net",
                "--unshare-uts", "--unshare-cgroup", "--die-with-parent", "--new-session",
                "--tmpfs", "/", "--proc", "/proc", "--dir", "/tmp"]
        sources: list[Path] = []
        destination_dirs = {Path("/tmp")}
        def bind(option: str, source: Path, destination: Path | None = None) -> None:
            destination = destination or source
            missing = []
            parent = destination.parent
            while parent != Path("/") and parent not in destination_dirs:
                missing.append(parent)
                parent = parent.parent
            for directory in reversed(missing):
                argv.extend(("--dir", str(directory)))
                destination_dirs.add(directory)
            sources.append(source)
            argv.extend((option, f"@FD:{len(sources) - 1}@", str(destination)))
            if destination.is_dir():
                destination_dirs.add(destination)
        for item in _runtime_roots(command, workdir):
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
        argv.extend(("--chdir", str(workdir)))
        drop = (
            [setpriv, "--reuid", str(os.getuid()), "--regid", str(os.getgid()),
             "--clear-groups", "--"] if setpriv else []
        )
        sandboxed = _limited_command(command, limits)
        if result_fifo is not None:
            sandboxed = _private_result_command(sandboxed, result_fifo, result_fd)
        argv.extend(("--", *drop, *sandboxed))
        return _staged_bwrap(argv, sources, tools), None
    raise RuntimeError("unsupported sandbox platform or mechanism")


def run_supervised(
    command: list[str], *, cwd: Path, timeout: int, env: dict[str, str],
    writable_roots: tuple[Path, ...], writable_files: tuple[Path, ...] = (),
    limits: SupervisorLimits = SupervisorLimits(),
    readable_roots: tuple[Path, ...] = (),
    readable_bindings: tuple[tuple[Path, Path], ...] = (),
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
            result_fifo=result_fifo, result_fd=result_fd,
        )
        _revalidate_privileged_command(argv)
    except RuntimeError as exc:
        return subprocess.CompletedProcess(command, 125, "", str(exc)), False
    token = uuid.uuid4().hex
    stdout_file = tempfile.TemporaryFile(mode="w+b")
    stderr_file = tempfile.TemporaryFile(mode="w+b")
    sandbox_environment = env | {
        "PYTHONDONTWRITEBYTECODE": "1",
        "PDD_SUPERVISION_TOKEN": token,
        "TMPDIR": str(writable_roots[0].resolve()),
        "TEMP": str(writable_roots[0].resolve()),
        "TMP": str(writable_roots[0].resolve()),
    }
    library_path = _sandbox_library_path(env)
    if library_path:
        sandbox_environment["LD_LIBRARY_PATH"] = library_path
    process = subprocess.Popen(
        argv, cwd=Path("/"), stdin=subprocess.PIPE,
        stdout=stdout_file, stderr=stderr_file,
        env=_privileged_helper_environment(sandbox_environment),
        start_new_session=True,
    )
    try:
        if process.stdin is None:
            raise RuntimeError("protected helper environment channel is unavailable")
        process.stdin.write(json.dumps(sandbox_environment).encode("utf-8"))
        process.stdin.close()
        process.stdin = None
    except (BrokenPipeError, OSError, RuntimeError) as exc:
        try:
            os.killpg(process.pid, signal.SIGKILL)
        except ProcessLookupError:
            pass
        process.wait()
        stdout_file.close()
        stderr_file.close()
        return subprocess.CompletedProcess(
            command, 125, "", f"protected helper startup failed: {exc}"
        ), False
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
