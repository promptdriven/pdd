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
    max_virtual_memory_bytes: int = 2 * 1024 * 1024 * 1024
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
        "systemd-run": shutil.which("systemd-run"),
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
        if path.name in {"bwrap", "setpriv", "sudo", "systemd-run", "mount", "umount"} or any(
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
    return [str(_SUPERVISOR_EXECUTABLE), "-c", script, str(limits.max_virtual_memory_bytes),
            str(limits.max_cpu_seconds), str(limits.max_processes),
            str(limits.max_output_bytes), "256", *command]


def _staged_bwrap(
    argv: list[str], sources: list[Path], path_tokens: list[str], *,
    cgroup_name: str, limits: SupervisorLimits, use_systemd_scope: bool,
) -> list[str]:
    """Stage trusted mounts and contain the complete child tree in cgroup v2."""
    helper = "\n".join((
        "import json,os,pathlib,shutil,signal,subprocess,sys,tempfile,time",
        "path_tokens=json.loads(sys.argv[1]); argv=json.loads(sys.argv[2]); paths=json.loads(sys.argv[3])",
        "name=sys.argv[4]; limits=json.loads(sys.argv[5])",
        "base=pathlib.Path(tempfile.mkdtemp(prefix='pdd-binds-',dir='/run'))",
        "os.chmod(base,0o755); staged=[]; result=None; cgroup=None",
        "def write(path,value): path.write_text(str(value),encoding='ascii')",
        "def cgroup_root():",
        " mount=pathlib.Path('/sys/fs/cgroup')",
        " if not (mount/'cgroup.controllers').is_file(): raise RuntimeError('protected sandbox requires writable cgroup v2')",
        " return mount",
        "def configure_group():",
        " root=cgroup_root(); controls=(root/'cgroup.subtree_control').read_text(encoding='ascii').split()",
        " available=(root/'cgroup.controllers').read_text(encoding='ascii').split()",
        " for controller in ('memory','pids'):",
        "  if controller not in available: raise RuntimeError('protected sandbox cgroup v2 lacks '+controller+' controller')",
        "  if controller not in controls: write(root/'cgroup.subtree_control','+'+controller)",
        " group=root/name; group.mkdir()",
        " try:",
        "  write(group/'memory.max',limits['memory'])",
        "  write(group/'memory.swap.max',0)",
        "  write(group/'memory.oom.group',1)",
        "  write(group/'pids.max',limits['pids'])",
        " except BaseException:",
        "  group.rmdir(); raise",
        " return group",
        "def cleanup_group(group):",
        " if group is None or not group.exists(): return",
        " write(group/'cgroup.kill',1)",
        " deadline=time.monotonic()+5",
        " while (group/'cgroup.procs').read_text(encoding='ascii').strip():",
        "  if time.monotonic() >= deadline: raise RuntimeError('protected sandbox cgroup did not empty')",
        "  time.sleep(.01)",
        " group.rmdir()",
        "try:",
        " for index,source in enumerate(paths):",
        "  source=pathlib.Path(source); target=base/str(index)",
        "  target.mkdir() if source.is_dir() else target.touch()",
        "  subprocess.run(['mount','--bind',str(source),str(target)],check=True)",
        "  staged.append(target)",
        " path_map={token:str(staged[index]) for index,token in enumerate(path_tokens)}",
        " argv=[path_map.get(value,value) for value in argv]",
        " cgroup=configure_group()",
        " pid=os.fork()",
        " if pid == 0:",
        "  os.kill(os.getpid(),signal.SIGSTOP)",
        "  os.execvpe(argv[0],argv,os.environ)",
        " stopped,status=os.waitpid(pid,os.WUNTRACED)",
        " if stopped != pid or not os.WIFSTOPPED(status): raise RuntimeError('protected sandbox cannot stop child before cgroup assignment')",
        " write(cgroup/'cgroup.procs',pid)",
        " os.kill(pid,signal.SIGCONT)",
        " _wait,status=os.waitpid(pid,0)",
        " result=os.waitstatus_to_exitcode(status)",
        "finally:",
        " cleanup_error=None",
        " try: cleanup_group(cgroup)",
        " except BaseException as exc: cleanup_error=exc",
        " for target in reversed(staged):",
        "  subprocess.run(['umount',str(target)],check=False)",
        " shutil.rmtree(base,ignore_errors=True)",
        "if cleanup_error is not None: raise RuntimeError('protected sandbox cgroup cleanup failed') from cleanup_error",
        "raise SystemExit(result if result is not None else 125)",
    ))
    command = ["sudo", "-n", "-E", str(_SUPERVISOR_EXECUTABLE), "-c", helper,
               json.dumps(path_tokens), json.dumps(argv),
               json.dumps([str(path) for path in sources]), cgroup_name,
               json.dumps({"memory": limits.max_memory_bytes, "pids": limits.max_processes})]
    if not use_systemd_scope:
        return command
    return [
        "sudo", "-n", "-E", "systemd-run", "--scope", "--quiet", "--wait",
        "--collect", f"--property=MemoryMax={limits.max_memory_bytes}",
        "--property=MemorySwapMax=0", f"--property=TasksMax={limits.max_processes}",
        "--property=OOMPolicy=kill", *command[3:],
    ]


_CGROUP_PROBE = """import os,pathlib,uuid
root=pathlib.Path('/sys/fs/cgroup')
if not (root/'cgroup.controllers').is_file(): raise SystemExit('cgroup v2 is unavailable')
available=(root/'cgroup.controllers').read_text(encoding='ascii').split()
if not {'memory','pids'} <= set(available): raise SystemExit('cgroup v2 memory/pids controllers are unavailable')
controls=(root/'cgroup.subtree_control').read_text(encoding='ascii').split()
for controller in ('memory','pids'):
    if controller not in controls: (root/'cgroup.subtree_control').write_text('+'+controller,encoding='ascii')
group=root/('pdd-probe-'+uuid.uuid4().hex)
group.mkdir()
try:
    (group/'memory.max').write_text('max',encoding='ascii')
    (group/'memory.swap.max').write_text('0',encoding='ascii')
    (group/'memory.oom.group').write_text('1',encoding='ascii')
    (group/'pids.max').write_text('max',encoding='ascii')
finally:
    group.rmdir()
"""


def _cgroup_v2_capability() -> str | None:
    """Probe the privileged cgroup-v2 controls required before candidate exec."""
    try:
        probe = subprocess.run(
            ["sudo", "-n", str(_SUPERVISOR_EXECUTABLE), "-c", _CGROUP_PROBE],
            capture_output=True, text=True, check=False,
        )
    except OSError as exc:
        return f"protected sandbox cannot probe cgroup v2 controls: {exc}"
    if probe.returncode != 0:
        detail = " ".join(probe.stderr.split())[:256]
        return "protected sandbox requires writable cgroup v2 memory/pids controls" + (
            f": {detail}" if detail else ""
        )
    return None


def _systemd_scope_usable(limits: SupervisorLimits) -> bool:
    """Return whether a transient scope can prove the required cgroup properties."""
    systemd = shutil.which("systemd-run")
    if systemd is None or not Path(systemd).is_file():
        return False
    try:
        result = subprocess.run(
            ["sudo", "-n", systemd, "--scope", "--quiet", "--wait", "--collect",
             f"--property=MemoryMax={limits.max_memory_bytes}",
             "--property=MemorySwapMax=0",
             f"--property=TasksMax={limits.max_processes}",
             "--property=OOMPolicy=kill", "/bin/true"],
            capture_output=True, text=True, check=False,
        )
    except OSError:
        return False
    return result.returncode == 0


_CGROUP_CLEANUP = """import pathlib,sys,time
name=sys.argv[1]
if not name.startswith('pdd-') or len(name) != 36: raise SystemExit('invalid protected cgroup name')
group=pathlib.Path('/sys/fs/cgroup')/name
if not group.exists(): raise SystemExit(0)
(group/'cgroup.kill').write_text('1',encoding='ascii')
deadline=time.monotonic()+5
while (group/'cgroup.procs').read_text(encoding='ascii').strip():
    if time.monotonic() >= deadline: raise SystemExit('protected cgroup did not empty')
    time.sleep(.01)
group.rmdir()
"""


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
    writable_bindings: tuple[tuple[Path, Path], ...] = (),
    result_fifo: Path | None = None,
    result_fd: int = 198,
    cgroup_name: str | None = None,
) -> tuple[list[str], Path | None]:
    # pylint: disable=too-many-locals,too-many-branches,too-many-statements
    """Return an explicitly detected macOS/Linux sandbox command."""
    if sys.platform == "darwin":
        raise RuntimeError(
            "unsupported protected sandbox: macOS cannot prove process lifetime isolation"
        )
    if sys.platform.startswith("linux") and shutil.which("bwrap"):
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
        capability_error = _cgroup_v2_capability()
        if capability_error is not None:
            raise RuntimeError(capability_error)
        workdir = (cwd or Path.cwd()).resolve()
        argv = ["bwrap", "--unshare-ipc", "--unshare-pid", "--unshare-net",
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

        for source, destination in writable_bindings:
            bind("--bind", source.resolve(), destination)
        for item in _runtime_roots(command, workdir):
            # A host bind follows symlinks, but the process command and ELF
            # loader retain their original spellings in the new namespace.
            bind("--ro-bind", item.resolve(), item)
        # The candidate can inspect only a read-only cgroup-v2 view.  It needs
        # this for diagnostics, but cannot write controls or migrate itself.
        bind("--ro-bind", Path("/sys/fs/cgroup"))
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
        return _staged_bwrap(
            argv, sources, path_tokens,
            cgroup_name=cgroup_name or f"pdd-{uuid.uuid4().hex}", limits=limits,
            use_systemd_scope=_systemd_scope_usable(limits),
        ), None
    raise RuntimeError("unsupported sandbox platform or mechanism")


def run_supervised(
    command: list[str], *, cwd: Path, timeout: int, env: dict[str, str],
    writable_roots: tuple[Path, ...], writable_files: tuple[Path, ...] = (),
    limits: SupervisorLimits = SupervisorLimits(),
    readable_roots: tuple[Path, ...] = (),
    readable_bindings: tuple[tuple[Path, Path], ...] = (),
    writable_bindings: tuple[tuple[Path, Path], ...] = (),
    temp_directory: Path | None = None,
    result_fifo: Path | None = None,
    result_fd: int = 198,
) -> tuple[subprocess.CompletedProcess[str], bool]:
    """Run sandboxed and terminate marked descendants across session changes."""
    # pylint: disable=consider-using-with,too-many-locals,too-many-branches,too-many-statements
    try:
        cgroup_name = f"pdd-{uuid.uuid4().hex}"
        argv, profile = _sandbox_command(
            command, writable_roots, cwd=cwd, writable_files=writable_files,
            limits=limits, readable_roots=readable_roots,
            readable_bindings=readable_bindings,
            writable_bindings=writable_bindings,
            result_fifo=result_fifo, result_fd=result_fd, cgroup_name=cgroup_name,
        )
    except RuntimeError as exc:
        return subprocess.CompletedProcess(command, 125, "", str(exc)), False
    token = uuid.uuid4().hex
    stdout_file = tempfile.TemporaryFile(mode="w+b")
    stderr_file = tempfile.TemporaryFile(mode="w+b")
    sandbox_environment = env | {
        "PYTHONDONTWRITEBYTECODE": "1",
        "PDD_SUPERVISION_TOKEN": token,
        "PDD_CGROUP_NAME": cgroup_name,
        "TMPDIR": str(temp_directory or writable_roots[0].resolve()),
        "TEMP": str(temp_directory or writable_roots[0].resolve()),
        "TMP": str(temp_directory or writable_roots[0].resolve()),
    }
    library_path = _sandbox_library_path(env)
    if library_path:
        sandbox_environment["LD_LIBRARY_PATH"] = library_path
    try:
        process = subprocess.Popen(
            argv, cwd=cwd, stdout=stdout_file, stderr=stderr_file,
            env=sandbox_environment,
            start_new_session=True,
        )
    except OSError as exc:
        stdout_file.close()
        stderr_file.close()
        return subprocess.CompletedProcess(command, 125, "", str(exc)), False
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
        try:
            cleanup = subprocess.run(
                ["sudo", "-n", str(_SUPERVISOR_EXECUTABLE), "-c", _CGROUP_CLEANUP,
                 cgroup_name], capture_output=True, text=True, check=False,
            )
            cleanup_error = cleanup.stderr if cleanup.returncode != 0 else ""
        except OSError as exc:
            cleanup_error = str(exc)
        if cleanup_error:
            output_limited = True
            stderr_file.write(
                ("protected sandbox cgroup teardown failed: " + cleanup_error).encode()
            )
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
