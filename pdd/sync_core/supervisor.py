"""Fail-closed OS sandbox and complete process-group supervision."""
# pylint: disable=too-many-arguments,too-many-lines

from __future__ import annotations

import hashlib
import inspect
import json
import os
import re
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
_TRUSTED_ROOT_PATH = "/usr/local/sbin:/usr/local/bin:/usr/sbin:/usr/bin:/sbin:/bin"
_SCOPE_PATTERN = re.compile(r"pdd-validator-[0-9a-f]{32}\.scope")


@dataclass(frozen=True)
class SupervisorLimits:
    """Hard limits applied to every untrusted validator process tree."""

    max_output_bytes: int = 16 * 1024 * 1024
    max_writable_bytes: int = 512 * 1024 * 1024
    max_memory_bytes: int = 2 * 1024 * 1024 * 1024
    max_virtual_memory_bytes: int = 2 * 1024 * 1024 * 1024
    max_cpu_seconds: int = 300
    max_processes: int = 128


@dataclass(frozen=True)
class _TrustedTools:
    """Exact privileged executable identities used by one protected run."""

    bwrap: Path
    mount: Path
    setpriv: Path
    sudo: Path
    systemctl: Path
    systemd_run: Path
    umount: Path


@dataclass(frozen=True)
class _ScopePlan:
    """Immutable transient-scope construction and cleanup state."""

    unit_name: str
    control_directory: Path
    helper_source: str
    bwrap_argv: tuple[str, ...]
    sources: tuple[Path, ...]
    staging_targets: tuple[Path, ...]
    tools: _TrustedTools


def _scope_unit_name() -> str:
    """Return an unguessable unit name reserved to one supervisor invocation."""
    return f"pdd-validator-{uuid.uuid4().hex}.scope"


def _validated_scope_unit(unit_name: str) -> str:
    """Reject any unit spelling that could target another systemd object."""
    if _SCOPE_PATTERN.fullmatch(unit_name) is None:
        raise RuntimeError("invalid protected scope unit name")
    return unit_name


def _trusted_executable(name: str) -> Path:
    """Resolve one regular executable from the fixed trusted root PATH."""
    value = shutil.which(name, path=_TRUSTED_ROOT_PATH)
    if value is None:
        raise RuntimeError(f"protected sandbox requires trusted {name}")
    try:
        path = Path(value).resolve(strict=True)
    except OSError as exc:
        raise RuntimeError(f"protected sandbox cannot resolve trusted {name}") from exc
    if not path.is_file() or not os.access(path, os.X_OK):
        raise RuntimeError(f"protected sandbox trusted {name} is not executable")
    return path


def _trusted_tools() -> _TrustedTools:
    """Resolve the complete privileged toolchain once for probe and execution."""
    return _TrustedTools(**{
        name.replace("-", "_"): _trusted_executable(name)
        for name in (
            "bwrap", "mount", "setpriv", "sudo", "systemctl", "systemd-run",
            "umount",
        )
    })


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
    sandbox_commands = {}
    if sys.platform.startswith("linux"):
        for name in (
            "bwrap", "mount", "setpriv", "sudo", "systemctl", "systemd-run",
            "umount",
        ):
            if shutil.which(name, path=_TRUSTED_ROOT_PATH):
                sandbox_commands[name] = _trusted_executable(name)
    for name, value in sandbox_commands.items():
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
        if path.name in {
            "bwrap", "setpriv", "sudo", "systemctl", "systemd-run", "mount", "umount",
        } or any(
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
        "v=[int(x) for x in sys.argv[1:5]];"
        "resource.setrlimit(resource.RLIMIT_AS,(v[0],v[0]));"
        "resource.setrlimit(resource.RLIMIT_CPU,(v[1],v[1]));"
        "resource.setrlimit(resource.RLIMIT_FSIZE,(v[2],v[2]));"
        "resource.setrlimit(resource.RLIMIT_NOFILE,(v[3],v[3]));"
        "os.execvpe(sys.argv[5],sys.argv[5:],os.environ)"
    )
    return [str(_SUPERVISOR_EXECUTABLE), "-c", script, str(limits.max_virtual_memory_bytes),
            str(limits.max_cpu_seconds), str(limits.max_writable_bytes), "256", *command]


def _writable_file_identity(path: Path) -> tuple[int, int, int, int, str]:
    """Return a no-follow identity for one publishable regular file."""
    try:
        metadata = path.lstat()
        if not stat.S_ISREG(metadata.st_mode) or path.is_symlink():
            raise RuntimeError("publishable writable output must be a regular file")
        digest = hashlib.sha256()
        descriptor = os.open(path, os.O_RDONLY | getattr(os, "O_NOFOLLOW", 0))
        try:
            with os.fdopen(descriptor, "rb", closefd=False) as stream:
                for chunk in iter(lambda: stream.read(1024 * 1024), b""):
                    digest.update(chunk)
        finally:
            os.close(descriptor)
        current = path.lstat()
    except OSError as exc:
        raise RuntimeError("publishable writable output is unavailable") from exc
    if (metadata.st_dev, metadata.st_ino, metadata.st_size, metadata.st_mtime_ns) != (
        current.st_dev, current.st_ino, current.st_size, current.st_mtime_ns,
    ):
        raise RuntimeError("publishable writable output changed during validation")
    return (
        current.st_size, stat.S_IMODE(current.st_mode), current.st_uid,
        current.st_gid, digest.hexdigest(),
    )


def _fsync_directory(directory: Path) -> None:
    """Persist directory entry changes on a publication destination filesystem."""
    descriptor = os.open(directory, os.O_RDONLY | getattr(os, "O_DIRECTORY", 0))
    try:
        os.fsync(descriptor)
    finally:
        os.close(descriptor)


def _publish_writable_files(
    publications: tuple[
        tuple[Path, Path, tuple[int, int, int, int, str]], ...
    ],
) -> None:
    """Atomically publish a set of staged files, rolling back the whole set."""
    destinations = tuple(
        destination for _source, destination, _expected in publications
    )
    if len(set(destinations)) != len(destinations):
        raise RuntimeError("writable output publication has duplicate destinations")
    prepared: list[tuple[Path, Path, Path]] = []
    backups: list[tuple[Path, Path]] = []
    installed: set[Path] = set()
    try:
        for source, destination, expected in publications:
            if _writable_file_identity(destination) != expected:
                raise RuntimeError("writable output changed before publication")
            source_identity = _writable_file_identity(source)
            if source_identity[1:4] != expected[1:4]:
                raise RuntimeError("staged writable output metadata changed")
            descriptor, temporary_name = tempfile.mkstemp(
                prefix=".pdd-publish-", dir=destination.parent
            )
            temporary = Path(temporary_name)
            try:
                with source.open("rb") as source_stream, os.fdopen(
                    descriptor, "wb"
                ) as destination_stream:
                    shutil.copyfileobj(source_stream, destination_stream)
                    destination_stream.flush()
                    os.fchmod(destination_stream.fileno(), expected[1])
                    os.fchown(destination_stream.fileno(), expected[2], expected[3])
                    os.fsync(destination_stream.fileno())
            except BaseException:
                temporary.unlink(missing_ok=True)
                raise
            prepared.append((temporary, destination, source))
            replacement_identity = _writable_file_identity(temporary)
            if replacement_identity != (
                source_identity[0], expected[1], expected[2], expected[3],
                source_identity[4],
            ):
                raise RuntimeError("staged writable output replacement is invalid")
        for _temporary, destination, _source in prepared:
            descriptor, backup_name = tempfile.mkstemp(
                prefix=".pdd-rollback-", dir=destination.parent
            )
            os.close(descriptor)
            backup = Path(backup_name)
            backup.unlink()
            os.link(destination, backup, follow_symlinks=False)
            backups.append((backup, destination))
            expected = next(
                identity for _staged, item, identity in publications
                if item == destination
            )
            if _writable_file_identity(backup) != expected:
                raise RuntimeError("writable output changed before rollback snapshot")
        for temporary, destination, _source in prepared:
            os.replace(temporary, destination)
            installed.add(destination)
        for _temporary, destination, source in prepared:
            published = _writable_file_identity(destination)
            source_identity = _writable_file_identity(source)
            if published[0] != source_identity[0] or published[4] != source_identity[4]:
                raise RuntimeError("published writable output verification failed")
        for parent in {destination.parent for destination in destinations}:
            _fsync_directory(parent)
    except BaseException as exc:
        rollback_errors = []
        for backup, destination in reversed(backups):
            try:
                if destination in installed:
                    os.replace(backup, destination)
                else:
                    backup.unlink(missing_ok=True)
            except OSError as rollback_exc:
                rollback_errors.append(str(rollback_exc))
        for temporary, _destination, _source in prepared:
            try:
                temporary.unlink(missing_ok=True)
            except OSError as cleanup_exc:
                rollback_errors.append(str(cleanup_exc))
        for parent in {destination.parent for destination in destinations}:
            try:
                _fsync_directory(parent)
            except OSError as rollback_exc:
                rollback_errors.append(str(rollback_exc))
        if rollback_errors:
            raise RuntimeError("writable output publication rollback failed") from exc
        raise RuntimeError("writable output publication failed") from exc
    for backup, _destination in backups:
        backup.unlink()


def _staged_bwrap(
    argv: list[str], sources: list[Path], path_tokens: list[str], *,
    writable_roots: tuple[Path, ...], writable_specs: list[tuple[str, int, str]],
    publish_indexes: tuple[int, ...],
    result_fifo: Path | None,
    unit_name: str, control_directory: Path, limits: SupervisorLimits,
    tools: _TrustedTools,
) -> tuple[list[str], _ScopePlan]:
    """Build one scope-held helper that releases Bubblewrap after verification."""
    unit_name = _validated_scope_unit(unit_name)
    staging_targets = tuple(
        control_directory / "binds" / str(index) for index in range(len(sources))
    )
    publication_source = "\n\n".join(
        inspect.getsource(function) for function in (
            _writable_file_identity, _fsync_directory, _publish_writable_files,
        )
    )
    helper = "\n".join((
        "from __future__ import annotations",
        "import hashlib,json,os,pathlib,shutil,stat,subprocess,sys,tempfile,time",
        "from pathlib import Path",
        publication_source,
        "control=pathlib.Path(sys.argv[1]); mount=sys.argv[2]; umount=sys.argv[3]",
        "writable_roots=[pathlib.Path(value) for value in json.loads(sys.argv[4])]",
        "writable_specs=json.loads(sys.argv[5]); publish_indexes=json.loads(sys.argv[6])",
        "result_fifo=sys.argv[7] or None",
        "limits=json.loads(sys.argv[-1])",
        "path_tokens=json.loads(sys.argv[-5]); argv=json.loads(sys.argv[-4]); "
        "paths=json.loads(sys.argv[-3])",
        "targets=[control/'binds'/str(index) for index in range(len(paths))]",
        "staged=[]; result=None; cleanup_error=None; result_write=None",
        "def wait_for(name):",
        " path=control/name",
        " while not path.exists(): time.sleep(.01)",
        "def own_cgroup():",
        " lines=pathlib.Path('/proc/self/cgroup').read_text(encoding='ascii').splitlines()",
        " relative=next((line[3:] for line in lines if line.startswith('0::')),None)",
        " if not relative: raise RuntimeError('protected scope has no cgroup-v2 membership')",
        " source=pathlib.Path('/sys/fs/cgroup')/relative.lstrip('/')",
        " if source == pathlib.Path('/sys/fs/cgroup') or not source.is_dir(): "
        "raise RuntimeError('protected scope cgroup is invalid')",
        " return source",
        "def validate_tree(root):",
        " total=0",
        " for path in (root,*root.rglob('*')):",
        "  metadata=path.lstat()",
        "  if stat.S_ISLNK(metadata.st_mode): "
        "raise RuntimeError('writable tree contains symlink')",
        "  if stat.S_ISREG(metadata.st_mode): total+=metadata.st_size",
        "  elif not stat.S_ISDIR(metadata.st_mode): "
        "raise RuntimeError('writable tree contains special file')",
        " return total",
        "def copy_owned(source,target):",
        " if source.is_dir(): shutil.copytree(source,target)",
        " else: shutil.copy2(source,target)",
        " pairs=[(source,target)]",
        " if source.is_dir(): pairs.extend((item,target/item.relative_to(source)) "
        "for item in source.rglob('*'))",
        " for original,copied in pairs:",
        "  metadata=original.stat(follow_symlinks=False)",
        "  os.chown(copied,metadata.st_uid,metadata.st_gid,follow_symlinks=False)",
        "try:",
        " writable_target=control/'binds'/'writable'",
        " subprocess.run([mount,'-t','tmpfs','-o',"
        "f\"size={limits['writable']},mode=0700,nosuid,nodev\",'tmpfs',"
        "str(writable_target)],check=True)",
        " staged.append(writable_target)",
        " mount_lines=pathlib.Path('/proc/self/mountinfo').read_text("
        "encoding='utf-8').splitlines()",
        " mount_fields=[line.split() for line in mount_lines]",
        " mounted=next((fields for fields in mount_fields if len(fields)>6 and "
        "pathlib.Path(fields[4])==writable_target),None)",
        " if mounted is None or '-' not in mounted or "
        "mounted[mounted.index('-')+1]!='tmpfs': "
        "raise RuntimeError('writable tmpfs mount probe failed')",
        " capacity=os.statvfs(writable_target).f_blocks*"
        "os.statvfs(writable_target).f_frsize",
        " if capacity > limits['writable']+os.sysconf('SC_PAGE_SIZE'): "
        "raise RuntimeError('writable tmpfs size probe failed')",
        " publish_expected={index:_writable_file_identity(writable_roots[index]) "
        "for index in publish_indexes}",
        " writable_paths=[]",
        " for index,source in enumerate(writable_roots):",
        "  target=writable_target/str(index); copy_owned(source,target); "
        "writable_paths.append(target)",
        " for index in publish_indexes:",
        "  if _writable_file_identity(writable_paths[index]) != "
        "publish_expected[index]: raise RuntimeError('writable output staging changed')",
        " if sum(validate_tree(path) for path in writable_paths) > "
        "limits['writable']: raise RuntimeError('initial writable quota exceeded')",
        " for source,target in zip(paths,targets):",
        "  subprocess.run([mount,'--bind',source,str(target)],check=True)",
        "  staged.append(target)",
        " path_map={token:str(targets[index]) for index,token in enumerate(path_tokens)}",
        " for token,index,relative in writable_specs: "
        "path_map[token]=str(writable_paths[index]/relative)",
        " argv=[path_map.get(value,value) for value in argv]",
        " cgroup_target=control/'binds'/'cgroup'",
        " subprocess.run([mount,'--bind',str(own_cgroup()),str(cgroup_target)],check=True)",
        " staged.append(cgroup_target)",
        " subprocess.run([umount,str(cgroup_target)],check=True)",
        " staged.pop()",
        " subprocess.run([mount,'--bind',str(own_cgroup()),str(cgroup_target)],check=True)",
        " staged.append(cgroup_target)",
        " argv=[str(cgroup_target) if value == '@PDD-CGROUP@' else value for value in argv]",
        " if result_fifo:",
        "  result_write=os.open(result_fifo,os.O_WRONLY|os.O_CLOEXEC)",
        "  os.unlink(result_fifo)",
        "  os.dup2(result_write,3,inheritable=True)",
        " (control/'ready').write_text('ready',encoding='ascii')",
        " wait_for('start')",
        " pid=os.fork()",
        " if pid == 0:",
        "  if result_fifo: os.set_inheritable(3,True)",
        "  os.execvpe(argv[0],argv,os.environ)",
        " _wait,status=os.waitpid(pid,0)",
        " result=os.waitstatus_to_exitcode(status)",
        " if sum(validate_tree(path) for path in writable_paths) > "
        "limits['writable']: raise RuntimeError('final writable quota exceeded')",
        " publications=tuple((writable_paths[index],writable_roots[index],"
        "publish_expected[index]) for index in publish_indexes)",
        " _publish_writable_files(publications)",
        " temporary=control/'result.tmp'",
        " temporary.write_text(json.dumps({'returncode':result}),encoding='ascii')",
        " os.replace(temporary,control/'result.json')",
        " wait_for('finish')",
        "finally:",
        " if result_write is not None: os.close(result_write)",
        " for target in reversed(staged):",
        "  completed=subprocess.run([umount,str(target)],capture_output=True,"
        "text=True,check=False)",
        "  if completed.returncode != 0: cleanup_error=completed.stderr or 'umount failed'",
        "if cleanup_error:",
        " (control/'cleanup-error').write_text(cleanup_error,encoding='utf-8')",
        " raise SystemExit(125)",
        "raise SystemExit(result if result is not None and result >= 0 else "
        "(128-result if result is not None else 125))",
    ))
    plan = _ScopePlan(
        unit_name, control_directory, helper, tuple(argv), tuple(sources),
        (*staging_targets, control_directory / "binds" / "writable",
         control_directory / "binds" / "cgroup"), tools,
    )
    command = [
        str(tools.sudo), "-n", "-E", str(tools.systemd_run), "--scope", "--quiet",
        f"--unit={unit_name}", f"--property=MemoryMax={limits.max_memory_bytes}",
        "--property=MemorySwapMax=0", f"--property=TasksMax={limits.max_processes}",
        "--property=OOMPolicy=kill", "--property=KillMode=control-group", "--",
        str(_SUPERVISOR_EXECUTABLE), "-c", helper, str(control_directory),
        str(tools.mount), str(tools.umount),
        json.dumps([str(path) for path in writable_roots]), json.dumps(writable_specs),
        json.dumps(publish_indexes), str(result_fifo or ""),
        json.dumps(path_tokens), json.dumps(argv),
        json.dumps([str(path) for path in sources]), unit_name,
        json.dumps({"memory": limits.max_memory_bytes, "pids": limits.max_processes,
                    "writable": limits.max_writable_bytes}),
    ]
    return command, plan


def _private_result_command(
    command: list[str], result_fd: int, source_fd: int = 3,
) -> list[str]:
    """Move the helper-opened private result descriptor to its fixed number."""
    script = (
        "import os,sys;"
        "source=int(sys.argv[1]);target=int(sys.argv[2]);"
        "os.dup2(source,target);"
        "os.close(source) if source!=target else None;"
        "os.execvpe(sys.argv[3],sys.argv[3:],os.environ)"
    )
    return [str(_SUPERVISOR_EXECUTABLE), "-c", script,
            str(source_fd), str(result_fd), *command]

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
    """Measure logical bytes for diagnostics, failing on incomplete traversal."""
    total = 0
    try:
        for root in roots:
            paths = (root, *root.rglob("*")) if root.is_dir() else (root,)
            for path in paths:
                metadata = path.lstat()
                if stat.S_ISLNK(metadata.st_mode):
                    raise RuntimeError("writable accounting rejects symlinks")
                if stat.S_ISREG(metadata.st_mode):
                    total += metadata.st_size
                elif not stat.S_ISDIR(metadata.st_mode):
                    raise RuntimeError("writable accounting rejects special files")
    except OSError as exc:
        raise RuntimeError("writable accounting failed") from exc
    return total


def _writable_storage_roots(paths: tuple[Path, ...]) -> tuple[Path, ...]:
    """Return disjoint real roots mirrored into one bounded writable filesystem."""
    resolved = []
    for path in paths:
        try:
            if path.is_symlink():
                raise RuntimeError("writable storage root cannot be a symlink")
            value = path.resolve(strict=True)
        except OSError as exc:
            raise RuntimeError("writable storage root is unavailable") from exc
        if not (value.is_dir() or value.is_file()):
            raise RuntimeError("writable storage root must be a regular file or directory")
        resolved.append(value)
    roots = []
    for path in sorted(set(resolved), key=lambda item: (len(item.parts), str(item))):
        if not any(path == root or path.is_relative_to(root) for root in roots):
            roots.append(path)
    return tuple(roots)


def _writable_publication_files(
    paths: tuple[Path, ...], storage_roots: tuple[Path, ...],
) -> tuple[Path, ...]:
    """Validate distinct regular outputs that do not overlap ephemeral storage."""
    resolved = []
    identities = []
    for path in paths:
        try:
            if path.is_symlink():
                raise RuntimeError("publishable writable output cannot be a symlink")
            value = path.resolve(strict=True)
        except OSError as exc:
            raise RuntimeError("publishable writable output is unavailable") from exc
        if not value.is_file():
            raise RuntimeError("publishable writable output must be a regular file")
        resolved.append(value)
        metadata = value.stat()
        identities.append((metadata.st_dev, metadata.st_ino))
    if len(set(resolved)) != len(resolved) or len(set(identities)) != len(identities):
        raise RuntimeError("publishable writable outputs contain duplicates")
    root_identities = {
        (metadata.st_dev, metadata.st_ino)
        for root in storage_roots
        if stat.S_ISREG((metadata := root.stat()).st_mode)
    }
    if root_identities.intersection(identities):
        raise RuntimeError("publishable writable output overlaps a writable root")
    if any(
        path == root or path.is_relative_to(root) or root.is_relative_to(path)
        for path in resolved for root in storage_roots
    ):
        raise RuntimeError("publishable writable output overlaps a writable root")
    return tuple(resolved)


def _root_environment() -> dict[str, str]:
    """Return the fixed environment used for every privileged tool invocation."""
    return {"PATH": _TRUSTED_ROOT_PATH, "LANG": "C", "LC_ALL": "C"}


def _root_run(
    tools: _TrustedTools, arguments: list[str], *, check: bool = False,
) -> subprocess.CompletedProcess[str]:
    """Invoke systemctl through the exact sudo/systemctl identities already probed."""
    return subprocess.run(
        [str(tools.sudo), "-n", str(tools.systemctl), *arguments],
        capture_output=True, text=True, check=check, env=_root_environment(),
    )


def _scope_properties(unit_name: str, tools: _TrustedTools) -> dict[str, str]:
    """Read authoritative transient-scope state without collecting the unit."""
    unit_name = _validated_scope_unit(unit_name)
    names = (
        "LoadState", "ActiveState", "ControlGroup", "MemoryMax",
        "MemorySwapMax", "TasksMax", "OOMPolicy", "KillMode", "Result",
        "OOMKilled",
    )
    completed = _root_run(
        tools, ["show", unit_name, *(f"--property={name}" for name in names)],
    )
    if completed.returncode != 0:
        raise RuntimeError(
            "protected scope probe failed: " + (completed.stderr.strip() or "systemctl show failed")
        )
    properties = {}
    for line in completed.stdout.splitlines():
        name, separator, value = line.partition("=")
        if separator:
            properties[name] = value
    return properties


def _scope_cgroup(properties: dict[str, str]) -> Path:
    """Validate the systemd-owned workload cgroup path."""
    relative = properties.get("ControlGroup", "")
    if not relative.startswith("/") or relative == "/" or ".." in Path(relative).parts:
        raise RuntimeError("protected scope has invalid ControlGroup")
    root = Path("/sys/fs/cgroup")
    path = root / relative.lstrip("/")
    try:
        if not path.resolve(strict=True).is_relative_to(root.resolve(strict=True)):
            raise RuntimeError("protected scope escaped cgroup-v2 root")
    except OSError as exc:
        raise RuntimeError("protected scope cgroup does not exist") from exc
    return path


def _cgroup_events(cgroup: Path, filename: str) -> dict[str, int]:
    """Read one kernel cgroup event file as non-negative counters."""
    try:
        lines = (cgroup / filename).read_text(encoding="ascii").splitlines()
        events = {name: int(value) for name, value in (line.split() for line in lines)}
    except (OSError, ValueError) as exc:
        raise RuntimeError(f"protected scope cannot read {filename}") from exc
    if any(value < 0 for value in events.values()):
        raise RuntimeError(f"protected scope has invalid {filename}")
    return events


def _probe_scope(
    plan: _ScopePlan, limits: SupervisorLimits,
) -> tuple[Path, dict[str, int], dict[str, int]]:
    """Prove systemd and kernel limits before releasing the candidate."""
    properties = _scope_properties(plan.unit_name, plan.tools)
    expected = {
        "LoadState": "loaded", "ActiveState": "active",
        "MemoryMax": str(limits.max_memory_bytes), "MemorySwapMax": "0",
        "TasksMax": str(limits.max_processes), "OOMPolicy": "kill",
        "KillMode": "control-group",
    }
    differences = [
        f"{name}={properties.get(name, '<missing>')}"
        for name, value in expected.items() if properties.get(name) != value
    ]
    if differences:
        raise RuntimeError("protected scope properties unverified: " + ", ".join(differences))
    cgroup = _scope_cgroup(properties)
    kernel_limits = {
        "memory.max": str(limits.max_memory_bytes), "memory.swap.max": "0",
        "memory.oom.group": "1", "pids.max": str(limits.max_processes),
    }
    for filename, expected_value in kernel_limits.items():
        try:
            actual = (cgroup / filename).read_text(encoding="ascii").strip()
        except OSError as exc:
            raise RuntimeError(f"protected scope cannot read {filename}") from exc
        if actual != expected_value:
            raise RuntimeError(
                f"protected scope kernel limit mismatch: {filename}={actual}"
            )
    return cgroup, _cgroup_events(cgroup, "memory.events"), _cgroup_events(cgroup, "pids.events")


def _stop_scope(unit_name: str, tools: _TrustedTools) -> None:
    """Kill the exact whole scope and prove that systemd removed it."""
    unit_name = _validated_scope_unit(unit_name)
    initial = _root_run(tools, ["show", unit_name, "--property=LoadState"])
    if initial.stdout.strip() == "LoadState=not-found" or (
        initial.returncode != 0
        and any(value in initial.stderr.lower() for value in ("not loaded", "not found"))
    ):
        return
    if initial.returncode != 0:
        raise RuntimeError(
            "protected scope teardown failed: "
            + (initial.stderr.strip() or "cannot probe scope")
        )
    errors = []
    for arguments in (
        ["kill", "--kill-whom=all", "--signal=SIGKILL", unit_name],
        ["stop", unit_name],
        ["reset-failed", unit_name],
    ):
        completed = _root_run(tools, arguments)
        if completed.returncode != 0 and "not loaded" not in completed.stderr.lower():
            errors.append(completed.stderr.strip() or " ".join(arguments) + " failed")
    deadline = time.monotonic() + 5
    while time.monotonic() < deadline:
        completed = _root_run(tools, ["show", unit_name, "--property=LoadState"])
        output = completed.stdout.strip()
        if completed.returncode != 0 or output == "LoadState=not-found":
            break
        time.sleep(.05)
    else:
        errors.append("scope unit was not removed")
    if errors:
        raise RuntimeError("protected scope teardown failed: " + "; ".join(errors))


def _prepare_staging(plan: _ScopePlan) -> None:
    """Create private bind targets before the privileged scope helper starts."""
    binds = plan.control_directory / "binds"
    binds.mkdir(mode=0o700)
    for source, target in zip(plan.sources, plan.staging_targets[:-2]):
        if source.is_dir():
            target.mkdir(mode=0o700)
        else:
            target.touch(mode=0o600)
    plan.staging_targets[-2].mkdir(mode=0o700)
    plan.staging_targets[-1].mkdir(mode=0o700)


def _mounted_paths() -> set[Path]:
    """Return host mountpoints using the kernel's escaped mount table."""
    paths = set()
    try:
        lines = Path("/proc/self/mountinfo").read_text(encoding="utf-8").splitlines()
    except OSError:
        return paths
    for line in lines:
        fields = line.split()
        if len(fields) > 4:
            paths.add(Path(fields[4].replace("\\040", " ").replace("\\134", "\\")))
    return paths


def _cleanup_staging(plan: _ScopePlan) -> None:
    """Remove any helper mounts left after authoritative scope termination."""
    errors = []
    for target in reversed(plan.staging_targets):
        if target not in _mounted_paths():
            continue
        completed = subprocess.run(
            [str(plan.tools.sudo), "-n", str(plan.tools.umount), str(target)],
            capture_output=True, text=True, check=False, env=_root_environment(),
        )
        if completed.returncode != 0:
            errors.append(completed.stderr.strip() or f"cannot unmount {target}")
    if any(target in _mounted_paths() for target in plan.staging_targets):
        errors.append("protected bind staging remains mounted")
    if errors:
        raise RuntimeError("protected scope staging cleanup failed: " + "; ".join(errors))


def _sandbox_command(
    command: list[str], writable_roots: tuple[Path, ...], *, cwd: Path | None = None,
    writable_files: tuple[Path, ...] = (), limits: SupervisorLimits = SupervisorLimits(),
    readable_roots: tuple[Path, ...] = (),
    readable_bindings: tuple[tuple[Path, Path], ...] = (),
    writable_bindings: tuple[tuple[Path, Path], ...] = (),
    result_fifo: Path | None = None,
    result_fd: int = 198,
    unit_name: str | None = None,
    control_directory: Path | None = None,
) -> tuple[list[str], _ScopePlan]:
    # pylint: disable=too-many-locals,too-many-branches,too-many-statements
    """Return an explicitly detected macOS/Linux sandbox command."""
    if sys.platform == "darwin":
        raise RuntimeError(
            "unsupported protected sandbox: macOS cannot prove process lifetime isolation"
        )
    if sys.platform.startswith("linux"):
        tools = _trusted_tools()
        if os.getuid() == 0:
            raise RuntimeError(
                "protected sandbox requires a non-root caller so process limits "
                "remain kernel-enforced"
            )
        if subprocess.run(
            [str(tools.sudo), "-n", str(_SUPERVISOR_EXECUTABLE), "-c", "pass"],
            capture_output=True, check=False, env=_root_environment(),
        ).returncode != 0:
            raise RuntimeError("protected sandbox requires privileged bind staging")
        workdir = (cwd or Path.cwd()).resolve()
        writable_sources = tuple(
            source for source, _destination in writable_bindings
        ) + writable_roots
        ephemeral_roots = _writable_storage_roots(writable_sources)
        publication_files = _writable_publication_files(
            writable_files, ephemeral_roots
        )
        storage_roots = (*ephemeral_roots, *publication_files)
        publish_indexes = tuple(range(len(ephemeral_roots), len(storage_roots)))
        if _writable_size(storage_roots) > limits.max_writable_bytes:
            raise RuntimeError("initial writable quota exceeded")
        argv = [str(tools.bwrap), "--unshare-ipc", "--unshare-pid", "--unshare-net",
                "--unshare-uts", "--unshare-cgroup", "--die-with-parent", "--new-session",
                "--tmpfs", "/", "--proc", "/proc", "--dir", "/tmp",
                "--dir", "/sys", "--dir", "/sys/fs", "--dir", "/sys/fs/cgroup"]
        sources: list[Path] = []
        path_tokens: list[str] = []
        writable_specs: list[tuple[str, int, str]] = []
        destination_dirs = {Path("/tmp")}
        mounted: dict[Path, tuple[str, Path]] = {}

        def stage_source(source: Path, writable: bool = False) -> str:
            token = f"@PDD-PATH-{uuid.uuid4().hex}@"
            if writable:
                for index, root in enumerate(storage_roots):
                    if source == root or source.is_relative_to(root):
                        relative = source.relative_to(root).as_posix() or "."
                        writable_specs.append((token, index, relative))
                        return token
                raise RuntimeError("writable source is outside bounded storage")
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
            argv.extend((option, stage_source(source, option == "--bind"), str(destination)))
            if destination.is_dir():
                destination_dirs.add(destination)

        for source, destination in writable_bindings:
            bind("--bind", source.resolve(), destination)
        for item in _runtime_roots(command, workdir):
            # A host bind follows symlinks, but the process command and ELF
            # loader retain their original spellings in the new namespace.
            bind("--ro-bind", item.resolve(), item)
        # The helper replaces this placeholder with only its systemd scope.
        argv.extend(("--ro-bind", "@PDD-CGROUP@", "/sys/fs/cgroup"))
        # ``setpriv`` executes after the namespace root is installed, so bind
        # it and its ELF closure directly even when PATH resolution differs.
        if tools.setpriv:
            for item in (tools.setpriv, *_linked_libraries(tools.setpriv)):
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
        argv.extend(("--chdir", str(workdir)))
        drop = (
            [str(tools.setpriv), "--reuid", str(os.getuid()), "--regid", str(os.getgid()),
             "--clear-groups", "--"]
        )
        sandboxed = _limited_command(command, limits)
        if result_fifo is not None:
            argv[1:1] = ["--preserve-fds", "1"]
            sandboxed = _private_result_command(sandboxed, result_fd, 3)
        argv.extend(("--", *drop, *sandboxed))
        return _staged_bwrap(
            argv, sources, path_tokens, writable_roots=storage_roots,
            writable_specs=writable_specs, publish_indexes=publish_indexes,
            result_fifo=result_fifo,
            unit_name=unit_name or _scope_unit_name(),
            control_directory=control_directory or (
                Path(tempfile.gettempdir()) / f"pdd-scope-{uuid.uuid4().hex}"
            ),
            limits=limits, tools=tools,
        )
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
    """Run only after proving one aggregate systemd scope, then remove it."""
    # pylint: disable=consider-using-with,too-many-locals,too-many-branches,too-many-statements
    token = uuid.uuid4().hex
    unit_name = _scope_unit_name()
    stdout_buffer = bytearray()
    stderr_buffer = bytearray()
    diagnostics = bytearray()
    output_lock = threading.Lock()
    output_size = 0
    output_overflow = False
    output_threads: list[threading.Thread] = []
    timed_out = False
    failed_closed = False
    surviving = False
    candidate_returncode: int | None = None
    process: subprocess.Popen[bytes] | None = None
    plan: _ScopePlan | None = None
    cgroup: Path | None = None
    memory_before: dict[str, int] = {}
    pids_before: dict[str, int] = {}
    tracked: dict[int, str | None] = {}
    tracking_done = threading.Event()
    tracker: threading.Thread | None = None
    phase = "construction"

    def add_diagnostic(value: str) -> None:
        data = value.encode("utf-8", errors="replace")
        remaining = max(0, limits.max_output_bytes - len(diagnostics))
        diagnostics.extend(data[:remaining])

    def drain_output(stream, buffer: bytearray) -> None:
        nonlocal output_size, output_overflow
        while chunk := stream.read(65536):
            with output_lock:
                remaining = max(0, limits.max_output_bytes - output_size)
                buffer.extend(chunk[:remaining])
                output_size += len(chunk)
                if len(chunk) > remaining:
                    output_overflow = True

    def limit_error() -> str | None:
        with output_lock:
            exceeded = output_overflow
            observed = output_size
        if exceeded:
            return (
                "protected supervisor output quota exceeded: "
                f"{observed}>{limits.max_output_bytes}"
            )
        return None

    def fail_for_limit() -> bool:
        nonlocal failed_closed
        error = limit_error()
        if error is None:
            return False
        failed_closed = True
        add_diagnostic(f"protected supervisor phase={phase}: {error}\n")
        return True

    def record_events() -> None:
        nonlocal failed_closed
        if cgroup is None:
            return
        memory_after = None
        pids_after = None
        try:
            memory_after = _cgroup_events(cgroup, "memory.events")
            pids_after = _cgroup_events(cgroup, "pids.events")
        except RuntimeError:
            pass
        oom_delta = 0
        pids_delta = 0
        if memory_after is not None:
            oom_delta = max(
                memory_after.get("oom", 0) - memory_before.get("oom", 0),
                memory_after.get("oom_kill", 0) - memory_before.get("oom_kill", 0),
            )
        if pids_after is not None:
            pids_delta = pids_after.get("max", 0) - pids_before.get("max", 0)
        if oom_delta <= 0:
            try:
                properties = _scope_properties(plan.unit_name, plan.tools)
                if properties.get("Result") == "oom-kill" or properties.get("OOMKilled") == "yes":
                    oom_delta = 1
            except RuntimeError:
                pass
        if oom_delta > 0:
            add_diagnostic(f"cgroup memory.events oom delta={oom_delta}\n")
        if pids_delta > 0:
            add_diagnostic(f"cgroup pids.events max delta={pids_delta}\n")

    try:
        with tempfile.TemporaryDirectory(prefix="pdd-scope-") as control_value:
            control = Path(control_value)
            try:
                argv, plan = _sandbox_command(
                    command, writable_roots, cwd=cwd, writable_files=writable_files,
                    limits=limits, readable_roots=readable_roots,
                    readable_bindings=readable_bindings,
                    writable_bindings=writable_bindings,
                    result_fifo=result_fifo, result_fd=result_fd,
                    unit_name=unit_name, control_directory=control,
                )
                _prepare_staging(plan)
            except (OSError, RuntimeError) as exc:
                return subprocess.CompletedProcess(
                    command, 125, "", f"protected supervisor phase=construction: {exc}"
                ), False
            sandbox_environment = env | {
                "PATH": _TRUSTED_ROOT_PATH,
                "PYTHONDONTWRITEBYTECODE": "1",
                "PDD_SUPERVISION_TOKEN": token,
                "TMPDIR": str(temp_directory or writable_roots[0].resolve()),
                "TEMP": str(temp_directory or writable_roots[0].resolve()),
                "TMP": str(temp_directory or writable_roots[0].resolve()),
            }
            library_path = _sandbox_library_path(env)
            if library_path:
                sandbox_environment["LD_LIBRARY_PATH"] = library_path
            try:
                process = subprocess.Popen(
                    argv, cwd=cwd, stdout=subprocess.PIPE, stderr=subprocess.PIPE,
                    env=sandbox_environment, start_new_session=True,
                )
            except OSError as exc:
                _cleanup_staging(plan)
                return subprocess.CompletedProcess(
                    command, 125, "", f"protected supervisor phase=launch: {exc}"
                ), False

            assert process.stdout is not None and process.stderr is not None
            output_threads = [
                threading.Thread(
                    target=drain_output, args=(process.stdout, stdout_buffer), daemon=True
                ),
                threading.Thread(
                    target=drain_output, args=(process.stderr, stderr_buffer), daemon=True
                ),
            ]
            for output_thread in output_threads:
                output_thread.start()

            def track_process_tree() -> None:
                while not tracking_done.wait(0.005):
                    for pid in _process_descendants(process.pid):
                        tracked.setdefault(pid, _process_identity(pid))

            tracker = threading.Thread(target=track_process_tree, daemon=True)
            tracker.start()
            deadline = time.monotonic() + timeout
            phase = "scope-setup"
            try:
                while not (control / "ready").exists():
                    if process.poll() is not None:
                        raise RuntimeError("protected scope exited before verification")
                    if time.monotonic() >= deadline:
                        timed_out = True
                        break
                    if fail_for_limit():
                        break
                    time.sleep(.01)
                if not timed_out and not failed_closed:
                    cgroup, memory_before, pids_before = _probe_scope(plan, limits)
                    (control / "start").write_text("start", encoding="ascii")
                    phase = "candidate-execution"
                    while not (control / "result.json").exists():
                        if process.poll() is not None:
                            break
                        if time.monotonic() >= deadline:
                            timed_out = True
                            break
                        if fail_for_limit():
                            break
                        time.sleep(.01)
                    if (control / "result.json").exists():
                        phase = "result-handoff"
                        payload = json.loads(
                            (control / "result.json").read_text(encoding="ascii")
                        )
                        candidate_returncode = int(payload["returncode"])
                        fail_for_limit()
                    record_events()
                    if candidate_returncode is None and not timed_out and not failed_closed:
                        failed_closed = True
                        add_diagnostic(
                            "protected supervisor phase=candidate-execution: "
                            "scope produced no candidate result\n"
                        )
                    if process.poll() is None and not timed_out and not failed_closed:
                        (control / "finish").write_text("finish", encoding="ascii")
                        try:
                            process.wait(timeout=5)
                        except subprocess.TimeoutExpired:
                            failed_closed = True
                            add_diagnostic(
                                "protected supervisor result-handoff did not finish\n"
                            )
            except (OSError, ValueError, KeyError, RuntimeError) as exc:
                failed_closed = True
                add_diagnostic(f"protected supervisor phase={phase}: {exc}\n")
            finally:
                if timed_out:
                    add_diagnostic(f"protected supervisor timeout phase={phase}\n")
                if cgroup is None and process.poll() is None:
                    try:
                        os.killpg(process.pid, signal.SIGKILL)
                    except ProcessLookupError:
                        pass
                    process.wait()
                try:
                    _stop_scope(plan.unit_name, plan.tools)
                except RuntimeError as exc:
                    failed_closed = True
                    add_diagnostic(f"protected supervisor phase=scope-cleanup: {exc}\n")
                if process.poll() is None:
                    try:
                        os.killpg(process.pid, signal.SIGKILL)
                    except ProcessLookupError:
                        pass
                process.wait()
                try:
                    _cleanup_staging(plan)
                except RuntimeError as exc:
                    failed_closed = True
                    add_diagnostic(f"protected supervisor phase=mount-cleanup: {exc}\n")
    finally:
        tracking_done.set()
        if tracker is not None:
            tracker.join(timeout=1)
        for output_thread in output_threads:
            output_thread.join(timeout=1)
            if output_thread.is_alive():
                failed_closed = True
                add_diagnostic("protected supervisor output drain did not finish\n")
        observed = set()
        if process is not None:
            observed = _supervised_descendants(token)
            observed.discard(process.pid)
        for pid in observed:
            tracked.setdefault(pid, _process_identity(pid))
        descendants = _live_processes(tracked)
        if descendants:
            surviving = True
            failed_closed = True
            for pid in descendants:
                try:
                    os.kill(pid, signal.SIGKILL)
                except ProcessLookupError:
                    pass

    stdout_bytes = bytes(stdout_buffer)
    remaining = max(0, limits.max_output_bytes - len(stdout_bytes))
    stderr_bytes = bytes(stderr_buffer[:remaining])
    remaining -= len(stderr_bytes)
    stderr_bytes += bytes(diagnostics[:remaining])
    if output_overflow:
        failed_closed = True
    return subprocess.CompletedProcess(
        command,
        125 if failed_closed else (124 if timed_out else candidate_returncode),
        stdout_bytes.decode("utf-8", errors="replace"),
        stderr_bytes.decode("utf-8", errors="replace"),
    ), surviving
