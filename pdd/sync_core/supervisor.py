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
from enum import Enum
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


class TerminationKind(str, Enum):
    """Trusted reason the supervised process stopped."""

    EXIT = "exit"
    SIGNAL = "signal"
    TIMEOUT = "timeout"
    RESOURCE_LIMIT = "resource-limit"
    SANDBOX_ERROR = "sandbox-error"


@dataclass(frozen=True)
class SupervisorTermination:
    """Typed termination evidence retained outside candidate-controlled output."""

    kind: TerminationKind
    exit_code: int | None = None
    signal_number: int | None = None
    timeout_seconds: int | None = None
    resource_limit: str | None = None


class SupervisedCompletedProcess(subprocess.CompletedProcess[str]):  # pylint: disable=too-few-public-methods
    """Completed process carrying trusted supervisor termination evidence."""

    termination: SupervisorTermination

    def __init__(
        self,
        args: list[str],
        returncode: int,
        stdout: str,
        stderr: str,
        *,
        termination: SupervisorTermination,
    ) -> None:
        super().__init__(args, returncode, stdout, stderr)
        self.termination = termination


def _supervised_result(
    command: list[str],
    returncode: int,
    stdout: str,
    stderr: str,
    termination: SupervisorTermination,
) -> SupervisedCompletedProcess:
    """Construct one subprocess-compatible result with trusted termination data."""
    return SupervisedCompletedProcess(
        command, returncode, stdout, stderr, termination=termination
    )


def _termination_evidence(
    returncode: int,
    *,
    timed_out: bool,
    timeout_seconds: int,
    resource_limit: str | None,
) -> SupervisorTermination:
    """Classify only termination causes observed by the trusted supervisor."""
    if resource_limit is not None:
        return SupervisorTermination(
            TerminationKind.RESOURCE_LIMIT, resource_limit=resource_limit
        )
    if timed_out:
        return SupervisorTermination(
            TerminationKind.TIMEOUT, timeout_seconds=timeout_seconds
        )
    if returncode < 0:
        signal_number = -returncode
        return SupervisorTermination(
            TerminationKind.SIGNAL,
            signal_number=signal_number,
        )
    return SupervisorTermination(TerminationKind.EXIT, exit_code=returncode)


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
    """Measure one executable fd and reject mutable path ancestry."""
    descriptor = None
    try:
        resolved = path.resolve(strict=True)
        if require_root:
            _validate_trusted_executable_chain(resolved)
        descriptor = os.open(
            resolved, os.O_RDONLY | os.O_CLOEXEC | os.O_NOFOLLOW
        )
        metadata = os.fstat(descriptor)
    except OSError as exc:
        raise RuntimeError("protected sandbox requires a trusted root-owned executable") from exc
    if (
        not stat.S_ISREG(metadata.st_mode)
        or not metadata.st_mode & 0o111
        or (require_root and metadata.st_uid != 0)
        or metadata.st_mode & 0o022
    ):
        if descriptor is not None:
            os.close(descriptor)
        raise RuntimeError("protected sandbox requires a trusted root-owned executable")
    digest = hashlib.sha256()
    try:
        for chunk in iter(lambda: os.read(descriptor, 1024 * 1024), b""):
            digest.update(chunk)
        final_metadata = os.fstat(descriptor)
        if require_root:
            _validate_trusted_executable_chain(resolved)
    except OSError as exc:
        raise RuntimeError("protected sandbox requires a trusted root-owned executable") from exc
    finally:
        if descriptor is not None:
            os.close(descriptor)
    measured = (
        metadata.st_dev, metadata.st_ino, stat.S_IMODE(metadata.st_mode),
        metadata.st_uid, metadata.st_size, metadata.st_mtime_ns,
    )
    final = (
        final_metadata.st_dev, final_metadata.st_ino,
        stat.S_IMODE(final_metadata.st_mode), final_metadata.st_uid,
        final_metadata.st_size, final_metadata.st_mtime_ns,
    )
    if measured != final:
        raise RuntimeError("protected executable identity changed during measurement")
    return _ExecutableIdentity(
        resolved, measured,
        digest.hexdigest(), require_root,
    )


def _validate_trusted_executable_chain(path: Path) -> None:
    """Require every resolved ancestor to be immutable to unprivileged users."""
    if not path.is_absolute():
        raise RuntimeError("protected executable path is not absolute")
    for directory in reversed(path.parents):
        try:
            metadata = directory.lstat()
        except OSError as exc:
            raise RuntimeError("protected executable ancestor is unavailable") from exc
        if (
            not stat.S_ISDIR(metadata.st_mode)
            or stat.S_ISLNK(metadata.st_mode)
            or metadata.st_uid != 0
            or metadata.st_mode & 0o022
        ):
            raise RuntimeError("protected executable ancestor is attacker-writable")


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


def _trusted_helper_runtime_roots(
    identity: _ExecutableIdentity,
) -> tuple[Path, ...]:
    """Return the minimal immutable stdlib root needed for Python startup."""
    version = identity.path.name.removeprefix("python")
    if (
        version.count(".") != 1
        or not all(part.isdigit() for part in version.split("."))
    ):
        raise RuntimeError("protected helper Python version is not identity-bound")
    try:
        encodings = (
            identity.path.parent.parent / "lib" / f"python{version}" / "encodings"
        ).resolve(strict=True)
        metadata = encodings.lstat()
        _validate_trusted_executable_chain(encodings / "__init__.py")
        init_metadata = (encodings / "__init__.py").lstat()
    except OSError as exc:
        raise RuntimeError("protected helper Python runtime is unavailable") from exc
    if (
        not stat.S_ISDIR(metadata.st_mode)
        or stat.S_ISLNK(metadata.st_mode)
        or metadata.st_uid != 0
        or metadata.st_mode & 0o022
    ):
        raise RuntimeError("protected helper Python runtime is not immutable")
    if (
        not stat.S_ISREG(init_metadata.st_mode)
        or stat.S_ISLNK(init_metadata.st_mode)
        or init_metadata.st_uid != 0
        or init_metadata.st_mode & 0o022
    ):
        raise RuntimeError("protected helper Python runtime is not immutable")
    return (encodings,)


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
            "sh", "xargs", "env",
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


def _python_version(value: str) -> str | None:
    """Return a validated major.minor prefix from a Python version spelling."""
    parts = value.strip().split(".")
    if len(parts) < 2 or not all(
        1 <= len(part) <= 3
        and all("0" <= character <= "9" for character in part)
        for part in parts[:2]
    ):
        return None
    return f"{int(parts[0])}.{int(parts[1])}"


def _configured_python_runtime(executable: Path) -> tuple[Path, str] | None:
    """Read a bounded native prefix/version pair from adjacent venv metadata."""
    configuration = executable.parent.parent / "pyvenv.cfg"
    try:
        with configuration.open("r", encoding="utf-8") as stream:
            payload = stream.read(64 * 1024 + 1)
        if len(payload) > 64 * 1024:
            return None
        values = {
            key.strip().lower(): value.strip()
            for line in payload.splitlines()
            if "=" in line
            for key, value in (line.split("=", 1),)
        }
        home = Path(values.get("home", ""))
        version = _python_version(values.get("version", ""))
        if home.is_absolute() and home.name in {"bin", "Scripts"} and version:
            return home.parent, version
    except (OSError, UnicodeError):
        return None
    return None


def _discovered_python_version(
    prefix: Path, library_names: tuple[str, ...],
) -> str | None:
    """Return one unambiguous bounded version from native stdlib directories."""
    discovered = set()
    matching_entries = 0
    for library_name in library_names:
        library_root = prefix / library_name
        if not library_root.is_dir():
            continue
        try:
            entries = library_root.iterdir()
        except OSError:
            continue
        try:
            for entry in entries:
                version = _python_version(entry.name.removeprefix("python"))
                if not version or not entry.name.startswith("python"):
                    continue
                if not entry.is_dir():
                    continue
                matching_entries += 1
                if matching_entries > 64:
                    return None
                discovered.add(version)
        except OSError:
            return None
    return discovered.pop() if len(discovered) == 1 else None


def _native_stdlib_root(
    prefix: Path, version: str, library_names: tuple[str, ...],
    preferred_library_name: str | None = None,
) -> Path | None:
    """Select one unambiguous exact stdlib root for a native runtime."""
    roots: dict[str, Path] = {}
    for library_name in library_names:
        try:
            root = (
                prefix / library_name / f"python{version}"
            ).resolve(strict=True)
            if root.is_dir() and (root / "linecache.py").is_file():
                roots[library_name] = root
        except (OSError, RuntimeError):
            continue
    unique_roots = set(roots.values())
    if len(unique_roots) == 1:
        return unique_roots.pop()
    if preferred_library_name and preferred_library_name in roots:
        return roots[preferred_library_name]
    return None


def _native_python_runtime_roots(executable: Path) -> tuple[Path, ...]:
    """Derive only the native stdlib root selected by a Python executable."""
    try:
        resolved = executable.resolve(strict=True)
    except (OSError, RuntimeError):
        return ()
    try:
        current_executable = _SUPERVISOR_EXECUTABLE.resolve(strict=True)
    except (OSError, RuntimeError):
        current_executable = None
    versions: list[tuple[Path, str, str | None]] = []
    configured = _configured_python_runtime(executable)
    if configured:
        versions.append((*configured, None))
    resolved_version = _python_version(resolved.name.removeprefix("python"))
    if resolved_version:
        preference = sys.platlibdir if resolved == current_executable else None
        versions.append((resolved.parent.parent, resolved_version, preference))
    if not resolved_version and resolved == current_executable:
        current_version = f"{sys.version_info.major}.{sys.version_info.minor}"
        versions.append((resolved.parent.parent, current_version, sys.platlibdir))
    library_names = tuple(dict.fromkeys((sys.platlibdir, "lib", "lib64")))
    unversioned_python_names = {"python", "python3"}
    if (
        not versions
        and executable.name in unversioned_python_names
        and resolved.name in unversioned_python_names
    ):
        discovered = _discovered_python_version(
            resolved.parent.parent, library_names,
        )
        if discovered:
            versions.append((resolved.parent.parent, discovered, None))
    roots = []
    for prefix, version, preference in versions:
        root = _native_stdlib_root(
            prefix, version, library_names, preference,
        )
        if root is not None and root not in roots:
            roots.append(root)
    return tuple(roots)


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
        roots.update(_native_python_runtime_roots(executable))
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


def _candidate_environment_launcher() -> str:
    """Return the post-uid-drop launcher that preserves exact child status."""
    return "\n".join((
        "import os,sys",
        "fd=os.open(sys.argv[1],os.O_RDONLY|os.O_CLOEXEC|os.O_NOFOLLOW)",
        "try:",
        " chunks=[]",
        " while True:",
        "  chunk=os.read(fd,1024*1024)",
        "  if not chunk: break",
        "  chunks.append(chunk)",
        "finally: os.close(fd)",
        "items=b''.join(chunks).split(b'\\0')",
        "boundary=next((i for i,item in enumerate(items) if b'=' not in item),None)",
        "if boundary is None: raise RuntimeError('candidate command missing')",
        "environment={}",
        "for item in items[:boundary]:",
        " key,value=item.split(b'=',1)",
        " key=key.decode('utf-8');value=value.decode('utf-8')",
        " if not key or key in environment: raise RuntimeError('invalid candidate environment')",
        " environment[key]=value",
        "command=[item.decode('utf-8') for item in items[boundary:]]",
        "if not command or not command[0]: raise RuntimeError('candidate command missing')",
        "os.execve(command[0],command,environment)",
    ))


def _subprocess_status_handoff() -> str:
    """Return helper code that preserves a nested subprocess signal exactly."""
    return "\n".join((
        "import signal",
        "status=result.returncode if result is not None else 1",
        "if status<0:",
        " signal.signal(-status,signal.SIG_DFL)",
        " os.kill(os.getpid(),-status)",
        " raise RuntimeError('subprocess signal handoff returned')",
        "raise SystemExit(status)",
    ))


def _staged_bwrap(
    argv: list[str], sources: list[Path],
    tools: dict[str, _ExecutableIdentity], *, candidate_command: list[str],
    candidate_uid: int, candidate_gid: int,
) -> list[str]:
    """Stage exact bind mounts wholly inside a private mount namespace."""
    helper = "\n".join((
        "import hashlib,json,os,pathlib,shutil,stat,subprocess,sys,tempfile",
        "helper_env={'HOME':'/root','LANG':'C','LC_ALL':'C',"
        "'PATH':'/usr/sbin:/usr/bin:/sbin:/bin'}",
        "os.environ.clear(); os.environ.update(helper_env)",
        "candidate_command=json.loads(sys.argv[1]); uid=int(sys.argv[2]); gid=int(sys.argv[3])",
        "manifest=json.loads(sys.argv[4]); argv=json.loads(sys.argv[5]); "
        "paths=json.loads(sys.argv[6])",
        "def verify_chain(path):",
        " for parent in reversed(path.parents):",
        "  metadata=parent.lstat()",
        "  if not stat.S_ISDIR(metadata.st_mode) or stat.S_ISLNK(metadata.st_mode) "
        "or metadata.st_uid!=0 or metadata.st_mode&0o022: "
        "raise RuntimeError('protected executable ancestor changed')",
        "def verify(name):",
        " expected=manifest[name]; path=pathlib.Path(expected['path'])",
        " verify_chain(path)",
        " fd=os.open(path,os.O_RDONLY|os.O_CLOEXEC|os.O_NOFOLLOW)",
        " try:",
        "  metadata=os.fstat(fd); digest=hashlib.sha256()",
        "  while True:",
        "   chunk=os.read(fd,1024*1024)",
        "   if not chunk: break",
        "   digest.update(chunk)",
        "  final=os.fstat(fd)",
        " finally: os.close(fd)",
        " verify_chain(path)",
        " if (metadata.st_dev,metadata.st_ino,metadata.st_mode,metadata.st_uid,"
        "metadata.st_size,metadata.st_mtime_ns)!=(final.st_dev,final.st_ino,"
        "final.st_mode,final.st_uid,final.st_size,final.st_mtime_ns): "
        "raise RuntimeError('protected executable changed during measurement')",
        " actual={'path':str(path.resolve(strict=True)),'device':metadata.st_dev,"
        "'inode':metadata.st_ino,'mode':stat.S_IMODE(metadata.st_mode),"
        "'uid':metadata.st_uid,'size':metadata.st_size,"
        "'mtime_ns':metadata.st_mtime_ns,'sha256':digest.hexdigest()}",
        " if actual!=expected or metadata.st_uid!=0 or metadata.st_mode&0o022 "
        "or not stat.S_ISREG(metadata.st_mode): "
        "raise RuntimeError(f'protected executable identity changed: {name}')",
        " return str(path)",
        "candidate_env=json.load(sys.stdin)",
        "if not isinstance(candidate_env,dict) or not all(isinstance(k,str) and k "
        "and '=' not in k and '\\x00' not in k and isinstance(v,str) and '\\x00' not in v "
        "for k,v in candidate_env.items()): raise RuntimeError('invalid candidate environment')",
        "for name in manifest: verify(name)",
        "mount=verify('mount'); umount=verify('umount'); bwrap=verify('bwrap')",
        "base=pathlib.Path(tempfile.mkdtemp(prefix='pdd-binds-',dir='/run'))",
        "os.chmod(base,0o700); staged=[]; result=None",
        "try:",
        " env_path=base/'candidate-env'",
        " env_items=[f'{key}={value}' for key,value in sorted(candidate_env.items())]",
        " env_payload=b'\\0'.join(value.encode() for value in (*env_items,*candidate_command))",
        " env_fd=os.open(env_path,os.O_WRONLY|os.O_CREAT|os.O_EXCL|os.O_NOFOLLOW,0o600)",
        " try:",
        "  os.fchown(env_fd,uid,gid); remaining=memoryview(env_payload)",
        "  while remaining: remaining=remaining[os.write(env_fd,remaining):]",
        "  os.fsync(env_fd)",
        " finally: os.close(env_fd)",
        " for index,source in enumerate(paths):",
        "  source=pathlib.Path(source); target=base/str(index)",
        "  target.mkdir() if source.is_dir() else target.touch()",
        "  mount=verify('mount')",
        "  subprocess.run([mount,'--bind',str(source),str(target)],check=True)",
        "  staged.append(target)",
        " argv=[str(staged[int(x[4:-1])]) if x.startswith('@FD:') else x for x in argv]",
        " argv=[('/run/pdd-candidate-env' if x=='@PDD-CANDIDATE-ENV@' else x) for x in argv]",
        " separator=argv.index('--')",
        " argv[separator:separator]=['--ro-bind',str(env_path),'/run/pdd-candidate-env']",
        " if argv[0]!=bwrap: raise RuntimeError('protected bwrap identity mismatch')",
        " verify('bwrap')",
        " result=subprocess.run(argv,check=False,env=helper_env)",
        "finally:",
        " for target in reversed(staged):",
        "  umount=verify('umount')",
        "  subprocess.run([umount,str(target)],check=False)",
        " shutil.rmtree(base,ignore_errors=True)",
        *_subprocess_status_handoff().splitlines(),
    ))
    manifest = json.dumps({name: identity.payload() for name, identity in tools.items()})
    return [
        str(tools["sudo"].path), "-n", "--", str(tools["unshare"].path),
        "--mount", "--propagation", "private", "--wd", "/",
        str(tools["python"].path), "-I", "-S", "-c", helper,
        json.dumps(candidate_command), str(candidate_uid), str(candidate_gid), manifest,
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
            "sh": _trusted_tool("sh"),
            "xargs": _trusted_tool("xargs"),
            "env": _trusted_tool("env"),
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
                "--tmpfs", "/", "--proc", "/proc", "--dir", "/tmp",
                "--dir", "/run"]
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
        for tool_name in ("setpriv", "python", "sh", "xargs", "env"):
            tool_path = tools[tool_name].path
            for item in (tool_path, *_linked_libraries(tool_path)):
                bind("--ro-bind", item.resolve(), item)
        for item in _trusted_helper_runtime_roots(tools["python"]):
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
        sandboxed = _limited_command(command, limits)
        if result_fifo is not None:
            sandboxed = _private_result_command(sandboxed, result_fifo, result_fd)
        drop = [
            setpriv, "--reuid", str(os.getuid()), "--regid", str(os.getgid()),
            "--clear-groups", "--", str(tools["python"].path), "-I", "-S",
            "-c", _candidate_environment_launcher(), "@PDD-CANDIDATE-ENV@",
        ]
        argv.extend(("--", *drop))
        return _staged_bwrap(
            argv, sources, tools, candidate_command=sandboxed,
            candidate_uid=os.getuid(), candidate_gid=os.getgid(),
        ), None
    raise RuntimeError("unsupported sandbox platform or mechanism")


def run_supervised(
    command: list[str], *, cwd: Path, timeout: int, env: dict[str, str],
    writable_roots: tuple[Path, ...], writable_files: tuple[Path, ...] = (),
    limits: SupervisorLimits = SupervisorLimits(),
    readable_roots: tuple[Path, ...] = (),
    readable_bindings: tuple[tuple[Path, Path], ...] = (),
    result_fifo: Path | None = None,
    result_fd: int = 198,
) -> tuple[SupervisedCompletedProcess, bool]:
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
        return _supervised_result(
            command,
            125,
            "",
            str(exc),
            SupervisorTermination(TerminationKind.SANDBOX_ERROR, exit_code=125),
        ), False
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
        return _supervised_result(
            command,
            125,
            "",
            f"protected helper startup failed: {exc}",
            SupervisorTermination(TerminationKind.SANDBOX_ERROR, exit_code=125),
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
    resource_limit: str | None = None
    try:
        while process.poll() is None:
            if time.monotonic() >= deadline:
                timed_out = True
                break
            if _writable_size(writable_roots) > limits.max_writable_bytes:
                resource_limit = "writable-bytes"
                break
            if stdout_file.tell() + stderr_file.tell() > limits.max_output_bytes:
                resource_limit = "output-bytes"
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
        resource_limit = "output-bytes"
    stdout_file.close()
    stderr_file.close()
    stdout = stdout_bytes.decode("utf-8", errors="replace")
    stderr = stderr_bytes.decode("utf-8", errors="replace")
    returncode = 125 if resource_limit else (124 if timed_out else process.returncode)
    termination = _termination_evidence(
        process.returncode,
        timed_out=timed_out,
        timeout_seconds=timeout,
        resource_limit=resource_limit,
    )
    return _supervised_result(
        command, returncode, stdout, stderr, termination
    ), surviving
