"""Deterministically stage the closed standalone global-sync checker wheel."""
# pylint: disable=too-many-branches,too-many-locals,too-many-boolean-expressions

from __future__ import annotations

import ast
import base64
import contextlib
from email import policy
from email.parser import BytesParser
import hashlib
import io
import json
import os
import re
import stat
from pathlib import Path, PurePosixPath
from typing import Any, Mapping
import zipfile

from packaging.utils import InvalidWheelFilename, parse_wheel_filename


class StandalonePackageError(ValueError):
    """Raised when the protected standalone checker boundary is invalid."""


_MANIFEST_PATH = PurePosixPath(".pdd/global-sync/standalone-checker-modules.json")
_MANIFEST_KEYS = frozenset({
    "schema_version", "package", "distribution", "entry_point", "modules",
    "data", "dependencies", "target",
})
_TARGET_KEYS = frozenset({"platform", "glibc"})
_PACKAGE = "pdd_sync_checker"
_DISTRIBUTION = "pdd-sync-checker"
_ENTRY_POINT = "pdd_sync_checker.checker_cli:main"
_EMBEDDED_MANIFEST = f"{_PACKAGE}/standalone-checker-modules.json"
_INIT_BYTES = b'"""Standalone global-sync checker namespace."""\n'
_WHEEL_BYTES = (
    b"Wheel-Version: 1.0\nGenerator: pdd-standalone-checker\n"
    b"Root-Is-Purelib: true\nTag: py3-none-any\n"
)
_DATA_MAPPINGS = (
    {
        "source": "pdd/data/language_format.csv",
        "destination": "data/language_format.csv",
    },
    {
        "source": "pdd/sync_core/pytest_probe.py",
        "destination": "pytest_probe.py",
    },
)
_DATA_KEYS = frozenset({"source", "destination"})
_MODULE_NAME = re.compile(r"[a-z][a-z0-9_]*\.py")
_DATA_PATH = re.compile(r"[a-zA-Z0-9_.-]+(?:/[a-zA-Z0-9_.-]+)*")
_DEPENDENCY = re.compile(r"[A-Za-z][A-Za-z0-9-]* (?:==|>=)[^ ]+(?:,<[0-9]+)?")
_SHA256 = re.compile(r"[0-9a-f]{64}")
_ZIP_TIMESTAMP = (1980, 1, 1, 0, 0, 0)
_DIRECTORY_FLAGS = (
    os.O_RDONLY
    | getattr(os, "O_DIRECTORY", 0)
    | getattr(os, "O_NOFOLLOW", 0)
)
_FILE_FLAGS = os.O_RDONLY | getattr(os, "O_NOFOLLOW", 0)
_BOOTSTRAP_PYTHON = r"""import base64
import hashlib
import importlib
import importlib.util
import io
import os
import re
import stat
import sys
import zipfile
from pathlib import Path, PurePosixPath

def fail(message):
    raise RuntimeError("standalone checker bootstrap: " + message)

def record_hash(content):
    return base64.urlsafe_b64encode(
        hashlib.sha256(content).digest()
    ).rstrip(b"=").decode("ascii")

def read_regular(path, label, directory=None):
    try:
        descriptor = os.open(
            path,
            os.O_RDONLY | getattr(os, "O_NOFOLLOW", 0),
            dir_fd=directory,
        )
    except OSError as exc:
        fail(label + " is unsafe: " + str(exc))
    try:
        if not stat.S_ISREG(os.fstat(descriptor).st_mode):
            fail(label + " is not regular")
        chunks = []
        while True:
            chunk = os.read(descriptor, 1024 * 1024)
            if not chunk:
                return b"".join(chunks)
            chunks.append(chunk)
    finally:
        os.close(descriptor)

def open_directory(parent, name):
    try:
        descriptor = os.open(
            name,
            os.O_RDONLY
            | getattr(os, "O_DIRECTORY", 0)
            | getattr(os, "O_NOFOLLOW", 0),
            dir_fd=parent,
        )
    except OSError as exc:
        fail("installed package directory is unsafe: " + str(exc))
    if not stat.S_ISDIR(os.fstat(descriptor).st_mode):
        os.close(descriptor)
        fail("installed package directory is not a directory")
    return descriptor

launcher = Path(sys.argv[1])
if not launcher.is_absolute():
    fail("entrypoint path must be absolute")
arguments = [str(launcher), *sys.argv[2:]]
candidate_cwd = os.getcwd()
venv = launcher.parent.parent
os.chdir(venv)
sys.dont_write_bytecode = True
os.environ["PYTHONDONTWRITEBYTECODE"] = "1"
sys.prefix = str(venv)
sys.exec_prefix = str(venv)
purelib = (
    venv / "lib" / ("python%d.%d" % sys.version_info[:2]) / "site-packages"
)
package_root = purelib / "pdd_sync_checker"
wheel_value = os.environ.get("PDD_RELEASED_CHECKER_WHEEL_PATH")
expected_digest = os.environ.get("PDD_RELEASED_CHECKER_WHEEL_SHA256", "")
if not wheel_value or re.fullmatch("[0-9a-f]{64}", expected_digest) is None:
    fail("released wheel provenance is required")
wheel_path = Path(wheel_value)
if not wheel_path.is_absolute():
    fail("released wheel path must be absolute")
wheel_bytes = read_regular(wheel_path, "released wheel")
if hashlib.sha256(wheel_bytes).hexdigest() != expected_digest:
    fail("released wheel digest does not match")

try:
    with zipfile.ZipFile(io.BytesIO(wheel_bytes)) as archive:
        infos = archive.infolist()
        names = [item.filename for item in infos]
        if len(names) != len(set(names)):
            fail("released wheel contains duplicate members")
        for item in infos:
            path = PurePosixPath(item.filename)
            mode = item.external_attr >> 16
            if (
                item.is_dir()
                or not item.filename
                or "\\" in item.filename
                or path.is_absolute()
                or ".." in path.parts
                or not stat.S_ISREG(mode)
            ):
                fail("released wheel contains an unsafe member")
        record_names = [
            name for name in names if name.endswith(".dist-info/RECORD")
        ]
        if len(record_names) != 1:
            fail("released wheel RECORD is invalid")
        record_name = record_names[0]
        rows = {}
        for line in archive.read(record_name).decode("ascii").splitlines():
            columns = line.split(",")
            if len(columns) != 3 or not columns[0] or columns[0] in rows:
                fail("released wheel RECORD is malformed")
            rows[columns[0]] = (columns[1], columns[2])
        if set(rows) != set(names):
            fail("released wheel RECORD is not closed")
        for name in names:
            encoded, size = rows[name]
            if name == record_name:
                if encoded or size:
                    fail("released wheel RECORD self-entry is invalid")
            else:
                content = archive.read(name)
                if (
                    encoded != "sha256=" + record_hash(content)
                    or size != str(len(content))
                ):
                    fail("released wheel RECORD does not match bytes")
        expected = {
            PurePosixPath(name).relative_to("pdd_sync_checker").as_posix():
            archive.read(name)
            for name in names
            if name.startswith("pdd_sync_checker/")
        }
        bootstrap_names = [
            name
            for name in names
            if name.endswith(".data/scripts/pdd-sync-checker")
        ]
        if (
            len(bootstrap_names) != 1
            or read_regular(launcher, "installed bootstrap")
            != archive.read(bootstrap_names[0])
        ):
            fail("installed bootstrap differs from released wheel")
except (OSError, UnicodeDecodeError, zipfile.BadZipFile, KeyError) as exc:
    fail("released wheel cannot be inspected: " + str(exc))
if not expected:
    fail("released wheel contains no checker package")

root_fd = os.open(
    venv,
    os.O_RDONLY
    | getattr(os, "O_DIRECTORY", 0)
    | getattr(os, "O_NOFOLLOW", 0),
)
opened = [root_fd]
try:
    for component in (
        "lib",
        "python%d.%d" % sys.version_info[:2],
        "site-packages",
        "pdd_sync_checker",
    ):
        opened.append(open_directory(opened[-1], component))
    package_fd = opened[-1]
    expected_directories = {
        PurePosixPath(*PurePosixPath(name).parts[:index]).as_posix()
        for name in expected
        for index in range(1, len(PurePosixPath(name).parts))
    }
    actual = set()

    def walk(descriptor, prefix=""):
        with os.scandir(descriptor) as entries:
            for entry in entries:
                relative = prefix + entry.name
                mode = entry.stat(follow_symlinks=False).st_mode
                if stat.S_ISDIR(mode):
                    if relative not in expected_directories:
                        fail("installed checker has an unlisted directory: " + relative)
                    child = open_directory(descriptor, entry.name)
                    try:
                        walk(child, relative + "/")
                    finally:
                        os.close(child)
                elif stat.S_ISREG(mode):
                    actual.add(relative)
                    content = read_regular(
                        entry.name,
                        "installed checker member " + relative,
                        descriptor,
                    )
                    if relative not in expected or content != expected[relative]:
                        fail("installed checker closure differs from wheel")
                else:
                    fail("installed checker has a nonregular entry: " + relative)

    walk(package_fd)
    if actual != set(expected):
        fail("installed checker closure differs from wheel")
finally:
    for descriptor in reversed(opened):
        os.close(descriptor)

stdlib_paths = [
    value
    for value in sys.path
    if value and Path(value).resolve() not in {Path(candidate_cwd), launcher.parent}
]
sys.path[:] = [str(purelib), *stdlib_paths]
init_path = package_root / "__init__.py"
spec = importlib.util.spec_from_file_location(
    "pdd_sync_checker",
    init_path,
    submodule_search_locations=[str(package_root)],
)
if spec is None or spec.loader is None:
    fail("installed checker package cannot be loaded")
package = importlib.util.module_from_spec(spec)
sys.modules["pdd_sync_checker"] = package
spec.loader.exec_module(package)
checker = importlib.import_module("pdd_sync_checker.checker_cli")
os.chdir(candidate_cwd)
sys.argv = arguments
raise SystemExit(checker.main(sys.argv[1:]))
"""
_BOOTSTRAP_SCRIPT = (
    "#!/bin/sh\n"
    "case \"$0\" in\n"
    "  /*) ;;\n"
    "  *) echo 'pdd-sync-checker requires an absolute executable path' >&2; exit 126 ;;\n"
    "esac\n"
    "exec \"${0%/*}/python\" -I -B -S - \"$0\" \"$@\" <<'PDD_SYNC_BOOTSTRAP'\n"
    f"{_BOOTSTRAP_PYTHON}"
    "PDD_SYNC_BOOTSTRAP\n"
).encode("ascii")


def _error(message: str) -> StandalonePackageError:
    return StandalonePackageError(f"standalone checker package: {message}")


@contextlib.contextmanager
def _open_directory_path(path: Path, label: str):
    """Open every absolute directory component without following links."""
    absolute = Path(path).expanduser().absolute()
    descriptors: list[int] = []
    try:
        descriptor = os.open("/", _DIRECTORY_FLAGS)
        descriptors.append(descriptor)
        for component in absolute.parts[1:]:
            descriptor = os.open(
                component, _DIRECTORY_FLAGS, dir_fd=descriptor
            )
            descriptors.append(descriptor)
        if not stat.S_ISDIR(os.fstat(descriptor).st_mode):
            raise _error(f"{label} is not a directory")
        yield descriptor
    except OSError as exc:
        raise _error(f"{label} contains an unsafe path component") from exc
    finally:
        for descriptor in reversed(descriptors):
            os.close(descriptor)


def _read_relative_regular(root: Path, relative: PurePosixPath, label: str) -> bytes:
    """Read one regular descendant through stable no-follow descriptors."""
    if relative.is_absolute() or not relative.parts or ".." in relative.parts:
        raise _error(f"{label} path is unsafe")
    descriptors: list[int] = []
    file_descriptor: int | None = None
    try:
        with _open_directory_path(root, "repository root") as root_descriptor:
            descriptor = os.dup(root_descriptor)
            descriptors.append(descriptor)
            for component in relative.parts[:-1]:
                descriptor = os.open(
                    component, _DIRECTORY_FLAGS, dir_fd=descriptor
                )
                descriptors.append(descriptor)
            file_descriptor = os.open(
                relative.parts[-1],
                _FILE_FLAGS,
                dir_fd=descriptor,
            )
            if not stat.S_ISREG(os.fstat(file_descriptor).st_mode):
                raise _error(f"{label} must be a regular file")
            with os.fdopen(file_descriptor, "rb") as handle:
                file_descriptor = None
                return handle.read()
    except OSError as exc:
        raise _error(f"{label} must be a regular file") from exc
    finally:
        if file_descriptor is not None:
            os.close(file_descriptor)
        for descriptor in reversed(descriptors):
            os.close(descriptor)


def _read_regular_path(path: Path, label: str) -> bytes:
    absolute = Path(path).expanduser().absolute()
    return _read_relative_regular(
        absolute.parent, PurePosixPath(absolute.name), label
    )


def _repository_root(root: Path) -> Path:
    """Return a lexical repository root only when every component is a directory."""
    repository = Path(root).expanduser().absolute()
    with _open_directory_path(repository, "repository root"):
        pass
    return repository


def _manifest_bytes(manifest: Mapping[str, Any]) -> bytes:
    return (
        json.dumps(manifest, indent=2, ensure_ascii=True).encode("utf-8")
        + b"\n"
    )


def _parse_manifest(source: Path | bytes) -> dict[str, Any]:
    if isinstance(source, bytes):
        encoded = source
        try:
            payload = json.loads(source.decode("utf-8"))
        except (UnicodeDecodeError, json.JSONDecodeError) as exc:
            raise _error("module manifest is malformed") from exc
    else:
        encoded = _read_regular_path(source, "module manifest")
        try:
            payload = json.loads(encoded.decode("utf-8"))
        except (UnicodeDecodeError, json.JSONDecodeError) as exc:
            raise _error("module manifest is malformed") from exc
    if not isinstance(payload, dict) or set(payload) != _MANIFEST_KEYS:
        raise _error("module manifest schema is closed and malformed")
    if (
        payload["schema_version"] != 1
        or payload["package"] != _PACKAGE
        or payload["distribution"] != _DISTRIBUTION
        or payload["entry_point"] != _ENTRY_POINT
    ):
        raise _error("module manifest identity is invalid")
    modules = payload["modules"]
    data = payload["data"]
    dependencies = payload["dependencies"]
    target = payload["target"]
    if (
        not isinstance(modules, list)
        or not modules
        or any(
            not isinstance(item, str) or _MODULE_NAME.fullmatch(item) is None
            for item in modules
        )
        or modules != sorted(modules)
        or len(modules) != len(set(modules))
        or not isinstance(data, list)
        or data != list(_DATA_MAPPINGS)
        or any(
            not isinstance(item, dict)
            or set(item) != _DATA_KEYS
            or any(
                not isinstance(value, str)
                or _DATA_PATH.fullmatch(value) is None
                for value in item.values()
            )
            for item in data
        )
        or not isinstance(dependencies, list)
        or any(
            not isinstance(item, str) or _DEPENDENCY.fullmatch(item) is None
            for item in dependencies
        )
        or dependencies != sorted(dependencies, key=str.lower)
        or len(dependencies) != len(set(dependencies))
        or not isinstance(target, dict)
        or set(target) != _TARGET_KEYS
        or target != {"platform": "linux_x86_64_cp312", "glibc": "2.36"}
    ):
        raise _error("module manifest closure is malformed")
    if encoded != _manifest_bytes(payload):
        raise _error("module manifest is not canonical")
    return payload


def load_standalone_manifest(root: Path) -> dict[str, Any]:
    """Load the one protected module/dependency authority from a safe checkout."""
    repository = _repository_root(root)
    return _parse_manifest(
        _read_relative_regular(
            repository, _MANIFEST_PATH, "module manifest"
        )
    )


def _source_bytes(root: Path, module: str) -> bytes:
    return _read_relative_regular(
        root,
        PurePosixPath("pdd", "sync_core", module),
        f"module {module}",
    )


def _relative_imports(module: str, source: bytes) -> set[str]:
    try:
        tree = ast.parse(source, filename=module)
    except SyntaxError as exc:
        raise _error(f"module {module} is malformed") from exc
    imports: set[str] = set()
    for node in ast.walk(tree):
        if isinstance(node, ast.Import):
            if any(alias.name == "pdd" or alias.name.startswith("pdd.") for alias in node.names):
                raise _error(f"module {module} imports pdd")
        elif isinstance(node, ast.ImportFrom):
            if node.level == 0 and node.module and (
                node.module == "pdd" or node.module.startswith("pdd.")
            ):
                raise _error(f"module {module} imports pdd")
            if node.level > 1:
                raise _error(f"module {module} escapes the standalone namespace")
            if node.level == 1:
                if node.module:
                    imports.add(f"{node.module.split('.', 1)[0]}.py")
                else:
                    imports.update(f"{alias.name}.py" for alias in node.names)
    return imports


def _checked_module_bytes(root: Path, manifest: Mapping[str, Any]) -> dict[str, bytes]:
    modules = set(manifest["modules"])
    required = {"checker_cli.py", "released_checker.py", "standalone_package.py"}
    if not required <= modules:
        raise _error("module manifest omits a required entrypoint module")
    source = {module: _source_bytes(root, module) for module in modules}
    closure = set(required)
    pending = list(required)
    while pending:
        module = pending.pop()
        for imported in _relative_imports(module, source[module]):
            if imported not in modules:
                raise _error(f"module {module} imports unmanifested {imported}")
            if imported not in closure:
                closure.add(imported)
                pending.append(imported)
    if closure != modules:
        extra = sorted(modules - closure)
        raise _error(f"module manifest contains extra module {extra[0]}")
    return source


def _record_hash(content: bytes) -> str:
    return base64.urlsafe_b64encode(hashlib.sha256(content).digest()).rstrip(b"=").decode("ascii")


def _dist_info(version: str) -> str:
    if not re.fullmatch(r"[0-9]+(?:\.[0-9]+){2}", version):
        raise _error("wheel version must be a canonical X.Y.Z value")
    return f"pdd_sync_checker-{version}.dist-info"


def _metadata_bytes(manifest: Mapping[str, Any], version: str) -> bytes:
    return "\n".join(
        (
            "Metadata-Version: 2.1",
            f"Name: {manifest['distribution']}",
            f"Version: {version}",
            "Summary: Standalone PDD global-sync checker",
            *(f"Requires-Dist: {dependency}" for dependency in manifest["dependencies"]),
            "",
        )
    ).encode("utf-8")


def _bootstrap_member(version: str) -> str:
    return f"pdd_sync_checker-{version}.data/scripts/pdd-sync-checker"


def _wheel_members(root: Path, manifest: Mapping[str, Any], version: str) -> dict[str, bytes]:
    modules = _checked_module_bytes(root, manifest)
    data = {
        item["destination"]: _read_relative_regular(
            root,
            PurePosixPath(item["source"]),
            f"data source {item['source']}",
        )
        for item in manifest["data"]
    }
    manifest_bytes = _read_relative_regular(
        root, _MANIFEST_PATH, "module manifest"
    )
    dist_info = _dist_info(version)
    members = {
        f"{_PACKAGE}/__init__.py": _INIT_BYTES,
        **{f"{_PACKAGE}/{module}": content for module, content in modules.items()},
        **{f"{_PACKAGE}/{item}": content for item, content in data.items()},
        _EMBEDDED_MANIFEST: manifest_bytes,
        _bootstrap_member(version): _BOOTSTRAP_SCRIPT,
        f"{dist_info}/METADATA": _metadata_bytes(manifest, version),
        f"{dist_info}/WHEEL": _WHEEL_BYTES,
    }
    record = "".join(
        f"{name},sha256={_record_hash(content)},{len(content)}\n"
        for name, content in sorted(members.items())
    ) + f"{dist_info}/RECORD,,\n"
    members[f"{dist_info}/RECORD"] = record.encode("ascii")
    return members


def _zip_info(name: str, *, executable: bool = False) -> zipfile.ZipInfo:
    info = zipfile.ZipInfo(name, date_time=_ZIP_TIMESTAMP)
    info.compress_type = zipfile.ZIP_STORED
    info.external_attr = (
        stat.S_IFREG | (0o755 if executable else 0o644)
    ) << 16
    info.create_system = 3
    return info


@contextlib.contextmanager
def _open_output_directory(path: Path):
    """Create and open an output directory without following any component."""
    destination = Path(path).expanduser().absolute()
    descriptors: list[int] = []
    try:
        descriptor = os.open("/", _DIRECTORY_FLAGS)
        descriptors.append(descriptor)
        for component in destination.parts[1:]:
            try:
                next_descriptor = os.open(
                    component, _DIRECTORY_FLAGS, dir_fd=descriptor
                )
            except FileNotFoundError:
                os.mkdir(component, mode=0o755, dir_fd=descriptor)
                next_descriptor = os.open(
                    component, _DIRECTORY_FLAGS, dir_fd=descriptor
                )
            descriptor = next_descriptor
            descriptors.append(descriptor)
        yield destination, descriptor
    except OSError as exc:
        raise _error("wheel output directory is unsafe") from exc
    finally:
        for descriptor in reversed(descriptors):
            os.close(descriptor)


def build_standalone_wheel(root: Path, output: Path, *, version: str) -> Path:
    """Build one byte-reproducible standalone wheel from manifest-authorized bytes."""
    repository = _repository_root(root)
    manifest = load_standalone_manifest(repository)
    members = _wheel_members(repository, manifest, version)
    wheel_name = f"pdd_sync_checker-{version}-py3-none-any.whl"
    with _open_output_directory(Path(output)) as (destination, directory):
        wheel = destination / wheel_name
        try:
            descriptor = os.open(
                wheel_name,
                os.O_RDWR
                | os.O_CREAT
                | os.O_EXCL
                | getattr(os, "O_NOFOLLOW", 0),
                0o644,
                dir_fd=directory,
            )
        except OSError as exc:
            raise _error("wheel output already exists or is unsafe") from exc
        with os.fdopen(descriptor, "w+b") as handle:
            with zipfile.ZipFile(
                handle,
                "w",
                compression=zipfile.ZIP_STORED,
                strict_timestamps=True,
            ) as archive:
                bootstrap = _bootstrap_member(version)
                for name, content in sorted(members.items()):
                    archive.writestr(
                        _zip_info(name, executable=name == bootstrap),
                        content,
                    )
            handle.flush()
            os.fsync(handle.fileno())
    validate_standalone_wheel(wheel, manifest)
    return wheel


def _safe_member(name: str) -> PurePosixPath:
    path = PurePosixPath(name)
    if not name or "\\" in name or path.is_absolute() or ".." in path.parts:
        raise _error("wheel contains an unsafe member")
    return path


def _read_record(record: bytes) -> dict[str, tuple[str, str]]:
    try:
        lines = record.decode("ascii").splitlines()
    except UnicodeDecodeError as exc:
        raise _error("wheel RECORD is not ASCII") from exc
    entries: dict[str, tuple[str, str]] = {}
    for line in lines:
        columns = line.split(",")
        if len(columns) != 3 or not columns[0] or columns[0] in entries:
            raise _error("wheel RECORD is malformed")
        entries[columns[0]] = (columns[1], columns[2])
    return entries


def _canonical_wheel_files(
    wheel_bytes: bytes, bootstrap: str
) -> dict[str, bytes]:
    """Return archive bytes only when every member has canonical attributes."""
    try:
        with zipfile.ZipFile(io.BytesIO(wheel_bytes)) as archive:
            files: dict[str, bytes] = {}
            for member in archive.infolist():
                path = _safe_member(member.filename)
                mode = member.external_attr >> 16
                expected_mode = stat.S_IFREG | (
                    0o755 if path.as_posix() == bootstrap else 0o644
                )
                if (
                    member.is_dir()
                    or mode != expected_mode
                    or member.create_system != 3
                    or member.compress_type != zipfile.ZIP_STORED
                    or member.date_time != _ZIP_TIMESTAMP
                    or path.as_posix() in files
                ):
                    raise _error("wheel contains an unsafe member")
                files[path.as_posix()] = archive.read(member)
    except (OSError, zipfile.BadZipFile) as exc:
        raise _error("wheel cannot be inspected") from exc
    return files


def _validate_metadata_authority(
    metadata: bytes, manifest: Mapping[str, Any], version: str
) -> None:
    """Require parsed and byte-exact core metadata from protected authority."""
    try:
        parsed = BytesParser(policy=policy.default).parsebytes(metadata)
    except (TypeError, ValueError) as exc:
        raise _error("wheel METADATA is malformed") from exc
    if (
        parsed.defects
        or parsed.get("Metadata-Version") != "2.1"
        or parsed.get("Name") != manifest["distribution"]
        or parsed.get("Version") != version
        or parsed.get_all("Requires-Dist", []) != manifest["dependencies"]
        or metadata != _metadata_bytes(manifest, version)
    ):
        raise _error("wheel METADATA differs from protected authority")


def validate_standalone_wheel(wheel_path: Path, manifest: Mapping[str, Any]) -> None:
    """Fail closed unless the archive has exactly the manifest-authorized RECORD closure."""
    wheel = Path(wheel_path).expanduser().absolute()
    wheel_bytes = _read_regular_path(wheel, "wheel")
    try:
        name, version_value, build, tags = parse_wheel_filename(wheel.name)
    except InvalidWheelFilename as exc:
        raise _error("wheel filename is malformed") from exc
    version = str(version_value)
    if (
        name != manifest["distribution"]
        or build
        or wheel.name
        != f"pdd_sync_checker-{version}-py3-none-any.whl"
        or {str(tag) for tag in tags} != {"py3-none-any"}
    ):
        raise _error("wheel tags are not standalone checker tags")
    expected_prefix = f"{manifest['package']}/"
    bootstrap = _bootstrap_member(version)
    files = _canonical_wheel_files(wheel_bytes, bootstrap)
    if any(name.startswith("pdd/") for name in files):
        raise _error("wheel contains the pdd package")
    expected_modules = {f"{expected_prefix}__init__.py", _EMBEDDED_MANIFEST} | {
        f"{expected_prefix}{module}" for module in manifest["modules"]
    } | {
        f"{expected_prefix}{item['destination']}"
        for item in manifest["data"]
    }
    dist_info = _dist_info(version)
    dist_infos = {
        PurePosixPath(member_name).parts[0]
        for member_name in files
        if ".dist-info/" in member_name
    }
    if dist_infos != {dist_info}:
        raise _error("wheel dist-info closure is invalid")
    expected = expected_modules | {
        bootstrap,
        f"{dist_info}/METADATA",
        f"{dist_info}/WHEEL",
        f"{dist_info}/RECORD",
    }
    if set(files) != expected:
        raise _error("wheel member closure is invalid")
    if files[f"{expected_prefix}__init__.py"] != _INIT_BYTES:
        raise _error("wheel package initializer is invalid")
    if files[_EMBEDDED_MANIFEST] != _manifest_bytes(manifest):
        raise _error("wheel embedded module manifest differs from authority")
    if files[f"{dist_info}/WHEEL"] != _WHEEL_BYTES:
        raise _error("wheel metadata identity is invalid")
    if files[bootstrap] != _BOOTSTRAP_SCRIPT:
        raise _error("wheel bootstrap entrypoint is invalid")
    _validate_metadata_authority(
        files[f"{dist_info}/METADATA"], manifest, version
    )
    record_name = f"{dist_info}/RECORD"
    records = _read_record(files[record_name])
    if set(records) != set(files):
        raise _error("wheel RECORD does not close over members")
    for name, content in files.items():
        encoded, size = records[name]
        if name == record_name:
            if encoded or size:
                raise _error("wheel RECORD self-entry is invalid")
            continue
        if encoded != f"sha256={_record_hash(content)}" or size != str(len(content)):
            raise _error("wheel RECORD does not match member bytes")


def _verified_archive_files(wheel_path: Path) -> dict[str, bytes]:
    """Read one standalone archive only after closing every member through RECORD."""
    wheel_bytes = _read_regular_path(Path(wheel_path), "wheel")
    try:
        with zipfile.ZipFile(io.BytesIO(wheel_bytes)) as archive:
            files: dict[str, bytes] = {}
            for member in archive.infolist():
                path = _safe_member(member.filename)
                mode = member.external_attr >> 16
                if (
                    member.is_dir()
                    or not stat.S_ISREG(mode)
                    or path.as_posix() in files
                ):
                    raise _error("wheel contains an unsafe member")
                files[path.as_posix()] = archive.read(member)
    except (OSError, zipfile.BadZipFile) as exc:
        raise _error("wheel cannot be inspected") from exc
    record_names = [name for name in files if name.endswith(".dist-info/RECORD")]
    if len(record_names) != 1:
        raise _error("wheel RECORD is malformed")
    records = _read_record(files[record_names[0]])
    if set(records) != set(files):
        raise _error("wheel RECORD does not close over members")
    for name, content in files.items():
        encoded, size = records[name]
        if name == record_names[0]:
            if encoded or size:
                raise _error("wheel RECORD self-entry is invalid")
        elif encoded != f"sha256={_record_hash(content)}" or size != str(len(content)):
            raise _error("wheel RECORD does not match member bytes")
    return files


def _read_descriptor_regular(
    directory: int, name: str, label: str
) -> bytes:
    descriptor: int | None = None
    try:
        descriptor = os.open(name, _FILE_FLAGS, dir_fd=directory)
        if not stat.S_ISREG(os.fstat(descriptor).st_mode):
            raise _error(f"{label} is not a regular file")
        with os.fdopen(descriptor, "rb") as handle:
            descriptor = None
            return handle.read()
    except OSError as exc:
        raise _error(f"{label} is unsafe") from exc
    finally:
        if descriptor is not None:
            os.close(descriptor)


def _closed_installed_package(
    package_root: Path, expected: Mapping[str, bytes]
) -> None:
    """Compare a no-follow installed tree to the exact wheel package closure."""
    expected_directories = {
        PurePosixPath(*PurePosixPath(name).parts[:index]).as_posix()
        for name in expected
        for index in range(1, len(PurePosixPath(name).parts))
    }
    actual: dict[str, bytes] = {}

    def walk(directory: int, prefix: str = "") -> None:
        try:
            with os.scandir(directory) as iterator:
                entries = sorted(iterator, key=lambda entry: entry.name)
        except OSError as exc:
            raise _error("installed checker closure cannot be inspected") from exc
        for entry in entries:
            relative = f"{prefix}{entry.name}"
            try:
                mode = entry.stat(follow_symlinks=False).st_mode
            except OSError as exc:
                raise _error("installed checker closure cannot be inspected") from exc
            if stat.S_ISDIR(mode):
                if relative not in expected_directories:
                    raise _error(
                        f"installed checker contains unlisted directory {relative}"
                    )
                try:
                    child = os.open(
                        entry.name, _DIRECTORY_FLAGS, dir_fd=directory
                    )
                except OSError as exc:
                    raise _error(
                        f"installed checker directory is unsafe: {relative}"
                    ) from exc
                try:
                    walk(child, f"{relative}/")
                finally:
                    os.close(child)
            elif stat.S_ISREG(mode):
                actual[relative] = _read_descriptor_regular(
                    directory,
                    entry.name,
                    f"installed checker member {relative}",
                )
            else:
                raise _error(
                    f"installed checker contains nonregular entry {relative}"
                )

    with _open_directory_path(package_root, "installed checker package") as descriptor:
        walk(descriptor)
    if set(actual) != set(expected):
        raise _error("installed checker closure differs from the wheel")
    for relative, expected_bytes in expected.items():
        if actual[relative] != expected_bytes:
            raise _error("installed checker bytes differ from the wheel")


def _installed_package_files(wheel: Path, installed_package: Path) -> dict[str, bytes]:
    """Return the closed checker module set only when installed bytes equal the wheel."""
    files = _verified_archive_files(wheel)
    try:
        manifest = _parse_manifest(files[_EMBEDDED_MANIFEST])
    except KeyError as exc:
        raise _error("wheel embedded module manifest is missing") from exc
    validate_standalone_wheel(wheel, manifest)
    if any(name.startswith("pdd/") for name in files):
        raise _error("wheel contains the pdd package")
    expected = {
        PurePosixPath(name).relative_to(_PACKAGE).as_posix(): content
        for name, content in files.items()
        if name.startswith(f"{_PACKAGE}/")
    }
    if not expected:
        raise _error("wheel contains no standalone checker package")
    path = Path(installed_package).expanduser().absolute()
    try:
        package_index = max(
            index for index, part in enumerate(path.parts) if part == _PACKAGE
        )
    except ValueError as exc:
        raise _error("installed checker module is outside its package") from exc
    package_root = Path(*path.parts[: package_index + 1])
    installed_relative = path.relative_to(package_root).as_posix()
    if installed_relative not in expected:
        raise _error("installed checker module is outside the wheel closure")
    _closed_installed_package(package_root, expected)
    return expected


def installed_checker_runtime_lock(wheel: Path, installed_package: Path) -> bytes:
    """Generate a canonical lock solely from validated installed checker bytes."""
    files = _installed_package_files(wheel, installed_package)
    archive = _verified_archive_files(wheel)
    metadata = next(
        content for name, content in archive.items() if name.endswith(".dist-info/METADATA")
    )
    try:
        dependencies = sorted(
            line.removeprefix("Requires-Dist: ")
            for line in metadata.decode("utf-8").splitlines()
            if line.startswith("Requires-Dist: ")
        )
    except UnicodeDecodeError as exc:
        raise _error("wheel metadata is not UTF-8") from exc
    payload = {
        "dependencies": dependencies,
        "files": [
            {"path": path, "sha256": hashlib.sha256(content).hexdigest()}
            for path, content in sorted(files.items())
        ],
        "package": _PACKAGE,
        "schema_version": 1,
        "wheel_sha256": hashlib.sha256(
            _read_regular_path(wheel, "wheel")
        ).hexdigest(),
    }
    return json.dumps(payload, sort_keys=True, separators=(",", ":")).encode("utf-8") + b"\n"


def validate_installed_checker_runtime_lock(
    lock: bytes, wheel: Path, installed_package: Path
) -> None:
    """Reject lock drift, including source-checkout substitution and installed tampering."""
    if not isinstance(lock, bytes) or not lock.endswith(b"\n"):
        raise _error("installed checker runtime lock is malformed")
    try:
        payload = json.loads(lock)
    except json.JSONDecodeError as exc:
        raise _error("installed checker runtime lock is malformed") from exc
    expected = installed_checker_runtime_lock(wheel, installed_package)
    if lock != expected or not isinstance(payload, dict) or payload.get("schema_version") != 1:
        raise _error("installed checker runtime lock differs from installed bytes")


def wheel_is_compatible_with_target(filename: str) -> bool:
    """Apply the fixed CPython 3.12/Linux glibc compatibility policy to one wheel."""
    try:
        _name, _version, _build, tags = parse_wheel_filename(filename)
    except InvalidWheelFilename:
        return False
    for tag in tags:
        if (
            tag.interpreter in {"py3", "py312", "py2.py3"}
            and tag.abi == "none"
            and tag.platform == "any"
        ):
            return True
        match = re.fullmatch(r"manylinux_(2)_(\d+)_x86_64", tag.platform)
        if match is None or int(match.group(2)) > 36:
            continue
        if tag.interpreter == "cp312" and tag.abi in {"cp312", "abi3", "none"}:
            return True
        if tag.interpreter in {"py3", "py312", "py2.py3"} and tag.abi == "none":
            return True
        abi3 = re.fullmatch(r"cp(3[0-9]{1,2})", tag.interpreter)
        if abi3 and tag.abi == "abi3" and 32 <= int(abi3.group(1)) <= 312:
            return True
    return False
