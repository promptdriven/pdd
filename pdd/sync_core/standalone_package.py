"""Deterministically stage the closed standalone global-sync checker wheel."""
# pylint: disable=too-many-branches,too-many-locals,too-many-boolean-expressions

from __future__ import annotations

import ast
import base64
import hashlib
import json
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
_MODULE_NAME = re.compile(r"[a-z][a-z0-9_]*\.py")
_DEPENDENCY = re.compile(r"[A-Za-z][A-Za-z0-9-]* (?:==|>=)[^ ]+(?:,<[0-9]+)?")
_SHA256 = re.compile(r"[0-9a-f]{64}")
_ZIP_TIMESTAMP = (1980, 1, 1, 0, 0, 0)


def _error(message: str) -> StandalonePackageError:
    return StandalonePackageError(f"standalone checker package: {message}")


def _regular(path: Path, label: str) -> Path:
    if path.is_symlink() or not path.is_file():
        raise _error(f"{label} must be a regular file")
    return path


def _parse_manifest(source: Path | bytes) -> dict[str, Any]:
    if isinstance(source, bytes):
        try:
            payload = json.loads(source.decode("utf-8"))
        except (UnicodeDecodeError, json.JSONDecodeError) as exc:
            raise _error("module manifest is malformed") from exc
    else:
        _regular(source, "module manifest")
        try:
            payload = json.loads(source.read_text(encoding="utf-8"))
        except (OSError, UnicodeDecodeError, json.JSONDecodeError) as exc:
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
        or data != ["pytest_probe.py"]
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
    return payload


def load_standalone_manifest(root: Path) -> dict[str, Any]:
    """Load the one protected module/dependency authority from a safe checkout."""
    repository = Path(root).resolve()
    for component in (repository, *repository.parents):
        if component.is_symlink():
            raise _error("repository root is unsafe")
    return _parse_manifest(repository.joinpath(*_MANIFEST_PATH.parts))


def _source_path(root: Path, module: str) -> Path:
    path = root / "pdd" / "sync_core" / module
    _regular(path, f"module {module}")
    return path


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
    source = {module: _source_path(root, module).read_bytes() for module in modules}
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


def _wheel_members(root: Path, manifest: Mapping[str, Any], version: str) -> dict[str, bytes]:
    modules = _checked_module_bytes(root, manifest)
    data = {item: _source_path(root, item).read_bytes() for item in manifest["data"]}
    manifest_bytes = (root / _MANIFEST_PATH).read_bytes()
    dist_info = _dist_info(version)
    metadata = "\n".join(
        (
            "Metadata-Version: 2.1",
            f"Name: {manifest['distribution']}",
            f"Version: {version}",
            "Summary: Standalone PDD global-sync checker",
            *(f"Requires-Dist: {dependency}" for dependency in manifest["dependencies"]),
            "",
        )
    ).encode("utf-8")
    members = {
        f"{_PACKAGE}/__init__.py": b'"""Standalone global-sync checker namespace."""\n',
        **{f"{_PACKAGE}/{module}": content for module, content in modules.items()},
        **{f"{_PACKAGE}/{item}": content for item, content in data.items()},
        _EMBEDDED_MANIFEST: manifest_bytes,
        f"{dist_info}/METADATA": metadata,
        f"{dist_info}/WHEEL": (
            b"Wheel-Version: 1.0\nGenerator: pdd-standalone-checker\n"
            b"Root-Is-Purelib: true\nTag: py3-none-any\n"
        ),
        f"{dist_info}/entry_points.txt": (
            b"[console_scripts]\npdd-sync-checker = pdd_sync_checker.checker_cli:main\n"
        ),
    }
    record = "".join(
        f"{name},sha256={_record_hash(content)},{len(content)}\n"
        for name, content in sorted(members.items())
    ) + f"{dist_info}/RECORD,,\n"
    members[f"{dist_info}/RECORD"] = record.encode("ascii")
    return members


def _zip_info(name: str) -> zipfile.ZipInfo:
    info = zipfile.ZipInfo(name, date_time=_ZIP_TIMESTAMP)
    info.compress_type = zipfile.ZIP_STORED
    info.external_attr = (stat.S_IFREG | 0o644) << 16
    info.create_system = 3
    return info


def build_standalone_wheel(root: Path, output: Path, *, version: str) -> Path:
    """Build one byte-reproducible standalone wheel from manifest-authorized bytes."""
    repository = Path(root).resolve()
    manifest = load_standalone_manifest(repository)
    members = _wheel_members(repository, manifest, version)
    destination = Path(output)
    if destination.exists() and (destination.is_symlink() or not destination.is_dir()):
        raise _error("wheel output directory is unsafe")
    destination.mkdir(parents=True, exist_ok=True)
    wheel = destination / f"pdd_sync_checker-{version}-py3-none-any.whl"
    if wheel.exists() or wheel.is_symlink():
        raise _error("wheel output already exists")
    with zipfile.ZipFile(
        wheel, "w", compression=zipfile.ZIP_STORED, strict_timestamps=True
    ) as archive:
        for name, content in sorted(members.items()):
            archive.writestr(_zip_info(name), content)
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


def validate_standalone_wheel(wheel_path: Path, manifest: Mapping[str, Any]) -> None:
    """Fail closed unless the archive has exactly the manifest-authorized RECORD closure."""
    wheel = _regular(Path(wheel_path), "wheel")
    try:
        _name, _version, _build, tags = parse_wheel_filename(wheel.name)
    except InvalidWheelFilename as exc:
        raise _error("wheel filename is malformed") from exc
    if {str(tag) for tag in tags} != {"py3-none-any"}:
        raise _error("wheel tags are not standalone checker tags")
    expected_prefix = f"{manifest['package']}/"
    try:
        with zipfile.ZipFile(wheel) as archive:
            files: dict[str, bytes] = {}
            for member in archive.infolist():
                path = _safe_member(member.filename)
                mode = member.external_attr >> 16
                if member.is_dir() or stat.S_ISLNK(mode) or path.as_posix() in files:
                    raise _error("wheel contains an unsafe member")
                files[path.as_posix()] = archive.read(member)
    except (OSError, zipfile.BadZipFile) as exc:
        raise _error("wheel cannot be inspected") from exc
    if any(name.startswith("pdd/") for name in files):
        raise _error("wheel contains the pdd package")
    expected_modules = {f"{expected_prefix}__init__.py", _EMBEDDED_MANIFEST} | {
        f"{expected_prefix}{module}" for module in manifest["modules"]
    } | {f"{expected_prefix}{item}" for item in manifest["data"]}
    dist_infos = {PurePosixPath(name).parts[0] for name in files if ".dist-info/" in name}
    if len(dist_infos) != 1:
        raise _error("wheel dist-info closure is invalid")
    dist_info = next(iter(dist_infos))
    expected = expected_modules | {
        f"{dist_info}/METADATA",
        f"{dist_info}/WHEEL",
        f"{dist_info}/entry_points.txt",
        f"{dist_info}/RECORD",
    }
    if set(files) != expected:
        raise _error("wheel member closure is invalid")
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
    wheel = _regular(Path(wheel_path), "wheel")
    try:
        with zipfile.ZipFile(wheel) as archive:
            files: dict[str, bytes] = {}
            for member in archive.infolist():
                path = _safe_member(member.filename)
                mode = member.external_attr >> 16
                if member.is_dir() or stat.S_ISLNK(mode) or path.as_posix() in files:
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
    path = _regular(Path(installed_package), "installed checker module")
    try:
        package_index = max(
            index for index, part in enumerate(path.parts) if part == _PACKAGE
        )
    except ValueError as exc:
        raise _error("installed checker module is outside its package") from exc
    package_root = Path(*path.parts[: package_index + 1])
    for relative, expected_bytes in expected.items():
        candidate = package_root / relative
        if (
            candidate.is_symlink()
            or not candidate.is_file()
            or candidate.read_bytes() != expected_bytes
        ):
            raise _error("installed checker bytes differ from the wheel")
    for candidate in package_root.rglob("*"):
        relative = candidate.relative_to(package_root)
        if "__pycache__" in relative.parts:
            continue
        if candidate.is_symlink() or (
            candidate.is_file() and relative.as_posix() not in expected
        ):
            raise _error("installed checker closure differs from the wheel")
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
        "wheel_sha256": hashlib.sha256(_regular(wheel, "wheel").read_bytes()).hexdigest(),
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
