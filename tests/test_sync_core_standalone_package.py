"""Contract tests for the standalone global-sync checker wheel."""

from __future__ import annotations

import base64
import hashlib
import json
import os
from pathlib import Path
import stat
import subprocess
import sys
import zipfile

import pytest

from pdd.sync_core.standalone_package import (
    StandalonePackageError,
    build_standalone_wheel,
    installed_checker_runtime_lock,
    load_standalone_manifest,
    validate_installed_checker_runtime_lock,
    validate_standalone_wheel,
    wheel_is_compatible_with_target,
)


ROOT = Path(__file__).resolve().parents[1]


def _record_hash(content: bytes) -> str:
    return base64.urlsafe_b64encode(
        hashlib.sha256(content).digest()
    ).rstrip(b"=").decode("ascii")


def _rerecorded_mutation(
    source_path: Path, target_path: Path, mutation: str
) -> Path:
    target_path.parent.mkdir(parents=True)
    with zipfile.ZipFile(source_path) as source:
        contents = {
            entry.filename: source.read(entry.filename)
            for entry in source.infolist()
        }
        infos = {entry.filename: entry for entry in source.infolist()}
    record_name = next(
        name for name in contents if name.endswith(".dist-info/RECORD")
    )
    if mutation == "dependency":
        metadata = next(name for name in contents if name.endswith(".dist-info/METADATA"))
        contents[metadata] += b"Requires-Dist: attacker >=1\n"
    elif mutation == "bootstrap":
        bootstrap = next(
            name for name in contents if name.endswith(".data/scripts/pdd-sync-checker")
        )
        contents[bootstrap] += b"\n# attacker entrypoint\n"
    elif mutation == "wheel":
        wheel = next(name for name in contents if name.endswith(".dist-info/WHEEL"))
        contents[wheel] += b"Generator: attacker\n"
    elif mutation == "manifest":
        manifest = next(
            name for name in contents if name.endswith("standalone-checker-modules.json")
        )
        contents[manifest] += b" "
    elif mutation == "dist-info":
        original = record_name.split("/", 1)[0]
        replacement = "attacker-1.0.0.dist-info"
        contents = {
            name.replace(f"{original}/", f"{replacement}/", 1): content
            if name.startswith(f"{original}/")
            else content
            for name, content in contents.items()
        }
        infos = {
            name.replace(f"{original}/", f"{replacement}/", 1): info
            if name.startswith(f"{original}/")
            else info
            for name, info in infos.items()
        }
        record_name = f"{replacement}/RECORD"
    elif mutation == "nonregular-mode":
        member = "pdd_sync_checker/checker_cli.py"
        infos[member].external_attr = (stat.S_IFIFO | 0o644) << 16
    else:
        raise AssertionError(f"unknown mutation: {mutation}")

    contents[record_name] = (
        "".join(
            f"{name},sha256={_record_hash(content)},{len(content)}\n"
            for name, content in sorted(contents.items())
            if name != record_name
        )
        + f"{record_name},,\n"
    ).encode("ascii")
    with zipfile.ZipFile(target_path, "w") as target:
        for name, content in sorted(contents.items()):
            info = infos[name]
            if info.filename != name:
                renamed = zipfile.ZipInfo(name, date_time=info.date_time)
                renamed.compress_type = info.compress_type
                renamed.create_system = info.create_system
                renamed.external_attr = info.external_attr
                info = renamed
            target.writestr(info, content)
    return target_path


def test_builder_is_reproducible_and_copies_only_closed_checker_modules(tmp_path) -> None:
    manifest = load_standalone_manifest(ROOT)
    first = build_standalone_wheel(ROOT, tmp_path / "first", version="1.0.0")
    second = build_standalone_wheel(ROOT, tmp_path / "second", version="1.0.0")

    assert first.read_bytes() == second.read_bytes()
    with zipfile.ZipFile(first) as wheel:
        names = set(wheel.namelist())
        assert not any(name.startswith("pdd/") for name in names)
        assert "pdd_sync_checker/checker_cli.py" in names
        assert "pdd_sync_checker/released_checker.py" in names
        assert "pdd_sync_checker/data/language_format.csv" in names
        assert any(name.endswith(".data/scripts/pdd-sync-checker") for name in names)
        assert all(
            wheel.read(f"pdd_sync_checker/{module}")
            == (ROOT / "pdd" / "sync_core" / module).read_bytes()
            for module in manifest["modules"]
        )
        metadata = next(name for name in names if name.endswith(".dist-info/METADATA"))
        assert "Requires-Dist: z3-solver" not in wheel.read(metadata).decode("utf-8")
        assert "Requires-Dist: packaging >=24,<26" in wheel.read(metadata).decode("utf-8")
        assert "Requires-Dist: pytest ==9.0.3" in wheel.read(metadata).decode("utf-8")
    validate_standalone_wheel(first, manifest)


@pytest.mark.parametrize(
    "mutation",
    [
        "absolute-import",
        "missing",
        "extra",
        "symlink",
        "root-symlink",
        "sync-core-symlink",
    ],
)
def test_builder_rejects_unclosed_or_unsafe_manifest_inputs(tmp_path, mutation: str) -> None:
    source = tmp_path / "source"
    source.mkdir()
    manifest = json.loads(
        (ROOT / ".pdd/global-sync/standalone-checker-modules.json").read_text(
            encoding="utf-8"
        )
    )
    (source / "pdd/sync_core").mkdir(parents=True)
    for module in manifest["modules"]:
        target = source / "pdd/sync_core" / module
        target.parent.mkdir(parents=True, exist_ok=True)
        target.write_bytes((ROOT / "pdd/sync_core" / module).read_bytes())
    for data in manifest["data"]:
        data_source = (
            Path(data["source"])
            if isinstance(data, dict)
            else Path("pdd/sync_core") / data
        )
        target = source / data_source
        target.parent.mkdir(parents=True, exist_ok=True)
        target.write_bytes((ROOT / data_source).read_bytes())
    (source / ".pdd/global-sync").mkdir(parents=True)
    manifest_path = source / ".pdd/global-sync/standalone-checker-modules.json"
    manifest_path.write_text(json.dumps(manifest), encoding="utf-8")

    if mutation == "absolute-import":
        (source / "pdd/sync_core/checker_cli.py").write_text("import pdd.cli\n")
    elif mutation == "missing":
        (source / "pdd/sync_core" / manifest["modules"][0]).unlink()
    elif mutation == "extra":
        (source / "pdd/sync_core/unlisted.py").write_text("VALUE = 1\n")
        manifest["modules"].append("unlisted.py")
        manifest_path.write_text(json.dumps(manifest), encoding="utf-8")
    elif mutation == "symlink":
        target = source / "pdd/sync_core" / manifest["modules"][0]
        copied = source / "copied.py"
        copied.write_bytes(target.read_bytes())
        target.unlink()
        target.symlink_to(copied)
    elif mutation == "root-symlink":
        linked_source = tmp_path / "linked-source"
        linked_source.symlink_to(source, target_is_directory=True)
        source = linked_source
    else:
        sync_core = source / "pdd/sync_core"
        copied = source / "copied-sync-core"
        sync_core.rename(copied)
        sync_core.symlink_to(copied, target_is_directory=True)

    with pytest.raises(StandalonePackageError):
        build_standalone_wheel(source, tmp_path / "wheel", version="1.0.0")


def test_builder_rejects_symlinked_output_parent(tmp_path) -> None:
    real_output = tmp_path / "real-output"
    real_output.mkdir()
    linked_output = tmp_path / "linked-output"
    linked_output.symlink_to(real_output, target_is_directory=True)

    with pytest.raises(StandalonePackageError, match="output"):
        build_standalone_wheel(ROOT, linked_output / "wheel", version="1.0.0")


def test_wheel_validation_rejects_record_and_member_tampering(tmp_path) -> None:
    wheel = build_standalone_wheel(ROOT, tmp_path / "wheel", version="1.0.0")
    manifest = load_standalone_manifest(ROOT)
    tampered = tmp_path / "tampered" / wheel.name
    tampered.parent.mkdir()
    with zipfile.ZipFile(wheel) as source, zipfile.ZipFile(tampered, "w") as target:
        for entry in source.infolist():
            content = source.read(entry.filename)
            if entry.filename.endswith("pdd_sync_checker/checker_cli.py"):
                content += b"# modified\n"
            target.writestr(entry, content)

    with pytest.raises(StandalonePackageError, match="RECORD"):
        validate_standalone_wheel(tampered, manifest)


@pytest.mark.parametrize(
    "mutation",
    [
        "dependency",
        "bootstrap",
        "wheel",
        "manifest",
        "dist-info",
        "nonregular-mode",
    ],
)
def test_wheel_validation_rejects_rerecorded_authority_mutations(
    tmp_path, mutation: str
) -> None:
    wheel = build_standalone_wheel(ROOT, tmp_path / "wheel", version="1.0.0")
    manifest = load_standalone_manifest(ROOT)
    tampered = _rerecorded_mutation(
        wheel, tmp_path / "tampered" / mutation / wheel.name, mutation
    )

    with pytest.raises(StandalonePackageError):
        validate_standalone_wheel(tampered, manifest)


def test_runtime_lock_is_generated_and_validated_from_installed_checker_bytes(tmp_path) -> None:
    wheel = build_standalone_wheel(ROOT, tmp_path / "wheel", version="1.0.0")
    installed = tmp_path / "installed"
    subprocess.run(
        [
            sys.executable,
            "-m",
            "pip",
            "install",
            "--no-compile",
            "--no-deps",
            "--target",
            str(installed),
            str(wheel),
        ],
        check=True,
        capture_output=True,
        text=True,
    )
    package = installed / "pdd_sync_checker" / "released_checker.py"

    lock = installed_checker_runtime_lock(wheel, package)
    validate_installed_checker_runtime_lock(lock, wheel, package)
    package.write_bytes(package.read_bytes() + b"# tampered\n")

    with pytest.raises(StandalonePackageError, match="installed"):
        validate_installed_checker_runtime_lock(lock, wheel, package)


@pytest.mark.parametrize("mutation", ["pyc", "nonregular"])
def test_runtime_lock_rejects_unlisted_installed_entry(
    tmp_path, mutation: str
) -> None:
    wheel = build_standalone_wheel(ROOT, tmp_path / "wheel", version="1.0.0")
    installed = tmp_path / "installed"
    subprocess.run(
        [
            sys.executable,
            "-m",
            "pip",
            "install",
            "--no-compile",
            "--no-deps",
            "--target",
            str(installed),
            str(wheel),
        ],
        check=True,
        capture_output=True,
        text=True,
    )
    package_root = installed / "pdd_sync_checker"
    if mutation == "pyc":
        malicious = package_root / "__pycache__/checker_cli.cpython-312.pyc"
        malicious.parent.mkdir()
        malicious.write_bytes(b"malicious bytecode")
    else:
        os.mkfifo(package_root / "malicious")

    with pytest.raises(StandalonePackageError, match="installed"):
        installed_checker_runtime_lock(
            wheel, package_root / "released_checker.py"
        )


def test_z3_manylinux_227_is_accepted_only_for_the_supported_glibc_target() -> None:
    manifest = load_standalone_manifest(ROOT)

    assert manifest["target"]["glibc"] == "2.36"
    assert wheel_is_compatible_with_target(
        "z3_solver-4.16.0.0-py3-none-manylinux_2_27_x86_64.whl"
    )
    assert not wheel_is_compatible_with_target(
        "z3_solver-4.16.0.0-py3-none-manylinux_2_37_x86_64.whl"
    )
