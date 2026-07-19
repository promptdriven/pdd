"""Contract tests for the standalone global-sync checker wheel."""

from __future__ import annotations

import json
from pathlib import Path
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
    "mutation", ["absolute-import", "missing", "extra", "symlink", "root-symlink"]
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
        target = source / "pdd/sync_core" / data
        target.write_bytes((ROOT / "pdd/sync_core" / data).read_bytes())
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
    else:
        linked_source = tmp_path / "linked-source"
        linked_source.symlink_to(source, target_is_directory=True)
        source = linked_source

    with pytest.raises(StandalonePackageError):
        build_standalone_wheel(source, tmp_path / "wheel", version="1.0.0")


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


def test_runtime_lock_is_generated_and_validated_from_installed_checker_bytes(tmp_path) -> None:
    wheel = build_standalone_wheel(ROOT, tmp_path / "wheel", version="1.0.0")
    installed = tmp_path / "installed"
    subprocess.run(
        [sys.executable, "-m", "pip", "install", "--no-deps", "--target", str(installed), str(wheel)],
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


def test_z3_manylinux_227_is_accepted_only_for_the_supported_glibc_target() -> None:
    manifest = load_standalone_manifest(ROOT)

    assert manifest["target"]["glibc"] == "2.36"
    assert wheel_is_compatible_with_target(
        "z3_solver-4.16.0.0-py3-none-manylinux_2_27_x86_64.whl"
    )
    assert not wheel_is_compatible_with_target(
        "z3_solver-4.16.0.0-py3-none-manylinux_2_37_x86_64.whl"
    )
