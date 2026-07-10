"""Entrypoint for certification from a pinned independently released wheel."""

from __future__ import annotations

import hashlib
import importlib
import os
import sys
import zipfile
from pathlib import Path, PurePosixPath

from .certificate import CheckerIdentity, checker_identity_from_environment


class ReleasedCheckerError(RuntimeError):
    """Raised when runtime provenance cannot prove released-wheel execution."""


def _sha256(path: Path) -> str:
    digest = hashlib.sha256()
    with path.open("rb") as handle:
        for chunk in iter(lambda: handle.read(1024 * 1024), b""):
            digest.update(chunk)
    return digest.hexdigest()


def _verify_installed_package(wheel: Path, installed_package: Path) -> None:
    """Compare every installed PDD member byte-for-byte with the pinned wheel."""
    package_parts = installed_package.parts
    package_index = max(
        index for index, part in enumerate(package_parts) if part == "pdd"
    )
    site_packages = Path(*package_parts[:package_index])
    try:
        with zipfile.ZipFile(wheel) as archive:
            wheel_members = {
                name: archive.read(name)
                for name in archive.namelist()
                if name.startswith("pdd/") and not name.endswith("/")
            }
    except (OSError, zipfile.BadZipFile, KeyError) as exc:
        raise ReleasedCheckerError("released checker wheel cannot be inspected") from exc
    if not wheel_members:
        raise ReleasedCheckerError("released checker wheel contains no PDD package")
    for member, expected in wheel_members.items():
        installed = site_packages / PurePosixPath(member)
        if installed.is_symlink() or not installed.is_file():
            raise ReleasedCheckerError(f"installed checker member is unsafe: {member}")
        if installed.read_bytes() != expected:
            raise ReleasedCheckerError(f"installed checker member differs from wheel: {member}")


def validate_released_checker_runtime(
    identity: CheckerIdentity,
    wheel_path: Path,
    *,
    package_path: Path | None = None,
    prefix: Path | None = None,
    base_prefix: Path | None = None,
) -> None:
    """Fail closed unless this process came from the pinned wheel in a venv."""
    wheel = Path(wheel_path)
    if wheel.is_symlink() or not wheel.is_file() or wheel.suffix != ".whl":
        raise ReleasedCheckerError("released checker wheel path is unsafe")
    if _sha256(wheel) != identity.wheel_sha256:
        raise ReleasedCheckerError("released checker wheel digest does not match")

    runtime_prefix = Path(prefix or sys.prefix).resolve()
    runtime_base = Path(base_prefix or sys.base_prefix).resolve()
    installed_package = Path(package_path or __file__).resolve()
    if runtime_prefix == runtime_base:
        raise ReleasedCheckerError("released checker requires an isolated environment")
    try:
        installed_package.relative_to(runtime_prefix)
    except ValueError as exc:
        raise ReleasedCheckerError(
            "released checker package is outside the isolated environment"
        ) from exc
    if "site-packages" not in installed_package.parts:
        raise ReleasedCheckerError("released checker was imported from a source checkout")
    _verify_installed_package(wheel, installed_package)


def main() -> None:
    """Verify runtime provenance, then run the strict global certify command."""
    identity = checker_identity_from_environment(require_execution_marker=False)
    wheel_value = os.environ.get("PDD_RELEASED_CHECKER_WHEEL_PATH")
    if not wheel_value:
        raise ReleasedCheckerError("PDD_RELEASED_CHECKER_WHEEL_PATH is required")
    validate_released_checker_runtime(identity, Path(wheel_value))
    os.environ["PDD_RELEASED_CHECKER_EXECUTION"] = "1"

    cli = importlib.import_module("pdd.cli").cli

    cli.main(
        args=["sync", "certify", *sys.argv[1:]],
        prog_name="pdd-sync-checker",
        standalone_mode=True,
    )


if __name__ == "__main__":
    main()
