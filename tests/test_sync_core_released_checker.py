"""Tests for pinned released-checker runtime provenance."""

import hashlib
from pathlib import Path
import zipfile

import pytest

from pdd.sync_core import CheckerIdentity, checker_identity_from_environment
from pdd.sync_core.released_checker import (
    ReleasedCheckerError,
    validate_released_checker_runtime,
)


def _wheel(tmp_path: Path) -> tuple[Path, CheckerIdentity, Path, Path]:
    wheel = tmp_path / "pdd-1.0-py3-none-any.whl"
    member = "pdd/sync_core/released_checker.py"
    content = b"exact installed checker bytes\n"
    with zipfile.ZipFile(wheel, "w") as archive:
        archive.writestr(member, content)
    prefix = tmp_path / "venv"
    package = prefix / "lib/python3.12/site-packages" / member
    package.parent.mkdir(parents=True)
    package.write_bytes(content)
    identity = CheckerIdentity(
        hashlib.sha256(wheel.read_bytes()).hexdigest(),
        "refs/tags/v1.0.0",
        "promptdriven/pdd/.github/workflows/global-sync.yml@refs/tags/v1.0.0",
    )
    return wheel, identity, prefix, package


def test_pinned_wheel_in_isolated_site_packages_is_accepted(tmp_path) -> None:
    wheel, identity, prefix, package = _wheel(tmp_path)
    validate_released_checker_runtime(
        identity,
        wheel,
        package_path=package,
        prefix=prefix,
        base_prefix=tmp_path / "system",
    )


def test_modified_wheel_is_rejected(tmp_path) -> None:
    wheel, identity, prefix, package = _wheel(tmp_path)
    wheel.write_bytes(b"modified after pinning")
    with pytest.raises(ReleasedCheckerError, match="digest does not match"):
        validate_released_checker_runtime(
            identity,
            wheel,
            package_path=package,
            prefix=prefix,
            base_prefix=tmp_path / "system",
        )


def test_source_checkout_import_is_rejected(tmp_path) -> None:
    wheel, identity, prefix, _package = _wheel(tmp_path)
    with pytest.raises(ReleasedCheckerError, match="source checkout"):
        validate_released_checker_runtime(
            identity,
            wheel,
            package_path=tmp_path / "venv/src/pdd/sync_core/released_checker.py",
            prefix=prefix,
            base_prefix=tmp_path / "system",
        )


def test_modified_installed_checker_is_rejected(tmp_path) -> None:
    wheel, identity, prefix, package = _wheel(tmp_path)
    package.write_bytes(b"modified installed checker\n")
    with pytest.raises(ReleasedCheckerError, match="differs from wheel"):
        validate_released_checker_runtime(
            identity,
            wheel,
            package_path=package,
            prefix=prefix,
            base_prefix=tmp_path / "system",
        )


def test_global_identity_requires_released_entrypoint_marker(monkeypatch) -> None:
    monkeypatch.setenv("PDD_RELEASED_CHECKER_WHEEL_SHA256", "c" * 64)
    monkeypatch.setenv("PDD_RELEASED_CHECKER_REF", "refs/tags/v1.0.0")
    monkeypatch.setenv(
        "PDD_RELEASED_CHECKER_WORKFLOW_IDENTITY",
        "promptdriven/pdd/.github/workflows/global-sync.yml@refs/tags/v1.0.0",
    )
    monkeypatch.delenv("PDD_RELEASED_CHECKER_EXECUTION", raising=False)
    with pytest.raises(ValueError, match="pdd-sync-checker"):
        checker_identity_from_environment()
    monkeypatch.setenv("PDD_RELEASED_CHECKER_EXECUTION", "1")
    assert checker_identity_from_environment().wheel_sha256 == "c" * 64
