#!/usr/bin/env python3
"""Create and verify the installed-wheel Vitest package attestation."""

# pylint: disable=too-many-boolean-expressions,unidiomatic-typecheck

from __future__ import annotations

import argparse
import hashlib
import json
import os
import secrets
import stat
import subprocess
import sys
from pathlib import Path


_SCHEMA = "vitest-wheel-package-attestation-v1"
_FIELDS = frozenset({
    "schema",
    "diagnostic_head_sha",
    "wheel_sha256",
    "producer_sha256",
    "installed_runner_sha256",
    "import_origin",
})
_MAX_BYTES = 4096
_IMPORT_PROBE = """
import json
import sys
from pathlib import Path

import pdd
import pdd.sync_core.runner as runner

print(json.dumps({
    "prefix": str(Path(sys.prefix).resolve()),
    "package": str(Path(pdd.__file__).resolve()),
    "runner": str(Path(runner.__file__).resolve()),
}, sort_keys=True, separators=(",", ":")))
"""


class AttestationError(ValueError):
    """A deliberately non-reflective package-attestation rejection."""


def _is_digest(value: object, length: int) -> bool:
    """Return whether a value is exact lowercase hexadecimal."""
    return (
        type(value) is str
        and len(value) == length
        and all(character in "0123456789abcdef" for character in value)
    )


def _sha256(path: Path) -> str:
    """Hash one verifier-controlled regular file without loading it whole."""
    digest = hashlib.sha256()
    with path.open("rb") as handle:
        while chunk := handle.read(1024 * 1024):
            digest.update(chunk)
    return digest.hexdigest()


def _regular_file(path: Path) -> Path:
    """Resolve and require a non-symlink regular file."""
    metadata = path.lstat()
    if stat.S_ISLNK(metadata.st_mode) or not stat.S_ISREG(metadata.st_mode):
        raise AttestationError
    return path.resolve(strict=True)


def _git_head(repository: Path) -> str:
    """Measure the exact checked-out repository head."""
    completed = subprocess.run(
        ["git", "rev-parse", "HEAD"],
        cwd=repository,
        check=True,
        capture_output=True,
        text=True,
    )
    head = completed.stdout.strip()
    if not _is_digest(head, 40):
        raise AttestationError
    return head


def _measure_installed_runner(
    installed_python: Path,
    repository: Path,
    producer_sha256: str,
) -> str:
    """Prove an isolated interpreter imports the reviewed runner from its venv."""
    interpreter = installed_python.resolve(strict=True)
    if not interpreter.is_file():
        raise AttestationError
    environment = dict(os.environ)
    environment.pop("PYTHONPATH", None)
    environment["PYTHONNOUSERSITE"] = "1"
    completed = subprocess.run(
        [str(installed_python), "-I", "-c", _IMPORT_PROBE],
        cwd=repository.parent,
        env=environment,
        check=True,
        capture_output=True,
        text=True,
    )
    try:
        measured = json.loads(completed.stdout)
    except json.JSONDecodeError as exc:
        raise AttestationError from exc
    if type(measured) is not dict or set(measured) != {
        "prefix", "package", "runner",
    } or any(type(value) is not str for value in measured.values()):
        raise AttestationError
    prefix = Path(measured["prefix"]).resolve(strict=True)
    package = Path(measured["package"]).resolve(strict=True)
    runner = Path(measured["runner"])
    runner_metadata = runner.lstat()
    runner = runner.resolve(strict=True)
    if (
        stat.S_ISLNK(runner_metadata.st_mode)
        or not stat.S_ISREG(runner_metadata.st_mode)
        or not package.is_relative_to(prefix)
        or not runner.is_relative_to(prefix)
        or package.is_relative_to(repository)
        or runner.is_relative_to(repository)
        or "site-packages" not in package.parts
        or "site-packages" not in runner.parts
    ):
        raise AttestationError
    installed_digest = _sha256(runner)
    if installed_digest != producer_sha256:
        raise AttestationError
    return installed_digest


def _measure(
    repository: Path,
    wheel: Path,
    installed_python: Path,
    diagnostic_head_sha: str,
    producer_sha256: str,
) -> dict[str, str]:
    """Measure every package-attestation binding from local trusted state."""
    if not _is_digest(diagnostic_head_sha, 40) or not _is_digest(
        producer_sha256, 64,
    ):
        raise AttestationError
    repository = repository.resolve(strict=True)
    if _git_head(repository) != diagnostic_head_sha:
        raise AttestationError
    source_runner = _regular_file(repository / "pdd/sync_core/runner.py")
    if _sha256(source_runner) != producer_sha256:
        raise AttestationError
    wheel = _regular_file(wheel)
    installed_digest = _measure_installed_runner(
        installed_python, repository, producer_sha256,
    )
    return {
        "schema": _SCHEMA,
        "diagnostic_head_sha": diagnostic_head_sha,
        "wheel_sha256": _sha256(wheel),
        "producer_sha256": producer_sha256,
        "installed_runner_sha256": installed_digest,
        "import_origin": "installed-wheel",
    }


def _atomic_write(path: Path, content: bytes) -> None:
    """Atomically write a mode-0600 regular file in a protected directory."""
    directory = path.parent
    metadata = directory.stat()
    if not stat.S_ISDIR(metadata.st_mode) or stat.S_IMODE(metadata.st_mode) & 0o022:
        raise AttestationError
    temporary = path.with_name(f".{path.name}.{secrets.token_hex(16)}.tmp")
    descriptor = os.open(
        temporary,
        os.O_WRONLY | os.O_CREAT | os.O_EXCL | getattr(os, "O_NOFOLLOW", 0),
        0o600,
    )
    try:
        remaining = memoryview(content)
        while remaining:
            written = os.write(descriptor, remaining)
            if written <= 0:
                raise AttestationError
            remaining = remaining[written:]
        os.fsync(descriptor)
        os.fchmod(descriptor, 0o600)
    finally:
        os.close(descriptor)
    os.replace(temporary, path)


def _create(arguments: argparse.Namespace) -> None:
    """Create one canonical attestation and upload digest sidecar."""
    payload = _measure(
        Path(arguments.repository),
        Path(arguments.wheel),
        Path(arguments.installed_python),
        arguments.diagnostic_head_sha,
        arguments.producer_sha256,
    )
    encoded = (
        json.dumps(payload, sort_keys=True, separators=(",", ":")) + "\n"
    ).encode("ascii")
    destination = Path(arguments.attestation)
    _atomic_write(destination, encoded)
    _atomic_write(
        Path(str(destination) + ".sha256"),
        hashlib.sha256(encoded).hexdigest().encode("ascii") + b"\n",
    )


def _decode(path: Path, expected_sha256: str) -> dict[str, object]:
    """Strictly decode one canonical checksummed attestation."""
    if not _is_digest(expected_sha256, 64):
        raise AttestationError
    resolved = _regular_file(path)
    metadata = resolved.stat()
    directory_metadata = resolved.parent.stat()
    if (
        stat.S_IMODE(metadata.st_mode) != 0o600
        or stat.S_IMODE(directory_metadata.st_mode) & 0o022
        or not 0 < metadata.st_size <= _MAX_BYTES
    ):
        raise AttestationError
    encoded = resolved.read_bytes()
    if hashlib.sha256(encoded).hexdigest() != expected_sha256:
        raise AttestationError
    sidecar = _regular_file(Path(str(path) + ".sha256"))
    if (
        stat.S_IMODE(sidecar.stat().st_mode) != 0o600
        or sidecar.read_bytes() != expected_sha256.encode("ascii") + b"\n"
    ):
        raise AttestationError
    try:
        source = encoded.decode("ascii")
        payload = json.loads(source)
    except (UnicodeDecodeError, json.JSONDecodeError) as exc:
        raise AttestationError from exc
    if type(payload) is not dict or set(payload) != _FIELDS:
        raise AttestationError
    canonical = (
        json.dumps(payload, sort_keys=True, separators=(",", ":")) + "\n"
    ).encode("ascii")
    if encoded != canonical:
        raise AttestationError
    return payload


def _verify(arguments: argparse.Namespace) -> None:
    """Verify schema and independently remeasure every attested binding."""
    payload = _decode(
        Path(arguments.attestation), arguments.attestation_sha256,
    )
    measured = _measure(
        Path(arguments.repository),
        Path(arguments.wheel),
        Path(arguments.installed_python),
        arguments.diagnostic_head_sha,
        arguments.producer_sha256,
    )
    if payload != measured:
        raise AttestationError


def _arguments() -> argparse.Namespace:
    """Parse the exact package-attestation command surface."""
    parser = argparse.ArgumentParser()
    subparsers = parser.add_subparsers(dest="command", required=True)
    for command in ("create", "verify"):
        subparser = subparsers.add_parser(command)
        subparser.add_argument("--attestation", required=True)
        subparser.add_argument("--wheel", required=True)
        subparser.add_argument("--installed-python", required=True)
        subparser.add_argument("--repository", required=True)
        subparser.add_argument("--diagnostic-head-sha", required=True)
        subparser.add_argument("--producer-sha256", required=True)
        if command == "verify":
            subparser.add_argument("--attestation-sha256", required=True)
    return parser.parse_args()


def main() -> int:
    """Create or verify without reflecting rejected candidate-controlled data."""
    arguments = _arguments()
    try:
        if arguments.command == "create":
            _create(arguments)
        else:
            _verify(arguments)
    except (
        AttestationError,
        OSError,
        ValueError,
        subprocess.SubprocessError,
    ):
        print("Vitest package attestation rejected", file=sys.stderr)
        return 1
    print("Vitest package attestation verified")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
