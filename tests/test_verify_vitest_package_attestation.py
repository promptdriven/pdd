"""Executable contracts for installed-wheel Vitest package attestations."""

# pylint: disable=too-many-arguments,too-many-locals,too-many-positional-arguments

from __future__ import annotations

import hashlib
import json
import stat
import subprocess
import sys
from pathlib import Path


SCRIPT = (
    Path(__file__).parents[1]
    / "scripts"
    / "verify_vitest_package_attestation.py"
)


def _git(repository: Path, *arguments: str) -> str:
    completed = subprocess.run(
        ["git", *arguments],
        cwd=repository,
        check=True,
        capture_output=True,
        text=True,
    )
    return completed.stdout.strip()


def _fixture(tmp_path: Path) -> tuple[Path, Path, Path, str, str]:
    repository = tmp_path / "reviewed"
    runner = repository / "pdd" / "sync_core" / "runner.py"
    runner.parent.mkdir(parents=True)
    (repository / "pdd" / "__init__.py").write_text("", encoding="utf-8")
    (runner.parent / "__init__.py").write_text("", encoding="utf-8")
    runner.write_text("VALUE = 'reviewed-installed-runner'\n", encoding="utf-8")
    _git(repository, "init", "-q")
    _git(repository, "config", "user.email", "package@example.com")
    _git(repository, "config", "user.name", "Package Attestation")
    _git(repository, "add", ".")
    _git(repository, "commit", "-q", "-m", "reviewed runner")
    head = _git(repository, "rev-parse", "HEAD")
    producer_sha256 = hashlib.sha256(runner.read_bytes()).hexdigest()

    wheel = tmp_path / "pdd_cli-0-py3-none-any.whl"
    wheel.write_bytes(b"deterministic-test-wheel")
    environment = tmp_path / "wheel-environment"
    subprocess.run([sys.executable, "-m", "venv", environment], check=True)
    installed_python = environment / "bin" / "python"
    site_packages = Path(subprocess.run(
        [installed_python, "-I", "-c", "import sysconfig; print(sysconfig.get_path('purelib'))"],
        check=True,
        capture_output=True,
        text=True,
    ).stdout.strip())
    installed = site_packages / "pdd" / "sync_core"
    installed.mkdir(parents=True)
    (installed.parent / "__init__.py").write_text("", encoding="utf-8")
    (installed / "__init__.py").write_text("", encoding="utf-8")
    (installed / "runner.py").write_bytes(runner.read_bytes())
    return repository, wheel, installed_python, head, producer_sha256


def _arguments(
    artifact: Path,
    repository: Path,
    wheel: Path,
    installed_python: Path,
    head: str,
    producer_sha256: str,
) -> list[str]:
    return [
        "--attestation", str(artifact),
        "--wheel", str(wheel),
        "--installed-python", str(installed_python),
        "--repository", str(repository),
        "--diagnostic-head-sha", head,
        "--producer-sha256", producer_sha256,
    ]


def test_package_attestation_create_and_verify_real_installed_import(
    tmp_path: Path,
) -> None:
    """The real helper binds a canonical wheel/head/import proof and checksum."""
    repository, wheel, installed_python, head, producer_sha256 = _fixture(tmp_path)
    evidence = tmp_path / "evidence"
    evidence.mkdir(mode=0o700)
    artifact = evidence / "vitest-wheel-package-attestation-v1.json"
    arguments = _arguments(
        artifact, repository, wheel, installed_python, head, producer_sha256,
    )

    created = subprocess.run(
        [sys.executable, SCRIPT, "create", *arguments],
        check=False,
        capture_output=True,
        text=True,
    )
    assert created.returncode == 0, created.stderr
    encoded = artifact.read_bytes()
    payload = json.loads(encoded)
    assert payload == {
        "schema": "vitest-wheel-package-attestation-v1",
        "diagnostic_head_sha": head,
        "wheel_sha256": hashlib.sha256(wheel.read_bytes()).hexdigest(),
        "producer_sha256": producer_sha256,
        "installed_runner_sha256": producer_sha256,
        "import_origin": "installed-wheel",
    }
    assert encoded == (
        json.dumps(payload, sort_keys=True, separators=(",", ":")) + "\n"
    ).encode("ascii")
    assert stat.S_IMODE(artifact.stat().st_mode) == 0o600
    sidecar = Path(str(artifact) + ".sha256")
    artifact_sha256 = hashlib.sha256(encoded).hexdigest()
    assert sidecar.read_text(encoding="ascii") == artifact_sha256 + "\n"
    assert stat.S_IMODE(sidecar.stat().st_mode) == 0o600

    verified = subprocess.run(
        [
            sys.executable, SCRIPT, "verify", *arguments,
            "--attestation-sha256", artifact_sha256,
        ],
        check=False,
        capture_output=True,
        text=True,
    )
    assert verified.returncode == 0, verified.stderr

    wrong_head = subprocess.run(
        [
            sys.executable, SCRIPT, "verify",
            *_arguments(
                artifact, repository, wheel, installed_python, "0" * 40,
                producer_sha256,
            ),
            "--attestation-sha256", artifact_sha256,
        ],
        check=False,
        capture_output=True,
        text=True,
    )
    assert wrong_head.returncode == 1
    assert wrong_head.stderr == "Vitest package attestation rejected\n"

    wheel.write_bytes(b"changed-wheel")
    rejected = subprocess.run(
        [
            sys.executable, SCRIPT, "verify", *arguments,
            "--attestation-sha256", artifact_sha256,
        ],
        check=False,
        capture_output=True,
        text=True,
    )
    assert rejected.returncode == 1
    assert rejected.stderr == "Vitest package attestation rejected\n"


def test_package_attestation_rejects_source_checkout_import_and_head_mismatch(
    tmp_path: Path,
) -> None:
    """An isolated interpreter cannot attest a source import or another head."""
    repository, wheel, installed_python, head, producer_sha256 = _fixture(tmp_path)
    site_packages = Path(subprocess.run(
        [installed_python, "-I", "-c", "import sysconfig; print(sysconfig.get_path('purelib'))"],
        check=True,
        capture_output=True,
        text=True,
    ).stdout.strip())
    installed_pdd = site_packages / "pdd"
    (installed_pdd / "__init__.py").write_text(
        f"__path__ = [{str(repository / 'pdd')!r}]\n", encoding="utf-8",
    )
    artifact = tmp_path / "source-rejected" / "attestation.json"
    artifact.parent.mkdir(mode=0o700)
    arguments = _arguments(
        artifact, repository, wheel, installed_python, head, producer_sha256,
    )

    source_rejected = subprocess.run(
        [sys.executable, SCRIPT, "create", *arguments],
        check=False,
        capture_output=True,
        text=True,
    )
    assert source_rejected.returncode == 1
    assert source_rejected.stderr == "Vitest package attestation rejected\n"
    assert str(repository) not in source_rejected.stderr
    assert not artifact.exists()
