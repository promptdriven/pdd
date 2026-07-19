"""Direct CLI tests for the standalone global-sync checker."""

from __future__ import annotations

import hashlib
import json
import os
from pathlib import Path
import subprocess
import sys
import venv

import pytest

from pdd.sync_core.standalone_package import (
    build_standalone_wheel,
)


ROOT = Path(__file__).resolve().parents[1]


def test_clean_installed_console_uses_standalone_module_not_checkout(tmp_path) -> None:
    wheel = build_standalone_wheel(ROOT, tmp_path / "wheel", version="1.0.0")
    environment = tmp_path / "venv"
    venv.EnvBuilder(with_pip=True).create(environment)
    python = environment / "bin/python"
    console = environment / "bin/pdd-sync-checker"
    subprocess.run(
        [str(python), "-m", "pip", "install", "--no-compile", str(wheel)],
        check=True,
        capture_output=True,
        text=True,
    )
    shadow = tmp_path / "candidate"
    subprocess.run(
        ["git", "clone", "-q", "--no-hardlinks", str(ROOT), str(shadow)],
        check=True,
        capture_output=True,
    )
    marker = tmp_path / "shadow-imported"
    shadow_code = (
        "from pathlib import Path\n"
        f"Path({str(marker)!r}).write_text('shadow imported', encoding='utf-8')\n"
        "raise RuntimeError('candidate shadow imported')\n"
    )
    (shadow / "pdd/__init__.py").write_text(shadow_code, encoding="utf-8")
    (shadow / "pdd_sync_checker").mkdir()
    (shadow / "pdd_sync_checker/__init__.py").write_text(
        shadow_code, encoding="utf-8"
    )
    environment_values = os.environ | {
        "PDD_RELEASED_CHECKER_WHEEL_PATH": str(wheel),
        "PDD_RELEASED_CHECKER_WHEEL_SHA256": hashlib.sha256(wheel.read_bytes()).hexdigest(),
        "PDD_RELEASED_CHECKER_REF": "refs/tags/v1.0.0",
        "PDD_RELEASED_CHECKER_WORKFLOW_IDENTITY": (
            "promptdriven/pdd/.github/workflows/release.yml@refs/tags/v1.0.0"
        ),
        "PYTHONPATH": str(shadow),
    }

    help_result = subprocess.run(
        [str(console), "--help"],
        cwd=shadow,
        env=environment_values,
        capture_output=True,
        text=True,
        check=False,
    )
    result = subprocess.run(
        [str(console), "certify", "--base-ref", "HEAD", "--head-ref", "HEAD"],
        cwd=shadow,
        env=environment_values,
        capture_output=True,
        text=True,
        check=False,
    )

    assert help_result.returncode == 0, help_result.stderr
    assert "certify" in help_result.stdout
    report = json.loads(result.stdout)
    assert result.returncode in {0, 1}, result.stderr
    assert report["schema_version"] == 1
    assert "counts" in report and "units" in report
    assert "cannot read language registry" not in result.stdout
    assert not marker.exists()
    assert not list((environment / "lib").rglob("__pycache__"))

    package_root = next(
        (environment / "lib").glob("python*/site-packages/pdd_sync_checker")
    )
    malicious_pyc = package_root / "__pycache__/checker_cli.cpython-312.pyc"
    malicious_pyc.parent.mkdir()
    malicious_pyc.write_bytes(b"malicious bytecode")
    pyc_result = subprocess.run(
        [str(console), "--help"],
        cwd=shadow,
        env=environment_values,
        capture_output=True,
        text=True,
        check=False,
    )
    assert pyc_result.returncode != 0
    malicious_pyc.unlink()
    malicious_pyc.parent.rmdir()

    malicious_fifo = package_root / "malicious"
    os.mkfifo(malicious_fifo)
    fifo_result = subprocess.run(
        [str(console), "--help"],
        cwd=shadow,
        env=environment_values,
        capture_output=True,
        text=True,
        check=False,
    )
    assert fifo_result.returncode != 0


def test_direct_cli_rejects_candidate_arguments_before_loading_them(monkeypatch, tmp_path) -> None:
    from pdd.sync_core import checker_cli

    monkeypatch.setattr(checker_cli, "_validated_runtime_identity", lambda: object())
    monkeypatch.setattr(
        checker_cli,
        "_evidence_main",
        lambda _arguments: (_ for _ in ()).throw(
            checker_cli.CheckerCliError("regular JSON input is required")
        ),
    )

    with pytest.raises(checker_cli.CheckerCliError, match="regular JSON"):
        checker_cli.main(("release-pin-evidence", "--ledger-source", str(tmp_path / "missing")))


def test_direct_cli_help_requires_runtime_provenance(monkeypatch) -> None:
    from pdd.sync_core import checker_cli

    monkeypatch.setattr(
        checker_cli,
        "_validated_runtime_identity",
        lambda: (_ for _ in ()).throw(
            checker_cli.ReleasedCheckerError("provenance failed")
        ),
    )

    with pytest.raises(checker_cli.CheckerCliError, match="provenance failed"):
        checker_cli.main(("--help",))
