"""Direct CLI tests for the standalone global-sync checker."""

from __future__ import annotations

import hashlib
import os
from pathlib import Path
import subprocess
import sys
import venv

import pytest
import cryptography

from pdd.sync_core.standalone_package import build_standalone_wheel


ROOT = Path(__file__).resolve().parents[1]


def test_clean_installed_console_uses_standalone_module_not_checkout(tmp_path) -> None:
    wheel = build_standalone_wheel(ROOT, tmp_path / "wheel", version="1.0.0")
    environment = tmp_path / "venv"
    venv.EnvBuilder(with_pip=True, system_site_packages=True).create(environment)
    python = environment / "bin/python"
    console = environment / "bin/pdd-sync-checker"
    subprocess.run(
        [str(python), "-m", "pip", "install", "--no-deps", str(wheel)],
        check=True,
        capture_output=True,
        text=True,
    )
    shadow = tmp_path / "shadow"
    (shadow / "pdd").mkdir(parents=True)
    (shadow / "pdd/__init__.py").write_text("raise RuntimeError('checkout imported')\n")
    environment_values = os.environ | {
        "PDD_RELEASED_CHECKER_WHEEL_PATH": str(wheel),
        "PDD_RELEASED_CHECKER_WHEEL_SHA256": hashlib.sha256(wheel.read_bytes()).hexdigest(),
        "PDD_RELEASED_CHECKER_REF": "refs/tags/v1.0.0",
        "PDD_RELEASED_CHECKER_WORKFLOW_IDENTITY": (
            "promptdriven/pdd/.github/workflows/release.yml@refs/tags/v1.0.0"
        ),
        "PYTHONPATH": str(shadow) + os.pathsep + str(Path(cryptography.__file__).parents[1]),
    }

    result = subprocess.run(
        [str(console), "--help"],
        cwd=shadow,
        env=environment_values,
        capture_output=True,
        text=True,
        check=False,
    )

    assert result.returncode == 0, result.stderr
    assert "certify" in result.stdout
    assert "pdd" not in result.stderr.lower()


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
