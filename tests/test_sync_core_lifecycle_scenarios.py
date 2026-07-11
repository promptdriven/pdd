"""Process-level merge, wheel, and real-consumer lifecycle scenarios."""

import argparse
import os
import json
import subprocess
import sys
from pathlib import Path, PurePosixPath

import pytest

from pdd.sync_core.certificate import LifecycleResult
from pdd.sync_core.lifecycle import _isolated_lifecycle_environment
from pdd.sync_core.scenario_contract import REQUIRED_SCENARIOS
from pdd.sync_core import scenario_harness
from pdd.sync_core import (
    PlannedWrite,
    TransactionConflict,
    TransactionManager,
    build_unit_manifest,
)
from pdd.sync_core.identity import initialize_repository_identity


def _run(root: Path, *args: str, env=None) -> subprocess.CompletedProcess[str]:
    return subprocess.run(
        args,
        cwd=root,
        capture_output=True,
        text=True,
        check=False,
        env=env,
    )


def _git(root: Path, *args: str) -> str:
    result = _run(root, "git", *args)
    assert result.returncode == 0, result.stderr
    return result.stdout.strip()


def _record_metric(name: str, value: int) -> None:
    configured = os.environ.get("PDD_LIFECYCLE_METRICS_PATH")
    if not configured:
        return
    path = Path(configured)
    payload = json.loads(path.read_text()) if path.exists() else {}
    payload[name] = value
    path.write_text(json.dumps(payload, sort_keys=True))


def test_lifecycle_contract_requires_public_repair_injection_scenarios() -> None:
    required = {
        "public-prompt-only-repair-zero-write-rerun",
        "public-code-only-repair-zero-write-rerun",
        "public-test-only-repair-zero-write-rerun",
        "public-include-only-repair-zero-write-rerun",
        "public-simultaneous-edit-repair-block",
    }
    assert required <= REQUIRED_SCENARIOS


def test_lifecycle_predicate_requires_dependency_environment_digest() -> None:
    result = LifecycleResult(
        0,
        0,
        0,
        0,
        0,
        0,
        candidate_wheel_sha256="a" * 64,
        dependency_environment_digest="b" * 64,
    )
    assert result.dependency_environment_digest == "b" * 64


def test_lifecycle_environment_strips_signer_capabilities(tmp_path, monkeypatch) -> None:
    monkeypatch.setenv("PDD_ATTESTATION_SIGNER_COMMAND", "protected-attestation")
    monkeypatch.setenv("PDD_CERTIFICATE_ISSUER", "protected-issuer")
    monkeypatch.setenv("PDD_RELEASED_CHECKER_COMMAND", "protected-checker")
    environment = _isolated_lifecycle_environment(tmp_path)
    assert "PDD_ATTESTATION_SIGNER_COMMAND" not in environment
    assert "PDD_CERTIFICATE_ISSUER" not in environment
    assert "PDD_RELEASED_CHECKER_COMMAND" not in environment


def test_candidate_scenario_environment_strips_signer_capabilities(
    tmp_path, monkeypatch
) -> None:
    captured = {}

    def fake_run(*_args, **kwargs):
        captured.update(kwargs["env"])
        return subprocess.CompletedProcess(_args[0], 0, "", "")

    monkeypatch.setenv("PDD_ATTESTATION_SIGNER_COMMAND", "protected-attestation")
    monkeypatch.setenv("PDD_CERTIFICATE_ISSUER", "protected-issuer")
    monkeypatch.setenv("PDD_RELEASED_CHECKER_COMMAND", "protected-checker")
    monkeypatch.setattr(scenario_harness.subprocess, "run", fake_run)
    scenario_harness._candidate(
        argparse.Namespace(candidate_python=sys.executable),
        tmp_path,
        "--version",
    )
    assert "PDD_ATTESTATION_SIGNER_COMMAND" not in captured
    assert "PDD_CERTIFICATE_ISSUER" not in captured
    assert "PDD_RELEASED_CHECKER_COMMAND" not in captured


def test_merge_base_movement_blocks_stale_repair_and_converges(tmp_path) -> None:
    """A repair planned before merge movement must never overwrite merged bytes."""
    root = tmp_path / "merge-repo"
    root.mkdir()
    _git(root, "init", "-q")
    _git(root, "config", "user.email", "sync@example.com")
    _git(root, "config", "user.name", "Sync Test")
    initialize_repository_identity(root, "a1970bc0-ecde-4c13-b3dc-ee2fccf1d043")
    (root / "prompts").mkdir()
    (root / "src").mkdir()
    (root / "prompts/widget_python.prompt").write_text("REQ-1: widget\n")
    target = root / "src/widget.py"
    target.write_text("value = 1\n")
    (root / "architecture.json").write_text(
        '[{"filename":"widget_python.prompt","filepath":"src/widget.py"}]\n'
    )
    _git(root, "add", ".")
    _git(root, "commit", "-qm", "protected base")
    base = _git(root, "rev-parse", "HEAD")

    manager = TransactionManager(root)
    repair = (
        PlannedWrite(PurePosixPath("src/widget.py"), b"value = 2\n", "100644"),
    )
    manager.prepare("stale-repair", repair)
    target.write_text("merged = True\n")
    _git(root, "add", "src/widget.py")
    _git(root, "commit", "-qm", "merge group moved")
    head = _git(root, "rev-parse", "HEAD")
    assert head != base
    manifest = build_unit_manifest(root, base_ref=base, head_ref=head)
    assert manifest.base_ref == base
    assert manifest.head_ref == head
    with pytest.raises(TransactionConflict, match="destination changed"):
        manager.commit("stale-repair")
    assert target.read_text() == "merged = True\n"

    fresh = TransactionManager(root)
    fresh.prepare("fresh-repair", repair)
    fresh.commit("fresh-repair")
    before_second = _git(root, "status", "--porcelain", "--untracked-files=all")
    second = fresh.prepare("second-run", repair)
    assert second.no_op is True
    after_second = _git(root, "status", "--porcelain", "--untracked-files=all")
    _record_metric(
        "post_merge_tree_changes",
        int(before_second != after_second) + len(second.changed_paths),
    )


@pytest.fixture(scope="module")
def released_checker(tmp_path_factory) -> Path:
    """Build and install the exact wheel used by clean-environment scenarios."""
    tmp_path = tmp_path_factory.mktemp("released-checker")
    root = Path(__file__).resolve().parents[1]
    dist = tmp_path / "dist"
    build = _run(root, sys.executable, "-m", "build", "--wheel", "--outdir", str(dist))
    assert build.returncode == 0, build.stdout + build.stderr
    wheels = tuple(dist.glob("*.whl"))
    assert len(wheels) == 1
    wheel = wheels[0]
    environment = tmp_path / "venv"
    create = _run(
        root,
        sys.executable,
        "-m",
        "venv",
        "--system-site-packages",
        str(environment),
    )
    assert create.returncode == 0, create.stderr
    python = environment / ("Scripts/python.exe" if os.name == "nt" else "bin/python")
    install = _run(
        root, str(python), "-m", "pip", "install", "--no-deps", str(wheel)
    )
    assert install.returncode == 0, install.stdout + install.stderr
    return python


def test_built_wheel_runs_in_clean_virtual_environment(
    tmp_path, released_checker
) -> None:
    """The packaged checker and protected registry work outside the source tree."""
    probe = _run(
        tmp_path,
        str(released_checker),
        "-c",
        (
            "from pdd.sync_core import LanguageRegistry; "
            "r=LanguageRegistry.bundled(); "
            "assert r.resolve_alias('python').language_id == 'python'"
        ),
    )
    assert probe.returncode == 0, probe.stdout + probe.stderr
