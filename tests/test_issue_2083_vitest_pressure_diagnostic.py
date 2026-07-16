"""Contracts for the immutable issue-2083 hosted diagnostic payload."""

from __future__ import annotations

import hashlib
import importlib.util
import json
from pathlib import Path

import pytest


ROOT = Path(__file__).resolve().parents[1]
RUNNER = ROOT / "scripts/ci/run_issue_2083_vitest_pressure.py"
PLUGIN = ROOT / "scripts/ci/issue_2083_vitest_barrier.py"
SUBJECT = "bd4a250420c3b7aaa50bab6fd73aded271115c71"
SOURCE_PATHS = {
    RUNNER.relative_to(ROOT).as_posix(),
    PLUGIN.relative_to(ROOT).as_posix(),
    Path(__file__).relative_to(ROOT).as_posix(),
}
SHA256_A = "a" * 64
SHA256_B = "b" * 64


def _runner_module():
    spec = importlib.util.spec_from_file_location("issue_2083_runner", RUNNER)
    assert spec is not None and spec.loader is not None
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    return module


def _identity() -> dict[str, object]:
    return {
        "schema": "pdd-vitest-toolchain-attestation-v1",
        "versions": {
            "node": "v22.17.0",
            "npm": "10.9.2",
            "vitest": "4.1.10",
        },
        "package": {
            "package_json_sha256": SHA256_A,
            "package_lock_sha256": SHA256_B,
            "vitest_package_sha256": SHA256_A,
        },
        "runtime_manifest_sha256": SHA256_B,
        "launcher": {"name": "node", "sha256": SHA256_A},
        "entrypoint": {"name": "vitest.mjs", "sha256": SHA256_B},
        "native_closure": [
            {"name": "ld-linux-x86-64.so.2", "sha256": SHA256_A},
            {"name": "libc.so.6", "sha256": SHA256_B},
        ],
    }


def _write_canonical(path: Path, payload: object) -> None:
    path.write_text(
        json.dumps(payload, separators=(",", ":"), sort_keys=True),
        encoding="utf-8",
    )


def test_source_is_minimal_and_has_no_workflow() -> None:
    """Only the immutable runner, barrier, and their contract may change."""
    changed = {
        value
        for value in (
            path.relative_to(ROOT).as_posix()
            for path in ROOT.rglob("*")
            if path.is_file()
        )
        if value in SOURCE_PATHS or value.endswith("2083-vitest-pressure-diagnostic.yml")
    }

    assert changed == SOURCE_PATHS
    assert not (ROOT / ".github/workflows/2083-vitest-pressure-diagnostic.yml").exists()


def test_runner_has_exact_bounded_matrix_and_redaction() -> None:
    """The payload must exercise only the planned bounded test matrix."""
    source = RUNNER.read_text(encoding="utf-8")

    assert SUBJECT in source
    assert "tests/test_sync_core_runner_vitest.py::" in source
    assert (
        "test_real_vitest_runs_copied_entrypoint_without_candidate_result_access"
        in source
    )
    assert "SERIAL_REPETITIONS = 3" in source
    assert "CONCURRENT_WIDTHS = (2, 4)" in source
    assert "CONCURRENT_WAVES = 3" in source
    assert "INVOCATION_TIMEOUT_SECONDS = 75" in source
    assert "candidate_stdout" not in source
    assert "candidate_stderr" not in source
    assert "MemAvailable" in source
    assert "memory.current" in source
    assert "pids.current" in source
    assert "thread_count" in source
    assert "diagnostic_sha256" in source


def test_toolchain_identity_is_required_canonical_and_redacted(tmp_path: Path) -> None:
    """Identity must be canonical, complete, versioned, and path-free."""
    runner = _runner_module()
    missing = tmp_path / "missing.json"
    with pytest.raises(ValueError, match="unavailable"):
        runner.load_toolchain_identity(missing)

    identity = _identity()
    manifest = tmp_path / "identity.json"
    _write_canonical(manifest, identity)
    loaded, digest = runner.load_toolchain_identity(manifest)

    assert loaded == identity
    assert digest == hashlib.sha256(manifest.read_bytes()).hexdigest()
    assert "/" not in json.dumps(loaded)
    assert "\\" not in json.dumps(loaded)

    manifest.write_text(json.dumps(identity, indent=2), encoding="utf-8")
    with pytest.raises(ValueError, match="canonical"):
        runner.load_toolchain_identity(manifest)


@pytest.mark.parametrize(
    ("mutation", "message"),
    [
        (lambda value: value["versions"].update(vitest="4.1.9"), "Vitest"),
        (lambda value: value["versions"].update(node="22"), "node"),
        (lambda value: value["package"].update(package_lock_sha256="bad"), "digest"),
        (lambda value: value.update(runtime_manifest_sha256="bad"), "runtime"),
        (lambda value: value["launcher"].update(name="/usr/bin/node"), "name"),
        (lambda value: value.update(native_closure=[]), "closure"),
    ],
)
def test_toolchain_identity_rejects_malformed_fields(
    tmp_path: Path, mutation, message: str,
) -> None:
    """Malformed or insufficient toolchain identity must fail closed."""
    runner = _runner_module()
    identity = _identity()
    mutation(identity)
    manifest = tmp_path / "identity.json"
    _write_canonical(manifest, identity)

    with pytest.raises(ValueError, match=message):
        runner.load_toolchain_identity(manifest)


def test_changed_toolchain_identity_changes_attestation_digest(tmp_path: Path) -> None:
    """Any accepted toolchain identity change must alter its sealed digest."""
    runner = _runner_module()
    first = tmp_path / "first.json"
    second = tmp_path / "second.json"
    identity = _identity()
    _write_canonical(first, identity)
    identity["versions"]["npm"] = "10.9.3"
    _write_canonical(second, identity)

    _, first_digest = runner.load_toolchain_identity(first)
    _, second_digest = runner.load_toolchain_identity(second)

    assert first_digest != second_digest


def test_runtime_manifest_must_match_attested_digest(tmp_path: Path) -> None:
    """The path-bearing runtime manifest must match its redacted attestation."""
    runner = _runner_module()
    runtime_manifest = tmp_path / "runtime.json"
    runtime_manifest.write_text("trusted runtime roles", encoding="utf-8")
    identity = _identity()
    identity["runtime_manifest_sha256"] = hashlib.sha256(
        runtime_manifest.read_bytes()
    ).hexdigest()

    runner.verify_runtime_manifest(identity, runtime_manifest)
    runtime_manifest.write_text("changed runtime roles", encoding="utf-8")
    with pytest.raises(ValueError, match="changed"):
        runner.verify_runtime_manifest(identity, runtime_manifest)
    with pytest.raises(ValueError, match="unavailable"):
        runner.verify_runtime_manifest(identity, tmp_path / "missing.json")


def test_seal_hashes_identity_and_detects_mutation(tmp_path: Path) -> None:
    """The evidence manifest must hash the standalone identity attestation."""
    runner = _runner_module()
    incomplete = tmp_path / "incomplete"
    incomplete.mkdir()
    with pytest.raises(ValueError, match="identity evidence"):
        runner.seal(incomplete, tmp_path / "rejected", "source", "run", "1")

    live = tmp_path / "live"
    sealed = tmp_path / "sealed"
    live.mkdir()
    _write_canonical(live / "toolchain-identity.json", _identity())
    _write_canonical(live / "results.json", {"schema": "results-v1"})

    runner.seal(live, sealed, "source-sha", "run-id", "1")
    runner.verify_seal(sealed)
    manifest = json.loads((sealed / "manifest.json").read_text(encoding="utf-8"))

    assert "toolchain-identity.json" in manifest["files"]
    assert manifest["files"]["toolchain-identity.json"]["sha256"] == hashlib.sha256(
        (sealed / "toolchain-identity.json").read_bytes()
    ).hexdigest()
    (sealed / "toolchain-identity.json").chmod(0o644)
    (sealed / "toolchain-identity.json").write_text("{}", encoding="utf-8")
    with pytest.raises(ValueError, match="SHA256"):
        runner.verify_seal(sealed)


def test_barrier_is_bounded_and_scoped_to_exact_vitest_call() -> None:
    """The concurrency barrier must be bounded and adapter-specific."""
    source = PLUGIN.read_text(encoding="utf-8")

    assert "PDD_2083_BARRIER_DIRECTORY" in source
    assert "PDD_2083_BARRIER_PARTIES" in source
    assert "PDD_2083_BARRIER_TOKEN" in source
    assert "time.monotonic()" in source
    assert "30.0" in source
    assert "_run_vitest" in source
    assert "os.environ" in source
