"""Focused contracts for fixed-enum Vitest Stage A evidence verification."""

import hashlib
import json
import stat
import subprocess
import sys
from pathlib import Path

import pytest


_FAILURE_BASELINE_SHA = "b09b6bef2c8c4bee762965be463527cd0b050154"
_PROTECTED_BASE_SHA = "39776aa9bb027c638812a01b8dabbe03cab92f64"
_RUNNER_IMAGE = "ubuntu-24.04/20260714.240.1"
_RUNNER_PROVISIONER = "20260707.563"
_PYTHON_VERSION = "3.12.13"
_NODE_VERSION = "22.23.1"
_VITEST_PACKAGE_SHA256 = "63b0ce64263ea3acaed934e5fb5fbbb98d7fcd7673acd40e164dea2a648f2da5"
_VITEST_LOCK_SHA256 = "bfc69a55d08997f553a0901c2ec0b7830cb01d6c6cc81257d150dcc79d20783c"
_TEST_NODE = (
    "tests/test_sync_core_runner_vitest.py::"
    "test_real_vitest_runs_copied_entrypoint_without_candidate_result_access"
)


def _write(path: Path, payload: dict[str, object]) -> str:
    """Write canonical owner-only evidence and its exact digest sidecar."""
    encoded = (json.dumps(payload, sort_keys=True, separators=(",", ":")) + "\n").encode(
        "ascii"
    )
    path.write_bytes(encoded)
    path.chmod(0o600)
    digest = hashlib.sha256(encoded).hexdigest()
    sidecar = Path(str(path) + ".sha256")
    sidecar.write_text(digest + "\n", encoding="ascii")
    sidecar.chmod(0o600)
    return digest


def _fixture(
    tmp_path: Path, lane: str = "source",
) -> tuple[Path, Path, dict[str, object], list[str], Path | None]:
    """Build a complete exact source or installed-wheel Stage A envelope."""
    repository = Path(__file__).resolve().parents[1]
    verifier = repository / "scripts/verify_vitest_stage_a_evidence.py"
    termination = repository / "scripts/verify_vitest_termination_evidence.py"
    observation = repository / "scripts/verify_vitest_no_result_observation.py"
    native_addon = repository / "pdd/sync_core/native/vitest_fd_cloexec.c"
    package = repository / "scripts/verify_vitest_package_attestation.py"
    provenance = repository / "scripts/verify_vitest_package_provenance.sh"
    runner = repository / "pdd/sync_core/runner.py"
    head = subprocess.run(
        ["git", "rev-parse", "HEAD"], cwd=repository, check=True,
        capture_output=True, text=True,
    ).stdout.strip()
    digests = {
        "producer_sha256": hashlib.sha256(runner.read_bytes()).hexdigest(),
        "termination_verifier_sha256": hashlib.sha256(termination.read_bytes()).hexdigest(),
        "observation_verifier_sha256": hashlib.sha256(observation.read_bytes()).hexdigest(),
        "stage_a_verifier_sha256": hashlib.sha256(verifier.read_bytes()).hexdigest(),
        "native_addon_sha256": hashlib.sha256(native_addon.read_bytes()).hexdigest(),
        "package_verifier_sha256": hashlib.sha256(package.read_bytes()).hexdigest(),
        "package_provenance_sha256": hashlib.sha256(provenance.read_bytes()).hexdigest(),
    }
    evidence_directory = tmp_path / "evidence"
    evidence_directory.mkdir(mode=0o700)
    review_path = evidence_directory / "review.json"
    review_digest = _write(review_path, {
        "schema": "vitest-diagnostic-review-v1",
        "failure_baseline_sha": _FAILURE_BASELINE_SHA,
        "protected_base_sha": _PROTECTED_BASE_SHA,
        "diagnostic_head_sha": head,
        "producer_sha256": digests["producer_sha256"],
        "verifier_sha256": digests["termination_verifier_sha256"],
        "observation_verifier_sha256": digests["observation_verifier_sha256"],
        "stage_a_verifier_sha256": digests["stage_a_verifier_sha256"],
        "native_addon_sha256": digests["native_addon_sha256"],
        "package_verifier_sha256": digests["package_verifier_sha256"],
        "package_provenance_sha256": digests["package_provenance_sha256"],
        "verdict": "APPROVE",
        "behavioral_verdict": "NO_BEHAVIORAL_FIX",
    })
    payload: dict[str, object] = {
        "schema": "vitest-stage-a-native-seal-v1",
        "failure_baseline_sha": _FAILURE_BASELINE_SHA,
        "protected_base_sha": _PROTECTED_BASE_SHA,
        "trigger_head_sha": head,
        "checkout_head_sha": head,
        "reviewed_head_sha": head,
        "review_evidence_sha256": review_digest,
        **digests,
        "runner_image": _RUNNER_IMAGE,
        "runner_provisioner": _RUNNER_PROVISIONER,
        "python": _PYTHON_VERSION,
        "node": _NODE_VERSION,
        "vitest_package_sha256": _VITEST_PACKAGE_SHA256,
        "vitest_lock_sha256": _VITEST_LOCK_SHA256,
        "test_node": _TEST_NODE,
        "lane": lane,
        "runner_origin": "source-checkout" if lane == "source" else "installed-wheel",
        "supervisor_exit_code": 0,
        "result_frame_present": False,
        "process_role": "vitest-coordinator",
        "failure_stage": "reporter-authority-seal",
        "native_failure_reason": "PDD_VITEST_SEAL_DESCRIPTOR_TABLE_OPEN",
        "progress_frames": [
            "post-drop-probes", "candidate-exec", "coordinator-bootstrap",
            "reporter-module-start", "reporter-addon-load-start",
            "reporter-addon-load-succeeded", "reporter-authority-seal-start",
            "reporter-authority-seal-failed", "coordinator-exit",
        ],
        "cgroup_memory_oom_delta": 0,
        "cgroup_memory_oom_kill_delta": 0,
        "cgroup_pids_max_delta": 0,
        "cause_red_status": "pending",
    }
    attestation_path: Path | None = None
    if lane == "installed-wheel":
        attestation_path = evidence_directory / "wheel-attestation.json"
        wheel_sha256 = "b" * 64
        attestation_sha256 = _write(attestation_path, {
            "schema": "vitest-wheel-package-attestation-v1",
            "diagnostic_head_sha": head,
            "wheel_sha256": wheel_sha256,
            "producer_sha256": digests["producer_sha256"],
            "installed_runner_sha256": digests["producer_sha256"],
            "import_origin": "installed-wheel",
        })
        payload.update({
            "package_attestation_sha256": attestation_sha256,
            "wheel_sha256": wheel_sha256,
            "installed_runner_sha256": digests["producer_sha256"],
        })
    evidence = evidence_directory / "stage-a.json"
    evidence_digest = _write(evidence, payload)
    arguments = [
        sys.executable, str(verifier), "--evidence", str(evidence),
        "--evidence-sha256", evidence_digest, "--review-evidence", str(review_path),
        "--review-evidence-sha256", review_digest, "--repository", str(repository),
        "--failure-baseline-sha", _FAILURE_BASELINE_SHA,
        "--protected-base-sha", _PROTECTED_BASE_SHA, "--trigger-head-sha", head,
        "--checkout-head-sha", head, "--reviewed-head-sha", head,
        "--producer-sha256", digests["producer_sha256"],
        "--termination-verifier-sha256", digests["termination_verifier_sha256"],
        "--observation-verifier-sha256", digests["observation_verifier_sha256"],
        "--stage-a-verifier-sha256", digests["stage_a_verifier_sha256"],
        "--native-addon-sha256", digests["native_addon_sha256"],
        "--package-verifier-sha256", digests["package_verifier_sha256"],
        "--package-provenance-sha256", digests["package_provenance_sha256"],
        "--runner-image", _RUNNER_IMAGE, "--runner-provisioner", _RUNNER_PROVISIONER,
        "--python", _PYTHON_VERSION, "--node", _NODE_VERSION,
        "--vitest-package-sha256", _VITEST_PACKAGE_SHA256,
        "--vitest-lock-sha256", _VITEST_LOCK_SHA256, "--test-node", _TEST_NODE,
        "--lane", lane,
    ]
    if lane == "installed-wheel" and attestation_path is not None:
        arguments.extend((
            "--package-attestation", str(attestation_path),
            "--package-attestation-sha256", payload["package_attestation_sha256"],
            "--wheel-sha256", payload["wheel_sha256"],
            "--installed-runner-sha256", payload["installed_runner_sha256"],
        ))
    return evidence, review_path, payload, arguments, attestation_path


def _verify(arguments: list[str]) -> subprocess.CompletedProcess[str]:
    """Run the verifier without raising for intentional fail-closed cases."""
    return subprocess.run(arguments, capture_output=True, text=True, check=False)


def _rewrite(path: Path, payload: dict[str, object], arguments: list[str]) -> None:
    """Rewrite a canonical record and update only its declared digest argument."""
    arguments[arguments.index("--evidence-sha256") + 1] = _write(path, payload)


@pytest.mark.parametrize("lane", ("source", "installed-wheel"))
def test_stage_a_verifier_accepts_exact_native_enum_lanes(
    tmp_path: Path, lane: str,
) -> None:
    """Both lanes accept one exact native code with complete provenance."""
    _evidence, _review, payload, arguments, _attestation = _fixture(tmp_path, lane)

    completed = _verify(arguments)

    assert completed.returncode == 0, completed.stderr
    assert payload["native_failure_reason"] == "PDD_VITEST_SEAL_DESCRIPTOR_TABLE_OPEN"
    assert "cause-specific RED pending" in completed.stdout


@pytest.mark.parametrize(
    ("mutation", "lane"),
    (
        ("free-form-reason", "source"),
        ("broad-boundary", "source"),
        ("pre-seal-exit", "source"),
        ("wrong-toolchain", "source"),
        ("review-substitution", "source"),
        ("lane-substitution", "source"),
        ("wrong-mode", "source"),
        ("missing-sidecar", "source"),
        ("attestation-sidecar", "installed-wheel"),
        ("package-substitution", "installed-wheel"),
    ),
)
def test_stage_a_verifier_rejects_tampered_reason_trace_sidecar_and_lane(
    tmp_path: Path, mutation: str, lane: str,
) -> None:
    """Unknown reasons, malformed routes, bad sidecars, and lanes fail closed."""
    evidence, review, payload, arguments, attestation = _fixture(tmp_path, lane)
    if mutation == "free-form-reason":
        payload["native_failure_reason"] = "errno:EACCES"
        _rewrite(evidence, payload, arguments)
    elif mutation == "broad-boundary":
        payload["progress_frames"] = [
            "post-drop-probes", "candidate-exec", "coordinator-bootstrap",
            "reporter-authority-seal-failed", "coordinator-exit",
        ]
        _rewrite(evidence, payload, arguments)
    elif mutation == "pre-seal-exit":
        payload["progress_frames"] = [
            "post-drop-probes", "candidate-exec", "coordinator-bootstrap",
            "coordinator-explicit-exit", "reporter-module-start",
            "reporter-addon-load-start", "reporter-addon-load-succeeded",
            "reporter-authority-seal-start", "reporter-authority-seal-failed",
            "coordinator-exit",
        ]
        _rewrite(evidence, payload, arguments)
    elif mutation == "wrong-toolchain":
        payload["runner_image"] = "ubuntu-24.04/unknown"
        _rewrite(evidence, payload, arguments)
    elif mutation == "review-substitution":
        review_payload = json.loads(review.read_text(encoding="ascii"))
        review_payload["verdict"] = "REJECT"
        review_digest = _write(review, review_payload)
        arguments[arguments.index("--review-evidence-sha256") + 1] = review_digest
        payload["review_evidence_sha256"] = review_digest
        _rewrite(evidence, payload, arguments)
    elif mutation == "lane-substitution":
        payload["runner_origin"] = "installed-wheel"
        _rewrite(evidence, payload, arguments)
    elif mutation == "wrong-mode":
        evidence.chmod(0o644)
    elif mutation == "missing-sidecar":
        Path(str(evidence) + ".sha256").unlink()
    else:
        assert attestation is not None
        if mutation == "attestation-sidecar":
            Path(str(attestation) + ".sha256").unlink()
        else:
            payload["wheel_sha256"] = "c" * 64
            _rewrite(evidence, payload, arguments)

    rejected = _verify(arguments)

    assert rejected.returncode == 1
    assert rejected.stderr == "Vitest Stage A evidence rejected\n"
    assert stat.S_IMODE(evidence.stat().st_mode) in {0o600, 0o644}
