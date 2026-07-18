"""Focused contracts for fail-closed Vitest no-result observations."""

import hashlib
import json
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
    """Write a canonical mode-restricted evidence file and sidecar."""
    encoded = (json.dumps(payload, sort_keys=True, separators=(",", ":")) + "\n").encode("ascii")
    path.write_bytes(encoded)
    path.chmod(0o600)
    digest = hashlib.sha256(encoded).hexdigest()
    sidecar = Path(str(path) + ".sha256")
    sidecar.write_text(digest + "\n", encoding="ascii")
    sidecar.chmod(0o600)
    return digest


def _fixture(
    tmp_path: Path, lane: str = "source",
) -> tuple[Path, Path, dict[str, object], list[str]]:
    """Build exact source or installed-wheel evidence with protected inputs."""
    repository = Path(__file__).resolve().parents[1]
    verifier = repository / "scripts/verify_vitest_no_result_observation.py"
    termination = repository / "scripts/verify_vitest_termination_evidence.py"
    package = repository / "scripts/verify_vitest_package_attestation.py"
    provenance = repository / "scripts/verify_vitest_package_provenance.sh"
    head = subprocess.run(
        ["git", "rev-parse", "HEAD"], cwd=repository, check=True,
        capture_output=True, text=True,
    ).stdout.strip()
    runner = repository / "pdd/sync_core/runner.py"
    digests = {
        "producer_sha256": hashlib.sha256(runner.read_bytes()).hexdigest(),
        "termination_verifier_sha256": hashlib.sha256(termination.read_bytes()).hexdigest(),
        "observation_verifier_sha256": hashlib.sha256(verifier.read_bytes()).hexdigest(),
        "package_verifier_sha256": hashlib.sha256(package.read_bytes()).hexdigest(),
        "package_provenance_sha256": hashlib.sha256(provenance.read_bytes()).hexdigest(),
    }
    review_path = tmp_path / "review.json"
    review_digest = _write(review_path, {
        "schema": "vitest-diagnostic-review-v1",
        "failure_baseline_sha": _FAILURE_BASELINE_SHA,
        "protected_base_sha": _PROTECTED_BASE_SHA,
        "diagnostic_head_sha": head,
        "producer_sha256": digests["producer_sha256"],
        "verifier_sha256": digests["termination_verifier_sha256"],
        "observation_verifier_sha256": digests["observation_verifier_sha256"],
        "package_verifier_sha256": digests["package_verifier_sha256"],
        "package_provenance_sha256": digests["package_provenance_sha256"],
        "verdict": "APPROVE",
        "behavioral_verdict": "NO_BEHAVIORAL_FIX",
    })
    payload: dict[str, object] = {
        "schema": "vitest-no-result-observation-v1",
        "failure_baseline_sha": _FAILURE_BASELINE_SHA,
        "protected_base_sha": _PROTECTED_BASE_SHA,
        "trigger_head_sha": head,
        "checkout_head_sha": head,
        "reviewed_head_sha": head,
        "review_evidence_sha256": review_digest,
        "producer_sha256": digests["producer_sha256"],
        "termination_verifier_sha256": digests["termination_verifier_sha256"],
        "observation_verifier_sha256": digests["observation_verifier_sha256"],
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
        "progress_frames": [
            "post-drop-probes", "candidate-exec", "coordinator-bootstrap",
            "coordinator-before-exit", "coordinator-exit",
        ],
        "cause_eligible": False,
    }
    arguments = [
        sys.executable, str(verifier), "--evidence", str(tmp_path / "observation.json"),
        "--evidence-sha256", "", "--review-evidence", str(review_path),
        "--review-evidence-sha256", review_digest, "--repository", str(repository),
        "--failure-baseline-sha", _FAILURE_BASELINE_SHA,
        "--protected-base-sha", _PROTECTED_BASE_SHA, "--trigger-head-sha", head,
        "--checkout-head-sha", head, "--reviewed-head-sha", head,
        "--producer-sha256", digests["producer_sha256"],
        "--termination-verifier-sha256", digests["termination_verifier_sha256"],
        "--observation-verifier-sha256", digests["observation_verifier_sha256"],
        "--package-verifier-sha256", digests["package_verifier_sha256"],
        "--package-provenance-sha256", digests["package_provenance_sha256"],
        "--runner-image", _RUNNER_IMAGE, "--runner-provisioner", _RUNNER_PROVISIONER,
        "--python", _PYTHON_VERSION, "--node", _NODE_VERSION,
        "--vitest-package-sha256", _VITEST_PACKAGE_SHA256,
        "--vitest-lock-sha256", _VITEST_LOCK_SHA256, "--test-node", _TEST_NODE,
        "--lane", lane,
    ]
    if lane == "installed-wheel":
        payload.update({
            "package_attestation_sha256": "a" * 64,
            "wheel_sha256": "b" * 64,
            "installed_runner_sha256": digests["producer_sha256"],
        })
        arguments.extend((
            "--package-attestation-sha256", "a" * 64,
            "--wheel-sha256", "b" * 64,
            "--installed-runner-sha256", digests["producer_sha256"],
        ))
    evidence = Path(arguments[arguments.index("--evidence") + 1])
    arguments[arguments.index("--evidence-sha256") + 1] = _write(evidence, payload)
    return evidence, review_path, payload, arguments


def _verify(arguments: list[str]) -> subprocess.CompletedProcess[str]:
    """Run the standalone verifier without raising for expected rejections."""
    return subprocess.run(arguments, capture_output=True, text=True, check=False)


def _rewrite(evidence: Path, payload: dict[str, object], arguments: list[str]) -> None:
    arguments[arguments.index("--evidence-sha256") + 1] = _write(evidence, payload)


@pytest.mark.parametrize("lane", ("source", "installed-wheel"))
def test_observation_verifier_accepts_canonical_lane(tmp_path: Path, lane: str) -> None:
    """Both lane schemas verify only with their exact protected identities."""
    _evidence, _review, payload, arguments = _fixture(tmp_path, lane)

    completed = _verify(arguments)

    assert completed.returncode == 0, completed.stderr
    assert payload["cause_eligible"] is False
    assert "cause_eligible: false" in completed.stdout


@pytest.mark.parametrize(
    ("lane", "field", "value"),
    (
        ("source", "wheel_sha256", "b" * 64),
        ("source", "runner_origin", "installed-wheel"),
        ("installed-wheel", "package_attestation_sha256", "c" * 64),
        ("installed-wheel", "wheel_sha256", "c" * 64),
        ("installed-wheel", "installed_runner_sha256", "c" * 64),
    ),
)
def test_observation_verifier_rejects_lane_identity_substitution(
    tmp_path: Path, lane: str, field: str, value: object,
) -> None:
    """Source forbids wheel fields and wheel bindings remain exact."""
    evidence, _review, payload, arguments = _fixture(tmp_path, lane)
    payload[field] = value
    _rewrite(evidence, payload, arguments)

    completed = _verify(arguments)

    assert completed.returncode == 1
    assert completed.stderr == "Vitest no-result observation rejected\n"


@pytest.mark.parametrize(
    ("field", "value"),
    (
        ("cause_eligible", True),
        ("result_frame_present", True),
        ("supervisor_exit_code", 1),
        ("progress_frames", ["coordinator-exit", "candidate-exec"]),
        ("progress_frames", ["post-drop-probes"] * 257),
    ),
)
def test_observation_verifier_rejects_non_observation_or_unbounded_progress(
    tmp_path: Path, field: str, value: object,
) -> None:
    """No generic lifecycle symptom can be relabeled as a cause artifact."""
    evidence, _review, payload, arguments = _fixture(tmp_path)
    payload[field] = value
    _rewrite(evidence, payload, arguments)

    assert _verify(arguments).returncode == 1


@pytest.mark.parametrize(
    "progress_frames",
    (
        ["post-drop-probes", "candidate-exec", "coordinator-bootstrap", "result-published"],
        ["post-drop-probes", "candidate-exec", "coordinator-bootstrap", "reporter-authority-seal-start"],
        ["post-drop-probes", "candidate-exec", "coordinator-bootstrap", "reporter-module-start", "reporter-addon-load-start", "reporter-addon-load-succeeded", "reporter-addon-load-failed"],
        ["post-drop-probes", "candidate-exec", "coordinator-bootstrap", "coordinator-exit", "coordinator-before-exit"],
        ["post-drop-probes", "candidate-exec", "coordinator-bootstrap", "worker-start", "worker-start"],
    ),
)
def test_observation_verifier_rejects_impossible_producer_progress(
    tmp_path: Path, progress_frames: list[str],
) -> None:
    """The verifier independently rejects every impossible producer transition."""
    evidence, _review, payload, arguments = _fixture(tmp_path)
    payload["progress_frames"] = progress_frames
    _rewrite(evidence, payload, arguments)

    rejected = _verify(arguments)

    assert rejected.returncode == 1
    assert rejected.stderr == "Vitest no-result observation rejected\n"


@pytest.mark.parametrize("mutation", ("digest", "review", "toolchain"))
def test_observation_verifier_rejects_digest_review_and_toolchain_tampering(
    tmp_path: Path, mutation: str,
) -> None:
    """The verifier independently rejects every protected identity class."""
    evidence, review, _payload, arguments = _fixture(tmp_path)
    if mutation == "digest":
        arguments[arguments.index("--evidence-sha256") + 1] = "0" * 64
    elif mutation == "review":
        review_payload = json.loads(review.read_text(encoding="ascii"))
        review_payload["observation_verifier_sha256"] = "d" * 64
        arguments[arguments.index("--review-evidence-sha256") + 1] = _write(
            review, review_payload,
        )
    else:
        arguments[arguments.index("--node") + 1] = "0.0.0"
    assert _verify(arguments).returncode == 1
    assert evidence.exists()


@pytest.mark.parametrize("lane", ("source", "installed-wheel"))
def test_termination_verifier_rejects_each_observation_stably(
    tmp_path: Path, lane: str,
) -> None:
    """Stage A termination verification must never accept an A0 observation."""
    evidence, review, _payload, arguments = _fixture(tmp_path, lane)
    termination = (
        Path(__file__).resolve().parents[1]
        / "scripts/verify_vitest_termination_evidence.py"
    )

    def argument(name: str) -> str:
        return arguments[arguments.index(name) + 1]

    rejected = subprocess.run([
        sys.executable, str(termination), "--evidence", str(evidence),
        "--evidence-sha256", argument("--evidence-sha256"),
        "--review-evidence", str(review),
        "--review-evidence-sha256", argument("--review-evidence-sha256"),
        "--repository", argument("--repository"),
        "--failure-baseline-sha", _FAILURE_BASELINE_SHA,
        "--protected-base-sha", _PROTECTED_BASE_SHA,
        "--diagnostic-head-sha", argument("--reviewed-head-sha"),
        "--producer-sha256", argument("--producer-sha256"),
        "--verifier-sha256", argument("--termination-verifier-sha256"),
        "--observation-verifier-sha256", argument("--observation-verifier-sha256"),
        "--package-verifier-sha256", argument("--package-verifier-sha256"),
        "--package-provenance-sha256", argument("--package-provenance-sha256"),
        "--runner-image", _RUNNER_IMAGE, "--runner-provisioner", _RUNNER_PROVISIONER,
        "--python", _PYTHON_VERSION, "--node", _NODE_VERSION,
        "--vitest-package-sha256", _VITEST_PACKAGE_SHA256,
        "--vitest-lock-sha256", _VITEST_LOCK_SHA256, "--test-node", _TEST_NODE,
    ], capture_output=True, text=True, check=False)

    assert rejected.returncode == 1
    assert rejected.stderr == "Vitest termination evidence rejected\n"
