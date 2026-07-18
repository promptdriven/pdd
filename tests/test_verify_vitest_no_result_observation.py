"""Focused contracts for fail-closed Vitest no-result observations."""

import hashlib
import json
import subprocess
import sys
from pathlib import Path

import pytest


_FAILURE_BASELINE_SHA = "b09b6bef2c8c4bee762965be463527cd0b050154"
_PROTECTED_BASE_SHA = "0e22fe9f42f72a70fc85cb6f9c289fd8187df451"
_RUNNER_IMAGE = "ubuntu-24.04/20260714.240.1"
_RUNNER_PROVISIONER = "20260707.563"
_PYTHON_VERSION = "3.12.13"
_NODE_VERSION = "22.23.1"
_VITEST_PACKAGE_SHA256 = (
    "63b0ce64263ea3acaed934e5fb5fbbb98d7fcd7673acd40e164dea2a648f2da5"
)
_VITEST_LOCK_SHA256 = (
    "bfc69a55d08997f553a0901c2ec0b7830cb01d6c6cc81257d150dcc79d20783c"
)
_TEST_NODE = (
    "tests/test_sync_core_runner_vitest.py::"
    "test_real_vitest_runs_copied_entrypoint_without_candidate_result_access"
)


def _canonical(payload: dict[str, object]) -> bytes:
    return (json.dumps(payload, sort_keys=True, separators=(",", ":")) + "\n").encode("ascii")


def _write(path: Path, payload: dict[str, object]) -> str:
    encoded = _canonical(payload)
    path.write_bytes(encoded)
    path.chmod(0o600)
    (path.parent / f"{path.name}.sha256").write_text(
        hashlib.sha256(encoded).hexdigest() + "\n", encoding="ascii"
    )
    (path.parent / f"{path.name}.sha256").chmod(0o600)
    return hashlib.sha256(encoded).hexdigest()


def _fixture(
    tmp_path: Path, lane: str = "source",
) -> tuple[Path, dict[str, object], list[str]]:
    repository = Path(__file__).resolve().parents[1]
    observation_verifier = repository / "scripts/verify_vitest_no_result_observation.py"
    termination_verifier = repository / "scripts/verify_vitest_termination_evidence.py"
    producer = repository / "pdd/sync_core/runner.py"
    package_verifier = repository / "scripts/verify_vitest_package_attestation.py"
    package_provenance = repository / "scripts/verify_vitest_package_provenance.sh"
    head = subprocess.run(
        ["git", "rev-parse", "HEAD"], cwd=repository,
        capture_output=True, text=True, check=True,
    ).stdout.strip()
    digests = {
        "producer_sha256": hashlib.sha256(producer.read_bytes()).hexdigest(),
        "termination_verifier_sha256": hashlib.sha256(
            termination_verifier.read_bytes()
        ).hexdigest(),
        "observation_verifier_sha256": hashlib.sha256(
            observation_verifier.read_bytes()
        ).hexdigest(),
        "package_verifier_sha256": hashlib.sha256(package_verifier.read_bytes()).hexdigest(),
        "package_provenance_sha256": hashlib.sha256(package_provenance.read_bytes()).hexdigest(),
    }
    review = {
        "schema": "vitest-diagnostic-review-v1",
        "failure_baseline_sha": _FAILURE_BASELINE_SHA,
        "protected_base_sha": _PROTECTED_BASE_SHA,
        "diagnostic_head_sha": head,
        **digests,
        "verdict": "APPROVE",
        "behavioral_verdict": "NO_BEHAVIORAL_FIX",
    }
    review_path = tmp_path / "vitest-diagnostic-review-v1.json"
    review_digest = _write(review_path, review)
    payload: dict[str, object] = {
        "schema": "vitest-no-result-observation-v1",
        "failure_baseline_sha": _FAILURE_BASELINE_SHA,
        "protected_base_sha": _PROTECTED_BASE_SHA,
        "trigger_head_sha": head,
        "checkout_head_sha": head,
        "reviewed_head_sha": head,
        "review_evidence_sha256": review_digest,
        **{key: digests[key] for key in (
            "producer_sha256", "termination_verifier_sha256", "observation_verifier_sha256",
        )},
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
        sys.executable, str(observation_verifier),
        "--evidence", str(tmp_path / "observation.json"),
        "--evidence-sha256", "",
        "--review-evidence", str(review_path),
        "--review-evidence-sha256", review_digest,
        "--repository", str(repository),
        "--failure-baseline-sha", _FAILURE_BASELINE_SHA,
        "--protected-base-sha", _PROTECTED_BASE_SHA,
        "--trigger-head-sha", head,
        "--checkout-head-sha", head,
        "--reviewed-head-sha", head,
        "--producer-sha256", digests["producer_sha256"],
        "--termination-verifier-sha256", digests["termination_verifier_sha256"],
        "--observation-verifier-sha256", digests["observation_verifier_sha256"],
        "--package-verifier-sha256", digests["package_verifier_sha256"],
        "--package-provenance-sha256", digests["package_provenance_sha256"],
        "--runner-image", _RUNNER_IMAGE,
        "--runner-provisioner", _RUNNER_PROVISIONER,
        "--python", _PYTHON_VERSION,
        "--node", _NODE_VERSION,
        "--vitest-package-sha256", _VITEST_PACKAGE_SHA256,
        "--vitest-lock-sha256", _VITEST_LOCK_SHA256,
        "--test-node", _TEST_NODE,
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
    evidence_path = Path(arguments[arguments.index("--evidence") + 1])
    arguments[arguments.index("--evidence-sha256") + 1] = _write(evidence_path, payload)
    return evidence_path, payload, arguments


@pytest.mark.parametrize("lane", ("source", "installed-wheel"))
def test_observation_verifier_accepts_exact_cause_ineligible_lane(
    tmp_path: Path, lane: str,
) -> None:
    _evidence, _payload, arguments = _fixture(tmp_path, lane)

    completed = subprocess.run(arguments, capture_output=True, text=True, check=False)

    assert completed.returncode == 0, completed.stderr
    assert "cause_eligible: false" in completed.stdout


def test_observation_verifier_rejects_source_wheel_binding(tmp_path: Path) -> None:
    evidence, payload, arguments = _fixture(tmp_path)
    payload["wheel_sha256"] = "b" * 64
    arguments[arguments.index("--evidence-sha256") + 1] = _write(evidence, payload)

    completed = subprocess.run(arguments, capture_output=True, text=True, check=False)

    assert completed.returncode == 1
    assert completed.stderr == "Vitest no-result observation rejected\n"


@pytest.mark.parametrize("lane", ("source", "installed-wheel"))
def test_termination_verifier_rejects_each_observation_stably(
    tmp_path: Path, lane: str,
) -> None:
    evidence, _payload, arguments = _fixture(tmp_path, lane)
    termination = Path(__file__).resolve().parents[1] / "scripts/verify_vitest_termination_evidence.py"
    rejected = subprocess.run(
        [
            sys.executable, str(termination),
            "--evidence", str(evidence),
            "--evidence-sha256", arguments[arguments.index("--evidence-sha256") + 1],
            "--review-evidence", arguments[arguments.index("--review-evidence") + 1],
            "--review-evidence-sha256", arguments[arguments.index("--review-evidence-sha256") + 1],
            "--repository", arguments[arguments.index("--repository") + 1],
            "--failure-baseline-sha", _FAILURE_BASELINE_SHA,
            "--protected-base-sha", _PROTECTED_BASE_SHA,
            "--diagnostic-head-sha", arguments[arguments.index("--reviewed-head-sha") + 1],
            "--producer-sha256", arguments[arguments.index("--producer-sha256") + 1],
            "--verifier-sha256", arguments[arguments.index("--termination-verifier-sha256") + 1],
            "--package-verifier-sha256", arguments[arguments.index("--package-verifier-sha256") + 1],
            "--package-provenance-sha256", arguments[arguments.index("--package-provenance-sha256") + 1],
            "--runner-image", _RUNNER_IMAGE,
            "--runner-provisioner", _RUNNER_PROVISIONER,
            "--python", _PYTHON_VERSION,
            "--node", _NODE_VERSION,
            "--vitest-package-sha256", _VITEST_PACKAGE_SHA256,
            "--vitest-lock-sha256", _VITEST_LOCK_SHA256,
            "--test-node", _TEST_NODE,
        ],
        capture_output=True, text=True, check=False,
    )
    assert rejected.returncode == 1
    assert rejected.stderr == "Vitest termination evidence rejected\n"


@pytest.mark.parametrize(
    "field,value",
    (
        ("cause_eligible", True),
        ("result_frame_present", True),
        ("supervisor_exit_code", 1),
        ("progress_frames", ["coordinator-exit", "candidate-exec"]),
    ),
)
def test_observation_verifier_rejects_non_observation_claims(
    tmp_path: Path, field: str, value: object,
) -> None:
    evidence, payload, arguments = _fixture(tmp_path)
    payload[field] = value
    arguments[arguments.index("--evidence-sha256") + 1] = _write(evidence, payload)

    completed = subprocess.run(arguments, capture_output=True, text=True, check=False)

    assert completed.returncode == 1
    assert completed.stderr == "Vitest no-result observation rejected\n"
