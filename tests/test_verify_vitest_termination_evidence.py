"""Focused contract tests for the strict Vitest termination verifier."""

# pylint: disable=duplicate-code

import hashlib
import json
import subprocess
import sys
from pathlib import Path

import pytest


_FAILURE_BASELINE_SHA = "b09b6bef2c8c4bee762965be463527cd0b050154"
_PROTECTED_BASE_SHA = "cc97ef23a478fa123a7b9ffc5d7450b4d55b70e7"
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
_CAUSE_RED_TEST_NODE = _TEST_NODE


def _repository_head(repository: Path) -> str:
    """Read the exact test checkout head without accepting ambient values."""
    return subprocess.run(
        ["git", "rev-parse", "HEAD"], cwd=repository,
        capture_output=True, text=True, check=True,
    ).stdout.strip()


def _canonical(payload: dict[str, object]) -> bytes:
    """Encode one evidence record in the required canonical form."""
    return (
        json.dumps(payload, sort_keys=True, separators=(",", ":")) + "\n"
    ).encode("ascii")


def _fixture(tmp_path: Path) -> tuple[Path, dict[str, object], list[str]]:
    """Create exact evidence and independent protected command-line pins."""
    repository = Path(__file__).resolve().parents[1]
    verifier = repository / "scripts" / "verify_vitest_termination_evidence.py"
    assert verifier.is_file()
    producer = repository / "pdd" / "sync_core" / "runner.py"
    head = _repository_head(repository)
    payload: dict[str, object] = {
        "schema": "vitest-termination-v1",
        "failure_baseline_sha": _FAILURE_BASELINE_SHA,
        "protected_base_sha": _PROTECTED_BASE_SHA,
        "diagnostic_head_sha": head,
        "producer_sha256": hashlib.sha256(producer.read_bytes()).hexdigest(),
        "verifier_sha256": hashlib.sha256(verifier.read_bytes()).hexdigest(),
        "runner_image": _RUNNER_IMAGE,
        "runner_provisioner": _RUNNER_PROVISIONER,
        "python": _PYTHON_VERSION,
        "node": _NODE_VERSION,
        "vitest_package_sha256": _VITEST_PACKAGE_SHA256,
        "vitest_lock_sha256": _VITEST_LOCK_SHA256,
        "test_node": _TEST_NODE,
        "process_role": "vitest-coordinator",
        "failure_stage": "coordinator-termination",
        "cause_code": "coordinator-explicit-exit",
        "exit_code": 1,
        "cgroup_memory_oom_delta": 0,
        "cgroup_memory_oom_kill_delta": 0,
        "cgroup_pids_max_delta": 0,
        "diagnostic_sha256": "d" * 64,
        "red_test": {
            "node_id": _CAUSE_RED_TEST_NODE,
            "outcome": "fail",
            "failure_baseline_sha": _FAILURE_BASELINE_SHA,
            "diagnostic_head_sha": head,
        },
    }
    evidence = tmp_path / "vitest-termination-v1.json"
    encoded = _canonical(payload)
    evidence.write_bytes(encoded)
    evidence.chmod(0o600)
    arguments = [
        sys.executable,
        str(verifier),
        "--evidence", str(evidence),
        "--evidence-sha256", hashlib.sha256(encoded).hexdigest(),
        "--repository", str(repository),
        "--failure-baseline-sha", _FAILURE_BASELINE_SHA,
        "--protected-base-sha", _PROTECTED_BASE_SHA,
        "--diagnostic-head-sha", head,
        "--producer-sha256", str(payload["producer_sha256"]),
        "--verifier-sha256", str(payload["verifier_sha256"]),
        "--runner-image", _RUNNER_IMAGE,
        "--runner-provisioner", _RUNNER_PROVISIONER,
        "--python", _PYTHON_VERSION,
        "--node", _NODE_VERSION,
        "--vitest-package-sha256", _VITEST_PACKAGE_SHA256,
        "--vitest-lock-sha256", _VITEST_LOCK_SHA256,
        "--test-node", _TEST_NODE,
        "--cause-red-test-node", _CAUSE_RED_TEST_NODE,
        "--cause-red-outcome", "fail",
    ]
    return evidence, payload, arguments


def _rewrite(
    evidence: Path, payload: dict[str, object], arguments: list[str],
) -> None:
    """Apply one canonical artifact mutation while retaining strict file mode."""
    encoded = _canonical(payload)
    evidence.write_bytes(encoded)
    evidence.chmod(0o600)
    arguments[arguments.index("--evidence-sha256") + 1] = hashlib.sha256(
        encoded
    ).hexdigest()


def _verify(arguments: list[str]) -> subprocess.CompletedProcess[str]:
    """Run the standalone verifier without raising on expected rejection."""
    return subprocess.run(arguments, capture_output=True, text=True, check=False)


def test_verifier_accepts_exact_canonical_evidence(tmp_path: Path) -> None:
    """One independently pinned, canonical v1 artifact is accepted."""
    _evidence, _payload, arguments = _fixture(tmp_path)

    completed = _verify(arguments)

    assert completed.returncode == 0, completed.stderr


@pytest.mark.parametrize("field", ("process_role", "failure_stage", "cause_code"))
def test_verifier_rejects_unknown_classification(
    tmp_path: Path, field: str,
) -> None:
    """UNKNOWN cannot stand in for a concrete protected failure."""
    evidence, payload, arguments = _fixture(tmp_path)
    payload[field] = "UNKNOWN"
    _rewrite(evidence, payload, arguments)

    assert _verify(arguments).returncode != 0


@pytest.mark.parametrize(
    "mutation",
    (
        "unknown-field",
        "missing-field",
        "boolean-exit",
        "negative-cgroup",
        "noncanonical",
        "wrong-mode",
        "red-mismatch",
        "invalid-cause-combination",
    ),
)
def test_verifier_rejects_malformed_or_unrelated_evidence(
    tmp_path: Path, mutation: str,
) -> None:
    """The schema, nested RED metadata, and cause mapping all fail closed."""
    evidence, payload, arguments = _fixture(tmp_path)
    if mutation == "unknown-field":
        payload["candidate_detail"] = "candidate-controlled-secret"
        _rewrite(evidence, payload, arguments)
    elif mutation == "missing-field":
        del payload["diagnostic_sha256"]
        _rewrite(evidence, payload, arguments)
    elif mutation == "boolean-exit":
        payload["exit_code"] = True
        _rewrite(evidence, payload, arguments)
    elif mutation == "negative-cgroup":
        payload["cgroup_pids_max_delta"] = -1
        _rewrite(evidence, payload, arguments)
    elif mutation == "noncanonical":
        evidence.write_text(json.dumps(payload), encoding="ascii")
        evidence.chmod(0o600)
        arguments[arguments.index("--evidence-sha256") + 1] = hashlib.sha256(
            evidence.read_bytes()
        ).hexdigest()
    elif mutation == "wrong-mode":
        evidence.chmod(0o644)
    elif mutation == "red-mismatch":
        red_test = payload["red_test"]
        assert isinstance(red_test, dict)
        red_test["diagnostic_head_sha"] = _FAILURE_BASELINE_SHA
        _rewrite(evidence, payload, arguments)
    else:
        payload["cause_code"] = "reporter-addon-load-failed"
        _rewrite(evidence, payload, arguments)

    completed = _verify(arguments)

    assert completed.returncode != 0
    assert "candidate-controlled-secret" not in completed.stderr


@pytest.mark.parametrize(
    ("option", "replacement"),
    (
        ("--failure-baseline-sha", "0" * 40),
        ("--protected-base-sha", "1" * 40),
        ("--diagnostic-head-sha", "2" * 40),
        ("--producer-sha256", "3" * 64),
        ("--verifier-sha256", "4" * 64),
        ("--runner-image", "untrusted-image"),
        ("--runner-provisioner", "untrusted-provisioner"),
        ("--python", "0.0.0"),
        ("--node", "0.0.0"),
        ("--vitest-package-sha256", "5" * 64),
        ("--vitest-lock-sha256", "6" * 64),
        ("--test-node", "candidate::node"),
        ("--cause-red-test-node", "candidate::red"),
        ("--cause-red-outcome", "pass"),
    ),
)
def test_verifier_rejects_every_protected_pin_mismatch(
    tmp_path: Path, option: str, replacement: str,
) -> None:
    """Every workflow-provided identity must equal the artifact exactly."""
    _evidence, _payload, arguments = _fixture(tmp_path)
    arguments[arguments.index(option) + 1] = replacement

    assert _verify(arguments).returncode != 0


def test_verifier_rejects_uploaded_artifact_digest_mismatch(tmp_path: Path) -> None:
    """The upload digest is independently checked rather than trusted in-band."""
    _evidence, _payload, arguments = _fixture(tmp_path)
    arguments[arguments.index("--evidence-sha256") + 1] = "f" * 64

    assert _verify(arguments).returncode != 0


@pytest.mark.parametrize(
    ("field", "option", "replacement"),
    (
        ("failure_baseline_sha", "--failure-baseline-sha", "0" * 40),
        ("protected_base_sha", "--protected-base-sha", "1" * 40),
        ("runner_image", "--runner-image", "untrusted-image"),
        ("runner_provisioner", "--runner-provisioner", "untrusted-provisioner"),
        ("python", "--python", "0.0.0"),
        ("node", "--node", "0.0.0"),
        ("vitest_package_sha256", "--vitest-package-sha256", "2" * 64),
        ("vitest_lock_sha256", "--vitest-lock-sha256", "3" * 64),
        ("test_node", "--test-node", "tests/untrusted.py::node"),
    ),
)
def test_verifier_rejects_substituted_static_pin_when_inputs_agree(
    tmp_path: Path, field: str, option: str, replacement: str,
) -> None:
    """Workflow arguments cannot replace an evidence protocol's fixed pins."""
    evidence, payload, arguments = _fixture(tmp_path)
    payload[field] = replacement
    _rewrite(evidence, payload, arguments)
    arguments[arguments.index(option) + 1] = replacement

    assert _verify(arguments).returncode != 0
