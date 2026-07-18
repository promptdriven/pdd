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


def _canonical(payload: dict[str, object]) -> bytes:
    """Encode one evidence record in the required canonical form."""
    return (
        json.dumps(payload, sort_keys=True, separators=(",", ":")) + "\n"
    ).encode("ascii")


def _write_canonical(path: Path, payload: dict[str, object]) -> str:
    """Write one protected canonical record and return its digest."""
    encoded = _canonical(payload)
    path.write_bytes(encoded)
    path.chmod(0o600)
    return hashlib.sha256(encoded).hexdigest()


def _fixture(
    tmp_path: Path,
) -> tuple[Path, dict[str, object], Path, dict[str, object], list[str]]:
    """Create stage-1 evidence plus independently supplied review evidence."""
    repository = Path(__file__).resolve().parents[1]
    verifier = repository / "scripts" / "verify_vitest_termination_evidence.py"
    producer = repository / "pdd" / "sync_core" / "runner.py"
    head = subprocess.run(
        ["git", "rev-parse", "HEAD"], cwd=repository,
        capture_output=True, text=True, check=True,
    ).stdout.strip()
    producer_digest = hashlib.sha256(producer.read_bytes()).hexdigest()
    verifier_digest = hashlib.sha256(verifier.read_bytes()).hexdigest()
    payload: dict[str, object] = {
        "schema": "vitest-termination-v1",
        "failure_baseline_sha": _FAILURE_BASELINE_SHA,
        "protected_base_sha": _PROTECTED_BASE_SHA,
        "diagnostic_head_sha": head,
        "producer_sha256": producer_digest,
        "verifier_sha256": verifier_digest,
        "runner_image": _RUNNER_IMAGE,
        "runner_provisioner": _RUNNER_PROVISIONER,
        "python": _PYTHON_VERSION,
        "node": _NODE_VERSION,
        "vitest_package_sha256": _VITEST_PACKAGE_SHA256,
        "vitest_lock_sha256": _VITEST_LOCK_SHA256,
        "test_node": _TEST_NODE,
        "process_role": "vitest-coordinator",
        "failure_stage": "reporter-addon-load",
        "cause_code": "reporter-addon-load-failed",
        "exit_code": 1,
        "cgroup_memory_oom_delta": 0,
        "cgroup_memory_oom_kill_delta": 0,
        "cgroup_pids_max_delta": 0,
        "diagnostic_sha256": "d" * 64,
        "cause_red_status": "pending",
    }
    review: dict[str, object] = {
        "schema": "vitest-diagnostic-review-v1",
        "failure_baseline_sha": _FAILURE_BASELINE_SHA,
        "protected_base_sha": _PROTECTED_BASE_SHA,
        "diagnostic_head_sha": head,
        "producer_sha256": producer_digest,
        "verifier_sha256": verifier_digest,
        "verdict": "APPROVE",
        "behavioral_verdict": "NO_BEHAVIORAL_FIX",
    }
    evidence = tmp_path / "vitest-termination-v1.json"
    review_evidence = tmp_path / "vitest-diagnostic-review-v1.json"
    evidence_digest = _write_canonical(evidence, payload)
    review_digest = _write_canonical(review_evidence, review)
    arguments = [
        sys.executable, str(verifier),
        "--evidence", str(evidence),
        "--evidence-sha256", evidence_digest,
        "--review-evidence", str(review_evidence),
        "--review-evidence-sha256", review_digest,
        "--repository", str(repository),
        "--failure-baseline-sha", _FAILURE_BASELINE_SHA,
        "--protected-base-sha", _PROTECTED_BASE_SHA,
        "--diagnostic-head-sha", head,
        "--producer-sha256", producer_digest,
        "--verifier-sha256", verifier_digest,
        "--runner-image", _RUNNER_IMAGE,
        "--runner-provisioner", _RUNNER_PROVISIONER,
        "--python", _PYTHON_VERSION,
        "--node", _NODE_VERSION,
        "--vitest-package-sha256", _VITEST_PACKAGE_SHA256,
        "--vitest-lock-sha256", _VITEST_LOCK_SHA256,
        "--test-node", _TEST_NODE,
    ]
    return evidence, payload, review_evidence, review, arguments


def _rewrite(
    path: Path, payload: dict[str, object], arguments: list[str], option: str,
) -> None:
    """Rewrite one canonical input and update only its declared digest."""
    arguments[arguments.index(option) + 1] = _write_canonical(path, payload)


def _verify(arguments: list[str]) -> subprocess.CompletedProcess[str]:
    """Run the standalone verifier without raising on expected rejection."""
    return subprocess.run(arguments, capture_output=True, text=True, check=False)


def test_verifier_accepts_exact_stage_one_evidence(tmp_path: Path) -> None:
    """A reviewed stage-1 artifact is accepted without claiming cause RED."""
    _evidence, _payload, _review_path, _review, arguments = _fixture(tmp_path)

    completed = _verify(arguments)

    assert completed.returncode == 0, completed.stderr
    assert "cause-specific RED pending" in completed.stdout


def test_verifier_accepts_review_preflight_before_candidate_execution(
    tmp_path: Path,
) -> None:
    """The independently reviewed identity can be checked before pytest."""
    _evidence, _payload, _review_path, _review, arguments = _fixture(tmp_path)
    evidence_index = arguments.index("--evidence")
    del arguments[evidence_index:evidence_index + 2]
    digest_index = arguments.index("--evidence-sha256")
    del arguments[digest_index:digest_index + 2]
    arguments.insert(2, "--review-only")

    completed = _verify(arguments)

    assert completed.returncode == 0, completed.stderr
    assert "review evidence verified" in completed.stdout


@pytest.mark.parametrize("field", ("process_role", "failure_stage", "cause_code"))
def test_verifier_rejects_unknown_classification(
    tmp_path: Path, field: str,
) -> None:
    """UNKNOWN cannot stand in for a concrete protected operation failure."""
    evidence, payload, _review_path, _review, arguments = _fixture(tmp_path)
    payload[field] = "UNKNOWN"
    _rewrite(evidence, payload, arguments, "--evidence-sha256")

    assert _verify(arguments).returncode != 0


@pytest.mark.parametrize(
    "mutation",
    (
        "unknown-field", "missing-field", "boolean-exit", "negative-cgroup",
        "wrong-red-status", "invalid-cause-combination", "wrong-mode",
    ),
)
def test_verifier_rejects_malformed_or_unrelated_evidence(
    tmp_path: Path, mutation: str,
) -> None:
    """The exact schema and fixed operation/cause mapping fail closed."""
    evidence, payload, _review_path, _review, arguments = _fixture(tmp_path)
    if mutation == "unknown-field":
        payload["candidate_detail"] = "candidate-controlled-secret"
    elif mutation == "missing-field":
        del payload["diagnostic_sha256"]
    elif mutation == "boolean-exit":
        payload["exit_code"] = True
    elif mutation == "negative-cgroup":
        payload["cgroup_pids_max_delta"] = -1
    elif mutation == "wrong-red-status":
        payload["cause_red_status"] = "fail"
    elif mutation == "invalid-cause-combination":
        payload["failure_stage"] = "reporter-constructor"
    else:
        evidence.chmod(0o644)
        assert _verify(arguments).returncode != 0
        return
    _rewrite(evidence, payload, arguments, "--evidence-sha256")

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
    ),
)
def test_verifier_rejects_every_protected_pin_mismatch(
    tmp_path: Path, option: str, replacement: str,
) -> None:
    """Every protected argument must equal artifact and review inputs."""
    _evidence, _payload, _review_path, _review, arguments = _fixture(tmp_path)
    arguments[arguments.index(option) + 1] = replacement

    assert _verify(arguments).returncode != 0


def test_verifier_rejects_paired_artifact_and_argument_identity_substitution(
    tmp_path: Path,
) -> None:
    """In-band agreement cannot replace the independently reviewed identity."""
    evidence, payload, _review_path, _review, arguments = _fixture(tmp_path)
    replacement = "a" * 40
    payload["diagnostic_head_sha"] = replacement
    _rewrite(evidence, payload, arguments, "--evidence-sha256")
    arguments[arguments.index("--diagnostic-head-sha") + 1] = replacement

    assert _verify(arguments).returncode != 0


@pytest.mark.parametrize(
    "mutation", ("extra", "verdict", "head", "producer", "verifier", "digest"),
)
def test_verifier_rejects_untrusted_or_malformed_review_evidence(
    tmp_path: Path, mutation: str,
) -> None:
    """Review evidence is independently digested, exact, and identity binding."""
    _evidence, _payload, review_path, review, arguments = _fixture(tmp_path)
    if mutation == "extra":
        review["comment"] = "not protected"
    elif mutation == "verdict":
        review["behavioral_verdict"] = "APPROVED"
    elif mutation == "head":
        review["diagnostic_head_sha"] = "a" * 40
    elif mutation == "producer":
        review["producer_sha256"] = "b" * 64
    elif mutation == "verifier":
        review["verifier_sha256"] = "c" * 64
    else:
        arguments[arguments.index("--review-evidence-sha256") + 1] = "f" * 64
        assert _verify(arguments).returncode != 0
        return
    _rewrite(review_path, review, arguments, "--review-evidence-sha256")

    assert _verify(arguments).returncode != 0
