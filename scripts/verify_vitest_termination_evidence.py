#!/usr/bin/env python3
"""Fail-closed verifier for the diagnostic-only Vitest termination artifact."""

# pylint: disable=duplicate-code,too-many-boolean-expressions,unidiomatic-typecheck

from __future__ import annotations

import argparse
import hashlib
import json
import stat
import subprocess
import sys
from pathlib import Path


_SCHEMA = "vitest-termination-v1"
_MAX_EVIDENCE_BYTES = 16 * 1024
_STATIC_PINS = {
    "failure_baseline_sha": "b09b6bef2c8c4bee762965be463527cd0b050154",
    "protected_base_sha": "cc97ef23a478fa123a7b9ffc5d7450b4d55b70e7",
    "runner_image": "ubuntu-24.04/20260714.240.1",
    "runner_provisioner": "20260707.563",
    "python": "3.12.13",
    "node": "22.23.1",
    "vitest_package_sha256": (
        "63b0ce64263ea3acaed934e5fb5fbbb98d7fcd7673acd40e164dea2a648f2da5"
    ),
    "vitest_lock_sha256": (
        "bfc69a55d08997f553a0901c2ec0b7830cb01d6c6cc81257d150dcc79d20783c"
    ),
    "test_node": (
        "tests/test_sync_core_runner_vitest.py::"
        "test_real_vitest_runs_copied_entrypoint_without_candidate_result_access"
    ),
}
_TOP_LEVEL_FIELDS = frozenset({
    "schema",
    "failure_baseline_sha",
    "protected_base_sha",
    "diagnostic_head_sha",
    "producer_sha256",
    "verifier_sha256",
    "runner_image",
    "runner_provisioner",
    "python",
    "node",
    "vitest_package_sha256",
    "vitest_lock_sha256",
    "test_node",
    "process_role",
    "failure_stage",
    "cause_code",
    "exit_code",
    "cgroup_memory_oom_delta",
    "cgroup_memory_oom_kill_delta",
    "cgroup_pids_max_delta",
    "diagnostic_sha256",
    "red_test",
})
_RED_TEST_FIELDS = frozenset({
    "node_id", "outcome", "failure_baseline_sha", "diagnostic_head_sha",
})
_CAUSES = frozenset({
    (
        "vitest-coordinator",
        "coordinator-bootstrap",
        "coordinator-uncaught-before-reporter",
    ),
    (
        "vitest-coordinator",
        "coordinator-termination",
        "coordinator-explicit-exit",
    ),
    (
        "vitest-coordinator",
        "coordinator-termination",
        "coordinator-event-loop-drained-before-reporter",
    ),
    (
        "vitest-coordinator",
        "reporter-module-load",
        "reporter-module-uncaught",
    ),
    (
        "vitest-coordinator",
        "reporter-addon-load",
        "reporter-addon-load-failed",
    ),
    (
        "vitest-coordinator",
        "reporter-authority-seal",
        "reporter-authority-seal-failed",
    ),
    (
        "vitest-coordinator",
        "reporter-authority-seal",
        "reporter-authority-seal-invalid",
    ),
    (
        "vitest-coordinator",
        "reporter-constructor",
        "reporter-constructor-uncaught",
    ),
})


class EvidenceError(ValueError):
    """A deliberately non-reflective evidence rejection."""


def _sha256(path: Path) -> str:
    """Return the SHA-256 of one verifier-controlled regular file."""
    return hashlib.sha256(path.read_bytes()).hexdigest()


def _is_sha(value: object, length: int) -> bool:
    """Validate an exact lowercase hexadecimal digest without coercion."""
    return (
        type(value) is str
        and len(value) == length
        and all(character in "0123456789abcdef" for character in value)
    )


def _is_test_node(value: object) -> bool:
    """Accept bounded protected node metadata, never arbitrary text blobs."""
    return (
        type(value) is str
        and value.isascii()
        and 1 <= len(value) <= 512
        and value.startswith("tests/")
        and "::" in value
        and "\n" not in value
        and "\r" not in value
        and "\x00" not in value
    )


def _no_duplicate_object(pairs: list[tuple[object, object]]) -> dict[str, object]:
    """Decode a JSON object while rejecting duplicate or non-string keys."""
    result: dict[str, object] = {}
    for key, value in pairs:
        if type(key) is not str or key in result:
            raise EvidenceError
        result[key] = value
    return result


def _decode_evidence(path: Path, expected_digest: str) -> dict[str, object]:
    """Read one mode-restricted canonical artifact and verify its upload digest."""
    if not _is_sha(expected_digest, 64):
        raise EvidenceError
    metadata = path.lstat()
    parent_metadata = path.parent.stat()
    if (
        not stat.S_ISREG(metadata.st_mode)
        or stat.S_IMODE(metadata.st_mode) != 0o600
        or not stat.S_ISDIR(parent_metadata.st_mode)
        or stat.S_IMODE(parent_metadata.st_mode) & 0o022
        or metadata.st_size <= 0
        or metadata.st_size > _MAX_EVIDENCE_BYTES
    ):
        raise EvidenceError
    encoded = path.read_bytes()
    if hashlib.sha256(encoded).hexdigest() != expected_digest:
        raise EvidenceError
    try:
        source = encoded.decode("ascii")
        payload = json.loads(
            source,
            object_pairs_hook=_no_duplicate_object,
            parse_constant=lambda _value: (_ for _ in ()).throw(EvidenceError()),
        )
    except (UnicodeDecodeError, json.JSONDecodeError, EvidenceError) as exc:
        raise EvidenceError from exc
    if type(payload) is not dict:
        raise EvidenceError
    canonical = (
        json.dumps(payload, sort_keys=True, separators=(",", ":")) + "\n"
    ).encode("ascii")
    if encoded != canonical:
        raise EvidenceError
    return payload


def _require_exact_fields(
    payload: dict[str, object], fields: frozenset[str],
) -> None:
    """Reject absent, surplus, or type-confused schema object fields."""
    if set(payload) != fields:
        raise EvidenceError


def _require_scalar_payload(payload: dict[str, object]) -> None:
    """Validate only the artifact's fixed scalar field grammar."""
    if payload.get("schema") != _SCHEMA:
        raise EvidenceError
    for field in (
        "failure_baseline_sha",
        "protected_base_sha",
        "diagnostic_head_sha",
    ):
        if not _is_sha(payload.get(field), 40):
            raise EvidenceError
    for field in (
        "producer_sha256",
        "verifier_sha256",
        "vitest_package_sha256",
        "vitest_lock_sha256",
        "diagnostic_sha256",
    ):
        if not _is_sha(payload.get(field), 64):
            raise EvidenceError
    for field in ("runner_image", "runner_provisioner", "python", "node"):
        value = payload.get(field)
        if (
            type(value) is not str
            or not value.isascii()
            or not value
            or len(value) > 128
            or "\n" in value
            or "\r" in value
            or "\x00" in value
        ):
            raise EvidenceError
    if not _is_test_node(payload.get("test_node")):
        raise EvidenceError
    if type(payload.get("exit_code")) is not int or payload["exit_code"] != 1:
        raise EvidenceError
    for field in (
        "cgroup_memory_oom_delta",
        "cgroup_memory_oom_kill_delta",
        "cgroup_pids_max_delta",
    ):
        value = payload.get(field)
        if type(value) is not int or value < 0:
            raise EvidenceError
    classification = (
        payload.get("process_role"),
        payload.get("failure_stage"),
        payload.get("cause_code"),
    )
    if classification not in _CAUSES:
        raise EvidenceError


def _require_red_metadata(payload: dict[str, object], arguments: argparse.Namespace) -> None:
    """Bind the RED observation to the exact diagnostic and baseline identities."""
    red_test = payload.get("red_test")
    if type(red_test) is not dict:
        raise EvidenceError
    _require_exact_fields(red_test, _RED_TEST_FIELDS)
    if (
        not _is_test_node(red_test.get("node_id"))
        or red_test.get("outcome") != "fail"
        or red_test["node_id"] != arguments.cause_red_test_node
        or red_test["failure_baseline_sha"] != payload["failure_baseline_sha"]
        or red_test["diagnostic_head_sha"] != payload["diagnostic_head_sha"]
    ):
        raise EvidenceError


def _git_sha(repository: Path) -> str:
    """Read HEAD only when Git supplies an exact lower-case commit SHA."""
    completed = subprocess.run(
        ["git", "rev-parse", "HEAD"],
        cwd=repository,
        stdout=subprocess.PIPE,
        stderr=subprocess.DEVNULL,
        text=True,
        check=False,
    )
    value = completed.stdout.strip()
    if completed.returncode != 0 or not _is_sha(value, 40):
        raise EvidenceError
    return value


def _git_is_ancestor(repository: Path, older: str, newer: str) -> bool:
    """Return a quiet, exact Git ancestry predicate."""
    return subprocess.run(
        ["git", "merge-base", "--is-ancestor", older, newer],
        cwd=repository,
        stdout=subprocess.DEVNULL,
        stderr=subprocess.DEVNULL,
        check=False,
    ).returncode == 0


def _require_pins(payload: dict[str, object], arguments: argparse.Namespace) -> None:
    """Require every protected workflow pin to bind the matching artifact field."""
    for field, expected in _STATIC_PINS.items():
        if getattr(arguments, field) != expected:
            raise EvidenceError
    for field in (
        "failure_baseline_sha",
        "protected_base_sha",
        "diagnostic_head_sha",
        "producer_sha256",
        "verifier_sha256",
        "runner_image",
        "runner_provisioner",
        "python",
        "node",
        "vitest_package_sha256",
        "vitest_lock_sha256",
        "test_node",
    ):
        if payload.get(field) != getattr(arguments, field):
            raise EvidenceError
    if arguments.cause_red_outcome != "fail":
        raise EvidenceError


def _verify_local_identities(arguments: argparse.Namespace) -> None:
    """Recompute repository, producer, and verifier identities independently."""
    repository = Path(arguments.repository).resolve(strict=True)
    if not repository.is_dir():
        raise EvidenceError
    head = _git_sha(repository)
    if head != arguments.diagnostic_head_sha:
        raise EvidenceError
    if not (
        _git_is_ancestor(
            repository, arguments.failure_baseline_sha, arguments.diagnostic_head_sha,
        )
        and _git_is_ancestor(
            repository, arguments.protected_base_sha, arguments.diagnostic_head_sha,
        )
    ):
        raise EvidenceError
    producer = repository / "pdd" / "sync_core" / "runner.py"
    producer_metadata = producer.lstat()
    verifier = Path(__file__).resolve(strict=True)
    verifier_metadata = verifier.lstat()
    if (
        not stat.S_ISREG(producer_metadata.st_mode)
        or not stat.S_ISREG(verifier_metadata.st_mode)
        or _sha256(producer) != arguments.producer_sha256
        or _sha256(verifier) != arguments.verifier_sha256
    ):
        raise EvidenceError


def _arguments() -> argparse.Namespace:
    """Parse the complete, independently protected verifier input surface."""
    parser = argparse.ArgumentParser(add_help=True)
    parser.add_argument("--evidence", required=True)
    parser.add_argument("--evidence-sha256", required=True)
    parser.add_argument("--repository", required=True)
    parser.add_argument("--failure-baseline-sha", required=True)
    parser.add_argument("--protected-base-sha", required=True)
    parser.add_argument("--diagnostic-head-sha", required=True)
    parser.add_argument("--producer-sha256", required=True)
    parser.add_argument("--verifier-sha256", required=True)
    parser.add_argument("--runner-image", required=True)
    parser.add_argument("--runner-provisioner", required=True)
    parser.add_argument("--python", required=True)
    parser.add_argument("--node", required=True)
    parser.add_argument("--vitest-package-sha256", required=True)
    parser.add_argument("--vitest-lock-sha256", required=True)
    parser.add_argument("--test-node", required=True)
    parser.add_argument("--cause-red-test-node", required=True)
    parser.add_argument("--cause-red-outcome", required=True)
    return parser.parse_args()


def main() -> int:
    """Verify one complete cause-evidence artifact without reflecting its content."""
    try:
        arguments = _arguments()
        payload = _decode_evidence(
            Path(arguments.evidence), arguments.evidence_sha256,
        )
        _require_exact_fields(payload, _TOP_LEVEL_FIELDS)
        _require_scalar_payload(payload)
        _require_pins(payload, arguments)
        _require_red_metadata(payload, arguments)
        _verify_local_identities(arguments)
    except (EvidenceError, OSError, ValueError, subprocess.SubprocessError):
        print("Vitest termination evidence rejected", file=sys.stderr)
        return 1
    print("Vitest termination evidence verified")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
