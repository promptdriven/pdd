#!/usr/bin/env python3
"""Fail-closed verifier for fixed-enum Vitest Stage A diagnostics."""

# pylint: disable=too-many-boolean-expressions,too-many-branches,unidiomatic-typecheck

from __future__ import annotations

import argparse
import hashlib
import json
import stat
import subprocess
import sys
from pathlib import Path


_SCHEMA = "vitest-stage-a-native-seal-v1"
_REVIEW_SCHEMA = "vitest-diagnostic-review-v1"
_ATTESTATION_SCHEMA = "vitest-wheel-package-attestation-v1"
_MAX_EVIDENCE_BYTES = 16 * 1024
_MAX_ATTESTATION_BYTES = 4096
_MAX_PROGRESS_FRAMES = 32
_STATIC_PINS = {
    "failure_baseline_sha": "b09b6bef2c8c4bee762965be463527cd0b050154",
    "protected_base_sha": "39776aa9bb027c638812a01b8dabbe03cab92f64",
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
_COMMON_FIELDS = frozenset({
    "schema", "failure_baseline_sha", "protected_base_sha", "trigger_head_sha",
    "checkout_head_sha", "reviewed_head_sha", "review_evidence_sha256",
    "producer_sha256", "termination_verifier_sha256",
    "observation_verifier_sha256", "stage_a_verifier_sha256",
    "native_addon_sha256", "package_verifier_sha256",
    "package_provenance_sha256", "runner_image", "runner_provisioner",
    "python", "node", "vitest_package_sha256", "vitest_lock_sha256",
    "test_node", "lane", "runner_origin", "supervisor_exit_code",
    "result_frame_present", "process_role", "failure_stage",
    "native_failure_reason", "progress_frames", "cgroup_memory_oom_delta",
    "cgroup_memory_oom_kill_delta", "cgroup_pids_max_delta", "cause_red_status",
})
_WHEEL_FIELDS = frozenset({
    "package_attestation_sha256", "wheel_sha256", "installed_runner_sha256",
})
_REVIEW_FIELDS = frozenset({
    "schema", "failure_baseline_sha", "protected_base_sha", "diagnostic_head_sha",
    "producer_sha256", "verifier_sha256", "observation_verifier_sha256",
    "stage_a_verifier_sha256", "native_addon_sha256",
    "package_verifier_sha256", "package_provenance_sha256", "verdict",
    "behavioral_verdict",
})
_ATTESTATION_FIELDS = frozenset({
    "schema", "diagnostic_head_sha", "wheel_sha256", "producer_sha256",
    "installed_runner_sha256", "import_origin",
})
_NATIVE_REASONS = frozenset({
    "PDD_VITEST_SEAL_INVALID_ARGUMENT",
    "PDD_VITEST_SEAL_DESCRIPTOR_IDENTITY",
    "PDD_VITEST_SEAL_PROCFS_SEAL",
    "PDD_VITEST_SEAL_DESCRIPTOR_TABLE_OPEN",
    "PDD_VITEST_SEAL_DESCRIPTOR_INSPECTION",
    "PDD_VITEST_SEAL_CLOEXEC_SET",
    "PDD_VITEST_SEAL_CLOEXEC_VERIFICATION",
    "PDD_VITEST_SEAL_DESCRIPTOR_TABLE_READ",
    "PDD_VITEST_SEAL_DESCRIPTOR_TABLE_CLOSE",
    "PDD_VITEST_SEAL_ALIAS_NOT_FOUND",
    "PDD_VITEST_SEAL_RESPONSE_CREATION",
})
_REQUIRED_PROGRESS = (
    "post-drop-probes", "candidate-exec", "coordinator-bootstrap",
    "reporter-module-start", "reporter-addon-load-start",
    "reporter-addon-load-succeeded", "reporter-authority-seal-start",
    "reporter-authority-seal-failed", "coordinator-exit",
)
_OPTIONAL_PROGRESS = frozenset({
    "coordinator-uncaught-exception", "coordinator-explicit-exit",
    "coordinator-before-exit",
})


class StageAEvidenceError(ValueError):
    """A deliberately non-reflective Stage A evidence rejection."""


def _is_digest(value: object, length: int) -> bool:
    """Return whether one value is an exact lowercase hexadecimal digest."""
    return (
        type(value) is str
        and len(value) == length
        and all(character in "0123456789abcdef" for character in value)
    )


def _sha256(path: Path) -> str:
    """Hash one verifier-controlled regular file."""
    return hashlib.sha256(path.read_bytes()).hexdigest()


def _regular(path: Path) -> Path:
    """Resolve one non-symlink regular file without accepting a substitution."""
    metadata = path.lstat()
    if stat.S_ISLNK(metadata.st_mode) or not stat.S_ISREG(metadata.st_mode):
        raise StageAEvidenceError
    return path.resolve(strict=True)


def _no_duplicate_object(pairs: list[tuple[object, object]]) -> dict[str, object]:
    """Decode a JSON object while rejecting duplicate and non-string keys."""
    decoded: dict[str, object] = {}
    for key, value in pairs:
        if type(key) is not str or key in decoded:
            raise StageAEvidenceError
        decoded[key] = value
    return decoded


def _decode(path: Path, expected_digest: str, maximum: int) -> dict[str, object]:
    """Decode exact canonical evidence and its owner-only SHA-256 sidecar."""
    if not _is_digest(expected_digest, 64):
        raise StageAEvidenceError
    evidence = _regular(path)
    sidecar = _regular(Path(str(path) + ".sha256"))
    parent = evidence.parent.stat()
    metadata = evidence.stat()
    sidecar_metadata = sidecar.stat()
    if (
        not stat.S_ISDIR(parent.st_mode)
        or stat.S_IMODE(parent.st_mode) & 0o022
        or stat.S_IMODE(metadata.st_mode) != 0o600
        or stat.S_IMODE(sidecar_metadata.st_mode) != 0o600
        or not 0 < metadata.st_size <= maximum
    ):
        raise StageAEvidenceError
    encoded = evidence.read_bytes()
    if (
        hashlib.sha256(encoded).hexdigest() != expected_digest
        or sidecar.read_bytes() != expected_digest.encode("ascii") + b"\n"
    ):
        raise StageAEvidenceError
    try:
        payload = json.loads(
            encoded.decode("ascii"), object_pairs_hook=_no_duplicate_object,
            parse_constant=lambda _value: (_ for _ in ()).throw(StageAEvidenceError()),
        )
    except (UnicodeDecodeError, json.JSONDecodeError, StageAEvidenceError) as exc:
        raise StageAEvidenceError from exc
    if type(payload) is not dict or encoded != (
        json.dumps(payload, sort_keys=True, separators=(",", ":")) + "\n"
    ).encode("ascii"):
        raise StageAEvidenceError
    return payload


def _require_text(value: object) -> None:
    """Require bounded scalar metadata, not an arbitrary diagnostic blob."""
    if (
        type(value) is not str or not value or not value.isascii() or len(value) > 512
        or "\n" in value or "\r" in value or "\x00" in value
    ):
        raise StageAEvidenceError


def _require_progress(value: object) -> None:
    """Require the one native-seal failure route, never a broad boundary."""
    if type(value) is not list or not 0 < len(value) <= _MAX_PROGRESS_FRAMES:
        raise StageAEvidenceError
    if (
        any(type(stage) is not str for stage in value)
        or len(value) != len(set(value))
        or any(stage not in set(_REQUIRED_PROGRESS) | _OPTIONAL_PROGRESS for stage in value)
    ):
        raise StageAEvidenceError
    try:
        positions = tuple(value.index(stage) for stage in _REQUIRED_PROGRESS)
    except ValueError as exc:
        raise StageAEvidenceError from exc
    failure_position = value.index("reporter-authority-seal-failed")
    exit_position = value.index("coordinator-exit")
    if (
        positions != tuple(sorted(positions))
        or any(
            not failure_position < value.index(stage) < exit_position
            for stage in _OPTIONAL_PROGRESS if stage in value
        )
    ):
        raise StageAEvidenceError


def _require_arguments(arguments: argparse.Namespace) -> None:
    """Reject free-form and unreviewed command inputs before decoding evidence."""
    for field, expected in _STATIC_PINS.items():
        if getattr(arguments, field) != expected:
            raise StageAEvidenceError
    for field in (
        "failure_baseline_sha", "protected_base_sha", "trigger_head_sha",
        "checkout_head_sha", "reviewed_head_sha",
    ):
        if not _is_digest(getattr(arguments, field), 40):
            raise StageAEvidenceError
    for field in (
        "evidence_sha256", "review_evidence_sha256", "producer_sha256",
        "termination_verifier_sha256", "observation_verifier_sha256",
        "stage_a_verifier_sha256", "native_addon_sha256",
        "package_verifier_sha256", "package_provenance_sha256",
    ):
        if not _is_digest(getattr(arguments, field), 64):
            raise StageAEvidenceError
    if arguments.lane == "source":
        if any(value is not None for value in (
            arguments.package_attestation, arguments.package_attestation_sha256,
            arguments.wheel_sha256, arguments.installed_runner_sha256,
        )):
            raise StageAEvidenceError
    elif not all(
        isinstance(value, str) and _is_digest(value, 64)
        for value in (
            arguments.package_attestation_sha256, arguments.wheel_sha256,
            arguments.installed_runner_sha256,
        )
    ) or not isinstance(arguments.package_attestation, str) or not arguments.package_attestation:
        raise StageAEvidenceError


def _require_review(review: dict[str, object], arguments: argparse.Namespace) -> None:
    """Bind Stage A to the independently approved exact source identities."""
    expected = {
        "failure_baseline_sha": arguments.failure_baseline_sha,
        "protected_base_sha": arguments.protected_base_sha,
        "diagnostic_head_sha": arguments.reviewed_head_sha,
        "producer_sha256": arguments.producer_sha256,
        "verifier_sha256": arguments.termination_verifier_sha256,
        "observation_verifier_sha256": arguments.observation_verifier_sha256,
        "stage_a_verifier_sha256": arguments.stage_a_verifier_sha256,
        "native_addon_sha256": arguments.native_addon_sha256,
        "package_verifier_sha256": arguments.package_verifier_sha256,
        "package_provenance_sha256": arguments.package_provenance_sha256,
    }
    if (
        set(review) != _REVIEW_FIELDS
        or review.get("schema") != _REVIEW_SCHEMA
        or review.get("verdict") != "APPROVE"
        or review.get("behavioral_verdict") != "NO_BEHAVIORAL_FIX"
        or any(review.get(field) != value for field, value in expected.items())
    ):
        raise StageAEvidenceError


def _git_head(repository: Path) -> str:
    """Read the current local commit only when it has exact SHA grammar."""
    completed = subprocess.run(
        ["git", "rev-parse", "HEAD"], cwd=repository, text=True,
        stdout=subprocess.PIPE, stderr=subprocess.DEVNULL, check=False,
    )
    value = completed.stdout.strip()
    if completed.returncode != 0 or not _is_digest(value, 40):
        raise StageAEvidenceError
    return value


def _is_ancestor(repository: Path, older: str, newer: str) -> bool:
    """Return a quiet exact Git ancestry predicate."""
    return subprocess.run(
        ["git", "merge-base", "--is-ancestor", older, newer], cwd=repository,
        stdout=subprocess.DEVNULL, stderr=subprocess.DEVNULL, check=False,
    ).returncode == 0


def _verify_local_identities(arguments: argparse.Namespace) -> None:
    """Recompute every source identity before accepting the transport artifact."""
    repository = Path(arguments.repository).resolve(strict=True)
    if (
        not repository.is_dir()
        or _git_head(repository) != arguments.reviewed_head_sha
        or arguments.trigger_head_sha != arguments.reviewed_head_sha
        or arguments.checkout_head_sha != arguments.reviewed_head_sha
        or not _is_ancestor(
            repository, arguments.failure_baseline_sha, arguments.reviewed_head_sha,
        )
        or not _is_ancestor(
            repository, arguments.protected_base_sha, arguments.reviewed_head_sha,
        )
    ):
        raise StageAEvidenceError
    identities = (
        (repository / "pdd/sync_core/runner.py", arguments.producer_sha256),
        (repository / "scripts/verify_vitest_termination_evidence.py",
         arguments.termination_verifier_sha256),
        (repository / "scripts/verify_vitest_no_result_observation.py",
         arguments.observation_verifier_sha256),
        (Path(__file__).resolve(strict=True), arguments.stage_a_verifier_sha256),
        (repository / "pdd/sync_core/native/vitest_fd_cloexec.c",
         arguments.native_addon_sha256),
        (repository / "scripts/verify_vitest_package_attestation.py",
         arguments.package_verifier_sha256),
        (repository / "scripts/verify_vitest_package_provenance.sh",
         arguments.package_provenance_sha256),
    )
    for path, expected in identities:
        if _sha256(_regular(path)) != expected:
            raise StageAEvidenceError


def _require_wheel_attestation(arguments: argparse.Namespace) -> None:
    """Bind wheel-lane evidence to one canonical package import attestation."""
    if arguments.lane == "source":
        return
    attestation = _decode(
        Path(arguments.package_attestation), arguments.package_attestation_sha256,
        _MAX_ATTESTATION_BYTES,
    )
    expected = {
        "schema": _ATTESTATION_SCHEMA,
        "diagnostic_head_sha": arguments.reviewed_head_sha,
        "wheel_sha256": arguments.wheel_sha256,
        "producer_sha256": arguments.producer_sha256,
        "installed_runner_sha256": arguments.installed_runner_sha256,
        "import_origin": "installed-wheel",
    }
    if set(attestation) != _ATTESTATION_FIELDS or attestation != expected:
        raise StageAEvidenceError


def _require_payload(payload: dict[str, object], arguments: argparse.Namespace) -> None:
    """Require one exact source or wheel Stage A envelope and native enum."""
    lane = payload.get("lane")
    expected_fields = _COMMON_FIELDS if lane == "source" else _COMMON_FIELDS | _WHEEL_FIELDS
    if set(payload) != expected_fields or lane != arguments.lane:
        raise StageAEvidenceError
    if payload.get("schema") != _SCHEMA:
        raise StageAEvidenceError
    for field in (
        "failure_baseline_sha", "protected_base_sha", "trigger_head_sha",
        "checkout_head_sha", "reviewed_head_sha",
    ):
        if not _is_digest(payload.get(field), 40):
            raise StageAEvidenceError
    for field in (
        "review_evidence_sha256", "producer_sha256",
        "termination_verifier_sha256", "observation_verifier_sha256",
        "stage_a_verifier_sha256", "native_addon_sha256",
        "package_verifier_sha256", "package_provenance_sha256",
    ) + (("package_attestation_sha256", "wheel_sha256", "installed_runner_sha256")
         if lane == "installed-wheel" else ()):
        if not _is_digest(payload.get(field), 64):
            raise StageAEvidenceError
    for field in ("runner_image", "runner_provisioner", "python", "node", "test_node"):
        _require_text(payload.get(field))
    if (
        payload.get("runner_origin") != (
            "source-checkout" if lane == "source" else "installed-wheel"
        )
        or payload.get("supervisor_exit_code") != 0
        or type(payload.get("supervisor_exit_code")) is not int
        or payload.get("result_frame_present") is not False
        or payload.get("process_role") != "vitest-coordinator"
        or payload.get("failure_stage") != "reporter-authority-seal"
        or payload.get("native_failure_reason") not in _NATIVE_REASONS
        or payload.get("cause_red_status") != "pending"
    ):
        raise StageAEvidenceError
    for field in (
        "cgroup_memory_oom_delta", "cgroup_memory_oom_kill_delta",
        "cgroup_pids_max_delta",
    ):
        if type(payload.get(field)) is not int or payload[field] < 0:
            raise StageAEvidenceError
    _require_progress(payload.get("progress_frames"))
    for field in _STATIC_PINS:
        if payload.get(field) != getattr(arguments, field):
            raise StageAEvidenceError
    for field in (
        "failure_baseline_sha", "protected_base_sha", "trigger_head_sha",
        "checkout_head_sha", "reviewed_head_sha", "review_evidence_sha256",
        "producer_sha256", "termination_verifier_sha256",
        "observation_verifier_sha256", "stage_a_verifier_sha256",
        "native_addon_sha256", "package_verifier_sha256",
        "package_provenance_sha256",
    ):
        if payload.get(field) != getattr(arguments, field):
            raise StageAEvidenceError
    if lane == "installed-wheel" and any(
        payload.get(field) != getattr(arguments, field)
        for field in (
            "package_attestation_sha256", "wheel_sha256", "installed_runner_sha256",
        )
    ):
        raise StageAEvidenceError


def _arguments() -> argparse.Namespace:
    """Parse the complete source-or-wheel Stage A verification surface."""
    parser = argparse.ArgumentParser(add_help=True)
    parser.add_argument("--evidence", required=True)
    parser.add_argument("--evidence-sha256", required=True)
    parser.add_argument("--review-evidence", required=True)
    parser.add_argument("--review-evidence-sha256", required=True)
    parser.add_argument("--repository", required=True)
    parser.add_argument("--failure-baseline-sha", required=True)
    parser.add_argument("--protected-base-sha", required=True)
    parser.add_argument("--trigger-head-sha", required=True)
    parser.add_argument("--checkout-head-sha", required=True)
    parser.add_argument("--reviewed-head-sha", required=True)
    parser.add_argument("--producer-sha256", required=True)
    parser.add_argument("--termination-verifier-sha256", required=True)
    parser.add_argument("--observation-verifier-sha256", required=True)
    parser.add_argument("--stage-a-verifier-sha256", required=True)
    parser.add_argument("--native-addon-sha256", required=True)
    parser.add_argument("--package-verifier-sha256", required=True)
    parser.add_argument("--package-provenance-sha256", required=True)
    parser.add_argument("--runner-image", required=True)
    parser.add_argument("--runner-provisioner", required=True)
    parser.add_argument("--python", required=True)
    parser.add_argument("--node", required=True)
    parser.add_argument("--vitest-package-sha256", required=True)
    parser.add_argument("--vitest-lock-sha256", required=True)
    parser.add_argument("--test-node", required=True)
    parser.add_argument("--lane", choices=("source", "installed-wheel"), required=True)
    parser.add_argument("--package-attestation")
    parser.add_argument("--package-attestation-sha256")
    parser.add_argument("--wheel-sha256")
    parser.add_argument("--installed-runner-sha256")
    return parser.parse_args()


def main() -> int:
    """Verify fixed-enum Stage A evidence without changing test behavior."""
    try:
        arguments = _arguments()
        _require_arguments(arguments)
        review = _decode(
            Path(arguments.review_evidence), arguments.review_evidence_sha256,
            _MAX_EVIDENCE_BYTES,
        )
        _require_review(review, arguments)
        _verify_local_identities(arguments)
        _require_wheel_attestation(arguments)
        payload = _decode(
            Path(arguments.evidence), arguments.evidence_sha256,
            _MAX_EVIDENCE_BYTES,
        )
        _require_payload(payload, arguments)
    except (StageAEvidenceError, OSError, ValueError, subprocess.SubprocessError):
        print("Vitest Stage A evidence rejected", file=sys.stderr)
        return 1
    print("Vitest Stage A evidence verified; cause-specific RED pending")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
