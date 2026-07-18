#!/usr/bin/env python3
"""Fail-closed verifier for Vitest exit-zero/no-result observations."""

# pylint: disable=too-many-boolean-expressions,too-many-branches,unidiomatic-typecheck

from __future__ import annotations

import argparse
import hashlib
import json
import stat
import subprocess
import sys
from pathlib import Path


_SCHEMA = "vitest-no-result-observation-v1"
_REVIEW_SCHEMA = "vitest-diagnostic-review-v1"
_MAX_EVIDENCE_BYTES = 16 * 1024
_MAX_PROGRESS_FRAMES = 256
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
    "observation_verifier_sha256", "runner_image", "runner_provisioner",
    "python", "node", "vitest_package_sha256", "vitest_lock_sha256",
    "test_node", "lane", "runner_origin", "supervisor_exit_code",
    "result_frame_present", "progress_frames", "cause_eligible",
})
_WHEEL_FIELDS = frozenset({
    "package_attestation_sha256", "wheel_sha256", "installed_runner_sha256",
})
_REVIEW_FIELDS = frozenset({
    "schema", "failure_baseline_sha", "protected_base_sha", "diagnostic_head_sha",
    "producer_sha256", "verifier_sha256", "observation_verifier_sha256",
    "package_verifier_sha256", "package_provenance_sha256", "verdict",
    "behavioral_verdict",
})
_PROGRESS = frozenset({
    "post-drop-probes", "candidate-exec", "coordinator-bootstrap",
    "coordinator-uncaught-exception", "coordinator-explicit-exit",
    "coordinator-before-exit", "coordinator-exit", "reporter-module-start",
    "reporter-addon-load-start", "reporter-addon-load-failed",
    "reporter-addon-load-succeeded", "reporter-authority-seal-start",
    "reporter-authority-seal-failed", "reporter-authority-seal-invalid",
    "reporter-authority-seal-succeeded", "reporter-constructor-start",
    "reporter-constructor-failed", "reporter-constructor-succeeded",
    "coordinator-start", "worker-start", "collection-complete", "result-published",
})
_PROGRESS_PREDECESSORS = {
    "post-drop-probes": frozenset(),
    "candidate-exec": frozenset({"post-drop-probes"}),
    "coordinator-bootstrap": frozenset({"candidate-exec"}),
    "coordinator-uncaught-exception": frozenset({"coordinator-bootstrap"}),
    "coordinator-explicit-exit": frozenset({"coordinator-bootstrap"}),
    "coordinator-before-exit": frozenset({"coordinator-bootstrap"}),
    "coordinator-exit": frozenset({"coordinator-bootstrap"}),
    "reporter-module-start": frozenset({"coordinator-bootstrap"}),
    "reporter-addon-load-start": frozenset({"reporter-module-start"}),
    "reporter-addon-load-failed": frozenset({"reporter-addon-load-start"}),
    "reporter-addon-load-succeeded": frozenset({"reporter-addon-load-start"}),
    "reporter-authority-seal-start": frozenset({"reporter-addon-load-succeeded"}),
    "reporter-authority-seal-failed": frozenset({"reporter-authority-seal-start"}),
    "reporter-authority-seal-invalid": frozenset({"reporter-authority-seal-start"}),
    "reporter-authority-seal-succeeded": frozenset({"reporter-authority-seal-start"}),
    "reporter-constructor-start": frozenset({"reporter-authority-seal-succeeded"}),
    "reporter-constructor-failed": frozenset({"reporter-constructor-start"}),
    "reporter-constructor-succeeded": frozenset({"reporter-constructor-start"}),
    "coordinator-start": frozenset({"candidate-exec"}),
    "worker-start": frozenset({"candidate-exec"}),
    "collection-complete": frozenset({"coordinator-start"}),
    "result-published": frozenset({"coordinator-start"}),
}
_PROGRESS_OUTCOME_GROUPS = (
    frozenset({"reporter-addon-load-failed", "reporter-addon-load-succeeded"}),
    frozenset({
        "reporter-authority-seal-failed", "reporter-authority-seal-invalid",
        "reporter-authority-seal-succeeded",
    }),
    frozenset({"reporter-constructor-failed", "reporter-constructor-succeeded"}),
)


class ObservationError(ValueError):
    """A deliberately non-reflective no-result observation rejection."""


def _is_digest(value: object, length: int) -> bool:
    return (
        type(value) is str
        and len(value) == length
        and all(character in "0123456789abcdef" for character in value)
    )


def _sha256(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def _regular(path: Path) -> Path:
    metadata = path.lstat()
    if stat.S_ISLNK(metadata.st_mode) or not stat.S_ISREG(metadata.st_mode):
        raise ObservationError
    return path.resolve(strict=True)


def _no_duplicate_object(pairs: list[tuple[object, object]]) -> dict[str, object]:
    payload: dict[str, object] = {}
    for key, value in pairs:
        if type(key) is not str or key in payload:
            raise ObservationError
        payload[key] = value
    return payload


def _decode(path: Path, expected_digest: str) -> dict[str, object]:
    if not _is_digest(expected_digest, 64):
        raise ObservationError
    evidence = _regular(path)
    parent = evidence.parent.stat()
    metadata = evidence.stat()
    sidecar = _regular(Path(str(path) + ".sha256"))
    if (
        stat.S_IMODE(parent.st_mode) & 0o022
        or stat.S_IMODE(metadata.st_mode) != 0o600
        or stat.S_IMODE(sidecar.stat().st_mode) != 0o600
        or not 0 < metadata.st_size <= _MAX_EVIDENCE_BYTES
    ):
        raise ObservationError
    encoded = evidence.read_bytes()
    if (
        hashlib.sha256(encoded).hexdigest() != expected_digest
        or sidecar.read_bytes() != expected_digest.encode("ascii") + b"\n"
    ):
        raise ObservationError
    try:
        payload = json.loads(
            encoded.decode("ascii"), object_pairs_hook=_no_duplicate_object,
            parse_constant=lambda _value: (_ for _ in ()).throw(ObservationError()),
        )
    except (UnicodeDecodeError, json.JSONDecodeError, ObservationError) as exc:
        raise ObservationError from exc
    if type(payload) is not dict or encoded != (
        json.dumps(payload, sort_keys=True, separators=(",", ":")) + "\n"
    ).encode("ascii"):
        raise ObservationError
    return payload


def _require_text(value: object) -> None:
    if (
        type(value) is not str or not value or not value.isascii() or len(value) > 512
        or "\n" in value or "\r" in value or "\x00" in value
    ):
        raise ObservationError


def _require_progress(value: object) -> None:
    if type(value) is not list or len(value) > _MAX_PROGRESS_FRAMES:
        raise ObservationError
    seen: set[str] = set()
    for stage in value:
        if (
            type(stage) is not str
            or stage not in _PROGRESS
            or stage == "result-published"
            or stage in seen
            or "coordinator-exit" in seen
            or not _PROGRESS_PREDECESSORS[stage].issubset(seen)
            or any(stage in group and seen.intersection(group)
                   for group in _PROGRESS_OUTCOME_GROUPS)
        ):
            raise ObservationError
        seen.add(stage)


def _require_payload(payload: dict[str, object], arguments: argparse.Namespace) -> None:
    lane = payload.get("lane")
    expected_fields = _COMMON_FIELDS if lane == "source" else _COMMON_FIELDS | _WHEEL_FIELDS
    if set(payload) != expected_fields or lane != arguments.lane:
        raise ObservationError
    if payload.get("schema") != _SCHEMA:
        raise ObservationError
    for field in (
        "failure_baseline_sha", "protected_base_sha", "trigger_head_sha",
        "checkout_head_sha", "reviewed_head_sha",
    ):
        if not _is_digest(payload.get(field), 40):
            raise ObservationError
    for field in (
        "review_evidence_sha256", "producer_sha256", "termination_verifier_sha256",
        "observation_verifier_sha256",
    ) + (("package_attestation_sha256", "wheel_sha256", "installed_runner_sha256")
         if lane == "installed-wheel" else ()):
        if not _is_digest(payload.get(field), 64):
            raise ObservationError
    for field in ("runner_image", "runner_provisioner", "python", "node", "test_node"):
        _require_text(payload.get(field))
    if (
        payload.get("runner_origin") != (
            "source-checkout" if lane == "source" else "installed-wheel"
        )
        or type(payload.get("supervisor_exit_code")) is not int
        or payload.get("supervisor_exit_code") != 0
        or payload.get("result_frame_present") is not False
        or payload.get("cause_eligible") is not False
    ):
        raise ObservationError
    _require_progress(payload.get("progress_frames"))
    for field in _STATIC_PINS:
        if payload.get(field) != getattr(arguments, field):
            raise ObservationError
    if (
        payload.get("trigger_head_sha") != arguments.trigger_head_sha
        or payload.get("checkout_head_sha") != arguments.checkout_head_sha
        or payload.get("reviewed_head_sha") != arguments.reviewed_head_sha
        or payload.get("producer_sha256") != arguments.producer_sha256
        or payload.get("termination_verifier_sha256") != arguments.termination_verifier_sha256
        or payload.get("observation_verifier_sha256") != arguments.observation_verifier_sha256
        or payload.get("review_evidence_sha256") != arguments.review_evidence_sha256
    ):
        raise ObservationError
    if lane == "source":
        if any(value is not None for value in (
            arguments.package_attestation_sha256, arguments.wheel_sha256,
            arguments.installed_runner_sha256,
        )):
            raise ObservationError
    elif (
        payload.get("package_attestation_sha256") != arguments.package_attestation_sha256
        or payload.get("wheel_sha256") != arguments.wheel_sha256
        or payload.get("installed_runner_sha256") != arguments.installed_runner_sha256
    ):
        raise ObservationError


def _require_review(review: dict[str, object], arguments: argparse.Namespace) -> None:
    if (
        set(review) != _REVIEW_FIELDS
        or review.get("schema") != _REVIEW_SCHEMA
        or review.get("verdict") != "APPROVE"
        or review.get("behavioral_verdict") != "NO_BEHAVIORAL_FIX"
    ):
        raise ObservationError
    expected = {
        "failure_baseline_sha": arguments.failure_baseline_sha,
        "protected_base_sha": arguments.protected_base_sha,
        "diagnostic_head_sha": arguments.reviewed_head_sha,
        "producer_sha256": arguments.producer_sha256,
        "verifier_sha256": arguments.termination_verifier_sha256,
        "observation_verifier_sha256": arguments.observation_verifier_sha256,
        "package_verifier_sha256": arguments.package_verifier_sha256,
        "package_provenance_sha256": arguments.package_provenance_sha256,
    }
    if any(review.get(field) != value for field, value in expected.items()):
        raise ObservationError


def _git_head(repository: Path) -> str:
    completed = subprocess.run(
        ["git", "rev-parse", "HEAD"], cwd=repository, text=True,
        stdout=subprocess.PIPE, stderr=subprocess.DEVNULL, check=False,
    )
    value = completed.stdout.strip()
    if completed.returncode != 0 or not _is_digest(value, 40):
        raise ObservationError
    return value


def _is_ancestor(repository: Path, older: str, newer: str) -> bool:
    return subprocess.run(
        ["git", "merge-base", "--is-ancestor", older, newer], cwd=repository,
        stdout=subprocess.DEVNULL, stderr=subprocess.DEVNULL, check=False,
    ).returncode == 0


def _verify_local_identities(arguments: argparse.Namespace) -> None:
    repository = Path(arguments.repository).resolve(strict=True)
    if (
        not repository.is_dir() or _git_head(repository) != arguments.reviewed_head_sha
        or arguments.checkout_head_sha != arguments.reviewed_head_sha
        or arguments.trigger_head_sha != arguments.reviewed_head_sha
        or not _is_ancestor(
            repository, arguments.failure_baseline_sha, arguments.reviewed_head_sha,
        )
        or not _is_ancestor(
            repository, arguments.protected_base_sha, arguments.reviewed_head_sha,
        )
    ):
        raise ObservationError
    identities = (
        (repository / "pdd/sync_core/runner.py", arguments.producer_sha256),
        (repository / "scripts/verify_vitest_termination_evidence.py",
         arguments.termination_verifier_sha256),
        (Path(__file__).resolve(strict=True),
         arguments.observation_verifier_sha256),
        (repository / "scripts/verify_vitest_package_attestation.py",
         arguments.package_verifier_sha256),
        (repository / "scripts/verify_vitest_package_provenance.sh",
         arguments.package_provenance_sha256),
    )
    for path, expected in identities:
        if _sha256(_regular(path)) != expected:
            raise ObservationError


def _arguments() -> argparse.Namespace:
    """Parse the complete, lane-specific protected observation surface."""
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
    parser.add_argument("--package-attestation-sha256")
    parser.add_argument("--wheel-sha256")
    parser.add_argument("--installed-runner-sha256")
    return parser.parse_args()


def main() -> int:
    """Verify a cause-ineligible Stage A0 observation without reflection."""
    try:
        arguments = _arguments()
        for field, expected in _STATIC_PINS.items():
            if getattr(arguments, field) != expected:
                raise ObservationError
        for field in (
            "failure_baseline_sha", "protected_base_sha", "trigger_head_sha",
            "checkout_head_sha", "reviewed_head_sha",
        ):
            if not _is_digest(getattr(arguments, field), 40):
                raise ObservationError
        for field in (
            "producer_sha256", "termination_verifier_sha256",
            "observation_verifier_sha256", "package_verifier_sha256",
            "package_provenance_sha256", "review_evidence_sha256",
        ):
            if not _is_digest(getattr(arguments, field), 64):
                raise ObservationError
        if arguments.lane == "installed-wheel" and not all(
            _is_digest(value, 64) for value in (
                arguments.package_attestation_sha256, arguments.wheel_sha256,
                arguments.installed_runner_sha256,
            )
        ):
            raise ObservationError
        review = _decode(Path(arguments.review_evidence), arguments.review_evidence_sha256)
        _require_review(review, arguments)
        _verify_local_identities(arguments)
        payload = _decode(Path(arguments.evidence), arguments.evidence_sha256)
        _require_payload(payload, arguments)
    except (ObservationError, OSError, ValueError, subprocess.SubprocessError):
        print("Vitest no-result observation rejected", file=sys.stderr)
        return 1
    print("Vitest no-result observation verified; cause_eligible: false")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
