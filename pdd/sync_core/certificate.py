"""Cross-repository signed Global Sync Certificate aggregation."""
# pylint: disable=too-many-lines

from __future__ import annotations

import base64
import ast
import json
import os
import subprocess
import fnmatch
import tempfile
from dataclasses import dataclass, replace
from datetime import datetime, timedelta, timezone
from pathlib import Path, PurePosixPath
from typing import Any, Protocol

from cryptography.exceptions import InvalidSignature
from cryptography.hazmat.primitives.asymmetric.ed25519 import Ed25519PublicKey

from .artifact_provenance import (
    CandidateArtifactPolicy,
    CandidateArtifactProvenance,
    CandidateArtifactProvenanceError,
)
from .reporting import CanonicalReportOptions, build_canonical_report


class CertificateSigner(Protocol):
    """Minimal signer surface implemented by protected remote authorities."""

    issuer: str

    def public_key_bytes(self) -> bytes:
        """Return the pinned Ed25519 public key."""

    def sign_bytes(self, payload: bytes) -> str:
        """Return a base64 Ed25519 signature from the remote authority."""


class RemoteCertificateSigner:
    """Invoke a protected KMS/keyless signer without loading private key bytes."""

    def __init__(self, issuer: str, public_key: bytes, command: tuple[str, ...]) -> None:
        if not issuer or len(public_key) != 32 or not command:
            raise ValueError("remote certificate signer configuration is invalid")
        self.issuer = issuer
        self._public_key = public_key
        self._command = command

    def public_key_bytes(self) -> bytes:
        """Return the protected expected public key."""
        return self._public_key

    def sign_bytes(self, payload: bytes) -> str:
        """Sign canonical bytes remotely and verify the response locally."""
        result = subprocess.run(
            self._command,
            input=payload,
            capture_output=True,
            check=False,
        )
        if result.returncode != 0:
            raise ValueError("remote certificate signer rejected the request")
        try:
            signature = base64.b64decode(result.stdout.strip(), validate=True)
            Ed25519PublicKey.from_public_bytes(self._public_key).verify(signature, payload)
        except (ValueError, InvalidSignature) as exc:
            raise ValueError("remote certificate signer returned an invalid signature") from exc
        return base64.b64encode(signature).decode("ascii")


@dataclass(frozen=True)
class RepositoryTarget:
    """Repository path and exact protected refs to certify."""

    name: str
    path: Path
    base_ref: str = "HEAD"
    head_ref: str = "HEAD"


@dataclass(frozen=True)
class LifecycleResult:
    # pylint: disable=too-many-instance-attributes
    """Externally produced required-scenario and test-outcome totals."""

    failed: int
    required_tests_skipped_or_xfailed: int
    collection_errors: int
    timeouts: int
    post_repair_second_run_writes: int
    post_merge_tree_changes: int
    missing_scenarios: tuple[str, ...] = ()
    candidate_wheel_sha256: str = ""
    dependency_environment_digest: str = ""
    candidate_artifact: CandidateArtifactProvenance | None = None


@dataclass(frozen=True)
class CheckerIdentity:
    """Protected released-checker artifact and workflow provenance."""

    wheel_sha256: str
    release_ref: str
    workflow_identity: str

    def __post_init__(self) -> None:
        if (
            len(self.wheel_sha256) != 64
            or any(character not in "0123456789abcdef" for character in self.wheel_sha256)
            or not self.release_ref.startswith("refs/tags/")
            or not self.workflow_identity
        ):
            raise ValueError("released checker identity is malformed")

    def payload(self) -> dict[str, str]:
        """Return the canonical signed checker identity payload."""
        return {
            "wheel_sha256": self.wheel_sha256,
            "release_ref": self.release_ref,
            "workflow_identity": self.workflow_identity,
        }


@dataclass(frozen=True)
class NightlyObservation:
    """Externally observed temporal checks bound into a signed nightly row."""

    complete_scan: bool
    ledgers_deleted_before_scan: bool
    normal_scan_writes: int
    injected_canary_detected: bool
    injected_canary_outcome: str
    post_canary_rerun_writes: int

    def payload(self) -> dict[str, bool | int | str]:
        """Return the canonical signed observation payload."""
        return {
            "complete_scan": self.complete_scan,
            "ledgers_deleted_before_scan": self.ledgers_deleted_before_scan,
            "normal_scan_writes": self.normal_scan_writes,
            "injected_canary_detected": self.injected_canary_detected,
            "injected_canary_outcome": self.injected_canary_outcome,
            "post_canary_rerun_writes": self.post_canary_rerun_writes,
        }


@dataclass(frozen=True)
class _NightlyVerificationPolicy:
    """Protected inputs required to accept one historical nightly row."""

    public_key: bytes
    expected_issuer: str
    targets: tuple[RepositoryTarget, ...]
    checker_identity: CheckerIdentity
    candidate_artifact_policy: CandidateArtifactPolicy


@dataclass(frozen=True)
class GlobalCertificateOptions:
    """Trust and external evidence inputs for global certification."""

    replay_ledger_root: Path
    lifecycle_result: LifecycleResult
    nightly_ledger: Path
    required_nightly_streak: int = 7
    checker_identity: CheckerIdentity | None = None
    nightly_observation: NightlyObservation | None = None
    candidate_artifact_policy: CandidateArtifactPolicy | None = None


def _canonical_bytes(payload: dict[str, Any]) -> bytes:
    return json.dumps(payload, sort_keys=True, separators=(",", ":")).encode()


def count_vendored_sync_semantics(
    root: Path, *, base_ref: str = "HEAD", head_ref: str = "HEAD"
) -> int:
    # pylint: disable=too-many-locals,too-many-boolean-expressions
    """Enforce the protected consumer dependency boundary at exact Git refs."""
    repository_root = Path(root).resolve()
    try:
        raw_policy = _git(
            repository_root,
            "show",
            f"{base_ref}:.pdd/sync-consumer-boundary.json",
        )
        policy = json.loads(raw_policy)
        patterns = policy["forbidden_paths"]
        forbidden_imports = policy["forbidden_imports"]
        forbidden_symbols = policy["forbidden_symbols"]
        excluded_paths = policy["excluded_paths"]
        if (
            policy.get("schema_version") != 1
            or policy.get("canonical_package") != "pdd.sync_core"
            or not isinstance(patterns, list)
            or not patterns
            or not all(isinstance(item, str) and item for item in patterns)
            or not isinstance(forbidden_imports, list)
            or not all(isinstance(item, str) and item for item in forbidden_imports)
            or not isinstance(forbidden_symbols, list)
            or not all(isinstance(item, str) and item for item in forbidden_symbols)
            or not isinstance(excluded_paths, list)
            or not all(isinstance(item, str) and item for item in excluded_paths)
        ):
            return 1
        tracked = _git(repository_root, "ls-tree", "-r", "--name-only", head_ref)
    except (KeyError, json.JSONDecodeError, ValueError):
        return 1
    paths = [item for item in tracked.splitlines() if item]
    analyzed_paths = [
        path
        for path in paths
        if not any(fnmatch.fnmatchcase(path, pattern) for pattern in excluded_paths)
    ]
    count = sum(
        any(fnmatch.fnmatchcase(path, pattern) for pattern in patterns)
        for path in analyzed_paths
    )
    excluded = {"node_modules", "private-pdd", "experiments", "research"}
    blocked_tokens = tuple(forbidden_imports) + tuple(forbidden_symbols)
    declarations = _forbidden_declaration_paths(
        repository_root, head_ref, blocked_tokens
    )
    count += sum(
        path in declarations
        and not any(part in excluded for part in PurePosixPath(path).parts)
        for path in analyzed_paths
    )
    for path in analyzed_paths:
        relpath = PurePosixPath(path)
        if any(part in excluded for part in relpath.parts):
            continue
        if relpath.suffix != ".py":
            continue
        try:
            tree = ast.parse(_git(repository_root, "show", f"{head_ref}:{path}"))
        except (SyntaxError, ValueError):
            count += 1
            continue
        for node in ast.walk(tree):
            imported = None
            if isinstance(node, ast.ImportFrom):
                imported = node.module
            elif isinstance(node, ast.Import):
                imported_names = [item.name for item in node.names]
                count += sum(
                    any(
                        name == blocked or name.startswith(blocked + ".")
                        for blocked in forbidden_imports
                    )
                    for name in imported_names
                )
            if imported is not None and any(
                imported == blocked or imported.startswith(blocked + ".")
                for blocked in forbidden_imports
            ):
                count += 1
            if isinstance(node, (ast.FunctionDef, ast.AsyncFunctionDef)) and any(
                symbol.casefold() in node.name.casefold()
                for symbol in forbidden_symbols
            ):
                count += 1
    return count


def _forbidden_declaration_paths(
    root: Path, ref: str, blocked_tokens: tuple[str, ...]
) -> set[str]:
    """Find prompt and architecture declarations containing protected symbols."""
    command = ["git", "grep", "-I", "-l", "-F"]
    for token in blocked_tokens:
        command.extend(("-e", token))
    command.extend((ref, "--", "*.prompt", "architecture.json", "**/architecture.json"))
    result = subprocess.run(
        command, cwd=root, capture_output=True, text=True, check=False
    )
    if result.returncode not in {0, 1}:
        raise ValueError(result.stderr.strip() or "Git declaration scan failed")
    return {
        line.split(":", 1)[1] if ":" in line else line
        for line in result.stdout.splitlines()
        if line
    }


def _git(root: Path, *args: str) -> str:
    result = subprocess.run(
        ["git", *args], cwd=root, capture_output=True, text=True, check=False
    )
    if result.returncode != 0:
        raise ValueError(result.stderr.strip() or "Git certification check failed")
    return result.stdout.strip()


def _validate_target(target: RepositoryTarget) -> RepositoryTarget:
    path = Path(target.path).resolve()
    base_sha = _git(path, "rev-parse", "--verify", f"{target.base_ref}^{{commit}}")
    head_sha = _git(path, "rev-parse", "--verify", f"{target.head_ref}^{{commit}}")
    if base_sha == head_sha:
        raise ValueError(f"{target.name}: protected base and head must be distinct")
    ancestry = subprocess.run(
        ["git", "merge-base", "--is-ancestor", base_sha, head_sha],
        cwd=path,
        capture_output=True,
        check=False,
    )
    if ancestry.returncode != 0:
        raise ValueError(f"{target.name}: protected base is not an ancestor of head")
    if _git(path, "rev-parse", "HEAD") != head_sha:
        raise ValueError(f"{target.name}: checkout HEAD is not the certified SHA")
    if _git(path, "status", "--porcelain", "--untracked-files=all"):
        raise ValueError(f"{target.name}: certification requires a clean checkout")
    return RepositoryTarget(target.name, path, base_sha, head_sha)


def _certification_targets(
    targets: tuple[RepositoryTarget, ...], directory: Path
) -> tuple[RepositoryTarget, ...]:
    """Create independent exact-SHA clones for all certificate reads."""
    isolated: list[RepositoryTarget] = []
    for target in targets:
        destination = directory / target.name
        command = [
            "git",
            "clone",
            "-q",
            "--no-local",
            "--no-checkout",
            str(target.path),
            str(destination),
        ]
        result = subprocess.run(
            command,
            capture_output=True,
            text=True,
            check=False,
        )
        if result.returncode != 0:
            raise ValueError(f"{target.name}: cannot create certification clone")
        _git(destination, "checkout", "-q", "--detach", target.head_ref)
        _git(destination, "cat-file", "-e", f"{target.base_ref}^{{commit}}")
        isolated.append(
            RepositoryTarget(
                target.name,
                destination,
                target.base_ref,
                target.head_ref,
            )
        )
    return tuple(isolated)


def _nightly_lineage(
    row: dict[str, Any], targets: tuple[RepositoryTarget, ...]
) -> bool:
    reports = row.get("repositories")
    if not isinstance(reports, list):
        return False
    by_name = {
        item.get("repository"): item for item in reports if isinstance(item, dict)
    }
    for target in targets:
        report = by_name.get(target.name)
        if not isinstance(report, dict):
            return False
        historical_head = report.get("head_sha")
        if (
            report.get("repository_id") is None
            or not isinstance(historical_head, str)
            or len(historical_head) != 40
        ):
            return False
        current_identity = _git(target.path, "show", f"{target.head_ref}:.pdd/repository-id")
        if report["repository_id"] != current_identity:
            return False
        ancestry = subprocess.run(
            ["git", "merge-base", "--is-ancestor", historical_head, target.head_ref],
            cwd=target.path,
            capture_output=True,
            check=False,
        )
        if ancestry.returncode != 0:
            return False
    return True


def _complete_nightly(
    row: Any,
    policy: _NightlyVerificationPolicy,
) -> bool:
    if not isinstance(row, dict) or row.get("scan_ok") is not True:
        return False
    repositories = row.get("repositories")
    counts = row.get("counts")
    lifecycle = row.get("lifecycle")
    if not isinstance(repositories, list) or {
        item.get("repository") for item in repositories if isinstance(item, dict)
    } != {"pdd", "pdd_cloud"}:
        return False
    if not isinstance(counts, dict) or not isinstance(lifecycle, dict):
        return False
    try:
        checked_at = _row_checked_at(row)
    except ValueError:
        return False
    required_counts = {
        "unaccounted_tracked_paths",
        "managed_units",
        "trusted_in_sync",
        "nightly_streak",
    }
    required_lifecycle = {
        "lifecycle_matrix_failed",
        "required_tests_skipped_or_xfailed",
        "collection_errors",
        "timeouts",
        "candidate_wheel_sha256",
        "dependency_environment_digest",
        "candidate_artifact",
    }
    if not (
        required_counts <= counts.keys()
        and required_lifecycle <= lifecycle.keys()
        and _nightly_observation_complete(row.get("nightly_observation"))
        and row.get("checker") == policy.checker_identity.payload()
        and _nightly_lineage(row, policy.targets)
        and _verify_certificate_integrity(
            row, policy.public_key, expected_issuer=policy.expected_issuer
        )
    ):
        return False
    return _nightly_candidate_artifact_valid(repositories, lifecycle, policy, checked_at)


def _row_checked_at(row: dict[str, Any]) -> datetime:
    """Return one immutable nightly row timestamp as UTC."""
    try:
        checked_at = datetime.fromisoformat(str(row["checked_at"]))
    except (KeyError, ValueError) as exc:
        raise ValueError("nightly row checked_at is invalid") from exc
    if checked_at.tzinfo is None:
        raise ValueError("nightly row checked_at is not timezone-aware")
    return checked_at.astimezone(timezone.utc)


def _nightly_candidate_artifact_valid(
    repositories: list[Any],
    lifecycle: dict[str, Any],
    policy: _NightlyVerificationPolicy,
    checked_at: datetime,
) -> bool:
    """Verify the candidate artifact embedded in one historical nightly row."""
    by_name = {
        item.get("repository"): item for item in repositories if isinstance(item, dict)
    }
    pdd_report = by_name.get("pdd")
    if not isinstance(pdd_report, dict):
        return False
    try:
        artifact = CandidateArtifactProvenance.from_payload(
            lifecycle.get("candidate_artifact")
        )
        artifact.verify(
            policy.candidate_artifact_policy,
            expected_source_sha=str(pdd_report.get("head_sha", "")),
            now=checked_at,
            consume_replay=False,
        )
    except (CandidateArtifactProvenanceError, ValueError):
        return False
    return artifact.wheel_sha256 == lifecycle.get("candidate_wheel_sha256")


def _nightly_observation_complete(payload: Any) -> bool:
    """Validate the signed observations required for one temporal row."""
    if not isinstance(payload, dict):
        return False
    return (
        payload.get("complete_scan") is True
        and payload.get("ledgers_deleted_before_scan") is True
        and payload.get("normal_scan_writes") == 0
        and not isinstance(payload.get("normal_scan_writes"), bool)
        and payload.get("injected_canary_detected") is True
        and payload.get("injected_canary_outcome") in {"REPAIRED", "BLOCKED"}
        and payload.get("post_canary_rerun_writes") == 0
        and not isinstance(payload.get("post_canary_rerun_writes"), bool)
    )


def _nightly_streak(
    path: Path,
    policy: _NightlyVerificationPolicy,
) -> int:
    if not path.exists():
        return 0
    if path.is_symlink() or not path.is_file():
        raise ValueError("nightly certificate ledger is unsafe")
    try:
        rows = [json.loads(line) for line in path.read_text().splitlines() if line]
    except json.JSONDecodeError as exc:
        raise ValueError("nightly certificate ledger is malformed") from exc
    streak = 0
    previous_date = None
    today = datetime.now(timezone.utc).date()
    for row in reversed(rows):
        if not _complete_nightly(row, policy):
            break
        try:
            checked_at = _row_checked_at(row)
        except ValueError:
            break
        date = checked_at.date()
        if previous_date is None and date not in {today, today - timedelta(days=1)}:
            break
        if previous_date is not None and (previous_date - date).days != 1:
            break
        streak += 1
        previous_date = date
    return streak


def _aggregate_counts(reports: list[dict[str, Any]]) -> dict[str, int]:
    names = {
        "unaccounted_tracked_paths",
        "managed_units",
        "protected_expected_managed_units",
        "managed_waivers",
        "DRIFTED",
        "UNBASELINED",
        "CORRUPT",
        "UNKNOWN",
        "CONFLICT",
        "FAILED",
        "INVALID",
        "trusted_in_sync",
        "verification_profile_complete",
        "trusted_current_evidence",
    }
    result = {name: 0 for name in names}
    mapping = {
        "DRIFTED": "drifted",
        "UNBASELINED": "unbaselined",
        "CORRUPT": "corrupt",
        "UNKNOWN": "unknown",
        "CONFLICT": "conflict",
        "FAILED": "failed",
        "INVALID": "invalid",
    }
    for report in reports:
        counts = report.get("counts", {})
        for name in names:
            result[name] += int(counts.get(mapping.get(name, name), 0))
    return result


def _scan_predicate(
    counts: dict[str, int], lifecycle: LifecycleResult, extra: dict[str, int]
) -> bool:
    managed = counts["managed_units"]
    baseline_failures = ("DRIFTED", "UNBASELINED", "CORRUPT")
    semantic_failures = ("UNKNOWN", "CONFLICT", "FAILED", "INVALID")
    return (
        counts["unaccounted_tracked_paths"] == 0
        and managed > 0
        and managed == counts["protected_expected_managed_units"]
        and counts["managed_waivers"] == 0
        and counts["trusted_in_sync"] == managed
        and counts["verification_profile_complete"] == managed
        and counts["trusted_current_evidence"] == managed
        and all(counts[name] == 0 for name in baseline_failures)
        and all(counts[name] == 0 for name in semantic_failures)
        and lifecycle.failed == 0
        and lifecycle.required_tests_skipped_or_xfailed == 0
        and lifecycle.collection_errors == 0
        and lifecycle.timeouts == 0
        and not lifecycle.missing_scenarios
        and extra["pdd_cloud_vendored_sync_semantics"] == 0
        and lifecycle.post_repair_second_run_writes == 0
        and lifecycle.post_merge_tree_changes == 0
        and len(lifecycle.candidate_wheel_sha256) == 64
        and all(
            character in "0123456789abcdef"
            for character in lifecycle.candidate_wheel_sha256
        )
        and len(lifecycle.dependency_environment_digest) == 64
        and all(
            character in "0123456789abcdef"
            for character in lifecycle.dependency_environment_digest
        )
        and lifecycle.candidate_artifact is not None
        and extra["nightly_observation_complete"] == 1
    )


def _predicate(
    counts: dict[str, int], lifecycle: LifecycleResult, extra: dict[str, int]
) -> bool:
    return _scan_predicate(counts, lifecycle, extra) and (
        extra["nightly_streak"] >= extra["required_nightly_streak"]
    )


def _canonical_report_predicate(report: dict[str, Any]) -> bool:
    counts = report.get("counts")
    if not isinstance(counts, dict):
        return False
    required = {
        "unaccounted_tracked_paths",
        "managed_units",
        "protected_expected_managed_units",
        "managed_waivers",
        "trusted_in_sync",
        "verification_profile_complete",
        "trusted_current_evidence",
        "drifted",
        "unbaselined",
        "corrupt",
        "unknown",
        "conflict",
        "failed",
        "invalid",
    }
    if not required <= counts.keys() or any(
        not isinstance(counts[name], int) or isinstance(counts[name], bool)
        or counts[name] < 0
        for name in required
    ):
        return False
    managed = counts["managed_units"]
    return (
        report.get("errors") == []
        and report.get("recovery_required") == []
        and isinstance(report.get("repository_id"), str)
        and bool(report["repository_id"])
        and isinstance(report.get("base_sha"), str)
        and len(report["base_sha"]) == 40
        and isinstance(report.get("head_sha"), str)
        and len(report["head_sha"]) == 40
        and managed > 0
        and counts["unaccounted_tracked_paths"] == 0
        and managed == counts["protected_expected_managed_units"]
        and counts["managed_waivers"] == 0
        and counts["trusted_in_sync"] == managed
        and counts["verification_profile_complete"] == managed
        and counts["trusted_current_evidence"] == managed
        and all(
            counts[name] == 0
            for name in (
                "drifted",
                "unbaselined",
                "corrupt",
                "unknown",
                "conflict",
                "failed",
                "invalid",
            )
        )
    )


def _recompute_certificate_predicates(body: dict[str, Any]) -> tuple[bool, bool]:
    # pylint: disable=too-many-locals,too-many-return-statements,too-many-branches
    if body.get("schema_version") != 3:
        return False, False
    checker = body.get("checker")
    try:
        if not isinstance(checker, dict):
            return False, False
        CheckerIdentity(
            str(checker["wheel_sha256"]),
            str(checker["release_ref"]),
            str(checker["workflow_identity"]),
        )
    except (KeyError, ValueError):
        return False, False
    reports = body.get("repositories")
    counts_payload = body.get("counts")
    lifecycle_payload = body.get("lifecycle")
    if (
        not isinstance(reports, list)
        or not isinstance(counts_payload, dict)
        or not isinstance(lifecycle_payload, dict)
    ):
        return False, False
    if {item.get("repository") for item in reports if isinstance(item, dict)} != {
        "pdd",
        "pdd_cloud",
    } or len(reports) != 2:
        return False, False
    report_results = [
        _canonical_report_predicate(item) if isinstance(item, dict) else False
        for item in reports
    ]
    if any(
        not isinstance(item, dict) or item.get("ok") is not result
        for item, result in zip(reports, report_results)
    ):
        return False, False
    aggregate = _aggregate_counts(reports)
    if any(counts_payload.get(name) != value for name, value in aggregate.items()):
        return False, False
    lifecycle_names = {
        "lifecycle_matrix_failed": "failed",
        "required_tests_skipped_or_xfailed": "required_tests_skipped_or_xfailed",
        "collection_errors": "collection_errors",
        "timeouts": "timeouts",
        "post_repair_second_run_writes": "post_repair_second_run_writes",
        "post_merge_tree_changes": "post_merge_tree_changes",
    }
    if any(
        not isinstance(lifecycle_payload.get(name), int)
        or isinstance(lifecycle_payload.get(name), bool)
        or lifecycle_payload[name] < 0
        for name in lifecycle_names
    ) or not isinstance(lifecycle_payload.get("missing_scenarios"), list):
        return False, False
    digest_names = ("candidate_wheel_sha256", "dependency_environment_digest")
    digests = {name: lifecycle_payload.get(name) for name in digest_names}
    if any(
        not isinstance(value, str)
        or len(value) != 64
        or any(character not in "0123456789abcdef" for character in value)
        for value in digests.values()
    ):
        return False, False
    candidate_artifact_payload = lifecycle_payload.get("candidate_artifact")
    try:
        candidate_artifact = CandidateArtifactProvenance.from_payload(
            candidate_artifact_payload
        )
    except (CandidateArtifactProvenanceError, ValueError):
        return False, False
    if candidate_artifact.wheel_sha256 != digests["candidate_wheel_sha256"]:
        return False, False
    pdd_report = next(
        (
            item
            for item in reports
            if isinstance(item, dict) and item.get("repository") == "pdd"
        ),
        None,
    )
    if (
        not isinstance(pdd_report, dict)
        or candidate_artifact.source_sha != pdd_report.get("head_sha")
    ):
        return False, False
    lifecycle = LifecycleResult(
        *(lifecycle_payload[name] for name in lifecycle_names),
        tuple(lifecycle_payload["missing_scenarios"]),
        *(digests[name] for name in digest_names),
        candidate_artifact,
    )
    extra_names = {
        "pdd_cloud_vendored_sync_semantics",
        "nightly_streak",
        "required_nightly_streak",
        "nightly_observation_complete",
    }
    if any(
        not isinstance(counts_payload.get(name), int)
        or isinstance(counts_payload.get(name), bool)
        or counts_payload[name] < 0
        for name in extra_names
    ):
        return False, False
    extra = {name: counts_payload[name] for name in extra_names}
    if extra["nightly_observation_complete"] != int(
        _nightly_observation_complete(body.get("nightly_observation"))
    ):
        return False, False
    expected_profile_coverage = (
        100
        if aggregate["managed_units"] > 0
        and aggregate["verification_profile_complete"] == aggregate["managed_units"]
        else 0
    )
    expected_evidence_coverage = (
        100
        if aggregate["managed_units"] > 0
        and aggregate["trusted_current_evidence"] == aggregate["managed_units"]
        else 0
    )
    if (
        counts_payload.get("verification_profile_coverage")
        != expected_profile_coverage
        or counts_payload.get("trusted_current_evidence_coverage")
        != expected_evidence_coverage
    ):
        return False, False
    scan_ok = all(report_results) and _scan_predicate(aggregate, lifecycle, extra)
    ok = all(report_results) and _predicate(aggregate, lifecycle, extra)
    return scan_ok, ok


def _build_global_certificate_from_targets(
    targets: tuple[RepositoryTarget, ...],
    options: GlobalCertificateOptions,
    *,
    signer: CertificateSigner,
) -> dict[str, Any]:
    """Build and sign the complete cross-repository machine predicate."""
    if not targets:
        raise ValueError("global certificate requires at least one repository")
    if options.checker_identity is None:
        raise ValueError("global certificate requires released checker identity")
    if options.candidate_artifact_policy is None:
        raise ValueError("global certificate requires candidate artifact policy")
    reports = []
    for target in targets:
        report = build_canonical_report(
            target.path,
            CanonicalReportOptions(
                base_ref=target.base_ref,
                head_ref=target.head_ref,
                replay_ledger_path=options.replay_ledger_root / f"{target.name}.json",
            ),
        )
        reports.append({**report, "repository": target.name})
    counts = _aggregate_counts(reports)
    pdd_report = next(report for report in reports if report["repository"] == "pdd")
    candidate_artifact_valid = False
    if options.lifecycle_result.candidate_artifact is not None:
        try:
            options.lifecycle_result.candidate_artifact.verify(
                options.candidate_artifact_policy,
                expected_source_sha=str(pdd_report.get("head_sha", "")),
            )
            candidate_artifact_valid = True
        except CandidateArtifactProvenanceError:
            candidate_artifact_valid = False
    cloud = next((target for target in targets if target.name == "pdd_cloud"), None)
    extra = {
        "pdd_cloud_vendored_sync_semantics": (
            count_vendored_sync_semantics(
                cloud.path, base_ref=cloud.base_ref, head_ref=cloud.head_ref
            )
            if cloud
            else 1
        ),
        "nightly_streak": _nightly_streak(
            options.nightly_ledger,
            _NightlyVerificationPolicy(
                signer.public_key_bytes(),
                signer.issuer,
                targets,
                options.checker_identity,
                options.candidate_artifact_policy,
            ),
        ),
        "required_nightly_streak": options.required_nightly_streak,
        "nightly_observation_complete": int(
            options.nightly_observation is not None
            and _nightly_observation_complete(options.nightly_observation.payload())
        ),
    }
    lifecycle = (
        options.lifecycle_result
        if candidate_artifact_valid
        else replace(options.lifecycle_result, candidate_artifact=None)
    )
    body: dict[str, Any] = {
        "schema_version": 3,
        "checked_at": datetime.now(timezone.utc).isoformat(),
        "checker": options.checker_identity.payload(),
        "candidate_artifact_policy": options.candidate_artifact_policy.identity(),
        "nightly_observation": (
            options.nightly_observation.payload()
            if options.nightly_observation is not None
            else None
        ),
        "repositories": reports,
        "counts": {
            **counts,
            **extra,
            "verification_profile_coverage": (
                100
                if counts["managed_units"] > 0
                and counts["verification_profile_complete"] == counts["managed_units"]
                else 0
            ),
            "trusted_current_evidence_coverage": (
                100
                if counts["managed_units"] > 0
                and counts["trusted_current_evidence"] == counts["managed_units"]
                else 0
            ),
        },
        "lifecycle": {
            "lifecycle_matrix_failed": lifecycle.failed,
            "required_tests_skipped_or_xfailed": lifecycle.required_tests_skipped_or_xfailed,
            "collection_errors": lifecycle.collection_errors,
            "timeouts": lifecycle.timeouts,
            "post_repair_second_run_writes": lifecycle.post_repair_second_run_writes,
            "post_merge_tree_changes": lifecycle.post_merge_tree_changes,
            "missing_scenarios": list(lifecycle.missing_scenarios),
            "candidate_wheel_sha256": lifecycle.candidate_wheel_sha256,
            "dependency_environment_digest": lifecycle.dependency_environment_digest,
            "candidate_artifact": (
                lifecycle.candidate_artifact.payload()
                if lifecycle.candidate_artifact is not None and candidate_artifact_valid
                else None
            ),
        },
    }
    body["scan_ok"] = all(report.get("ok") for report in reports) and _scan_predicate(
        counts, lifecycle, extra
    )
    body["ok"] = all(report.get("ok") for report in reports) and _predicate(
        counts, lifecycle, extra
    )
    return {
        **body,
        "signature": {
            "algorithm": "Ed25519",
            "issuer": signer.issuer,
            "value": signer.sign_bytes(_canonical_bytes(body)),
        },
    }


def build_global_certificate(
    targets: tuple[RepositoryTarget, ...],
    options: GlobalCertificateOptions,
    *,
    signer: CertificateSigner,
) -> dict[str, Any]:
    """Build from independent exact-SHA clones and revalidate before signing."""
    if not targets:
        raise ValueError("global certificate requires at least one repository")
    validated = tuple(_validate_target(target) for target in targets)
    with tempfile.TemporaryDirectory(prefix="pdd-global-certificate-") as directory:
        isolated = _certification_targets(validated, Path(directory))
        certificate = _build_global_certificate_from_targets(
            isolated, options, signer=signer
        )
        revalidated = tuple(_validate_target(target) for target in isolated)
        if tuple((item.base_ref, item.head_ref) for item in revalidated) != tuple(
            (item.base_ref, item.head_ref) for item in isolated
        ):
            raise ValueError("certification clone refs changed during verification")
        return certificate


def _verify_certificate_integrity(
    certificate: dict[str, Any],
    public_key: bytes,
    *,
    expected_issuer: str,
) -> bool:
    """Verify one signed body without treating a red historical scan as accepted."""
    signature = certificate.get("signature")
    if (
        not isinstance(signature, dict)
        or signature.get("algorithm") != "Ed25519"
        or signature.get("issuer") != expected_issuer
    ):
        return False
    body = {key: value for key, value in certificate.items() if key != "signature"}
    try:
        raw = base64.b64decode(str(signature["value"]), validate=True)
        Ed25519PublicKey.from_public_bytes(public_key).verify(raw, _canonical_bytes(body))
    except (KeyError, ValueError, InvalidSignature):
        return False
    scan_ok, ok = _recompute_certificate_predicates(body)
    return body.get("scan_ok") is scan_ok and body.get("ok") is ok


def verify_global_certificate(
    certificate: dict[str, Any],
    public_key: bytes,
    *,
    expected_issuer: str,
    expected_repository_shas: dict[str, tuple[str, str]],
    expected_repository_ids: dict[str, str],
    expected_checker_identity: CheckerIdentity,
    expected_candidate_artifact_policy: CandidateArtifactPolicy,
    now: datetime | None = None,
    maximum_age: timedelta = timedelta(minutes=15),
) -> bool:
    # pylint: disable=too-many-arguments,too-many-return-statements,too-many-locals
    """Accept only a fresh green certificate for exact expected repository refs."""
    if not _verify_certificate_integrity(
        certificate, public_key, expected_issuer=expected_issuer
    ):
        return False
    if certificate.get("ok") is not True or certificate.get("scan_ok") is not True:
        return False
    if certificate.get("checker") != expected_checker_identity.payload():
        return False
    if (
        certificate.get("candidate_artifact_policy")
        != expected_candidate_artifact_policy.identity()
    ):
        return False
    lifecycle = certificate.get("lifecycle")
    reports = certificate.get("repositories")
    if not isinstance(lifecycle, dict) or not isinstance(reports, list):
        return False
    pdd_report = next(
        (
            item
            for item in reports
            if isinstance(item, dict) and item.get("repository") == "pdd"
        ),
        None,
    )
    try:
        artifact = CandidateArtifactProvenance.from_payload(
            lifecycle.get("candidate_artifact")
        )
        artifact.verify(
            expected_candidate_artifact_policy,
            expected_source_sha=str(pdd_report.get("head_sha", "")),
            consume_replay=False,
        )
    except (CandidateArtifactProvenanceError, AttributeError, ValueError):
        return False
    try:
        checked_at = datetime.fromisoformat(str(certificate["checked_at"]))
    except (KeyError, ValueError):
        return False
    if checked_at.tzinfo is None:
        return False
    current = (now or datetime.now(timezone.utc)).astimezone(timezone.utc)
    checked_at = checked_at.astimezone(timezone.utc)
    if checked_at > current or current - checked_at > maximum_age:
        return False
    if not isinstance(reports, list) or len(reports) != len(expected_repository_shas):
        return False
    actual = {
        str(item.get("repository")): (
            item.get("base_sha"),
            item.get("head_sha"),
        )
        for item in reports
        if isinstance(item, dict)
    }
    actual_ids = {
        str(item.get("repository")): item.get("repository_id")
        for item in reports
        if isinstance(item, dict)
    }
    return (
        actual == expected_repository_shas
        and actual_ids == expected_repository_ids
        and set(expected_repository_shas) == set(expected_repository_ids)
    )


def signer_from_environment() -> CertificateSigner:
    """Load a remote signing authority without accepting local private keys."""
    if os.environ.get("PDD_CERTIFICATE_SIGNING_KEY"):
        raise ValueError("local certificate signing keys are forbidden")
    encoded = os.environ.get("PDD_CERTIFICATE_PUBLIC_KEY")
    issuer = os.environ.get("PDD_CERTIFICATE_ISSUER", "")
    command_raw = os.environ.get("PDD_CERTIFICATE_SIGNER_COMMAND", "")
    if not encoded or not issuer or not command_raw:
        raise ValueError("protected remote certificate signer is required")
    try:
        public_key = base64.b64decode(encoded, validate=True)
        command_payload = json.loads(command_raw)
    except (ValueError, json.JSONDecodeError) as exc:
        raise ValueError("remote certificate signer configuration is malformed") from exc
    if not isinstance(command_payload, list) or not all(
        isinstance(item, str) and item for item in command_payload
    ):
        raise ValueError("remote certificate signer command is malformed")
    return RemoteCertificateSigner(issuer, public_key, tuple(command_payload))


def checker_identity_from_environment(
    *, require_execution_marker: bool = True
) -> CheckerIdentity:
    """Load released artifact provenance supplied only by protected CI."""
    if (
        require_execution_marker
        and os.environ.get("PDD_RELEASED_CHECKER_EXECUTION") != "1"
    ):
        raise ValueError("global certification must run through pdd-sync-checker")
    required = {
        "wheel_sha256": os.environ.get("PDD_RELEASED_CHECKER_WHEEL_SHA256", ""),
        "release_ref": os.environ.get("PDD_RELEASED_CHECKER_REF", ""),
        "workflow_identity": os.environ.get(
            "PDD_RELEASED_CHECKER_WORKFLOW_IDENTITY", ""
        ),
    }
    if not all(required.values()):
        raise ValueError("protected released checker provenance is required")
    return CheckerIdentity(**required)
