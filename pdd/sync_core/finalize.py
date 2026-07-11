"""Trusted validation and transactional canonical fingerprint finalization."""

from __future__ import annotations

import base64
import hashlib
import json
import os
import subprocess
import uuid
from dataclasses import dataclass
from datetime import datetime, timezone
from pathlib import Path, PurePosixPath

from .alias_policy import load_protected_aliases
from .evidence_store import (
    encode_attestation,
    evidence_relpath,
    load_attestation,
    load_trust_policy,
)
from .fingerprint_store import FingerprintStore, encode_fingerprint
from .git_io import resolve_git_commit
from .manifest import build_unit_manifest, require_valid_manifest
from .path_policy import PathPolicy
from .runner import (
    TRUSTED_RUNNER_VERSION,
    AttestationIssue,
    RunBinding,
    RunnerConfig,
    run_profile,
    runner_identity_digest,
)
from .snapshot import build_unit_snapshot
from .transaction import (
    FileState,
    PlannedWrite,
    TransactionManager,
    TransactionPhase,
    TransactionResult,
)
from .trust import AttestationBinding, AttestationIssuer, RemoteAttestationSigner
from .types import (
    EvidenceOutcome,
    FingerprintProvenance,
    FingerprintRecord,
    SemanticStatus,
)
from .verification import load_verification_profiles


@dataclass(frozen=True)
class FinalizeResult:
    """Committed trusted finalization and its signed attestation identity."""

    transaction: TransactionResult
    attestation_id: str
    fingerprint_path: PurePosixPath


class CanonicalFinalizationError(RuntimeError):
    """Raised when an opted-in mutation cannot commit trusted final state."""


def preflight_legacy_mutation(paths: dict[str, Path] | None = None) -> None:
    """Reject legacy production mutation before any model call or write."""
    if canonical_root_for_paths(paths) is not None:
        raise CanonicalFinalizationError(
            "protected canonical sync blocks legacy production mutation; "
            "use read-only reporting or trusted finalization until the staged "
            "repair executor is enabled"
        )


def canonical_root_for_paths(paths: dict[str, Path] | None) -> Path | None:
    """Return the opted-in Git root for legacy path-based callers."""
    # pylint: disable=import-outside-toplevel
    from ..continuous_sync import canonical_sync_enabled, repository_root

    start = Path(paths.get("prompt", Path.cwd())) if paths else Path.cwd()
    if not canonical_sync_enabled(start):
        return None
    return repository_root(start)


def finalize_legacy_paths(paths: dict[str, Path] | None) -> bool:
    """Route a legacy fingerprint request through trusted canonical finalization."""
    root = canonical_root_for_paths(paths)
    if root is None:
        return False
    try:
        if not paths or "prompt" not in paths:
            raise ValueError("canonical finalization requires an exact prompt path")
        protected_base = os.environ.get("PDD_SYNC_PROTECTED_BASE_SHA")
        if not protected_base:
            raise ValueError("canonical sync requires PDD_SYNC_PROTECTED_BASE_SHA")
        module = lexical_managed_module(
            root, Path(paths["prompt"]), base_ref=protected_base, head_ref="HEAD"
        )
        finalize_unit(
            root,
            module,
            base_ref=protected_base,
            head_ref="HEAD",
            signer=attestation_signer_from_environment(),
        )
    except (OSError, RuntimeError, ValueError) as exc:
        raise CanonicalFinalizationError(
            f"trusted canonical finalization failed: {exc}"
        ) from exc
    return True


def lexical_managed_module(
    root: Path, prompt: Path, *, base_ref: str, head_ref: str
) -> PurePosixPath:
    """Return a policy-validated prompt's lexical repository identity."""
    repository_root = Path(root).resolve()
    lexical_prompt = Path(os.path.abspath(prompt))
    try:
        module = PurePosixPath(lexical_prompt.relative_to(repository_root).as_posix())
    except ValueError as exc:
        raise ValueError("canonical prompt path escapes project root") from exc
    manifest = build_unit_manifest(
        repository_root, base_ref=base_ref, head_ref=head_ref
    )
    require_valid_manifest(manifest)
    policy = PathPolicy(
        repository_root,
        approved_aliases=load_protected_aliases(repository_root, manifest),
        base_ref=manifest.base_ref,
        head_ref=manifest.head_ref,
    )
    return policy.resolve(module).logical_relpath


def attestation_signer_from_environment() -> AttestationIssuer:
    """Load a remote evidence authority without accepting local private keys."""
    if os.environ.get("PDD_ATTESTATION_SIGNING_KEY"):
        raise ValueError("local attestation signing keys are forbidden")
    encoded = os.environ.get("PDD_ATTESTATION_PUBLIC_KEY")
    issuer = os.environ.get("PDD_ATTESTATION_ISSUER", "")
    command_raw = os.environ.get("PDD_ATTESTATION_SIGNER_COMMAND", "")
    if not encoded or not issuer or not command_raw:
        raise ValueError("protected remote attestation signer is required")
    try:
        public_key = base64.b64decode(encoded, validate=True)
        command_payload = json.loads(command_raw)
    except (ValueError, json.JSONDecodeError) as exc:
        raise ValueError("remote attestation signer configuration is malformed") from exc
    if not isinstance(command_payload, list) or not all(
        isinstance(item, str) and item for item in command_payload
    ):
        raise ValueError("remote attestation signer command is malformed")
    return RemoteAttestationSigner(issuer, public_key, tuple(command_payload))


def _artifact_writes(root: Path, snapshot) -> tuple[PlannedWrite, ...]:
    writes = []
    for artifact in snapshot.artifacts:
        if not artifact.exists or artifact.git_mode not in {"100644", "100755"}:
            raise ValueError(
                f"cannot transactionally finalize artifact: {artifact.relpath}"
            )
        path = root.joinpath(*artifact.relpath.parts)
        content = path.read_bytes()
        if hashlib.sha256(content).hexdigest() != artifact.digest:
            raise ValueError(f"artifact changed while snapshotting: {artifact.relpath}")
        writes.append(
            PlannedWrite(
                artifact.relpath,
                content,
                artifact.git_mode,
                expected=FileState(
                    True, artifact.digest, artifact.git_mode, "regular"
                ),
            )
        )
    return tuple(writes)


def _external_replay_ledger(root: Path, configured: Path | None) -> Path:
    value = configured or (
        Path(os.environ["PDD_ATTESTATION_REPLAY_LEDGER"])
        if os.environ.get("PDD_ATTESTATION_REPLAY_LEDGER")
        else None
    )
    if value is None:
        raise ValueError("canonical finalization requires an external replay ledger")
    replay = value.expanduser().resolve()
    try:
        replay.relative_to(root)
    except ValueError:
        return replay
    raise ValueError("attestation replay ledger must be outside the candidate checkout")


def _reusable_result(
    root: Path,
    snapshot,
    profile,
    store: FingerprintStore,
    verifier,
    *,
    base_sha: str,
    head_sha: str,
    now: datetime,
) -> FinalizeResult | None:
    # pylint: disable=too-many-arguments,too-many-locals
    baseline = store.load(snapshot.unit_id)
    if (
        baseline is None
        or baseline.snapshot != snapshot
        or baseline.claimed_semantic_status is not SemanticStatus.VERIFIED
        or not baseline.attestation_ref
    ):
        return None
    envelope = load_attestation(root, baseline.attestation_ref)
    binding = AttestationBinding(
        snapshot.unit_id,
        snapshot.digest(),
        profile.profile_digest,
        runner_identity_digest(profile, root=root, ref=head_sha),
        TRUSTED_RUNNER_VERSION,
        base_sha,
        envelope.binding.checked_sha,
    )
    verifier.verify_current_for_idempotency(envelope, binding, now=now)
    ancestry = subprocess.run(
        ["git", "merge-base", "--is-ancestor", binding.checked_sha, head_sha],
        cwd=root,
        capture_output=True,
        check=False,
    )
    required = {item.obligation_id for item in profile.obligations if item.required}
    passed = {
        item.obligation_id
        for item in envelope.results
        if item.outcome is EvidenceOutcome.PASS
    }
    if ancestry.returncode != 0 or required != passed:
        return None
    fingerprint = PurePosixPath(store.path_for(snapshot.unit_id).relative_to(root).as_posix())
    transaction = TransactionResult(
        baseline.provenance.transaction_id,
        TransactionPhase.COMMITTED,
        (),
        True,
    )
    return FinalizeResult(transaction, envelope.attestation_id, fingerprint)


def _checkout_is_clean_for_finalization(root: Path) -> bool:
    """Allow only checker-owned durable state from an earlier finalization."""
    status = subprocess.run(
        ["git", "status", "--porcelain=v1", "-z", "--untracked-files=all"],
        cwd=root, capture_output=True, check=False,
    )
    if status.returncode != 0:
        return False
    allowed = (
        ".pdd/meta/v2/", ".pdd/evidence/v2/", ".pdd/locks/transactions/",
        ".pdd/transactions/",
    )
    fields = status.stdout.split(b"\0")
    index = 0
    while index < len(fields) and fields[index]:
        record = fields[index]
        if len(record) < 4:
            return False
        code = record[:2]
        paths = [record[3:].decode("utf-8", errors="surrogateescape")]
        if b"R" in code or b"C" in code:
            index += 1
            if index >= len(fields) or not fields[index]:
                return False
            paths.append(fields[index].decode("utf-8", errors="surrogateescape"))
        if any(not path.startswith(allowed) for path in paths):
            return False
        index += 1
    return True


def finalize_unit(
    root: Path,
    module: PurePosixPath,
    *,
    base_ref: str,
    head_ref: str,
    signer: AttestationIssuer,
    config: RunnerConfig = RunnerConfig(),
    replay_ledger_path: Path | None = None,
) -> FinalizeResult:
    # pylint: disable=too-many-arguments,too-many-locals
    """Validate one complete unit and atomically finalize all trusted state."""
    repository_root = Path(root).resolve()
    base_sha = resolve_git_commit(repository_root, base_ref)
    head_sha = resolve_git_commit(repository_root, head_ref)
    if resolve_git_commit(repository_root, "HEAD") != head_sha:
        raise ValueError("canonical finalization requires HEAD at the checked SHA")
    manifest = build_unit_manifest(
        repository_root, base_ref=base_sha, head_ref=head_sha
    )
    managed_ids = {unit.unit_id for unit in manifest.managed_units}
    if (
        manifest.invalid_reasons
        or manifest.unaccounted_tracked_paths
        or managed_ids != set(manifest.expected_managed)
    ):
        raise ValueError(
            "canonical finalization requires a valid protected candidate manifest"
        )
    matches = [
        unit
        for unit in manifest.managed_units
        if unit.unit_id.prompt_relpath == module
    ]
    if len(matches) != 1:
        raise ValueError(f"finalization requires exactly one managed unit: {module}")
    profiles = load_verification_profiles(repository_root, manifest)
    profile = profiles.for_unit(matches[0].unit_id)
    if profile is None or not profile.complete:
        raise ValueError("finalization requires a complete protected profile")
    snapshot = build_unit_snapshot(repository_root, manifest, matches[0], profile)
    artifact_writes = _artifact_writes(repository_root, snapshot)
    now = datetime.now(timezone.utc)
    replay = _external_replay_ledger(repository_root, replay_ledger_path)
    verifier = load_trust_policy(
        repository_root, base_sha, replay_ledger_path=replay
    ).verifier
    if not _checkout_is_clean_for_finalization(repository_root):
        raise ValueError("canonical finalization requires a completely clean checkout")
    reusable = _reusable_result(
        repository_root,
        snapshot,
        profile,
        FingerprintStore(repository_root),
        verifier,
        base_sha=base_sha,
        head_sha=head_sha,
        now=now,
    )
    if reusable is not None:
        return reusable
    transaction_id = f"finalize-{uuid.uuid4()}"
    attestation_id = f"attestation-{uuid.uuid4()}"
    envelope, executions = run_profile(
        repository_root,
        profile,
        RunBinding(snapshot.digest(), base_sha, head_sha),
        AttestationIssue(signer, attestation_id, str(uuid.uuid4()), now),
        config,
    )
    failures = [item for item in executions if item.outcome is not EvidenceOutcome.PASS]
    if failures:
        detail = "; ".join(
            f"{item.obligation_id}={item.outcome.value}" for item in failures
        )
        raise ValueError(f"trusted validation did not pass: {detail}")
    post_run_snapshot = build_unit_snapshot(
        repository_root, manifest, matches[0], profile
    )
    if post_run_snapshot != snapshot:
        raise ValueError("artifact closure changed during trusted validation")
    verifier.verify(envelope, envelope.binding, now=now)
    provenance = FingerprintProvenance(
        "trusted-validation",
        f"pdd validate --module {module.as_posix()}",
        transaction_id,
        head_sha,
        now.isoformat(),
        TRUSTED_RUNNER_VERSION,
    )
    record = FingerprintRecord(
        snapshot, 2, 2, provenance, SemanticStatus.VERIFIED, attestation_id
    )
    store = FingerprintStore(repository_root)
    store.validate(record)
    fingerprint = PurePosixPath(
        store.path_for(record.snapshot.unit_id).relative_to(repository_root).as_posix()
    )
    writes = (
        *artifact_writes,
        PlannedWrite(evidence_relpath(attestation_id), encode_attestation(envelope), "100644"),
        PlannedWrite(fingerprint, encode_fingerprint(record), "100644"),
    )
    manager = TransactionManager(
        repository_root, approved_aliases=load_protected_aliases(repository_root, manifest)
    )
    manager.prepare(transaction_id, writes)
    transaction = manager.commit(transaction_id)
    return FinalizeResult(transaction, attestation_id, fingerprint)
