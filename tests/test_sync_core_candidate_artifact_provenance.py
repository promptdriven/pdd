"""Strict tests for protected candidate-wheel build provenance."""
# pylint: disable=missing-function-docstring,line-too-long

import hashlib
import json
import threading
from datetime import datetime, timedelta, timezone
from pathlib import Path
import sys
import zipfile

import pytest

from pdd.sync_core import AttestationSigner
from pdd.sync_core.artifact_provenance import (
    CandidateArtifactPolicy,
    CandidateArtifactProvenanceError,
    RuntimeBundleError,
    RuntimeBundlePolicy,
    canonical_runtime_manifest_sha256,
    load_candidate_artifact_provenance,
    runtime_bundle_policy_from_environment,
    require_independent_runtime_provenance,
    validate_runtime_bundle,
)


SOURCE_SHA = "a" * 40
LOCK_SHA256 = "b" * 64
WORKFLOW = "promptdriven/pdd/.github/workflows/candidate-wheel.yml@refs/heads/main"
TARGET = {
    "implementation": "CPython",
    "version": "3.12.3",
    "abi": "cp312",
    "platform": "manylinux_2_17_x86_64",
}


def _policy(authority: AttestationSigner) -> CandidateArtifactPolicy:
    return CandidateArtifactPolicy(
        authority.issuer,
        authority.public_key_bytes(),
        WORKFLOW,
        LOCK_SHA256,
        TARGET["implementation"],
        TARGET["version"],
        TARGET["abi"],
        TARGET["platform"],
    )


def _policy_with_replay_ledger(authority: AttestationSigner, replay_ledger) -> CandidateArtifactPolicy:
    policy = _policy(authority)
    policy.replay_ledger_path = replay_ledger
    return policy


def _attestation(
    wheel,
    authority: AttestationSigner,
    **overrides,
) -> dict:
    now = datetime.now(timezone.utc)
    payload = {
        "schema_version": 1,
        "issuer": authority.issuer,
        "attestation_id": "candidate-build-123",
        "nonce": "candidate-build-nonce-123",
        "issued_at": now.isoformat(),
        "expires_at": (now + timedelta(minutes=10)).isoformat(),
        "wheel_sha256": hashlib.sha256(wheel.read_bytes()).hexdigest(),
        "source_sha": SOURCE_SHA,
        "dependency_lock_sha256": LOCK_SHA256,
        "python": TARGET,
        "builder_workflow_identity": WORKFLOW,
    }
    payload.update(overrides)
    payload["signature"] = {
        "algorithm": "Ed25519",
        "value": authority.sign_bytes(
            json.dumps(payload, sort_keys=True, separators=(",", ":")).encode()
        ),
    }
    return payload


def _load(tmp_path, wheel, authority, **overrides):
    path = tmp_path / "candidate-build-attestation.json"
    path.write_text(json.dumps(_attestation(wheel, authority, **overrides)))
    return load_candidate_artifact_provenance(path, wheel, _policy(authority))


def test_unrelated_wheel_cannot_use_another_wheels_attestation(tmp_path) -> None:
    authority = AttestationSigner("candidate-builder", b"a" * 32)
    certified = tmp_path / "certified.whl"
    unrelated = tmp_path / "unrelated.whl"
    certified.write_bytes(b"certified candidate wheel")
    unrelated.write_bytes(b"unrelated candidate wheel")
    with pytest.raises(CandidateArtifactProvenanceError, match="digest"):
        _load(tmp_path, unrelated, authority, wheel_sha256=hashlib.sha256(certified.read_bytes()).hexdigest())


def test_correct_wheel_with_wrong_certified_source_sha_is_rejected(tmp_path) -> None:
    authority = AttestationSigner("candidate-builder", b"a" * 32)
    wheel = tmp_path / "candidate.whl"
    wheel.write_bytes(b"exact wheel")
    with pytest.raises(CandidateArtifactProvenanceError, match="source SHA"):
        _load(tmp_path, wheel, authority, source_sha="c" * 40).verify(
            _policy(authority), expected_source_sha=SOURCE_SHA
        )


def test_forged_build_attestation_is_rejected(tmp_path) -> None:
    authority = AttestationSigner("candidate-builder", b"a" * 32)
    wheel = tmp_path / "candidate.whl"
    wheel.write_bytes(b"exact wheel")
    path = tmp_path / "candidate-build-attestation.json"
    forged = _attestation(wheel, authority)
    forged["source_sha"] = "c" * 40
    path.write_text(json.dumps(forged))
    with pytest.raises(CandidateArtifactProvenanceError, match="signature"):
        load_candidate_artifact_provenance(path, wheel, _policy(authority))


def test_stale_or_replayed_build_attestation_is_rejected(tmp_path) -> None:
    authority = AttestationSigner("candidate-builder", b"a" * 32)
    wheel = tmp_path / "candidate.whl"
    wheel.write_bytes(b"exact wheel")
    with pytest.raises(CandidateArtifactProvenanceError, match="expired"):
        _load(
            tmp_path,
            wheel,
            authority,
            issued_at=(datetime.now(timezone.utc) - timedelta(hours=2)).isoformat(),
            expires_at=(datetime.now(timezone.utc) - timedelta(hours=1)).isoformat(),
        )
    policy = _policy(authority)
    provenance = _load(tmp_path, wheel, authority)
    provenance.verify(policy, expected_source_sha=SOURCE_SHA)
    with pytest.raises(CandidateArtifactProvenanceError, match="replayed"):
        provenance.verify(policy, expected_source_sha=SOURCE_SHA)


def test_overlong_build_attestation_is_rejected(tmp_path) -> None:
    authority = AttestationSigner("candidate-builder", b"a" * 32)
    wheel = tmp_path / "candidate.whl"
    wheel.write_bytes(b"exact wheel")
    issued = datetime.now(timezone.utc)
    with pytest.raises(CandidateArtifactProvenanceError, match="lifetime"):
        _load(
            tmp_path,
            wheel,
            authority,
            issued_at=issued.isoformat(),
            expires_at=(issued + timedelta(days=1)).isoformat(),
        )


@pytest.mark.parametrize("link_parent", [False, True])
def test_durable_replay_ledger_rejects_symlink_components(tmp_path, link_parent) -> None:
    authority = AttestationSigner("candidate-builder", b"a" * 32)
    wheel = tmp_path / "candidate.whl"
    wheel.write_bytes(b"exact wheel")
    outside = tmp_path / "outside"
    outside.mkdir()
    if link_parent:
        linked = tmp_path / "linked"
        linked.symlink_to(outside, target_is_directory=True)
        replay_ledger = linked / "replay.json"
    else:
        target = outside / "replay.json"
        target.write_text("[]")
        replay_ledger = tmp_path / "replay.json"
        replay_ledger.symlink_to(target)
    provenance = _load(tmp_path, wheel, authority)
    with pytest.raises(CandidateArtifactProvenanceError, match="unsafe"):
        provenance.verify(
            _policy_with_replay_ledger(authority, replay_ledger),
            expected_source_sha=SOURCE_SHA,
        )


def test_replayed_build_attestation_is_rejected_across_policy_instances(tmp_path) -> None:
    authority = AttestationSigner("candidate-builder", b"a" * 32)
    wheel = tmp_path / "candidate.whl"
    wheel.write_bytes(b"exact wheel")
    replay_ledger = tmp_path / "external-candidate-replay.json"
    provenance = _load(tmp_path, wheel, authority)
    provenance.verify(
        _policy_with_replay_ledger(authority, replay_ledger),
        expected_source_sha=SOURCE_SHA,
    )
    with pytest.raises(CandidateArtifactProvenanceError, match="replayed"):
        provenance.verify(
            _policy_with_replay_ledger(authority, replay_ledger),
            expected_source_sha=SOURCE_SHA,
        )


def test_concurrent_durable_replay_consumers_are_atomic(tmp_path, monkeypatch) -> None:
    authority = AttestationSigner("candidate-builder", b"a" * 32)
    wheel = tmp_path / "candidate.whl"
    wheel.write_bytes(b"exact wheel")
    replay_ledger = tmp_path / "external-candidate-replay.json"
    provenance = _load(tmp_path, wheel, authority)
    write_barrier = threading.Barrier(2)
    original_write_text = type(replay_ledger).write_text

    def synchronized_ledger_write(path, *args, **kwargs):
        if path == replay_ledger:
            write_barrier.wait(timeout=5)
        return original_write_text(path, *args, **kwargs)

    monkeypatch.setattr(type(replay_ledger), "write_text", synchronized_ledger_write)
    results: list[str] = []
    lock = threading.Lock()

    def consume() -> None:
        try:
            provenance.verify(
                _policy_with_replay_ledger(authority, replay_ledger),
                expected_source_sha=SOURCE_SHA,
            )
            outcome = "accepted"
        except CandidateArtifactProvenanceError as exc:
            outcome = str(exc)
        with lock:
            results.append(outcome)

    threads = [threading.Thread(target=consume) for _ in range(2)]
    for thread in threads:
        thread.start()
    for thread in threads:
        thread.join(timeout=10)

    assert sorted(results) == ["accepted", "candidate attestation is replayed"]


@pytest.mark.parametrize(
    ("field", "value", "error"),
    [
        ("builder_workflow_identity", "attacker/workflow@main", "builder workflow"),
        ("dependency_lock_sha256", "c" * 64, "dependency lock"),
        ("python", {**TARGET, "abi": "cp313"}, "interpreter"),
    ],
)
def test_wrong_protected_build_environment_is_rejected(tmp_path, field, value, error) -> None:
    authority = AttestationSigner("candidate-builder", b"a" * 32)
    wheel = tmp_path / "candidate.whl"
    wheel.write_bytes(b"exact wheel")
    with pytest.raises(CandidateArtifactProvenanceError, match=error):
        _load(tmp_path, wheel, authority, **{field: value}).verify(
            _policy(authority), expected_source_sha=SOURCE_SHA
        )


def test_source_checkout_is_not_a_candidate_artifact(tmp_path) -> None:
    authority = AttestationSigner("candidate-builder", b"a" * 32)
    wheel = tmp_path / "candidate.whl"
    wheel.write_bytes(b"exact wheel")
    checkout = tmp_path / "pdd"
    checkout.mkdir()
    path = tmp_path / "candidate-build-attestation.json"
    path.write_text(json.dumps(_attestation(wheel, authority)))
    with pytest.raises(CandidateArtifactProvenanceError, match="wheel path"):
        load_candidate_artifact_provenance(path, checkout, _policy(authority))


def test_valid_exact_sha_artifact_is_accepted(tmp_path) -> None:
    authority = AttestationSigner("candidate-builder", b"a" * 32)
    wheel = tmp_path / "candidate.whl"
    wheel.write_bytes(b"exact wheel")
    provenance = _load(tmp_path, wheel, authority)
    provenance.verify(_policy(authority), expected_source_sha=SOURCE_SHA)
    assert provenance.source_sha == SOURCE_SHA
    assert provenance.wheel_sha256 == hashlib.sha256(wheel.read_bytes()).hexdigest()


def test_durable_replay_ledger_rejects_symlink_lock(tmp_path) -> None:
    authority = AttestationSigner("candidate-builder", b"a" * 32)
    wheel = tmp_path / "candidate.whl"
    wheel.write_bytes(b"exact wheel")
    replay_ledger = tmp_path / "replay.json"
    outside = tmp_path / "outside.lock"
    outside.write_text("do not touch")
    replay_ledger.with_name("replay.json.lock").symlink_to(outside)
    provenance = _load(tmp_path, wheel, authority)
    with pytest.raises(CandidateArtifactProvenanceError, match="unsafe"):
        provenance.verify(
            _policy_with_replay_ledger(authority, replay_ledger),
            expected_source_sha=SOURCE_SHA,
        )


RUNTIME_IDENTITY = {
    "implementation": "CPython", "version": "3.12.3", "abi": "cp312",
    "platform": "linux_x86_64",
}
RUNTIME_INSTALLED = [{"name": "pdd-cli", "version": "1.2.3",
                      "files": [{"path": "pdd/__init__.py", "sha256": "1" * 64}]}]
RUNTIME_ENTRIES = [
    {"name": "pdd", "path": "bin/pdd", "sha256": "2" * 64},
    {"name": "pdd-sync-checker", "path": "bin/pdd-sync-checker", "sha256": "3" * 64},
]
RUNTIME_STARTUP = {"pth": [], "sitecustomize": None, "usercustomize": None}
RUNTIME_NATIVE = {"status": "complete", "members": [], "shared_libraries": []}


def _runtime_wheel(path: Path, name: str, version: str) -> None:
    """Create a minimal wheel with one exact distribution identity."""
    dist_info = f"{name.replace('-', '_')}-{version}.dist-info"
    with zipfile.ZipFile(path, "w") as archive:
        archive.writestr(f"{dist_info}/METADATA",
                         f"Metadata-Version: 2.1\nName: {name}\nVersion: {version}\n")
        archive.writestr(f"{dist_info}/RECORD", "")


def _runtime_bundle(tmp_path: Path, monkeypatch) -> tuple[Path, dict, RuntimeBundlePolicy]:
    """Build a controlled asset bundle and mock the Linux installed closure."""
    bundle = tmp_path / "bundle"
    wheelhouse = bundle / "wheelhouse"
    wheelhouse.mkdir(parents=True)
    _runtime_wheel(wheelhouse / "click-8.4.1-py3-none-any.whl", "click", "8.4.1")
    _runtime_wheel(wheelhouse / "pdd_cli-1.2.3-py3-none-any.whl", "pdd-cli", "1.2.3")
    members = [{"name": item.name, "sha256": hashlib.sha256(item.read_bytes()).hexdigest()}
               for item in sorted(wheelhouse.iterdir(), key=lambda item: item.name)]
    lock = "".join(f"{name}=={version} --hash=sha256:{digest}\n" for name, version, digest in (
        ("click", "8.4.1", members[0]["sha256"]),
        ("pdd-cli", "1.2.3", members[1]["sha256"]),
    ))
    (bundle / "runtime.lock").write_text(lock, encoding="utf-8")
    manifest = {
        "schema_version": 1, "repository": "promptdriven/pdd", "tag": "v1.2.3",
        "source_sha": "a" * 40, "pdd_wheel": members[1],
        "runtime_lock": {"name": "runtime.lock", "sha256": hashlib.sha256(lock.encode()).hexdigest()},
        "wheelhouse": {"members": members, "digest": canonical_runtime_manifest_sha256(members)},
        "runtime": RUNTIME_IDENTITY, "interpreter": {"sha256": "4" * 64},
        "console_entry_points": RUNTIME_ENTRIES, "installed_distributions": RUNTIME_INSTALLED,
        "startup": RUNTIME_STARTUP, "native_closure": RUNTIME_NATIVE,
        "independent_provenance": {"status": "unsigned-blocked"},
    }
    (bundle / "runtime-manifest.json").write_text(
        json.dumps(manifest, sort_keys=True, separators=(",", ":")), encoding="utf-8")
    monkeypatch.setattr("pdd.sync_core.artifact_provenance._runtime_identity", lambda: RUNTIME_IDENTITY)
    monkeypatch.setattr("pdd.sync_core.artifact_provenance._runtime_site_packages", lambda: tmp_path)
    monkeypatch.setattr("pdd.sync_core.artifact_provenance._runtime_installed_distributions",
                        lambda _root: RUNTIME_INSTALLED)
    monkeypatch.setattr("pdd.sync_core.artifact_provenance._runtime_entry_points",
                        lambda _root: RUNTIME_ENTRIES)
    monkeypatch.setattr("pdd.sync_core.artifact_provenance._runtime_startup", lambda _root: RUNTIME_STARTUP)
    monkeypatch.setattr("pdd.sync_core.artifact_provenance._runtime_native_closure", lambda _root: RUNTIME_NATIVE)
    original_sha = hashlib.sha256
    monkeypatch.setattr("pdd.sync_core.artifact_provenance._sha256", lambda path: (
        "4" * 64 if Path(path) == Path(sys.executable).resolve()
        else original_sha(Path(path).read_bytes()).hexdigest()))
    policy = RuntimeBundlePolicy(canonical_runtime_manifest_sha256(manifest),
                                 "promptdriven/pdd", "v1.2.3", "a" * 40)
    return bundle, manifest, policy


def test_runtime_bundle_valid_round_trip_and_protected_policy(tmp_path, monkeypatch) -> None:
    bundle, manifest, policy = _runtime_bundle(tmp_path, monkeypatch)
    assert validate_runtime_bundle(bundle, policy) == manifest
    monkeypatch.setenv("PDD_RUNTIME_BUNDLE_DIR", str(bundle))
    monkeypatch.setenv("PDD_RUNTIME_BUNDLE_MANIFEST_SHA256", policy.manifest_sha256)
    monkeypatch.setenv("PDD_RUNTIME_BUNDLE_REPOSITORY", policy.repository)
    monkeypatch.setenv("PDD_RUNTIME_BUNDLE_TAG", policy.tag)
    monkeypatch.setenv("PDD_RUNTIME_BUNDLE_SOURCE_SHA", policy.source_sha)
    assert runtime_bundle_policy_from_environment()[1] == policy
    with pytest.raises(RuntimeBundleError, match="independent runtime bundle provenance"):
        require_independent_runtime_provenance(manifest)
    monkeypatch.delenv("PDD_RUNTIME_BUNDLE_MANIFEST_SHA256")
    with pytest.raises(RuntimeBundleError, match="policy is required"):
        runtime_bundle_policy_from_environment()


@pytest.mark.parametrize("mutation", [
    "lock", "wheel", "extra-wheel", "unknown-key", "traversal", "duplicate-normalized",
])
def test_runtime_bundle_asset_schema_and_candidate_policy_mutations_fail_closed(
    tmp_path, monkeypatch, mutation
) -> None:
    bundle, manifest, policy = _runtime_bundle(tmp_path, monkeypatch)
    if mutation == "lock":
        (bundle / "runtime.lock").write_text("click==8.4.1\n", encoding="utf-8")
    elif mutation == "wheel":
        (bundle / "wheelhouse" / manifest["pdd_wheel"]["name"]).write_bytes(b"replacement")
    elif mutation == "extra-wheel":
        _runtime_wheel(bundle / "wheelhouse" / "extra-1.0-py3-none-any.whl", "extra", "1.0")
    else:
        if mutation == "unknown-key":
            manifest["candidate_policy"] = {"accept": True}
        elif mutation == "traversal":
            manifest["pdd_wheel"]["name"] = "../replacement.whl"
        else:
            manifest["wheelhouse"]["members"].append(
                {"name": "PDD_CLI-1.2.3-py3-none-any.whl", "sha256": "0" * 64})
        (bundle / "runtime-manifest.json").write_text(
            json.dumps(manifest, sort_keys=True, separators=(",", ":")), encoding="utf-8")
        policy = RuntimeBundlePolicy(canonical_runtime_manifest_sha256(manifest),
                                     policy.repository, policy.tag, policy.source_sha)
    with pytest.raises(RuntimeBundleError):
        validate_runtime_bundle(bundle, policy)


@pytest.mark.parametrize("function, value", [
    ("_runtime_installed_distributions", [{"name": "pdd-cli", "version": "1.2.3", "files": []}]),
    ("_runtime_entry_points", [{"name": "pdd-sync-checker", "path": "bin/pdd-sync-checker", "sha256": "0" * 64}]),
    ("_runtime_startup", {"pth": [{"path": "injected.pth", "sha256": "0" * 64}], "sitecustomize": None, "usercustomize": None}),
    ("_runtime_identity", {**RUNTIME_IDENTITY, "platform": "wrong"}),
    ("_runtime_native_closure", {"status": "unsupported"}),
])
def test_runtime_record_entrypoint_startup_platform_and_native_mutations_fail_closed(
    tmp_path, monkeypatch, function, value
) -> None:
    bundle, _manifest, policy = _runtime_bundle(tmp_path, monkeypatch)
    monkeypatch.setattr(f"pdd.sync_core.artifact_provenance.{function}",
                        lambda _root=None: value)
    with pytest.raises(RuntimeBundleError):
        validate_runtime_bundle(bundle, policy)
