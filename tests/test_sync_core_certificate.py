"""Tests for the signed cross-repository certificate predicate."""

import base64
import json
import subprocess
from datetime import datetime, timedelta, timezone

import pytest

from pdd.sync_core import (
    AttestationSigner,
    CandidateArtifactPolicy,
    CandidateArtifactProvenance,
    CheckerIdentity,
    GlobalCertificateOptions,
    LifecycleResult,
    NightlyObservation,
    RepositoryTarget,
    build_global_certificate,
    count_vendored_sync_semantics,
    signer_from_environment,
    verify_global_certificate,
)
from pdd.sync_core.lifecycle import _isolated_lifecycle_environment
from pdd.sync_core.certificate import (
    _NightlyVerificationPolicy,
    _nightly_lineage,
    _nightly_streak,
)


CHECKER = CheckerIdentity(
    "c" * 64,
    "refs/tags/v-test-checker",
    "promptdriven/pdd/.github/workflows/global-sync.yml@refs/tags/v-test-checker",
)
OBSERVATION = NightlyObservation(True, True, 0, True, "BLOCKED", 0)
CANDIDATE_WHEEL_SHA256 = "d" * 64
DEPENDENCY_ENVIRONMENT_DIGEST = "e" * 64
CANDIDATE_BUILDER = AttestationSigner("candidate-builder", b"h" * 32)
CANDIDATE_POLICY = CandidateArtifactPolicy(
    CANDIDATE_BUILDER.issuer,
    CANDIDATE_BUILDER.public_key_bytes(),
    "promptdriven/pdd/.github/workflows/candidate-wheel.yml@refs/heads/main",
    DEPENDENCY_ENVIRONMENT_DIGEST,
    "CPython",
    "3.12.3",
    "cp312",
    "manylinux_2_17_x86_64",
)
MEASURED_CLOSURE = {
    "runtime_lock_sha256": DEPENDENCY_ENVIRONMENT_DIGEST,
    "interpreter": {"implementation": "CPython", "version": "3.12.3",
                    "abi": "cp312", "platform": "manylinux_2_17_x86_64"},
    "installed_files": (("pdd", "1.0", "pdd/__init__.py", "f" * 64),),
    "measurement_authority": "pdd-released-checker-v1",
}


@pytest.fixture(autouse=True)
def _avoid_real_clones(monkeypatch):
    monkeypatch.setattr(
        "pdd.sync_core.certificate._certification_targets",
        lambda targets, _directory: targets,
    )
    monkeypatch.setattr(
        "pdd.sync_core.certificate._nightly_lineage", lambda _row, _targets: True
    )


def _report(name):
    return {
        "ok": True,
        "project_root": name,
        "repository_id": f"repository-{name}",
        "base_sha": "a" * 40,
        "head_sha": "b" * 40,
        "errors": [],
        "recovery_required": [],
        "counts": {
            "unaccounted_tracked_paths": 0,
            "managed_units": 1,
            "protected_expected_managed_units": 1,
            "managed_waivers": 0,
            "trusted_in_sync": 1,
            "verification_profile_complete": 1,
            "trusted_current_evidence": 1,
            "drifted": 0,
            "unbaselined": 0,
            "corrupt": 0,
            "unknown": 0,
            "conflict": 0,
            "failed": 0,
            "invalid": 0,
        },
    }


def _nightly(
    path,
    signer,
    count=7,
    *,
    include_observation=True,
    candidate_artifact=None,
    start=None,
):
    start = start or datetime.now(timezone.utc) - timedelta(days=count - 1)
    rows = []
    for index in range(count):
        checked_at = start + timedelta(days=index)
        row_candidate_artifact = candidate_artifact or _candidate_artifact(
            issued_at=checked_at - timedelta(minutes=5),
            expires_at=checked_at + timedelta(minutes=10),
        )
        reports = [
            {**_report("pdd"), "repository": "pdd"},
            {**_report("pdd_cloud"), "repository": "pdd_cloud"},
        ]
        counts = {
            "unaccounted_tracked_paths": 0,
            "managed_units": 2,
            "protected_expected_managed_units": 2,
            "managed_waivers": 0,
            "trusted_in_sync": 2,
            "verification_profile_complete": 2,
            "trusted_current_evidence": 2,
            "DRIFTED": 0,
            "UNBASELINED": 0,
            "CORRUPT": 0,
            "UNKNOWN": 0,
            "CONFLICT": 0,
            "FAILED": 0,
            "INVALID": 0,
            "pdd_cloud_vendored_sync_semantics": 0,
            "nightly_streak": index,
            "required_nightly_streak": 7,
            "verification_profile_coverage": 100,
            "trusted_current_evidence_coverage": 100,
            "nightly_observation_complete": 1,
        }
        lifecycle = {
            "lifecycle_matrix_failed": 0,
            "required_tests_skipped_or_xfailed": 0,
            "collection_errors": 0,
            "timeouts": 0,
            "post_repair_second_run_writes": 0,
            "post_merge_tree_changes": 0,
            "missing_scenarios": [],
            "candidate_wheel_sha256": CANDIDATE_WHEEL_SHA256,
            "dependency_environment_digest": DEPENDENCY_ENVIRONMENT_DIGEST,
            "candidate_artifact": row_candidate_artifact.payload(),
        }
        body = {
            "schema_version": 3,
            "checked_at": checked_at.isoformat(),
            "checker": CHECKER.payload(),
            "candidate_artifact_policy": CANDIDATE_POLICY.identity(),
            "repositories": reports,
            "counts": counts,
            "lifecycle": lifecycle,
            "scan_ok": True,
            "ok": index >= 7,
        }
        if include_observation:
            body["nightly_observation"] = OBSERVATION.payload()
        rows.append(
            {
                **body,
                "signature": {
                    "algorithm": "Ed25519",
                    "issuer": signer.issuer,
                    "value": signer.sign_bytes(
                        json.dumps(
                            body, sort_keys=True, separators=(",", ":")
                        ).encode()
                    ),
                },
            }
        )
    path.write_text("".join(json.dumps(row) + "\n" for row in rows))


def _expected_ids(certificate):
    return {
        report["repository"]: report["repository_id"]
        for report in certificate["repositories"]
    }


def _candidate_artifact(source_sha="b" * 40, *, issued_at=None, expires_at=None):
    return _candidate_artifact_with_authority(
        CANDIDATE_BUILDER,
        source_sha,
        issued_at=issued_at,
        expires_at=expires_at,
    )


def _candidate_artifact_with_authority(
    authority,
    source_sha="b" * 40,
    *,
    issued_at=None,
    expires_at=None,
):
    now = datetime.now(timezone.utc)
    issued_at = issued_at or now
    expires_at = expires_at or now + timedelta(minutes=10)
    artifact = CandidateArtifactProvenance(
        authority.issuer,
        f"candidate-build-{now.timestamp()}",
        f"candidate-build-nonce-{now.timestamp()}",
        issued_at.isoformat(),
        expires_at.isoformat(),
        CANDIDATE_WHEEL_SHA256,
        source_sha,
        DEPENDENCY_ENVIRONMENT_DIGEST,
        {
            "implementation": CANDIDATE_POLICY.python_implementation,
            "version": CANDIDATE_POLICY.python_version,
            "abi": CANDIDATE_POLICY.python_abi,
            "platform": CANDIDATE_POLICY.python_platform,
        },
        CANDIDATE_POLICY.builder_workflow_identity,
        "",
    )
    return CandidateArtifactProvenance(
        **{
            **artifact.__dict__,
            "signature": authority.sign_bytes(
                json.dumps(
                    artifact.unsigned_payload(), sort_keys=True, separators=(",", ":")
                ).encode()
            ),
        }
    )


def test_lifecycle_child_environment_excludes_all_signing_material(
    tmp_path, monkeypatch
) -> None:
    monkeypatch.setenv("PDD_CERTIFICATE_SIGNING_KEY", "certificate-secret")
    monkeypatch.setenv("PDD_ATTESTATION_SIGNING_KEY", "attestation-secret")
    monkeypatch.setenv("OPENAI_API_KEY", "provider-secret")
    environment = _isolated_lifecycle_environment(tmp_path / "isolated-home")
    assert "PDD_CERTIFICATE_SIGNING_KEY" not in environment
    assert "PDD_ATTESTATION_SIGNING_KEY" not in environment
    assert "OPENAI_API_KEY" not in environment
    assert environment["HOME"] == str(tmp_path / "isolated-home")


def test_certificate_signing_uses_remote_verified_authority(
    monkeypatch,
) -> None:
    authority = AttestationSigner("certificate-kms", b"k" * 32)
    monkeypatch.setenv("PDD_CERTIFICATE_ISSUER", authority.issuer)
    monkeypatch.setenv(
        "PDD_CERTIFICATE_PUBLIC_KEY",
        base64.b64encode(authority.public_key_bytes()).decode("ascii"),
    )
    monkeypatch.setenv(
        "PDD_CERTIFICATE_SIGNER_COMMAND", json.dumps(["protected-kms-sign"])
    )

    def remote_sign(command, *, input, capture_output, check):
        assert command == ("protected-kms-sign",)
        assert capture_output is True and check is False
        signature = authority.sign_bytes(input).encode("ascii")
        return subprocess.CompletedProcess(command, 0, stdout=signature, stderr=b"")

    monkeypatch.setattr("pdd.sync_core.certificate.subprocess.run", remote_sign)
    signer = signer_from_environment()
    assert signer.sign_bytes(b"canonical certificate") == authority.sign_bytes(
        b"canonical certificate"
    )


def test_local_certificate_private_key_is_forbidden(monkeypatch) -> None:
    monkeypatch.setenv("PDD_CERTIFICATE_SIGNING_KEY", "candidate-secret")
    with pytest.raises(ValueError, match="local certificate signing keys are forbidden"):
        signer_from_environment()


def test_complete_global_predicate_is_signed_and_verifiable(tmp_path, monkeypatch) -> None:
    pdd = tmp_path / "pdd"
    cloud = tmp_path / "pdd_cloud"
    pdd.mkdir()
    cloud.mkdir()
    nightly = tmp_path / "nightly.jsonl"
    signer = AttestationSigner("certificate-ci", b"g" * 32)
    _nightly(nightly, signer)
    monkeypatch.setattr(
        "pdd.sync_core.certificate.build_canonical_report",
        lambda root, _options: _report(str(root)),
    )
    monkeypatch.setattr(
        "pdd.sync_core.certificate._validate_target", lambda target: target
    )
    monkeypatch.setattr(
        "pdd.sync_core.certificate.count_vendored_sync_semantics", lambda *_a, **_k: 0
    )
    lifecycle = LifecycleResult(
        0,
        0,
        0,
        0,
        0,
        0,
        candidate_wheel_sha256=CANDIDATE_WHEEL_SHA256,
        dependency_environment_digest=DEPENDENCY_ENVIRONMENT_DIGEST,
        candidate_artifact=_candidate_artifact(),
        **MEASURED_CLOSURE,
    )
    certificate = build_global_certificate(
        (
            RepositoryTarget("pdd", pdd),
            RepositoryTarget("pdd_cloud", cloud),
        ),
        GlobalCertificateOptions(
            tmp_path / "replay",
            lifecycle,
            nightly,
            checker_identity=CHECKER,
            nightly_observation=OBSERVATION,
            candidate_artifact_policy=CANDIDATE_POLICY,
        ),
        signer=signer,
    )
    assert certificate["ok"] is True
    assert certificate["counts"]["managed_units"] == 2
    assert certificate["counts"]["verification_profile_coverage"] == 100
    assert certificate["counts"]["trusted_current_evidence_coverage"] == 100
    expected = {
        "pdd": ("a" * 40, "b" * 40),
        "pdd_cloud": ("a" * 40, "b" * 40),
    }
    assert verify_global_certificate(
        certificate,
        signer.public_key_bytes(),
        expected_issuer=signer.issuer,
        expected_repository_shas=expected,
        expected_repository_ids=_expected_ids(certificate),
        expected_checker_identity=CHECKER,
        expected_candidate_artifact_policy=CANDIDATE_POLICY,
    ) is True
    assert (
        certificate["lifecycle"]["candidate_wheel_sha256"]
        == CANDIDATE_WHEEL_SHA256
    )
    certificate["lifecycle"]["candidate_wheel_sha256"] = "not-a-wheel-digest"
    body = {key: value for key, value in certificate.items() if key != "signature"}
    certificate["signature"]["value"] = signer.sign_bytes(
        json.dumps(body, sort_keys=True, separators=(",", ":")).encode()
    )
    assert verify_global_certificate(
        certificate,
        signer.public_key_bytes(),
        expected_issuer=signer.issuer,
        expected_repository_shas=expected,
        expected_repository_ids=_expected_ids(certificate),
        expected_checker_identity=CHECKER,
        expected_candidate_artifact_policy=CANDIDATE_POLICY,
    ) is False
    certificate["lifecycle"]["candidate_wheel_sha256"] = CANDIDATE_WHEEL_SHA256
    forged_artifact = certificate["lifecycle"]["candidate_artifact"]
    forged_artifact["source_sha"] = "c" * 40
    unsigned_artifact = {
        key: value for key, value in forged_artifact.items() if key != "signature"
    }
    forged_artifact["signature"]["value"] = CANDIDATE_BUILDER.sign_bytes(
        json.dumps(unsigned_artifact, sort_keys=True, separators=(",", ":")).encode()
    )
    body = {key: value for key, value in certificate.items() if key != "signature"}
    certificate["signature"]["value"] = signer.sign_bytes(
        json.dumps(body, sort_keys=True, separators=(",", ":")).encode()
    )
    assert verify_global_certificate(
        certificate,
        signer.public_key_bytes(),
        expected_issuer=signer.issuer,
        expected_repository_shas=expected,
        expected_repository_ids=_expected_ids(certificate),
        expected_checker_identity=CHECKER,
        expected_candidate_artifact_policy=CANDIDATE_POLICY,
    ) is False
    certificate["counts"]["managed_units"] = 0
    assert verify_global_certificate(
        certificate,
        signer.public_key_bytes(),
        expected_issuer=signer.issuer,
        expected_repository_shas=expected,
        expected_repository_ids=_expected_ids(certificate),
        expected_checker_identity=CHECKER,
        expected_candidate_artifact_policy=CANDIDATE_POLICY,
    ) is False


def test_missing_lifecycle_scenario_blocks_certificate(tmp_path, monkeypatch) -> None:
    for name in ("pdd", "pdd_cloud"):
        (tmp_path / name).mkdir()
    nightly = tmp_path / "nightly.jsonl"
    signer = AttestationSigner("certificate-ci", b"g" * 32)
    _nightly(nightly, signer)
    monkeypatch.setattr(
        "pdd.sync_core.certificate.build_canonical_report",
        lambda root, _options: _report(str(root)),
    )
    monkeypatch.setattr(
        "pdd.sync_core.certificate._validate_target", lambda target: target
    )
    monkeypatch.setattr(
        "pdd.sync_core.certificate.count_vendored_sync_semantics", lambda *_a, **_k: 0
    )
    lifecycle = LifecycleResult(
        0,
        0,
        0,
        0,
        0,
        0,
        ("merge-group",),
        CANDIDATE_WHEEL_SHA256,
        DEPENDENCY_ENVIRONMENT_DIGEST,
        _candidate_artifact(),
    )
    certificate = build_global_certificate(
        (
            RepositoryTarget("pdd", tmp_path / "pdd"),
            RepositoryTarget("pdd_cloud", tmp_path / "pdd_cloud"),
        ),
        GlobalCertificateOptions(
            tmp_path / "replay",
            lifecycle,
            nightly,
            checker_identity=CHECKER,
            nightly_observation=OBSERVATION,
            candidate_artifact_policy=CANDIDATE_POLICY,
        ),
        signer=signer,
    )
    assert certificate["ok"] is False
    expected = {
        "pdd": ("a" * 40, "b" * 40),
        "pdd_cloud": ("a" * 40, "b" * 40),
    }
    assert verify_global_certificate(
        certificate,
        signer.public_key_bytes(),
        expected_issuer=signer.issuer,
        expected_repository_shas=expected,
        expected_repository_ids=_expected_ids(certificate),
        expected_checker_identity=CHECKER,
        expected_candidate_artifact_policy=CANDIDATE_POLICY,
    ) is False


def test_certificate_acceptance_binds_freshness_issuer_and_exact_refs(
    tmp_path, monkeypatch
) -> None:
    for name in ("pdd", "pdd_cloud"):
        (tmp_path / name).mkdir()
    signer = AttestationSigner("certificate-ci", b"g" * 32)
    nightly = tmp_path / "nightly.jsonl"
    _nightly(nightly, signer)
    monkeypatch.setattr(
        "pdd.sync_core.certificate.build_canonical_report",
        lambda root, _options: _report(str(root)),
    )
    monkeypatch.setattr(
        "pdd.sync_core.certificate._validate_target", lambda target: target
    )
    monkeypatch.setattr(
        "pdd.sync_core.certificate.count_vendored_sync_semantics",
        lambda *_args, **_kwargs: 0,
    )
    certificate = build_global_certificate(
        (
            RepositoryTarget("pdd", tmp_path / "pdd"),
            RepositoryTarget("pdd_cloud", tmp_path / "pdd_cloud"),
        ),
        GlobalCertificateOptions(
            tmp_path / "replay",
            LifecycleResult(
                0,
                0,
                0,
                0,
                0,
                0,
                candidate_wheel_sha256=CANDIDATE_WHEEL_SHA256,
                dependency_environment_digest=DEPENDENCY_ENVIRONMENT_DIGEST,
                candidate_artifact=_candidate_artifact(),
                **MEASURED_CLOSURE,
            ),
            nightly,
            checker_identity=CHECKER,
            nightly_observation=OBSERVATION,
            candidate_artifact_policy=CANDIDATE_POLICY,
        ),
        signer=signer,
    )
    expected = {
        "pdd": ("a" * 40, "b" * 40),
        "pdd_cloud": ("a" * 40, "b" * 40),
    }
    checked = datetime.fromisoformat(certificate["checked_at"])
    common = {
        "expected_issuer": signer.issuer,
        "expected_repository_shas": expected,
        "expected_repository_ids": _expected_ids(certificate),
        "expected_checker_identity": CHECKER,
        "expected_candidate_artifact_policy": CANDIDATE_POLICY,
    }
    assert verify_global_certificate(
        certificate, signer.public_key_bytes(), **common
    ) is True
    other_checker = CheckerIdentity(
        "d" * 64,
        CHECKER.release_ref,
        CHECKER.workflow_identity,
    )
    assert verify_global_certificate(
        certificate,
        signer.public_key_bytes(),
        expected_issuer=signer.issuer,
        expected_repository_shas=expected,
        expected_repository_ids=_expected_ids(certificate),
        expected_checker_identity=other_checker,
        expected_candidate_artifact_policy=CANDIDATE_POLICY,
    ) is False
    wrong_ids = {**_expected_ids(certificate), "pdd_cloud": "wrong-repository"}
    assert verify_global_certificate(
        certificate,
        signer.public_key_bytes(),
        expected_issuer=signer.issuer,
        expected_repository_shas=expected,
        expected_repository_ids=wrong_ids,
        expected_checker_identity=CHECKER,
        expected_candidate_artifact_policy=CANDIDATE_POLICY,
    ) is False
    assert verify_global_certificate(
        certificate,
        signer.public_key_bytes(),
        now=checked + timedelta(hours=1),
        **common,
    ) is False
    assert verify_global_certificate(
        certificate,
        signer.public_key_bytes(),
        expected_issuer="wrong-issuer",
        expected_repository_shas=expected,
        expected_repository_ids=_expected_ids(certificate),
        expected_checker_identity=CHECKER,
        expected_candidate_artifact_policy=CANDIDATE_POLICY,
    ) is False
    wrong_refs = {**expected, "pdd_cloud": ("a" * 40, "c" * 40)}
    assert verify_global_certificate(
        certificate,
        signer.public_key_bytes(),
        expected_issuer=signer.issuer,
        expected_repository_shas=wrong_refs,
        expected_repository_ids=_expected_ids(certificate),
        expected_checker_identity=CHECKER,
        expected_candidate_artifact_policy=CANDIDATE_POLICY,
    ) is False


def test_vendored_sync_function_is_counted(tmp_path) -> None:
    subprocess.run(["git", "init", "-q"], cwd=tmp_path, check=True)
    subprocess.run(
        ["git", "config", "user.email", "certificate@example.com"],
        cwd=tmp_path,
        check=True,
    )
    subprocess.run(
        ["git", "config", "user.name", "Certificate Test"],
        cwd=tmp_path,
        check=True,
    )
    policy = tmp_path / ".pdd/sync-consumer-boundary.json"
    policy.parent.mkdir()
    policy.write_text(
        json.dumps(
            {
                "schema_version": 1,
                "canonical_package": "pdd.sync_core",
                "forbidden_paths": ["**/pdd_fingerprint.py"],
                "forbidden_imports": ["pdd.operation_log"],
                "forbidden_symbols": ["extract_include_deps"],
                "excluded_paths": [],
            }
        )
    )
    service = tmp_path / "service.py"
    service.write_text("def extract_include_deps(path):\n    return {}\n")
    prompt = tmp_path / "prompts/service_Python.prompt"
    prompt.parent.mkdir()
    prompt.write_text("Call pdd.operation_log.save_fingerprint after each run.\n")
    architecture = tmp_path / "architecture.json"
    architecture.write_text(
        json.dumps(
            [
                {
                    "filename": "service_Python.prompt",
                    "description": "Owns extract_include_deps for consumer sync",
                }
            ]
        )
    )
    subprocess.run(["git", "add", "."], cwd=tmp_path, check=True)
    subprocess.run(["git", "commit", "-qm", "consumer"], cwd=tmp_path, check=True)
    assert count_vendored_sync_semantics(tmp_path) == 3


def test_unsigned_nightly_rows_cannot_fabricate_temporal_proof(
    tmp_path, monkeypatch
) -> None:
    for name in ("pdd", "pdd_cloud"):
        (tmp_path / name).mkdir()
    nightly = tmp_path / "nightly.jsonl"
    nightly.write_text(
        "".join(
            json.dumps({"scan_ok": True, "checked_at": "2026-07-10T00:00:00+00:00"})
            + "\n"
            for _ in range(7)
        )
    )
    monkeypatch.setattr(
        "pdd.sync_core.certificate.build_canonical_report",
        lambda root, _options: _report(str(root)),
    )
    monkeypatch.setattr(
        "pdd.sync_core.certificate._validate_target", lambda target: target
    )
    monkeypatch.setattr(
        "pdd.sync_core.certificate.count_vendored_sync_semantics", lambda *_a, **_k: 0
    )
    certificate = build_global_certificate(
        (
            RepositoryTarget("pdd", tmp_path / "pdd"),
            RepositoryTarget("pdd_cloud", tmp_path / "pdd_cloud"),
        ),
        GlobalCertificateOptions(
            tmp_path / "replay",
            LifecycleResult(
                0,
                0,
                0,
                0,
                0,
                0,
                candidate_wheel_sha256=CANDIDATE_WHEEL_SHA256,
                dependency_environment_digest=DEPENDENCY_ENVIRONMENT_DIGEST,
                candidate_artifact=_candidate_artifact(),
                **MEASURED_CLOSURE,
            ),
            nightly,
            checker_identity=CHECKER,
            nightly_observation=OBSERVATION,
            candidate_artifact_policy=CANDIDATE_POLICY,
        ),
        signer=AttestationSigner("certificate-ci", b"g" * 32),
    )
    assert certificate["counts"]["nightly_streak"] == 0
    assert certificate["scan_ok"] is True
    assert certificate["ok"] is False


def test_signed_nightly_rows_without_observations_do_not_extend_streak(
    tmp_path, monkeypatch
) -> None:
    for name in ("pdd", "pdd_cloud"):
        (tmp_path / name).mkdir()
    signer = AttestationSigner("certificate-ci", b"g" * 32)
    nightly = tmp_path / "nightly.jsonl"
    _nightly(nightly, signer, include_observation=False)
    monkeypatch.setattr(
        "pdd.sync_core.certificate.build_canonical_report",
        lambda root, _options: _report(str(root)),
    )
    monkeypatch.setattr(
        "pdd.sync_core.certificate._validate_target", lambda target: target
    )
    monkeypatch.setattr(
        "pdd.sync_core.certificate.count_vendored_sync_semantics", lambda *_a, **_k: 0
    )
    certificate = build_global_certificate(
        (
            RepositoryTarget("pdd", tmp_path / "pdd"),
            RepositoryTarget("pdd_cloud", tmp_path / "pdd_cloud"),
        ),
        GlobalCertificateOptions(
            tmp_path / "replay",
            LifecycleResult(
                0,
                0,
                0,
                0,
                0,
                0,
                candidate_wheel_sha256=CANDIDATE_WHEEL_SHA256,
                dependency_environment_digest=DEPENDENCY_ENVIRONMENT_DIGEST,
                candidate_artifact=_candidate_artifact(),
                **MEASURED_CLOSURE,
            ),
            nightly,
            checker_identity=CHECKER,
            nightly_observation=OBSERVATION,
            candidate_artifact_policy=CANDIDATE_POLICY,
        ),
        signer=signer,
    )
    assert certificate["counts"]["nightly_streak"] == 0
    assert certificate["ok"] is False


def test_signed_nightly_rows_with_untrusted_candidate_artifacts_do_not_extend_streak(
    tmp_path, monkeypatch
) -> None:
    for name in ("pdd", "pdd_cloud"):
        (tmp_path / name).mkdir()
    signer = AttestationSigner("certificate-ci", b"g" * 32)
    attacker = AttestationSigner("attacker-builder", b"z" * 32)
    nightly = tmp_path / "nightly.jsonl"
    _nightly(
        nightly,
        signer,
        candidate_artifact=_candidate_artifact_with_authority(attacker),
    )
    monkeypatch.setattr(
        "pdd.sync_core.certificate.build_canonical_report",
        lambda root, _options: _report(str(root)),
    )
    monkeypatch.setattr(
        "pdd.sync_core.certificate._validate_target", lambda target: target
    )
    monkeypatch.setattr(
        "pdd.sync_core.certificate.count_vendored_sync_semantics", lambda *_a, **_k: 0
    )
    certificate = build_global_certificate(
        (
            RepositoryTarget("pdd", tmp_path / "pdd"),
            RepositoryTarget("pdd_cloud", tmp_path / "pdd_cloud"),
        ),
        GlobalCertificateOptions(
            tmp_path / "replay",
            LifecycleResult(
                0,
                0,
                0,
                0,
                0,
                0,
                candidate_wheel_sha256=CANDIDATE_WHEEL_SHA256,
                candidate_artifact=_candidate_artifact(),
                **MEASURED_CLOSURE,
            ),
            nightly,
            checker_identity=CHECKER,
            nightly_observation=OBSERVATION,
            candidate_artifact_policy=CANDIDATE_POLICY,
        ),
        signer=signer,
    )
    assert certificate["counts"]["nightly_streak"] == 0
    assert certificate["ok"] is False


def test_historical_nightly_candidate_artifact_uses_row_checked_at(tmp_path) -> None:
    signer = AttestationSigner("certificate-ci", b"g" * 32)
    checked_at = datetime.now(timezone.utc) - timedelta(days=1)
    artifact = _candidate_artifact(
        issued_at=checked_at - timedelta(minutes=5),
        expires_at=checked_at + timedelta(minutes=10),
    )
    nightly = tmp_path / "nightly.jsonl"
    _nightly(nightly, signer, count=1, candidate_artifact=artifact, start=checked_at)

    assert _nightly_streak(
        nightly,
        _NightlyVerificationPolicy(
            signer.public_key_bytes(),
            signer.issuer,
            (),
            CHECKER,
            CANDIDATE_POLICY,
        ),
    ) == 1


def test_nightly_lineage_requires_identity_and_ancestry(tmp_path) -> None:
    targets = []
    reports = []
    for name in ("pdd", "pdd_cloud"):
        root = tmp_path / name
        root.mkdir()
        subprocess.run(["git", "init", "-q"], cwd=root, check=True)
        subprocess.run(
            ["git", "config", "user.email", "lineage@example.com"],
            cwd=root,
            check=True,
        )
        subprocess.run(
            ["git", "config", "user.name", "Lineage Test"], cwd=root, check=True
        )
        (root / ".pdd").mkdir()
        identity = f"identity-{name}"
        (root / ".pdd/repository-id").write_text(identity + "\n")
        subprocess.run(["git", "add", "."], cwd=root, check=True)
        subprocess.run(["git", "commit", "-qm", "base"], cwd=root, check=True)
        historical = subprocess.run(
            ["git", "rev-parse", "HEAD"],
            cwd=root,
            capture_output=True,
            text=True,
            check=True,
        ).stdout.strip()
        (root / "later").write_text("current\n")
        subprocess.run(["git", "add", "."], cwd=root, check=True)
        subprocess.run(["git", "commit", "-qm", "head"], cwd=root, check=True)
        current = subprocess.run(
            ["git", "rev-parse", "HEAD"],
            cwd=root,
            capture_output=True,
            text=True,
            check=True,
        ).stdout.strip()
        targets.append(RepositoryTarget(name, root, historical, current))
        reports.append(
            {
                "repository": name,
                "repository_id": identity,
                "head_sha": historical,
            }
        )
    row = {"repositories": reports}
    assert _nightly_lineage(row, tuple(targets)) is True
    reports[1]["repository_id"] = "wrong-identity"
    assert _nightly_lineage(row, tuple(targets)) is False
