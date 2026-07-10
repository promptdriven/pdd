"""Tests for the signed cross-repository certificate predicate."""

import json
import subprocess
from datetime import datetime, timedelta, timezone

import pytest

from pdd.sync_core import (
    AttestationSigner,
    CheckerIdentity,
    GlobalCertificateOptions,
    LifecycleResult,
    RepositoryTarget,
    build_global_certificate,
    count_vendored_sync_semantics,
    verify_global_certificate,
)
from pdd.sync_core.lifecycle import _isolated_lifecycle_environment
from pdd.sync_core.certificate import _nightly_lineage


CHECKER = CheckerIdentity(
    "c" * 64,
    "refs/tags/v-test-checker",
    "promptdriven/pdd/.github/workflows/global-sync.yml@refs/tags/v-test-checker",
)


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


def _nightly(path, signer, count=7):
    start = datetime(2026, 7, 3, tzinfo=timezone.utc)
    rows = []
    for index in range(count):
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
        }
        lifecycle = {
            "lifecycle_matrix_failed": 0,
            "required_tests_skipped_or_xfailed": 0,
            "collection_errors": 0,
            "timeouts": 0,
            "post_repair_second_run_writes": 0,
            "post_merge_tree_changes": 0,
            "missing_scenarios": [],
        }
        body = {
            "schema_version": 2,
            "checked_at": (start + timedelta(days=index)).isoformat(),
            "checker": CHECKER.payload(),
            "repositories": reports,
            "counts": counts,
            "lifecycle": lifecycle,
            "scan_ok": True,
            "ok": index >= 7,
        }
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
    lifecycle = LifecycleResult(0, 0, 0, 0, 0, 0)
    certificate = build_global_certificate(
        (
            RepositoryTarget("pdd", pdd),
            RepositoryTarget("pdd_cloud", cloud),
        ),
        GlobalCertificateOptions(
            tmp_path / "replay", lifecycle, nightly, checker_identity=CHECKER
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
    ) is True
    certificate["counts"]["managed_units"] = 0
    assert verify_global_certificate(
        certificate,
        signer.public_key_bytes(),
        expected_issuer=signer.issuer,
        expected_repository_shas=expected,
        expected_repository_ids=_expected_ids(certificate),
        expected_checker_identity=CHECKER,
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
    lifecycle = LifecycleResult(0, 0, 0, 0, 0, 0, ("merge-group",))
    certificate = build_global_certificate(
        (
            RepositoryTarget("pdd", tmp_path / "pdd"),
            RepositoryTarget("pdd_cloud", tmp_path / "pdd_cloud"),
        ),
        GlobalCertificateOptions(
            tmp_path / "replay", lifecycle, nightly, checker_identity=CHECKER
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
            LifecycleResult(0, 0, 0, 0, 0, 0),
            nightly,
            checker_identity=CHECKER,
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
    ) is False
    wrong_ids = {**_expected_ids(certificate), "pdd_cloud": "wrong-repository"}
    assert verify_global_certificate(
        certificate,
        signer.public_key_bytes(),
        expected_issuer=signer.issuer,
        expected_repository_shas=expected,
        expected_repository_ids=wrong_ids,
        expected_checker_identity=CHECKER,
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
    ) is False
    wrong_refs = {**expected, "pdd_cloud": ("a" * 40, "c" * 40)}
    assert verify_global_certificate(
        certificate,
        signer.public_key_bytes(),
        expected_issuer=signer.issuer,
        expected_repository_shas=wrong_refs,
        expected_repository_ids=_expected_ids(certificate),
        expected_checker_identity=CHECKER,
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
            LifecycleResult(0, 0, 0, 0, 0, 0),
            nightly,
            checker_identity=CHECKER,
        ),
        signer=AttestationSigner("certificate-ci", b"g" * 32),
    )
    assert certificate["counts"]["nightly_streak"] == 0
    assert certificate["scan_ok"] is True
    assert certificate["ok"] is False


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
