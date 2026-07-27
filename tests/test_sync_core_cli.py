"""CLI contract tests for canonical synchronization certification."""
# pylint: disable=missing-function-docstring

import base64
import json
from datetime import datetime, timedelta, timezone

from click.testing import CliRunner

from pdd.cli import cli
from pdd.sync_core import AttestationSigner, CandidateArtifactProvenance, LifecycleResult
from pdd.sync_core.certificate import CheckerIdentity, RepositoryTarget


def test_root_certify_command_is_registered() -> None:
    result = CliRunner().invoke(cli, ["certify", "--help"])
    assert result.exit_code == 0, result.output
    assert "--repos" in result.output
    assert "--run-lifecycle-matrix" in result.output


def test_global_certify_requires_complete_acceptance_inputs(tmp_path) -> None:
    replay = tmp_path / "replay"
    result = CliRunner().invoke(
        cli,
        [
            "certify",
            "--repos",
            "pdd,pdd_cloud",
            "--replay-ledger",
            str(replay),
        ],
    )
    assert result.exit_code == 1
    assert "global certification requires" in result.output
    assert "--full-inventory" in result.output


def test_global_certify_rejects_replayed_candidate_attestation_from_cli_policy(
    tmp_path, monkeypatch
) -> None:
    authority = AttestationSigner("candidate-builder", b"b" * 32)
    lock_sha = "c" * 64
    now = datetime.now(timezone.utc)
    unsigned = {
        "schema_version": 1,
        "issuer": authority.issuer,
        "attestation_id": "candidate-build-123",
        "nonce": "candidate-nonce-123",
        "issued_at": now.isoformat(),
        "expires_at": (now + timedelta(minutes=10)).isoformat(),
        "wheel_sha256": "d" * 64,
        "source_sha": "a" * 40,
        "dependency_lock_sha256": lock_sha,
        "python": {
            "implementation": "CPython",
            "version": "3.12.3",
            "abi": "cp312",
            "platform": "manylinux_2_17_x86_64",
        },
        "builder_workflow_identity": (
            "promptdriven/pdd/.github/workflows/candidate-wheel.yml@refs/heads/main"
        ),
    }
    artifact = CandidateArtifactProvenance.from_payload(
        {
            **unsigned,
            "signature": {
                "algorithm": "Ed25519",
                "value": authority.sign_bytes(
                    json.dumps(
                        unsigned, sort_keys=True, separators=(",", ":")
                    ).encode()
                ),
            },
        }
    )

    def fake_build_global_certificate(_targets, options, *, signer):
        del signer
        options.lifecycle_result.candidate_artifact.verify(
            options.candidate_artifact_policy,
            expected_source_sha="a" * 40,
        )
        return {"schema_version": 3, "ok": True}

    monkeypatch.setenv("PDD_CANDIDATE_ATTESTATION_ISSUER", authority.issuer)
    monkeypatch.setenv(
        "PDD_CANDIDATE_ATTESTATION_PUBLIC_KEY",
        base64.b64encode(authority.public_key_bytes()).decode("ascii"),
    )
    monkeypatch.setenv(
        "PDD_CANDIDATE_BUILDER_WORKFLOW_IDENTITY",
        unsigned["builder_workflow_identity"],
    )
    monkeypatch.setenv("PDD_CANDIDATE_DEPENDENCY_LOCK_SHA256", lock_sha)
    monkeypatch.setenv("PDD_CANDIDATE_PYTHON_IMPLEMENTATION", "CPython")
    monkeypatch.setenv("PDD_CANDIDATE_PYTHON_VERSION", "3.12.3")
    monkeypatch.setenv("PDD_CANDIDATE_PYTHON_ABI", "cp312")
    monkeypatch.setenv("PDD_CANDIDATE_PYTHON_PLATFORM", "manylinux_2_17_x86_64")
    monkeypatch.setattr(
        "pdd.commands.sync_core._global_targets",
        lambda _repositories, _merge_group, cwd: (
            RepositoryTarget("pdd", cwd, "0" * 40, "a" * 40),
            RepositoryTarget("pdd_cloud", cwd, "1" * 40, "2" * 40),
        ),
    )
    monkeypatch.setattr(
        "pdd.commands.sync_core.run_lifecycle_matrix",
        lambda *_args, **_kwargs: LifecycleResult(
            0,
            0,
            0,
            0,
            0,
            0,
            candidate_wheel_sha256="d" * 64,
            dependency_environment_digest=lock_sha,
            candidate_artifact=artifact,
        ),
    )
    monkeypatch.setattr(
        "pdd.commands.sync_core.checker_identity_from_environment",
        lambda: CheckerIdentity("e" * 64, "refs/tags/v1", "workflow"),
    )
    monkeypatch.setattr(
        "pdd.commands.sync_core.signer_from_environment",
        lambda: authority,
    )
    monkeypatch.setattr(
        "pdd.commands.sync_core.build_global_certificate",
        fake_build_global_certificate,
    )

    args = [
        "certify",
        "--repos",
        "pdd,pdd_cloud",
        "--merge-group",
        "a" * 40,
        "--full-inventory",
        "--run-lifecycle-matrix",
        "--require-nightly-streak",
        "7",
        "--replay-ledger",
        str(tmp_path / "replay"),
    ]
    runner = CliRunner()
    first = runner.invoke(cli, args)
    assert first.exit_code == 0, first.output
    second = runner.invoke(cli, args)
    assert second.exit_code == 1
    assert "candidate attestation is replayed" in second.output


def test_sync_certify_remains_available_as_sync_basename() -> None:
    result = CliRunner().invoke(cli, ["sync", "certify", "--dry-run", "--json"])
    assert result.exit_code == 0, result.output
    assert "global certification requires" not in result.output
    assert "--repos" not in result.output


def test_reviewed_baseline_command_is_registered() -> None:
    result = CliRunner().invoke(cli, ["baseline", "--help"])
    assert result.exit_code == 0, result.output
    assert "--reviewed-by" in result.output
    assert "--reason" in result.output


def test_trusted_validate_command_is_registered() -> None:
    result = CliRunner().invoke(cli, ["validate", "--help"])
    assert result.exit_code == 0, result.output
    assert "--base-ref" in result.output
