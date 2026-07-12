"""Lifecycle test for trusted canonical reporting through the real WAL."""

import base64
import json
import os
import subprocess
from datetime import datetime, timezone
from pathlib import Path, PurePosixPath
from unittest.mock import patch

from click.testing import CliRunner
import pytest

from pdd.sync_core import (
    AttestationBinding,
    AttestationRequest,
    AttestationSigner,
    CanonicalReportOptions,
    EvidenceOutcome,
    FingerprintProvenance,
    FingerprintRecord,
    FingerprintStore,
    PlannedWrite,
    SemanticStatus,
    TransactionManager,
    TRUSTED_RUNNER_VERSION,
    build_canonical_report,
    build_unit_manifest,
    build_unit_snapshot,
    encode_attestation,
    encode_fingerprint,
    evidence_relpath,
    finalize_unit,
    load_verification_profiles,
    runner_identity_digest,
)
from pdd.sync_core.identity import initialize_repository_identity
from pdd.sync_core.types import ObligationEvidence
from pdd.ci_drift_heal import main as ci_drift_heal_main
from pdd.commands.sync_core import baseline as baseline_command
from pdd.continuous_sync import build_report as build_compatibility_report
from pdd.continuous_sync import (
    canonical_sync_enabled,
    project_root,
    repository_root,
)
from pdd.operation_log import save_fingerprint


REPOSITORY_ID = "3b4d7b1c-d6cc-4752-ba93-6b98d1a710e0"
NOW = datetime(2026, 7, 10, 12, 0, tzinfo=timezone.utc)
SIGNER = AttestationSigner("trusted-ci", b"r" * 32)


def _git(root: Path, *args: str) -> str:
    return subprocess.run(
        ["git", *args], cwd=root, capture_output=True, text=True, check=True
    ).stdout.strip()


def _repository(tmp_path: Path) -> tuple[Path, str]:
    root = tmp_path / "repo"
    root.mkdir()
    _git(root, "init", "-q")
    _git(root, "config", "user.email", "report@example.com")
    _git(root, "config", "user.name", "Report Test")
    initialize_repository_identity(root, REPOSITORY_ID)
    for directory in ("prompts", "src", "docs", "tests"):
        (root / directory).mkdir()
    (root / "prompts/widget_python.prompt").write_text(
        "REQ-1: Build widget\n<include>docs/widget.md</include>\n"
    )
    (root / "docs/widget.md").write_text("Widget contract\n")
    (root / "src/widget.py").write_text("value = 1\n")
    (root / "tests/test_widget.py").write_text("def test_widget(): assert True\n")
    (root / "architecture.json").write_text(
        json.dumps(
            [{"filename": "widget_python.prompt", "filepath": "src/widget.py"}]
        )
    )
    (root / ".pdd/sync-ownership.json").write_text(
        json.dumps(
            {
                "rules": [
                    {
                        "pattern": "docs/widget.md",
                        "inventory": "HUMAN_OWNED",
                        "role": "documentation",
                        "owner": "docs@example.com",
                    },
                    {
                        "pattern": "tests/test_widget.py",
                        "inventory": "HUMAN_OWNED",
                        "role": "test",
                        "owner": "quality@example.com",
                    },
                ]
            }
        )
    )
    (root / ".pdd/sync-policy.json").write_text(
        json.dumps({"schema_version": 1, "enforcement": "active"})
    )
    (root / ".pdd/verification-profiles.json").write_text(
        json.dumps(
            {
                "profiles": [
                    {
                        "prompt_path": "prompts/widget_python.prompt",
                        "language_id": "python",
                        "required_requirement_ids": ["REQ-1"],
                        "obligations": [
                            {
                                "obligation_id": "pytest",
                                "kind": "test",
                                "validator_id": "pytest",
                                "validator_config_digest": "e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855",
                                "requirement_ids": ["REQ-1"],
                                "artifact_paths": ["tests/test_widget.py"],
                            }
                        ],
                    }
                ]
            }
        )
    )
    (root / ".pdd/attestation-trust.json").write_text(
        json.dumps(
            {
                "issuers": [
                    {
                        "issuer_id": "trusted-ci",
                        "public_key": base64.b64encode(
                            SIGNER.public_key_bytes()
                        ).decode("ascii"),
                    }
                ],
                "revoked_issuers": [],
                "revoked_attestations": [],
            }
        )
    )
    _git(root, "add", ".")
    _git(root, "commit", "-q", "-m", "managed baseline")
    return root, _git(root, "rev-parse", "HEAD")


def _finalize_trusted_baseline(root: Path, commit: str) -> None:
    manifest = build_unit_manifest(root, base_ref=commit, head_ref=commit)
    profile = load_verification_profiles(root, manifest).profiles[0]
    unit = manifest.managed_units[0]
    snapshot = build_unit_snapshot(root, manifest, unit, profile)
    binding = AttestationBinding(
        unit.unit_id,
        snapshot.digest(),
        profile.profile_digest,
        runner_identity_digest(profile, root=root, ref=commit),
        TRUSTED_RUNNER_VERSION,
        commit,
        commit,
    )
    envelope = SIGNER.issue(
        AttestationRequest(
            "attestation-widget-1",
            binding,
            (ObligationEvidence("pytest", EvidenceOutcome.PASS),),
            "nonce-widget-1",
            NOW,
        )
    )
    provenance = FingerprintProvenance(
        "generated",
        "pdd sync widget",
        "transaction-widget-1",
        commit,
        NOW.isoformat(),
        "pdd-test",
    )
    record = FingerprintRecord(
        snapshot,
        2,
        2,
        provenance,
        SemanticStatus.VERIFIED,
        envelope.attestation_id,
    )
    store = FingerprintStore(root)
    fingerprint_path = store.path_for(unit.unit_id).relative_to(root)
    writes = (
        PlannedWrite(
            evidence_relpath(envelope.attestation_id),
            encode_attestation(envelope),
            "100644",
        ),
        PlannedWrite(
            PurePosixPath(fingerprint_path.as_posix()),
            encode_fingerprint(record),
            "100644",
        ),
    )
    manager = TransactionManager(root)
    manager.prepare("transaction-widget-1", writes)
    manager.commit("transaction-widget-1")


def _options(tmp_path: Path, commit: str) -> CanonicalReportOptions:
    return CanonicalReportOptions(
        base_ref=commit,
        head_ref=commit,
        replay_ledger_path=tmp_path / "external-trust/replay.json",
        now=NOW,
    )


def test_trusted_transactional_baseline_passes_canonical_predicate(tmp_path) -> None:
    root, commit = _repository(tmp_path)
    _finalize_trusted_baseline(root, commit)
    report = build_canonical_report(root, _options(tmp_path, commit))
    assert report["ok"] is True
    assert report["counts"]["managed_units"] == 1
    assert report["counts"]["trusted_in_sync"] == 1
    assert report["counts"]["unaccounted_tracked_paths"] == 0
    assert report["units"][0]["in_sync"] is True


def test_managed_waiver_is_counted_and_blocks_certificate_predicate(tmp_path) -> None:
    root, _commit = _repository(tmp_path)
    (root / ".pdd/sync-waivers.json").write_text(
        json.dumps(
            {
                "waivers": [
                    {
                        "waiver_id": "SYNC-1",
                        "prompt_path": "prompts/widget_python.prompt",
                        "snapshot_digest": "a" * 64,
                        "approved_by": "reviewer@example.com",
                        "reason": "temporary reviewed exception",
                        "expires_at": "2026-08-01T00:00:00+00:00",
                    }
                ]
            }
        )
    )
    _git(root, "add", ".pdd/sync-waivers.json")
    _git(root, "commit", "-q", "-m", "protected waiver")
    commit = _git(root, "rev-parse", "HEAD")
    report = build_canonical_report(root, _options(tmp_path, commit))
    assert report["counts"]["managed_waivers"] == 1
    assert report["ok"] is False


def test_candidate_cannot_delete_protected_sync_waiver(tmp_path) -> None:
    root, _commit = _repository(tmp_path)
    waiver = root / ".pdd/sync-waivers.json"
    waiver.write_text(
        json.dumps(
            {
                "waivers": [
                    {
                        "waiver_id": "SYNC-1",
                        "prompt_path": "prompts/widget_python.prompt",
                        "snapshot_digest": "b" * 64,
                        "approved_by": "reviewer@example.com",
                        "reason": "protected exception",
                        "expires_at": "2026-08-01T00:00:00+00:00",
                    }
                ]
            }
        )
    )
    _git(root, "add", ".pdd/sync-waivers.json")
    _git(root, "commit", "-q", "-m", "protected waiver")
    base = _git(root, "rev-parse", "HEAD")
    waiver.unlink()
    _git(root, "add", ".pdd/sync-waivers.json")
    _git(root, "commit", "-q", "-m", "remove waiver")
    head = _git(root, "rev-parse", "HEAD")
    options = CanonicalReportOptions(
        base_ref=base,
        head_ref=head,
        replay_ledger_path=tmp_path / "external-trust/removal.json",
        now=NOW,
    )
    report = build_canonical_report(root, options)
    assert report["counts"]["managed_waivers"] == 1
    assert any("removed protected waiver" in item for item in report["errors"])


def test_nested_config_cannot_bypass_repository_canonical_finalizer(
    tmp_path, monkeypatch
) -> None:
    root, _commit = _repository(tmp_path)
    nested = root / "nested"
    prompts = nested / "prompts"
    prompts.mkdir(parents=True)
    (nested / ".pddrc").write_text("[pdd]\n")
    prompt = prompts / "worker_python.prompt"
    prompt.write_text("REQ-1: Build nested worker\n")
    _git(root, "add", "nested")
    _git(root, "commit", "-q", "-m", "nested project")
    head = _git(root, "rev-parse", "HEAD")
    monkeypatch.setenv("PDD_SYNC_PROTECTED_BASE_SHA", head)

    assert project_root(prompt) == nested
    assert repository_root(prompt) == root
    assert canonical_sync_enabled(nested) is True
    signer = object()
    with patch(
        "pdd.sync_core.finalize.attestation_signer_from_environment",
        return_value=signer,
    ), patch("pdd.sync_core.finalize.finalize_unit") as mocked_finalize:
        save_fingerprint(
            "worker",
            "python",
            "generate",
            {"prompt": prompt},
        )
    mocked_finalize.assert_called_once_with(
        root,
        PurePosixPath("nested/prompts/worker_python.prompt"),
        base_ref=head,
        head_ref="HEAD",
        signer=signer,
    )


def test_repository_identity_does_not_activate_enforcement_without_policy(
    tmp_path,
) -> None:
    root, _commit = _repository(tmp_path)
    policy = root / ".pdd/sync-policy.json"
    policy.unlink()
    _git(root, "add", "-u", ".pdd/sync-policy.json")
    _git(root, "commit", "-q", "-m", "remove activation policy")

    assert canonical_sync_enabled(root) is False


def test_committed_policy_stays_active_when_worktree_policy_is_deleted(tmp_path) -> None:
    root, _commit = _repository(tmp_path)
    (root / ".pdd/sync-policy.json").unlink()
    assert canonical_sync_enabled(root) is True


def test_policy_free_linked_worktree_avoids_git_subprocess(tmp_path, monkeypatch) -> None:
    (tmp_path / ".git").write_text("gitdir: /protected/main/.git/worktrees/unit\n")

    def unexpected_subprocess(*_args, **_kwargs):
        raise AssertionError("legacy worktree must not enter protected Git lookup")

    monkeypatch.setattr("pdd.continuous_sync.subprocess.run", unexpected_subprocess)
    assert canonical_sync_enabled(tmp_path) is False


def test_scoped_canonical_compatibility_uses_selected_counts_and_qualified_names(
    tmp_path, monkeypatch
) -> None:
    canonical = {
        "ok": False,
        "counts": {"managed_units": 2, "trusted_in_sync": 1, "drifted": 0,
                   "unbaselined": 0, "corrupt": 0, "unknown": 0,
                   "conflict": 0, "failed": 0, "invalid": 0},
        "units": [{"subject": "prompts/commands/foo_python.prompt",
                   "baseline": "CURRENT", "semantic": "PASS", "in_sync": True,
                   "reason": "trusted", "changed_roles": []}],
    }
    monkeypatch.setattr(
        "pdd.continuous_sync.build_canonical_report", lambda *_args, **_kwargs: canonical
    )
    monkeypatch.setattr("pdd.continuous_sync.canonical_sync_enabled", lambda _root: True)
    report = build_compatibility_report(
        consumer="reconcile", root=tmp_path, modules=("commands/foo",)
    )
    assert report["ok"] is True
    assert report["summary"]["total"] == 1
    assert report["units"][0]["basename"] == "commands/foo"


@pytest.mark.parametrize("protected_ref", ["missing-ref", "HEAD"])
def test_explicit_protected_mode_invalid_trust_input_fails_closed(
    tmp_path, monkeypatch, protected_ref
) -> None:
    root, _commit = _repository(tmp_path)
    if protected_ref == "HEAD":
        (root / ".pdd/sync-policy.json").write_text("{not-json")
        _git(root, "add", ".pdd/sync-policy.json")
        _git(root, "commit", "-q", "-m", "malformed protected policy")
    monkeypatch.setenv("PDD_SYNC_PROTECTED_BASE_SHA", protected_ref)
    with pytest.raises(ValueError, match="protected"):
        canonical_sync_enabled(root)


def test_code_drift_cannot_reuse_old_attestation(tmp_path) -> None:
    root, commit = _repository(tmp_path)
    _finalize_trusted_baseline(root, commit)
    (root / "src/widget.py").write_text("value = 2\n")
    report = build_canonical_report(root, _options(tmp_path, commit))
    assert report["ok"] is False
    assert report["counts"]["drifted"] == 1
    assert report["counts"]["trusted_in_sync"] == 0


def test_forged_candidate_evidence_is_rejected(tmp_path) -> None:
    root, commit = _repository(tmp_path)
    _finalize_trusted_baseline(root, commit)
    evidence_path = root.joinpath(*evidence_relpath("attestation-widget-1").parts)
    payload = json.loads(evidence_path.read_text())
    payload["binding"]["checked_sha"] = "forged-head"
    evidence_path.write_text(json.dumps(payload))
    report = build_canonical_report(root, _options(tmp_path, commit))
    assert report["ok"] is False
    assert report["counts"]["failed"] == 1
    assert "signature is invalid" in report["units"][0]["reason"]


def test_live_ci_uses_canonical_gate_and_fails_on_drift(tmp_path, monkeypatch) -> None:
    root, commit = _repository(tmp_path)
    _finalize_trusted_baseline(root, commit)
    monkeypatch.chdir(root)
    monkeypatch.setenv(
        "PDD_ATTESTATION_REPLAY_LEDGER",
        str(tmp_path / "external-trust/replay.json"),
    )
    monkeypatch.setattr("pdd.sync_core.reporting.datetime", type("Clock", (), {"now": staticmethod(lambda _tz: NOW)}))
    assert ci_drift_heal_main(skip_ci=True) == 0
    (root / "src/widget.py").write_text("value = 3\n")
    assert ci_drift_heal_main(skip_ci=True) == 1


def test_legacy_report_consumer_cannot_self_certify_matching_v1_hashes(
    tmp_path, monkeypatch
) -> None:
    root = tmp_path / "canonical"
    (root / ".pdd").mkdir(parents=True)
    (root / ".pdd/repository-id").write_text(REPOSITORY_ID + "\n")
    canonical = {
        "ok": False,
        "project_root": str(root),
        "counts": {
            "managed_units": 1,
            "trusted_in_sync": 0,
            "drifted": 0,
            "unbaselined": 0,
            "corrupt": 0,
            "unknown": 1,
            "conflict": 0,
            "failed": 0,
            "invalid": 0,
        },
        "units": [
            {
                "subject": "prompts/widget_python.prompt",
                "baseline": "CURRENT",
                "semantic": "UNKNOWN",
                "in_sync": False,
                "reason": "legacy fingerprint has no trusted evidence",
                "changed_roles": [],
            }
        ],
    }
    monkeypatch.setattr(
        "pdd.continuous_sync.build_canonical_report", lambda *_a, **_k: canonical
    )
    monkeypatch.setattr("pdd.continuous_sync.canonical_sync_enabled", lambda _root: True)
    report = build_compatibility_report(consumer="sync-dry-run", root=root)
    assert report["ok"] is False
    assert report["summary"]["synced"] == 0
    assert report["summary"]["failures"] == 1
    assert report["units"][0]["classification"] == "FAILURE"


def test_reviewed_baseline_command_records_current_unknown(tmp_path, monkeypatch) -> None:
    root, commit = _repository(tmp_path)
    monkeypatch.chdir(root)
    result = CliRunner().invoke(
        baseline_command,
        [
            "--module",
            "prompts/widget_python.prompt",
            "--reviewed-by",
            "reviewer@example.com",
            "--reason",
            "adopt existing bytes before trusted validation",
        ],
    )
    assert result.exit_code == 0, result.output
    report = build_canonical_report(root, _options(tmp_path, commit))
    assert report["ok"] is False
    assert report["units"][0]["baseline"] == "CURRENT"
    assert report["units"][0]["semantic"] == "UNKNOWN"
    assert report["counts"]["trusted_in_sync"] == 0


def test_trusted_finalizer_commits_artifact_closure_evidence_and_fingerprint(
    tmp_path,
) -> None:
    root, commit = _repository(tmp_path)
    result = finalize_unit(
        root,
        PurePosixPath("prompts/widget_python.prompt"),
        base_ref=commit,
        head_ref=commit,
        signer=SIGNER,
        replay_ledger_path=tmp_path / "external-trust/finalizer.json",
    )
    assert result.transaction.phase.value == "COMMITTED"
    _git(root, "add", ".pdd/meta/v2", ".pdd/evidence/v2")
    _git(root, "commit", "-q", "-m", "commit trusted sync evidence")
    finalized_commit = _git(root, "rev-parse", "HEAD")
    options = CanonicalReportOptions(
        base_ref=commit,
        head_ref=finalized_commit,
        replay_ledger_path=tmp_path / "external-trust/finalize-replay.json",
    )
    report = build_canonical_report(root, options)
    assert report["ok"] is True
    assert report["counts"]["trusted_in_sync"] == 1


def test_trusted_finalizer_second_run_is_zero_write_no_op(tmp_path) -> None:
    root, commit = _repository(tmp_path)
    replay = tmp_path / "external-trust/idempotency.json"
    first = finalize_unit(
        root,
        PurePosixPath("prompts/widget_python.prompt"),
        base_ref=commit,
        head_ref=commit,
        signer=SIGNER,
        replay_ledger_path=replay,
    )
    state_roots = (root / ".pdd/meta/v2", root / ".pdd/evidence/v2")
    before = {
        path.relative_to(root): path.read_bytes()
        for state_root in state_roots
        for path in state_root.rglob("*")
        if path.is_file()
    }
    with patch("pdd.sync_core.finalize.run_profile") as run_profile_mock:
        second = finalize_unit(
            root,
            PurePosixPath("prompts/widget_python.prompt"),
            base_ref=commit,
            head_ref=commit,
            signer=SIGNER,
            replay_ledger_path=replay,
        )
    after = {
        path.relative_to(root): path.read_bytes()
        for state_root in state_roots
        for path in state_root.rglob("*")
        if path.is_file()
    }
    assert second.transaction.no_op is True
    assert second.attestation_id == first.attestation_id
    assert before == after
    run_profile_mock.assert_not_called()
    metrics_path = os.environ.get("PDD_LIFECYCLE_METRICS_PATH")
    if metrics_path:
        path = Path(metrics_path)
        payload = json.loads(path.read_text()) if path.exists() else {}
        payload["post_repair_second_run_writes"] = (
            len(second.transaction.changed_paths) + int(before != after)
        )
        path.write_text(json.dumps(payload, sort_keys=True))


def test_trusted_finalizer_rejects_dirty_support_before_reuse(tmp_path) -> None:
    root, commit = _repository(tmp_path)
    replay = tmp_path / "external-trust/dirty-reuse.json"
    finalize_unit(
        root, PurePosixPath("prompts/widget_python.prompt"), base_ref=commit,
        head_ref=commit, signer=SIGNER, replay_ledger_path=replay,
    )
    (root / "conftest.py").write_text("pytest_plugins = []\n")
    with pytest.raises(ValueError, match="completely clean checkout"):
        finalize_unit(
            root, PurePosixPath("prompts/widget_python.prompt"), base_ref=commit,
            head_ref=commit, signer=SIGNER, replay_ledger_path=replay,
        )


def test_trusted_finalizer_rejects_allowed_state_renamed_to_support(tmp_path) -> None:
    root, commit = _repository(tmp_path)
    replay = tmp_path / "external-trust/rename-reuse.json"
    finalize_unit(
        root, PurePosixPath("prompts/widget_python.prompt"), base_ref=commit,
        head_ref=commit, signer=SIGNER, replay_ledger_path=replay,
    )
    evidence = next((root / ".pdd/evidence/v2").glob("*.json"))
    subprocess.run(["git", "add", evidence], cwd=root, check=True)
    subprocess.run(["git", "commit", "-q", "-m", "durable evidence"], cwd=root, check=True)
    evidence.rename(root / "conftest.py")
    with pytest.raises(ValueError, match="completely clean checkout"):
        finalize_unit(
            root, PurePosixPath("prompts/widget_python.prompt"), base_ref=commit,
            head_ref=_git(root, "rev-parse", "HEAD"), signer=SIGNER,
            replay_ledger_path=replay,
        )


@pytest.mark.parametrize(
    ("edits", "semantic", "changed_roles"),
    [
        (("prompt",), "UNKNOWN", ["prompt"]),
        (("code",), "UNKNOWN", ["code"]),
        (("test",), "UNKNOWN", ["test"]),
        (("include",), "UNKNOWN", ["include"]),
        (("prompt", "code"), "CONFLICT", ["code", "prompt"]),
    ],
)
def test_canonical_source_edit_matrix_detects_each_channel(
    tmp_path, edits, semantic, changed_roles
) -> None:
    root, commit = _repository(tmp_path)
    _finalize_trusted_baseline(root, commit)
    paths = {
        "prompt": root / "prompts/widget_python.prompt",
        "code": root / "src/widget.py",
        "test": root / "tests/test_widget.py",
        "include": root / "docs/widget.md",
    }
    for role in edits:
        with paths[role].open("a", encoding="utf-8") as handle:
            handle.write(f"# changed {role}\n")
    report = build_canonical_report(root, _options(tmp_path, commit))
    assert report["ok"] is False
    assert report["units"][0]["baseline"] == "DRIFTED"
    assert report["units"][0]["semantic"] == semantic
    assert report["units"][0]["changed_roles"] == changed_roles


def test_trusted_finalizer_rejects_test_time_artifact_mutation(tmp_path) -> None:
    root, _commit = _repository(tmp_path)
    source = root / "src/widget.py"
    original_source = source.read_bytes()
    (root / "tests/test_widget.py").write_text(
        "from pathlib import Path\n"
        "def test_widget():\n"
        "    Path('src/widget.py').write_text('mutated = True\\n')\n"
    )
    _git(root, "add", "tests/test_widget.py")
    _git(root, "commit", "-q", "-m", "protected mutation probe")
    head = _git(root, "rev-parse", "HEAD")
    with pytest.raises(ValueError, match="trusted validation did not pass"):
        finalize_unit(
            root,
            PurePosixPath("prompts/widget_python.prompt"),
            base_ref=head,
            head_ref=head,
            signer=SIGNER,
            replay_ledger_path=tmp_path / "external-trust/mutation.json",
        )
    assert not (root / ".pdd/evidence/v2").exists()
    assert source.read_bytes() == original_source
