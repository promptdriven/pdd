"""Lifecycle test for trusted canonical reporting through the real WAL."""

import base64
import json
import os
import shutil
import subprocess
import sys
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
    RunnerExecution,
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
    load_attestation,
    load_verification_profiles,
    runner_identity_digest,
)
from pdd.sync_core.identity import initialize_repository_identity
from pdd.sync_core.reporting import module_identity
from pdd.sync_core.types import ObligationEvidence
from pdd.ci_drift_heal import main as ci_drift_heal_main
from pdd.commands.sync_core import baseline as baseline_command
from pdd.commands.sync_core import validate as validate_command
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


def _repository(tmp_path: Path, *, approved_alias: bool = False) -> tuple[Path, str]:
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
    if approved_alias:
        (root / "canonical").mkdir()
        (root / "src/widget.py").rename(root / "canonical/widget.py")
        (root / "src").rmdir()
        (root / "src").symlink_to("canonical", target_is_directory=True)
        (root / ".pdd/sync-aliases.json").write_text(
            json.dumps(
                {
                    "schema_version": 1,
                    "aliases": [
                        {"alias_path": "src", "canonical_path": "canonical"}
                    ],
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


@pytest.fixture
def signed_passing_finalizer_profile(monkeypatch):
    """Provide input-bound signed PASS evidence for finalizer semantics tests."""

    def _run_profile(root, profile, binding, issuance, config):
        assert issuance.signer is SIGNER
        runner_digest = runner_identity_digest(
            profile, root=root, ref=binding.head_sha, config=config
        )
        attestation_binding = AttestationBinding(
            profile.unit_id,
            binding.snapshot_digest,
            profile.profile_digest,
            runner_digest,
            TRUSTED_RUNNER_VERSION,
            binding.base_sha,
            binding.head_sha,
            adapter_identities=config.adapter_identities,
        )
        results = tuple(
            ObligationEvidence(obligation.obligation_id, EvidenceOutcome.PASS)
            for obligation in profile.obligations
        )
        envelope = SIGNER.issue(
            AttestationRequest(
                issuance.attestation_id,
                attestation_binding,
                results,
                issuance.nonce,
                issuance.issued_at,
            )
        )
        executions = tuple(
            RunnerExecution(
                obligation.obligation_id,
                EvidenceOutcome.PASS,
                runner_digest,
                "test finalizer semantic evidence",
            )
            for obligation in profile.obligations
        )
        return envelope, executions

    monkeypatch.setattr("pdd.sync_core.finalize.run_profile", _run_profile)


def _durable_state(root: Path) -> dict[PurePosixPath, bytes]:
    """Capture checker-owned evidence and fingerprints for no-write assertions."""
    return {
        PurePosixPath(path.relative_to(root).as_posix()): path.read_bytes()
        for directory in (root / ".pdd/evidence/v2", root / ".pdd/meta/v2")
        if directory.exists()
        for path in directory.rglob("*")
        if path.is_file()
    }


def _invalid_candidate_profile(root: Path, mutation: str) -> None:
    """Commit one invalid protected-profile transition over the trusted base."""
    profile_path = root / ".pdd/verification-profiles.json"
    payload = json.loads(profile_path.read_text(encoding="utf-8"))
    profile = payload["profiles"][0]
    if mutation == "removed-protected-obligation":
        profile["obligations"] = []
    elif mutation == "changed-requirement":
        profile["required_requirement_ids"] = ["REQ-2"]
        profile["obligations"][0]["requirement_ids"] = ["REQ-2"]
        with (root / "prompts/widget_python.prompt").open("a", encoding="utf-8") as prompt:
            prompt.write("REQ-2: Reject invalid widgets\n")
    else:
        raise ValueError(f"unknown invalid profile mutation: {mutation}")
    profile_path.write_text(json.dumps(payload), encoding="utf-8")
    _git(
        root,
        "add",
        "-u",
        "--",
        ".pdd/verification-profiles.json",
        "prompts/widget_python.prompt",
    )
    _git(root, "commit", "-q", "-m", f"invalid candidate profile: {mutation}")


def test_trusted_transactional_baseline_passes_canonical_predicate(tmp_path) -> None:
    root, commit = _repository(tmp_path)
    _finalize_trusted_baseline(root, commit)
    report = build_canonical_report(root, _options(tmp_path, commit))
    assert report["ok"] is True
    assert report["counts"]["managed_units"] == 1
    assert report["counts"]["trusted_in_sync"] == 1
    assert report["counts"]["unaccounted_tracked_paths"] == 0
    assert report["units"][0]["in_sync"] is True


def test_invalid_profile_reconciliation_cannot_reuse_verified_evidence(
    tmp_path: Path,
) -> None:
    """Invalid protected profiles cannot certify with stale attestations."""
    root, base = _repository(tmp_path)
    _finalize_trusted_baseline(root, base)
    _invalid_candidate_profile(root, "removed-protected-obligation")
    head = _git(root, "rev-parse", "HEAD")

    with patch(
        "pdd.sync_core.reporting._evidence",
        side_effect=AssertionError("invalid profile attempted evidence verification"),
    ):
        report = build_canonical_report(
            root,
            CanonicalReportOptions(
                base_ref=base,
                head_ref=head,
                replay_ledger_path=tmp_path / "external-trust/invalid-profile.json",
                now=NOW,
            ),
        )

    assert report["ok"] is False
    assert report["counts"]["invalid"] == 1
    assert report["counts"]["unknown"] == 1
    assert report["counts"]["trusted_current_evidence"] == 0
    assert report["counts"]["trusted_in_sync"] == 0
    assert report["units"][0]["baseline"] == "CORRUPT"
    assert report["units"][0]["semantic"] == "UNKNOWN"
    assert report["units"][0]["evidence_complete"] is False
    assert report["units"][0]["in_sync"] is False


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


def test_legacy_finalizers_preserve_approved_prompt_alias_identity(
    tmp_path, monkeypatch
) -> None:
    root, _commit = _repository(tmp_path)
    canonical = root / "canonical-prompts"
    canonical.mkdir()
    prompt = root / "prompts/widget_python.prompt"
    prompt.rename(canonical / prompt.name)
    prompt.symlink_to("../canonical-prompts/widget_python.prompt")
    (root / ".pdd/sync-aliases.json").write_text(
        json.dumps(
            {
                "schema_version": 1,
                "aliases": [
                    {
                        "alias_path": "prompts/widget_python.prompt",
                        "canonical_path": "canonical-prompts/widget_python.prompt",
                    }
                ],
            }
        )
    )
    _git(root, "add", ".")
    _git(root, "commit", "-q", "-m", "protected prompt alias")
    head = _git(root, "rev-parse", "HEAD")
    monkeypatch.setenv("PDD_SYNC_PROTECTED_BASE_SHA", head)
    signer = object()

    with patch(
        "pdd.sync_core.finalize.attestation_signer_from_environment",
        return_value=signer,
    ), patch("pdd.sync_core.finalize.finalize_unit") as legacy_finalize:
        save_fingerprint("widget", "python", "generate", {"prompt": prompt})
    legacy_finalize.assert_called_once_with(
        root,
        PurePosixPath("prompts/widget_python.prompt"),
        base_ref=head,
        head_ref="HEAD",
        signer=signer,
    )

    with patch(
        "pdd.sync_core.attestation_signer_from_environment", return_value=signer
    ), patch("pdd.sync_core.finalize_unit") as orchestration_finalize:
        from pdd.sync_orchestration import _save_fingerprint_atomic

        _save_fingerprint_atomic(
            "widget", "python", "generate", {"prompt": prompt}, 0.0, "test"
        )
    orchestration_finalize.assert_called_once_with(
        root,
        PurePosixPath("prompts/widget_python.prompt"),
        base_ref=head,
        head_ref="HEAD",
        signer=signer,
    )


@pytest.mark.parametrize("explicit_protected_base", [False, True])
@pytest.mark.parametrize("bridge", ["operation_log", "orchestration"])
def test_legacy_finalizers_fail_closed_when_prompt_alias_is_live_retargeted(
    tmp_path, monkeypatch, explicit_protected_base, bridge
) -> None:
    """Lexical repository activation must precede a dirty alias resolution."""
    root, _commit = _repository(tmp_path)
    canonical = root / "canonical-prompts"
    canonical.mkdir()
    prompt = root / "prompts/widget_python.prompt"
    prompt.rename(canonical / prompt.name)
    prompt.symlink_to("../canonical-prompts/widget_python.prompt")
    (root / ".pdd/sync-aliases.json").write_text(
        json.dumps(
            {
                "schema_version": 1,
                "aliases": [
                    {
                        "alias_path": "prompts/widget_python.prompt",
                        "canonical_path": "canonical-prompts/widget_python.prompt",
                    }
                ],
            }
        )
    )
    _git(root, "add", ".")
    _git(root, "commit", "-q", "-m", "protected prompt alias")
    protected_base = _git(root, "rev-parse", "HEAD")
    outside = tmp_path / "outside.prompt"
    outside.write_text("untrusted\n")
    prompt.unlink()
    prompt.symlink_to(outside)
    monkeypatch.chdir(root)
    if explicit_protected_base:
        monkeypatch.setenv("PDD_SYNC_PROTECTED_BASE_SHA", protected_base)
    else:
        monkeypatch.delenv("PDD_SYNC_PROTECTED_BASE_SHA", raising=False)

    legacy_path = root / ".pdd/meta/widget_python.json"
    if bridge == "operation_log":
        from pdd.sync_core.finalize import CanonicalFinalizationError

        with pytest.raises(CanonicalFinalizationError):
            save_fingerprint("widget", "python", "generate", {"prompt": prompt})
    else:
        from pdd.sync_orchestration import _save_fingerprint_atomic

        with pytest.raises(RuntimeError):
            _save_fingerprint_atomic(
                "widget", "python", "generate", {"prompt": prompt}, 0.0, "test"
            )

    assert not legacy_path.exists()
    assert not list((root / ".pdd/meta/v2").glob("*.json"))


@pytest.mark.skipif(
    sys.platform == "darwin",
    reason="protected subprocess validation requires Linux process isolation",
)
def test_prompt_alias_uses_canonical_prompt_requirements_and_finalizes(tmp_path) -> None:
    root, _commit = _repository(tmp_path)
    canonical = root / "canonical-prompts"
    canonical.mkdir()
    prompt = root / "prompts/widget_python.prompt"
    prompt.rename(canonical / prompt.name)
    prompt.symlink_to("../canonical-prompts/widget_python.prompt")
    (root / ".pdd/sync-aliases.json").write_text(
        json.dumps(
            {
                "schema_version": 1,
                "aliases": [
                    {
                        "alias_path": "prompts/widget_python.prompt",
                        "canonical_path": "canonical-prompts/widget_python.prompt",
                    }
                ],
            }
        )
    )
    _git(root, "add", ".")
    _git(root, "commit", "-q", "-m", "protected prompt alias")
    commit = _git(root, "rev-parse", "HEAD")

    manifest = build_unit_manifest(root, base_ref=commit, head_ref=commit)
    profiles = load_verification_profiles(root, manifest)
    report = build_canonical_report(root, _options(tmp_path, commit))

    assert not profiles.invalid_reasons
    assert profiles.profiles[0].required_requirement_ids == ("REQ-1",)
    assert report["counts"]["invalid"] == 0
    result = finalize_unit(
        root,
        PurePosixPath("prompts/widget_python.prompt"),
        base_ref=commit,
        head_ref=commit,
        signer=SIGNER,
        replay_ledger_path=tmp_path / "external-trust/prompt-alias.json",
    )
    assert result.transaction.phase.value == "COMMITTED"


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


@pytest.mark.parametrize("mutation", ["delete", "rename"])
@pytest.mark.parametrize("bridge", ["operation_log", "orchestration"])
def test_dirty_worktree_policy_removal_cannot_enable_legacy_mutation(
    tmp_path, monkeypatch, mutation, bridge
) -> None:
    root, _commit = _repository(tmp_path)
    policy = root / ".pdd/sync-policy.json"
    if mutation == "delete":
        policy.unlink()
    else:
        policy.rename(policy.with_suffix(".disabled"))
    monkeypatch.chdir(root)
    monkeypatch.delenv("PDD_SYNC_PROTECTED_BASE_SHA", raising=False)
    paths = {"prompt": root / "prompts/widget_python.prompt"}
    legacy_path = root / ".pdd/meta/widget_python.json"

    if bridge == "operation_log":
        from pdd.sync_core.finalize import CanonicalFinalizationError

        with pytest.raises(CanonicalFinalizationError):
            save_fingerprint("widget", "python", "generate", paths)
    else:
        from pdd.sync_orchestration import _save_fingerprint_atomic

        with pytest.raises(RuntimeError):
            _save_fingerprint_atomic(
                "widget", "python", "generate", paths, 0.0, "test"
            )

    assert canonical_sync_enabled(root) is True
    assert not legacy_path.exists()


@pytest.mark.parametrize("mutation", ["delete", "rename"])
def test_linked_worktree_committed_policy_stays_active(tmp_path, mutation) -> None:
    root, _commit = _repository(tmp_path)
    linked = tmp_path / "linked"
    _git(root, "worktree", "add", "-q", str(linked), "-b", f"linked-{mutation}")
    policy = linked / ".pdd/sync-policy.json"
    if mutation == "delete":
        policy.unlink()
    else:
        policy.rename(policy.with_suffix(".disabled"))
    assert canonical_sync_enabled(linked) is True


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


def test_package_local_compatibility_keeps_qualified_duplicate_module_names(
    tmp_path, monkeypatch
) -> None:
    """Legacy projection uses the same exact prompt-root identity as filtering."""
    canonical = {
        "ok": True,
        "counts": {"managed_units": 2, "trusted_in_sync": 2, "drifted": 0,
                   "unbaselined": 0, "corrupt": 0, "unknown": 0,
                   "conflict": 0, "failed": 0, "invalid": 0},
        "units": [
            {"subject": "pdd/prompts/commands/foo_python.prompt",
             "baseline": "CURRENT", "semantic": "PASS", "in_sync": True,
             "reason": "trusted", "changed_roles": []},
            {"subject": "pdd/prompts/jobs/foo_python.prompt",
             "baseline": "CURRENT", "semantic": "PASS", "in_sync": True,
             "reason": "trusted", "changed_roles": []},
        ],
    }
    monkeypatch.setattr(
        "pdd.continuous_sync.build_canonical_report", lambda *_args, **_kwargs: canonical
    )
    monkeypatch.setattr("pdd.continuous_sync.canonical_sync_enabled", lambda _root: True)

    report = build_compatibility_report(consumer="reconcile", root=tmp_path)

    assert [item["basename"] for item in report["units"]] == [
        "commands/foo", "jobs/foo"
    ]
    assert module_identity(PurePosixPath("pdd/prompts/commands/foo_python.prompt")) == (
        "commands/foo"
    )
    assert module_identity(PurePosixPath("pdd/prompts/jobs/foo_python.prompt")) == (
        "jobs/foo"
    )
    for unsafe_path in (
        "pdd/prompts-archive/commands/foo_python.prompt",
        "prompts/../pdd/prompts/commands/foo_python.prompt",
    ):
        with pytest.raises(ValueError, match="outside supported prompt roots"):
            module_identity(PurePosixPath(unsafe_path))


def test_real_manifest_path_qualified_module_selects_one_duplicate_leaf(tmp_path) -> None:
    root, _commit = _repository(tmp_path)
    for scope in ("commands", "jobs"):
        (root / "prompts" / scope).mkdir()
        (root / "src" / scope).mkdir()
        (root / "prompts" / scope / "foo_python.prompt").write_text(
            f"REQ-{scope}: Build {scope} foo\n"
        )
        (root / "src" / scope / "foo.py").write_text("value = 1\n")
    architecture = json.loads((root / "architecture.json").read_text())
    architecture.extend([
        {"filename": "commands/foo_python.prompt", "filepath": "src/commands/foo.py"},
        {"filename": "jobs/foo_python.prompt", "filepath": "src/jobs/foo.py"},
    ])
    (root / "architecture.json").write_text(json.dumps(architecture))
    _git(root, "add", ".")
    _git(root, "commit", "-q", "-m", "duplicate qualified leaves")
    head = _git(root, "rev-parse", "HEAD")
    options = _options(tmp_path, head)
    report = build_canonical_report(
        root, CanonicalReportOptions(
            base_ref=options.base_ref,
            head_ref=options.head_ref,
            modules=("commands/foo",),
            replay_ledger_path=options.replay_ledger_path,
            now=options.now,
        )
    )
    assert [item["subject"] for item in report["units"]] == [
        "prompts/commands/foo_python.prompt"
    ]


def test_real_manifest_package_prompt_layout_selects_nested_module(tmp_path) -> None:
    """Package-local prompts use the same root-relative module identity."""
    root, _commit = _repository(tmp_path)
    (root / "pdd/prompts/commands").mkdir(parents=True)
    (root / "pdd/commands").mkdir()
    (root / "pdd/prompts/commands/foo_python.prompt").write_text(
        "REQ-package: Build package foo\n"
    )
    (root / "pdd/commands/foo.py").write_text("value = 1\n")
    architecture = json.loads((root / "architecture.json").read_text())
    architecture.append(
        {
            "filename": "commands/foo_python.prompt",
            "filepath": "pdd/commands/foo.py",
        }
    )
    (root / "architecture.json").write_text(json.dumps(architecture))
    _git(root, "add", ".")
    _git(root, "commit", "-q", "-m", "package-local nested prompt")
    head = _git(root, "rev-parse", "HEAD")
    options = _options(tmp_path, head)

    report = build_canonical_report(
        root,
        CanonicalReportOptions(
            base_ref=options.base_ref,
            head_ref=options.head_ref,
            modules=("commands/foo",),
            replay_ledger_path=options.replay_ledger_path,
            now=options.now,
        ),
    )

    assert [item["subject"] for item in report["units"]] == [
        "pdd/prompts/commands/foo_python.prompt"
    ]


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


def test_validate_command_wires_protected_jest_runner_config(
    tmp_path, monkeypatch
) -> None:
    root, commit = _repository(tmp_path)
    external = tmp_path / "trusted-tools" / "jest.py"
    external.parent.mkdir()
    external.write_text("print('trusted jest')\n")
    signer = object()
    monkeypatch.chdir(root)
    with patch(
        "pdd.commands.sync_core.attestation_signer_from_environment",
        return_value=signer,
    ), patch("pdd.commands.sync_core.finalize_unit") as mocked_finalize:
        mocked_finalize.return_value.transaction.transaction_id = "tx-1"
        mocked_finalize.return_value.attestation_id = "att-1"
        mocked_finalize.return_value.fingerprint_path = PurePosixPath(
            ".pdd/meta/v2/fingerprint.json"
        )
        result = CliRunner().invoke(
            validate_command,
            [
                "--module",
                "prompts/widget_python.prompt",
                "--base-ref",
                commit,
                "--jest-command",
                f"{os.sys.executable} {external}",
            ],
        )

    assert result.exit_code == 0, result.output
    call = mocked_finalize.call_args
    assert call.kwargs["signer"] is signer
    assert call.kwargs["config"].jest_command == (os.sys.executable, str(external))


def test_validate_command_wires_protected_vitest_runner_config(
    tmp_path, monkeypatch
) -> None:
    root, commit = _repository(tmp_path)
    toolchain = tmp_path / "trusted-tools"
    external = toolchain / "node_modules/vitest/vitest.py"
    external.parent.mkdir(parents=True)
    external.write_text("print('trusted vitest')\n")
    launcher = toolchain / "bin/node"
    launcher.parent.mkdir(parents=True)
    shutil.copy2(os.sys.executable, launcher)
    launcher.chmod(0o755)
    lockfile = toolchain / "package-lock.json"
    lockfile.write_text("{}\n", encoding="utf-8")
    headers = toolchain / "include/node"
    headers.mkdir(parents=True)
    for name in (
        "node_api.h",
        "node_api_types.h",
        "js_native_api.h",
        "js_native_api_types.h",
    ):
        (headers / name).write_text("\n", encoding="utf-8")
    manifest = toolchain / "manifest.json"
    manifest.write_text(
        json.dumps(
            {
                "version": 1,
                "roles": {
                    "launcher": str(launcher),
                    "entrypoint": str(external),
                    "dependencies": str(toolchain / "node_modules"),
                    "native_runtime": [str(launcher)],
                    "lockfile": str(lockfile),
                    "headers": str(headers),
                },
            }
        ),
        encoding="utf-8",
    )
    signer = object()
    monkeypatch.chdir(root)
    with patch(
        "pdd.commands.sync_core.attestation_signer_from_environment",
        return_value=signer,
    ), patch("pdd.commands.sync_core.finalize_unit") as mocked_finalize:
        mocked_finalize.return_value.transaction.transaction_id = "tx-1"
        mocked_finalize.return_value.attestation_id = "att-1"
        mocked_finalize.return_value.fingerprint_path = PurePosixPath(
            ".pdd/meta/v2/fingerprint.json"
        )
        result = CliRunner().invoke(
            validate_command,
            [
                "--module",
                "prompts/widget_python.prompt",
                "--base-ref",
                commit,
                "--vitest-command",
                f"{launcher} {external}",
                "--vitest-toolchain-manifest",
                str(manifest),
            ],
        )

    assert result.exit_code == 0, result.output
    call = mocked_finalize.call_args
    assert call.kwargs["signer"] is signer
    assert call.kwargs["config"].vitest_command == (str(launcher), str(external))
    assert call.kwargs["config"].vitest_toolchain_manifest == manifest


def test_validate_command_requires_vitest_command_and_manifest_together(
    tmp_path, monkeypatch
) -> None:
    root, commit = _repository(tmp_path)
    external = tmp_path / "trusted-tools/vitest.py"
    external.parent.mkdir()
    external.write_text("print('trusted vitest')\n", encoding="utf-8")
    monkeypatch.chdir(root)

    with patch(
        "pdd.commands.sync_core.attestation_signer_from_environment",
        return_value=object(),
    ):
        result = CliRunner().invoke(
            validate_command,
            [
                "--module",
                "prompts/widget_python.prompt",
                "--base-ref",
                commit,
                "--vitest-command",
                f"{os.sys.executable} {external}",
            ],
        )

    assert result.exit_code != 0
    assert "manifest" in result.output.lower()


def test_trusted_finalizer_commits_artifact_closure_evidence_and_fingerprint(
    tmp_path,
) -> None:
    root, commit = _repository(tmp_path)
    manifest = build_unit_manifest(root, base_ref=commit, head_ref=commit)
    profile = load_verification_profiles(root, manifest).profiles[0]
    unit = manifest.managed_units[0]
    snapshot = build_unit_snapshot(root, manifest, unit, profile)
    result = finalize_unit(
        root,
        PurePosixPath("prompts/widget_python.prompt"),
        base_ref=commit,
        head_ref=commit,
        signer=SIGNER,
        replay_ledger_path=tmp_path / "external-trust/finalizer.json",
    )
    assert result.transaction.phase.value == "COMMITTED"
    envelope = load_attestation(root, result.attestation_id)
    assert envelope.binding.subject == unit.unit_id
    assert envelope.binding.snapshot_digest == snapshot.digest()
    assert envelope.binding.profile_digest == profile.profile_digest
    assert envelope.binding.base_sha == commit
    assert envelope.binding.checked_sha == commit
    assert envelope.binding.tool_version == TRUSTED_RUNNER_VERSION
    assert envelope.binding.runner_digest == runner_identity_digest(
        profile, root=root, ref=commit
    )
    assert envelope.results == (
        ObligationEvidence("pytest", EvidenceOutcome.PASS),
    )
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


def test_trusted_finalizer_rejects_invalid_next_protected_base(tmp_path) -> None:
    """Per-unit finalization cannot bypass invalid protected controls."""
    root, _commit = _repository(tmp_path)
    (root / ".pdd/expected-managed.json").write_text(
        json.dumps(
            {
                "schema_version": 1,
                "units": [
                    {
                        "prompt_path": "prompts/widget_python.prompt",
                        "language_id": "python",
                    }
                ],
            }
        )
    )
    _git(root, "add", ".pdd/expected-managed.json")
    _git(root, "commit", "-q", "-m", "protect managed denominator")
    base = _git(root, "rev-parse", "HEAD")
    _git(
        root,
        "rm",
        ".pdd/expected-managed.json",
        ".pdd/sync-ownership.json",
    )
    _git(root, "commit", "-q", "-m", "delete protected controls")
    head = _git(root, "rev-parse", "HEAD")

    with pytest.raises(
        ValueError,
        match="canonical finalization requires a valid protected candidate manifest",
    ):
        finalize_unit(
            root,
            PurePosixPath("prompts/widget_python.prompt"),
            base_ref=base,
            head_ref=head,
            signer=SIGNER,
            replay_ledger_path=tmp_path / "external-trust/invalid-base.json",
        )


@pytest.mark.parametrize(
    "mutation", ["removed-protected-obligation", "changed-requirement"]
)
def test_trusted_finalizer_rejects_invalid_profile_before_trusted_state(
    tmp_path: Path, mutation: str
) -> None:
    """Invalid profile reconciliation stops before all trust/write boundaries."""
    root, base = _repository(tmp_path)
    _finalize_trusted_baseline(root, base)
    before = _durable_state(root)
    _invalid_candidate_profile(root, mutation)
    head = _git(root, "rev-parse", "HEAD")

    with patch(
        "pdd.sync_core.finalize._reusable_result",
        side_effect=AssertionError("invalid profile attempted evidence reuse"),
    ) as reusable, patch(
        "pdd.sync_core.finalize.run_profile",
        side_effect=AssertionError("invalid profile invoked runner"),
    ) as runner, patch(
        "pdd.sync_core.finalize.TransactionManager",
        side_effect=AssertionError("invalid profile created transaction manager"),
    ) as transaction_manager:
        with pytest.raises(
            ValueError,
            match="canonical finalization requires valid protected verification profiles",
        ):
            finalize_unit(
                root,
                PurePosixPath("prompts/widget_python.prompt"),
                base_ref=base,
                head_ref=head,
                signer=SIGNER,
                replay_ledger_path=tmp_path / f"external-trust/{mutation}.json",
            )

    reusable.assert_not_called()
    runner.assert_not_called()
    transaction_manager.assert_not_called()
    assert _durable_state(root) == before


@pytest.mark.skipif(
    sys.platform == "darwin",
    reason="protected subprocess validation requires Linux process isolation",
)
def test_trusted_finalizer_commits_artifact_through_protected_alias(tmp_path) -> None:
    root, commit = _repository(tmp_path, approved_alias=True)
    report = build_canonical_report(root, _options(tmp_path, commit))
    assert report["counts"]["invalid"] == 0
    assert report["counts"]["unaccounted_tracked_paths"] == 0
    assert ".pdd/sync-aliases.json" not in "\n".join(report["errors"])

    result = finalize_unit(
        root,
        PurePosixPath("prompts/widget_python.prompt"),
        base_ref=commit,
        head_ref=commit,
        signer=SIGNER,
        replay_ledger_path=tmp_path / "external-trust/finalizer-alias.json",
    )
    assert result.transaction.phase.value == "COMMITTED"
    assert (root / "canonical/widget.py").read_text() == "value = 1\n"


def test_approved_alias_target_does_not_blanket_account_candidate_files(
    tmp_path,
) -> None:
    root, commit = _repository(tmp_path, approved_alias=True)
    (root / "canonical/rogue.py").write_text("candidate = 'unowned'\n")
    _git(root, "add", "canonical/rogue.py")
    _git(root, "commit", "-q", "-m", "candidate adds unowned alias-target file")
    head = _git(root, "rev-parse", "HEAD")

    report = build_canonical_report(
        root,
        CanonicalReportOptions(
            base_ref=commit,
            head_ref=head,
            replay_ledger_path=tmp_path / "external-trust/rogue-alias-target.json",
        ),
    )

    assert report["counts"]["invalid"] > 0
    assert "canonical/rogue.py" in "\n".join(report["errors"])


def test_overlapping_alias_policy_cannot_account_rogue_counterparts(
    tmp_path,
) -> None:
    root, _commit = _repository(tmp_path, approved_alias=True)
    (root / "canonical/nested").mkdir()
    (root / "canonical/widget.py").rename(root / "canonical/nested/widget.py")
    (root / "other").mkdir()
    (root / "architecture.json").write_text(
        json.dumps(
            [{"filename": "widget_python.prompt", "filepath": "src/nested/widget.py"}]
        )
    )
    (root / ".pdd/sync-aliases.json").write_text(
        json.dumps(
            {
                "schema_version": 1,
                "aliases": [
                    {"alias_path": "src", "canonical_path": "canonical"},
                    {"alias_path": "src/nested", "canonical_path": "other"},
                ],
            }
        )
    )
    _git(root, "add", ".")
    _git(root, "commit", "-q", "-m", "overlapping protected alias policy")
    base = _git(root, "rev-parse", "HEAD")
    (root / "other/widget.py").write_text("candidate = 'unowned'\n")
    _git(root, "add", "other/widget.py")
    _git(root, "commit", "-q", "-m", "candidate adds alternate alias target")
    head = _git(root, "rev-parse", "HEAD")

    manifest = build_unit_manifest(root, base_ref=base, head_ref=head)

    errors = "\n".join(manifest.invalid_reasons)
    assert manifest.invalid_reasons
    assert "overlap" in errors or "other/widget.py" in errors


def test_chained_aliases_cannot_hide_terminal_canonical_owner(tmp_path) -> None:
    root, _commit = _repository(tmp_path, approved_alias=True)
    (root / "src").unlink()
    (root / "middle").symlink_to("canonical", target_is_directory=True)
    (root / "src").symlink_to("middle", target_is_directory=True)
    (root / "prompts/helper_python.prompt").write_text("REQ-2: Build helper\n")
    (root / "architecture.json").write_text(
        json.dumps(
            [
                {"filename": "widget_python.prompt", "filepath": "src/widget.py"},
                {
                    "filename": "helper_python.prompt",
                    "filepath": "canonical/widget.py",
                },
            ]
        )
    )
    (root / ".pdd/sync-aliases.json").write_text(
        json.dumps(
            {
                "schema_version": 1,
                "aliases": [
                    {"alias_path": "src", "canonical_path": "middle"},
                    {"alias_path": "middle", "canonical_path": "canonical"},
                ],
            }
        )
    )
    _git(root, "add", ".")
    _git(root, "commit", "-q", "-m", "immutable chained alias owners")
    commit = _git(root, "rev-parse", "HEAD")

    report = build_canonical_report(
        root,
        CanonicalReportOptions(
            base_ref=commit,
            head_ref=commit,
            replay_ledger_path=tmp_path / "external-trust/chained-alias.json",
        ),
    )

    assert report["counts"]["invalid"] > 0
    assert "namespace" in "\n".join(report["errors"])


def test_unlisted_canonical_symlink_cannot_hide_terminal_owner(tmp_path) -> None:
    root, _commit = _repository(tmp_path, approved_alias=True)
    (root / "src").unlink()
    (root / "middle").symlink_to("canonical", target_is_directory=True)
    (root / "src").symlink_to("middle", target_is_directory=True)
    (root / "prompts/helper_python.prompt").write_text("REQ-2: Build helper\n")
    (root / "architecture.json").write_text(
        json.dumps(
            [
                {"filename": "widget_python.prompt", "filepath": "src/widget.py"},
                {
                    "filename": "helper_python.prompt",
                    "filepath": "canonical/widget.py",
                },
            ]
        )
    )
    (root / ".pdd/sync-aliases.json").write_text(
        json.dumps(
            {
                "schema_version": 1,
                "aliases": [{"alias_path": "src", "canonical_path": "middle"}],
            }
        )
    )
    ownership = json.loads((root / ".pdd/sync-ownership.json").read_text())
    ownership["rules"].append(
        {
            "pattern": "middle",
            "inventory": "HUMAN_OWNED",
            "role": "compatibility-link",
            "owner": "platform@example.com",
        }
    )
    (root / ".pdd/sync-ownership.json").write_text(json.dumps(ownership))
    _git(root, "add", ".")
    _git(root, "commit", "-q", "-m", "unlisted terminal alias owner")
    commit = _git(root, "rev-parse", "HEAD")

    report = build_canonical_report(
        root,
        CanonicalReportOptions(
            base_ref=commit,
            head_ref=commit,
            replay_ledger_path=tmp_path / "external-trust/unlisted-terminal.json",
        ),
    )

    assert report["counts"]["invalid"] > 0
    errors = "\n".join(report["errors"])
    assert "unapproved" in errors and "middle" in errors


def test_descendant_canonical_symlink_cannot_hide_terminal_owner(tmp_path) -> None:
    root, _commit = _repository(tmp_path, approved_alias=True)
    (root / "canonical/widget.py").unlink()
    (root / "terminal").mkdir()
    (root / "terminal/widget.py").write_text("terminal = True\n")
    (root / "canonical/nested").symlink_to(
        "../terminal", target_is_directory=True
    )
    (root / "prompts/helper_python.prompt").write_text("REQ-2: Build helper\n")
    (root / "architecture.json").write_text(
        json.dumps(
            [
                {
                    "filename": "widget_python.prompt",
                    "filepath": "src/nested/widget.py",
                },
                {
                    "filename": "helper_python.prompt",
                    "filepath": "terminal/widget.py",
                },
            ]
        )
    )
    ownership = json.loads((root / ".pdd/sync-ownership.json").read_text())
    ownership["rules"].append(
        {
            "pattern": "canonical/nested",
            "inventory": "HUMAN_OWNED",
            "role": "compatibility-link",
            "owner": "platform@example.com",
        }
    )
    (root / ".pdd/sync-ownership.json").write_text(json.dumps(ownership))
    _git(root, "add", ".")
    _git(root, "commit", "-q", "-m", "descendant canonical terminal owner")
    commit = _git(root, "rev-parse", "HEAD")

    report = build_canonical_report(
        root,
        CanonicalReportOptions(
            base_ref=commit,
            head_ref=commit,
            replay_ledger_path=tmp_path / "external-trust/descendant-terminal.json",
        ),
    )

    assert report["counts"]["invalid"] > 0
    errors = "\n".join(report["errors"])
    assert "unapproved" in errors and "canonical/nested" in errors


def _alias_collision_repository(tmp_path: Path, *, different_unit: bool) -> tuple[Path, str]:
    root, _commit = _repository(tmp_path, approved_alias=True)
    prompt = "widget_python.prompt"
    if different_unit:
        prompt = "helper_python.prompt"
        (root / "prompts" / prompt).write_text("REQ-2: Build helper\n")
    architecture = json.loads((root / "architecture.json").read_text())
    architecture.append({"filename": prompt, "filepath": "canonical/widget.py"})
    (root / "architecture.json").write_text(json.dumps(architecture))
    _git(root, "add", ".")
    _git(root, "commit", "-q", "-m", "alias ownership collision")
    return root, _git(root, "rev-parse", "HEAD")


@pytest.mark.parametrize("different_unit", [False, True])
def test_baseline_rejects_invalid_alias_manifest_before_writes(
    tmp_path, monkeypatch, different_unit
) -> None:
    root, _commit = _alias_collision_repository(
        tmp_path, different_unit=different_unit
    )
    monkeypatch.chdir(root)
    with patch("pdd.commands.sync_core.TransactionManager.prepare") as prepare:
        result = CliRunner().invoke(
            baseline_command,
            [
                "--module",
                "prompts/widget_python.prompt",
                "--reviewed-by",
                "reviewer@example.com",
                "--reason",
                "collision probe",
            ],
        )

    assert result.exit_code != 0
    assert "manifest is invalid" in result.output
    prepare.assert_not_called()
    assert not (root / ".pdd/meta/v2").exists()


@pytest.mark.parametrize("different_unit", [False, True])
def test_finalizer_rejects_invalid_alias_manifest_before_validation_or_writes(
    tmp_path, different_unit
) -> None:
    root, commit = _alias_collision_repository(
        tmp_path, different_unit=different_unit
    )
    with patch("pdd.sync_core.finalize.run_profile") as run_profile, patch(
        "pdd.sync_core.finalize.TransactionManager.prepare"
    ) as prepare:
        with pytest.raises(
            ValueError,
            match="canonical finalization requires a valid protected candidate manifest",
        ):
            finalize_unit(
                root,
                PurePosixPath("prompts/widget_python.prompt"),
                base_ref=commit,
                head_ref=commit,
                signer=SIGNER,
                replay_ledger_path=tmp_path / "external-trust/invalid-manifest.json",
            )

    run_profile.assert_not_called()
    prepare.assert_not_called()
    assert not (root / ".pdd/meta/v2").exists()
    assert not (root / ".pdd/evidence/v2").exists()


def test_excluded_project_alias_counterpart_is_invalid_before_finalization(
    tmp_path,
) -> None:
    root, _commit = _repository(tmp_path, approved_alias=True)
    ownership = json.loads((root / ".pdd/sync-ownership.json").read_text())
    ownership["rules"].append(
        {
            "pattern": "canonical/**",
            "inventory": "HUMAN_OWNED",
            "role": "excluded-project",
            "owner": "vendor@example.com",
        }
    )
    (root / ".pdd/sync-ownership.json").write_text(json.dumps(ownership))
    _git(root, "add", ".pdd/sync-ownership.json")
    _git(root, "commit", "-q", "-m", "exclude canonical project")
    commit = _git(root, "rev-parse", "HEAD")

    manifest = build_unit_manifest(root, base_ref=commit, head_ref=commit)
    report = build_canonical_report(root, _options(tmp_path, commit))

    errors = "\n".join(manifest.invalid_reasons)
    assert "canonical/widget.py" in errors
    assert "ownership" in errors
    assert report["counts"]["invalid"] > 0
    with patch("pdd.sync_core.finalize.run_profile") as run_profile, patch(
        "pdd.sync_core.finalize.TransactionManager.prepare"
    ) as prepare:
        with pytest.raises(
            ValueError,
            match="canonical finalization requires a valid protected candidate manifest",
        ):
            finalize_unit(
                root,
                PurePosixPath("prompts/widget_python.prompt"),
                base_ref=commit,
                head_ref=commit,
                signer=SIGNER,
                replay_ledger_path=tmp_path / "external-trust/excluded-alias.json",
            )
    run_profile.assert_not_called()
    prepare.assert_not_called()


@pytest.mark.usefixtures("signed_passing_finalizer_profile")
def test_trusted_finalizer_second_run_is_zero_write_no_op(
    tmp_path,
) -> None:
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


@pytest.mark.usefixtures("signed_passing_finalizer_profile")
def test_trusted_finalizer_rejects_dirty_support_before_reuse(
    tmp_path,
) -> None:
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


@pytest.mark.usefixtures("signed_passing_finalizer_profile")
def test_trusted_finalizer_rejects_allowed_state_renamed_to_support(
    tmp_path,
) -> None:
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
