"""Tests for canonical v2 fingerprint persistence and migration safety."""

import hashlib
import json
import subprocess
from pathlib import Path, PurePosixPath

import pytest

from pdd.sync_core import (
    ArtifactSnapshot,
    CorruptFingerprintError,
    FingerprintProvenance,
    FingerprintMigrationAction,
    FingerprintMigrationError,
    FingerprintMigrationOptions,
    FingerprintRecord,
    FingerprintStore,
    FingerprintStoreError,
    SemanticStatus,
    UnitId,
    UnitSnapshot,
    plan_fingerprint_migration,
)
from pdd.sync_core.identity import initialize_repository_identity


REPOSITORY_ID = "3b4d7b1c-d6cc-4752-ba93-6b98d1a710e0"
UNIT_ID = UnitId(
    REPOSITORY_ID, PurePosixPath("prompts/widget_python.prompt"), "python"
)


def _store(tmp_path):
    initialize_repository_identity(tmp_path, REPOSITORY_ID)
    return FingerprintStore(tmp_path)


def _record(*, kind="generated", semantic=SemanticStatus.VERIFIED, attestation="att-1"):
    snapshot = UnitSnapshot(
        UNIT_ID,
        (
            ArtifactSnapshot(
                "prompt",
                PurePosixPath("prompts/widget_python.prompt"),
                "prompt-hash",
                "100644",
            ),
            ArtifactSnapshot(
                "test",
                PurePosixPath("tests/test_widget.py"),
                "test-hash",
                "100644",
            ),
            ArtifactSnapshot(
                "test",
                PurePosixPath("tests/test_widget_e2e.py"),
                "e2e-hash",
                "100755",
            ),
        ),
        "manifest-hash",
        "graph-hash",
        "profile-hash",
    )
    provenance = FingerprintProvenance(
        kind,
        "pdd sync widget",
        "transaction-1",
        "head-1",
        "2026-07-10T12:00:00+00:00",
        "pdd-test",
        "reviewer@example.com" if kind == "baseline-reset" else None,
        "reviewed migration" if kind == "baseline-reset" else None,
    )
    return FingerprintRecord(snapshot, 2, 2, provenance, semantic, attestation)


def _git(root: Path, *args: str) -> str:
    return subprocess.run(
        ["git", *args], cwd=root, capture_output=True, text=True, check=True
    ).stdout.strip()


def _migration_repository(tmp_path: Path, *, units: int = 1) -> tuple[Path, str]:
    root = tmp_path / "migration-repo"
    root.mkdir()
    _git(root, "init", "-q")
    _git(root, "config", "user.email", "migration@example.com")
    _git(root, "config", "user.name", "Migration Test")
    initialize_repository_identity(root, REPOSITORY_ID)
    for directory in ("prompts", "src", "docs", "tests"):
        (root / directory).mkdir()
    (root / ".pddrc").write_text("contexts: {}\n")
    (root / "prompts/widget_python.prompt").write_text(
        "REQ-1: widget\n<include>docs/one.md</include>\n"
    )
    (root / "docs/one.md").write_text("<include>docs/two.md</include>\n")
    (root / "docs/two.md").write_text("Recursive contract\n")
    (root / "src/widget.py").write_text("value = 1\n")
    (root / "tests/test_widget.py").write_text("def test_widget(): pass\n")
    modules = [{"filename": "widget_python.prompt", "filepath": "src/widget.py"}]
    profiles = [
        {
            "prompt_path": "prompts/widget_python.prompt",
            "language_id": "python",
            "required_requirement_ids": ["REQ-1"],
            "obligations": [
                {
                    "obligation_id": "widget-tests",
                    "kind": "test",
                    "validator_id": "pytest",
                    "validator_config_digest": hashlib.sha256(b"").hexdigest(),
                    "requirement_ids": ["REQ-1"],
                    "artifact_paths": ["tests/test_widget.py"],
                }
            ],
        }
    ]
    if units == 2:
        (root / "prompts/helper_python.prompt").write_text("REQ-2: helper\n")
        (root / "src/helper.py").write_text("value = 2\n")
        (root / "tests/test_helper.py").write_text("def test_helper(): pass\n")
        modules.append(
            {"filename": "helper_python.prompt", "filepath": "src/helper.py"}
        )
        profiles.append(
            {
                "prompt_path": "prompts/helper_python.prompt",
                "language_id": "python",
                "required_requirement_ids": ["REQ-2"],
                "obligations": [
                    {
                        "obligation_id": "helper-tests",
                        "kind": "test",
                        "validator_id": "pytest",
                        "validator_config_digest": hashlib.sha256(b"").hexdigest(),
                        "requirement_ids": ["REQ-2"],
                        "artifact_paths": ["tests/test_helper.py"],
                    }
                ],
            }
        )
    (root / "architecture.json").write_text(json.dumps(modules))
    (root / ".pdd/verification-profiles.json").write_text(
        json.dumps({"profiles": profiles})
    )
    (root / ".pdd/sync-ownership.json").write_text(
        json.dumps(
            {
                "rules": [
                    {
                        "pattern": "docs/*.md",
                        "inventory": "HUMAN_OWNED",
                        "role": "documentation",
                        "owner": "migration@example.com",
                    },
                    {
                        "pattern": "tests/*.py",
                        "inventory": "HUMAN_OWNED",
                        "role": "test",
                        "owner": "migration@example.com",
                    },
                ]
            }
        )
    )
    _git(root, "add", ".")
    _git(root, "commit", "-q", "-m", "migration fixture")
    return root, _git(root, "rev-parse", "HEAD")


def _review_manifest(
    path: Path,
    *,
    head: str,
    rows: list[dict[str, str]] | None = None,
) -> None:
    path.write_text(
        json.dumps(
            {
                "schema_version": 1,
                "repository_id": REPOSITORY_ID,
                "head_sha": head,
                "units": rows or [],
            }
        )
    )


def _options(
    review: Path,
    head: str,
    *,
    full: bool = False,
    limit: int = 100,
    cursor: str | None = None,
) -> FingerprintMigrationOptions:
    return FingerprintMigrationOptions(
        review,
        head,
        head,
        () if full else (PurePosixPath("prompts/widget_python.prompt"),),
        full,
        limit,
        cursor,
    )


def test_v2_round_trip_preserves_all_artifact_paths_and_modes(tmp_path) -> None:
    store = _store(tmp_path)
    record = _record()
    path = store.write(record)
    assert path.stat().st_mode & 0o777 == 0o644
    assert store.load(UNIT_ID) == record
    assert len(store.load(UNIT_ID).snapshot.artifacts) == 3


def test_corrupt_existing_record_fails_without_rewriting(tmp_path) -> None:
    store = _store(tmp_path)
    path = store.write(_record())
    path.write_text("{not-json", encoding="utf-8")
    before = path.read_bytes()
    with pytest.raises(CorruptFingerprintError):
        store.load(UNIT_ID)
    assert path.read_bytes() == before


def test_required_null_hash_is_rejected(tmp_path) -> None:
    store = _store(tmp_path)
    record = _record()
    missing = ArtifactSnapshot(
        "code", PurePosixPath("src/widget.py"), None, None, required=True
    )
    snapshot = UnitSnapshot(
        record.snapshot.unit_id,
        record.snapshot.artifacts + (missing,),
        record.snapshot.manifest_digest,
        record.snapshot.dependency_snapshot_digest,
        record.snapshot.verification_profile_digest,
    )
    invalid = FingerprintRecord(
        snapshot,
        2,
        2,
        record.provenance,
        record.claimed_semantic_status,
        record.attestation_ref,
    )
    with pytest.raises(FingerprintStoreError, match="null hash or mode"):
        store.write(invalid)


def test_verified_record_requires_attestation(tmp_path) -> None:
    with pytest.raises(FingerprintStoreError, match="requires an attestation"):
        _store(tmp_path).write(_record(attestation=None))


def test_baseline_reset_is_current_but_semantically_unknown(tmp_path) -> None:
    store = _store(tmp_path)
    record = _record(
        kind="baseline-reset", semantic=SemanticStatus.UNKNOWN, attestation=None
    )
    store.write(record)
    assert store.load(UNIT_ID).claimed_semantic_status is SemanticStatus.UNKNOWN
    with pytest.raises(FingerprintStoreError, match="must remain semantic UNKNOWN"):
        store.write(_record(kind="baseline-reset"))


def test_baseline_reset_requires_review_audit_fields(tmp_path) -> None:
    record = _record(
        kind="baseline-reset", semantic=SemanticStatus.UNKNOWN, attestation=None
    )
    provenance = FingerprintProvenance(
        record.provenance.kind,
        record.provenance.command,
        record.provenance.transaction_id,
        record.provenance.git_commit,
        record.provenance.timestamp,
        record.provenance.pdd_version,
    )
    with pytest.raises(FingerprintStoreError, match="reviewer and rationale"):
        _store(tmp_path).write(
            FingerprintRecord(record.snapshot, 2, 2, provenance, SemanticStatus.UNKNOWN, None)
        )


def test_legacy_record_is_readable_but_not_promoted(tmp_path) -> None:
    store = _store(tmp_path)
    legacy_path = tmp_path / ".pdd/meta/widget_python.json"
    legacy_path.parent.mkdir(parents=True, exist_ok=True)
    legacy_path.write_text(json.dumps({"prompt_hash": "legacy"}), encoding="utf-8")
    legacy = store.read_legacy(legacy_path)
    assert legacy.payload["prompt_hash"] == "legacy"
    assert store.load(UNIT_ID) is None


def test_legacy_record_symlink_is_rejected_before_target_read(tmp_path) -> None:
    store = _store(tmp_path)
    outside = tmp_path.parent / "outside-fingerprint.json"
    outside.write_text("{not-json", encoding="utf-8")
    legacy_path = tmp_path / ".pdd/meta/widget_python.json"
    legacy_path.parent.mkdir(parents=True, exist_ok=True)
    try:
        legacy_path.symlink_to(outside)
    except OSError as exc:  # pragma: no cover - platform permission guard
        pytest.skip(f"symlink creation unavailable: {exc}")

    with pytest.raises(FingerprintStoreError, match="not a regular file"):
        store.read_legacy(legacy_path)


def test_embedded_identity_mismatch_is_corrupt(tmp_path) -> None:
    store = _store(tmp_path)
    path = store.write(_record())
    payload = json.loads(path.read_text(encoding="utf-8"))
    payload["unit_id"]["prompt_relpath"] = "prompts/other_python.prompt"
    path.write_text(json.dumps(payload), encoding="utf-8")
    with pytest.raises(CorruptFingerprintError, match="embedded identity"):
        store.load(UNIT_ID)


def test_migration_dry_run_is_zero_write_and_binds_recursive_closure(tmp_path) -> None:
    root, head = _migration_repository(tmp_path)
    review = tmp_path / "review.json"
    _review_manifest(review, head=head)
    before = {
        path.relative_to(root): path.read_bytes()
        for path in root.rglob("*")
        if path.is_file()
    }

    report = plan_fingerprint_migration(root, _options(review, head))

    after = {
        path.relative_to(root): path.read_bytes()
        for path in root.rglob("*")
        if path.is_file()
    }
    assert before == after
    assert report.entries[0].action is FingerprintMigrationAction.BLOCKED
    assert report.entries[0].after_digest is not None
    identities = {
        (item.role, item.relpath.as_posix()) for item in report.entries[0].artifacts
    }
    assert ("config", ".pddrc") in identities
    assert ("architecture", "architecture.json") in identities
    assert ("include", "docs/one.md") in identities
    assert ("include", "docs/two.md") in identities


def test_reviewed_migration_plan_is_deterministic_and_unknown(tmp_path) -> None:
    root, head = _migration_repository(tmp_path)
    review = tmp_path / "review.json"
    _review_manifest(review, head=head)
    discovery = plan_fingerprint_migration(root, _options(review, head))
    digest = discovery.entries[0].after_digest
    assert digest is not None
    _review_manifest(
        review,
        head=head,
        rows=[
            {
                "prompt_path": "prompts/widget_python.prompt",
                "language_id": "python",
                "decision": "REVIEWED",
                "expected_snapshot_digest": digest,
                "reviewed_by": "reviewer@example.com",
                "reason": "prompt, code, tests, config, and architecture agree",
            }
        ],
    )

    first = plan_fingerprint_migration(root, _options(review, head))
    second = plan_fingerprint_migration(root, _options(review, head))

    assert first.as_dict() == second.as_dict()
    assert first.entries[0].action is FingerprintMigrationAction.VALIDATION_REQUIRED
    assert first.entries[0].semantic_status is SemanticStatus.UNKNOWN


def test_equivalent_canonical_record_is_preserved_as_no_op(tmp_path) -> None:
    root, head = _migration_repository(tmp_path)
    review = tmp_path / "review.json"
    _review_manifest(review, head=head)
    # Use the planner's exact snapshot rather than reconstructing closure digests.
    from pdd.sync_core import build_unit_manifest, build_unit_snapshot, load_verification_profiles

    manifest = build_unit_manifest(root, base_ref=head, head_ref=head)
    unit = manifest.managed_units[0]
    profile = load_verification_profiles(root, manifest).for_unit(unit.unit_id)
    assert profile is not None
    snapshot = build_unit_snapshot(root, manifest, unit, profile)
    provenance = FingerprintProvenance(
        "baseline-reset",
        "reviewed migration",
        "migration-1",
        head,
        "2026-07-16T00:00:00+00:00",
        "pdd-test",
        "reviewer@example.com",
        "equivalent canonical state",
    )
    FingerprintStore(root).write(
        FingerprintRecord(snapshot, 2, 2, provenance, SemanticStatus.UNKNOWN, None)
    )
    before = FingerprintStore(root).path_for(unit.unit_id).read_bytes()

    report = plan_fingerprint_migration(root, _options(review, head))

    assert report.entries[0].action is FingerprintMigrationAction.NO_OP
    assert FingerprintStore(root).path_for(unit.unit_id).read_bytes() == before


def test_full_repository_cursor_is_stable(tmp_path) -> None:
    root, head = _migration_repository(tmp_path, units=2)
    review = tmp_path / "review.json"
    _review_manifest(review, head=head)

    first = plan_fingerprint_migration(
        root, _options(review, head, full=True, limit=1)
    )
    second = plan_fingerprint_migration(
        root,
        _options(review, head, full=True, limit=1, cursor=first.next_cursor),
    )

    assert first.next_cursor is not None
    assert len(first.entries) == len(second.entries) == 1
    assert first.entries[0].unit_id != second.entries[0].unit_id
    assert second.next_cursor is None


def test_migration_blocks_missing_config_and_escaping_include(tmp_path) -> None:
    root, _head = _migration_repository(tmp_path)
    (root / ".pddrc").unlink()
    (root / "prompts/widget_python.prompt").write_text(
        "REQ-1: widget\n<include>../../outside.md</include>\n"
    )
    _git(root, "add", ".")
    _git(root, "commit", "-q", "-m", "invalid ownership closure")
    head = _git(root, "rev-parse", "HEAD")
    review = tmp_path / "review.json"
    _review_manifest(review, head=head)

    report = plan_fingerprint_migration(root, _options(review, head))

    assert report.entries[0].action is FingerprintMigrationAction.BLOCKED
    detail = "; ".join(report.entries[0].blockers)
    assert "governing .pddrc" in detail


def test_review_manifest_rejects_stale_head_and_ambiguous_architecture(tmp_path) -> None:
    root, head = _migration_repository(tmp_path)
    review = tmp_path / "review.json"
    _review_manifest(review, head="0" * 40)
    with pytest.raises(FingerprintMigrationError, match="checked HEAD"):
        plan_fingerprint_migration(root, _options(review, head))

    nested = root / "nested"
    nested.mkdir()
    (nested / "architecture.json").write_text(
        json.dumps(
            [{"filename": "widget_python.prompt", "filepath": "widget.py"}]
        )
    )
    (nested / "widget.py").write_text("duplicate = True\n")
    _git(root, "add", ".")
    _git(root, "commit", "-q", "-m", "ambiguous registry")
    ambiguous_head = _git(root, "rev-parse", "HEAD")
    _review_manifest(review, head=ambiguous_head)
    with pytest.raises(FingerprintMigrationError, match="multiple architecture"):
        plan_fingerprint_migration(root, _options(review, ambiguous_head))
