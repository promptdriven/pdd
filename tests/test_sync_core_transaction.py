"""Crash, CAS, mode, and recovery tests for the durable transaction WAL."""

import json
import os
import subprocess
from pathlib import PurePosixPath
from unittest.mock import patch

from click.testing import CliRunner
import pytest

from pdd.cli import cli
from pdd.sync_core import (
    PlannedWrite,
    TransactionConflict,
    TransactionError,
    TransactionManager,
    TransactionPhase,
)


def _git(root, *args: str) -> str:
    return subprocess.run(
        ["git", *args], cwd=root, capture_output=True, text=True, check=True
    ).stdout.strip()


def _writes():
    return (
        PlannedWrite(PurePosixPath("src/widget.py"), b"value = 2\n", "100755"),
        PlannedWrite(PurePosixPath(".pdd/evidence/widget.json"), b"{}\n", "100644"),
        PlannedWrite(PurePosixPath(".pdd/meta/v2/widget.json"), b"{}\n", "100644"),
    )


def test_success_commits_artifact_evidence_and_fingerprint_together(tmp_path) -> None:
    (tmp_path / "src").mkdir()
    (tmp_path / "src/widget.py").write_text("value = 1\n")
    manager = TransactionManager(tmp_path)
    prepared = manager.prepare("tx-success", _writes())
    assert prepared.phase is TransactionPhase.PREPARED
    assert (tmp_path / "src/widget.py").read_text() == "value = 1\n"
    result = manager.commit("tx-success")
    assert result.phase is TransactionPhase.COMMITTED
    assert (tmp_path / "src/widget.py").read_text() == "value = 2\n"
    assert (tmp_path / "src/widget.py").stat().st_mode & 0o777 == 0o755
    assert (tmp_path / ".pdd/evidence/widget.json").exists()
    assert (tmp_path / ".pdd/meta/v2/widget.json").exists()
    assert manager.incomplete() == ()


def test_identical_plan_is_a_no_op_without_journal(tmp_path) -> None:
    for write in _writes():
        path = tmp_path.joinpath(*write.relpath.parts)
        path.parent.mkdir(parents=True, exist_ok=True)
        path.write_bytes(write.content)
        os.chmod(path, 0o755 if write.git_mode == "100755" else 0o644)
    result = TransactionManager(tmp_path).prepare("tx-noop", _writes())
    assert result.no_op is True
    assert not (tmp_path / ".pdd/transactions/tx-noop").exists()


def test_external_edit_after_prepare_is_conflict_without_writes(tmp_path) -> None:
    (tmp_path / "src").mkdir()
    target = tmp_path / "src/widget.py"
    target.write_text("value = 1\n")
    manager = TransactionManager(tmp_path)
    manager.prepare("tx-conflict", _writes())
    target.write_text("external = True\n")
    with pytest.raises(TransactionConflict, match="destination changed"):
        manager.commit("tx-conflict")
    assert target.read_text() == "external = True\n"
    assert not (tmp_path / ".pdd/evidence/widget.json").exists()


def test_external_edit_after_first_install_prevents_commit(tmp_path) -> None:
    (tmp_path / "src").mkdir()
    target = tmp_path / "src/widget.py"
    target.write_text("value = 1\n")
    manager = TransactionManager(tmp_path)
    manager.prepare("tx-post-install-race", _writes())

    def race(event):
        if event == "after_install:0":
            target.write_text("external = True\n")

    with pytest.raises(TransactionConflict, match="rollback conflict"):
        manager.commit("tx-post-install-race", crash_hook=race)
    assert target.read_text() == "external = True\n"


def test_rollback_preserves_external_edit_after_install(tmp_path, monkeypatch) -> None:
    (tmp_path / "src").mkdir()
    target = tmp_path / "src/widget.py"
    target.write_text("value = 1\n")
    manager = TransactionManager(tmp_path)
    manager.prepare("tx-rollback-race", _writes())
    original_install = manager._install_entry
    calls = 0

    def failing_install(transaction_dir, entry):
        nonlocal calls
        calls += 1
        if calls == 2:
            raise TransactionError("later install failed")
        original_install(transaction_dir, entry)

    monkeypatch.setattr(manager, "_install_entry", failing_install)

    def race(event):
        if event == "after_install:0":
            target.write_text("external = True\n")

    with pytest.raises(TransactionConflict, match="rollback conflict"):
        manager.commit("tx-rollback-race", crash_hook=race)
    assert target.read_text() == "external = True\n"


@pytest.mark.parametrize("crash_event", ["after_committing", "after_install:0", "after_install:1"])
def test_process_death_recovers_committing_transaction(tmp_path, crash_event) -> None:
    (tmp_path / "src").mkdir()
    (tmp_path / "src/widget.py").write_text("value = 1\n")
    manager = TransactionManager(tmp_path)
    manager.prepare("tx-crash", _writes())

    def crash(event):
        if event == crash_event:
            raise SystemExit("simulated process death")

    with pytest.raises(SystemExit):
        manager.commit("tx-crash", crash_hook=crash)
    assert manager.incomplete() == ("tx-crash",)
    recovered = manager.recover("tx-crash")
    assert recovered.phase is TransactionPhase.COMMITTED
    assert (tmp_path / "src/widget.py").read_text() == "value = 2\n"
    assert (tmp_path / ".pdd/evidence/widget.json").exists()
    assert (tmp_path / ".pdd/meta/v2/widget.json").exists()
    assert manager.recover("tx-crash").no_op is True


def test_recovery_race_cannot_false_commit(tmp_path, monkeypatch) -> None:
    (tmp_path / "src").mkdir()
    target = tmp_path / "src/widget.py"
    target.write_text("value = 1\n")
    manager = TransactionManager(tmp_path)
    manager.prepare("tx-recovery-race", _writes())

    def crash(event):
        if event == "after_committing":
            raise SystemExit

    with pytest.raises(SystemExit):
        manager.commit("tx-recovery-race", crash_hook=crash)
    original = manager._install_entry
    calls = 0

    def raced_install(transaction_dir, entry):
        nonlocal calls
        original(transaction_dir, entry)
        calls += 1
        if calls == 1:
            target.write_text("external = True\n")

    monkeypatch.setattr(manager, "_install_entry", raced_install)
    with pytest.raises(TransactionConflict, match="rollback conflict"):
        manager.recover("tx-recovery-race")
    assert target.read_text() == "external = True\n"
    assert manager.incomplete() == ("tx-recovery-race",)


def test_prepared_transaction_recovers_by_rollback_without_destination_write(tmp_path) -> None:
    (tmp_path / "src").mkdir()
    target = tmp_path / "src/widget.py"
    target.write_text("value = 1\n")
    manager = TransactionManager(tmp_path)
    manager.prepare("tx-prepared", _writes())
    assert manager.recover("tx-prepared").phase is TransactionPhase.ROLLED_BACK
    assert target.read_text() == "value = 1\n"
    assert manager.incomplete() == ()


def test_corrupt_prepared_blob_never_commits(tmp_path) -> None:
    (tmp_path / "src").mkdir()
    target = tmp_path / "src/widget.py"
    target.write_text("value = 1\n")
    manager = TransactionManager(tmp_path)
    manager.prepare("tx-corrupt", _writes())
    blob = tmp_path / ".pdd/transactions/tx-corrupt/prepared-0.blob"
    blob.write_bytes(b"attacker bytes\n")
    with pytest.raises(TransactionError, match="prepared transaction blob is corrupt"):
        manager.commit("tx-corrupt")
    assert target.read_text() == "value = 1\n"


def test_later_corrupt_blob_is_detected_before_first_install(tmp_path) -> None:
    (tmp_path / "src").mkdir()
    target = tmp_path / "src/widget.py"
    target.write_text("value = 1\n")
    manager = TransactionManager(tmp_path)
    manager.prepare("tx-later-corrupt", _writes())
    transaction = tmp_path / ".pdd/transactions/tx-later-corrupt"
    (transaction / "prepared-1.blob").write_bytes(b"attacker bytes\n")
    with pytest.raises(TransactionError, match="prepared transaction blob is corrupt"):
        manager.commit("tx-later-corrupt")
    assert target.read_text() == "value = 1\n"
    assert not (tmp_path / ".pdd/evidence/widget.json").exists()


def test_later_corrupt_rollback_blob_is_detected_before_first_install(tmp_path) -> None:
    (tmp_path / "src").mkdir()
    target = tmp_path / "src/widget.py"
    target.write_text("value = 1\n")
    evidence = tmp_path / ".pdd/evidence/widget.json"
    evidence.parent.mkdir(parents=True)
    evidence.write_text("old evidence\n")
    manager = TransactionManager(tmp_path)
    manager.prepare("tx-rollback-corrupt", _writes())
    transaction = tmp_path / ".pdd/transactions/tx-rollback-corrupt"
    (transaction / "rollback-1.blob").write_bytes(b"attacker bytes\n")
    with pytest.raises(TransactionError, match="rollback transaction blob is corrupt"):
        manager.commit("tx-rollback-corrupt")
    assert target.read_text() == "value = 1\n"
    assert evidence.read_text() == "old evidence\n"


def test_recovery_rolls_back_partial_install_when_later_blob_is_corrupt(tmp_path) -> None:
    (tmp_path / "src").mkdir()
    target = tmp_path / "src/widget.py"
    target.write_text("value = 1\n")
    manager = TransactionManager(tmp_path)
    manager.prepare("tx-partial-corrupt", _writes())

    def crash(event):
        if event == "after_install:0":
            raise SystemExit("simulated process death")

    with pytest.raises(SystemExit):
        manager.commit("tx-partial-corrupt", crash_hook=crash)
    transaction = tmp_path / ".pdd/transactions/tx-partial-corrupt"
    (transaction / "prepared-1.blob").write_bytes(b"attacker bytes\n")
    with pytest.raises(TransactionError, match="prepared transaction blob is corrupt"):
        manager.recover("tx-partial-corrupt")
    assert target.read_text() == "value = 1\n"
    assert not (tmp_path / ".pdd/evidence/widget.json").exists()
    journal = json.loads((transaction / "journal.json").read_text())
    assert journal["phase"] == TransactionPhase.ROLLED_BACK.value


def test_read_only_incomplete_scan_does_not_change_journal_or_destinations(tmp_path) -> None:
    (tmp_path / "src").mkdir()
    target = tmp_path / "src/widget.py"
    target.write_text("value = 1\n")
    manager = TransactionManager(tmp_path)
    manager.prepare("tx-readonly", _writes())
    journal = tmp_path / ".pdd/transactions/tx-readonly/journal.json"
    before = journal.read_bytes()
    assert manager.incomplete() == ("tx-readonly",)
    assert journal.read_bytes() == before
    assert target.read_text() == "value = 1\n"


def test_journal_and_blobs_are_private_and_contain_modes(tmp_path) -> None:
    (tmp_path / "src").mkdir()
    (tmp_path / "src/widget.py").write_text("value = 1\n")
    manager = TransactionManager(tmp_path)
    manager.prepare("tx-private", _writes())
    transaction_dir = tmp_path / ".pdd/transactions/tx-private"
    assert transaction_dir.stat().st_mode & 0o777 == 0o700
    for path in transaction_dir.iterdir():
        assert path.stat().st_mode & 0o777 == 0o600
    payload = json.loads((transaction_dir / "journal.json").read_text())
    assert payload["entries"][0]["desired_mode"] == "100755"
    assert payload["entries"][0]["precondition"]["git_mode"] == "100644"


def test_secret_labeled_write_refuses_unencrypted_rollback(tmp_path) -> None:
    secret = PlannedWrite(
        PurePosixPath("secrets/token"), b"sensitive", "100644", secret=True
    )
    with pytest.raises(TransactionError, match="requires configured encryption"):
        TransactionManager(tmp_path).prepare("tx-secret", (secret,))


def test_descriptor_time_parent_symlink_swap_cannot_redirect_commit(
    tmp_path, monkeypatch
) -> None:
    source = tmp_path / "src"
    source.mkdir()
    target = source / "widget.py"
    target.write_text("value = 1\n")
    outside = tmp_path.parent / f"{tmp_path.name}-outside"
    outside.mkdir()
    outside_target = outside / "widget.py"
    outside_target.write_text("outside = True\n")

    manager = TransactionManager(tmp_path)
    manager.prepare("tx-parent-swap", _writes())
    original = manager._canonical_relpath  # pylint: disable=protected-access
    armed = True

    def swap_after_resolution(relpath, **kwargs):
        nonlocal armed
        canonical = original(relpath, **kwargs)
        if armed and relpath == PurePosixPath("src/widget.py"):
            armed = False
            source.rename(tmp_path / "src-before-swap")
            source.symlink_to(outside, target_is_directory=True)
        return canonical

    monkeypatch.setattr(manager, "_canonical_relpath", swap_after_resolution)
    with pytest.raises(
        TransactionConflict,
        match=(
            r"^destination (?:parent changed or is unsafe|alias policy changed): "
            r"src/widget\.py$"
        ),
    ):
        manager.commit("tx-parent-swap")

    assert outside_target.read_text() == "outside = True\n"
    assert (tmp_path / "src-before-swap/widget.py").read_text() == "value = 1\n"
    assert not (tmp_path / ".pdd/evidence/widget.json").exists()


def test_prepare_failure_never_publishes_orphan_transaction(tmp_path, monkeypatch) -> None:
    (tmp_path / "src").mkdir()
    (tmp_path / "src/widget.py").write_text("value = 1\n")
    manager = TransactionManager(tmp_path)
    original = manager._write_blob  # pylint: disable=protected-access
    calls = 0

    def fail_second(path, content):
        nonlocal calls
        calls += 1
        if calls == 2:
            raise OSError("simulated prepare failure")
        return original(path, content)

    monkeypatch.setattr(manager, "_write_blob", fail_second)
    with pytest.raises(OSError, match="simulated prepare failure"):
        manager.prepare("tx-failed", _writes())
    assert not (tmp_path / ".pdd/transactions/tx-failed").exists()
    assert manager.incomplete() == ()


def _approved_aliases():
    return {PurePosixPath("alias"): PurePosixPath("canonical")}


def test_transaction_commits_through_protected_approved_alias(tmp_path) -> None:
    (tmp_path / "canonical").mkdir()
    target = tmp_path / "canonical/widget.py"
    target.write_text("value = 1\n")
    (tmp_path / "alias").symlink_to("canonical", target_is_directory=True)
    writes = (PlannedWrite(PurePosixPath("alias/widget.py"), b"value = 2\n", "100644"),)

    manager = TransactionManager(tmp_path, approved_aliases=_approved_aliases())
    manager.prepare("tx-approved-alias", writes)
    assert manager.commit("tx-approved-alias").phase is TransactionPhase.COMMITTED
    assert target.read_text() == "value = 2\n"


def test_plan_rejects_duplicate_canonical_destinations_through_alias(tmp_path) -> None:
    (tmp_path / "canonical").mkdir()
    (tmp_path / "alias").symlink_to("canonical", target_is_directory=True)
    writes = (
        PlannedWrite(PurePosixPath("alias/widget.py"), b"alias\n", "100644"),
        PlannedWrite(PurePosixPath("canonical/widget.py"), b"canonical\n", "100644"),
    )

    manager = TransactionManager(tmp_path, approved_aliases=_approved_aliases())
    with pytest.raises(TransactionError, match="duplicate canonical destinations"):
        manager.prepare("tx-duplicate-canonical", writes)

    assert not (tmp_path / ".pdd/transactions/tx-duplicate-canonical").exists()


def test_alias_and_canonical_transactions_share_destination_lock(tmp_path) -> None:
    (tmp_path / "canonical").mkdir()
    (tmp_path / "canonical/widget.py").write_text("value = 1\n")
    (tmp_path / "alias").symlink_to("canonical", target_is_directory=True)
    manager = TransactionManager(tmp_path, approved_aliases=_approved_aliases())
    manager.prepare(
        "tx-alias-lock",
        (PlannedWrite(PurePosixPath("alias/widget.py"), b"alias\n", "100644"),),
    )
    manager.prepare(
        "tx-canonical-lock",
        (PlannedWrite(PurePosixPath("canonical/widget.py"), b"canonical\n", "100644"),),
    )

    class RecordingLock:
        paths: list[str] = []

        def __init__(self, path: str) -> None:
            self.path = path

        def __enter__(self):
            self.paths.append(self.path)
            return self

        def __exit__(self, *_args):
            return False

    alias_payload = json.loads(
        (tmp_path / ".pdd/transactions/tx-alias-lock/journal.json").read_text()
    )
    canonical_payload = json.loads(
        (tmp_path / ".pdd/transactions/tx-canonical-lock/journal.json").read_text()
    )
    with patch("pdd.sync_core.transaction.FileLock", RecordingLock):
        with manager._locks(alias_payload):  # pylint: disable=protected-access
            alias_locks = set(RecordingLock.paths)
        RecordingLock.paths.clear()
        with manager._locks(canonical_payload):  # pylint: disable=protected-access
            canonical_locks = set(RecordingLock.paths)

    assert alias_locks & canonical_locks


def test_descriptor_time_approved_alias_swap_cannot_redirect_commit(tmp_path, monkeypatch) -> None:
    canonical = tmp_path / "canonical"
    canonical.mkdir()
    target = canonical / "widget.py"
    target.write_text("value = 1\n")
    outside = tmp_path.parent / f"{tmp_path.name}-outside-alias"
    outside.mkdir()
    outside_target = outside / "widget.py"
    outside_target.write_text("outside = True\n")
    alias = tmp_path / "alias"
    alias.symlink_to("canonical", target_is_directory=True)
    writes = (PlannedWrite(PurePosixPath("alias/widget.py"), b"value = 2\n", "100644"),)
    manager = TransactionManager(tmp_path, approved_aliases=_approved_aliases())
    manager.prepare("tx-alias-swap", writes)
    original = manager._canonical_relpath  # pylint: disable=protected-access

    def swap_after_resolution(relpath, **kwargs):
        result = original(relpath, **kwargs)
        alias.unlink()
        alias.symlink_to(outside, target_is_directory=True)
        return result

    monkeypatch.setattr(manager, "_canonical_relpath", swap_after_resolution)
    with pytest.raises(TransactionConflict):
        manager.commit("tx-alias-swap")
    assert outside_target.read_text() == "outside = True\n"
    assert target.read_text() == "value = 1\n"


def test_committing_recovery_rejects_retargeted_approved_alias(tmp_path) -> None:
    canonical = tmp_path / "canonical"
    canonical.mkdir()
    target = canonical / "widget.py"
    target.write_text("value = 1\n")
    other = tmp_path / "other"
    other.mkdir()
    other_target = other / "widget.py"
    other_target.write_text("outside = True\n")
    alias = tmp_path / "alias"
    alias.symlink_to("canonical", target_is_directory=True)
    writes = (PlannedWrite(PurePosixPath("alias/widget.py"), b"value = 2\n", "100644"),)
    manager = TransactionManager(tmp_path, approved_aliases=_approved_aliases())
    manager.prepare("tx-recovery-alias", writes)

    with pytest.raises(SystemExit):
        manager.commit(
            "tx-recovery-alias",
            crash_hook=lambda event: (_ for _ in ()).throw(SystemExit())
            if event == "after_committing"
            else None,
        )
    alias.unlink()
    alias.symlink_to("other", target_is_directory=True)

    with pytest.raises(TransactionConflict, match="alias"):
        manager.recover("tx-recovery-alias")
    assert target.read_text() == "value = 1\n"
    assert other_target.read_text() == "outside = True\n"


def test_recovery_requires_protected_alias_authority_not_only_journal(tmp_path) -> None:
    canonical = tmp_path / "canonical"
    canonical.mkdir()
    target = canonical / "widget.py"
    target.write_text("value = 1\n")
    (tmp_path / "alias").symlink_to("canonical", target_is_directory=True)
    writes = (PlannedWrite(PurePosixPath("alias/widget.py"), b"value = 2\n", "100644"),)
    manager = TransactionManager(tmp_path, approved_aliases=_approved_aliases())
    manager.prepare("tx-recovery-authority", writes)

    with pytest.raises(SystemExit):
        manager.commit(
            "tx-recovery-authority",
            crash_hook=lambda event: (_ for _ in ()).throw(SystemExit())
            if event == "after_committing"
            else None,
        )

    with pytest.raises(TransactionConflict, match="alias policy"):
        TransactionManager(tmp_path).recover("tx-recovery-authority")
    assert target.read_text() == "value = 1\n"


def test_public_recover_loads_committed_protected_alias_policy(
    tmp_path, monkeypatch
) -> None:
    _git(tmp_path, "init", "-q")
    _git(tmp_path, "config", "user.email", "recover@example.com")
    _git(tmp_path, "config", "user.name", "Recover Test")
    (tmp_path / ".pdd").mkdir()
    (tmp_path / ".pdd/sync-aliases.json").write_text(
        json.dumps(
            {
                "schema_version": 1,
                "aliases": [{"alias_path": "alias", "canonical_path": "canonical"}],
            }
        ),
        encoding="utf-8",
    )
    (tmp_path / "canonical").mkdir()
    target = tmp_path / "canonical/widget.py"
    target.write_text("value = 1\n")
    (tmp_path / "alias").symlink_to("canonical", target_is_directory=True)
    _git(tmp_path, "add", ".pdd/sync-aliases.json", "canonical/widget.py", "alias")
    _git(tmp_path, "commit", "-q", "-m", "protected alias policy")
    manager = TransactionManager(tmp_path, approved_aliases=_approved_aliases())
    manager.prepare(
        "tx-cli-recovery",
        (PlannedWrite(PurePosixPath("alias/widget.py"), b"value = 2\n", "100644"),),
    )
    with pytest.raises(SystemExit):
        manager.commit(
            "tx-cli-recovery",
            crash_hook=lambda event: (_ for _ in ()).throw(SystemExit())
            if event == "after_committing"
            else None,
        )

    monkeypatch.chdir(tmp_path)
    result = CliRunner().invoke(cli, ["recover", "--transaction", "tx-cli-recovery"])

    assert result.exit_code == 0, result.output
    assert '"phase": "COMMITTED"' in result.output
    assert target.read_text() == "value = 2\n"
