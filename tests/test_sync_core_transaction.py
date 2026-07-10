"""Crash, CAS, mode, and recovery tests for the durable transaction WAL."""

import json
import os
from pathlib import PurePosixPath

import pytest

from pdd.sync_core import (
    PlannedWrite,
    TransactionConflict,
    TransactionError,
    TransactionManager,
    TransactionPhase,
)


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
