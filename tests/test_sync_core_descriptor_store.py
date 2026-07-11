"""Regression tests for descriptor-anchored replay ledger storage."""

from __future__ import annotations

import json
import os

import pytest

from pdd.sync_core.descriptor_store import DescriptorStoreError, update_json


def test_checker_owned_replay_root_ignores_platform_temp_ancestor_mode(
    tmp_path,
) -> None:
    """Only the configured checker-owned root begins the protected boundary."""
    platform_temp = tmp_path / "platform-temp"
    platform_temp.mkdir(mode=0o777)
    platform_temp.chmod(0o777)
    replay_root = platform_temp / "checker-owned"
    replay_root.mkdir(mode=0o700)
    ledger = replay_root / "nested" / "replay.json"

    update_json(
        ledger,
        [],
        lambda records: [*records, "accepted"],
        trust_root=replay_root,
    )

    assert json.loads(ledger.read_text(encoding="utf-8")) == ["accepted"]


def test_checker_owned_replay_root_rejects_symlinked_descendant(tmp_path) -> None:
    """Descriptor traversal below the trust root must never follow symlinks."""
    replay_root = tmp_path / "checker-owned"
    replay_root.mkdir(mode=0o700)
    outside = tmp_path / "outside"
    outside.mkdir()
    (replay_root / "linked").symlink_to(outside, target_is_directory=True)

    with pytest.raises(DescriptorStoreError, match="parent is unsafe"):
        update_json(
            replay_root / "linked" / "replay.json",
            [],
            lambda records: records,
            trust_root=replay_root,
        )

    assert not (outside / "replay.json").exists()


def test_existing_writable_replay_root_is_rejected_without_repair(tmp_path) -> None:
    replay_root = tmp_path / "checker-owned"
    replay_root.mkdir(mode=0o700)
    ledger = replay_root / "replay.json"
    ledger.write_text('["preserved-nonce"]\n', encoding="utf-8")
    ledger.chmod(0o600)
    replay_root.chmod(0o777)

    with pytest.raises(DescriptorStoreError, match="root is unsafe"):
        update_json(
            ledger,
            [],
            lambda records: [*records, "new-nonce"],
            trust_root=replay_root,
        )

    assert replay_root.stat().st_mode & 0o777 == 0o777
    assert json.loads(ledger.read_text(encoding="utf-8")) == ["preserved-nonce"]


def test_foreign_owned_replay_leaves_are_rejected(tmp_path, monkeypatch) -> None:
    replay_root = tmp_path / "checker-owned"
    replay_root.mkdir(mode=0o700)
    ledger = replay_root / "replay.json"
    ledger.write_text("[]\n", encoding="utf-8")
    ledger.chmod(0o600)
    original_fstat = os.fstat

    def foreign_regular(descriptor):
        metadata = original_fstat(descriptor)
        if not os.path.isfile(f"/dev/fd/{descriptor}"):
            return metadata
        fields = list(metadata)
        fields[4] = metadata.st_uid + 1
        return os.stat_result(fields)

    monkeypatch.setattr("pdd.sync_core.descriptor_store.os.fstat", foreign_regular)
    with pytest.raises(DescriptorStoreError, match="unsafe"):
        update_json(ledger, [], lambda records: records, trust_root=replay_root)
