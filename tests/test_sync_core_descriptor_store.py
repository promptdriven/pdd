"""Regression tests for descriptor-anchored replay ledger storage."""

from __future__ import annotations

import json

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
