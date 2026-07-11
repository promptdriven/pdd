"""Integrity checks for the initial protected verification-profile rollout."""

from __future__ import annotations

import hashlib
import json
import re
from dataclasses import replace
from pathlib import Path, PurePosixPath

from pdd.sync_core import build_unit_manifest, load_verification_profiles
from pdd.sync_core.git_io import read_git_blob
from pdd.sync_core.manifest import ManifestRefs
from pdd.sync_core.runner import pytest_validator_config_digest
from pdd.sync_core.verification import PROFILE_PATH
import pdd.sync_core.verification as verification


ROOT = Path(__file__).resolve().parents[1]
PROFILE_FILE = ROOT / PROFILE_PATH
EXPECTED_PROFILE_COUNT = 466
REQUIREMENT_ID = re.compile(r"\bREQ-[A-Za-z0-9_.:-]+\b")


def _requirements(prompt_path: PurePosixPath) -> list[str]:
    raw = (ROOT / prompt_path).read_bytes()
    explicit = sorted(set(REQUIREMENT_ID.findall(raw.decode("utf-8"))))
    return explicit or [f"CONTRACT-SHA256:{hashlib.sha256(raw).hexdigest()}"]


def _profile_bytes_as_protected_base(monkeypatch, profile_bytes: bytes):
    """Return a loader whose arbitrary profile refs resolve to fixed rollout bytes."""

    def protected_read(_root: Path, _ref: str, path: PurePosixPath) -> bytes | None:
        if path == PROFILE_PATH:
            return profile_bytes
        return read_git_blob(ROOT, "HEAD", path)

    monkeypatch.setattr(verification, "read_git_blob", protected_read)


def test_rollout_profiles_cover_the_protected_pdd_denominator(monkeypatch) -> None:
    """Require one complete, reviewable profile for every protected PDD unit."""
    payload = json.loads(PROFILE_FILE.read_text(encoding="utf-8"))
    rows = payload["profiles"]
    manifest = build_unit_manifest(ROOT, base_ref="HEAD", head_ref="HEAD")
    expected = {
        (unit.prompt_relpath.as_posix(), unit.language_id)
        for unit in manifest.expected_managed
    }
    actual = {(row["prompt_path"], row["language_id"]) for row in rows}

    assert len(expected) == EXPECTED_PROFILE_COUNT
    assert len(rows) == EXPECTED_PROFILE_COUNT
    assert len(actual) == len(rows)
    assert actual == expected

    for row in rows:
        prompt_path = PurePosixPath(row["prompt_path"])
        requirements = _requirements(prompt_path)
        assert row["required_requirement_ids"] == requirements
        assert len(row["obligations"]) == 1
        obligation = row["obligations"][0]
        assert obligation["obligation_id"] == "threshold-human-attestation"
        assert obligation["kind"] == "human-attestation"
        assert obligation["validator_id"] == "threshold-ed25519"
        assert obligation["validator_config_digest"] == "threshold-ed25519-v1"
        assert obligation["required"] is True
        assert obligation["requirement_ids"] == requirements
        assert obligation["artifact_paths"] == [prompt_path.as_posix()]
        assert (ROOT / prompt_path).is_file()

    profile_bytes = PROFILE_FILE.read_bytes()
    protected_manifest = replace(
        manifest, refs=ManifestRefs("protected-base", "candidate-head")
    )
    _profile_bytes_as_protected_base(monkeypatch, profile_bytes)
    profiles = load_verification_profiles(ROOT, protected_manifest)
    assert profiles.invalid_reasons == ()
    assert profiles.coverage == 1.0
    assert len(profiles.profiles) == EXPECTED_PROFILE_COUNT

    pytest_obligations = [
        obligation
        for profile in profiles.profiles
        for obligation in profile.obligations
        if obligation.validator_id == "pytest"
    ]
    for obligation in pytest_obligations:
        assert obligation.validator_config_digest == pytest_validator_config_digest(
            ROOT, "HEAD", obligation.artifact_paths
        )
    assert pytest_obligations == []


def test_rollout_profiles_cannot_self_authorize(monkeypatch) -> None:
    """A candidate copy is rejected until this rollout has merged as protected base."""
    manifest = build_unit_manifest(ROOT, base_ref="HEAD", head_ref="HEAD")
    candidate_manifest = replace(
        manifest, refs=ManifestRefs("protected-base", "candidate-head")
    )
    profile_bytes = PROFILE_FILE.read_bytes()

    def candidate_only_read(_root: Path, ref: str, path: PurePosixPath) -> bytes | None:
        if path == PROFILE_PATH:
            return profile_bytes if ref == "candidate-head" else None
        return read_git_blob(ROOT, "HEAD", path)

    monkeypatch.setattr(verification, "read_git_blob", candidate_only_read)
    profiles = load_verification_profiles(ROOT, candidate_manifest)

    assert profiles.coverage == 0.0
    assert len(profiles.invalid_reasons) == EXPECTED_PROFILE_COUNT
    assert all("candidate-only profile lacks protected approval" in reason for reason in profiles.invalid_reasons)
