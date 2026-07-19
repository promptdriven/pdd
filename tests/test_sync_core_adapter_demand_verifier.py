"""Tests for exact-SHA PDD machine adapter-demand evidence."""

import hashlib
import json
import subprocess
import sys
from pathlib import Path

import pytest

from pdd.sync_core import adapter_demand_verifier
from pdd.sync_core.adapter_demand_verifier import (
    AdapterDemandError,
    EXPECTED_MACHINE_OBLIGATION_IDS,
    EXPECTED_MACHINE_VALIDATOR_IDS,
    PROFILE_EVIDENCE_SOURCE_SHA,
    PROTECTED_PROFILES_SHA256,
    PROTECTED_MAIN_SHA,
    PROFILE_PATH,
    _parse_profiles,
    _summarize_profiles,
    build_adapter_demand,
    canonical_json,
)


ROOT = Path(__file__).resolve().parents[1]
ARTIFACT = ROOT / "docs" / "global_sync_pdd_adapter_demand.json"
EXPECTED_PROTECTED_MAIN_SHA = "c712cbb7e08c157757a238cb8e49d65a9a3a2239"


def test_adapter_demand_protected_registry_matches_committed_artifact() -> None:
    """The committed artifact is the exact canonical protected-Git result."""
    assert PROTECTED_MAIN_SHA == EXPECTED_PROTECTED_MAIN_SHA
    demand = build_adapter_demand(
        ROOT,
        PROFILE_EVIDENCE_SOURCE_SHA,
        PROTECTED_MAIN_SHA,
        PROFILE_PATH,
        PROTECTED_PROFILES_SHA256,
    )
    assert demand["profile_count"] == 468
    assert demand["machine_obligation_profile_count"] == 1
    assert demand["human_attestation_only_profile_count"] == 467
    assert demand["machine_validator_ids"] == list(EXPECTED_MACHINE_VALIDATOR_IDS)
    assert demand["machine_obligation_ids"] == list(EXPECTED_MACHINE_OBLIGATION_IDS)
    assert not demand["unknown_demanded_adapters"]
    assert demand["profile_evidence_source_sha"] == PROFILE_EVIDENCE_SOURCE_SHA
    assert demand["protected_main_sha"] == PROTECTED_MAIN_SHA
    assert ARTIFACT.read_bytes() == canonical_json(demand)


def test_adapter_demand_cli_writes_exact_canonical_artifact(tmp_path: Path) -> None:
    """The ledger-controlled command reproduces the committed evidence bytes."""
    output = tmp_path / "adapter-demand.json"
    result = subprocess.run(
        [
            sys.executable,
            "-m",
            "pdd.sync_core.adapter_demand_verifier",
            "--pdd-profiles",
            ".pdd/verification-profiles.json",
            "--profile-evidence-source-sha",
            PROFILE_EVIDENCE_SOURCE_SHA,
            "--protected-main-sha",
            PROTECTED_MAIN_SHA,
            "--profiles-sha256",
            PROTECTED_PROFILES_SHA256,
            "--output",
            str(output),
            "--require-exact-validators",
            "pytest",
            "--require-no-unknown-adapters",
        ],
        cwd=ROOT,
        check=False,
        capture_output=True,
        text=True,
    )
    assert result.returncode == 0, result.stderr
    assert output.read_bytes() == ARTIFACT.read_bytes()


def test_adapter_demand_cli_failure_removes_preseeded_output_and_temp_files(
    tmp_path: Path,
) -> None:
    """Failed verification cannot leave stale or partially written evidence."""
    output = tmp_path / "adapter-demand.json"
    output.write_text("stale evidence", encoding="utf-8")
    result = subprocess.run(
        [
            sys.executable,
            "-m",
            "pdd.sync_core.adapter_demand_verifier",
            "--pdd-profiles",
            ".pdd/verification-profiles.json",
            "--profile-evidence-source-sha",
            PROFILE_EVIDENCE_SOURCE_SHA,
            "--protected-main-sha",
            "0" * 40,
            "--profiles-sha256",
            PROTECTED_PROFILES_SHA256,
            "--output",
            str(output),
            "--require-exact-validators",
            "pytest",
            "--require-no-unknown-adapters",
        ],
        cwd=ROOT,
        check=False,
        capture_output=True,
        text=True,
    )
    assert result.returncode == 1
    assert "protected main SHA does not match" in result.stderr
    assert not output.exists()
    assert not list(tmp_path.iterdir())


def test_adapter_demand_argparse_failure_removes_every_preseeded_output(
    tmp_path: Path,
) -> None:
    """Raw output options are invalidated before a missing required option exits."""
    first_output = tmp_path / "first-output.json"
    second_output = tmp_path / "second-output.json"
    first_output.write_text("stale first evidence", encoding="utf-8")
    second_output.write_text("stale second evidence", encoding="utf-8")
    result = subprocess.run(
        [
            sys.executable,
            "-m",
            "pdd.sync_core.adapter_demand_verifier",
            "--pdd-profiles",
            ".pdd/verification-profiles.json",
            "--output",
            str(first_output),
            f"--output={second_output}",
        ],
        cwd=ROOT,
        check=False,
        capture_output=True,
        text=True,
    )
    assert result.returncode == 2
    assert not first_output.exists()
    assert not second_output.exists()


def test_adapter_demand_rejects_abbreviated_output_without_invalidating_its_value(
    tmp_path: Path,
) -> None:
    """An unknown output abbreviation cannot trigger raw stale-output cleanup."""
    valid_output = tmp_path / "valid-output.json"
    abbreviated_value = tmp_path / "abbreviated-value.json"
    abbreviated_value.write_text("retain this", encoding="utf-8")
    result = subprocess.run(
        [
            sys.executable,
            "-m",
            "pdd.sync_core.adapter_demand_verifier",
            "--pdd-profiles",
            ".pdd/verification-profiles.json",
            "--profile-evidence-source-sha",
            PROFILE_EVIDENCE_SOURCE_SHA,
            "--protected-main-sha",
            PROTECTED_MAIN_SHA,
            "--output",
            str(valid_output),
            "--out",
            str(abbreviated_value),
        ],
        cwd=ROOT,
        check=False,
        capture_output=True,
        text=True,
    )
    assert result.returncode == 2
    assert "unrecognized arguments: --out" in result.stderr
    assert not valid_output.exists()
    assert abbreviated_value.read_text(encoding="utf-8") == "retain this"


def test_adapter_demand_does_not_invalidate_output_tokens_after_double_dash(
    tmp_path: Path,
) -> None:
    """The raw scan honors argparse's option-terminator boundary."""
    post_boundary_output = tmp_path / "post-boundary-output.json"
    post_boundary_output.write_text("retain this too", encoding="utf-8")
    result = subprocess.run(
        [
            sys.executable,
            "-m",
            "pdd.sync_core.adapter_demand_verifier",
            "--pdd-profiles",
            ".pdd/verification-profiles.json",
            "--profile-evidence-source-sha",
            PROFILE_EVIDENCE_SOURCE_SHA,
            "--protected-main-sha",
            PROTECTED_MAIN_SHA,
            "--",
            "--output",
            str(post_boundary_output),
        ],
        cwd=ROOT,
        check=False,
        capture_output=True,
        text=True,
    )
    assert result.returncode == 2
    assert post_boundary_output.read_text(encoding="utf-8") == "retain this too"


@pytest.mark.parametrize(
    ("output_arguments", "filename"),
    (
        (("--output", "-"), "-"),
        (("--output=-1",), "-1"),
    ),
)
def test_adapter_demand_rejects_dash_prefixed_outputs_without_deletion(
    tmp_path: Path,
    monkeypatch: pytest.MonkeyPatch,
    output_arguments: tuple[str, ...],
    filename: str,
) -> None:
    """Split and equals output forms reject dash paths without stale-file cleanup."""
    invalid_path = tmp_path / filename
    invalid_path.write_text("retain this invalid path", encoding="utf-8")
    monkeypatch.chdir(tmp_path)
    monkeypatch.setattr(
        sys,
        "argv",
        [
            "adapter-demand-verifier",
            "--pdd-profiles",
            ".pdd/verification-profiles.json",
            "--profile-evidence-source-sha",
            PROFILE_EVIDENCE_SOURCE_SHA,
            "--protected-main-sha",
            PROTECTED_MAIN_SHA,
            *output_arguments,
        ],
    )
    with pytest.raises(SystemExit) as exc_info:
        adapter_demand_verifier.main()
    assert exc_info.value.code == 2
    assert invalid_path.read_text(encoding="utf-8") == "retain this invalid path"


def test_adapter_demand_cli_rejects_required_validator_mismatch(tmp_path: Path) -> None:
    """A controlling command cannot claim a validator the registry does not demand."""
    result = subprocess.run(
        [
            sys.executable,
            "-m",
            "pdd.sync_core.adapter_demand_verifier",
            "--pdd-profiles",
            ".pdd/verification-profiles.json",
            "--profile-evidence-source-sha",
            PROFILE_EVIDENCE_SOURCE_SHA,
            "--protected-main-sha",
            PROTECTED_MAIN_SHA,
            "--output",
            str(tmp_path / "should-not-exist.json"),
            "--require-exact-validators",
            "vitest",
        ],
        cwd=ROOT,
        check=False,
        capture_output=True,
        text=True,
    )
    assert result.returncode == 1
    assert "required machine validators do not match" in result.stderr


def test_adapter_demand_rejects_duplicate_profile_json_members() -> None:
    """Repeated JSON keys cannot overwrite protected obligations silently."""
    raw = b'{"schema_version":1,"schema_version":1,"profiles":[]}'
    with pytest.raises(AdapterDemandError, match="JSON is malformed"):
        _parse_profiles(raw)


def test_adapter_demand_does_not_count_human_validator_as_machine_adapter() -> None:
    """Human threshold attestations do not demand an executable adapter."""
    payload = {
        "schema_version": 1,
        "profiles": [
            {
                "prompt_path": "pdd/prompts/example.prompt",
                "language_id": "python",
                "required_requirement_ids": ["REQ-1"],
                "obligations": [
                    {
                        "obligation_id": "threshold-human-attestation",
                        "kind": "human-attestation",
                        "validator_id": "threshold-ed25519",
                        "validator_config_digest": "threshold-ed25519-v1",
                        "requirement_ids": ["REQ-1"],
                        "artifact_paths": ["pdd/prompts/example.prompt"],
                        "required": True,
                    }
                ],
            }
        ],
    }
    summary = _summarize_profiles(_parse_profiles(json.dumps(payload).encode()))
    assert summary.machine_profile_count == 0
    assert summary.human_only_profile_count == 1
    assert not summary.machine_validator_ids
    assert not summary.unknown_adapters


def test_adapter_demand_identifies_unknown_machine_adapters() -> None:
    """Only machine test obligations participate in the unknown-adapter check."""
    payload = {
        "schema_version": 1,
        "profiles": [
            {
                "prompt_path": "pdd/prompts/example.prompt",
                "language_id": "python",
                "required_requirement_ids": ["REQ-1"],
                "obligations": [
                    {
                        "obligation_id": "unrecognized-adapter",
                        "kind": "test",
                        "validator_id": "unrecognized",
                        "validator_config_digest": "unrecognized-v1",
                        "requirement_ids": ["REQ-1"],
                        "artifact_paths": ["tests/test_example.py"],
                        "required": True,
                    }
                ],
            }
        ],
    }
    summary = _summarize_profiles(_parse_profiles(json.dumps(payload).encode()))
    assert summary.machine_validator_ids == ("unrecognized",)
    assert summary.unknown_adapters == ("unrecognized",)


def test_adapter_demand_rejects_unpinned_digest() -> None:
    """A caller cannot substitute a different mutable registry digest."""
    with pytest.raises(AdapterDemandError, match="digest does not match"):
        build_adapter_demand(
            ROOT,
            PROFILE_EVIDENCE_SOURCE_SHA,
            PROTECTED_MAIN_SHA,
            PROFILE_PATH,
            "0" * 64,
        )


def test_adapter_demand_rejects_protected_main_profile_drift(
    tmp_path: Path, monkeypatch: pytest.MonkeyPatch
) -> None:
    """Divergent protected-main profile bytes cannot produce trusted demand."""
    root = tmp_path / "repository"
    root.mkdir()
    _git(root, "init", "-q")
    _git(root, "config", "user.email", "verifier@example.com")
    _git(root, "config", "user.name", "Verifier Test")
    profile_bytes = json.dumps(_human_profile_payload(), sort_keys=True).encode("utf-8")
    policy = root / ".pdd" / "verification-profiles.json"
    policy.parent.mkdir()
    policy.write_bytes(profile_bytes)
    repository_id = "11111111-1111-1111-1111-111111111111"
    (root / ".pdd" / "repository-id").write_text(repository_id, encoding="ascii")
    _git(root, "add", ".")
    _git(root, "commit", "-qm", "immutable profile evidence source")
    source_sha = _git(root, "rev-parse", "HEAD")
    policy.write_bytes(profile_bytes + b"\n")
    _git(root, "add", ".")
    _git(root, "commit", "-qm", "divergent protected main")
    main_sha = _git(root, "rev-parse", "HEAD")
    _configure_minimal_protected_registry(
        monkeypatch, source_sha, main_sha, profile_bytes, repository_id
    )
    with pytest.raises(AdapterDemandError, match="differs from immutable evidence"):
        build_adapter_demand(root, source_sha, main_sha, PROFILE_PATH)


def test_adapter_demand_main_rejects_profile_drift_and_removes_stale_output(
    tmp_path: Path, monkeypatch: pytest.MonkeyPatch, capsys: pytest.CaptureFixture[str]
) -> None:
    """The CLI cannot leave stale output when protected-main bytes diverge."""
    root = tmp_path / "repository"
    root.mkdir()
    _git(root, "init", "-q")
    _git(root, "config", "user.email", "verifier@example.com")
    _git(root, "config", "user.name", "Verifier Test")
    profile_bytes = json.dumps(_human_profile_payload(), sort_keys=True).encode("utf-8")
    policy = root / ".pdd" / "verification-profiles.json"
    policy.parent.mkdir()
    policy.write_bytes(profile_bytes)
    repository_id = "11111111-1111-1111-1111-111111111111"
    (root / ".pdd" / "repository-id").write_text(repository_id, encoding="ascii")
    _git(root, "add", ".")
    _git(root, "commit", "-qm", "immutable profile evidence source")
    source_sha = _git(root, "rev-parse", "HEAD")
    policy.write_bytes(profile_bytes + b"\n")
    _git(root, "add", ".")
    _git(root, "commit", "-qm", "divergent protected main")
    main_sha = _git(root, "rev-parse", "HEAD")
    _configure_minimal_protected_registry(
        monkeypatch, source_sha, main_sha, profile_bytes, repository_id
    )
    output = tmp_path / "adapter-demand.json"
    output.write_text("stale evidence", encoding="utf-8")
    monkeypatch.chdir(root)
    monkeypatch.setattr(
        sys,
        "argv",
        [
            "adapter-demand-verifier",
            "--pdd-profiles",
            ".pdd/verification-profiles.json",
            "--profile-evidence-source-sha",
            source_sha,
            "--protected-main-sha",
            main_sha,
            "--output",
            str(output),
        ],
    )
    with pytest.raises(SystemExit) as exc_info:
        adapter_demand_verifier.main()
    assert exc_info.value.code == 1
    assert "differs from immutable evidence" in capsys.readouterr().err
    assert not output.exists()
    assert not list(tmp_path.glob(".adapter-demand.json.*"))


def test_adapter_demand_ignores_replace_ref_for_repository_identity(
    tmp_path: Path, monkeypatch: pytest.MonkeyPatch
) -> None:
    """A replacement commit cannot forge the identity beside an unchanged profile."""
    root = tmp_path / "repository"
    root.mkdir()
    _git(root, "init", "-q")
    _git(root, "config", "user.email", "verifier@example.com")
    _git(root, "config", "user.name", "Verifier Test")
    profile = _human_profile_payload()
    profile_bytes = json.dumps(profile, sort_keys=True).encode("utf-8")
    expected_id = "11111111-1111-1111-1111-111111111111"
    forged_id = "22222222-2222-2222-2222-222222222222"
    policy = root / ".pdd" / "verification-profiles.json"
    policy.parent.mkdir()
    policy.write_bytes(profile_bytes)
    (root / ".pdd" / "repository-id").write_text(expected_id, encoding="ascii")
    _git(root, "add", ".")
    _git(root, "commit", "-qm", "actual protected tree")
    protected_sha = _git(root, "rev-parse", "HEAD")
    (root / ".pdd" / "repository-id").write_text(forged_id, encoding="ascii")
    _git(root, "add", ".")
    _git(root, "commit", "-qm", "forged replacement tree")
    forged_sha = _git(root, "rev-parse", "HEAD")
    _git(root, "replace", protected_sha, forged_sha)
    assert _git(root, "show", f"{protected_sha}:.pdd/repository-id") == forged_id
    _configure_minimal_protected_registry(
        monkeypatch, protected_sha, protected_sha, profile_bytes, expected_id
    )
    demand = build_adapter_demand(root, protected_sha, protected_sha, PROFILE_PATH)
    assert demand["repository_id"] == expected_id


def _git(root: Path, *arguments: str) -> str:
    """Run one local test-repository command without mutating process globals."""
    return subprocess.run(
        ["git", *arguments],
        cwd=root,
        check=True,
        capture_output=True,
        text=True,
    ).stdout.strip()


def _configure_minimal_protected_registry(
    monkeypatch: pytest.MonkeyPatch,
    source_sha: str,
    main_sha: str,
    profile_bytes: bytes,
    repository_id: str,
) -> None:
    """Bind the verifier's immutable expectations to one local test repository."""
    monkeypatch.setattr(adapter_demand_verifier, "PROFILE_EVIDENCE_SOURCE_SHA", source_sha)
    monkeypatch.setattr(adapter_demand_verifier, "PROTECTED_MAIN_SHA", main_sha)
    monkeypatch.setattr(adapter_demand_verifier, "PROTECTED_REPOSITORY_ID", repository_id)
    monkeypatch.setattr(
        adapter_demand_verifier,
        "PROTECTED_PROFILES_SHA256",
        hashlib.sha256(profile_bytes).hexdigest(),
    )
    monkeypatch.setattr(adapter_demand_verifier, "EXPECTED_PROFILE_COUNT", 1)
    monkeypatch.setattr(adapter_demand_verifier, "EXPECTED_MACHINE_PROFILE_COUNT", 0)
    monkeypatch.setattr(adapter_demand_verifier, "EXPECTED_HUMAN_ONLY_PROFILE_COUNT", 1)
    monkeypatch.setattr(adapter_demand_verifier, "EXPECTED_MACHINE_VALIDATOR_IDS", ())
    monkeypatch.setattr(adapter_demand_verifier, "EXPECTED_MACHINE_OBLIGATION_IDS", ())


def _human_profile_payload() -> dict[str, object]:
    """Build the smallest strict profile registry with human-only demand."""
    return {
        "schema_version": 1,
        "profiles": [
            {
                "prompt_path": "pdd/prompts/example.prompt",
                "language_id": "python",
                "required_requirement_ids": ["REQ-1"],
                "obligations": [
                    {
                        "obligation_id": "threshold-human-attestation",
                        "kind": "human-attestation",
                        "validator_id": "threshold-ed25519",
                        "validator_config_digest": "threshold-ed25519-v1",
                        "requirement_ids": ["REQ-1"],
                        "artifact_paths": ["pdd/prompts/example.prompt"],
                        "required": True,
                    }
                ],
            }
        ],
    }
