"""Tests for released-checker runtime provenance and wrapper evidence schemas."""

from copy import deepcopy
import hashlib
import json
from pathlib import Path
import sys
import zipfile

import pytest

from pdd.sync_core import CheckerIdentity, checker_identity_from_environment
from pdd.sync_core.released_checker import (
    ReleasePin,
    ReleasedCheckerError,
    ReleasedCheckerEvidenceError,
    _evidence_main,
    build_intermediate_release_evidence,
    main,
    validate_intermediate_release_evidence,
    validate_released_checker_runtime,
)


def _wheel(tmp_path: Path) -> tuple[Path, CheckerIdentity, Path, Path]:
    tmp_path.mkdir(parents=True, exist_ok=True)
    wheel = tmp_path / "pdd-1.0-py3-none-any.whl"
    member = "pdd/sync_core/released_checker.py"
    content = b"exact installed checker bytes\n"
    with zipfile.ZipFile(wheel, "w") as archive:
        archive.writestr(member, content)
    prefix = tmp_path / "venv"
    package = prefix / "lib/python3.12/site-packages" / member
    package.parent.mkdir(parents=True)
    package.write_bytes(content)
    identity = CheckerIdentity(
        hashlib.sha256(wheel.read_bytes()).hexdigest(),
        "refs/tags/v1.0.0",
        "promptdriven/pdd/.github/workflows/release.yml@refs/tags/v1.0.0",
    )
    return wheel, identity, prefix, package


def _pin() -> dict[str, object]:
    return {
        "schema_version": 1,
        "repository": "promptdriven/pdd",
        "repository_id": "3b4d7b1c-d6cc-4752-ba93-6b98d1a710e0",
        "repository_sha": "a" * 40,
        "release_ref": "refs/tags/v1.2.3",
        "release_url": "https://github.com/promptdriven/pdd/releases/tag/v1.2.3",
        "wheel_url": "https://files.pythonhosted.org/packages/a6/66/pdd_cli-1.2.3-py3-none-any.whl",
        "wheel_sha256": "b" * 64,
        "workflow_run_url": "https://github.com/promptdriven/pdd/actions/runs/12345",
        "workflow_run_conclusion": "success",
        "workflow_job_url": "https://github.com/promptdriven/pdd/actions/runs/12345/job/67890",
        "workflow_identity": "promptdriven/pdd/.github/workflows/release.yml@refs/tags/v1.2.3",
        "pypi_provenance_url": "https://pypi.org/integrity/pdd-cli/1.2.3/pdd_cli-1.2.3-py3-none-any.whl/provenance",
    }


def _profiles() -> dict[str, object]:
    shared = {
        "obligation_id": "required-human",
        "kind": "human-attestation",
        "validator_id": "threshold-ed25519",
        "validator_config_digest": "threshold-ed25519-v1",
        "requirement_ids": ["requirement-human"],
        "artifact_paths": ["pdd/prompts/human_python.prompt"],
        "required": True,
    }
    return {
        "schema_version": 1,
        "profiles": [
            {
                "prompt_path": "pdd/prompts/machine_python.prompt",
                "language_id": "python",
                "required_requirement_ids": ["requirement-machine"],
                "obligations": [
                    {
                        "obligation_id": "required-pytest",
                        "kind": "test",
                        "validator_id": "pytest",
                        "validator_config_digest": "pytest-v1",
                        "requirement_ids": ["requirement-machine"],
                        "artifact_paths": ["tests/test_machine.py"],
                        "code_under_test_paths": ["pdd/sync_core/released_checker.py"],
                        "required": True,
                    }
                ],
            },
            {
                "prompt_path": "pdd/prompts/human_python.prompt",
                "language_id": "python",
                "required_requirement_ids": ["requirement-human"],
                "obligations": [shared],
            },
        ],
    }


def _report() -> dict[str, object]:
    counts = {
        "unaccounted_tracked_paths": 0,
        "managed_units": 2,
        "protected_expected_managed_units": 2,
        "managed_waivers": 0,
        "invalid": 1,
        "trusted_in_sync": 0,
        "verification_profile_complete": 2,
        "trusted_current_evidence": 0,
        "drifted": 1,
        "unbaselined": 1,
        "corrupt": 0,
        "unknown": 1,
        "conflict": 0,
        "failed": 1,
    }
    return {
        "schema_version": 1,
        "ok": False,
        "project_root": "/protected/repository",
        "repository_id": "3b4d7b1c-d6cc-4752-ba93-6b98d1a710e0",
        "base_sha": "a" * 40,
        "head_sha": "a" * 40,
        "manifest_digest": "c" * 64,
        "counts": counts,
        "errors": ["protected base has no attestation trust policy"],
        "recovery_required": [],
        "units": [
            {
                "subject": "pdd/prompts/machine_python.prompt",
                "inventory": "MANAGED",
                "baseline": "DRIFTED",
                "semantic": "FAILED",
                "in_sync": False,
                "evidence_complete": False,
                "changed_roles": [],
                "reason": "no trustworthy baseline exists",
            },
            {
                "subject": "pdd/prompts/human_python.prompt",
                "inventory": "MANAGED",
                "baseline": "UNBASELINED",
                "semantic": "UNKNOWN",
                "in_sync": False,
                "evidence_complete": False,
                "changed_roles": [],
                "reason": "no trustworthy baseline exists",
            },
        ],
    }


def _evidence() -> tuple[dict[str, object], dict[str, object], dict[str, object]]:
    report = _report()
    profiles = _profiles()
    return build_intermediate_release_evidence(_pin(), report, profiles, exit_code=1), report, profiles


def test_pinned_wheel_in_isolated_site_packages_is_accepted(tmp_path) -> None:
    wheel, identity, prefix, package = _wheel(tmp_path)
    validate_released_checker_runtime(
        identity, wheel, package_path=package, prefix=prefix, base_prefix=tmp_path / "system"
    )


def test_modified_wheel_and_source_checkout_are_rejected(tmp_path) -> None:
    wheel, identity, prefix, package = _wheel(tmp_path)
    wheel.write_bytes(b"modified after pinning")
    with pytest.raises(ReleasedCheckerError, match="digest does not match"):
        validate_released_checker_runtime(
            identity, wheel, package_path=package, prefix=prefix, base_prefix=tmp_path / "system"
        )
    wheel, identity, prefix, _ = _wheel(tmp_path / "source")
    with pytest.raises(ReleasedCheckerError, match="source checkout"):
        validate_released_checker_runtime(
            identity,
            wheel,
            package_path=tmp_path / "source/venv/src/pdd/sync_core/released_checker.py",
            prefix=prefix,
            base_prefix=tmp_path / "system",
        )


def test_global_identity_requires_released_entrypoint_marker(monkeypatch) -> None:
    monkeypatch.setenv("PDD_RELEASED_CHECKER_WHEEL_SHA256", "c" * 64)
    monkeypatch.setenv("PDD_RELEASED_CHECKER_REF", "refs/tags/v1.0.0")
    monkeypatch.setenv(
        "PDD_RELEASED_CHECKER_WORKFLOW_IDENTITY",
        "promptdriven/pdd/.github/workflows/release.yml@refs/tags/v1.0.0",
    )
    monkeypatch.delenv("PDD_RELEASED_CHECKER_EXECUTION", raising=False)
    with pytest.raises(ValueError, match="pdd-sync-checker"):
        checker_identity_from_environment()
    monkeypatch.setenv("PDD_RELEASED_CHECKER_EXECUTION", "1")
    assert checker_identity_from_environment().wheel_sha256 == "c" * 64


def test_generic_release_pin_and_hashed_evidence_are_valid() -> None:
    evidence, report, profiles = _evidence()
    pin = ReleasePin.from_payload(_pin())

    assert pin.release_ref == "refs/tags/v1.2.3"
    assert evidence["machine_obligation_profile_units"] == ["pdd/prompts/machine_python.prompt"]
    assert evidence["human_attestation_only_profile_units"] == ["pdd/prompts/human_python.prompt"]
    assert len(evidence["canonical_report_sha256"]) == 64
    assert len(evidence["profiles_sha256"]) == 64
    validate_intermediate_release_evidence(evidence, report, profiles)


@pytest.mark.parametrize(
    ("field", "value"),
    [
        ("release_ref", "refs/tags/v1.2"),
        ("release_url", "https://github.com/attacker/pdd/releases/tag/v1.2.3"),
        ("wheel_url", "https://files.pythonhosted.org/packages/x/pdd_cli-9.9.9-py3-none-any.whl"),
        ("wheel_sha256", "A" * 64),
        ("repository_sha", "z" * 40),
        ("workflow_job_url", "https://github.com/promptdriven/pdd/actions/runs/999/job/67890"),
        ("workflow_identity", "promptdriven/pdd/.github/workflows/release.yml@main"),
    ],
)
def test_release_pin_rejects_inconsistent_identity(field: str, value: str) -> None:
    pin = _pin()
    pin[field] = value
    with pytest.raises(ReleasedCheckerEvidenceError):
        ReleasePin.from_payload(pin)


def test_release_pin_rejects_unknown_and_missing_keys() -> None:
    unknown = _pin()
    unknown["machine_verified"] = False
    missing = _pin()
    del missing["wheel_url"]
    with pytest.raises(ReleasedCheckerEvidenceError):
        ReleasePin.from_payload(unknown)
    with pytest.raises(ReleasedCheckerEvidenceError):
        ReleasePin.from_payload(missing)


@pytest.mark.parametrize(
    "mutate",
    [
        lambda report: report.__setitem__("schema_version", 999),
        lambda report: report.__setitem__("ok", True),
        lambda report: report.__setitem__("errors", []),
        lambda report: report["counts"].__setitem__("managed_units", 1),
        lambda report: report.__setitem__("unknown_key", True),
        lambda report: report["counts"].__setitem__("unknown_key", 1),
        lambda report: report["units"][0].__setitem__("unknown_key", True),
    ],
)
def test_report_schema_and_fail_closed_semantics_are_enforced(mutate) -> None:
    report = _report()
    mutate(report)
    with pytest.raises(ReleasedCheckerEvidenceError):
        build_intermediate_release_evidence(_pin(), report, _profiles(), exit_code=1)


def test_report_rejects_impossible_semantic_and_counter_combinations() -> None:
    invalid_semantic = _report()
    invalid_semantic["units"][0]["semantic"] = "PASS"
    stale_failed_count = _report()
    stale_failed_count["units"][0]["semantic"] = "UNKNOWN"
    invalid_candidate_count = _report()
    invalid_candidate_count["counts"]["invalid"] = 468

    for report in (invalid_semantic, stale_failed_count, invalid_candidate_count):
        with pytest.raises(ReleasedCheckerEvidenceError):
            build_intermediate_release_evidence(
                _pin(), report, _profiles(), exit_code=1
            )


def test_profile_obligation_schema_and_profile_digest_are_enforced() -> None:
    evidence, report, profiles = _evidence()
    malformed = deepcopy(profiles)
    malformed["profiles"][0]["obligations"][0]["unknown_key"] = True
    malformed_profile = deepcopy(profiles)
    malformed_profile["profiles"][0]["unknown_key"] = True
    changed = deepcopy(profiles)
    changed["profiles"][0]["language_id"] = "other"

    with pytest.raises(ReleasedCheckerEvidenceError):
        build_intermediate_release_evidence(_pin(), report, malformed, exit_code=1)
    with pytest.raises(ReleasedCheckerEvidenceError):
        build_intermediate_release_evidence(_pin(), report, malformed_profile, exit_code=1)
    with pytest.raises(ReleasedCheckerEvidenceError, match="profiles digest"):
        validate_intermediate_release_evidence(evidence, report, changed)


def test_changed_report_bytes_and_false_claims_are_rejected() -> None:
    evidence, report, profiles = _evidence()
    changed_report = deepcopy(report)
    changed_report["units"][0]["reason"] = "changed bytes"
    promoted = deepcopy(evidence)
    promoted["satisfies_gate_6"] = True
    mislabeled = deepcopy(evidence)
    mislabeled["machine_verified"] = False

    with pytest.raises(ReleasedCheckerEvidenceError, match="report digest"):
        validate_intermediate_release_evidence(evidence, changed_report, profiles)
    with pytest.raises(ReleasedCheckerEvidenceError):
        validate_intermediate_release_evidence(promoted, report, profiles)
    with pytest.raises(ReleasedCheckerEvidenceError):
        validate_intermediate_release_evidence(mislabeled, report, profiles)


def test_evidence_subcommand_requires_runtime_before_candidate_inputs(monkeypatch, tmp_path) -> None:
    wheel = tmp_path / "invalid.whl"
    wheel.write_bytes(b"not the declared wheel")
    monkeypatch.setenv("PDD_RELEASED_CHECKER_WHEEL_PATH", str(wheel))
    monkeypatch.setenv("PDD_RELEASED_CHECKER_WHEEL_SHA256", "c" * 64)
    monkeypatch.setenv("PDD_RELEASED_CHECKER_REF", "refs/tags/v1.2.3")
    monkeypatch.setenv(
        "PDD_RELEASED_CHECKER_WORKFLOW_IDENTITY",
        "promptdriven/pdd/.github/workflows/release.yml@refs/tags/v1.2.3",
    )

    with pytest.raises(ReleasedCheckerError, match="digest does not match"):
        _evidence_main(("--ledger-source", str(tmp_path / "malformed.yaml")))


def test_evidence_main_rejects_missing_runtime_provenance_before_arguments(monkeypatch) -> None:
    for name in (
        "PDD_RELEASED_CHECKER_WHEEL_PATH",
        "PDD_RELEASED_CHECKER_WHEEL_SHA256",
        "PDD_RELEASED_CHECKER_REF",
        "PDD_RELEASED_CHECKER_WORKFLOW_IDENTITY",
    ):
        monkeypatch.delenv(name, raising=False)
    monkeypatch.setattr(sys, "argv", ["pdd-sync-checker", "release-pin-evidence", "--bad"])

    with pytest.raises(ValueError, match="provenance is required"):
        main()
