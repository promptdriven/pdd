"""Tests for pinned released-checker runtime provenance."""

from copy import deepcopy
import hashlib
import json
from pathlib import Path
import zipfile

import pytest

from pdd.sync_core import CheckerIdentity, checker_identity_from_environment
from pdd.sync_core.released_checker import (
    EXACT_PYPI_PROVENANCE_URL,
    EXACT_RELEASE_REF,
    EXACT_RELEASE_SHA,
    EXACT_RELEASE_URL,
    EXACT_REPOSITORY_ID,
    EXACT_WHEEL_SHA256,
    EXACT_WHEEL_URL,
    EXACT_WORKFLOW_IDENTITY,
    EXACT_WORKFLOW_JOB_URL,
    EXACT_WORKFLOW_RUN_URL,
    ReleasePin,
    ReleasedCheckerEvidenceError,
    ReleasedCheckerError,
    build_intermediate_release_evidence,
    validate_intermediate_release_evidence,
    validate_released_checker_runtime,
)


def _wheel(tmp_path: Path) -> tuple[Path, CheckerIdentity, Path, Path]:
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
        "promptdriven/pdd/.github/workflows/global-sync.yml@refs/tags/v1.0.0",
    )
    return wheel, identity, prefix, package


def test_pinned_wheel_in_isolated_site_packages_is_accepted(tmp_path) -> None:
    wheel, identity, prefix, package = _wheel(tmp_path)
    validate_released_checker_runtime(
        identity,
        wheel,
        package_path=package,
        prefix=prefix,
        base_prefix=tmp_path / "system",
    )


def test_modified_wheel_is_rejected(tmp_path) -> None:
    wheel, identity, prefix, package = _wheel(tmp_path)
    wheel.write_bytes(b"modified after pinning")
    with pytest.raises(ReleasedCheckerError, match="digest does not match"):
        validate_released_checker_runtime(
            identity,
            wheel,
            package_path=package,
            prefix=prefix,
            base_prefix=tmp_path / "system",
        )


def test_source_checkout_import_is_rejected(tmp_path) -> None:
    wheel, identity, prefix, _package = _wheel(tmp_path)
    with pytest.raises(ReleasedCheckerError, match="source checkout"):
        validate_released_checker_runtime(
            identity,
            wheel,
            package_path=tmp_path / "venv/src/pdd/sync_core/released_checker.py",
            prefix=prefix,
            base_prefix=tmp_path / "system",
        )


def test_modified_installed_checker_is_rejected(tmp_path) -> None:
    wheel, identity, prefix, package = _wheel(tmp_path)
    package.write_bytes(b"modified installed checker\n")
    with pytest.raises(ReleasedCheckerError, match="differs from wheel"):
        validate_released_checker_runtime(
            identity,
            wheel,
            package_path=package,
            prefix=prefix,
            base_prefix=tmp_path / "system",
        )


def test_global_identity_requires_released_entrypoint_marker(monkeypatch) -> None:
    monkeypatch.setenv("PDD_RELEASED_CHECKER_WHEEL_SHA256", "c" * 64)
    monkeypatch.setenv("PDD_RELEASED_CHECKER_REF", "refs/tags/v1.0.0")
    monkeypatch.setenv(
        "PDD_RELEASED_CHECKER_WORKFLOW_IDENTITY",
        "promptdriven/pdd/.github/workflows/global-sync.yml@refs/tags/v1.0.0",
    )
    monkeypatch.delenv("PDD_RELEASED_CHECKER_EXECUTION", raising=False)
    with pytest.raises(ValueError, match="pdd-sync-checker"):
        checker_identity_from_environment()
    monkeypatch.setenv("PDD_RELEASED_CHECKER_EXECUTION", "1")
    assert checker_identity_from_environment().wheel_sha256 == "c" * 64


def _release_pin() -> dict[str, object]:
    return {
        "schema_version": 1,
        "repository": "promptdriven/pdd",
        "repository_id": EXACT_REPOSITORY_ID,
        "repository_sha": EXACT_RELEASE_SHA,
        "release_ref": EXACT_RELEASE_REF,
        "release_url": EXACT_RELEASE_URL,
        "wheel_url": EXACT_WHEEL_URL,
        "wheel_sha256": EXACT_WHEEL_SHA256,
        "workflow_run_url": EXACT_WORKFLOW_RUN_URL,
        "workflow_run_conclusion": "success",
        "workflow_job_url": EXACT_WORKFLOW_JOB_URL,
        "workflow_identity": EXACT_WORKFLOW_IDENTITY,
        "pypi_provenance_url": EXACT_PYPI_PROVENANCE_URL,
    }


def _profiles() -> dict[str, object]:
    return json.loads(Path(".pdd/verification-profiles.json").read_text(encoding="utf-8"))


def _report(profiles: dict[str, object]) -> dict[str, object]:
    profile_rows = profiles["profiles"]
    assert isinstance(profile_rows, list)
    return {
        "schema_version": 1,
        "repository_id": EXACT_REPOSITORY_ID,
        "base_sha": EXACT_RELEASE_SHA,
        "head_sha": EXACT_RELEASE_SHA,
        "counts": {
            "managed_units": 468,
            "verification_profile_complete": 468,
            "unaccounted_tracked_paths": 0,
        },
        "units": [
            {"subject": profile["prompt_path"]}
            for profile in profile_rows
            if isinstance(profile, dict)
        ],
    }


def _valid_evidence() -> tuple[dict[str, object], dict[str, object]]:
    profiles = _profiles()
    evidence = build_intermediate_release_evidence(
        _release_pin(), _report(profiles), profiles, exit_code=1
    )
    return evidence, profiles


def test_release_pin_and_intermediate_evidence_are_valid() -> None:
    evidence, profiles = _valid_evidence()

    pin = ReleasePin.from_payload(_release_pin())

    assert pin.wheel_sha256 == EXACT_WHEEL_SHA256
    assert evidence["evidence_classification"] == "intermediate-release-evidence"
    assert evidence["included_units"] == [
        "pdd/prompts/durable_sync_runner_python.prompt"
    ]
    assert len(evidence["excluded_units"]) == 467
    validate_intermediate_release_evidence(evidence, profiles)


@pytest.mark.parametrize(
    ("field", "value"),
    [
        ("wheel_url", "http://files.pythonhosted.org/not-the-pinned-wheel.whl"),
        ("release_url", "https://github.com/attacker/pdd/releases/tag/v0.0.306"),
        ("pypi_provenance_url", "https://pypi.org/integrity/pdd-cli/0.0.305/x"),
        ("wheel_sha256", "A" * 64),
        ("release_ref", "refs/tags/v0.0.307"),
        ("repository_sha", "0" * 40),
        ("workflow_identity", "promptdriven/pdd/.github/workflows/release.yml@main"),
        ("workflow_run_conclusion", "failure"),
        ("workflow_job_url", "https://github.com/promptdriven/pdd/actions/runs/1/job/2"),
    ],
)
def test_release_pin_rejects_url_digest_tag_sha_and_workflow_mismatch(
    field: str, value: str
) -> None:
    pin = _release_pin()
    pin[field] = value

    with pytest.raises(ReleasedCheckerEvidenceError):
        ReleasePin.from_payload(pin)


def test_release_pin_rejects_unknown_and_missing_schema_keys() -> None:
    unknown = _release_pin()
    unknown["machine_verified"] = False
    missing = _release_pin()
    del missing["wheel_url"]
    wrong_type = _release_pin()
    wrong_type["schema_version"] = True

    with pytest.raises(ReleasedCheckerEvidenceError):
        ReleasePin.from_payload(unknown)
    with pytest.raises(ReleasedCheckerEvidenceError):
        ReleasePin.from_payload(missing)
    with pytest.raises(ReleasedCheckerEvidenceError):
        ReleasePin.from_payload(wrong_type)


def test_intermediate_evidence_rejects_duplicate_overlap_and_missing_units() -> None:
    evidence, profiles = _valid_evidence()
    duplicate = deepcopy(evidence)
    duplicate["excluded_units"].append(duplicate["excluded_units"][0])
    overlap = deepcopy(evidence)
    overlap["excluded_units"][0] = overlap["included_units"][0]
    missing = deepcopy(evidence)
    missing["excluded_units"].pop()

    for malformed in (duplicate, overlap, missing):
        with pytest.raises(ReleasedCheckerEvidenceError):
            validate_intermediate_release_evidence(malformed, profiles)


def test_intermediate_evidence_rejects_false_narrowing_and_denominator_mismatch() -> None:
    evidence, profiles = _valid_evidence()
    narrowed = deepcopy(evidence)
    narrowed["included_units"] = []
    narrowed["excluded_units"] = sorted(
        narrowed["excluded_units"] + evidence["included_units"]
    )
    denominator = deepcopy(evidence)
    denominator["denominator"] = 1

    with pytest.raises(ReleasedCheckerEvidenceError):
        validate_intermediate_release_evidence(narrowed, profiles)
    with pytest.raises(ReleasedCheckerEvidenceError):
        validate_intermediate_release_evidence(denominator, profiles)


@pytest.mark.parametrize(
    "claim", [
        "global_completion",
        "satisfies_gate_6",
        "satisfies_gate_10",
        "certificate_a",
        "certificate_b",
    ],
)
def test_intermediate_evidence_rejects_completion_gate_and_certificate_claims(
    claim: str,
) -> None:
    evidence, profiles = _valid_evidence()
    evidence[claim] = True

    with pytest.raises(ReleasedCheckerEvidenceError):
        validate_intermediate_release_evidence(evidence, profiles)


def test_intermediate_evidence_rejects_unknown_schema_and_report_subject_mismatch() -> None:
    evidence, profiles = _valid_evidence()
    evidence["machine_verified"] = False
    wrong_exit_type, _ = _valid_evidence()
    wrong_exit_type["released_checker_exit_code"] = True
    report = _report(profiles)
    report["units"].pop()

    with pytest.raises(ReleasedCheckerEvidenceError):
        validate_intermediate_release_evidence(evidence, profiles)
    with pytest.raises(ReleasedCheckerEvidenceError):
        validate_intermediate_release_evidence(wrong_exit_type, profiles)
    with pytest.raises(ReleasedCheckerEvidenceError):
        build_intermediate_release_evidence(_release_pin(), report, profiles, exit_code=1)
