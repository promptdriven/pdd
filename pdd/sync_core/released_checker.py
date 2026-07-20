"""Entrypoint and releaseable evidence wrapper for released checker wheels."""
# pylint: disable=cyclic-import

from __future__ import annotations

import argparse
import base64
import hashlib
import json
import os
import re
import sys
import zipfile
from dataclasses import dataclass
from pathlib import Path, PurePosixPath
from typing import Any, Mapping, Sequence
from urllib.parse import urlparse

from .certificate import CheckerIdentity, checker_identity_from_environment
from .global_sync_ledger import load_unique_yaml


class ReleasedCheckerError(RuntimeError):
    """Raised when runtime provenance cannot prove released-wheel execution."""


class ReleasedCheckerEvidenceError(ValueError):
    """Raised when release-wrapper evidence is malformed or overclaims."""


RELEASE_PIN_SCHEMA_VERSION = 1
INTERMEDIATE_EVIDENCE_SCHEMA_VERSION = 1
EXPECTED_DEMANDED_VALIDATORS = ("pytest",)
_SHA256 = re.compile(r"[0-9a-f]{64}")
_SHA1 = re.compile(r"[0-9a-f]{40}")
_REPOSITORY = re.compile(r"[A-Za-z0-9_.-]+/[A-Za-z0-9_.-]+")
_REPOSITORY_ID = re.compile(
    r"[0-9a-f]{8}-[0-9a-f]{4}-[0-9a-f]{4}-[0-9a-f]{4}-[0-9a-f]{12}"
)
_RELEASE_REF = re.compile(r"refs/tags/v(\d+\.\d+\.\d+)")
_RELEASE_PIN_KEYS = frozenset(
    {
        "schema_version",
        "repository",
        "repository_id",
        "repository_sha",
        "release_ref",
        "release_url",
        "wheel_url",
        "wheel_sha256",
        "workflow_run_url",
        "workflow_run_conclusion",
        "workflow_job_url",
        "workflow_identity",
        "pypi_provenance_url",
    }
)
_INTERMEDIATE_EVIDENCE_KEYS = frozenset(
    {
        "schema_version",
        "evidence_classification",
        "release_pin",
        "base_sha",
        "head_sha",
        "released_checker_exit_code",
        "canonical_report_sha256",
        "profiles_sha256",
        "demanded_validator_ids",
        "report_counts",
        "machine_obligation_profile_units",
        "human_attestation_only_profile_units",
        "denominator",
        "global_completion",
        "satisfies_gate_6",
        "satisfies_gate_10",
        "certificate_a",
        "certificate_b",
    }
)
_REPORT_KEYS = frozenset(
    {
        "schema_version",
        "ok",
        "project_root",
        "repository_id",
        "base_sha",
        "head_sha",
        "manifest_digest",
        "counts",
        "errors",
        "recovery_required",
        "units",
    }
)
_REPORT_COUNT_KEYS = frozenset(
    {
        "unaccounted_tracked_paths",
        "managed_units",
        "protected_expected_managed_units",
        "managed_waivers",
        "invalid",
        "trusted_in_sync",
        "verification_profile_complete",
        "trusted_current_evidence",
        "drifted",
        "unbaselined",
        "corrupt",
        "unknown",
        "conflict",
        "failed",
    }
)
_UNIT_KEYS = frozenset(
    {
        "subject",
        "inventory",
        "baseline",
        "semantic",
        "in_sync",
        "evidence_complete",
        "changed_roles",
        "reason",
    }
)
_PROFILE_KEYS = frozenset(
    {"prompt_path", "language_id", "required_requirement_ids", "obligations"}
)
_HUMAN_OBLIGATION_KEYS = frozenset(
    {
        "obligation_id",
        "kind",
        "validator_id",
        "validator_config_digest",
        "requirement_ids",
        "artifact_paths",
        "required",
    }
)
_MACHINE_OBLIGATION_KEYS = _HUMAN_OBLIGATION_KEYS | frozenset({"code_under_test_paths"})
_INVENTORY_VALUES = frozenset({"MANAGED", "UNACCOUNTED"})
_BASELINE_VALUES = frozenset({"CURRENT", "DRIFTED", "UNBASELINED", "CORRUPT"})
_SEMANTIC_VALUES = frozenset({"VERIFIED", "FAILED", "UNKNOWN", "CONFLICT"})
_KNOWN_FAIL_CLOSED_ERROR = "protected base has no attestation trust policy"


def _require_closed_mapping(
    payload: object, expected_keys: frozenset[str], name: str
) -> Mapping[str, Any]:
    """Require a string-keyed mapping with precisely the reviewed schema."""
    if not isinstance(payload, Mapping) or set(payload) != expected_keys:
        raise ReleasedCheckerEvidenceError(f"{name} schema is closed and malformed")
    return payload


def _require_string(value: object, name: str) -> str:
    """Require a non-empty string without JSON/YAML coercion."""
    if not isinstance(value, str) or not value:
        raise ReleasedCheckerEvidenceError(f"{name} must be a non-empty string")
    return value


def _require_exact_int(value: object, expected: int, name: str) -> int:
    """Require one exact integer without accepting Python's boolean subtype."""
    if not isinstance(value, int) or isinstance(value, bool) or value != expected:
        raise ReleasedCheckerEvidenceError(f"{name} does not match the protected value")
    return value


def _require_sha(value: object, name: str, pattern: re.Pattern[str]) -> str:
    """Require a lowercase hexadecimal digest or commit."""
    if not isinstance(value, str) or pattern.fullmatch(value) is None:
        raise ReleasedCheckerEvidenceError(f"{name} is not a lowercase hexadecimal value")
    return value


def _canonical_sha256(payload: object) -> str:
    """Hash canonical JSON bytes for a complete checked report or profile payload."""
    try:
        encoded = json.dumps(payload, sort_keys=True, separators=(",", ":")).encode("utf-8")
    except (TypeError, ValueError) as exc:
        raise ReleasedCheckerEvidenceError("evidence input is not canonical JSON") from exc
    return hashlib.sha256(encoded).hexdigest()


def _https_url(value: object, host: str, path: str, name: str) -> str:
    """Require an exact HTTPS host and path with no ambiguous URL components."""
    url = _require_string(value, name)
    parsed = urlparse(url)
    invalid = (
        parsed.scheme != "https",
        parsed.netloc != host,
        parsed.path != path,
        parsed.username is not None,
        parsed.password is not None,
        parsed.port is not None,
        bool(parsed.query),
        bool(parsed.fragment),
    )
    if any(invalid):
        raise ReleasedCheckerEvidenceError(f"{name} host or path is invalid")
    return url


def _release_version(release_ref: object) -> tuple[str, str]:
    """Return a complete immutable tag and semantic version from one release ref."""
    ref = _require_string(release_ref, "release_ref")
    match = _RELEASE_REF.fullmatch(ref)
    if match is None:
        raise ReleasedCheckerEvidenceError("release_ref must be an immutable vX.Y.Z tag")
    return ref, match.group(1)


@dataclass(frozen=True)
class ReleasePin:  # pylint: disable=too-many-instance-attributes
    """A closed, internally consistent future released-checker pin."""

    repository: str
    repository_id: str
    repository_sha: str
    release_ref: str
    release_url: str
    wheel_url: str
    wheel_sha256: str
    workflow_run_url: str
    workflow_run_conclusion: str
    workflow_job_url: str
    workflow_identity: str
    pypi_provenance_url: str

    @classmethod
    def from_payload(cls, payload: object) -> "ReleasePin":
        # pylint: disable=too-many-locals
        """Decode a generic strict pin and validate all release identities agree."""
        values = _require_closed_mapping(payload, _RELEASE_PIN_KEYS, "release pin")
        _require_exact_int(
            values["schema_version"], RELEASE_PIN_SCHEMA_VERSION, "schema_version"
        )
        repository = _require_string(values["repository"], "repository")
        if _REPOSITORY.fullmatch(repository) is None:
            raise ReleasedCheckerEvidenceError("repository identity is invalid")
        repository_id = _require_sha(
            values["repository_id"], "repository_id", _REPOSITORY_ID
        )
        repository_sha = _require_sha(values["repository_sha"], "repository_sha", _SHA1)
        release_ref, version = _release_version(values["release_ref"])
        release_url = _https_url(
            values["release_url"],
            "github.com",
            f"/{repository}/releases/tag/v{version}",
            "release_url",
        )
        wheel_name = f"pdd_cli-{version}-py3-none-any.whl"
        wheel_url = _https_url(
            values["wheel_url"],
            "files.pythonhosted.org",
            "/packages/"
            + urlparse(_require_string(values["wheel_url"], "wheel_url")).path.split(
                "/packages/", 1
            )[-1],
            "wheel_url",
        )
        if not wheel_url.endswith(f"/{wheel_name}"):
            raise ReleasedCheckerEvidenceError("wheel_url version does not match release_ref")
        wheel_sha256 = _require_sha(values["wheel_sha256"], "wheel_sha256", _SHA256)
        run_url = _require_string(values["workflow_run_url"], "workflow_run_url")
        run_match = re.fullmatch(
            rf"https://github\.com/{re.escape(repository)}/actions/runs/(\d+)", run_url
        )
        if run_match is None:
            raise ReleasedCheckerEvidenceError("workflow_run_url does not match repository")
        job_url = _https_url(
            values["workflow_job_url"],
            "github.com",
            f"/{repository}/actions/runs/{run_match.group(1)}/job/"
            + _workflow_job_id(values["workflow_job_url"]),
            "workflow_job_url",
        )
        workflow_identity = _require_string(values["workflow_identity"], "workflow_identity")
        if workflow_identity != f"{repository}/.github/workflows/release.yml@{release_ref}":
            raise ReleasedCheckerEvidenceError("workflow_identity does not match release pin")
        provenance_url = _https_url(
            values["pypi_provenance_url"],
            "pypi.org",
            f"/integrity/pdd-cli/{version}/{wheel_name}/provenance",
            "pypi_provenance_url",
        )
        if values["workflow_run_conclusion"] != "success":
            raise ReleasedCheckerEvidenceError("release workflow is not a terminal success")
        return cls(
            repository,
            repository_id,
            repository_sha,
            release_ref,
            release_url,
            wheel_url,
            wheel_sha256,
            run_url,
            "success",
            job_url,
            workflow_identity,
            provenance_url,
        )

    def payload(self) -> dict[str, object]:
        """Return the canonical closed-schema representation for evidence."""
        return {"schema_version": RELEASE_PIN_SCHEMA_VERSION, **self.__dict__}

    def checker_identity(self) -> CheckerIdentity:
        """Return the exact released-wheel identity that must execute this wrapper."""
        return CheckerIdentity(
            self.wheel_sha256, self.release_ref, self.workflow_identity
        )


def _workflow_job_id(value: object) -> str:
    """Extract only a decimal job identifier from a reviewed GitHub job URL."""
    job_url = _require_string(value, "workflow_job_url")
    match = re.fullmatch(
        r"https://github\.com/[^/]+/[^/]+/actions/runs/\d+/job/(\d+)", job_url
    )
    if match is None:
        raise ReleasedCheckerEvidenceError("workflow_job_url is malformed")
    return match.group(1)


def _string_list(value: object, name: str) -> list[str]:
    """Require a list of non-empty strings without duplicate path aliases."""
    if not isinstance(value, list) or not all(
        isinstance(item, str) and item for item in value
    ):
        raise ReleasedCheckerEvidenceError(f"{name} must be a string list")
    if len(value) != len(set(value)):
        raise ReleasedCheckerEvidenceError(f"{name} contains duplicates")
    return value


def _profile_unit_sets(
    profiles_payload: object,
) -> tuple[tuple[str, ...], tuple[str, ...], tuple[str, ...]]:
    """Close protected profile schemas and classify every unit mechanically."""
    root = _require_closed_mapping(
        profiles_payload, frozenset({"schema_version", "profiles"}), "profiles"
    )
    _require_exact_int(root["schema_version"], 1, "profile schema_version")
    profiles = root["profiles"]
    if not isinstance(profiles, list) or not profiles:
        raise ReleasedCheckerEvidenceError("profiles are absent")
    machine_units: list[str] = []
    human_only_units: list[str] = []
    validators: set[str] = set()
    seen: set[str] = set()
    for profile in profiles:
        row = _require_closed_mapping(profile, _PROFILE_KEYS, "profile")
        prompt_path = _require_string(row["prompt_path"], "profile prompt_path")
        _require_string(row["language_id"], "profile language_id")
        _string_list(row["required_requirement_ids"], "profile required_requirement_ids")
        if prompt_path in seen:
            raise ReleasedCheckerEvidenceError("profiles contain duplicate prompt paths")
        seen.add(prompt_path)
        obligations = row["obligations"]
        if not isinstance(obligations, list) or not obligations:
            raise ReleasedCheckerEvidenceError("profile obligations are absent")
        has_machine_obligation = False
        for obligation in obligations:
            if not isinstance(obligation, Mapping):
                raise ReleasedCheckerEvidenceError("obligation must be a mapping")
            keys = frozenset(obligation)
            if keys not in {_HUMAN_OBLIGATION_KEYS, _MACHINE_OBLIGATION_KEYS}:
                raise ReleasedCheckerEvidenceError("obligation schema is closed and malformed")
            for key in (
                "obligation_id",
                "kind",
                "validator_id",
                "validator_config_digest",
            ):
                _require_string(obligation[key], f"obligation {key}")
            _string_list(obligation["requirement_ids"], "obligation requirement_ids")
            _string_list(obligation["artifact_paths"], "obligation artifact_paths")
            if keys == _MACHINE_OBLIGATION_KEYS:
                _string_list(
                    obligation["code_under_test_paths"], "obligation code_under_test_paths"
                )
            if not isinstance(obligation["required"], bool):
                raise ReleasedCheckerEvidenceError("obligation required must be boolean")
            if obligation["required"] and obligation["kind"] != "human-attestation":
                has_machine_obligation = True
                validators.add(obligation["validator_id"])
        (machine_units if has_machine_obligation else human_only_units).append(prompt_path)
    if tuple(sorted(validators)) != EXPECTED_DEMANDED_VALIDATORS:
        raise ReleasedCheckerEvidenceError("protected demanded validators do not match")
    return (
        tuple(sorted(machine_units)),
        tuple(sorted(human_only_units)),
        tuple(sorted(seen)),
    )


def _report_counts(report: Mapping[str, Any], denominator: int) -> dict[str, int]:
    """Require the full counter schema and its fail-closed denominator consistency."""
    counts = _require_closed_mapping(
        report["counts"], _REPORT_COUNT_KEYS, "report counts"
    )
    if any(
        not isinstance(value, int) or isinstance(value, bool) or value < 0
        for value in counts.values()
    ):
        raise ReleasedCheckerEvidenceError("report counts must be non-negative integers")
    if (
        counts["managed_units"] != denominator
        or counts["protected_expected_managed_units"] != denominator
        or counts["verification_profile_complete"] != denominator
        or counts["unaccounted_tracked_paths"] != 0
        or counts["failed"] < 1
    ):
        raise ReleasedCheckerEvidenceError(
            "report counts contradict the fail-closed denominator"
        )
    return dict(counts)


def _validated_report_unit(unit: object) -> Mapping[str, Any]:
    """Validate one serialized SyncVerdict and its cross-field invariants."""
    row = _require_closed_mapping(unit, _UNIT_KEYS, "report unit")
    _require_string(row["subject"], "report unit subject")
    if (
        row["inventory"] not in _INVENTORY_VALUES
        or row["baseline"] not in _BASELINE_VALUES
    ):
        raise ReleasedCheckerEvidenceError("report unit inventory or baseline is invalid")
    if row["semantic"] not in _SEMANTIC_VALUES:
        raise ReleasedCheckerEvidenceError("report unit semantic status is invalid")
    if not isinstance(row["in_sync"], bool) or not isinstance(
        row["evidence_complete"], bool
    ):
        raise ReleasedCheckerEvidenceError("report unit booleans are malformed")
    is_verified = row["semantic"] == "VERIFIED"
    expected_in_sync = (
        row["inventory"] == "MANAGED"
        and row["baseline"] == "CURRENT"
        and is_verified
        and row["evidence_complete"]
    )
    if (
        row["evidence_complete"] != is_verified
        or row["in_sync"] != expected_in_sync
        or (is_verified and not expected_in_sync)
    ):
        raise ReleasedCheckerEvidenceError(
            "report unit state contradicts the canonical in-sync predicate"
        )
    _string_list(row["changed_roles"], "report unit changed_roles")
    _require_string(row["reason"], "report unit reason")
    return row


def _validate_report(report: object, pin: ReleasePin, denominator: int) -> tuple[str, ...]:
    """Close every report layer and bind its exact false result to the pin."""
    payload = _require_closed_mapping(report, _REPORT_KEYS, "released checker report")
    _require_exact_int(payload["schema_version"], 1, "report schema_version")
    if payload["ok"] is not False:
        raise ReleasedCheckerEvidenceError("released checker report must fail closed")
    _require_string(payload["project_root"], "report project_root")
    _require_string(payload["manifest_digest"], "report manifest_digest")
    _require_sha(payload["manifest_digest"], "report manifest_digest", _SHA256)
    if payload["repository_id"] != pin.repository_id:
        raise ReleasedCheckerEvidenceError("report repository identity does not match pin")
    if payload["base_sha"] != pin.repository_sha or payload["head_sha"] != pin.repository_sha:
        raise ReleasedCheckerEvidenceError("report SHA does not match release pin")
    errors = _string_list(payload["errors"], "report errors")
    if _KNOWN_FAIL_CLOSED_ERROR not in errors:
        raise ReleasedCheckerEvidenceError("report does not contain the known fail-closed error")
    if not isinstance(payload["recovery_required"], list) or not all(
        isinstance(item, str) and item for item in payload["recovery_required"]
    ):
        raise ReleasedCheckerEvidenceError("report recovery_required is malformed")
    units = payload["units"]
    if not isinstance(units, list) or len(units) != denominator:
        raise ReleasedCheckerEvidenceError("report unit denominator does not match")
    subjects: list[str] = []
    derived_counts = {
        "managed_units": 0,
        "trusted_in_sync": 0,
        "trusted_current_evidence": 0,
        "drifted": 0,
        "unbaselined": 0,
        "corrupt": 0,
        "unknown": 0,
        "conflict": 0,
        "failed": 0,
    }
    for unit in units:
        row = _validated_report_unit(unit)
        subjects.append(row["subject"])
        derived_counts["managed_units"] += row["inventory"] == "MANAGED"
        derived_counts["trusted_in_sync"] += row["in_sync"]
        derived_counts["trusted_current_evidence"] += row["evidence_complete"]
        derived_counts["drifted"] += row["baseline"] == "DRIFTED"
        derived_counts["unbaselined"] += row["baseline"] == "UNBASELINED"
        derived_counts["corrupt"] += row["baseline"] == "CORRUPT"
        derived_counts["unknown"] += row["semantic"] == "UNKNOWN"
        derived_counts["conflict"] += row["semantic"] == "CONFLICT"
        derived_counts["failed"] += row["semantic"] == "FAILED"
    if len(subjects) != len(set(subjects)):
        raise ReleasedCheckerEvidenceError("report has duplicate subjects")
    counts = _report_counts(payload, denominator)
    if (
        any(counts[key] != value for key, value in derived_counts.items())
        or counts["invalid"] != 1
    ):
        raise ReleasedCheckerEvidenceError(
            "report counters do not match unit rows or the reviewed fail-closed result"
        )
    return tuple(sorted(subjects))


def build_intermediate_release_evidence(
    pin_payload: object, report: object, profiles_payload: object, *, exit_code: int
) -> dict[str, object]:
    """Build bounded descriptive evidence without promoting it to verification."""
    pin = ReleasePin.from_payload(pin_payload)
    machine_units, human_only_units, profile_subjects = _profile_unit_sets(profiles_payload)
    if not isinstance(exit_code, int) or isinstance(exit_code, bool) or exit_code != 1:
        raise ReleasedCheckerEvidenceError("released checker must fail closed with exit code 1")
    if _validate_report(report, pin, len(profile_subjects)) != profile_subjects:
        raise ReleasedCheckerEvidenceError("report subjects do not match protected profiles")
    if len(machine_units) + len(human_only_units) != len(profile_subjects):
        raise ReleasedCheckerEvidenceError("profile classifications do not cover the denominator")
    report_mapping = _require_closed_mapping(
        report, _REPORT_KEYS, "released checker report"
    )
    report_counts = _report_counts(report_mapping, len(profile_subjects))
    evidence = {
        "schema_version": INTERMEDIATE_EVIDENCE_SCHEMA_VERSION,
        "evidence_classification": "intermediate-release-evidence",
        "release_pin": pin.payload(),
        "base_sha": pin.repository_sha,
        "head_sha": pin.repository_sha,
        "released_checker_exit_code": exit_code,
        "canonical_report_sha256": _canonical_sha256(report),
        "profiles_sha256": _canonical_sha256(profiles_payload),
        "demanded_validator_ids": list(EXPECTED_DEMANDED_VALIDATORS),
        "report_counts": report_counts,
        "machine_obligation_profile_units": list(machine_units),
        "human_attestation_only_profile_units": list(human_only_units),
        "denominator": len(profile_subjects),
        "global_completion": False,
        "satisfies_gate_6": False,
        "satisfies_gate_10": False,
        "certificate_a": False,
        "certificate_b": False,
    }
    validate_intermediate_release_evidence(evidence, report, profiles_payload)
    return evidence


def validate_intermediate_release_evidence(
    payload: object, report: object, profiles_payload: object
) -> None:
    """Reject narrowing, mutable report bytes, and all promotion claims."""
    values = _require_closed_mapping(
        payload, _INTERMEDIATE_EVIDENCE_KEYS, "intermediate evidence"
    )
    _require_exact_int(
        values["schema_version"], INTERMEDIATE_EVIDENCE_SCHEMA_VERSION, "evidence schema_version"
    )
    if values["evidence_classification"] != "intermediate-release-evidence":
        raise ReleasedCheckerEvidenceError("evidence classification is invalid")
    pin = ReleasePin.from_payload(values["release_pin"])
    if values["base_sha"] != pin.repository_sha or values["head_sha"] != pin.repository_sha:
        raise ReleasedCheckerEvidenceError("evidence SHA does not match release pin")
    if (
        values["released_checker_exit_code"] != 1
        or isinstance(values["released_checker_exit_code"], bool)
    ):
        raise ReleasedCheckerEvidenceError("released checker exit code must be 1")
    if values["canonical_report_sha256"] != _canonical_sha256(report):
        raise ReleasedCheckerEvidenceError("canonical report digest does not match")
    if values["profiles_sha256"] != _canonical_sha256(profiles_payload):
        raise ReleasedCheckerEvidenceError("profiles digest does not match")
    machine_units, human_only_units, profile_subjects = _profile_unit_sets(profiles_payload)
    if _validate_report(report, pin, len(profile_subjects)) != profile_subjects:
        raise ReleasedCheckerEvidenceError("report subjects do not match protected profiles")
    if values["demanded_validator_ids"] != list(EXPECTED_DEMANDED_VALIDATORS):
        raise ReleasedCheckerEvidenceError("demanded validators do not match")
    if values["report_counts"] != _report_counts(
        _require_closed_mapping(report, _REPORT_KEYS, "released checker report"),
        len(profile_subjects),
    ):
        raise ReleasedCheckerEvidenceError("evidence report counts do not match")
    if (
        values["machine_obligation_profile_units"] != list(machine_units)
        or values["human_attestation_only_profile_units"] != list(human_only_units)
        or values["denominator"] != len(profile_subjects)
        or len(machine_units) + len(human_only_units) != values["denominator"]
    ):
        raise ReleasedCheckerEvidenceError("profile classification denominator is invalid")
    for claim in (
        "global_completion",
        "satisfies_gate_6",
        "satisfies_gate_10",
        "certificate_a",
        "certificate_b",
    ):
        if values[claim] is not False:
            raise ReleasedCheckerEvidenceError(f"intermediate evidence must not claim {claim}")


def _sha256(path: Path) -> str:
    digest = hashlib.sha256()
    with path.open("rb") as handle:
        for chunk in iter(lambda: handle.read(1024 * 1024), b""):
            digest.update(chunk)
    return digest.hexdigest()


def _verify_standalone_wheel_record(archive: zipfile.ZipFile) -> None:
    """Reject a standalone archive whose RECORD does not bind every regular member."""
    members = [item for item in archive.infolist() if not item.is_dir()]
    names = [item.filename for item in members]
    if len(names) != len(set(names)) or any(
        "\\" in name or name.startswith("/") or ".." in PurePosixPath(name).parts
        for name in names
    ):
        raise ReleasedCheckerError("released checker wheel has unsafe members")
    record_names = [name for name in names if name.endswith(".dist-info/RECORD")]
    if len(record_names) != 1:
        raise ReleasedCheckerError("released checker wheel RECORD is invalid")
    try:
        parsed_rows = [
            line.split(",")
            for line in archive.read(record_names[0]).decode("ascii").splitlines()
        ]
    except (KeyError, UnicodeDecodeError):
        raise ReleasedCheckerError("released checker wheel RECORD is invalid") from None
    if any(len(parts) != 3 for parts in parsed_rows):
        raise ReleasedCheckerError("released checker wheel RECORD is invalid")
    rows = {parts[0]: (parts[1], parts[2]) for parts in parsed_rows}
    if (
        set(rows) != set(names)
        or len(rows) != len(names)
        or len(rows) != len(parsed_rows)
    ):
        raise ReleasedCheckerError("released checker wheel RECORD is not closed")
    for name in names:
        encoded, size = rows[name]
        if name == record_names[0]:
            if encoded or size:
                raise ReleasedCheckerError("released checker wheel RECORD is invalid")
            continue
        content = archive.read(name)
        hash_value = base64.urlsafe_b64encode(
            hashlib.sha256(content).digest()
        ).rstrip(b"=").decode("ascii")
        if encoded != f"sha256={hash_value}" or size != str(len(content)):
            raise ReleasedCheckerError("released checker wheel RECORD does not match bytes")


def _verify_installed_package(  # pylint: disable=too-many-locals
    wheel: Path, installed_package: Path
) -> None:
    """Compare every installed checker member byte-for-byte with the pinned wheel."""
    package_parts = installed_package.parts
    package_name = "pdd_sync_checker" if "pdd_sync_checker" in package_parts else "pdd"
    package_index = max(index for index, part in enumerate(package_parts) if part == package_name)
    site_packages = Path(*package_parts[:package_index])
    try:
        with zipfile.ZipFile(wheel) as archive:
            if package_name == "pdd_sync_checker":
                _verify_standalone_wheel_record(archive)
                if any(name.startswith("pdd/") for name in archive.namelist()):
                    raise ReleasedCheckerError("released checker wheel contains the pdd package")
            wheel_members = {
                name: archive.read(name)
                for name in archive.namelist()
                if name.startswith(f"{package_name}/") and not name.endswith("/")
            }
    except (OSError, zipfile.BadZipFile, KeyError) as exc:
        raise ReleasedCheckerError("released checker wheel cannot be inspected") from exc
    if not wheel_members:
        raise ReleasedCheckerError("released checker wheel contains no checker package")
    for member, expected in wheel_members.items():
        installed = site_packages / PurePosixPath(member)
        if installed.is_symlink() or not installed.is_file():
            raise ReleasedCheckerError(f"installed checker member is unsafe: {member}")
        if installed.read_bytes() != expected:
            raise ReleasedCheckerError(f"installed checker member differs from wheel: {member}")
    if package_name == "pdd_sync_checker":
        from .standalone_package import installed_checker_runtime_lock  # pylint: disable=import-outside-toplevel

        installed_checker_runtime_lock(wheel, installed_package)


def validate_released_checker_runtime(
    identity: CheckerIdentity,
    wheel_path: Path,
    *,
    package_path: Path | None = None,
    prefix: Path | None = None,
    base_prefix: Path | None = None,
) -> None:
    """Fail closed unless this process came from the pinned wheel in a venv."""
    wheel = Path(wheel_path)
    if wheel.is_symlink() or not wheel.is_file() or wheel.suffix != ".whl":
        raise ReleasedCheckerError("released checker wheel path is unsafe")
    if _sha256(wheel) != identity.wheel_sha256:
        raise ReleasedCheckerError("released checker wheel digest does not match")
    runtime_prefix = Path(prefix or sys.prefix).resolve()
    runtime_base = Path(base_prefix or sys.base_prefix).resolve()
    installed_package = Path(package_path or __file__).resolve()
    if runtime_prefix == runtime_base:
        raise ReleasedCheckerError("released checker requires an isolated environment")
    try:
        installed_package.relative_to(runtime_prefix)
    except ValueError as exc:
        raise ReleasedCheckerError(
            "released checker package is outside the isolated environment"
        ) from exc
    if "site-packages" not in installed_package.parts:
        raise ReleasedCheckerError("released checker was imported from a source checkout")
    _verify_installed_package(wheel, installed_package)


def _validated_runtime_identity() -> CheckerIdentity:
    """Validate the same installed-wheel provenance before either checker mode runs."""
    identity = checker_identity_from_environment(require_execution_marker=False)
    wheel_value = os.environ.get("PDD_RELEASED_CHECKER_WHEEL_PATH")
    if not wheel_value:
        raise ReleasedCheckerError("PDD_RELEASED_CHECKER_WHEEL_PATH is required")
    validate_released_checker_runtime(identity, Path(wheel_value))
    return identity


def _load_json(path: Path) -> object:
    """Load a regular JSON file only after released runtime provenance is proved."""
    if path.is_symlink() or not path.is_file():
        raise ReleasedCheckerEvidenceError(f"JSON input must be a regular file: {path}")
    try:
        return json.loads(path.read_text(encoding="utf-8"))
    except (OSError, UnicodeDecodeError, json.JSONDecodeError) as exc:
        raise ReleasedCheckerEvidenceError(f"cannot parse JSON input {path}") from exc


def _evidence_main(arguments: Sequence[str]) -> None:
    """Generate evidence only from a provenance-validated installed wrapper wheel."""
    identity = _validated_runtime_identity()
    parser = argparse.ArgumentParser(description="Generate released-wrapper intermediate evidence")
    parser.add_argument("--ledger-source", required=True, type=Path)
    parser.add_argument("--report", required=True, type=Path)
    parser.add_argument("--profiles", required=True, type=Path)
    parser.add_argument("--released-checker-exit-code", required=True, type=int)
    parser.add_argument("--output", required=True, type=Path)
    args = parser.parse_args(arguments)
    ledger = load_unique_yaml(args.ledger_source)
    steps = ledger.get("steps")
    if not isinstance(steps, list) or len(steps) < 2 or not isinstance(steps[1], Mapping):
        raise ReleasedCheckerEvidenceError("reviewed source does not contain Gate 2")
    pin = ReleasePin.from_payload(steps[1].get("release_pin"))
    if pin.checker_identity() != identity:
        raise ReleasedCheckerEvidenceError("release pin does not match executing wheel identity")
    report = _load_json(args.report)
    profiles = _load_json(args.profiles)
    evidence = build_intermediate_release_evidence(
        pin.payload(), report, profiles, exit_code=args.released_checker_exit_code
    )
    args.output.parent.mkdir(parents=True, exist_ok=True)
    args.output.write_text(json.dumps(evidence, indent=2, sort_keys=True) + "\n", encoding="utf-8")
    validate_intermediate_release_evidence(evidence, report, profiles)


def main() -> None:
    """Run the direct checker CLI without importing the PDD command graph."""
    from .checker_cli import main as checker_main  # pylint: disable=import-outside-toplevel

    raise SystemExit(checker_main(sys.argv[1:]))


if __name__ == "__main__":
    main()
