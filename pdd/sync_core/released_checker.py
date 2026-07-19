"""Entrypoint for certification from a pinned independently released wheel."""

from __future__ import annotations

import argparse
import hashlib
import importlib
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
    """Raised when the bounded release-pin evidence is malformed or overclaims."""


RELEASE_PIN_SCHEMA_VERSION = 1
INTERMEDIATE_EVIDENCE_SCHEMA_VERSION = 1
EXACT_RELEASE_SHA = "89218463d33baa58fdfeb37599e49a6e2cd13283"
EXACT_RELEASE_REF = "refs/tags/v0.0.306"
EXACT_REPOSITORY = "promptdriven/pdd"
EXACT_REPOSITORY_ID = "3b4d7b1c-d6cc-4752-ba93-6b98d1a710e0"
EXACT_WHEEL_URL = (
    "https://files.pythonhosted.org/packages/"
    + "a6/66/562f6ae454c29ee6dcd064e1952f1029ca0a891cc379623ec5d22bff8aac/"
    + "pdd_cli-0.0.306-py3-none-any.whl"
)
EXACT_WHEEL_SHA256 = "e666ab38ce49413ff90c24f96fcbd9dbd01f73e4e38a3c6eb4391dd18369784d"
EXACT_RELEASE_URL = "https://github.com/promptdriven/pdd/releases/tag/v0.0.306"
EXACT_WORKFLOW_RUN_URL = "https://github.com/promptdriven/pdd/actions/runs/29691352403"
EXACT_WORKFLOW_JOB_URL = (
    "https://github.com/promptdriven/pdd/actions/runs/" + "29691352403/job/88204544350"
)
EXACT_WORKFLOW_IDENTITY = (
    "promptdriven/pdd/.github/workflows/release.yml@refs/tags/v0.0.306"
)
EXACT_PYPI_PROVENANCE_URL = (
    "https://pypi.org/integrity/pdd-cli/0.0.306/"
    "pdd_cli-0.0.306-py3-none-any.whl/provenance"
)
EXPECTED_MANAGED_DENOMINATOR = 468
EXPECTED_DEMANDED_VALIDATORS = ("pytest",)
_SHA256 = re.compile(r"[0-9a-f]{64}")
_SHA1 = re.compile(r"[0-9a-f]{40}")
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
        "demanded_validator_ids",
        "report_counts",
        "included_units",
        "excluded_units",
        "denominator",
        "global_completion",
        "satisfies_gate_6",
        "satisfies_gate_10",
        "certificate_a",
        "certificate_b",
    }
)
_REPORT_COUNTS_KEYS = frozenset(
    {
        "managed_units",
        "verification_profile_complete",
        "unaccounted_tracked_paths",
    }
)


def _require_closed_mapping(
    payload: object, expected_keys: frozenset[str], name: str
) -> Mapping[str, Any]:
    """Require a string-keyed mapping with precisely the reviewed schema."""
    if not isinstance(payload, Mapping) or set(payload) != expected_keys:
        raise ReleasedCheckerEvidenceError(f"{name} schema is closed and malformed")
    return payload


def _require_exact_string(value: object, expected: str, name: str) -> str:
    """Require one exact string without YAML/JSON coercion."""
    if not isinstance(value, str) or value != expected:
        raise ReleasedCheckerEvidenceError(f"{name} does not match the protected pin")
    return value


def _require_exact_int(value: object, expected: int, name: str) -> int:
    """Require one exact integer without accepting Python's boolean subtype."""
    if not isinstance(value, int) or isinstance(value, bool) or value != expected:
        raise ReleasedCheckerEvidenceError(f"{name} does not match the protected pin")
    return value


def _require_sha(value: object, expected: str, name: str, pattern: re.Pattern[str]) -> str:
    """Require a lowercase hexadecimal digest or commit before comparing it."""
    if not isinstance(value, str) or pattern.fullmatch(value) is None or value != expected:
        raise ReleasedCheckerEvidenceError(f"{name} does not match the protected pin")
    return value


def _require_https_url(value: object, expected: str, name: str) -> str:
    """Require an exact HTTPS URL including its reviewed host and path."""
    if not isinstance(value, str):
        raise ReleasedCheckerEvidenceError(f"{name} must be an HTTPS URL")
    parsed = urlparse(value)
    expected_parsed = urlparse(expected)
    invalid = (
        parsed.scheme != "https",
        parsed.username is not None,
        parsed.password is not None,
        parsed.port is not None,
        bool(parsed.query),
        bool(parsed.fragment),
        parsed.netloc != expected_parsed.netloc,
        parsed.path != expected_parsed.path,
        value != expected,
    )
    if any(invalid):
        raise ReleasedCheckerEvidenceError(f"{name} host or path does not match the pin")
    return value


@dataclass(frozen=True)
class ReleasePin:  # pylint: disable=too-many-instance-attributes
    """The sole reviewed v0.0.306 checker release identity accepted by Gate 2."""

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
        """Decode and strictly validate the closed reviewed release-pin schema."""
        values = _require_closed_mapping(payload, _RELEASE_PIN_KEYS, "release pin")
        _require_exact_int(
            values["schema_version"], RELEASE_PIN_SCHEMA_VERSION, "release pin schema_version"
        )
        return cls(
            repository=_require_exact_string(
                values["repository"], EXACT_REPOSITORY, "repository"
            ),
            repository_id=_require_exact_string(
                values["repository_id"], EXACT_REPOSITORY_ID, "repository_id"
            ),
            repository_sha=_require_sha(
                values["repository_sha"], EXACT_RELEASE_SHA, "repository_sha", _SHA1
            ),
            release_ref=_require_exact_string(
                values["release_ref"], EXACT_RELEASE_REF, "release_ref"
            ),
            release_url=_require_https_url(
                values["release_url"], EXACT_RELEASE_URL, "release_url"
            ),
            wheel_url=_require_https_url(values["wheel_url"], EXACT_WHEEL_URL, "wheel_url"),
            wheel_sha256=_require_sha(
                values["wheel_sha256"], EXACT_WHEEL_SHA256, "wheel_sha256", _SHA256
            ),
            workflow_run_url=_require_https_url(
                values["workflow_run_url"], EXACT_WORKFLOW_RUN_URL, "workflow_run_url"
            ),
            workflow_run_conclusion=_require_exact_string(
                values["workflow_run_conclusion"], "success", "workflow_run_conclusion"
            ),
            workflow_job_url=_require_https_url(
                values["workflow_job_url"], EXACT_WORKFLOW_JOB_URL, "workflow_job_url"
            ),
            workflow_identity=_require_exact_string(
                values["workflow_identity"], EXACT_WORKFLOW_IDENTITY, "workflow_identity"
            ),
            pypi_provenance_url=_require_https_url(
                values["pypi_provenance_url"],
                EXACT_PYPI_PROVENANCE_URL,
                "pypi_provenance_url",
            ),
        )

    def payload(self) -> dict[str, object]:
        """Return the canonical closed-schema representation for an evidence file."""
        return {"schema_version": RELEASE_PIN_SCHEMA_VERSION, **self.__dict__}


def _profile_unit_sets(profiles_payload: object) -> tuple[tuple[str, ...], tuple[str, ...]]:
    """Mechanically separate required machine and human-only profile subjects."""
    if not isinstance(profiles_payload, Mapping) or set(profiles_payload) != {
        "schema_version",
        "profiles",
    }:
        raise ReleasedCheckerEvidenceError("protected verification profiles are malformed")
    _require_exact_int(profiles_payload.get("schema_version"), 1, "profile schema_version")
    profiles = profiles_payload.get("profiles")
    if not isinstance(profiles, list):
        raise ReleasedCheckerEvidenceError("protected verification profiles are absent")
    included: list[str] = []
    excluded: list[str] = []
    seen: set[str] = set()
    validator_ids: set[str] = set()
    for profile in profiles:
        if not isinstance(profile, Mapping) or set(profile) != {
            "prompt_path", "language_id", "required_requirement_ids", "obligations"
        }:
            raise ReleasedCheckerEvidenceError("verification profile schema is malformed")
        prompt_path = profile.get("prompt_path")
        obligations = profile.get("obligations")
        if (
            not isinstance(prompt_path, str)
            or not prompt_path
            or prompt_path in seen
            or not isinstance(obligations, list)
        ):
            raise ReleasedCheckerEvidenceError("verification profile subject is malformed")
        seen.add(prompt_path)
        required_machine = False
        for obligation in obligations:
            if not isinstance(obligation, Mapping):
                raise ReleasedCheckerEvidenceError("verification obligation is malformed")
            required = obligation.get("required")
            kind = obligation.get("kind")
            validator = obligation.get("validator_id")
            if not isinstance(required, bool) or not isinstance(kind, str) or not isinstance(
                validator, str
            ):
                raise ReleasedCheckerEvidenceError("verification obligation identity is malformed")
            if required and kind != "human-attestation":
                required_machine = True
                validator_ids.add(validator)
        (included if required_machine else excluded).append(prompt_path)
    if tuple(sorted(validator_ids)) != EXPECTED_DEMANDED_VALIDATORS:
        raise ReleasedCheckerEvidenceError("protected demanded validators do not match")
    if len(seen) != EXPECTED_MANAGED_DENOMINATOR:
        raise ReleasedCheckerEvidenceError("protected profile denominator does not match")
    return tuple(sorted(included)), tuple(sorted(excluded))


def _report_subjects(report: object) -> tuple[str, ...]:
    """Validate the released report's identity and return every reported subject once."""
    if not isinstance(report, Mapping):
        raise ReleasedCheckerEvidenceError("released checker report is malformed")
    _require_sha(report.get("base_sha"), EXACT_RELEASE_SHA, "report base_sha", _SHA1)
    _require_sha(report.get("head_sha"), EXACT_RELEASE_SHA, "report head_sha", _SHA1)
    _require_exact_string(
        report.get("repository_id"), EXACT_REPOSITORY_ID, "report repository identity"
    )
    units = report.get("units")
    if not isinstance(units, list):
        raise ReleasedCheckerEvidenceError("released checker report units are absent")
    subjects: list[str] = []
    for unit in units:
        if not isinstance(unit, Mapping) or not isinstance(unit.get("subject"), str):
            raise ReleasedCheckerEvidenceError("released checker report unit subject is malformed")
        subjects.append(unit["subject"])
    if len(set(subjects)) != len(subjects):
        raise ReleasedCheckerEvidenceError("released checker report has duplicate subjects")
    return tuple(sorted(subjects))


def _report_counts(report: object) -> dict[str, int]:
    """Extract the narrow report counters that this intermediate layer may claim."""
    if not isinstance(report, Mapping) or not isinstance(report.get("counts"), Mapping):
        raise ReleasedCheckerEvidenceError("released checker report counts are malformed")
    counts = report["counts"]
    selected = {key: counts.get(key) for key in _REPORT_COUNTS_KEYS}
    expected = {
        "managed_units": EXPECTED_MANAGED_DENOMINATOR,
        "verification_profile_complete": EXPECTED_MANAGED_DENOMINATOR,
        "unaccounted_tracked_paths": 0,
    }
    if selected != expected or any(isinstance(value, bool) for value in selected.values()):
        raise ReleasedCheckerEvidenceError("released checker report counts do not match")
    return expected


def build_intermediate_release_evidence(
    pin_payload: object, report: object, profiles_payload: object, *, exit_code: int
) -> dict[str, object]:
    """Build non-promoting intermediate evidence from a released checker report."""
    pin = ReleasePin.from_payload(pin_payload)
    included, excluded = _profile_unit_sets(profiles_payload)
    subjects = _report_subjects(report)
    if subjects != tuple(sorted((*included, *excluded))):
        raise ReleasedCheckerEvidenceError("released report subjects do not match profiles")
    if exit_code != 1:
        raise ReleasedCheckerEvidenceError("released checker must fail closed with exit code 1")
    evidence = {
        "schema_version": INTERMEDIATE_EVIDENCE_SCHEMA_VERSION,
        "evidence_classification": "intermediate-release-evidence",
        "release_pin": pin.payload(),
        "base_sha": EXACT_RELEASE_SHA,
        "head_sha": EXACT_RELEASE_SHA,
        "released_checker_exit_code": exit_code,
        "demanded_validator_ids": list(EXPECTED_DEMANDED_VALIDATORS),
        "report_counts": _report_counts(report),
        "included_units": list(included),
        "excluded_units": list(excluded),
        "denominator": EXPECTED_MANAGED_DENOMINATOR,
        "global_completion": False,
        "satisfies_gate_6": False,
        "satisfies_gate_10": False,
        "certificate_a": False,
        "certificate_b": False,
    }
    validate_intermediate_release_evidence(evidence, profiles_payload)
    return evidence


def validate_intermediate_release_evidence(
    payload: object, profiles_payload: object
) -> None:
    """Reject narrowing, promotion, or certificate claims in intermediate evidence."""
    values = _require_closed_mapping(
        payload, _INTERMEDIATE_EVIDENCE_KEYS, "intermediate release evidence"
    )
    _require_exact_int(
        values["schema_version"],
        INTERMEDIATE_EVIDENCE_SCHEMA_VERSION,
        "intermediate evidence schema_version",
    )
    _require_exact_string(
        values["evidence_classification"],
        "intermediate-release-evidence",
        "evidence_classification",
    )
    ReleasePin.from_payload(values["release_pin"])
    _require_sha(values["base_sha"], EXACT_RELEASE_SHA, "evidence base_sha", _SHA1)
    _require_sha(values["head_sha"], EXACT_RELEASE_SHA, "evidence head_sha", _SHA1)
    if (
        not isinstance(values["released_checker_exit_code"], int)
        or isinstance(values["released_checker_exit_code"], bool)
        or values["released_checker_exit_code"] != 1
    ):
        raise ReleasedCheckerEvidenceError("released checker exit code must be 1")
    if values["demanded_validator_ids"] != list(EXPECTED_DEMANDED_VALIDATORS):
        raise ReleasedCheckerEvidenceError("demanded validators do not match")
    counts = _require_closed_mapping(values["report_counts"], _REPORT_COUNTS_KEYS, "report counts")
    if counts != {
        "managed_units": EXPECTED_MANAGED_DENOMINATOR,
        "verification_profile_complete": EXPECTED_MANAGED_DENOMINATOR,
        "unaccounted_tracked_paths": 0,
    }:
        raise ReleasedCheckerEvidenceError("intermediate report counts do not match")
    included, excluded = _profile_unit_sets(profiles_payload)
    claimed_included = values["included_units"]
    claimed_excluded = values["excluded_units"]
    if not isinstance(claimed_included, list) or not isinstance(claimed_excluded, list):
        raise ReleasedCheckerEvidenceError("intermediate evidence unit classification is invalid")
    if not all(isinstance(unit, str) for unit in claimed_included + claimed_excluded):
        raise ReleasedCheckerEvidenceError("intermediate evidence unit classification is invalid")
    if (
        tuple(claimed_included) != included
        or tuple(claimed_excluded) != excluded
        or set(claimed_included).intersection(claimed_excluded)
    ):
        raise ReleasedCheckerEvidenceError("intermediate evidence unit classification is invalid")
    if (
        values["denominator"] != EXPECTED_MANAGED_DENOMINATOR
        or len(claimed_included) != 1
        or len(claimed_excluded) != EXPECTED_MANAGED_DENOMINATOR - 1
        or len(claimed_included) + len(claimed_excluded) != values["denominator"]
    ):
        raise ReleasedCheckerEvidenceError("intermediate evidence denominator is invalid")
    for claim in (
        "global_completion",
        "satisfies_gate_6",
        "satisfies_gate_10",
        "certificate_a",
        "certificate_b",
    ):
        if values[claim] is not False:
            raise ReleasedCheckerEvidenceError(f"intermediate evidence must not claim {claim}")


def _load_json(path: Path) -> object:
    """Load a regular JSON file for the evidence wrapper CLI."""
    if path.is_symlink() or not path.is_file():
        raise ReleasedCheckerEvidenceError(f"JSON input must be a regular file: {path}")
    try:
        return json.loads(path.read_text(encoding="utf-8"))
    except (OSError, UnicodeDecodeError, json.JSONDecodeError) as exc:
        raise ReleasedCheckerEvidenceError(f"cannot parse JSON input {path}") from exc


def _evidence_main(arguments: Sequence[str]) -> None:
    """Generate and revalidate the narrowly scoped intermediate evidence JSON."""
    parser = argparse.ArgumentParser(description="Validate the Gate 2 release pin")
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
    pin = steps[1].get("release_pin")
    evidence = build_intermediate_release_evidence(
        pin,
        _load_json(args.report),
        _load_json(args.profiles),
        exit_code=args.released_checker_exit_code,
    )
    args.output.parent.mkdir(parents=True, exist_ok=True)
    args.output.write_text(json.dumps(evidence, indent=2, sort_keys=True) + "\n", encoding="utf-8")
    validate_intermediate_release_evidence(evidence, _load_json(args.profiles))


def _sha256(path: Path) -> str:
    digest = hashlib.sha256()
    with path.open("rb") as handle:
        for chunk in iter(lambda: handle.read(1024 * 1024), b""):
            digest.update(chunk)
    return digest.hexdigest()


def _verify_installed_package(wheel: Path, installed_package: Path) -> None:
    """Compare every installed PDD member byte-for-byte with the pinned wheel."""
    package_parts = installed_package.parts
    package_index = max(
        index for index, part in enumerate(package_parts) if part == "pdd"
    )
    site_packages = Path(*package_parts[:package_index])
    try:
        with zipfile.ZipFile(wheel) as archive:
            wheel_members = {
                name: archive.read(name)
                for name in archive.namelist()
                if name.startswith("pdd/") and not name.endswith("/")
            }
    except (OSError, zipfile.BadZipFile, KeyError) as exc:
        raise ReleasedCheckerError("released checker wheel cannot be inspected") from exc
    if not wheel_members:
        raise ReleasedCheckerError("released checker wheel contains no PDD package")
    for member, expected in wheel_members.items():
        installed = site_packages / PurePosixPath(member)
        if installed.is_symlink() or not installed.is_file():
            raise ReleasedCheckerError(f"installed checker member is unsafe: {member}")
        if installed.read_bytes() != expected:
            raise ReleasedCheckerError(f"installed checker member differs from wheel: {member}")


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


def main() -> None:
    """Verify runtime provenance, then run the strict global certify command."""
    if len(sys.argv) > 1 and sys.argv[1] == "release-pin-evidence":
        _evidence_main(sys.argv[2:])
        return
    identity = checker_identity_from_environment(require_execution_marker=False)
    wheel_value = os.environ.get("PDD_RELEASED_CHECKER_WHEEL_PATH")
    if not wheel_value:
        raise ReleasedCheckerError("PDD_RELEASED_CHECKER_WHEEL_PATH is required")
    validate_released_checker_runtime(identity, Path(wheel_value))
    os.environ["PDD_RELEASED_CHECKER_EXECUTION"] = "1"

    cli = importlib.import_module("pdd.cli").cli

    cli.main(
        args=["certify", *sys.argv[1:]],
        prog_name="pdd-sync-checker",
        standalone_mode=True,
    )


if __name__ == "__main__":
    main()
