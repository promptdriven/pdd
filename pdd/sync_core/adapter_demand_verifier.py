"""Verify the immutable PDD profile registry's machine adapter demand."""

from __future__ import annotations

import argparse
import hashlib
import json
import os
import re
import subprocess
import sys
import tempfile
from dataclasses import dataclass
from pathlib import Path, PurePosixPath
from typing import Any, Sequence

PROFILE_PATH = PurePosixPath(".pdd/verification-profiles.json")
REPOSITORY_ID_PATH = PurePosixPath(".pdd/repository-id")
PROFILE_EVIDENCE_SOURCE_SHA = "2cacc91f90759ff45f1ad976da3b773e1a5f07a5"
PROTECTED_MAIN_SHA = "e7735e0f35a0915707142bfd4c767df59f8c3b9e"
PROTECTED_REPOSITORY_ID = "3b4d7b1c-d6cc-4752-ba93-6b98d1a710e0"
PROTECTED_PROFILES_SHA256 = (
    "56ea5d189034c9d85e91c86348689eb18c4c34fa67406258f78f0ae3330eaeb6"
)
EXPECTED_PROFILE_COUNT = 468
EXPECTED_MACHINE_PROFILE_COUNT = 1
EXPECTED_HUMAN_ONLY_PROFILE_COUNT = 467
EXPECTED_MACHINE_VALIDATOR_IDS = ("pytest",)
EXPECTED_MACHINE_OBLIGATION_IDS = (
    "pytest-descriptor-store",
    "pytest-signer-process",
    "pytest-supervisor",
)
SUPPORTED_MACHINE_ADAPTERS = frozenset(("jest", "pytest", "vitest"))
_SHA256 = re.compile(r"[0-9a-f]{64}")
_SHA1 = re.compile(r"[0-9a-f]{40}")
_REPOSITORY_ID = re.compile(
    r"[0-9a-f]{8}-[0-9a-f]{4}-[0-9a-f]{4}-[0-9a-f]{4}-[0-9a-f]{12}"
)


class AdapterDemandError(ValueError):
    """Raised when immutable adapter-demand evidence is not trustworthy."""


class _DuplicateJsonMember(ValueError):
    """Raised by the JSON decoder when an object repeats a member name."""


@dataclass(frozen=True)
class _Obligation:
    """The fields needed to distinguish machine and human obligations."""

    obligation_id: str
    kind: str
    validator_id: str


@dataclass(frozen=True)
class _Profile:
    """One strict PDD profile row."""

    obligations: tuple[_Obligation, ...]


def canonical_json(payload: dict[str, Any]) -> bytes:
    """Encode one deterministic JSON document suitable for a committed artifact."""
    return json.dumps(payload, sort_keys=True, separators=(",", ":")).encode("utf-8") + b"\n"


def build_adapter_demand(
    root: Path,
    profile_evidence_source_sha: str,
    protected_main_sha: str,
    profiles_path: PurePosixPath = PROFILE_PATH,
    profiles_sha256: str | None = None,
) -> dict[str, Any]:
    """Build exact adapter demand only when source and protected main agree."""
    _validate_inputs(
        profile_evidence_source_sha, protected_main_sha, profiles_path, profiles_sha256
    )
    if profile_evidence_source_sha != PROFILE_EVIDENCE_SOURCE_SHA:
        raise AdapterDemandError("profile evidence source SHA does not match")
    if protected_main_sha != PROTECTED_MAIN_SHA:
        raise AdapterDemandError("protected main SHA does not match")
    resolved_source_sha = _resolve_git_commit(root, profile_evidence_source_sha)
    resolved_main_sha = _resolve_git_commit(root, protected_main_sha)
    if resolved_source_sha != profile_evidence_source_sha:
        raise AdapterDemandError("profile evidence source SHA does not match")
    if resolved_main_sha != protected_main_sha:
        raise AdapterDemandError("protected main SHA does not match")
    source_profile_bytes = _read_git_regular_blob(
        root, resolved_source_sha, profiles_path
    )
    main_profile_bytes = _read_git_regular_blob(root, resolved_main_sha, profiles_path)
    if source_profile_bytes is None or main_profile_bytes is None:
        raise AdapterDemandError("protected profile registry is missing or not regular")
    if source_profile_bytes != main_profile_bytes:
        raise AdapterDemandError(
            "protected-main profile registry differs from immutable evidence source"
        )
    registry_digest = hashlib.sha256(source_profile_bytes).hexdigest()
    expected_digest = profiles_sha256 or PROTECTED_PROFILES_SHA256
    if registry_digest != expected_digest or registry_digest != PROTECTED_PROFILES_SHA256:
        raise AdapterDemandError("protected profile registry digest does not match")
    repository_id = _read_repository_id(root, resolved_source_sha)
    if _read_repository_id(root, resolved_main_sha) != repository_id:
        raise AdapterDemandError("protected repository identity differs from evidence source")
    profiles = _parse_profiles(source_profile_bytes)
    if len(profiles) != EXPECTED_PROFILE_COUNT:
        raise AdapterDemandError("profile count does not match")
    summary = _summarize_profiles(profiles)
    _validate_expected_summary(summary)
    return {
        "human_attestation_only_profile_count": summary.human_only_profile_count,
        "machine_obligation_ids": list(summary.machine_obligation_ids),
        "machine_obligation_profile_count": summary.machine_profile_count,
        "machine_validator_ids": list(summary.machine_validator_ids),
        "pdd_profiles_path": profiles_path.as_posix(),
        "profile_count": len(profiles),
        "registry_sha256": registry_digest,
        "repository_id": repository_id,
        "profile_evidence_source_sha": resolved_source_sha,
        "protected_main_sha": resolved_main_sha,
        "schema_version": 2,
        "unknown_demanded_adapters": list(summary.unknown_adapters),
    }


@dataclass(frozen=True)
class _DemandSummary:
    """Normalized machine demand calculated from strict profile rows."""

    machine_profile_count: int
    human_only_profile_count: int
    machine_validator_ids: tuple[str, ...]
    machine_obligation_ids: tuple[str, ...]
    unknown_adapters: tuple[str, ...]


def _validate_inputs(
    profile_evidence_source_sha: str,
    protected_main_sha: str,
    profiles_path: PurePosixPath,
    profiles_sha256: str | None,
) -> None:
    """Reject mutable paths and malformed protected identities."""
    for name, value in (
        ("profile evidence source SHA", profile_evidence_source_sha),
        ("protected main SHA", protected_main_sha),
    ):
        if value != value.lower() or _SHA1.fullmatch(value) is None:
            raise AdapterDemandError(f"{name} must be a lowercase full SHA-1")
    if profiles_path != PROFILE_PATH:
        raise AdapterDemandError("PDD profile registry path does not match")
    if profiles_sha256 is not None and (
        profiles_sha256 != profiles_sha256.lower()
        or _SHA256.fullmatch(profiles_sha256) is None
    ):
        raise AdapterDemandError("profile digest must be a lowercase SHA-256")


def _read_repository_id(root: Path, repository_sha: str) -> str:
    """Read a canonical repository identity from the exact immutable tree."""
    raw = _read_git_regular_blob(root, repository_sha, REPOSITORY_ID_PATH)
    if raw is None:
        raise AdapterDemandError("protected repository identity is missing or not regular")
    try:
        repository_id = raw.decode("ascii").strip()
    except UnicodeDecodeError as exc:
        raise AdapterDemandError("protected repository identity is not ASCII") from exc
    if _REPOSITORY_ID.fullmatch(repository_id) is None:
        raise AdapterDemandError("protected repository identity is malformed")
    if repository_id != PROTECTED_REPOSITORY_ID:
        raise AdapterDemandError("protected repository identity does not match")
    return repository_id


def _resolve_git_commit(root: Path, repository_sha: str) -> str:
    """Resolve a commit while ignoring local Git replacement references."""
    result = _run_git(root, "rev-parse", "--verify", f"{repository_sha}^{{commit}}")
    if result.returncode != 0 or not result.stdout.strip():
        raise AdapterDemandError("cannot resolve protected repository commit")
    try:
        return result.stdout.decode("ascii").strip()
    except UnicodeDecodeError as exc:
        raise AdapterDemandError("protected repository commit is malformed") from exc


def _read_git_regular_blob(
    root: Path, repository_sha: str, path: PurePosixPath
) -> bytes | None:
    """Read one regular tree blob while ignoring local replacement references."""
    result = _run_git(root, "ls-tree", "-z", repository_sha, "--", path.as_posix())
    if result.returncode != 0 or not result.stdout:
        return None
    try:
        record = result.stdout.split(b"\0", 1)[0]
        metadata, record_path = record.split(b"\t", 1)
        mode, object_type, object_id = metadata.decode("ascii").split()
    except (UnicodeDecodeError, ValueError):
        return None
    if (
        record_path != path.as_posix().encode("utf-8")
        or mode not in {"100644", "100755"}
        or object_type != "blob"
    ):
        return None
    blob = _run_git(root, "cat-file", "blob", object_id)
    return blob.stdout if blob.returncode == 0 else None


def _run_git(root: Path, *arguments: str) -> subprocess.CompletedProcess[bytes]:
    """Run Git with replacement refs disabled for every protected object read."""
    return subprocess.run(
        ["git", "--no-replace-objects", *arguments],
        cwd=root,
        capture_output=True,
        check=False,
    )


def _parse_profiles(raw: bytes) -> tuple[_Profile, ...]:
    """Parse the schema-1 PDD profile registry with no duplicate JSON keys."""
    try:
        payload = json.loads(raw, object_pairs_hook=_reject_duplicate_members)
    except (UnicodeDecodeError, json.JSONDecodeError, _DuplicateJsonMember) as exc:
        raise AdapterDemandError("protected profile registry JSON is malformed") from exc
    if not isinstance(payload, dict) or set(payload) != {"schema_version", "profiles"}:
        raise AdapterDemandError("protected profile registry schema is malformed")
    if (
        not isinstance(payload["schema_version"], int)
        or isinstance(payload["schema_version"], bool)
        or payload["schema_version"] != 1
    ):
        raise AdapterDemandError("protected profile registry schema version is malformed")
    rows = payload["profiles"]
    if not isinstance(rows, list) or not rows:
        raise AdapterDemandError("protected profile registry profiles are malformed")
    profiles = tuple(_parse_profile(row) for row in rows)
    if len(profiles) != len(rows):
        raise AdapterDemandError("protected profile registry count is malformed")
    return profiles


def _reject_duplicate_members(pairs: list[tuple[str, Any]]) -> dict[str, Any]:
    """Build one JSON object while rejecting repeated object keys at all depths."""
    payload: dict[str, Any] = {}
    for key, value in pairs:
        if key in payload:
            raise _DuplicateJsonMember(key)
        payload[key] = value
    return payload


def _parse_profile(row: Any) -> _Profile:
    """Validate one schema-1 profile row without accepting extension fields."""
    required = {
        "prompt_path",
        "language_id",
        "required_requirement_ids",
        "obligations",
    }
    if not isinstance(row, dict) or set(row) != required:
        raise AdapterDemandError("protected profile row schema is malformed")
    if not _nonempty_string(row["prompt_path"]) or not _nonempty_string(row["language_id"]):
        raise AdapterDemandError("protected profile identity is malformed")
    _require_string_list(row["required_requirement_ids"], "profile requirements")
    obligations = row["obligations"]
    if not isinstance(obligations, list) or not obligations:
        raise AdapterDemandError("protected profile obligations are malformed")
    parsed = tuple(_parse_obligation(item) for item in obligations)
    if len({item.obligation_id for item in parsed}) != len(parsed):
        raise AdapterDemandError("protected profile has duplicate obligation IDs")
    return _Profile(parsed)


def _parse_obligation(row: Any) -> _Obligation:
    """Validate one schema-1 obligation and retain its adapter classification."""
    required = {
        "obligation_id",
        "kind",
        "validator_id",
        "validator_config_digest",
        "requirement_ids",
        "artifact_paths",
        "required",
    }
    allowed = required | {"code_under_test_paths"}
    if not isinstance(row, dict) or (set(row) != required and set(row) != allowed):
        raise AdapterDemandError("protected obligation schema is malformed")
    for key in ("obligation_id", "kind", "validator_id", "validator_config_digest"):
        if not _nonempty_string(row[key]):
            raise AdapterDemandError("protected obligation identity is malformed")
    _require_string_list(row["requirement_ids"], "obligation requirements")
    _require_string_list(row["artifact_paths"], "obligation artifact paths")
    if "code_under_test_paths" in row:
        _require_string_list(row["code_under_test_paths"], "code-under-test paths")
    if not isinstance(row["required"], bool) or not row["required"]:
        raise AdapterDemandError("protected obligation required flag is malformed")
    if row["kind"] not in {"human-attestation", "test"}:
        raise AdapterDemandError("protected obligation kind is unsupported")
    return _Obligation(row["obligation_id"], row["kind"], row["validator_id"])


def _nonempty_string(value: Any) -> bool:
    """Return whether a field is an exact nonempty string."""
    return isinstance(value, str) and bool(value) and value.strip() == value


def _require_string_list(value: Any, name: str) -> None:
    """Require a nonempty duplicate-free list of exact nonempty strings."""
    if not isinstance(value, list) or not value or any(
        not _nonempty_string(item) for item in value
    ):
        raise AdapterDemandError(f"protected {name} are malformed")
    if len(value) != len(set(value)):
        raise AdapterDemandError(f"protected {name} contain duplicates")


def _summarize_profiles(profiles: tuple[_Profile, ...]) -> _DemandSummary:
    """Separate executable machine adapter demand from human attestations."""
    machine_profiles = 0
    human_only_profiles = 0
    machine_obligations: list[_Obligation] = []
    for profile in profiles:
        machines = tuple(item for item in profile.obligations if item.kind == "test")
        if machines:
            machine_profiles += 1
            machine_obligations.extend(machines)
        elif all(item.kind == "human-attestation" for item in profile.obligations):
            human_only_profiles += 1
        else:
            raise AdapterDemandError("profile obligation classification is malformed")
    validator_ids = tuple(sorted({item.validator_id for item in machine_obligations}))
    obligation_ids = tuple(sorted(item.obligation_id for item in machine_obligations))
    if len(obligation_ids) != len(set(obligation_ids)):
        raise AdapterDemandError("machine obligation IDs are duplicated")
    unknown_adapters = tuple(
        validator_id
        for validator_id in validator_ids
        if validator_id not in SUPPORTED_MACHINE_ADAPTERS
    )
    return _DemandSummary(
        machine_profiles,
        human_only_profiles,
        validator_ids,
        obligation_ids,
        unknown_adapters,
    )


def _validate_expected_summary(summary: _DemandSummary) -> None:
    """Keep the committed evidence pinned to its reviewed protected registry."""
    if summary.machine_profile_count != EXPECTED_MACHINE_PROFILE_COUNT:
        raise AdapterDemandError("machine-obligation profile count does not match")
    if summary.human_only_profile_count != EXPECTED_HUMAN_ONLY_PROFILE_COUNT:
        raise AdapterDemandError("human-attestation-only profile count does not match")
    if summary.machine_validator_ids != EXPECTED_MACHINE_VALIDATOR_IDS:
        raise AdapterDemandError("demanded machine validators do not match")
    if summary.machine_obligation_ids != EXPECTED_MACHINE_OBLIGATION_IDS:
        raise AdapterDemandError("demanded machine obligation IDs do not match")
    if summary.unknown_adapters:
        raise AdapterDemandError("unknown demanded adapters are present")


def _parse_arguments() -> argparse.Namespace:
    """Parse the ledger-controlled command shape."""
    parser = argparse.ArgumentParser(allow_abbrev=False)
    parser.add_argument("--pdd-profiles", required=True)
    parser.add_argument("--profile-evidence-source-sha", required=True)
    parser.add_argument("--protected-main-sha", required=True)
    parser.add_argument("--profiles-sha256")
    parser.add_argument("--output", type=_output_path, required=True)
    parser.add_argument("--require-exact-validators", nargs="+", default=[])
    parser.add_argument("--require-no-unknown-adapters", action="store_true")
    return parser.parse_args()


def main() -> None:
    """Write one canonical artifact or exit nonzero without producing evidence."""
    _invalidate_discoverable_outputs(sys.argv[1:])
    arguments = _parse_arguments()
    try:
        _remove_output(arguments.output)
        demand = build_adapter_demand(
            Path.cwd(),
            arguments.profile_evidence_source_sha,
            arguments.protected_main_sha,
            PurePosixPath(arguments.pdd_profiles),
            arguments.profiles_sha256,
        )
        validators = tuple(arguments.require_exact_validators)
        if validators and tuple(demand["machine_validator_ids"]) != validators:
            raise AdapterDemandError("required machine validators do not match")
        if arguments.require_no_unknown_adapters and demand["unknown_demanded_adapters"]:
            raise AdapterDemandError("unknown demanded adapters are present")
        _publish_output(arguments.output, canonical_json(demand))
    except (AdapterDemandError, OSError, ValueError) as exc:
        _remove_output_quietly(arguments.output)
        print(f"adapter-demand verification failed: {exc}", file=sys.stderr)
        raise SystemExit(1) from exc


def _invalidate_discoverable_outputs(arguments: Sequence[str]) -> None:
    """Remove only output values unambiguously bound by raw CLI option syntax."""
    for index, argument in enumerate(arguments):
        if argument == "--":
            break
        if argument.startswith("--output="):
            _invalidate_output_token(argument.removeprefix("--output="))
        elif argument == "--output" and index + 1 < len(arguments):
            candidate = arguments[index + 1]
            if _is_valid_output_value(candidate):
                _invalidate_output_token(candidate)


def _output_path(value: str) -> Path:
    """Parse one output path only when it matches raw cleanup eligibility."""
    if not _is_valid_output_value(value):
        raise argparse.ArgumentTypeError("output path must not start with '-'")
    return Path(value)


def _is_valid_output_value(value: str) -> bool:
    """Return whether a raw output token is safe to treat as a path value."""
    return bool(value) and "\0" not in value and not value.startswith("-")


def _invalidate_output_token(value: str) -> None:
    """Invalidate a nonempty output token that cannot contain a null path byte."""
    if _is_valid_output_value(value):
        _remove_output_quietly(Path(value))


def _remove_output(path: Path) -> None:
    """Invalidate any prior file evidence before starting verification."""
    try:
        path.unlink()
    except FileNotFoundError:
        pass


def _remove_output_quietly(path: Path) -> None:
    """Best-effort cleanup so a verifier failure cannot leave stale evidence."""
    try:
        _remove_output(path)
    except OSError:
        pass


def _publish_output(path: Path, payload: bytes) -> None:
    """Publish canonical bytes atomically from a temporary sibling file."""
    descriptor, temporary_name = tempfile.mkstemp(
        prefix=f".{path.name}.", dir=path.parent
    )
    temporary = Path(temporary_name)
    try:
        with os.fdopen(descriptor, "wb") as handle:
            handle.write(payload)
            handle.flush()
            os.fsync(handle.fileno())
        os.replace(temporary, path)
    finally:
        _remove_output_quietly(temporary)


if __name__ == "__main__":
    main()
