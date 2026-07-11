"""Protected base/head verification-profile loading and completeness checks."""

from __future__ import annotations

import hashlib
import json
import re
from dataclasses import dataclass, replace
from pathlib import Path, PurePosixPath
from typing import Any, Mapping

from .alias_policy import load_protected_aliases
from .manifest import UnitManifest
from .git_io import read_git_blob
from .types import UnitId, VerificationObligation, VerificationProfile


PROFILE_PATH = PurePosixPath(".pdd/verification-profiles.json")
ROTATION_POLICY_PATH = PurePosixPath(".pdd/verification-profile-rotations.json")
TRUST_POLICY_PATH = PurePosixPath(".pdd/attestation-trust.json")
_HUMAN_OBLIGATION_ID = "threshold-human-attestation"
_HUMAN_VALIDATOR_ID = "threshold-ed25519"
_PLACEHOLDER_POLICY_DIGEST = "threshold-ed25519-v1"


class VerificationProfileError(ValueError):
    """Raised when protected verification-profile data cannot be parsed."""


@dataclass(frozen=True)
class ProfileSet:
    """Effective protected profiles and policy violations for a checked head."""

    profiles: tuple[VerificationProfile, ...]
    invalid_reasons: tuple[str, ...]

    @property
    def coverage(self) -> float:
        """Return the fraction of expected profiles with complete obligations."""
        if not self.profiles:
            return 0.0
        complete = sum(profile.complete for profile in self.profiles)
        return complete / len(self.profiles)

    def for_unit(self, unit_id: UnitId) -> VerificationProfile | None:
        """Return one effective profile by stable unit identity."""
        return next((item for item in self.profiles if item.unit_id == unit_id), None)


@dataclass(frozen=True)
class _ProfileInput:
    """Parsed requirements and obligations from one immutable Git tree."""

    requirements: tuple[str, ...]
    obligations: tuple[VerificationObligation, ...]


@dataclass(frozen=True)
class _PolicyRotationAuthorization:
    """One protected, one-way authorization for a future trust-policy install."""

    obligation_id: str
    validator_id: str
    from_config_digest: str
    policy_path: PurePosixPath


_REQUIREMENT_ID = re.compile(r"\bREQ-[A-Za-z0-9_.:-]+\b")


def _prompt_requirements(raw: bytes) -> tuple[str, ...]:
    """Derive the protected requirement universe from exact prompt bytes."""
    try:
        text = raw.decode("utf-8")
    except UnicodeDecodeError as exc:
        raise VerificationProfileError("profile prompt is not UTF-8") from exc
    explicit = tuple(sorted(set(_REQUIREMENT_ID.findall(text))))
    if explicit:
        return explicit
    return (f"CONTRACT-SHA256:{hashlib.sha256(raw).hexdigest()}",)


def _obligation(payload: Mapping[str, Any]) -> VerificationObligation:
    try:
        requirement_ids = payload["requirement_ids"]
        if not isinstance(requirement_ids, list) or not all(
            isinstance(item, str) for item in requirement_ids
        ):
            raise TypeError("requirement_ids must be a string list")
        return VerificationObligation(
            str(payload["obligation_id"]),
            str(payload["kind"]),
            str(payload["validator_id"]),
            str(payload["validator_config_digest"]),
            tuple(sorted(requirement_ids)),
            tuple(
                sorted(
                    PurePosixPath(item)
                    for item in payload.get("artifact_paths", [])
                    if isinstance(item, str)
                )
            ),
            bool(payload.get("required", True)),
            tuple(
                sorted(
                    PurePosixPath(item)
                    for item in payload.get("code_under_test_paths", [])
                    if isinstance(item, str)
                )
            ),
        )
    except (KeyError, TypeError) as exc:
        raise VerificationProfileError("verification obligation is malformed") from exc


def _load_inputs(
    root: Path,
    ref: str,
    repository_id: str,
    approved_aliases: Mapping[PurePosixPath, PurePosixPath],
) -> tuple[dict[UnitId, _ProfileInput], list[str]]:
    # pylint: disable=too-many-branches,too-many-locals
    raw = read_git_blob(root, ref, PROFILE_PATH)
    if raw is None:
        return {}, []
    try:
        payload = json.loads(raw)
    except (json.JSONDecodeError, UnicodeDecodeError) as exc:
        raise VerificationProfileError(f"{ref}: profile file is malformed") from exc
    rows = payload.get("profiles") if isinstance(payload, dict) else None
    if not isinstance(rows, list):
        raise VerificationProfileError(f"{ref}: profiles must be a list")
    profiles: dict[UnitId, _ProfileInput] = {}
    invalid: list[str] = []
    for row in rows:
        if not isinstance(row, dict):
            invalid.append(f"{ref}: profile entry is not an object")
            continue
        try:
            unit_id = UnitId(
                repository_id,
                PurePosixPath(str(row["prompt_path"])),
                str(row["language_id"]),
            )
            requirements = row["required_requirement_ids"]
            obligations = row["obligations"]
            if not isinstance(requirements, list) or not all(
                isinstance(item, str) for item in requirements
            ):
                raise TypeError("required requirements must be a string list")
            if not isinstance(obligations, list):
                raise TypeError("obligations must be a list")
            parsed = _ProfileInput(
                tuple(sorted(requirements)),
                tuple(sorted(_obligation(item) for item in obligations)),
            )
        except (KeyError, TypeError, VerificationProfileError) as exc:
            invalid.append(f"{ref}: invalid profile entry: {exc}")
            continue
        prompt_relpath = unit_id.prompt_relpath
        for alias, canonical in approved_aliases.items():
            if prompt_relpath == alias:
                prompt_relpath = canonical
                break
            if prompt_relpath.parts[: len(alias.parts)] == alias.parts:
                prompt_relpath = canonical.joinpath(
                    *prompt_relpath.parts[len(alias.parts) :]
                )
                break
        prompt_raw = read_git_blob(root, ref, prompt_relpath)
        if prompt_raw is None:
            invalid.append(f"{ref}: profile prompt is absent: {unit_id.prompt_relpath}")
            continue
        try:
            protected_requirements = _prompt_requirements(prompt_raw)
        except VerificationProfileError as exc:
            invalid.append(f"{ref}: {unit_id.prompt_relpath}: {exc}")
            continue
        if parsed.requirements != protected_requirements:
            invalid.append(
                f"{ref}: {unit_id.prompt_relpath}: profile requirements do not "
                "match immutable prompt requirements"
            )
            continue
        if unit_id in profiles:
            invalid.append(f"{ref}: duplicate profile for {unit_id.prompt_relpath}")
        else:
            profiles[unit_id] = parsed
    return profiles, invalid


def _profile_digest(
    unit_id: UnitId,
    requirements: tuple[str, ...],
    obligations: tuple[VerificationObligation, ...],
) -> str:
    payload = {
        "unit": {
            "repository_id": unit_id.repository_id,
            "prompt_relpath": unit_id.prompt_relpath.as_posix(),
            "language_id": unit_id.language_id,
        },
        "required_requirement_ids": requirements,
        "obligations": [
            {
                "obligation_id": item.obligation_id,
                "kind": item.kind,
                "validator_id": item.validator_id,
                "validator_config_digest": item.validator_config_digest,
                "requirement_ids": item.requirement_ids,
                "artifact_paths": [path.as_posix() for path in item.artifact_paths],
                "code_under_test_paths": [
                    path.as_posix() for path in sorted(item.code_under_test_paths)
                ],
                "required": item.required,
            }
            for item in obligations
        ],
    }
    encoded = json.dumps(payload, sort_keys=True, separators=(",", ":")).encode()
    return hashlib.sha256(encoded).hexdigest()


def _load_rotation_authorizations(
    root: Path, protected_base_ref: str
) -> tuple[_PolicyRotationAuthorization, ...]:
    """Load narrowly-scoped profile rotation authority from the protected base."""
    raw = read_git_blob(root, protected_base_ref, ROTATION_POLICY_PATH)
    if raw is None:
        return ()
    try:
        payload = json.loads(raw)
        rows = payload["rotations"]
        if payload.get("schema_version") != 1 or not isinstance(rows, list):
            raise TypeError
    except (json.JSONDecodeError, TypeError, UnicodeDecodeError) as exc:
        raise VerificationProfileError("protected profile rotation policy is malformed") from exc

    authorizations: list[_PolicyRotationAuthorization] = []
    for row in rows:
        if not isinstance(row, dict) or set(row) != {
            "obligation_id",
            "validator_id",
            "from_config_digest",
            "policy_path",
        }:
            raise VerificationProfileError("protected profile rotation rule is malformed")
        authorization = _PolicyRotationAuthorization(
            str(row["obligation_id"]),
            str(row["validator_id"]),
            str(row["from_config_digest"]),
            PurePosixPath(str(row["policy_path"])),
        )
        if authorization != _PolicyRotationAuthorization(
            _HUMAN_OBLIGATION_ID,
            _HUMAN_VALIDATOR_ID,
            _PLACEHOLDER_POLICY_DIGEST,
            TRUST_POLICY_PATH,
        ):
            raise VerificationProfileError("protected profile rotation rule is not authorized")
        authorizations.append(authorization)
    if len(authorizations) != len(set(authorizations)):
        raise VerificationProfileError("protected profile rotation rules are duplicated")
    return tuple(authorizations)


def _rotation_updates(
    head: dict[UnitId, _ProfileInput],
    protected: list[tuple[UnitId, VerificationObligation]],
    target_digest: str,
) -> dict[tuple[UnitId, str], VerificationObligation] | None:
    """Return complete policy-bound updates, or reject a partial remap."""
    updates: dict[tuple[UnitId, str], VerificationObligation] = {}
    for unit_id, obligation in protected:
        candidate = next(
            (
                item
                for item in head.get(unit_id, _ProfileInput((), ())).obligations
                if item.obligation_id == obligation.obligation_id
            ),
            None,
        )
        rotated = candidate and replace(
            candidate, validator_config_digest=obligation.validator_config_digest
        )
        if (
            candidate is None
            or candidate.validator_config_digest != target_digest
            or rotated != obligation
        ):
            return None
        updates[(unit_id, obligation.obligation_id)] = candidate
    return updates


def _authorized_rotation_updates(
    root: Path,
    manifest: UnitManifest,
    base: dict[UnitId, _ProfileInput],
    head: dict[UnitId, _ProfileInput],
    authorizations: tuple[_PolicyRotationAuthorization, ...],
) -> tuple[dict[tuple[UnitId, str], VerificationObligation], list[str]]:
    """Authorize only complete, policy-byte-bound protected obligation rotations."""
    updates: dict[tuple[UnitId, str], VerificationObligation] = {}
    invalid: list[str] = []
    for authorization in authorizations:
        protected = [
            (unit_id, obligation)
            for unit_id, profile in base.items()
            if unit_id in set(manifest.expected_managed)
            for obligation in profile.obligations
            if obligation.obligation_id == authorization.obligation_id
            and obligation.validator_id == authorization.validator_id
            and obligation.validator_config_digest == authorization.from_config_digest
        ]
        if not protected:
            continue
        unchanged = _rotation_updates(
            head, protected, authorization.from_config_digest
        )
        if unchanged is not None:
            continue
        policy = read_git_blob(root, manifest.head_ref, authorization.policy_path)
        if policy is None:
            invalid.append("authorized profile rotation policy is absent from candidate")
            continue
        target_digest = hashlib.sha256(policy).hexdigest()
        candidate_updates = _rotation_updates(head, protected, target_digest)
        if candidate_updates is None:
            invalid.append(
                "authorized profile rotation must restamp every protected "
                "human-attestation obligation"
            )
            continue
        updates.update(candidate_updates)
    return updates, invalid


def _effective_profile(
    unit_id: UnitId,
    base: _ProfileInput | None,
    head: _ProfileInput | None,
    authorized_updates: dict[tuple[UnitId, str], VerificationObligation],
) -> tuple[VerificationProfile, list[str]]:
    invalid: list[str] = []
    if base is None and head is not None:
        invalid.append(
            f"{unit_id.prompt_relpath}: candidate-only profile lacks protected approval"
        )
        head = None
    base_requirements = set(base.requirements if base else ())
    if base_requirements - set(head.requirements if head else ()):
        invalid.append(f"{unit_id.prompt_relpath}: candidate removed protected requirements")
    requirements = tuple(sorted(base_requirements | set(head.requirements if head else ())))
    base_obligations = {item.obligation_id: item for item in (base.obligations if base else ())}
    head_obligations = {item.obligation_id: item for item in (head.obligations if head else ())}
    effective = dict(base_obligations)
    for obligation_id, obligation in head_obligations.items():
        protected = base_obligations.get(obligation_id)
        if protected is not None and protected != obligation:
            if authorized_updates.get((unit_id, obligation_id)) == obligation:
                effective[obligation_id] = obligation
                continue
            invalid.append(
                f"{unit_id.prompt_relpath}: candidate changed protected obligation "
                f"{obligation_id}"
            )
            continue
        effective[obligation_id] = obligation
    invalid.extend(
        f"{unit_id.prompt_relpath}: candidate removed protected obligation {item}"
        for item in sorted(set(base_obligations) - set(head_obligations))
    )
    obligations = tuple(sorted(effective.values()))
    profile = VerificationProfile(
        unit_id,
        obligations,
        requirements,
        _profile_digest(unit_id, requirements, obligations),
    )
    if not profile.complete:
        invalid.append(f"{unit_id.prompt_relpath}: verification profile is incomplete")
    return profile, invalid


def load_verification_profiles(root: Path, manifest: UnitManifest) -> ProfileSet:
    """Load the protected base/candidate union for every expected-managed unit."""
    alias_invalid: list[str] = []
    try:
        approved_aliases = load_protected_aliases(root, manifest)
    except ValueError as exc:
        approved_aliases = {}
        alias_invalid.append(str(exc))
    base, base_invalid = _load_inputs(
        root, manifest.base_ref, manifest.repository_id, approved_aliases
    )
    head, head_invalid = _load_inputs(
        root, manifest.head_ref, manifest.repository_id, approved_aliases
    )
    invalid = alias_invalid + base_invalid + head_invalid
    authorized_updates, rotation_invalid = _authorized_rotation_updates(
        root,
        manifest,
        base,
        head,
        _load_rotation_authorizations(root, manifest.base_ref),
    )
    invalid.extend(rotation_invalid)
    profiles: list[VerificationProfile] = []
    expected = set(manifest.expected_managed)
    unknown = (set(base) | set(head)) - expected
    invalid.extend(
        f"profile references non-expected unit {item.prompt_relpath}"
        for item in sorted(unknown)
    )
    for unit_id in manifest.expected_managed:
        if unit_id not in base and unit_id not in head:
            invalid.append(f"{unit_id.prompt_relpath}: verification profile is missing")
        profile, profile_invalid = _effective_profile(
            unit_id, base.get(unit_id), head.get(unit_id), authorized_updates
        )
        profiles.append(profile)
        invalid.extend(profile_invalid)
    return ProfileSet(tuple(profiles), tuple(sorted(set(invalid))))
