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
_SHA256 = re.compile(r"[0-9a-f]{64}\Z")

# This is a one-time bridge from the legacy schema-1 policy that protected the
# base of PR #1989.  The legacy parser did not understand requirement rotations,
# so it could not authorize the already-reviewed prompt-contract updates.  Keep
# every byte binding here: a later branch cannot reuse this bridge for a
# different base, profile file, or rotation policy.
_BOOTSTRAP_BASE_ROTATION_POLICY_SHA256 = (
    "36b113058a81da855a7117213db3b0e4da3e5bdfc944dadd220f83f4045f995d"
)
_BOOTSTRAP_BASE_PROFILE_SHA256 = (
    "ee4146f5b24eab5172d3cba0ef57bec967abfe21b271252f3c1fea9fa54ae8b6"
)
_BOOTSTRAP_HEAD_PROFILE_SHA256 = (
    "a11ee4ef9dd828c385d69c359dafdc54ab85c83f3b0f350179fa17dc497772da"
)
_BOOTSTRAP_HEAD_ROTATION_POLICY_SHA256 = (
    "338686a6232f744ad0c3f77578614b5234237bf3d20eab2a7b498c67edae7c14"
)


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


@dataclass(frozen=True)
class _RequirementRotationAuthorization:
    """One protected, byte-bound prompt-contract requirement transition."""

    prompt_path: PurePosixPath
    language_id: str
    from_requirement_id: str
    to_requirement_id: str
    policy_path: PurePosixPath
    from_policy_sha256: str
    to_policy_sha256: str


_BOOTSTRAP_REQUIREMENT_ROTATIONS = (
    _RequirementRotationAuthorization(
        PurePosixPath("pdd/prompts/agentic_common_python.prompt"),
        "python",
        "CONTRACT-SHA256:82a40d21370bc8aaf662b45274c36961284347203d57776e4e8b71e49b474a4e",
        "CONTRACT-SHA256:cf19479e2f90ea1bfb46c49b8dc1f9d4b8a6807b86f5803228e62f75dbee19e0",
        PROFILE_PATH,
        _BOOTSTRAP_BASE_PROFILE_SHA256,
        _BOOTSTRAP_HEAD_PROFILE_SHA256,
    ),
    _RequirementRotationAuthorization(
        PurePosixPath("pdd/prompts/commands/checkup_python.prompt"),
        "python",
        "CONTRACT-SHA256:62750858a2961ec33a0ed0ca64f37389c370d764fd53823065e7386c30f6faa8",
        "CONTRACT-SHA256:0f9a99e1b652f75e0777be14b0dadee6d21bacb567ea931ed5e16d9788073e6a",
        PROFILE_PATH,
        _BOOTSTRAP_BASE_PROFILE_SHA256,
        _BOOTSTRAP_HEAD_PROFILE_SHA256,
    ),
    _RequirementRotationAuthorization(
        PurePosixPath("pdd/prompts/generate_model_catalog_python.prompt"),
        "python",
        "CONTRACT-SHA256:1e0ffc1fb8e8172bb396b8050c67bfbf750e28bd4191ffb63f7d664d0530827e",
        "CONTRACT-SHA256:a086fdc50c2cb54bcd0543e467106dbc2fb87c3b2f196bfcc0f51b7ecf3bed97",
        PROFILE_PATH,
        _BOOTSTRAP_BASE_PROFILE_SHA256,
        _BOOTSTRAP_HEAD_PROFILE_SHA256,
    ),
    _RequirementRotationAuthorization(
        PurePosixPath("pdd/prompts/llm_invoke_python.prompt"),
        "python",
        "CONTRACT-SHA256:88face96e298219fba7448186eb71f1586a676888a827a04d326882df8e4f41e",
        "CONTRACT-SHA256:2a6545466c28fa2cf11a3ed7df5e3dbf1e3160222778941ce8a530b174afbfb3",
        PROFILE_PATH,
        _BOOTSTRAP_BASE_PROFILE_SHA256,
        _BOOTSTRAP_HEAD_PROFILE_SHA256,
    ),
    _RequirementRotationAuthorization(
        PurePosixPath("pdd/prompts/prompt_repair_python.prompt"),
        "python",
        "CONTRACT-SHA256:915a3f4e69e31010f156cc381d873ba75c6777365780ffc6d69020e914b0c846",
        "CONTRACT-SHA256:d136f2f47483b0a17b9f733402ecfe1d2e8d69540c054043eeee8a752aa69562",
        PROFILE_PATH,
        _BOOTSTRAP_BASE_PROFILE_SHA256,
        _BOOTSTRAP_HEAD_PROFILE_SHA256,
    ),
    _RequirementRotationAuthorization(
        PurePosixPath("pdd/prompts/routing_policy_python.prompt"),
        "python",
        "CONTRACT-SHA256:bd348ce36f1b63ddc9b12bc36e1a14b3206cb35491d278f9735375f1f39d9dc6",
        "CONTRACT-SHA256:3971482288276694f054c7fed70a09e43595b151d514200110b5f1937ee932ab",
        PROFILE_PATH,
        _BOOTSTRAP_BASE_PROFILE_SHA256,
        _BOOTSTRAP_HEAD_PROFILE_SHA256,
    ),
    _RequirementRotationAuthorization(
        PurePosixPath("pdd/prompts/setup_tool_python.prompt"),
        "python",
        "CONTRACT-SHA256:bb4e712d004c8c5afccc584629266eb7df00520483aacfd78aa27c2ef0cd2232",
        "CONTRACT-SHA256:2358501051357b8b7150c7aabdc470500d3869179a3c057948f01e9a63983ab6",
        PROFILE_PATH,
        _BOOTSTRAP_BASE_PROFILE_SHA256,
        _BOOTSTRAP_HEAD_PROFILE_SHA256,
    ),
)


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
) -> tuple[
    tuple[_PolicyRotationAuthorization, ...],
    tuple[_RequirementRotationAuthorization, ...],
]:
    """Load narrowly-scoped profile rotation authority from the protected base."""
    raw = read_git_blob(root, protected_base_ref, ROTATION_POLICY_PATH)
    if raw is None:
        return (), ()
    try:
        payload = json.loads(raw)
        schema_version = payload.get("schema_version")
        rows = payload["rotations"]
        if schema_version not in {1, 2} or not isinstance(rows, list):
            raise TypeError
        requirement_rows = (
            payload.get("requirement_rotations", []) if schema_version == 2 else []
        )
        if schema_version == 2 and (
            set(payload) != {"schema_version", "rotations", "requirement_rotations"}
            or not isinstance(requirement_rows, list)
        ):
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
    requirement_authorizations: list[_RequirementRotationAuthorization] = []
    required_keys = {
        "prompt_path",
        "language_id",
        "from_requirement_id",
        "to_requirement_id",
        "policy_path",
        "from_policy_sha256",
        "to_policy_sha256",
    }
    for row in requirement_rows:
        if not isinstance(row, dict) or set(row) != required_keys:
            raise VerificationProfileError("protected requirement rotation rule is malformed")
        if not all(isinstance(value, str) and value for value in row.values()):
            raise VerificationProfileError("protected requirement rotation rule is malformed")
        prompt_path = PurePosixPath(row["prompt_path"])
        policy_path = PurePosixPath(row["policy_path"])
        if (
            prompt_path.is_absolute()
            or ".." in prompt_path.parts
            or policy_path != PROFILE_PATH
            or not _SHA256.fullmatch(row["from_policy_sha256"])
            or not _SHA256.fullmatch(row["to_policy_sha256"])
        ):
            raise VerificationProfileError("protected requirement rotation rule is malformed")
        requirement_authorizations.append(
            _RequirementRotationAuthorization(
                prompt_path,
                row["language_id"],
                row["from_requirement_id"],
                row["to_requirement_id"],
                policy_path,
                row["from_policy_sha256"],
                row["to_policy_sha256"],
            )
        )
    if len(requirement_authorizations) != len(set(requirement_authorizations)):
        raise VerificationProfileError("protected requirement rotation rules are duplicated")
    return tuple(authorizations), tuple(requirement_authorizations)


def _bootstrap_requirement_rotation_authorizations(
    root: Path, manifest: UnitManifest
) -> tuple[_RequirementRotationAuthorization, ...]:
    """Bridge exactly one reviewed schema-1 requirement-rotation transition."""
    base_policy = read_git_blob(root, manifest.base_ref, ROTATION_POLICY_PATH)
    base_profile = read_git_blob(root, manifest.base_ref, PROFILE_PATH)
    head_policy = read_git_blob(root, manifest.head_ref, ROTATION_POLICY_PATH)
    head_profile = read_git_blob(root, manifest.head_ref, PROFILE_PATH)
    if (
        base_policy is None
        or base_profile is None
        or head_policy is None
        or head_profile is None
        or hashlib.sha256(base_policy).hexdigest()
        != _BOOTSTRAP_BASE_ROTATION_POLICY_SHA256
        or hashlib.sha256(base_profile).hexdigest() != _BOOTSTRAP_BASE_PROFILE_SHA256
        or hashlib.sha256(head_policy).hexdigest()
        != _BOOTSTRAP_HEAD_ROTATION_POLICY_SHA256
        or hashlib.sha256(head_profile).hexdigest() != _BOOTSTRAP_HEAD_PROFILE_SHA256
    ):
        return ()
    try:
        _, authorizations = _load_rotation_authorizations(root, manifest.head_ref)
    except VerificationProfileError:
        return ()
    if authorizations != _BOOTSTRAP_REQUIREMENT_ROTATIONS:
        return ()
    return authorizations


def _authorized_requirement_updates(
    root: Path,
    manifest: UnitManifest,
    base: dict[UnitId, _ProfileInput],
    head: dict[UnitId, _ProfileInput],
    authorizations: tuple[_RequirementRotationAuthorization, ...],
) -> tuple[dict[UnitId, tuple[str, ...]], list[str]]:
    """Accept only exact, protected-base-approved requirement replacements."""
    base_raw = read_git_blob(root, manifest.base_ref, PROFILE_PATH)
    head_raw = read_git_blob(root, manifest.head_ref, PROFILE_PATH)
    if base_raw is None or head_raw is None:
        return {}, []
    base_sha = hashlib.sha256(base_raw).hexdigest()
    head_sha = hashlib.sha256(head_raw).hexdigest()
    updates: dict[UnitId, tuple[str, ...]] = {}
    invalid: list[str] = []
    for unit_id, protected in base.items():
        candidate = head.get(unit_id)
        if candidate is None:
            continue
        removed = set(protected.requirements) - set(candidate.requirements)
        if not removed:
            continue
        added = set(candidate.requirements) - set(protected.requirements)
        matching = tuple(
            item
            for item in authorizations
            if item.prompt_path == unit_id.prompt_relpath
            and item.language_id == unit_id.language_id
            and item.from_policy_sha256 == base_sha
            and item.to_policy_sha256 == head_sha
        )
        if not matching:
            continue
        if (
            {item.from_requirement_id for item in matching} != removed
            or {item.to_requirement_id for item in matching} != added
            or len(matching) != len(removed)
        ):
            invalid.append(
                f"{unit_id.prompt_relpath}: authorized requirement rotation does not "
                "match the protected requirement transition"
            )
            continue
        updates[unit_id] = candidate.requirements
    return updates, invalid


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


def _config_digests_are_unchanged(
    head: dict[UnitId, _ProfileInput],
    protected: list[tuple[UnitId, VerificationObligation]],
) -> bool:
    """Return whether a requirement-only edit needs no trust-policy rotation."""
    return all(
        (candidate := next(
            (
                item
                for item in head.get(unit_id, _ProfileInput((), ())).obligations
                if item.obligation_id == obligation.obligation_id
            ),
            None,
        )) is not None
        and candidate.validator_config_digest == obligation.validator_config_digest
        for unit_id, obligation in protected
    )


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
        if _config_digests_are_unchanged(head, protected):
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
    authorized_requirement_updates: dict[UnitId, tuple[str, ...]],
) -> tuple[VerificationProfile, list[str]]:
    invalid: list[str] = []
    if base is None and head is not None:
        invalid.append(
            f"{unit_id.prompt_relpath}: candidate-only profile lacks protected approval"
        )
        head = None
    base_requirements = set(base.requirements if base else ())
    head_requirements = set(head.requirements if head else ())
    requirement_update = authorized_requirement_updates.get(unit_id)
    if base_requirements - head_requirements and requirement_update is None:
        invalid.append(f"{unit_id.prompt_relpath}: candidate removed protected requirements")
    requirements = (
        requirement_update
        if requirement_update is not None
        else tuple(sorted(base_requirements | head_requirements))
    )
    base_obligations = {item.obligation_id: item for item in (base.obligations if base else ())}
    head_obligations = {item.obligation_id: item for item in (head.obligations if head else ())}
    effective = dict(base_obligations)
    for obligation_id, obligation in head_obligations.items():
        protected = base_obligations.get(obligation_id)
        if protected is not None and protected != obligation:
            if authorized_updates.get((unit_id, obligation_id)) == obligation:
                effective[obligation_id] = obligation
                continue
            if (
                requirement_update is not None
                and obligation.obligation_id == _HUMAN_OBLIGATION_ID
                and obligation.validator_id == _HUMAN_VALIDATOR_ID
                and protected.requirement_ids == tuple(sorted(base_requirements))
                and obligation.requirement_ids == requirement_update
                and replace(obligation, requirement_ids=protected.requirement_ids)
                == protected
            ):
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
    policy_authorizations, requirement_authorizations = _load_rotation_authorizations(
        root, manifest.base_ref
    )
    authorized_updates, rotation_invalid = _authorized_rotation_updates(
        root,
        manifest,
        base,
        head,
        policy_authorizations,
    )
    invalid.extend(rotation_invalid)
    requirement_authorizations += _bootstrap_requirement_rotation_authorizations(
        root, manifest
    )
    authorized_requirement_updates, requirement_rotation_invalid = (
        _authorized_requirement_updates(
            root, manifest, base, head, requirement_authorizations
        )
    )
    invalid.extend(requirement_rotation_invalid)
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
            unit_id,
            base.get(unit_id),
            head.get(unit_id),
            authorized_updates,
            authorized_requirement_updates,
        )
        profiles.append(profile)
        invalid.extend(profile_invalid)
    return ProfileSet(tuple(profiles), tuple(sorted(set(invalid))))
