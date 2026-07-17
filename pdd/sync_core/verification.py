"""Protected base/head verification-profile loading and completeness checks."""

# Exact repository-bound rollout tables intentionally remain beside the verifier
# that consumes them so security review can compare code authority with policy.
# pylint: disable=too-many-lines

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
_MAX_REQUIREMENT_TRANSITIONS = 1_024
_PDD_REPOSITORY_ID = "3b4d7b1c-d6cc-4752-ba93-6b98d1a710e0"
_OPAQUE_REQUIREMENT_ID = re.compile(r"CONTRACT-SHA256:[0-9a-f]{64}")


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
class _RequirementTransitionBindings:
    """Exact immutable byte identities for both sides of a transition."""

    base_policy_sha256: str
    head_policy_sha256: str
    base_prompt_sha256: str
    head_prompt_sha256: str


@dataclass(frozen=True)
class _RequirementTransitionAuthorization:
    """One exact-byte-bound opaque prompt requirement transition."""

    prompt_path: PurePosixPath
    language_id: str
    from_requirement_id: str
    to_requirement_id: str
    policy_path: PurePosixPath
    bindings: _RequirementTransitionBindings


@dataclass(frozen=True)
class _AuthorizedProfileUpdates:
    """Narrowly authorized deltas, separated by transition dimension."""

    obligations: dict[tuple[UnitId, str], VerificationObligation]
    requirements: dict[UnitId, _ProfileInput]


@dataclass(frozen=True)
class _RequirementTransitionContext:
    """Immutable inputs shared while evaluating exact transition rules."""

    root: Path
    manifest: UnitManifest
    base: Mapping[UnitId, _ProfileInput]
    head: Mapping[UnitId, _ProfileInput]
    policies: tuple[bytes | None, bytes | None]


def _exact_bootstrap_requirement_transition(
    *row: str,
) -> _RequirementTransitionAuthorization:
    """Build one explicit exact-byte bootstrap trust root."""
    (
        prompt_path,
        language_id,
        from_digest,
        to_digest,
        base_policy_digest,
        head_policy_digest,
    ) = row
    return _RequirementTransitionAuthorization(
        PurePosixPath(prompt_path),
        language_id,
        f"CONTRACT-SHA256:{from_digest}",
        f"CONTRACT-SHA256:{to_digest}",
        PROFILE_PATH,
        _RequirementTransitionBindings(
            base_policy_digest,
            head_policy_digest,
            from_digest,
            to_digest,
        ),
    )


# Schema 2 cannot pre-authorize its own first protected installation. This exact
# repository-bound tuple is the one-time trust root for this dormant rule. Every
# later transition must already be present in the protected-base policy.
_BOOTSTRAP_REQUIREMENT_TRANSITIONS = (
    _RequirementTransitionAuthorization(
        PurePosixPath("pdd/prompts/ci_detect_changed_modules_python.prompt"),
        "python",
        "CONTRACT-SHA256:2d5d65f695fc6c8cd2f3e82f5c5d2a55ad3eb30fc4791b2a1d94ff8465ab6d10",
        "CONTRACT-SHA256:f0d873e5505d40035d3c7364fd3961b5602d21519ec9be2049c2f38b16239712",
        PROFILE_PATH,
        _RequirementTransitionBindings(
            "58a704c9d5d351e6b83e2c42126cfe85214aa3ffbf6cb3e64ac4105f3fb19b3e",
            "7df63fe892ac14382f226ea97dbd2ac186a8cb48213faec958ad32c51d51aeb5",
            "2d5d65f695fc6c8cd2f3e82f5c5d2a55ad3eb30fc4791b2a1d94ff8465ab6d10",
            "f0d873e5505d40035d3c7364fd3961b5602d21519ec9be2049c2f38b16239712",
        ),
    ),
    _exact_bootstrap_requirement_transition(
        "pdd/prompts/agentic_checkup_orchestrator_python.prompt",
        "python",
        "fc372c0369c895e42b4bb8f9277560facf086d999233d88bef8401766bccdf34",
        "379831026c7d037c2b7b529d48fcff8f33bfeb909b3608cc56aa35abdffa4134",
        "e9c53248c2f9bb4b86ec5631fe93f7901352cf200b781f1682de06092eff6bbf",
        "e451dc7b076388f184e8c9f5f4f89c93a027bcf1d666f5c96b3767f76cb22af5",
    ),
    _exact_bootstrap_requirement_transition(
        "pdd/prompts/agentic_checkup_python.prompt",
        "python",
        "fef53dad8950c06cc11e41265956a2ee174a90ff9e4985d7f30610f18c47b08b",
        "961a63b6b047e073179aa2596436338016b8c82f6c82c871e3edffa2e79dfaf9",
        "e9c53248c2f9bb4b86ec5631fe93f7901352cf200b781f1682de06092eff6bbf",
        "e451dc7b076388f184e8c9f5f4f89c93a027bcf1d666f5c96b3767f76cb22af5",
    ),
    _exact_bootstrap_requirement_transition(
        "pdd/prompts/agentic_checkup_step6_1_fix_LLM.prompt",
        "llm",
        "06f45aca3883f78f46fa9bdf37140b63aa3a41db27086aedba60abc9f480ade2",
        "a845a9233b62d960473389533733fbb5c02ce32868671394211d649a9a32eae5",
        "e9c53248c2f9bb4b86ec5631fe93f7901352cf200b781f1682de06092eff6bbf",
        "e451dc7b076388f184e8c9f5f4f89c93a027bcf1d666f5c96b3767f76cb22af5",
    ),
    _exact_bootstrap_requirement_transition(
        "pdd/prompts/agentic_checkup_step6_2_regression_tests_LLM.prompt",
        "llm",
        "b2253412164e803a93e6dd73abf8c4a0342af68f1ef94149096112252654b93d",
        "dd1060236858bc50923f247b064e5e94bb69fb8fd895e914fdfb3a6579958a28",
        "e9c53248c2f9bb4b86ec5631fe93f7901352cf200b781f1682de06092eff6bbf",
        "e451dc7b076388f184e8c9f5f4f89c93a027bcf1d666f5c96b3767f76cb22af5",
    ),
    _exact_bootstrap_requirement_transition(
        "pdd/prompts/agentic_checkup_step6_3_e2e_tests_LLM.prompt",
        "llm",
        "7f686093bfe73ab67b4e27fc878bc48706276732feb5670f34f7aa463e65e355",
        "9b771b0d5770610225a4bd2f5aca484fc8ab15216203ce290d4c4c0cf3de1d53",
        "e9c53248c2f9bb4b86ec5631fe93f7901352cf200b781f1682de06092eff6bbf",
        "e451dc7b076388f184e8c9f5f4f89c93a027bcf1d666f5c96b3767f76cb22af5",
    ),
    _exact_bootstrap_requirement_transition(
        "pdd/prompts/agentic_common_python.prompt",
        "python",
        "82a40d21370bc8aaf662b45274c36961284347203d57776e4e8b71e49b474a4e",
        "86e47992102e2344fe59ee9a3ece4c6cf356025edaadf693c12acac63a5c7490",
        "e9c53248c2f9bb4b86ec5631fe93f7901352cf200b781f1682de06092eff6bbf",
        "e451dc7b076388f184e8c9f5f4f89c93a027bcf1d666f5c96b3767f76cb22af5",
    ),
    _exact_bootstrap_requirement_transition(
        "pdd/prompts/checkup_review_loop_python.prompt",
        "python",
        "c44fbaf6b0c1ceb5c52cf514684a72e866bdc08d4bf0b948d978dec65afb0719",
        "a7fd72cadb0644d4d20d09868cc8e908e3122478e6127b3943de32b711d76c02",
        "e9c53248c2f9bb4b86ec5631fe93f7901352cf200b781f1682de06092eff6bbf",
        "e451dc7b076388f184e8c9f5f4f89c93a027bcf1d666f5c96b3767f76cb22af5",
    ),
    _exact_bootstrap_requirement_transition(
        "pdd/prompts/ci_drift_heal_python.prompt",
        "python",
        "e12dc6b48f34111182afb4a73b9ba66596617b9a6d8e393766d2cd6b847562ec",
        "fc595464ceb1bac758864cd66a87fd1ba4f72bae79660a1dd334e060cbb861f7",
        "e9c53248c2f9bb4b86ec5631fe93f7901352cf200b781f1682de06092eff6bbf",
        "e451dc7b076388f184e8c9f5f4f89c93a027bcf1d666f5c96b3767f76cb22af5",
    ),
    _exact_bootstrap_requirement_transition(
        "pdd/prompts/commands/checkup_python.prompt",
        "python",
        "62750858a2961ec33a0ed0ca64f37389c370d764fd53823065e7386c30f6faa8",
        "e31b6d61a09a408b41e769794587ac734cd72cb54b2dcb62c327683e586a6f20",
        "e9c53248c2f9bb4b86ec5631fe93f7901352cf200b781f1682de06092eff6bbf",
        "e451dc7b076388f184e8c9f5f4f89c93a027bcf1d666f5c96b3767f76cb22af5",
    ),
    _exact_bootstrap_requirement_transition(
        "pdd/prompts/story_regression_python.prompt",
        "python",
        "e5cc19e846c9fefe9608658c6186b911420c0fe4a769ed28a6be267d070909e4",
        "88ba7a932f444bb1b91e17429ca8c211742fadc8457b96d71b648b2529785d4f",
        "e9c53248c2f9bb4b86ec5631fe93f7901352cf200b781f1682de06092eff6bbf",
        "e451dc7b076388f184e8c9f5f4f89c93a027bcf1d666f5c96b3767f76cb22af5",
    ),
    _exact_bootstrap_requirement_transition(
        "pdd/prompts/llm_invoke_python.prompt",
        "python",
        "e9810acc9a371fd31d36e93ff45d33acda0469c17d1dd1cac359b86518a04ee5",
        "962185e93e75ec3662923a43ee591cd50df1413ba65f1e9b653cba287c0e5a7e",
        "e9c53248c2f9bb4b86ec5631fe93f7901352cf200b781f1682de06092eff6bbf",
        "b12b186f31608cef1e8dea42662171bc57d9bb786b942d0443cddae865e518f5",
    ),
    _exact_bootstrap_requirement_transition(
        "pdd/prompts/commands/analysis_python.prompt",
        "python",
        "6af82a6d490343742033a6083a3aa9117285843500edcd8a5d0088d0cb369f99",
        "5aff15e367047ac59ad70b842c7a0a59cdf266526e09df274f56f7928413aafd",
        "e9c53248c2f9bb4b86ec5631fe93f7901352cf200b781f1682de06092eff6bbf",
        "96eca0b44f3a82593e4b79ec03a1bf3d6c6a80b5a1b3cfb69733735a7dd24251",
    ),
    _exact_bootstrap_requirement_transition(
        "pdd/prompts/core/cloud_python.prompt",
        "python",
        "565f81380607551771e87da37bf291f553141513a7f8bad618d3344ee9dc15c8",
        "4c32578f0c81d4357d2760a388a930d9feded25aaebebb1ce3409a759a521e14",
        "7df63fe892ac14382f226ea97dbd2ac186a8cb48213faec958ad32c51d51aeb5",
        "e9c53248c2f9bb4b86ec5631fe93f7901352cf200b781f1682de06092eff6bbf",
    ),
    _exact_bootstrap_requirement_transition(
        "pdd/prompts/evidence_manifest_python.prompt",
        "python",
        "3b50a00e8deca49c70b127540a2e589aa3715a498b775ab4ddb482adb65eac6f",
        "55f2de2533a461b1d26f4c7641edd6c2c7c05858dc98102ed6f9df04d552e24d",
        "7df63fe892ac14382f226ea97dbd2ac186a8cb48213faec958ad32c51d51aeb5",
        "e9c53248c2f9bb4b86ec5631fe93f7901352cf200b781f1682de06092eff6bbf",
    ),
    _exact_bootstrap_requirement_transition(
        "pdd/prompts/get_jwt_token_python.prompt",
        "python",
        "f1fe2cab01019fd81d683c40511bfd09e698bd44458a4a4dd0b2158c82369ca3",
        "bb767fbd2936c5667b4e7faa71cb06e2fc32d8fe25db822715f100836cff2617",
        "7df63fe892ac14382f226ea97dbd2ac186a8cb48213faec958ad32c51d51aeb5",
        "e9c53248c2f9bb4b86ec5631fe93f7901352cf200b781f1682de06092eff6bbf",
    ),
    _exact_bootstrap_requirement_transition(
        "pdd/prompts/user_story_tests_python.prompt",
        "python",
        "81256961dd9cfbfbc998e3b34720a9cb7915cd81484a1857898f45b1585e63b2",
        "c63d875cc5d488b8fd9bfdd72ea015f33962d22b5cde90b9be751de55a209e32",
        "7df63fe892ac14382f226ea97dbd2ac186a8cb48213faec958ad32c51d51aeb5",
        "e9c53248c2f9bb4b86ec5631fe93f7901352cf200b781f1682de06092eff6bbf",
    ),
    _exact_bootstrap_requirement_transition(
        "pdd/prompts/commands/generate_python.prompt",
        "python",
        "83b45ad928a9bac3567dea786c4b48819400247e63c7210d8cb5d26e4750a52f",
        "503f997914734dbef8e0542efd1f3c495fa15a652782e15bf63638e35c841403",
        "96eca0b44f3a82593e4b79ec03a1bf3d6c6a80b5a1b3cfb69733735a7dd24251",
        "e6182473e28ea13ff6075902267370a78315a426c847b43e5868db62e680803c",
    ),
    _exact_bootstrap_requirement_transition(
        "pdd/prompts/core/cli_python.prompt",
        "python",
        "f1d49d5906b0a00226a0b33cf74be34ca4970efccc9531dbcd1b96c4b57e3724",
        "e01fb2968590ca4911044ef59f1091c2ea5de10b6257941078c63282c52e7d37",
        "96eca0b44f3a82593e4b79ec03a1bf3d6c6a80b5a1b3cfb69733735a7dd24251",
        "e6182473e28ea13ff6075902267370a78315a426c847b43e5868db62e680803c",
    ),
)


# One long-lived pre-schema-2 unit first becomes managed in pdd#1790. Bind its
# initial profile to the exact candidate policy and prompt bytes so the merged
# protected checker can authorize that addition without granting a general
# candidate-only profile escape hatch.
_BOOTSTRAP_PROFILE_ADDITIONS = (
    (
        PurePosixPath("pdd/prompts/checkup_agentic_artifact_python.prompt"),
        "python",
        "CONTRACT-SHA256:dc4db042ae408dcd90c0dcfe4fb9607421e331f024f56de8e22ca1272d0df1f7",
        "e9c53248c2f9bb4b86ec5631fe93f7901352cf200b781f1682de06092eff6bbf",
        "dc4db042ae408dcd90c0dcfe4fb9607421e331f024f56de8e22ca1272d0df1f7",
    ),
    (
        PurePosixPath("pdd/prompts/story_detection_result_python.prompt"),
        "python",
        "CONTRACT-SHA256:dd66389e2ec13002ff56ae34625443f463164a4fcadf51af6a98982c49ae01c3",
        "e9c53248c2f9bb4b86ec5631fe93f7901352cf200b781f1682de06092eff6bbf",
        "dd66389e2ec13002ff56ae34625443f463164a4fcadf51af6a98982c49ae01c3",
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
) -> tuple[_PolicyRotationAuthorization, ...]:
    """Load narrowly-scoped profile rotation authority from the protected base."""
    raw = read_git_blob(root, protected_base_ref, ROTATION_POLICY_PATH)
    if raw is None:
        return ()
    try:
        payload = json.loads(raw)
        rows = payload["rotations"]
        if payload.get("schema_version") not in {1, 2} or not isinstance(rows, list):
            raise TypeError
    except (json.JSONDecodeError, TypeError, UnicodeDecodeError) as exc:
        raise VerificationProfileError(
            "protected profile rotation policy is malformed"
        ) from exc

    authorizations: list[_PolicyRotationAuthorization] = []
    for row in rows:
        if not isinstance(row, dict) or set(row) != {
            "obligation_id",
            "validator_id",
            "from_config_digest",
            "policy_path",
        }:
            raise VerificationProfileError(
                "protected profile rotation rule is malformed"
            )
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
            raise VerificationProfileError(
                "protected profile rotation rule is not authorized"
            )
        authorizations.append(authorization)
    if len(authorizations) != len(set(authorizations)):
        raise VerificationProfileError(
            "protected profile rotation rules are duplicated"
        )
    return tuple(authorizations)


def _sha256(raw: bytes) -> str:
    """Return the lowercase SHA-256 identity used by rotation policy."""
    return hashlib.sha256(raw).hexdigest()


def _valid_requirement_transition(
    authorization: _RequirementTransitionAuthorization,
) -> bool:
    """Validate one bounded, repository-relative opaque transition rule."""
    prompt_path = authorization.prompt_path
    path_valid = (
        not prompt_path.is_absolute()
        and bool(prompt_path.parts)
        and ".." not in prompt_path.parts
    )
    requirements_valid = (
        authorization.from_requirement_id != authorization.to_requirement_id
        and _OPAQUE_REQUIREMENT_ID.fullmatch(authorization.from_requirement_id)
        is not None
        and _OPAQUE_REQUIREMENT_ID.fullmatch(authorization.to_requirement_id)
        is not None
    )
    bindings = authorization.bindings
    digest_valid = all(
        re.fullmatch(r"[0-9a-f]{64}", item) is not None
        for item in (
            bindings.base_policy_sha256,
            bindings.head_policy_sha256,
            bindings.base_prompt_sha256,
            bindings.head_prompt_sha256,
        )
    )
    return (
        authorization.policy_path == PROFILE_PATH
        and path_valid
        and bool(authorization.language_id)
        and authorization.language_id.strip() == authorization.language_id
        and requirements_valid
        and digest_valid
    )


def _parse_requirement_transition_authorizations(
    raw: bytes | None, source: str
) -> tuple[_RequirementTransitionAuthorization, ...]:
    """Parse one strict schema-2 transition policy without granting authority."""
    if raw is None:
        return ()
    try:
        payload = json.loads(raw)
        if not isinstance(payload, dict):
            raise TypeError
        if payload.get("schema_version") == 1:
            return ()
        rows = payload["requirement_rotations"]
        if (
            payload.get("schema_version") != 2
            or not isinstance(rows, list)
            or len(rows) > _MAX_REQUIREMENT_TRANSITIONS
        ):
            raise TypeError
    except (json.JSONDecodeError, TypeError, UnicodeDecodeError) as exc:
        raise VerificationProfileError(
            f"{source} requirement transition policy is malformed"
        ) from exc

    required_keys = {
        "prompt_path",
        "language_id",
        "from_requirement_id",
        "to_requirement_id",
        "policy_path",
        "base_policy_sha256",
        "head_policy_sha256",
        "base_prompt_sha256",
        "head_prompt_sha256",
    }
    authorizations = []
    for row in rows:
        if (
            not isinstance(row, dict)
            or set(row) != required_keys
            or any(not isinstance(row[key], str) for key in required_keys)
        ):
            raise VerificationProfileError(
                f"{source} requirement transition rule is malformed"
            )
        authorization = _RequirementTransitionAuthorization(
            PurePosixPath(row["prompt_path"]),
            row["language_id"],
            row["from_requirement_id"],
            row["to_requirement_id"],
            PurePosixPath(row["policy_path"]),
            _RequirementTransitionBindings(
                row["base_policy_sha256"],
                row["head_policy_sha256"],
                row["base_prompt_sha256"],
                row["head_prompt_sha256"],
            ),
        )
        if not _valid_requirement_transition(authorization):
            raise VerificationProfileError(
                f"{source} requirement transition rule is malformed"
            )
        authorizations.append(authorization)
    identities = [(item.prompt_path, item.language_id) for item in authorizations]
    if len(authorizations) != len(set(authorizations)) or len(identities) != len(
        set(identities)
    ):
        raise VerificationProfileError(
            f"{source} requirement transition rules are duplicated or ambiguous"
        )
    return tuple(authorizations)


def _load_requirement_transition_authorizations(
    root: Path, manifest: UnitManifest
) -> tuple[_RequirementTransitionAuthorization, ...]:
    """Accept candidate rules only when protected earlier or exactly bootstrapped."""
    protected = _parse_requirement_transition_authorizations(
        read_git_blob(root, manifest.base_ref, ROTATION_POLICY_PATH), "protected"
    )
    candidate = _parse_requirement_transition_authorizations(
        read_git_blob(root, manifest.head_ref, ROTATION_POLICY_PATH), "candidate"
    )
    authority = set(protected)
    if manifest.repository_id == _PDD_REPOSITORY_ID:
        authority.update(_BOOTSTRAP_REQUIREMENT_TRANSITIONS)
    if any(item not in authority for item in candidate):
        raise VerificationProfileError(
            "candidate requirement transition lacks protected authorization"
        )
    return candidate


def _transition_bytes_match(
    authorization: _RequirementTransitionAuthorization,
    base_policy: bytes | None,
    head_policy: bytes | None,
    base_prompt: bytes | None,
    head_prompt: bytes | None,
) -> bool:
    """Check all four byte identities and both derived requirement identities."""
    if None in (base_policy, head_policy, base_prompt, head_prompt):
        return False
    assert base_policy is not None and head_policy is not None
    assert base_prompt is not None and head_prompt is not None
    bindings = authorization.bindings
    return (
        _sha256(base_policy) == bindings.base_policy_sha256
        and _sha256(head_policy) == bindings.head_policy_sha256
        and _sha256(base_prompt) == bindings.base_prompt_sha256
        and _sha256(head_prompt) == bindings.head_prompt_sha256
        and _prompt_requirements(base_prompt) == (authorization.from_requirement_id,)
        and _prompt_requirements(head_prompt) == (authorization.to_requirement_id,)
    )


def _expected_requirement_update(
    authorization: _RequirementTransitionAuthorization,
    protected: _ProfileInput,
    candidate: _ProfileInput,
) -> tuple[_ProfileInput | None, str | None]:
    """Return the sole permitted profile delta for one exact prompt transition."""
    obligations = {item.obligation_id: item for item in protected.obligations}
    human = obligations.get(_HUMAN_OBLIGATION_ID)
    human_matches = (
        human is not None
        and human.kind == "human-attestation"
        and human.validator_id == _HUMAN_VALIDATOR_ID
        and human.requirement_ids == (authorization.from_requirement_id,)
        and human.required
    )
    if (
        protected.requirements != (authorization.from_requirement_id,)
        or candidate.requirements != (authorization.to_requirement_id,)
        or not human_matches
    ):
        return None, "requirement transition is partial or mismatched"
    assert human is not None
    obligations[_HUMAN_OBLIGATION_ID] = replace(
        human, requirement_ids=(authorization.to_requirement_id,)
    )
    expected = _ProfileInput(
        (authorization.to_requirement_id,), tuple(sorted(obligations.values()))
    )
    if candidate != expected:
        return None, "requirement transition changes protected fields"
    return expected, None


def _matches_bound_stationary_state(
    profile: _ProfileInput | None,
    policies: tuple[bytes | None, bytes | None],
    prompts: tuple[bytes | None, bytes | None],
    state: tuple[str, str, str],
) -> bool:
    """Return whether both refs hold one exact dormant or consumed state."""
    requirement_id, policy_digest, prompt_digest = state
    return (
        profile is not None
        and profile.requirements == (requirement_id,)
        and policies[0] == policies[1]
        and prompts[0] == prompts[1]
        and policies[0] is not None
        and prompts[0] is not None
        and _sha256(policies[0]) == policy_digest
        and _sha256(prompts[0]) == prompt_digest
        and _prompt_requirements(prompts[0]) == (requirement_id,)
    )


def _matches_unchanged_requirement_state(
    profile: _ProfileInput,
    prompts: tuple[bytes | None, bytes | None],
    authorization: _RequirementTransitionAuthorization,
) -> bool:
    """Keep one exact row dormant across unrelated profile-file rotations."""
    if prompts[0] is None or prompts[0] != prompts[1]:
        return False
    prompt_digest = _sha256(prompts[0])
    states = (
        (
            authorization.from_requirement_id,
            authorization.bindings.base_prompt_sha256,
        ),
        (
            authorization.to_requirement_id,
            authorization.bindings.head_prompt_sha256,
        ),
    )
    return any(
        profile.requirements == (requirement_id,)
        and prompt_digest == bound_prompt_digest
        and _prompt_requirements(prompts[0]) == (requirement_id,)
        for requirement_id, bound_prompt_digest in states
    )


def _evaluate_requirement_authorization(
    context: _RequirementTransitionContext,
    authorization: _RequirementTransitionAuthorization,
) -> tuple[UnitId, _ProfileInput | None, str | None]:
    """Evaluate one rule as dormant, consumed, exact, or invalid."""
    unit_id = UnitId(
        context.manifest.repository_id,
        authorization.prompt_path,
        authorization.language_id,
    )
    protected, candidate = context.base.get(unit_id), context.head.get(unit_id)
    if protected is None or candidate is None:
        # Existing profile accounting owns missing/candidate-only units. A
        # dormant transition must not duplicate those stable reasons or counts.
        return unit_id, None, None
    prompts = (
        read_git_blob(
            context.root, context.manifest.base_ref, authorization.prompt_path
        ),
        read_git_blob(
            context.root, context.manifest.head_ref, authorization.prompt_path
        ),
    )
    bindings = authorization.bindings
    stationary = protected == candidate and (
        _matches_unchanged_requirement_state(protected, prompts, authorization)
        or _matches_bound_stationary_state(
            protected,
            context.policies,
            prompts,
            (
                authorization.from_requirement_id,
                bindings.base_policy_sha256,
                bindings.base_prompt_sha256,
            ),
        )
        or _matches_bound_stationary_state(
            protected,
            context.policies,
            prompts,
            (
                authorization.to_requirement_id,
                bindings.head_policy_sha256,
                bindings.head_prompt_sha256,
            ),
        )
    )
    if stationary:
        return unit_id, None, None
    if not _transition_bytes_match(
        authorization,
        context.policies[0],
        context.policies[1],
        prompts[0],
        prompts[1],
    ):
        return unit_id, None, "requirement transition bindings mismatch"
    result, reason = _expected_requirement_update(authorization, protected, candidate)
    return unit_id, result, reason


def _authorized_requirement_updates(
    root: Path,
    manifest: UnitManifest,
    base: dict[UnitId, _ProfileInput],
    head: dict[UnitId, _ProfileInput],
    authorizations: tuple[_RequirementTransitionAuthorization, ...],
) -> tuple[dict[UnitId, _ProfileInput], list[str]]:
    """Authorize only exact opaque requirement and human mapping replacements."""
    updates: dict[UnitId, _ProfileInput] = {}
    invalid: list[str] = []
    policies = (
        read_git_blob(root, manifest.base_ref, PROFILE_PATH),
        read_git_blob(root, manifest.head_ref, PROFILE_PATH),
    )
    context = _RequirementTransitionContext(root, manifest, base, head, policies)
    for authorization in authorizations:
        unit_id, result, reason = _evaluate_requirement_authorization(
            context, authorization
        )
        if reason is not None:
            invalid.append(f"{authorization.prompt_path}: {reason}")
            continue
        if result is not None:
            updates[unit_id] = result
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
        config_unchanged = all(
            any(
                candidate.obligation_id == obligation.obligation_id
                and candidate.validator_config_digest
                == authorization.from_config_digest
                for candidate in head.get(unit_id, _ProfileInput((), ())).obligations
            )
            for unit_id, obligation in protected
        )
        if config_unchanged:
            continue
        policy = read_git_blob(root, manifest.head_ref, authorization.policy_path)
        if policy is None:
            invalid.append(
                "authorized profile rotation policy is absent from candidate"
            )
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


def _authorized_profile_additions(
    root: Path,
    manifest: UnitManifest,
    base: Mapping[UnitId, _ProfileInput],
    head: Mapping[UnitId, _ProfileInput],
) -> dict[UnitId, _ProfileInput]:
    """Authorize only repository-bound, exact-byte initial profile additions."""
    if manifest.repository_id != _PDD_REPOSITORY_ID:
        return {}
    candidate_policy = read_git_blob(root, manifest.head_ref, PROFILE_PATH)
    if candidate_policy is None:
        return {}
    candidate_policy_digest = _sha256(candidate_policy)
    expected_units = set(manifest.expected_managed)
    additions: dict[UnitId, _ProfileInput] = {}
    for addition in _BOOTSTRAP_PROFILE_ADDITIONS:
        unit_id = UnitId(manifest.repository_id, addition[0], addition[1])
        if unit_id not in expected_units or unit_id in base or unit_id not in head:
            continue
        base_prompt = read_git_blob(root, manifest.base_ref, addition[0])
        candidate_prompt = read_git_blob(root, manifest.head_ref, addition[0])
        if (
            base_prompt is not None
            or candidate_prompt is None
            or candidate_policy_digest != addition[3]
            or _sha256(candidate_prompt) != addition[4]
            or _prompt_requirements(candidate_prompt) != (addition[2],)
        ):
            continue
        expected = _ProfileInput(
            (addition[2],),
            (
                VerificationObligation(
                    _HUMAN_OBLIGATION_ID,
                    "human-attestation",
                    _HUMAN_VALIDATOR_ID,
                    _PLACEHOLDER_POLICY_DIGEST,
                    (addition[2],),
                    (addition[0],),
                    True,
                ),
            ),
        )
        if head[unit_id] == expected:
            additions[unit_id] = expected
    return additions


def _effective_profile(
    unit_id: UnitId,
    base: _ProfileInput | None,
    head: _ProfileInput | None,
    authorized: _AuthorizedProfileUpdates,
) -> tuple[VerificationProfile, list[str]]:
    invalid: list[str] = []
    if base is None and unit_id in authorized.requirements:
        base = authorized.requirements[unit_id]
    if base is None and head is not None:
        invalid.append(
            f"{unit_id.prompt_relpath}: candidate-only profile lacks protected approval"
        )
        head = None
    if unit_id in authorized.requirements:
        base = authorized.requirements[unit_id]
    base_requirements = set(base.requirements if base else ())
    if base_requirements - set(head.requirements if head else ()):
        invalid.append(
            f"{unit_id.prompt_relpath}: candidate removed protected requirements"
        )
    requirements = tuple(
        sorted(base_requirements | set(head.requirements if head else ()))
    )
    base_obligations = {
        item.obligation_id: item for item in (base.obligations if base else ())
    }
    head_obligations = {
        item.obligation_id: item for item in (head.obligations if head else ())
    }
    effective = dict(base_obligations)
    for obligation_id, obligation in head_obligations.items():
        protected = base_obligations.get(obligation_id)
        if protected is not None and protected != obligation:
            if authorized.obligations.get((unit_id, obligation_id)) == obligation:
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


def _build_effective_profiles(
    manifest: UnitManifest,
    base: dict[UnitId, _ProfileInput],
    head: dict[UnitId, _ProfileInput],
    authorized: _AuthorizedProfileUpdates,
) -> tuple[list[VerificationProfile], list[str]]:
    """Build the protected denominator without reducing missing or unknown units."""
    profiles: list[VerificationProfile] = []
    invalid: list[str] = []
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
            unit_id, base.get(unit_id), head.get(unit_id), authorized
        )
        profiles.append(profile)
        invalid.extend(profile_invalid)
    return profiles, invalid


def load_verification_profiles(root: Path, manifest: UnitManifest) -> ProfileSet:
    """Load the protected base/candidate union for every expected-managed unit."""
    invalid: list[str] = []
    try:
        approved_aliases = load_protected_aliases(root, manifest)
    except ValueError as exc:
        approved_aliases = {}
        invalid.append(str(exc))
    base, loaded_invalid = _load_inputs(
        root, manifest.base_ref, manifest.repository_id, approved_aliases
    )
    invalid.extend(loaded_invalid)
    head, loaded_invalid = _load_inputs(
        root, manifest.head_ref, manifest.repository_id, approved_aliases
    )
    invalid.extend(loaded_invalid)
    requirement_updates, requirement_invalid = _authorized_requirement_updates(
        root,
        manifest,
        base,
        head,
        _load_requirement_transition_authorizations(root, manifest),
    )
    invalid.extend(requirement_invalid)
    profile_additions = _authorized_profile_additions(root, manifest, base, head)
    requirement_updates = {**profile_additions, **requirement_updates}
    authorized_updates, rotation_invalid = _authorized_rotation_updates(
        root,
        manifest,
        base,
        head,
        _load_rotation_authorizations(root, manifest.base_ref),
    )
    invalid.extend(rotation_invalid)
    profiles, profile_invalid = _build_effective_profiles(
        manifest,
        base,
        head,
        _AuthorizedProfileUpdates(authorized_updates, requirement_updates),
    )
    invalid.extend(profile_invalid)
    return ProfileSet(tuple(profiles), tuple(sorted(set(invalid))))
