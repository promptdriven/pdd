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
        "379831026c7d037c2b7b529d48fcff8f33bfeb909b3608cc56aa35abdffa4134",
        "08e0c842d842974340b7ed3424f71fa20379c6922aaa6cfbca232d7d83a9a255",
        "71b12a08e5be55b958a737decde889c189f7ca00ceaddccd7b587f9c8b2a4b64",
        "f7df311558fb327cd21d8900ad1a9dc6d5a8145773a693fc3afd43a93a128c51",
    ),
    _exact_bootstrap_requirement_transition(
        "pdd/prompts/agentic_checkup_python.prompt",
        "python",
        "fef53dad8950c06cc11e41265956a2ee174a90ff9e4985d7f30610f18c47b08b",
        "1812c6d204e346d0745403c908a47e5d4d42b53612efd61efbe40af04ba4b868",
        "7df63fe892ac14382f226ea97dbd2ac186a8cb48213faec958ad32c51d51aeb5",
        "8e3ba247e42d1a4e1df3e1ba968b390595aa1173184f93419eea16af32fa89fc",
    ),
    _exact_bootstrap_requirement_transition(
        "pdd/prompts/agentic_checkup_step6_1_fix_LLM.prompt",
        "llm",
        "06f45aca3883f78f46fa9bdf37140b63aa3a41db27086aedba60abc9f480ade2",
        "a845a9233b62d960473389533733fbb5c02ce32868671394211d649a9a32eae5",
        "7df63fe892ac14382f226ea97dbd2ac186a8cb48213faec958ad32c51d51aeb5",
        "8e3ba247e42d1a4e1df3e1ba968b390595aa1173184f93419eea16af32fa89fc",
    ),
    _exact_bootstrap_requirement_transition(
        "pdd/prompts/agentic_checkup_step6_2_regression_tests_LLM.prompt",
        "llm",
        "b2253412164e803a93e6dd73abf8c4a0342af68f1ef94149096112252654b93d",
        "dd1060236858bc50923f247b064e5e94bb69fb8fd895e914fdfb3a6579958a28",
        "7df63fe892ac14382f226ea97dbd2ac186a8cb48213faec958ad32c51d51aeb5",
        "8e3ba247e42d1a4e1df3e1ba968b390595aa1173184f93419eea16af32fa89fc",
    ),
    _exact_bootstrap_requirement_transition(
        "pdd/prompts/agentic_checkup_step6_3_e2e_tests_LLM.prompt",
        "llm",
        "7f686093bfe73ab67b4e27fc878bc48706276732feb5670f34f7aa463e65e355",
        "9b771b0d5770610225a4bd2f5aca484fc8ab15216203ce290d4c4c0cf3de1d53",
        "7df63fe892ac14382f226ea97dbd2ac186a8cb48213faec958ad32c51d51aeb5",
        "8e3ba247e42d1a4e1df3e1ba968b390595aa1173184f93419eea16af32fa89fc",
    ),
    _exact_bootstrap_requirement_transition(
        "pdd/prompts/checkup_review_loop_python.prompt",
        "python",
        "a7fd72cadb0644d4d20d09868cc8e908e3122478e6127b3943de32b711d76c02",
        "c5ec02fb049e1359da107067d65e725b3ad0a8cca4da6fd31328821f6b6d1c73",
        "71b12a08e5be55b958a737decde889c189f7ca00ceaddccd7b587f9c8b2a4b64",
        "f7df311558fb327cd21d8900ad1a9dc6d5a8145773a693fc3afd43a93a128c51",
    ),
    _exact_bootstrap_requirement_transition(
        "pdd/prompts/ci_drift_heal_python.prompt",
        "python",
        "fc595464ceb1bac758864cd66a87fd1ba4f72bae79660a1dd334e060cbb861f7",
        "54f1c25a8cdbf5d1a724981f6fe9f9b6fbe5b20988f30fd2183c24b60d932d88",
        "71b12a08e5be55b958a737decde889c189f7ca00ceaddccd7b587f9c8b2a4b64",
        "f7df311558fb327cd21d8900ad1a9dc6d5a8145773a693fc3afd43a93a128c51",
    ),
    _exact_bootstrap_requirement_transition(
        "pdd/prompts/story_regression_python.prompt",
        "python",
        "e5cc19e846c9fefe9608658c6186b911420c0fe4a769ed28a6be267d070909e4",
        "88ba7a932f444bb1b91e17429ca8c211742fadc8457b96d71b648b2529785d4f",
        "7df63fe892ac14382f226ea97dbd2ac186a8cb48213faec958ad32c51d51aeb5",
        "8e3ba247e42d1a4e1df3e1ba968b390595aa1173184f93419eea16af32fa89fc",
    ),
)


# #1989 follows the schema-2 installation above. Each GPT-5.6 prompt/profile
# replacement is bound to the actual merged base and exact candidate bytes.
_PDD_1989_BOOTSTRAP_REQUIREMENT_TRANSITIONS = (
    _exact_bootstrap_requirement_transition(
        "pdd/prompts/agentic_common_python.prompt",
        "python",
        "c00fe698b5d829e1f2801c290f1bf425d2e7b392b733b7916519c6c39528b900",
        "e6568d79e16a7638ef275c71858d1c2468f593b1369ea602312524a9fef0b37c",
        "71b12a08e5be55b958a737decde889c189f7ca00ceaddccd7b587f9c8b2a4b64",
        "f7df311558fb327cd21d8900ad1a9dc6d5a8145773a693fc3afd43a93a128c51",
    ),
    _exact_bootstrap_requirement_transition(
        "pdd/prompts/commands/checkup_python.prompt",
        "python",
        "e31b6d61a09a408b41e769794587ac734cd72cb54b2dcb62c327683e586a6f20",
        "b453bb71475123c5545a37dd23bbff9f057d960b775c0e977151ee98a9b976e0",
        "f0f1d36e337541ba4425f081e236c42847f8132cb61f9f8fe06334a805fc5c7b",
        "71b12a08e5be55b958a737decde889c189f7ca00ceaddccd7b587f9c8b2a4b64",
    ),
    _exact_bootstrap_requirement_transition(
        "pdd/prompts/generate_model_catalog_python.prompt",
        "python",
        "1e0ffc1fb8e8172bb396b8050c67bfbf750e28bd4191ffb63f7d664d0530827e",
        "a086fdc50c2cb54bcd0543e467106dbc2fb87c3b2f196bfcc0f51b7ecf3bed97",
        "f0f1d36e337541ba4425f081e236c42847f8132cb61f9f8fe06334a805fc5c7b",
        "71b12a08e5be55b958a737decde889c189f7ca00ceaddccd7b587f9c8b2a4b64",
    ),
    _exact_bootstrap_requirement_transition(
        "pdd/prompts/llm_invoke_python.prompt",
        "python",
        "532c327642ab94293bc770e9367670416988eb075dd7bc6552ae8bf154b1d031",
        "15c51e9dbc3bb536ab6d6dfa1a7927a30f33b1423398e326e5a06f9524896735",
        "f0f1d36e337541ba4425f081e236c42847f8132cb61f9f8fe06334a805fc5c7b",
        "71b12a08e5be55b958a737decde889c189f7ca00ceaddccd7b587f9c8b2a4b64",
    ),
    _exact_bootstrap_requirement_transition(
        "pdd/prompts/prompt_repair_python.prompt",
        "python",
        "915a3f4e69e31010f156cc381d873ba75c6777365780ffc6d69020e914b0c846",
        "d136f2f47483b0a17b9f733402ecfe1d2e8d69540c054043eeee8a752aa69562",
        "f0f1d36e337541ba4425f081e236c42847f8132cb61f9f8fe06334a805fc5c7b",
        "71b12a08e5be55b958a737decde889c189f7ca00ceaddccd7b587f9c8b2a4b64",
    ),
    _exact_bootstrap_requirement_transition(
        "pdd/prompts/routing_policy_python.prompt",
        "python",
        "bd348ce36f1b63ddc9b12bc36e1a14b3206cb35491d278f9735375f1f39d9dc6",
        "3971482288276694f054c7fed70a09e43595b151d514200110b5f1937ee932ab",
        "f0f1d36e337541ba4425f081e236c42847f8132cb61f9f8fe06334a805fc5c7b",
        "71b12a08e5be55b958a737decde889c189f7ca00ceaddccd7b587f9c8b2a4b64",
    ),
    _exact_bootstrap_requirement_transition(
        "pdd/prompts/setup_tool_python.prompt",
        "python",
        "bb4e712d004c8c5afccc584629266eb7df00520483aacfd78aa27c2ef0cd2232",
        "2358501051357b8b7150c7aabdc470500d3869179a3c057948f01e9a63983ab6",
        "f0f1d36e337541ba4425f081e236c42847f8132cb61f9f8fe06334a805fc5c7b",
        "71b12a08e5be55b958a737decde889c189f7ca00ceaddccd7b587f9c8b2a4b64",
    ),
)
_BOOTSTRAP_REQUIREMENT_TRANSITIONS += _PDD_1989_BOOTSTRAP_REQUIREMENT_TRANSITIONS


# #2052 adds five non-overlapping protected prompt transitions. Its
# llm_invoke transition is composed into #1989 below because both branches
# modify that prompt.
_PDD_2052_BOOTSTRAP_REQUIREMENT_TRANSITIONS = (
    _exact_bootstrap_requirement_transition(
        "pdd/prompts/commands/analysis_python.prompt",
        "python",
        "0e6824053f24a2230d51000fd998ff01ebeb56a4784660757a811dc86894c1a4",
        "5aff15e367047ac59ad70b842c7a0a59cdf266526e09df274f56f7928413aafd",
        "8e3ba247e42d1a4e1df3e1ba968b390595aa1173184f93419eea16af32fa89fc",
        "f0f1d36e337541ba4425f081e236c42847f8132cb61f9f8fe06334a805fc5c7b",
    ),
    _exact_bootstrap_requirement_transition(
        "pdd/prompts/core/cloud_python.prompt",
        "python",
        "565f81380607551771e87da37bf291f553141513a7f8bad618d3344ee9dc15c8",
        "4c32578f0c81d4357d2760a388a930d9feded25aaebebb1ce3409a759a521e14",
        "8e3ba247e42d1a4e1df3e1ba968b390595aa1173184f93419eea16af32fa89fc",
        "f0f1d36e337541ba4425f081e236c42847f8132cb61f9f8fe06334a805fc5c7b",
    ),
    _exact_bootstrap_requirement_transition(
        "pdd/prompts/evidence_manifest_python.prompt",
        "python",
        "55f2de2533a461b1d26f4c7641edd6c2c7c05858dc98102ed6f9df04d552e24d",
        "2592f4de642e97d39c3ed3f9ee068af9c5bb80f0fca027e7f476ac0eb8787de9",
        "71b12a08e5be55b958a737decde889c189f7ca00ceaddccd7b587f9c8b2a4b64",
        "f7df311558fb327cd21d8900ad1a9dc6d5a8145773a693fc3afd43a93a128c51",
    ),
    _exact_bootstrap_requirement_transition(
        "pdd/prompts/get_jwt_token_python.prompt",
        "python",
        "f1fe2cab01019fd81d683c40511bfd09e698bd44458a4a4dd0b2158c82369ca3",
        "8f0d40d0303377678052509c9d6c1b1b3ca023f51ab95d2d3982af23c50ecf79",
        "8e3ba247e42d1a4e1df3e1ba968b390595aa1173184f93419eea16af32fa89fc",
        "f0f1d36e337541ba4425f081e236c42847f8132cb61f9f8fe06334a805fc5c7b",
    ),
    _exact_bootstrap_requirement_transition(
        "pdd/prompts/user_story_tests_python.prompt",
        "python",
        "81256961dd9cfbfbc998e3b34720a9cb7915cd81484a1857898f45b1585e63b2",
        "c63d875cc5d488b8fd9bfdd72ea015f33962d22b5cde90b9be751de55a209e32",
        "8e3ba247e42d1a4e1df3e1ba968b390595aa1173184f93419eea16af32fa89fc",
        "f0f1d36e337541ba4425f081e236c42847f8132cb61f9f8fe06334a805fc5c7b",
    ),
)
_BOOTSTRAP_REQUIREMENT_TRANSITIONS += _PDD_2052_BOOTSTRAP_REQUIREMENT_TRANSITIONS


# #2077 retains the one dormant generate estimate transition. It is bound to
# the exact profile composition after the current prompt-source transitions.
_PDD_1989_COMPOSED_ESTIMATE_REQUIREMENT_TRANSITIONS = (
    _exact_bootstrap_requirement_transition(
        "pdd/prompts/commands/generate_python.prompt",
        "python",
        "83b45ad928a9bac3567dea786c4b48819400247e63c7210d8cb5d26e4750a52f",
        "503f997914734dbef8e0542efd1f3c495fa15a652782e15bf63638e35c841403",
        "f7df311558fb327cd21d8900ad1a9dc6d5a8145773a693fc3afd43a93a128c51",
        "1f3b574c8e8d800a27444243affa6e8f7a2302a4cbd09d75b2aebcaa72c2986d",
    ),
    _exact_bootstrap_requirement_transition(
        "pdd/prompts/core/cli_python.prompt",
        "python",
        "f1d49d5906b0a00226a0b33cf74be34ca4970efccc9531dbcd1b96c4b57e3724",
        "779a19a53bdbb3c7ad5dbf4afb9fb29cf3f04b56e9bfc488552ed0eff823f46e",
        "71b12a08e5be55b958a737decde889c189f7ca00ceaddccd7b587f9c8b2a4b64",
        "f7df311558fb327cd21d8900ad1a9dc6d5a8145773a693fc3afd43a93a128c51",
    ),
)
_BOOTSTRAP_REQUIREMENT_TRANSITIONS += (
    _PDD_1989_COMPOSED_ESTIMATE_REQUIREMENT_TRANSITIONS
)


# #1998 reconciles every remaining replay-modified prompt with its exact
# protected profile bytes. These entries authorize only the reviewed base/head
# pairs; no candidate may self-authorize a different profile transition.
_REPLAY_PROMPT_REQUIREMENT_TRANSITIONS = (
    _exact_bootstrap_requirement_transition(
        "pdd/prompts/agentic_architecture_orchestrator_python.prompt",
        "python",
        "970bd3a10391c1ed87995920e3c25ee3a67844db4796c3e6104573774f47dee4",
        "24086f8a716d9bf49d291f6eecab9d6ab0594f2388610609497aa9a6870be4a1",
        "71b12a08e5be55b958a737decde889c189f7ca00ceaddccd7b587f9c8b2a4b64",
        "f7df311558fb327cd21d8900ad1a9dc6d5a8145773a693fc3afd43a93a128c51",
    ),
    _exact_bootstrap_requirement_transition(
        "pdd/prompts/agentic_bug_orchestrator_python.prompt",
        "python",
        "80577f381e7185bd9a77f32b8be81079166b5881e5ca148cdab020dcb7069e11",
        "dfbaabe591842937fd2141208b1b3c4104b7b89bf32d261d96a61830cc7fc872",
        "71b12a08e5be55b958a737decde889c189f7ca00ceaddccd7b587f9c8b2a4b64",
        "f7df311558fb327cd21d8900ad1a9dc6d5a8145773a693fc3afd43a93a128c51",
    ),
    _exact_bootstrap_requirement_transition(
        "pdd/prompts/agentic_change_orchestrator_python.prompt",
        "python",
        "868b316bb60d886ebf0be7f52fb940296abd11804606bde83b841f812bf660d8",
        "a5f609c2aa21b86d5b1bdb1ef7b36207c40326fc85b617c8b7d7b99dc5b23b9c",
        "71b12a08e5be55b958a737decde889c189f7ca00ceaddccd7b587f9c8b2a4b64",
        "f7df311558fb327cd21d8900ad1a9dc6d5a8145773a693fc3afd43a93a128c51",
    ),
    _exact_bootstrap_requirement_transition(
        "pdd/prompts/agentic_e2e_fix_orchestrator_python.prompt",
        "python",
        "179b3c8cba5ce703f943a0ebcf6f7c540d34d23e50506e7456d0aebec640726c",
        "91bc4b2ab37fca4aeb1c8ed135f694fd9b75273e50a482563ae674bc4124619f",
        "71b12a08e5be55b958a737decde889c189f7ca00ceaddccd7b587f9c8b2a4b64",
        "f7df311558fb327cd21d8900ad1a9dc6d5a8145773a693fc3afd43a93a128c51",
    ),
    _exact_bootstrap_requirement_transition(
        "pdd/prompts/agentic_e2e_fix_step9_verify_all_LLM.prompt",
        "llm",
        "228b06c686e6e8c416e2ab753791b4d4d63ae23fb14c810e9433870e34d0ed0e",
        "ec4e7456f445fa227a7bfeb58e55d2ef1fbec9cd3bd7cc51222a5d5474bdf27d",
        "71b12a08e5be55b958a737decde889c189f7ca00ceaddccd7b587f9c8b2a4b64",
        "f7df311558fb327cd21d8900ad1a9dc6d5a8145773a693fc3afd43a93a128c51",
    ),
    _exact_bootstrap_requirement_transition(
        "pdd/prompts/agentic_split_orchestrator_python.prompt",
        "python",
        "9c24971f6866c8432a6ae7102eb5777e1c7a36952c3321c577c520f7c8088d39",
        "0436452e88c77dd034d4aa00c20f8d8361830ca8196a5e8ec9c8f69666fc38a6",
        "71b12a08e5be55b958a737decde889c189f7ca00ceaddccd7b587f9c8b2a4b64",
        "f7df311558fb327cd21d8900ad1a9dc6d5a8145773a693fc3afd43a93a128c51",
    ),
    _exact_bootstrap_requirement_transition(
        "pdd/prompts/agentic_sync_python.prompt",
        "python",
        "aa67cf6c09fdd10aa2670a0c8c2dba3b01630b8c18c86c34d3f1ec213b45aad8",
        "5d9f8b0462c925413c1941286ae28c952ba8e5355f01cab3131d9a6e3c0a1659",
        "71b12a08e5be55b958a737decde889c189f7ca00ceaddccd7b587f9c8b2a4b64",
        "f7df311558fb327cd21d8900ad1a9dc6d5a8145773a693fc3afd43a93a128c51",
    ),
    _exact_bootstrap_requirement_transition(
        "pdd/prompts/agentic_sync_runner_python.prompt",
        "python",
        "99010afb8c3a52d2f1a1af15b8fa2c786d5fdcaaddb04b61e8c0ae719f7f23a1",
        "66b8a98d7f8a7d5b82093178be8196f6287125072e888356341f7691f6b66d57",
        "71b12a08e5be55b958a737decde889c189f7ca00ceaddccd7b587f9c8b2a4b64",
        "f7df311558fb327cd21d8900ad1a9dc6d5a8145773a693fc3afd43a93a128c51",
    ),
    _exact_bootstrap_requirement_transition(
        "pdd/prompts/agentic_test_orchestrator_python.prompt",
        "python",
        "068328249e60cfca625096866a6886de55c344e68539b5489e0b57ffdddb9593",
        "9f8e9ba75d0324d83aae431254ed78c8bfb9e73e800cbf06712de780a1c3fe25",
        "71b12a08e5be55b958a737decde889c189f7ca00ceaddccd7b587f9c8b2a4b64",
        "f7df311558fb327cd21d8900ad1a9dc6d5a8145773a693fc3afd43a93a128c51",
    ),
    _exact_bootstrap_requirement_transition(
        "pdd/prompts/ci_validation_python.prompt",
        "python",
        "9e2e7d49234d6edebc86bc0701de53df732c7c5b52621a4be0d25d69e6f9635f",
        "fe775e3133d44e7903ff4b19a18bda48de29d3cd82a9a1526536241e4495d885",
        "71b12a08e5be55b958a737decde889c189f7ca00ceaddccd7b587f9c8b2a4b64",
        "f7df311558fb327cd21d8900ad1a9dc6d5a8145773a693fc3afd43a93a128c51",
    ),
    _exact_bootstrap_requirement_transition(
        "pdd/prompts/cmd_test_main_python.prompt",
        "python",
        "9a96654683807432182c978b529ad6804db23591a602cab866fe592364e012e4",
        "1bc51147fc08fe0f79a6b361ba91378a81b51e6f7262d50c7534f8fa62240063",
        "71b12a08e5be55b958a737decde889c189f7ca00ceaddccd7b587f9c8b2a4b64",
        "f7df311558fb327cd21d8900ad1a9dc6d5a8145773a693fc3afd43a93a128c51",
    ),
    _exact_bootstrap_requirement_transition(
        "pdd/prompts/code_generator_main_python.prompt",
        "python",
        "8d0a51822aaa2c64e1b71579d0cb6e41460b90734441e0b6ec3ec146402495fe",
        "51ec006a5b7faeb397be9c1b8e61205e97459fdc08cd9e90e7f0692ccf55a1d5",
        "71b12a08e5be55b958a737decde889c189f7ca00ceaddccd7b587f9c8b2a4b64",
        "f7df311558fb327cd21d8900ad1a9dc6d5a8145773a693fc3afd43a93a128c51",
    ),
    _exact_bootstrap_requirement_transition(
        "pdd/prompts/commands/fix_python.prompt",
        "python",
        "3e180110a579e905ed0e7eeead2f5b8145a5cbbeed781942b6aaad1e713c3ec6",
        "9665945341cf2ac1860c535d6867cd0082f0184d462765ec277d3887cfaae583",
        "71b12a08e5be55b958a737decde889c189f7ca00ceaddccd7b587f9c8b2a4b64",
        "f7df311558fb327cd21d8900ad1a9dc6d5a8145773a693fc3afd43a93a128c51",
    ),
    _exact_bootstrap_requirement_transition(
        "pdd/prompts/commands/maintenance_python.prompt",
        "python",
        "5f50939cf7cd9dd3cf1269d20cef4ba1e3bbe8c242bd33ccfc4fdeef51d0cda6",
        "d745f41791cabdae9e76dbf21896f3a1dcba3435b6f599ffb9c67c0a8789c9b3",
        "71b12a08e5be55b958a737decde889c189f7ca00ceaddccd7b587f9c8b2a4b64",
        "f7df311558fb327cd21d8900ad1a9dc6d5a8145773a693fc3afd43a93a128c51",
    ),
    _exact_bootstrap_requirement_transition(
        "pdd/prompts/commands/modify_python.prompt",
        "python",
        "8d103ee748926ef9683ba4e0ab70ecfd32b91e9437eaf435767bb42d0beda647",
        "34ec165260531e0fd13b721a7fb9bb2ae5fe70275166044ddd204166adf660be",
        "71b12a08e5be55b958a737decde889c189f7ca00ceaddccd7b587f9c8b2a4b64",
        "f7df311558fb327cd21d8900ad1a9dc6d5a8145773a693fc3afd43a93a128c51",
    ),
    _exact_bootstrap_requirement_transition(
        "pdd/prompts/content_selector_python.prompt",
        "python",
        "df9a157338364189552d43732ed4a565eb5368d4a460a7b249962ff2a2b3a8ad",
        "b2f4bcb592f87c6bb782329df151acbd7045d0562bcf0805b00246d4f1ba0096",
        "71b12a08e5be55b958a737decde889c189f7ca00ceaddccd7b587f9c8b2a4b64",
        "f7df311558fb327cd21d8900ad1a9dc6d5a8145773a693fc3afd43a93a128c51",
    ),
    _exact_bootstrap_requirement_transition(
        "pdd/prompts/durable_sync_runner_python.prompt",
        "python",
        "fb45ad84ba8adb320baadeb47cac7917626dfd0e44916e8ffd6709cd13ccb72e",
        "5bfd76d356efbb0848b013c208909d1d6fc16b1dd7d7ef215457fd14debcf259",
        "71b12a08e5be55b958a737decde889c189f7ca00ceaddccd7b587f9c8b2a4b64",
        "f7df311558fb327cd21d8900ad1a9dc6d5a8145773a693fc3afd43a93a128c51",
    ),
    _exact_bootstrap_requirement_transition(
        "pdd/prompts/fix_main_python.prompt",
        "python",
        "f4b5f47aaeda04805ddf44d2ea465dace78206ef18bca05141156ff15de3d3ac",
        "c238141a397d86e9053d30413e6063d32f26194ad53148109c39ab5648998ecc",
        "71b12a08e5be55b958a737decde889c189f7ca00ceaddccd7b587f9c8b2a4b64",
        "f7df311558fb327cd21d8900ad1a9dc6d5a8145773a693fc3afd43a93a128c51",
    ),
    _exact_bootstrap_requirement_transition(
        "pdd/prompts/metadata_sync_python.prompt",
        "python",
        "c9dee496de479efe665cc44767871a5530bb09cdbcc797d8603fd6e3191d5561",
        "6ab860b38af47df67f30c5281e89df9a5dad98116fe41a7b21d630a06b028bfc",
        "71b12a08e5be55b958a737decde889c189f7ca00ceaddccd7b587f9c8b2a4b64",
        "f7df311558fb327cd21d8900ad1a9dc6d5a8145773a693fc3afd43a93a128c51",
    ),
    _exact_bootstrap_requirement_transition(
        "pdd/prompts/one_session_sync_python.prompt",
        "python",
        "907be3fbc932baf1b2373e831e9784a69fc91fd98bde925139bd89487a5ec419",
        "90edaa24ea338961a00053bc11e5254e4887af38d8b7aa304d852f656ee2963e",
        "71b12a08e5be55b958a737decde889c189f7ca00ceaddccd7b587f9c8b2a4b64",
        "f7df311558fb327cd21d8900ad1a9dc6d5a8145773a693fc3afd43a93a128c51",
    ),
    _exact_bootstrap_requirement_transition(
        "pdd/prompts/sync_determine_operation_python.prompt",
        "python",
        "1dcdbb492c9bdd543fd6d07fcd712b4d9b939a26caf60c53e447514472c5c956",
        "29779356fc293e48045a18ce068610df5869c26c9ff99b514b21f6a36c381a04",
        "71b12a08e5be55b958a737decde889c189f7ca00ceaddccd7b587f9c8b2a4b64",
        "f7df311558fb327cd21d8900ad1a9dc6d5a8145773a693fc3afd43a93a128c51",
    ),
    _exact_bootstrap_requirement_transition(
        "pdd/prompts/sync_main_python.prompt",
        "python",
        "f112de7cfda339c31245f82a1670cf75ff1a1afddac0d8bbcd176f1929bfa7ba",
        "5dd863bff75ca15b61764b524b6177d6fff78ba9860bb0beebc13caec6af4133",
        "71b12a08e5be55b958a737decde889c189f7ca00ceaddccd7b587f9c8b2a4b64",
        "f7df311558fb327cd21d8900ad1a9dc6d5a8145773a693fc3afd43a93a128c51",
    ),
    _exact_bootstrap_requirement_transition(
        "pdd/prompts/sync_orchestration_python.prompt",
        "python",
        "ca4ad5eff6774715d7a65c73e17a12f79da66cb409c69fe90bf41ae097181266",
        "efb635d393704cd2b4b1bbcc680400c9182469e60098c0df4da5a7892f2f60cc",
        "71b12a08e5be55b958a737decde889c189f7ca00ceaddccd7b587f9c8b2a4b64",
        "f7df311558fb327cd21d8900ad1a9dc6d5a8145773a693fc3afd43a93a128c51",
    ),
    _exact_bootstrap_requirement_transition(
        "pdd/prompts/sync_tui_python.prompt",
        "python",
        "a610a1cc0c82bde12f6e133b7e505c343ded9e8eb6fcd39a657263257d254515",
        "e13629d81b22d27148983600507273e1492101f3ccbd8e8203c39f7f799045ee",
        "71b12a08e5be55b958a737decde889c189f7ca00ceaddccd7b587f9c8b2a4b64",
        "f7df311558fb327cd21d8900ad1a9dc6d5a8145773a693fc3afd43a93a128c51",
    ),
)
_BOOTSTRAP_REQUIREMENT_TRANSITIONS += _REPLAY_PROMPT_REQUIREMENT_TRANSITIONS


# One long-lived pre-schema-2 unit first becomes managed in pdd#1790. Bind its
# initial profile to the exact candidate policy and prompt bytes so the merged
# protected checker can authorize that addition without granting a general
# candidate-only profile escape hatch.
_BOOTSTRAP_PROFILE_ADDITIONS = (
    (
        PurePosixPath("pdd/prompts/checkup_agentic_artifact_python.prompt"),
        "python",
        "CONTRACT-SHA256:dc4db042ae408dcd90c0dcfe4fb9607421e331f024f56de8e22ca1272d0df1f7",
        "8e3ba247e42d1a4e1df3e1ba968b390595aa1173184f93419eea16af32fa89fc",
        "dc4db042ae408dcd90c0dcfe4fb9607421e331f024f56de8e22ca1272d0df1f7",
    ),
    (
        PurePosixPath("pdd/prompts/story_detection_result_python.prompt"),
        "python",
        "CONTRACT-SHA256:dd66389e2ec13002ff56ae34625443f463164a4fcadf51af6a98982c49ae01c3",
        "f0f1d36e337541ba4425f081e236c42847f8132cb61f9f8fe06334a805fc5c7b",
        "dd66389e2ec13002ff56ae34625443f463164a4fcadf51af6a98982c49ae01c3",
    ),
    (
        PurePosixPath("pdd/prompts/mock_contract_validation_python.prompt"),
        "python",
        "CONTRACT-SHA256:3b37fbfbf9545fd0ddd57fa5238ab89be9d4444541efeb8cf1b30578f0f4bf8d",
        "f7df311558fb327cd21d8900ad1a9dc6d5a8145773a693fc3afd43a93a128c51",
        "3b37fbfbf9545fd0ddd57fa5238ab89be9d4444541efeb8cf1b30578f0f4bf8d",
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
    if any(
        obligation.requirement_ids != (authorization.from_requirement_id,)
        for obligation in obligations.values()
    ):
        return None, "requirement transition is partial or mismatched"
    obligations = {
        obligation_id: replace(
            obligation, requirement_ids=(authorization.to_requirement_id,)
        )
        for obligation_id, obligation in obligations.items()
    }
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
