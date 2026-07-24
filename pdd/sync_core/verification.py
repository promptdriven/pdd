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
# #1989 predates schema-2 representation locking. Keep this one reviewed
# historical transition readable by its complete protected policy identities;
# all later schema-2 candidates remain token-for-token append-only.
_LEGACY_PDD_1989_SCHEMA_2_HISTORY = (
    "af385bc3cb0cca5692fa46b315db1c69f9caaf688eea0a69dabe29e088878b36",
    "09bc30376c6ee5a836bef24f9123759e039dbe4a5b18d1f46b5cae513972edad",
)
_LEGACY_PDD_1989_PROFILE_BYTES = (
    "f0f1d36e337541ba4425f081e236c42847f8132cb61f9f8fe06334a805fc5c7b",
    "71b12a08e5be55b958a737decde889c189f7ca00ceaddccd7b587f9c8b2a4b64",
)
# PR #1971 consumed six prompt/profile transitions in one reviewed candidate.
# Retain its exact historical byte binding; it is not replay authority.
_PR1971_COMBINED_SCHEMA_2_HISTORY = (
    "8f423a11f5c25c3042073e733085ad08c5d03a999087cf04d2f6bc7f24fb0d72",
    "2b96e538280ebb79db86d0dece4791d80f46dadcc93ba6ab4ad81182b9491d5f",
)
_PR1971_COMBINED_PROFILE_BYTES = (
    "85fbc4f5957e9872b7d368a1b6f9e8c3bad852142ed4c0ec49589eaf63bd8fb3",
    "c566e1b87015632ca317e799f2756af9a25281c6e842c03ccad763b20d539bf1",
)
# #2168 advances the final-gate prompts after the #1998 replay campaign. Bind
# its two reviewed transitions to the complete policy/profile byte identities.
_LEGACY_PDD_2168_SCHEMA_2_HISTORY = (
    "85fd63ba8a0b8e5e4d514d4bd96c5f7ac423c8fea3c413a074ef7bdf3acec880",
    "5645cd84471c507c33a1ebbb2609ae1e2a5e908ac91995eaf2eeeb0c20ba87d0",
)
_LEGACY_PDD_2168_PROFILE_BYTES = (
    "fe80e8278f3f262f9902e8af6e88f79476f55fcb830929d5c3bea5a87e6e72c3",
    "e4c478dd7d01b17e2c56710fa7ecd19ce9e4560a86026233f526c0e062fd0786",
)
# #2168 was subsequently merged onto the #1998-composed current main.  Keep
# that rebased pair distinct from the original reviewed candidate so both byte
# histories remain explicit rather than rewriting either one.
_PDD_2168_REBASED_SCHEMA_2_HISTORY = (
    "0b00131438c93244513b77346ae2649d1073414621f30f536e2f6ae55ee7d9ee",
    "474fa05c3a0844b37fe9767a7db64e159781edb92db7b784e7f45d1592380823",
)
_PDD_2168_REBASED_PROFILE_BYTES = (
    "79ac687426546e1c81bbf50f60d7f1067016ec2a9f34d3278bb514a6b1a72836",
    "b4832ab48a0d0cf4570dc2de40ae3fe93dc406c03b3fd7807523f95cb8c62a7f",
)
# The replay campaign first composed the protected #1875 base.  It remains a
# separate exact history: later #1875 transition authorizations may not erase
# the protected-base evidence.
_PDD_1875_COMPOSED_BASE_SCHEMA_2_HISTORY = (
    "2b96e538280ebb79db86d0dece4791d80f46dadcc93ba6ab4ad81182b9491d5f",
    "85fd63ba8a0b8e5e4d514d4bd96c5f7ac423c8fea3c413a074ef7bdf3acec880",
)
_PDD_1875_COMPOSED_BASE_PROFILE_BYTES = (
    "c566e1b87015632ca317e799f2756af9a25281c6e842c03ccad763b20d539bf1",
    "fe80e8278f3f262f9902e8af6e88f79476f55fcb830929d5c3bea5a87e6e72c3",
)

# PR #1875 then consumed its four composed prompt transitions on the protected
# 85fd/fe80 base and produced the 0b00/79ac candidate.  These bytes are also
# the policy/profile boundary that #2168 was later rebased onto, but the
# transition authorizations below remain the immutable #1875 evidence.
_PDD_1875_COMPOSED_SCHEMA_2_HISTORY = (
    "85fd63ba8a0b8e5e4d514d4bd96c5f7ac423c8fea3c413a074ef7bdf3acec880",
    "0b00131438c93244513b77346ae2649d1073414621f30f536e2f6ae55ee7d9ee",
)
_PDD_1875_COMPOSED_PROFILE_BYTES = (
    "fe80e8278f3f262f9902e8af6e88f79476f55fcb830929d5c3bea5a87e6e72c3",
    "79ac687426546e1c81bbf50f60d7f1067016ec2a9f34d3278bb514a6b1a72836",
)

# PR #2171 updates the Terra/Sol bounded-review workflow and its generated
# command-completion prompts together.  These eight requirement transitions
# were composed against main before their profile rows could be installed as
# dormant authority.  Keep the one reviewed candidate bound to its complete
# policy/profile and prompt bytes; it grants no reusable transition authority.
_TERRA_SOL_COMPOSED_SCHEMA_2_HISTORY = (
    "0b00131438c93244513b77346ae2649d1073414621f30f536e2f6ae55ee7d9ee",
    "0b00131438c93244513b77346ae2649d1073414621f30f536e2f6ae55ee7d9ee",
)
_TERRA_SOL_COMPOSED_PROFILE_BYTES = (
    "79ac687426546e1c81bbf50f60d7f1067016ec2a9f34d3278bb514a6b1a72836",
    "033591bdbf15b8833802a91b20eb6d5e86dd870f200a49598a9bb5a145eb6f16",
)
# #2168 was then merged onto the reviewed Terra/Sol state. The raw rotation
# policy is unchanged; this exact pair permits only the three combined prompt
# transitions and their resulting profile bytes.
_PDD_2168_TERRA_CONTINUATION_SCHEMA_2_HISTORY = (
    "0b00131438c93244513b77346ae2649d1073414621f30f536e2f6ae55ee7d9ee",
    "0b00131438c93244513b77346ae2649d1073414621f30f536e2f6ae55ee7d9ee",
)
_PDD_2168_TERRA_CONTINUATION_PROFILE_BYTES = (
    "033591bdbf15b8833802a91b20eb6d5e86dd870f200a49598a9bb5a145eb6f16",
    "ea8502f8765d229587323bd5d5763866acd2b8e390bb5c8c58ceb035f99daf43",
)

# Gemini 3.6 installs two future prompt transitions after the Terra/Sol
# reconciliation was consumed. Bind that policy evolution and the only
# permitted current/future profile bytes exactly so the historical Terra/Sol
# overlay cannot become generic replay authority.
_GEMINI_36_PHASE_A_SCHEMA_2_HISTORY = (
    "0b00131438c93244513b77346ae2649d1073414621f30f536e2f6ae55ee7d9ee",
    "e53927642e3ffbe1655bb7e10f9d298fb33833b3598b47d3019be2fcf922da36",
)
_GEMINI_36_PROFILE_BYTES = (
    "033591bdbf15b8833802a91b20eb6d5e86dd870f200a49598a9bb5a145eb6f16",
    "c3f9d1344b067ba8640db6da706a8c17f13fcd47b09805b786e58a65fca6169e",
)
# PR #2168 can be consumed after Gemini 3.6 Phase A installs its dormant
# rotation rows.  Gemini changes only the rotation-policy bytes at this stage;
# #2168 changes the profile bytes.  Bind that cross-branch composition exactly
# so neither transition becomes generic replay authority.
_PDD_2168_GEMINI_36_SCHEMA_2_STATE = (
    _GEMINI_36_PHASE_A_SCHEMA_2_HISTORY[1],
    _GEMINI_36_PHASE_A_SCHEMA_2_HISTORY[1],
)
_PDD_2168_GEMINI_36_PROFILE_STATES = (
    _PDD_2168_TERRA_CONTINUATION_PROFILE_BYTES,
    (
        _PDD_2168_TERRA_CONTINUATION_PROFILE_BYTES[1],
        _PDD_2168_TERRA_CONTINUATION_PROFILE_BYTES[1],
    ),
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
class _RequirementTransitionRetirement:
    """One append-only replacement of an unreachable dormant transition."""

    obsolete: _RequirementTransitionAuthorization
    replacement: _RequirementTransitionAuthorization


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
    prompts: Mapping[
        PurePosixPath,
        tuple[bytes | None, bytes | None],
    ]


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
        "379831026c7d037c2b7b529d48fcff8f33bfeb909b3608cc56aa35abdffa4134",
        "71b12a08e5be55b958a737decde889c189f7ca00ceaddccd7b587f9c8b2a4b64",
        "fb1910fc60fd925043007b41631f1e8557159b3e789f22fcdf33ca080a84e34c",
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
        "fb1910fc60fd925043007b41631f1e8557159b3e789f22fcdf33ca080a84e34c",
    ),
    _exact_bootstrap_requirement_transition(
        "pdd/prompts/ci_drift_heal_python.prompt",
        "python",
        "fc595464ceb1bac758864cd66a87fd1ba4f72bae79660a1dd334e060cbb861f7",
        "54f1c25a8cdbf5d1a724981f6fe9f9b6fbe5b20988f30fd2183c24b60d932d88",
        "71b12a08e5be55b958a737decde889c189f7ca00ceaddccd7b587f9c8b2a4b64",
        "fb1910fc60fd925043007b41631f1e8557159b3e789f22fcdf33ca080a84e34c",
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
        "fb1910fc60fd925043007b41631f1e8557159b3e789f22fcdf33ca080a84e34c",
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
        "fb1910fc60fd925043007b41631f1e8557159b3e789f22fcdf33ca080a84e34c",
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


# #2077 pre-authorized two dormant estimate transitions. Bind those exact
# prompt changes to the final #1989 + #2052 profile composition.
_PDD_1989_COMPOSED_ESTIMATE_REQUIREMENT_TRANSITIONS = (
    _exact_bootstrap_requirement_transition(
        "pdd/prompts/commands/generate_python.prompt",
        "python",
        "83b45ad928a9bac3567dea786c4b48819400247e63c7210d8cb5d26e4750a52f",
        "503f997914734dbef8e0542efd1f3c495fa15a652782e15bf63638e35c841403",
        "71b12a08e5be55b958a737decde889c189f7ca00ceaddccd7b587f9c8b2a4b64",
        "1b4641d57921012a4aa7c507bb38b31c29dcc8ad23b370f0c4b979d8ff0a5d18",
    ),
    _exact_bootstrap_requirement_transition(
        "pdd/prompts/core/cli_python.prompt",
        "python",
        "f1d49d5906b0a00226a0b33cf74be34ca4970efccc9531dbcd1b96c4b57e3724",
        "779a19a53bdbb3c7ad5dbf4afb9fb29cf3f04b56e9bfc488552ed0eff823f46e",
        "71b12a08e5be55b958a737decde889c189f7ca00ceaddccd7b587f9c8b2a4b64",
        "fb1910fc60fd925043007b41631f1e8557159b3e789f22fcdf33ca080a84e34c",
    ),
    _exact_bootstrap_requirement_transition(
        "pdd/prompts/get_test_command_python.prompt",
        "python",
        "ef559f5558fb627aa53f078cba0eaae221a7af9a2c6bdadf580a4cb12bf217b7",
        "023045865bfe0d5920b5008986106a16e7014b35f09fc80faa43b1f0d42bcd44",
        "56ea5d189034c9d85e91c86348689eb18c4c34fa67406258f78f0ae3330eaeb6",
        "85fbc4f5957e9872b7d368a1b6f9e8c3bad852142ed4c0ec49589eaf63bd8fb3",
    ),
    _exact_bootstrap_requirement_transition(
        "pdd/prompts/fix_error_loop_python.prompt",
        "python",
        "afffd825b4495819b853fec9a86b0be7644f6fe0468d40548d8b9b2803d183ce",
        "8f4ef46cf85f9ed8e4ff28732dba2614005a1d50d6793ceb25e15608d5ffb751",
        "56ea5d189034c9d85e91c86348689eb18c4c34fa67406258f78f0ae3330eaeb6",
        "85fbc4f5957e9872b7d368a1b6f9e8c3bad852142ed4c0ec49589eaf63bd8fb3",
    ),
)
_BOOTSTRAP_REQUIREMENT_TRANSITIONS += (
    _PDD_1989_COMPOSED_ESTIMATE_REQUIREMENT_TRANSITIONS
)


_PDD_2168_FINAL_GATE_REQUIREMENT_TRANSITIONS = (
    _exact_bootstrap_requirement_transition(
        "pdd/prompts/agentic_checkup_orchestrator_python.prompt",
        "python",
        "379831026c7d037c2b7b529d48fcff8f33bfeb909b3608cc56aa35abdffa4134",
        "fce5b7e4354b4953ca629016cdc048c5b7d593cea1179b2ef497094934bc85c3",
        "c566e1b87015632ca317e799f2756af9a25281c6e842c03ccad763b20d539bf1",
        "b4832ab48a0d0cf4570dc2de40ae3fe93dc406c03b3fd7807523f95cb8c62a7f",
    ),
    _exact_bootstrap_requirement_transition(
        "pdd/prompts/agentic_common_python.prompt",
        "python",
        "c00fe698b5d829e1f2801c290f1bf425d2e7b392b733b7916519c6c39528b900",
        "3d5cd383fe74fe03e16653b942d775f04332680b7541c10fa529eebbd8e26851",
        "c566e1b87015632ca317e799f2756af9a25281c6e842c03ccad763b20d539bf1",
        "b4832ab48a0d0cf4570dc2de40ae3fe93dc406c03b3fd7807523f95cb8c62a7f",
    ),
)

# PR #1875 consumed the earlier checkup-orchestrator transition while its
# profile bytes were composed by the replay campaign. It remains a distinct,
# immutable historical pair from #2168's later final-gate transition.
_PDD_1875_CHECKUP_REQUIREMENT_TRANSITIONS = (
    _exact_bootstrap_requirement_transition(
        "pdd/prompts/agentic_checkup_orchestrator_python.prompt",
        "python",
        "379831026c7d037c2b7b529d48fcff8f33bfeb909b3608cc56aa35abdffa4134",
        "08e0c842d842974340b7ed3424f71fa20379c6922aaa6cfbca232d7d83a9a255",
        "c566e1b87015632ca317e799f2756af9a25281c6e842c03ccad763b20d539bf1",
        "fe80e8278f3f262f9902e8af6e88f79476f55fcb830929d5c3bea5a87e6e72c3",
    ),
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
        "fb1910fc60fd925043007b41631f1e8557159b3e789f22fcdf33ca080a84e34c",
    ),
    _exact_bootstrap_requirement_transition(
        "pdd/prompts/agentic_bug_orchestrator_python.prompt",
        "python",
        "80577f381e7185bd9a77f32b8be81079166b5881e5ca148cdab020dcb7069e11",
        "dfbaabe591842937fd2141208b1b3c4104b7b89bf32d261d96a61830cc7fc872",
        "71b12a08e5be55b958a737decde889c189f7ca00ceaddccd7b587f9c8b2a4b64",
        "fb1910fc60fd925043007b41631f1e8557159b3e789f22fcdf33ca080a84e34c",
    ),
    _exact_bootstrap_requirement_transition(
        "pdd/prompts/agentic_change_orchestrator_python.prompt",
        "python",
        "868b316bb60d886ebf0be7f52fb940296abd11804606bde83b841f812bf660d8",
        "a5f609c2aa21b86d5b1bdb1ef7b36207c40326fc85b617c8b7d7b99dc5b23b9c",
        "71b12a08e5be55b958a737decde889c189f7ca00ceaddccd7b587f9c8b2a4b64",
        "fb1910fc60fd925043007b41631f1e8557159b3e789f22fcdf33ca080a84e34c",
    ),
    _exact_bootstrap_requirement_transition(
        "pdd/prompts/agentic_e2e_fix_orchestrator_python.prompt",
        "python",
        "179b3c8cba5ce703f943a0ebcf6f7c540d34d23e50506e7456d0aebec640726c",
        "91bc4b2ab37fca4aeb1c8ed135f694fd9b75273e50a482563ae674bc4124619f",
        "71b12a08e5be55b958a737decde889c189f7ca00ceaddccd7b587f9c8b2a4b64",
        "fb1910fc60fd925043007b41631f1e8557159b3e789f22fcdf33ca080a84e34c",
    ),
    _exact_bootstrap_requirement_transition(
        "pdd/prompts/agentic_e2e_fix_step9_verify_all_LLM.prompt",
        "llm",
        "228b06c686e6e8c416e2ab753791b4d4d63ae23fb14c810e9433870e34d0ed0e",
        "ec4e7456f445fa227a7bfeb58e55d2ef1fbec9cd3bd7cc51222a5d5474bdf27d",
        "71b12a08e5be55b958a737decde889c189f7ca00ceaddccd7b587f9c8b2a4b64",
        "fb1910fc60fd925043007b41631f1e8557159b3e789f22fcdf33ca080a84e34c",
    ),
    _exact_bootstrap_requirement_transition(
        "pdd/prompts/agentic_split_orchestrator_python.prompt",
        "python",
        "9c24971f6866c8432a6ae7102eb5777e1c7a36952c3321c577c520f7c8088d39",
        "0436452e88c77dd034d4aa00c20f8d8361830ca8196a5e8ec9c8f69666fc38a6",
        "71b12a08e5be55b958a737decde889c189f7ca00ceaddccd7b587f9c8b2a4b64",
        "fb1910fc60fd925043007b41631f1e8557159b3e789f22fcdf33ca080a84e34c",
    ),
    _exact_bootstrap_requirement_transition(
        "pdd/prompts/agentic_sync_python.prompt",
        "python",
        "aa67cf6c09fdd10aa2670a0c8c2dba3b01630b8c18c86c34d3f1ec213b45aad8",
        "5d9f8b0462c925413c1941286ae28c952ba8e5355f01cab3131d9a6e3c0a1659",
        "71b12a08e5be55b958a737decde889c189f7ca00ceaddccd7b587f9c8b2a4b64",
        "fb1910fc60fd925043007b41631f1e8557159b3e789f22fcdf33ca080a84e34c",
    ),
    _exact_bootstrap_requirement_transition(
        "pdd/prompts/agentic_sync_runner_python.prompt",
        "python",
        "99010afb8c3a52d2f1a1af15b8fa2c786d5fdcaaddb04b61e8c0ae719f7f23a1",
        "66b8a98d7f8a7d5b82093178be8196f6287125072e888356341f7691f6b66d57",
        "71b12a08e5be55b958a737decde889c189f7ca00ceaddccd7b587f9c8b2a4b64",
        "fb1910fc60fd925043007b41631f1e8557159b3e789f22fcdf33ca080a84e34c",
    ),
    _exact_bootstrap_requirement_transition(
        "pdd/prompts/agentic_test_orchestrator_python.prompt",
        "python",
        "068328249e60cfca625096866a6886de55c344e68539b5489e0b57ffdddb9593",
        "9f8e9ba75d0324d83aae431254ed78c8bfb9e73e800cbf06712de780a1c3fe25",
        "71b12a08e5be55b958a737decde889c189f7ca00ceaddccd7b587f9c8b2a4b64",
        "fb1910fc60fd925043007b41631f1e8557159b3e789f22fcdf33ca080a84e34c",
    ),
    _exact_bootstrap_requirement_transition(
        "pdd/prompts/ci_validation_python.prompt",
        "python",
        "9e2e7d49234d6edebc86bc0701de53df732c7c5b52621a4be0d25d69e6f9635f",
        "fe775e3133d44e7903ff4b19a18bda48de29d3cd82a9a1526536241e4495d885",
        "71b12a08e5be55b958a737decde889c189f7ca00ceaddccd7b587f9c8b2a4b64",
        "fb1910fc60fd925043007b41631f1e8557159b3e789f22fcdf33ca080a84e34c",
    ),
    _exact_bootstrap_requirement_transition(
        "pdd/prompts/cmd_test_main_python.prompt",
        "python",
        "9a96654683807432182c978b529ad6804db23591a602cab866fe592364e012e4",
        "1bc51147fc08fe0f79a6b361ba91378a81b51e6f7262d50c7534f8fa62240063",
        "71b12a08e5be55b958a737decde889c189f7ca00ceaddccd7b587f9c8b2a4b64",
        "fb1910fc60fd925043007b41631f1e8557159b3e789f22fcdf33ca080a84e34c",
    ),
    _exact_bootstrap_requirement_transition(
        "pdd/prompts/code_generator_main_python.prompt",
        "python",
        "8d0a51822aaa2c64e1b71579d0cb6e41460b90734441e0b6ec3ec146402495fe",
        "51ec006a5b7faeb397be9c1b8e61205e97459fdc08cd9e90e7f0692ccf55a1d5",
        "71b12a08e5be55b958a737decde889c189f7ca00ceaddccd7b587f9c8b2a4b64",
        "fb1910fc60fd925043007b41631f1e8557159b3e789f22fcdf33ca080a84e34c",
    ),
    _exact_bootstrap_requirement_transition(
        "pdd/prompts/commands/fix_python.prompt",
        "python",
        "3e180110a579e905ed0e7eeead2f5b8145a5cbbeed781942b6aaad1e713c3ec6",
        "9665945341cf2ac1860c535d6867cd0082f0184d462765ec277d3887cfaae583",
        "71b12a08e5be55b958a737decde889c189f7ca00ceaddccd7b587f9c8b2a4b64",
        "fb1910fc60fd925043007b41631f1e8557159b3e789f22fcdf33ca080a84e34c",
    ),
    _exact_bootstrap_requirement_transition(
        "pdd/prompts/commands/maintenance_python.prompt",
        "python",
        "5f50939cf7cd9dd3cf1269d20cef4ba1e3bbe8c242bd33ccfc4fdeef51d0cda6",
        "d745f41791cabdae9e76dbf21896f3a1dcba3435b6f599ffb9c67c0a8789c9b3",
        "71b12a08e5be55b958a737decde889c189f7ca00ceaddccd7b587f9c8b2a4b64",
        "fb1910fc60fd925043007b41631f1e8557159b3e789f22fcdf33ca080a84e34c",
    ),
    _exact_bootstrap_requirement_transition(
        "pdd/prompts/commands/modify_python.prompt",
        "python",
        "8d103ee748926ef9683ba4e0ab70ecfd32b91e9437eaf435767bb42d0beda647",
        "34ec165260531e0fd13b721a7fb9bb2ae5fe70275166044ddd204166adf660be",
        "71b12a08e5be55b958a737decde889c189f7ca00ceaddccd7b587f9c8b2a4b64",
        "fb1910fc60fd925043007b41631f1e8557159b3e789f22fcdf33ca080a84e34c",
    ),
    _exact_bootstrap_requirement_transition(
        "pdd/prompts/content_selector_python.prompt",
        "python",
        "df9a157338364189552d43732ed4a565eb5368d4a460a7b249962ff2a2b3a8ad",
        "b2f4bcb592f87c6bb782329df151acbd7045d0562bcf0805b00246d4f1ba0096",
        "71b12a08e5be55b958a737decde889c189f7ca00ceaddccd7b587f9c8b2a4b64",
        "fb1910fc60fd925043007b41631f1e8557159b3e789f22fcdf33ca080a84e34c",
    ),
    _exact_bootstrap_requirement_transition(
        "pdd/prompts/durable_sync_runner_python.prompt",
        "python",
        "fb45ad84ba8adb320baadeb47cac7917626dfd0e44916e8ffd6709cd13ccb72e",
        "5bfd76d356efbb0848b013c208909d1d6fc16b1dd7d7ef215457fd14debcf259",
        "71b12a08e5be55b958a737decde889c189f7ca00ceaddccd7b587f9c8b2a4b64",
        "fb1910fc60fd925043007b41631f1e8557159b3e789f22fcdf33ca080a84e34c",
    ),
    _exact_bootstrap_requirement_transition(
        "pdd/prompts/fix_main_python.prompt",
        "python",
        "f4b5f47aaeda04805ddf44d2ea465dace78206ef18bca05141156ff15de3d3ac",
        "c238141a397d86e9053d30413e6063d32f26194ad53148109c39ab5648998ecc",
        "71b12a08e5be55b958a737decde889c189f7ca00ceaddccd7b587f9c8b2a4b64",
        "fb1910fc60fd925043007b41631f1e8557159b3e789f22fcdf33ca080a84e34c",
    ),
    _exact_bootstrap_requirement_transition(
        "pdd/prompts/metadata_sync_python.prompt",
        "python",
        "c9dee496de479efe665cc44767871a5530bb09cdbcc797d8603fd6e3191d5561",
        "6ab860b38af47df67f30c5281e89df9a5dad98116fe41a7b21d630a06b028bfc",
        "71b12a08e5be55b958a737decde889c189f7ca00ceaddccd7b587f9c8b2a4b64",
        "fb1910fc60fd925043007b41631f1e8557159b3e789f22fcdf33ca080a84e34c",
    ),
    _exact_bootstrap_requirement_transition(
        "pdd/prompts/one_session_sync_python.prompt",
        "python",
        "907be3fbc932baf1b2373e831e9784a69fc91fd98bde925139bd89487a5ec419",
        "90edaa24ea338961a00053bc11e5254e4887af38d8b7aa304d852f656ee2963e",
        "71b12a08e5be55b958a737decde889c189f7ca00ceaddccd7b587f9c8b2a4b64",
        "fb1910fc60fd925043007b41631f1e8557159b3e789f22fcdf33ca080a84e34c",
    ),
    _exact_bootstrap_requirement_transition(
        "pdd/prompts/sync_determine_operation_python.prompt",
        "python",
        "fd24cdd0df308353e33bfe6d7e004cd3064303c3d1eef536b1adbfc3a67bd1d8",
        "c84ef0e33d0759ffcf6920e5cd14951045b43d2e6d4d93e8b5b9fb31f8215ed7",
        "c566e1b87015632ca317e799f2756af9a25281c6e842c03ccad763b20d539bf1",
        "9caf55f5a1366c9e439b5ac4394f8192b3131102be4c648ab4bc3e89c42c5550",
    ),
    _exact_bootstrap_requirement_transition(
        "pdd/prompts/sync_main_python.prompt",
        "python",
        "f112de7cfda339c31245f82a1670cf75ff1a1afddac0d8bbcd176f1929bfa7ba",
        "fd8ff15f34913e59c0e9a167739916021bf6b0406b651a8603614139f0bf282f",
        "71b12a08e5be55b958a737decde889c189f7ca00ceaddccd7b587f9c8b2a4b64",
        "fb1910fc60fd925043007b41631f1e8557159b3e789f22fcdf33ca080a84e34c",
    ),
    _exact_bootstrap_requirement_transition(
        "pdd/prompts/sync_orchestration_python.prompt",
        "python",
        "5420f3f617586ceb3149a9efb557968b25115855ae65275be2d11d55c91f227e",
        "7cfd6ea5b6a182e1de3ac97ac8554ade69c7c486a2127faafec644438762b78a",
        "c566e1b87015632ca317e799f2756af9a25281c6e842c03ccad763b20d539bf1",
        "fe80e8278f3f262f9902e8af6e88f79476f55fcb830929d5c3bea5a87e6e72c3",
    ),
    _exact_bootstrap_requirement_transition(
        "pdd/prompts/sync_tui_python.prompt",
        "python",
        "a610a1cc0c82bde12f6e133b7e505c343ded9e8eb6fcd39a657263257d254515",
        "e13629d81b22d27148983600507273e1492101f3ccbd8e8203c39f7f799045ee",
        "71b12a08e5be55b958a737decde889c189f7ca00ceaddccd7b587f9c8b2a4b64",
        "fb1910fc60fd925043007b41631f1e8557159b3e789f22fcdf33ca080a84e34c",
    ),
    _exact_bootstrap_requirement_transition(
        "pdd/prompts/architecture_sync_python.prompt",
        "python",
        "754f44ef1cab69a0a1fc70b321333ec68476e2b5432e5b5e6be3a3e382c32e29",
        "a5fd7095f26859503d4f2a2c30b49b1a0fe834b78d55536f69eae26006fb9fb7",
        "71b12a08e5be55b958a737decde889c189f7ca00ceaddccd7b587f9c8b2a4b64",
        "fb1910fc60fd925043007b41631f1e8557159b3e789f22fcdf33ca080a84e34c",
    ),
)
_BOOTSTRAP_REQUIREMENT_TRANSITIONS += _REPLAY_PROMPT_REQUIREMENT_TRANSITIONS

_PDD_1875_COMPOSED_REQUIREMENT_TRANSITIONS = (
    _exact_bootstrap_requirement_transition(
        "pdd/prompts/commands/analysis_python.prompt",
        "python",
        "5aff15e367047ac59ad70b842c7a0a59cdf266526e09df274f56f7928413aafd",
        "89c8005f5fe933af745285a6a2f28f73b79112e1b96e7af4d7b0e47cde136a16",
        _PDD_1875_COMPOSED_PROFILE_BYTES[0],
        _PDD_1875_COMPOSED_PROFILE_BYTES[1],
    ),
    _exact_bootstrap_requirement_transition(
        "pdd/prompts/user_story_tests_python.prompt",
        "python",
        "c63d875cc5d488b8fd9bfdd72ea015f33962d22b5cde90b9be751de55a209e32",
        "1c467034344d9d87b8225995bc458bc8093e6759dd5c2eed8424b345f69a3ba7",
        _PDD_1875_COMPOSED_PROFILE_BYTES[0],
        _PDD_1875_COMPOSED_PROFILE_BYTES[1],
    ),
    _exact_bootstrap_requirement_transition(
        "pdd/prompts/detect_change_python.prompt",
        "python",
        "2987422f58c48f279289d5b739e46bd1346d596dce1ec14b67a1ac840ee33e60",
        "d5ac2b7fceec8fa95e4711829525faa57bdf5cf01f9d44132a346bb020dcf0a9",
        _PDD_1875_COMPOSED_PROFILE_BYTES[0],
        _PDD_1875_COMPOSED_PROFILE_BYTES[1],
    ),
    _exact_bootstrap_requirement_transition(
        "pdd/prompts/core/cli_python.prompt",
        "python",
        "779a19a53bdbb3c7ad5dbf4afb9fb29cf3f04b56e9bfc488552ed0eff823f46e",
        "e0f5f0173e29379d84dd34934b3221b5ae0f5c9c7b745ea35cb73699cb6162b1",
        _PDD_1875_COMPOSED_PROFILE_BYTES[0],
        _PDD_1875_COMPOSED_PROFILE_BYTES[1],
    ),
)

_TERRA_SOL_COMPOSED_REQUIREMENT_TRANSITIONS = (
    _exact_bootstrap_requirement_transition(
        "pdd/prompts/agentic_checkup_python.prompt",
        "python",
        "1812c6d204e346d0745403c908a47e5d4d42b53612efd61efbe40af04ba4b868",
        "6ffbc126545fc817d69c784521b32ca947fd6b120b891ab8f8a8f3f7ee4885bb",
        _TERRA_SOL_COMPOSED_PROFILE_BYTES[0],
        _TERRA_SOL_COMPOSED_PROFILE_BYTES[1],
    ),
    _exact_bootstrap_requirement_transition(
        "pdd/prompts/agentic_common_python.prompt",
        "python",
        "e6568d79e16a7638ef275c71858d1c2468f593b1369ea602312524a9fef0b37c",
        "11aa8636691deb2c6e1dd1051ba46cb06947bb1a65335914868647e8240cede9",
        _TERRA_SOL_COMPOSED_PROFILE_BYTES[0],
        _TERRA_SOL_COMPOSED_PROFILE_BYTES[1],
    ),
    _exact_bootstrap_requirement_transition(
        "pdd/prompts/checkup_agentic_artifact_python.prompt",
        "python",
        "dc4db042ae408dcd90c0dcfe4fb9607421e331f024f56de8e22ca1272d0df1f7",
        "460c5c8f6ec93da5aa0d3ee30d41d5dfbda05e4631c79354c1a16e6818b45a16",
        _TERRA_SOL_COMPOSED_PROFILE_BYTES[0],
        _TERRA_SOL_COMPOSED_PROFILE_BYTES[1],
    ),
    _exact_bootstrap_requirement_transition(
        "pdd/prompts/checkup_review_loop_python.prompt",
        "python",
        "c5ec02fb049e1359da107067d65e725b3ad0a8cca4da6fd31328821f6b6d1c73",
        "ee5a910b670cba4ad6a7f32617288783cf0fee8e843bc012e70e17a29e2a937b",
        _TERRA_SOL_COMPOSED_PROFILE_BYTES[0],
        _TERRA_SOL_COMPOSED_PROFILE_BYTES[1],
    ),
    _exact_bootstrap_requirement_transition(
        "pdd/prompts/commands/checkup_python.prompt",
        "python",
        "b453bb71475123c5545a37dd23bbff9f057d960b775c0e977151ee98a9b976e0",
        "c91feaa808d1c69a971626bbaedd813ecddae6d39d70711fc4c23a809c88a91a",
        _TERRA_SOL_COMPOSED_PROFILE_BYTES[0],
        _TERRA_SOL_COMPOSED_PROFILE_BYTES[1],
    ),
    _exact_bootstrap_requirement_transition(
        "pdd/prompts/pdd_completion_bash.prompt",
        "bash",
        "8ff68a8b73b323eaa876e51d15411c649ab4bd7aa1d90e23adcdbf4a08b5aa45",
        "e4c8b74fe2b4781e63d8c7d3a4b5f685b14895d68fdf3622f692a2c494bf115f",
        _TERRA_SOL_COMPOSED_PROFILE_BYTES[0],
        _TERRA_SOL_COMPOSED_PROFILE_BYTES[1],
    ),
    _exact_bootstrap_requirement_transition(
        "pdd/prompts/pdd_completion_fish.prompt",
        "fish",
        "ff9102336506e75466d9dc36af6a3afc93b0d07161df4ae76d7aa21267517675",
        "372e2e41f95d2d71e42dbf9a722cd8cf296e69c36c091f8461443b40b66a9504",
        _TERRA_SOL_COMPOSED_PROFILE_BYTES[0],
        _TERRA_SOL_COMPOSED_PROFILE_BYTES[1],
    ),
    _exact_bootstrap_requirement_transition(
        "pdd/prompts/pdd_completion_zsh.prompt",
        "zsh",
        "8a808a26292b9d46d515e8e12de6a8877fb5fdae8e4365c7285067fa216466cf",
        "5d05ee3fcc959bfba1312b3d2ded6c2329ef1f6df0f532e855ac5a345ec6a107",
        _TERRA_SOL_COMPOSED_PROFILE_BYTES[0],
        _TERRA_SOL_COMPOSED_PROFILE_BYTES[1],
    ),
)

_PDD_2168_TERRA_CONTINUATION_REQUIREMENT_TRANSITIONS = (
    _exact_bootstrap_requirement_transition(
        "pdd/prompts/agentic_checkup_python.prompt",
        "python",
        "6ffbc126545fc817d69c784521b32ca947fd6b120b891ab8f8a8f3f7ee4885bb",
        "fcf6ac41bfcf91a1289bb175036df1dd02c2e712c3482e7bc58efa6031f525f3",
        _PDD_2168_TERRA_CONTINUATION_PROFILE_BYTES[0],
        _PDD_2168_TERRA_CONTINUATION_PROFILE_BYTES[1],
    ),
    _exact_bootstrap_requirement_transition(
        "pdd/prompts/agentic_checkup_orchestrator_python.prompt",
        "python",
        "08e0c842d842974340b7ed3424f71fa20379c6922aaa6cfbca232d7d83a9a255",
        "bd868518d46fa67b4fc449f35130553623f9faed8bfb825c5fb88b22ea555fdc",
        _PDD_2168_TERRA_CONTINUATION_PROFILE_BYTES[0],
        _PDD_2168_TERRA_CONTINUATION_PROFILE_BYTES[1],
    ),
    _exact_bootstrap_requirement_transition(
        "pdd/prompts/agentic_common_python.prompt",
        "python",
        "11aa8636691deb2c6e1dd1051ba46cb06947bb1a65335914868647e8240cede9",
        "dd052c431b7ba192fd8527ae7d387effa9d8e8e74cfee023231792fc3fc7d187",
        _PDD_2168_TERRA_CONTINUATION_PROFILE_BYTES[0],
        _PDD_2168_TERRA_CONTINUATION_PROFILE_BYTES[1],
    ),
)

# PR #1971's six historical prompt/profile transitions remain exact protected
# evidence.  They deliberately are not appended to replay bootstrap authority.
_PR1971_COMBINED_REQUIREMENT_TRANSITIONS = (
    _exact_bootstrap_requirement_transition(
        "pdd/prompts/operation_log_python.prompt",
        "python",
        "e9314dff3064004dafe75821e7aec984cbbec76e4745f6c49e73c50105ecb9c8",
        "370d4f511f320b3db71cb74bb17532a6293d1c48def1a0faebfa8fbb7f00eb12",
        "85fbc4f5957e9872b7d368a1b6f9e8c3bad852142ed4c0ec49589eaf63bd8fb3",
        "c566e1b87015632ca317e799f2756af9a25281c6e842c03ccad763b20d539bf1",
    ),
    _exact_bootstrap_requirement_transition(
        "pdd/prompts/pin_example_hack_python.prompt",
        "python",
        "7efec65cda40e8357cd08c974abc4b1aebb450d2fe75401e5cc5629e0696feb9",
        "4b45b2744bb856ba48681d3038ba41512353df5e0ed77c3d698928ca89c6cabb",
        "85fbc4f5957e9872b7d368a1b6f9e8c3bad852142ed4c0ec49589eaf63bd8fb3",
        "c566e1b87015632ca317e799f2756af9a25281c6e842c03ccad763b20d539bf1",
    ),
    _exact_bootstrap_requirement_transition(
        "pdd/prompts/server/routes/prompts_python.prompt",
        "python",
        "8a88807f83d1d4bd5cfa9ccbd465a619a2d00fef9f81c53b84047470c8399293",
        "0cef545efaa9eef5007d338656c0e40e70db314ddbd0e7a00b64f300dba7f342",
        "85fbc4f5957e9872b7d368a1b6f9e8c3bad852142ed4c0ec49589eaf63bd8fb3",
        "c566e1b87015632ca317e799f2756af9a25281c6e842c03ccad763b20d539bf1",
    ),
    _exact_bootstrap_requirement_transition(
        "pdd/prompts/sync_determine_operation_python.prompt",
        "python",
        "1dcdbb492c9bdd543fd6d07fcd712b4d9b939a26caf60c53e447514472c5c956",
        "fd24cdd0df308353e33bfe6d7e004cd3064303c3d1eef536b1adbfc3a67bd1d8",
        "85fbc4f5957e9872b7d368a1b6f9e8c3bad852142ed4c0ec49589eaf63bd8fb3",
        "c566e1b87015632ca317e799f2756af9a25281c6e842c03ccad763b20d539bf1",
    ),
    _exact_bootstrap_requirement_transition(
        "pdd/prompts/sync_orchestration_python.prompt",
        "python",
        "ca4ad5eff6774715d7a65c73e17a12f79da66cb409c69fe90bf41ae097181266",
        "5420f3f617586ceb3149a9efb557968b25115855ae65275be2d11d55c91f227e",
        "85fbc4f5957e9872b7d368a1b6f9e8c3bad852142ed4c0ec49589eaf63bd8fb3",
        "c566e1b87015632ca317e799f2756af9a25281c6e842c03ccad763b20d539bf1",
    ),
    _exact_bootstrap_requirement_transition(
        "pdd/prompts/update_main_python.prompt",
        "python",
        "b1042be0dd594c9bbb197a4afe7e5c5a12aaad1574feadf7cb5b26f9bf85bccd",
        "17fc1c03860bca7d7889ac388e4de26c19b73edb7ead9bea20f6be1016995bb5",
        "85fbc4f5957e9872b7d368a1b6f9e8c3bad852142ed4c0ec49589eaf63bd8fb3",
        "c566e1b87015632ca317e799f2756af9a25281c6e842c03ccad763b20d539bf1",
    ),
)

_PR1971_COMBINED_PYTEST_OBLIGATIONS = {
    (
        PurePosixPath("pdd/prompts/operation_log_python.prompt"),
        "python",
    ): VerificationObligation(
        "pytest-operation-log",
        "test",
        "pytest",
        "7c29aa937a70b7db28c9353bbad309654e12d3fb4d317edf75b475bbc1880963",
        (
            "CONTRACT-SHA256:370d4f511f320b3db71cb74bb17532a6293d1c48def1a0faebfa8fbb7f00eb12",
        ),
        (PurePosixPath("tests/test_operation_log.py"),),
        True,
        (PurePosixPath("pdd/operation_log.py"),),
    ),
    (
        PurePosixPath("pdd/prompts/server/routes/prompts_python.prompt"),
        "python",
    ): VerificationObligation(
        "pytest-server-routes-prompts",
        "test",
        "pytest",
        "7c29aa937a70b7db28c9353bbad309654e12d3fb4d317edf75b475bbc1880963",
        (
            "CONTRACT-SHA256:0cef545efaa9eef5007d338656c0e40e70db314ddbd0e7a00b64f300dba7f342",
        ),
        (PurePosixPath("tests/server/routes/test_prompts.py"),),
        True,
        (PurePosixPath("pdd/server/routes/prompts.py"),),
    ),
    (
        PurePosixPath("pdd/prompts/update_main_python.prompt"),
        "python",
    ): VerificationObligation(
        "pytest-update-main",
        "test",
        "pytest",
        "7c29aa937a70b7db28c9353bbad309654e12d3fb4d317edf75b475bbc1880963",
        (
            "CONTRACT-SHA256:17fc1c03860bca7d7889ac388e4de26c19b73edb7ead9bea20f6be1016995bb5",
        ),
        (PurePosixPath("tests/test_update_main.py"),),
        True,
        (PurePosixPath("pdd/update_main.py"),),
    ),
}

# Eight replay-modified prompts already have protected transition rows: six
# historical bootstrap rows and two rows merged by #1971. Their reviewed
# replacements, together with the 23 otherwise-new replay rows above, are the
# only bootstrap authority allowed to carry a changed profile policy.
_REPLAY_REPLACED_PROMPT_PATHS = frozenset(
    {
        PurePosixPath("pdd/prompts/agentic_checkup_orchestrator_python.prompt"),
        PurePosixPath("pdd/prompts/agentic_common_python.prompt"),
        PurePosixPath("pdd/prompts/checkup_review_loop_python.prompt"),
        PurePosixPath("pdd/prompts/ci_drift_heal_python.prompt"),
        PurePosixPath("pdd/prompts/core/cli_python.prompt"),
        PurePosixPath("pdd/prompts/evidence_manifest_python.prompt"),
    }
)
# The replay now starts after main's story-regression rotation.  Rebind only its
# reviewed candidate transitions to that immutable base; older bootstrap rows
# retain their historical policy pairs and cannot authorize a new candidate.
_REPLAY_BASE_PROFILE_SHA256 = (
    "c566e1b87015632ca317e799f2756af9a25281c6e842c03ccad763b20d539bf1"
)
_REPLAY_HEAD_PROFILE_SHA256 = (
    "fe80e8278f3f262f9902e8af6e88f79476f55fcb830929d5c3bea5a87e6e72c3"
)
_REPLAY_PROFILE_REQUIREMENT_TRANSITIONS = tuple(
    replace(
        item,
        bindings=replace(
            item.bindings,
            base_policy_sha256=_REPLAY_BASE_PROFILE_SHA256,
            head_policy_sha256=_REPLAY_HEAD_PROFILE_SHA256,
        ),
    )
    for item in (
        _REPLAY_PROMPT_REQUIREMENT_TRANSITIONS
        + tuple(
            item
            for item in _BOOTSTRAP_REQUIREMENT_TRANSITIONS
            if item.prompt_path in _REPLAY_REPLACED_PROMPT_PATHS
        )
    )
)
_REPLAY_TRANSITION_BY_IDENTITY = {
    (item.prompt_path, item.language_id): item
    for item in _REPLAY_PROFILE_REQUIREMENT_TRANSITIONS
}
_BOOTSTRAP_REQUIREMENT_TRANSITIONS = tuple(
    _REPLAY_TRANSITION_BY_IDENTITY.get((item.prompt_path, item.language_id), item)
    for item in _BOOTSTRAP_REQUIREMENT_TRANSITIONS
)
_BOOTSTRAP_REQUIREMENT_TRANSITIONS += _PDD_1875_COMPOSED_REQUIREMENT_TRANSITIONS
_REPLAY_REPLACED_PROTECTED_TRANSITIONS = (
    _exact_bootstrap_requirement_transition(
        "pdd/prompts/sync_orchestration_python.prompt",
        "python",
        "ca4ad5eff6774715d7a65c73e17a12f79da66cb409c69fe90bf41ae097181266",
        "5420f3f617586ceb3149a9efb557968b25115855ae65275be2d11d55c91f227e",
        "85fbc4f5957e9872b7d368a1b6f9e8c3bad852142ed4c0ec49589eaf63bd8fb3",
        "c566e1b87015632ca317e799f2756af9a25281c6e842c03ccad763b20d539bf1",
    ),
    _exact_bootstrap_requirement_transition(
        "pdd/prompts/sync_determine_operation_python.prompt",
        "python",
        "1dcdbb492c9bdd543fd6d07fcd712b4d9b939a26caf60c53e447514472c5c956",
        "fd24cdd0df308353e33bfe6d7e004cd3064303c3d1eef536b1adbfc3a67bd1d8",
        "85fbc4f5957e9872b7d368a1b6f9e8c3bad852142ed4c0ec49589eaf63bd8fb3",
        "c566e1b87015632ca317e799f2756af9a25281c6e842c03ccad763b20d539bf1",
    ),
    _exact_bootstrap_requirement_transition(
        "pdd/prompts/agentic_checkup_orchestrator_python.prompt",
        "python",
        "fc372c0369c895e42b4bb8f9277560facf086d999233d88bef8401766bccdf34",
        "379831026c7d037c2b7b529d48fcff8f33bfeb909b3608cc56aa35abdffa4134",
        "7df63fe892ac14382f226ea97dbd2ac186a8cb48213faec958ad32c51d51aeb5",
        "8e3ba247e42d1a4e1df3e1ba968b390595aa1173184f93419eea16af32fa89fc",
    ),
    _exact_bootstrap_requirement_transition(
        "pdd/prompts/checkup_review_loop_python.prompt",
        "python",
        "c44fbaf6b0c1ceb5c52cf514684a72e866bdc08d4bf0b948d978dec65afb0719",
        "a7fd72cadb0644d4d20d09868cc8e908e3122478e6127b3943de32b711d76c02",
        "7df63fe892ac14382f226ea97dbd2ac186a8cb48213faec958ad32c51d51aeb5",
        "8e3ba247e42d1a4e1df3e1ba968b390595aa1173184f93419eea16af32fa89fc",
    ),
    _exact_bootstrap_requirement_transition(
        "pdd/prompts/ci_drift_heal_python.prompt",
        "python",
        "e12dc6b48f34111182afb4a73b9ba66596617b9a6d8e393766d2cd6b847562ec",
        "fc595464ceb1bac758864cd66a87fd1ba4f72bae79660a1dd334e060cbb861f7",
        "7df63fe892ac14382f226ea97dbd2ac186a8cb48213faec958ad32c51d51aeb5",
        "8e3ba247e42d1a4e1df3e1ba968b390595aa1173184f93419eea16af32fa89fc",
    ),
    _exact_bootstrap_requirement_transition(
        "pdd/prompts/agentic_common_python.prompt",
        "python",
        "86e47992102e2344fe59ee9a3ece4c6cf356025edaadf693c12acac63a5c7490",
        "c00fe698b5d829e1f2801c290f1bf425d2e7b392b733b7916519c6c39528b900",
        "f0f1d36e337541ba4425f081e236c42847f8132cb61f9f8fe06334a805fc5c7b",
        "71b12a08e5be55b958a737decde889c189f7ca00ceaddccd7b587f9c8b2a4b64",
    ),
    _exact_bootstrap_requirement_transition(
        "pdd/prompts/evidence_manifest_python.prompt",
        "python",
        "3b50a00e8deca49c70b127540a2e589aa3715a498b775ab4ddb482adb65eac6f",
        "55f2de2533a461b1d26f4c7641edd6c2c7c05858dc98102ed6f9df04d552e24d",
        "8e3ba247e42d1a4e1df3e1ba968b390595aa1173184f93419eea16af32fa89fc",
        "f0f1d36e337541ba4425f081e236c42847f8132cb61f9f8fe06334a805fc5c7b",
    ),
    _exact_bootstrap_requirement_transition(
        "pdd/prompts/core/cli_python.prompt",
        "python",
        "f1d49d5906b0a00226a0b33cf74be34ca4970efccc9531dbcd1b96c4b57e3724",
        "e01fb2968590ca4911044ef59f1091c2ea5de10b6257941078c63282c52e7d37",
        "71b12a08e5be55b958a737decde889c189f7ca00ceaddccd7b587f9c8b2a4b64",
        "1b4641d57921012a4aa7c507bb38b31c29dcc8ad23b370f0c4b979d8ff0a5d18",
    ),
)
_REPLAY_REQUIREMENT_REPLACEMENTS = frozenset(
    (
        protected,
        next(
            candidate
            for candidate in _REPLAY_PROFILE_REQUIREMENT_TRANSITIONS
            if candidate.prompt_path == protected.prompt_path
            and candidate.language_id == protected.language_id
        ),
    )
    for protected in _REPLAY_REPLACED_PROTECTED_TRANSITIONS
)
# The exact historical rows remain authority for the immutable #1989 replay
# pair only; they are absent from the current candidate policy and retain the
# legacy profile-byte guard for every other candidate.
_BOOTSTRAP_REQUIREMENT_TRANSITIONS += _REPLAY_REPLACED_PROTECTED_TRANSITIONS
_BOOTSTRAP_REQUIREMENT_TRANSITIONS += _PDD_2168_FINAL_GATE_REQUIREMENT_TRANSITIONS
_BOOTSTRAP_REQUIREMENT_TRANSITIONS += _PDD_1875_CHECKUP_REQUIREMENT_TRANSITIONS


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
        "CONTRACT-SHA256:34624bde64048913f0c05a3ce2d7faab89997cf46c97f81e4ae27a603e5ed506",
        "fe80e8278f3f262f9902e8af6e88f79476f55fcb830929d5c3bea5a87e6e72c3",
        "34624bde64048913f0c05a3ce2d7faab89997cf46c97f81e4ae27a603e5ed506",
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
        prompt_relpath = _canonical_prompt_path(
            unit_id.prompt_relpath, approved_aliases
        )
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


def _canonical_prompt_path(
    prompt_path: PurePosixPath,
    approved_aliases: Mapping[PurePosixPath, PurePosixPath],
) -> PurePosixPath:
    """Resolve one protected alias exactly as profile-input loading does."""
    for alias, canonical in approved_aliases.items():
        if prompt_path == alias:
            return canonical
        if prompt_path.parts[: len(alias.parts)] == alias.parts:
            return canonical.joinpath(*prompt_path.parts[len(alias.parts) :])
    return prompt_path


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
        payload = _strict_policy_json(raw, "protected")
        rows = payload["rotations"]
        if (
            type(payload.get("schema_version")) is not int
            or payload.get("schema_version") not in {1, 2, 3}
            or not isinstance(rows, list)
        ):
            raise TypeError
    except (json.JSONDecodeError, KeyError, TypeError, UnicodeDecodeError) as exc:
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


class _DuplicateJsonMember(ValueError):
    """Raised when a policy object repeats a member name."""


def _strict_policy_json(raw: bytes, source: str) -> dict[str, Any]:
    """Decode policy JSON while rejecting duplicate object members at every level."""

    def reject_duplicates(pairs: list[tuple[str, Any]]) -> dict[str, Any]:
        payload: dict[str, Any] = {}
        for key, value in pairs:
            if key in payload:
                raise _DuplicateJsonMember(key)
            payload[key] = value
        return payload

    try:
        payload = json.loads(raw, object_pairs_hook=reject_duplicates)
    except _DuplicateJsonMember as exc:
        raise VerificationProfileError(
            f"{source} requirement transition policy contains duplicate JSON members"
        ) from exc
    if not isinstance(payload, dict):
        raise TypeError
    return payload


def _json_skip_whitespace(raw: bytes, index: int) -> int:
    """Return the first non-whitespace byte from one validated JSON value."""
    while index < len(raw) and raw[index] in b" \t\r\n":
        index += 1
    return index


def _json_string_end(raw: bytes, index: int) -> int:
    """Return the byte after one validated JSON string token."""
    if index >= len(raw) or raw[index] != ord('"'):
        raise ValueError("JSON string is absent")
    index += 1
    while index < len(raw):
        if raw[index] == ord("\\"):
            index += 2
        elif raw[index] == ord('"'):
            return index + 1
        else:
            index += 1
    raise ValueError("JSON string is unterminated")


def _json_value_end(raw: bytes, index: int) -> int:
    """Return the byte after one validated JSON value without normalizing it."""
    index = _json_skip_whitespace(raw, index)
    if index >= len(raw):
        raise ValueError("JSON value is absent")
    if raw[index] == ord('"'):
        return _json_string_end(raw, index)
    if raw[index] not in (ord("["), ord("{")):
        while index < len(raw) and raw[index] not in b",]} \t\r\n":
            index += 1
        return index
    stack = [ord("]") if raw[index] == ord("[") else ord("}")]
    index += 1
    while stack:
        if index >= len(raw):
            raise ValueError("JSON container is unterminated")
        token = raw[index]
        if token == ord('"'):
            index = _json_string_end(raw, index)
            continue
        if token == ord("["):
            stack.append(ord("]"))
        elif token == ord("{"):
            stack.append(ord("}"))
        elif token == stack[-1]:
            stack.pop()
        index += 1
    return index


def _raw_json_object_members(raw: bytes) -> dict[str, bytes]:
    """Return exact validated JSON member values from one object token."""
    index = _json_skip_whitespace(raw, 0)
    if index >= len(raw) or raw[index] != ord("{"):
        raise ValueError("JSON object is absent")
    index = _json_skip_whitespace(raw, index + 1)
    members: dict[str, bytes] = {}
    while index < len(raw) and raw[index] != ord("}"):
        key_start = index
        key_end = _json_string_end(raw, key_start)
        key = json.loads(raw[key_start:key_end])
        index = _json_skip_whitespace(raw, key_end)
        if index >= len(raw) or raw[index] != ord(":"):
            raise ValueError("JSON object member lacks a colon")
        value_start = _json_skip_whitespace(raw, index + 1)
        value_end = _json_value_end(raw, value_start)
        members[key] = raw[value_start:value_end]
        index = _json_skip_whitespace(raw, value_end)
        if index < len(raw) and raw[index] == ord(","):
            index = _json_skip_whitespace(raw, index + 1)
        elif index >= len(raw) or raw[index] != ord("}"):
            raise ValueError("JSON object member lacks a delimiter")
    return members


def _raw_json_array_values(raw: bytes) -> tuple[bytes, ...]:
    """Return exact validated JSON value tokens from one array token."""
    index = _json_skip_whitespace(raw, 0)
    if index >= len(raw) or raw[index] != ord("["):
        raise ValueError("JSON array is absent")
    index = _json_skip_whitespace(raw, index + 1)
    values = []
    while index < len(raw) and raw[index] != ord("]"):
        value_start = index
        value_end = _json_value_end(raw, value_start)
        values.append(raw[value_start:value_end])
        index = _json_skip_whitespace(raw, value_end)
        if index < len(raw) and raw[index] == ord(","):
            index = _json_skip_whitespace(raw, index + 1)
        elif index >= len(raw) or raw[index] != ord("]"):
            raise ValueError("JSON array value lacks a delimiter")
    return tuple(values)


def _raw_requirement_transition_history(
    raw: bytes | None, source: str
) -> tuple[tuple[bytes, ...], tuple[bytes, ...]]:
    """Extract exact row/retirement tokens after strict policy JSON validation."""
    if raw is None:
        return (), ()
    try:
        members = _raw_json_object_members(raw)
        rows = _raw_json_array_values(members["requirement_rotations"])
        retirements = _raw_json_array_values(
            members.get("requirement_rotation_retirements", b"[]")
        )
    except (KeyError, ValueError, json.JSONDecodeError, UnicodeDecodeError) as exc:
        raise VerificationProfileError(
            f"{source} requirement transition policy representation is malformed"
        ) from exc
    return rows, retirements


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
        payload = _strict_policy_json(raw, source)
        schema_version = payload.get("schema_version")
        if type(schema_version) is not int:
            raise TypeError
        if schema_version == 1:
            _parse_dormant_policy_envelope(raw, source, allow_legacy_protected=True)
            return ()
        rows = payload["requirement_rotations"]
        if (
            schema_version not in {2, 3}
            or set(payload)
            != (
                {
                    "schema_version",
                    "rotations",
                    "requirement_rotations",
                }
                if schema_version == 2
                else {
                    "schema_version",
                    "rotations",
                    "requirement_rotations",
                    "requirement_rotation_retirements",
                }
            )
            or not isinstance(rows, list)
            or len(rows) > _MAX_REQUIREMENT_TRANSITIONS
            or (
                schema_version == 3
                and not isinstance(payload["requirement_rotation_retirements"], list)
            )
        ):
            raise TypeError
    except (json.JSONDecodeError, KeyError, TypeError, UnicodeDecodeError) as exc:
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
    if len(authorizations) != len(set(authorizations)) or (
        schema_version == 2 and len(identities) != len(set(identities))
    ):
        raise VerificationProfileError(
            f"{source} requirement transition rules are duplicated or ambiguous"
        )
    return tuple(authorizations)


def _parse_requirement_transition_retirements(
    raw: bytes | None, source: str
) -> tuple[_RequirementTransitionRetirement, ...]:
    """Parse exact schema-3 retirement records without granting authority."""
    if raw is None:
        return ()
    try:
        payload = _strict_policy_json(raw, source)
        schema_version = payload.get("schema_version")
        if type(schema_version) is not int:
            raise TypeError
        if schema_version in {1, 2}:
            _parse_dormant_policy_envelope(
                raw, source, allow_legacy_protected=schema_version == 1
            )
            _parse_requirement_transition_authorizations(raw, source)
            return ()
        rows = payload["requirement_rotation_retirements"]
        if schema_version != 3 or not isinstance(rows, list):
            raise TypeError
    except (json.JSONDecodeError, KeyError, TypeError, UnicodeDecodeError) as exc:
        raise VerificationProfileError(
            f"{source} requirement transition retirement policy is malformed"
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

    def parse_authorization(row: Any) -> _RequirementTransitionAuthorization:
        if (
            not isinstance(row, dict)
            or set(row) != required_keys
            or any(not isinstance(row[key], str) for key in required_keys)
        ):
            raise VerificationProfileError(
                f"{source} requirement transition retirement rule is malformed"
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
                f"{source} requirement transition retirement rule is malformed"
            )
        return authorization

    retirements = []
    for row in rows:
        if not isinstance(row, dict) or set(row) != {"obsolete", "replacement"}:
            raise VerificationProfileError(
                f"{source} requirement transition retirement rule is malformed"
            )
        obsolete = parse_authorization(row["obsolete"])
        replacement = parse_authorization(row["replacement"])
        if obsolete == replacement or (obsolete.prompt_path, obsolete.language_id) != (
            replacement.prompt_path,
            replacement.language_id,
        ):
            raise VerificationProfileError(
                f"{source} requirement transition retirement rule is ambiguous"
            )
        retirements.append(_RequirementTransitionRetirement(obsolete, replacement))

    obsolete = [item.obsolete for item in retirements]
    replacements = [item.replacement for item in retirements]
    if (
        len(retirements) > _MAX_REQUIREMENT_TRANSITIONS
        or len(obsolete) != len(set(obsolete))
        or len(replacements) != len(set(replacements))
        or set(obsolete) & set(replacements)
    ):
        raise VerificationProfileError(
            f"{source} requirement transition retirement rules are duplicated or chained"
        )
    return tuple(retirements)


def _validate_legacy_requirement_transition_rows(payload: dict[str, Any]) -> None:
    """Validate ignored schema-1 rows so legacy envelopes remain bounded."""
    rows = payload["requirement_rotations"]
    required_keys = {
        "prompt_path",
        "language_id",
        "from_requirement_id",
        "to_requirement_id",
        "policy_path",
        "from_policy_sha256",
        "to_policy_sha256",
    }
    if not isinstance(rows, list) or len(rows) > _MAX_REQUIREMENT_TRANSITIONS:
        raise TypeError
    identities: list[tuple[PurePosixPath, str]] = []
    for row in rows:
        if (
            not isinstance(row, dict)
            or set(row) != required_keys
            or any(not isinstance(row[key], str) for key in required_keys)
        ):
            raise TypeError
        prompt_path = PurePosixPath(row["prompt_path"])
        language_id = row["language_id"]
        if (
            prompt_path.is_absolute()
            or not prompt_path.parts
            or ".." in prompt_path.parts
            or not language_id
            or language_id.strip() != language_id
            or row["from_requirement_id"] == row["to_requirement_id"]
            or _OPAQUE_REQUIREMENT_ID.fullmatch(row["from_requirement_id"]) is None
            or _OPAQUE_REQUIREMENT_ID.fullmatch(row["to_requirement_id"]) is None
            or PurePosixPath(row["policy_path"]) != PROFILE_PATH
            or row["from_policy_sha256"] == row["to_policy_sha256"]
            or any(
                re.fullmatch(r"[0-9a-f]{64}", row[key]) is None
                for key in ("from_policy_sha256", "to_policy_sha256")
            )
        ):
            raise TypeError
        identities.append((prompt_path, language_id))
    if len(identities) != len(set(identities)):
        raise TypeError


def _parse_dormant_policy_envelope(
    raw: bytes | None, source: str, *, allow_legacy_protected: bool = False
) -> tuple[_PolicyRotationAuthorization, ...]:
    """Parse active authority while allowing only protected bootstrap sources."""
    if raw is None and allow_legacy_protected:
        return ()
    try:
        payload = _strict_policy_json(raw, source) if raw is not None else None
        if payload is None:
            raise TypeError
        schema_version = payload.get("schema_version")
        expected_keys = {
            "schema_version",
            "rotations",
            "requirement_rotations",
        }
        if allow_legacy_protected and schema_version == 1:
            schema_1_keys = {"schema_version", "rotations"}
            schema_1_keys_with_rows = schema_1_keys | {"requirement_rotations"}
            if set(payload) not in (schema_1_keys, schema_1_keys_with_rows):
                raise TypeError
            expected_keys = set(payload)
        elif schema_version == 3:
            expected_keys.add("requirement_rotation_retirements")
        if (
            type(schema_version) is not int
            or set(payload) != expected_keys
            or schema_version not in ({1, 2, 3} if allow_legacy_protected else {2, 3})
            or not isinstance(payload["rotations"], list)
            or (
                schema_version in {2, 3}
                and not isinstance(payload["requirement_rotations"], list)
            )
        ):
            raise TypeError
        if schema_version == 3 and not isinstance(
            payload["requirement_rotation_retirements"], list
        ):
            raise TypeError
        if schema_version == 1 and "requirement_rotations" in payload:
            _validate_legacy_requirement_transition_rows(payload)
    except (json.JSONDecodeError, KeyError, TypeError, UnicodeDecodeError) as exc:
        raise VerificationProfileError(
            f"{source} requirement transition policy envelope is malformed"
        ) from exc

    authorizations: list[_PolicyRotationAuthorization] = []
    for row in payload["rotations"]:
        if (
            not isinstance(row, dict)
            or set(row)
            != {
                "obligation_id",
                "validator_id",
                "from_config_digest",
                "policy_path",
            }
            or any(not isinstance(value, str) for value in row.values())
        ):
            raise VerificationProfileError(
                f"{source} profile rotation rule is malformed"
            )
        authorization = _PolicyRotationAuthorization(
            row["obligation_id"],
            row["validator_id"],
            row["from_config_digest"],
            PurePosixPath(row["policy_path"]),
        )
        if authorization != _PolicyRotationAuthorization(
            _HUMAN_OBLIGATION_ID,
            _HUMAN_VALIDATOR_ID,
            _PLACEHOLDER_POLICY_DIGEST,
            TRUST_POLICY_PATH,
        ):
            raise VerificationProfileError(
                f"{source} profile rotation rule is not authorized"
            )
        authorizations.append(authorization)
    if len(authorizations) != len(set(authorizations)):
        raise VerificationProfileError(
            f"{source} profile rotation rules are duplicated"
        )
    return tuple(authorizations)


def _validate_dormant_policy_installation(
    protected_raw: bytes | None, candidate_raw: bytes | None
) -> None:
    """Keep every existing non-requirement authority while adding future rows."""
    protected = _parse_dormant_policy_envelope(
        protected_raw, "protected", allow_legacy_protected=True
    )
    candidate = _parse_dormant_policy_envelope(candidate_raw, "candidate")
    if candidate != protected:
        raise VerificationProfileError(
            "candidate dormant requirement transition changes protected "
            "profile rotation authority"
        )


def _is_exact_combined_requirement_reconciliation(
    protected_policy: bytes | None,
    candidate_policy: bytes | None,
    protected_profile: bytes | None,
    candidate_profile: bytes | None,
) -> bool:
    """Recognize only the reviewed same-candidate policy/profile byte pairs."""
    if None in (
        protected_policy,
        candidate_policy,
        protected_profile,
        candidate_profile,
    ):
        return False
    assert protected_policy is not None and candidate_policy is not None
    assert protected_profile is not None and candidate_profile is not None
    policy_pair = (
        hashlib.sha256(protected_policy).hexdigest(),
        hashlib.sha256(candidate_policy).hexdigest(),
    )
    profile_pair = (
        hashlib.sha256(protected_profile).hexdigest(),
        hashlib.sha256(candidate_profile).hexdigest(),
    )
    return (policy_pair, profile_pair) in {
        (_LEGACY_PDD_1989_SCHEMA_2_HISTORY, _LEGACY_PDD_1989_PROFILE_BYTES),
        (_PR1971_COMBINED_SCHEMA_2_HISTORY, _PR1971_COMBINED_PROFILE_BYTES),
        (_LEGACY_PDD_2168_SCHEMA_2_HISTORY, _LEGACY_PDD_2168_PROFILE_BYTES),
        (_PDD_2168_REBASED_SCHEMA_2_HISTORY, _PDD_2168_REBASED_PROFILE_BYTES),
        (
            _PDD_1875_COMPOSED_BASE_SCHEMA_2_HISTORY,
            _PDD_1875_COMPOSED_BASE_PROFILE_BYTES,
        ),
        (_PDD_1875_COMPOSED_SCHEMA_2_HISTORY, _PDD_1875_COMPOSED_PROFILE_BYTES),
        (_TERRA_SOL_COMPOSED_SCHEMA_2_HISTORY, _TERRA_SOL_COMPOSED_PROFILE_BYTES),
        (
            _PDD_2168_TERRA_CONTINUATION_SCHEMA_2_HISTORY,
            _PDD_2168_TERRA_CONTINUATION_PROFILE_BYTES,
        ),
    }


def _is_exact_pr1971_pytest_reconciliation(
    manifest: UnitManifest,
    rotation_policies: tuple[bytes | None, bytes | None],
    profile_policies: tuple[bytes | None, bytes | None],
    authorizations: tuple[_RequirementTransitionAuthorization, ...],
) -> bool:
    """Recognize only #1971's complete reviewed profile-obligation addition."""
    pr1971_rows = tuple(
        item
        for item in authorizations
        if item.bindings.head_policy_sha256 == _PR1971_COMBINED_PROFILE_BYTES[1]
    )
    return (
        manifest.repository_id == _PDD_REPOSITORY_ID
        and _is_exact_combined_requirement_reconciliation(
            rotation_policies[0],
            rotation_policies[1],
            profile_policies[0],
            profile_policies[1],
        )
        and pr1971_rows == _PR1971_COMBINED_REQUIREMENT_TRANSITIONS
    )


def _is_exact_pdd2168_reconciliation(
    manifest: UnitManifest,
    rotation_policies: tuple[bytes | None, bytes | None],
    profile_policies: tuple[bytes | None, bytes | None],
) -> bool:
    """Recognize #2168's reviewed final-gate reconciliation on current main."""
    return (
        manifest.repository_id == _PDD_REPOSITORY_ID
        and _is_exact_combined_requirement_reconciliation(
            rotation_policies[0],
            rotation_policies[1],
            profile_policies[0],
            profile_policies[1],
        )
        and (
            hashlib.sha256(rotation_policies[0]).hexdigest(),
            hashlib.sha256(rotation_policies[1]).hexdigest(),
        )
        == _PDD_2168_REBASED_SCHEMA_2_HISTORY
        and (
            hashlib.sha256(profile_policies[0]).hexdigest(),
            hashlib.sha256(profile_policies[1]).hexdigest(),
        )
        == _PDD_2168_REBASED_PROFILE_BYTES
    )


def _is_exact_pdd2168_replay_continuation(
    manifest: UnitManifest,
    rotation_policies: tuple[bytes | None, bytes | None],
    profile_policies: tuple[bytes | None, bytes | None],
) -> bool:
    """Recognize #1998's exact base composed with the reviewed #2168 head."""
    if None in (*rotation_policies, *profile_policies):
        return False
    return (
        manifest.repository_id == _PDD_REPOSITORY_ID
        and hashlib.sha256(rotation_policies[1]).hexdigest()
        == _LEGACY_PDD_2168_SCHEMA_2_HISTORY[1]
        and (
            hashlib.sha256(profile_policies[0]).hexdigest(),
            hashlib.sha256(profile_policies[1]).hexdigest(),
        )
        == (
            "c566e1b87015632ca317e799f2756af9a25281c6e842c03ccad763b20d539bf1",
            _LEGACY_PDD_2168_PROFILE_BYTES[1],
        )
    )


def _is_exact_pdd2168_terra_continuation(
    manifest: UnitManifest,
    rotation_policies: tuple[bytes | None, bytes | None],
    profile_policies: tuple[bytes | None, bytes | None],
) -> bool:
    """Recognize only #2168's exact continuation after Terra/Sol."""
    return (
        manifest.repository_id == _PDD_REPOSITORY_ID
        and _is_exact_combined_requirement_reconciliation(
            rotation_policies[0],
            rotation_policies[1],
            profile_policies[0],
            profile_policies[1],
        )
        and (
            hashlib.sha256(rotation_policies[0]).hexdigest(),
            hashlib.sha256(rotation_policies[1]).hexdigest(),
        )
        == _PDD_2168_TERRA_CONTINUATION_SCHEMA_2_HISTORY
        and (
            hashlib.sha256(profile_policies[0]).hexdigest(),
            hashlib.sha256(profile_policies[1]).hexdigest(),
        )
        == _PDD_2168_TERRA_CONTINUATION_PROFILE_BYTES
    )


def _is_exact_pdd2168_terra_consumed_state(
    manifest: UnitManifest,
    rotation_policies: tuple[bytes | None, bytes | None],
    profile_policies: tuple[bytes | None, bytes | None],
) -> bool:
    """Retain #2168's Terra continuation only at its exact consumed bytes."""
    if None in (*rotation_policies, *profile_policies):
        return False
    return (
        manifest.repository_id == _PDD_REPOSITORY_ID
        and (
            hashlib.sha256(rotation_policies[0]).hexdigest(),
            hashlib.sha256(rotation_policies[1]).hexdigest(),
        )
        == _PDD_2168_TERRA_CONTINUATION_SCHEMA_2_HISTORY
        and (
            hashlib.sha256(profile_policies[0]).hexdigest(),
            hashlib.sha256(profile_policies[1]).hexdigest(),
        )
        == (
            _PDD_2168_TERRA_CONTINUATION_PROFILE_BYTES[1],
            _PDD_2168_TERRA_CONTINUATION_PROFILE_BYTES[1],
        )
    )


def _is_exact_pdd2168_gemini_36_composed_state(
    manifest: UnitManifest,
    rotation_policies: tuple[bytes | None, bytes | None],
    profile_policies: tuple[bytes | None, bytes | None],
) -> bool:
    """Recognize #2168 consumed on the exact Gemini 3.6 Phase-A policy."""
    if None in (*rotation_policies, *profile_policies):
        return False
    return (
        manifest.repository_id == _PDD_REPOSITORY_ID
        and (
            hashlib.sha256(rotation_policies[0]).hexdigest(),
            hashlib.sha256(rotation_policies[1]).hexdigest(),
        )
        == _PDD_2168_GEMINI_36_SCHEMA_2_STATE
        and (
            hashlib.sha256(profile_policies[0]).hexdigest(),
            hashlib.sha256(profile_policies[1]).hexdigest(),
        )
        in _PDD_2168_GEMINI_36_PROFILE_STATES
    )


def _candidate_authorization_is_strictly_dormant(
    manifest: UnitManifest,
    base: Mapping[UnitId, _ProfileInput],
    head: Mapping[UnitId, _ProfileInput],
    policies: tuple[bytes | None, bytes | None],
    prompts: tuple[bytes | None, bytes | None],
    authorization: _RequirementTransitionAuthorization,
) -> bool:
    """Accept a future rule only while every protected source byte is unchanged."""
    unit_id = UnitId(
        manifest.repository_id,
        authorization.prompt_path,
        authorization.language_id,
    )
    protected = base.get(unit_id)
    candidate = head.get(unit_id)
    if protected is None or protected != candidate:
        return False

    bindings = authorization.bindings
    if (
        policies[0] is None
        or policies[0] != policies[1]
        or prompts[0] is None
        or prompts[0] != prompts[1]
        or _sha256(policies[0]) != bindings.base_policy_sha256
        or _sha256(prompts[0]) != bindings.base_prompt_sha256
        or authorization.from_requirement_id
        != f"CONTRACT-SHA256:{bindings.base_prompt_sha256}"
        or authorization.to_requirement_id
        != f"CONTRACT-SHA256:{bindings.head_prompt_sha256}"
        or bindings.base_prompt_sha256 == bindings.head_prompt_sha256
        or bindings.base_policy_sha256 == bindings.head_policy_sha256
        or protected.requirements != (authorization.from_requirement_id,)
        or _prompt_requirements(prompts[0]) != (authorization.from_requirement_id,)
    ):
        return False

    human = next(
        (
            obligation
            for obligation in protected.obligations
            if obligation.obligation_id == _HUMAN_OBLIGATION_ID
        ),
        None,
    )
    return bool(
        human is not None
        and human.kind == "human-attestation"
        and human.validator_id == _HUMAN_VALIDATOR_ID
        and human.requirement_ids == (authorization.from_requirement_id,)
        and human.required
    )


def _authorization_is_consumed_at_current_state(
    manifest: UnitManifest,
    base: Mapping[UnitId, _ProfileInput],
    head: Mapping[UnitId, _ProfileInput],
    prompts: tuple[bytes | None, bytes | None],
    authorization: _RequirementTransitionAuthorization,
) -> bool:
    """Permit advancing an identity only after its protected rule was consumed."""
    unit_id = UnitId(
        manifest.repository_id,
        authorization.prompt_path,
        authorization.language_id,
    )
    protected = base.get(unit_id)
    candidate = head.get(unit_id)
    if (
        protected is None
        or protected != candidate
        or protected.requirements != (authorization.to_requirement_id,)
        or prompts[0] is None
        or prompts[0] != prompts[1]
        or _sha256(prompts[0]) != authorization.bindings.head_prompt_sha256
        or _prompt_requirements(prompts[0]) != (authorization.to_requirement_id,)
    ):
        return False
    human = next(
        (
            obligation
            for obligation in protected.obligations
            if obligation.obligation_id == _HUMAN_OBLIGATION_ID
        ),
        None,
    )
    return bool(
        human is not None
        and human.kind == "human-attestation"
        and human.validator_id == _HUMAN_VALIDATOR_ID
        and human.requirement_ids == (authorization.to_requirement_id,)
        and human.required
    )


def _active_requirement_transition_authorizations(
    authorizations: tuple[_RequirementTransitionAuthorization, ...],
    retirements: tuple[_RequirementTransitionRetirement, ...],
    source: str,
) -> tuple[_RequirementTransitionAuthorization, ...]:
    """Return the unretired rows after validating immutable history links."""
    rows = set(authorizations)
    retired = {item.obsolete for item in retirements}
    replacements = {item.replacement for item in retirements}
    if not retired <= rows or not replacements <= rows:
        raise VerificationProfileError(
            f"{source} requirement transition retirement does not name exact rows"
        )
    active = tuple(item for item in authorizations if item not in retired)
    identities = [(item.prompt_path, item.language_id) for item in active]
    if len(identities) != len(set(identities)):
        raise VerificationProfileError(
            f"{source} active requirement transition rules are ambiguous"
        )
    return active


def _retirement_is_provably_unreachable_dormant(
    manifest: UnitManifest,
    base: Mapping[UnitId, _ProfileInput],
    head: Mapping[UnitId, _ProfileInput],
    policies: tuple[bytes | None, bytes | None],
    prompts: tuple[bytes | None, bytes | None],
    authorization: _RequirementTransitionAuthorization,
) -> bool:
    """Accept only a dormant row whose whole-policy bindings cannot be reached."""
    unit_id = UnitId(
        manifest.repository_id,
        authorization.prompt_path,
        authorization.language_id,
    )
    protected = base.get(unit_id)
    candidate = head.get(unit_id)
    bindings = authorization.bindings
    if (
        protected is None
        or protected != candidate
        or policies[0] is None
        or policies[0] != policies[1]
        or prompts[0] is None
        or prompts[0] != prompts[1]
        or _sha256(policies[0])
        in {bindings.base_policy_sha256, bindings.head_policy_sha256}
        or _sha256(prompts[0]) != bindings.base_prompt_sha256
        or protected.requirements != (authorization.from_requirement_id,)
        or _prompt_requirements(prompts[0]) != (authorization.from_requirement_id,)
    ):
        return False
    human = next(
        (
            obligation
            for obligation in protected.obligations
            if obligation.obligation_id == _HUMAN_OBLIGATION_ID
        ),
        None,
    )
    return bool(
        human is not None
        and human.kind == "human-attestation"
        and human.validator_id == _HUMAN_VALIDATOR_ID
        and human.requirement_ids == (authorization.from_requirement_id,)
        and human.required
    )


def _validate_retirement_history_representation(
    protected_raw: bytes | None,
    candidate_raw: bytes | None,
) -> None:
    """Require every protected row and retirement token to remain byte-identical."""
    protected_rows, protected_retirements = _raw_requirement_transition_history(
        protected_raw, "protected"
    )
    candidate_rows, candidate_retirements = _raw_requirement_transition_history(
        candidate_raw, "candidate"
    )
    if (
        candidate_rows[: len(protected_rows)] != protected_rows
        or candidate_retirements[: len(protected_retirements)] != protected_retirements
    ):
        raise VerificationProfileError(
            "candidate retirement history rewrites protected representation"
        )


def _validate_schema_2_history_representation(
    manifest: UnitManifest,
    protected_raw: bytes | None,
    candidate_raw: bytes | None,
    protected_rows: tuple[_RequirementTransitionAuthorization, ...],
    candidate_rows: tuple[_RequirementTransitionAuthorization, ...],
) -> None:
    """Keep surviving schema-2 row tokens exact and ahead of new rows."""
    if (
        manifest.repository_id == _PDD_REPOSITORY_ID
        and protected_raw is not None
        and candidate_raw is not None
        and (
            hashlib.sha256(protected_raw).hexdigest(),
            hashlib.sha256(candidate_raw).hexdigest(),
        )
        in {
            _LEGACY_PDD_1989_SCHEMA_2_HISTORY,
            _LEGACY_PDD_2168_SCHEMA_2_HISTORY,
            _PDD_2168_REBASED_SCHEMA_2_HISTORY,
            _PDD_1875_COMPOSED_BASE_SCHEMA_2_HISTORY,
            _PDD_1875_COMPOSED_SCHEMA_2_HISTORY,
        }
    ):
        return
    protected_tokens, _ = _raw_requirement_transition_history(
        protected_raw, "protected"
    )
    candidate_tokens, _ = _raw_requirement_transition_history(
        candidate_raw, "candidate"
    )
    candidate_set = set(candidate_rows)
    surviving_history = tuple(
        (row, token)
        for row, token in zip(protected_rows, protected_tokens, strict=True)
        if row in candidate_set
    )
    candidate_prefix = tuple(zip(candidate_rows, candidate_tokens, strict=True))[
        : len(surviving_history)
    ]
    if candidate_prefix != surviving_history:
        raise VerificationProfileError(
            "candidate schema-2 history rewrites protected representation"
        )


def _policy_schema_version(raw: bytes | None, source: str) -> int | None:
    """Return the already-validated policy schema without normalizing its bytes."""
    if raw is None:
        return None
    try:
        schema_version = _strict_policy_json(raw, source)["schema_version"]
        if type(schema_version) is not int:
            raise TypeError
    except (json.JSONDecodeError, KeyError, TypeError, UnicodeDecodeError) as exc:
        raise VerificationProfileError(
            f"{source} requirement transition policy is malformed"
        ) from exc
    return schema_version


def _managed_prompt_byte_changes(
    root: Path,
    manifest: UnitManifest,
    approved_aliases: Mapping[PurePosixPath, PurePosixPath],
) -> set[PurePosixPath]:
    """Return changed canonical managed prompts using the manifest blob inventory."""
    candidates = {
        item.candidate_id.artifact_relpath: item for item in manifest.candidates
    }
    changed = set()
    for unit_id in manifest.expected_managed:
        prompt_path = _canonical_prompt_path(unit_id.prompt_relpath, approved_aliases)
        candidate = candidates.get(prompt_path)
        if candidate is not None and candidate.base_object_id is not None:
            if candidate.base_object_id != candidate.head_object_id:
                changed.add(prompt_path)
            continue
        base_prompt = read_git_blob(root, manifest.base_ref, prompt_path)
        head_prompt = read_git_blob(root, manifest.head_ref, prompt_path)
        if base_prompt is None or head_prompt is None or base_prompt != head_prompt:
            changed.add(prompt_path)
    return changed


def _validate_retirement_managed_prompt_bytes(
    root: Path,
    manifest: UnitManifest,
    approved_aliases: Mapping[PurePosixPath, PurePosixPath],
) -> None:
    """Keep every canonical managed prompt byte-identical during retirement Phase A."""
    changed = _managed_prompt_byte_changes(root, manifest, approved_aliases)
    if changed:
        raise VerificationProfileError(
            f"candidate retirement changes managed prompt bytes: {sorted(changed)[0]}"
        )


def _validate_new_authorization_managed_prompt_bytes(
    root: Path,
    manifest: UnitManifest,
    approved_aliases: Mapping[PurePosixPath, PurePosixPath],
    allowed_changes: set[PurePosixPath],
) -> None:
    """Keep every managed prompt unchanged while installing future authority."""
    changed = _managed_prompt_byte_changes(root, manifest, approved_aliases)
    unauthorized = changed - allowed_changes
    if unauthorized:
        raise VerificationProfileError(
            "candidate authority-only change modifies managed prompt bytes: "
            f"{sorted(unauthorized)[0]}"
        )


def _validate_consumed_managed_prompt_bytes(
    root: Path,
    manifest: UnitManifest,
    approved_aliases: Mapping[PurePosixPath, PurePosixPath],
    authorizations: tuple[_RequirementTransitionAuthorization, ...],
    updates: Mapping[UnitId, _ProfileInput],
    profile_addition_paths: set[PurePosixPath],
) -> None:
    """Limit Phase B prompt drift to exact protected rows consumed in this candidate."""
    consumed = {
        _canonical_prompt_path(authorization.prompt_path, approved_aliases)
        for authorization in authorizations
        if UnitId(
            manifest.repository_id,
            authorization.prompt_path,
            authorization.language_id,
        )
        in updates
    }
    unauthorized = (
        _managed_prompt_byte_changes(root, manifest, approved_aliases)
        - consumed
        - profile_addition_paths
    )
    if unauthorized:
        raise VerificationProfileError(
            "candidate requirement transition changes unmanaged prompt bytes: "
            f"{sorted(unauthorized)[0]}"
        )


def _validate_candidate_retirements(
    root: Path,
    manifest: UnitManifest,
    approved_aliases: Mapping[PurePosixPath, PurePosixPath],
    base: Mapping[UnitId, _ProfileInput],
    head: Mapping[UnitId, _ProfileInput],
    policies: tuple[bytes | None, bytes | None],
    prompts: Mapping[PurePosixPath, tuple[bytes | None, bytes | None]],
    protected_rows: tuple[_RequirementTransitionAuthorization, ...],
    protected_retirements: tuple[_RequirementTransitionRetirement, ...],
    candidate_rows: tuple[_RequirementTransitionAuthorization, ...],
    candidate_retirements: tuple[_RequirementTransitionRetirement, ...],
    protected_active: tuple[_RequirementTransitionAuthorization, ...],
    protected_policy: bytes | None,
    candidate_policy: bytes | None,
) -> None:
    """Validate append-only retirement/reissue of unreachable protected rows."""
    protected_schema = _policy_schema_version(protected_policy, "protected")
    candidate_schema = _policy_schema_version(candidate_policy, "candidate")
    if protected_schema == 2 and candidate_schema == 2:
        _validate_schema_2_history_representation(
            manifest,
            protected_policy,
            candidate_policy,
            protected_rows,
            candidate_rows,
        )
    if protected_schema != 3 and candidate_schema != 3:
        return
    if (
        len(candidate_rows) < len(protected_rows)
        or candidate_rows[: len(protected_rows)] != protected_rows
        or candidate_retirements[: len(protected_retirements)] != protected_retirements
    ):
        raise VerificationProfileError(
            "candidate retirement history is not append-only"
        )
    if protected_schema == 3 and candidate_schema != 3:
        raise VerificationProfileError(
            "candidate cannot remove protected schema-3 retirement history"
        )
    _validate_retirement_history_representation(protected_policy, candidate_policy)
    new_retirements = candidate_retirements[len(protected_retirements) :]
    if candidate_schema == 3 and protected_schema != 3 and not new_retirements:
        raise VerificationProfileError(
            "candidate schema-3 requirement transition policy requires a "
            "retirement/reissue record"
        )
    if new_retirements:
        _validate_retirement_managed_prompt_bytes(root, manifest, approved_aliases)
    for retirement in new_retirements:
        if (
            retirement.obsolete not in protected_active
            or retirement.replacement in protected_rows
            or retirement.replacement not in candidate_rows
            or not _retirement_is_provably_unreachable_dormant(
                manifest,
                base,
                head,
                policies,
                prompts[retirement.obsolete.prompt_path],
                retirement.obsolete,
            )
            or not _candidate_authorization_is_strictly_dormant(
                manifest,
                base,
                head,
                policies,
                prompts[retirement.replacement.prompt_path],
                retirement.replacement,
            )
        ):
            raise VerificationProfileError(
                "candidate retirement lacks an exact unreachable protected row "
                "and dormant replacement"
            )


def _load_requirement_transition_authorizations(
    root: Path,
    manifest: UnitManifest,
    base: Mapping[UnitId, _ProfileInput] | None = None,
    head: Mapping[UnitId, _ProfileInput] | None = None,
    approved_aliases: Mapping[PurePosixPath, PurePosixPath] | None = None,
) -> tuple[
    tuple[_RequirementTransitionAuthorization, ...],
    dict[PurePosixPath, tuple[bytes | None, bytes | None]],
    tuple[_RequirementTransitionAuthorization, ...],
]:
    """Return protected/candidate rules and candidate-added dormant rows.

    ``base`` and ``head`` are supplied by the production loader so prompt blobs
    can be evaluated once and reused. Optional empty mappings preserve the
    fail-closed two-argument boundary used by protected bootstrap-policy tests.
    The public loader enforces managed-prompt isolation for returned additions.
    """
    base = {} if base is None else base
    head = {} if head is None else head
    approved_aliases = {} if approved_aliases is None else approved_aliases
    protected_policy = read_git_blob(root, manifest.base_ref, ROTATION_POLICY_PATH)
    candidate_policy = read_git_blob(root, manifest.head_ref, ROTATION_POLICY_PATH)
    protected_rows = _parse_requirement_transition_authorizations(
        protected_policy, "protected"
    )
    candidate_rows = _parse_requirement_transition_authorizations(
        candidate_policy, "candidate"
    )
    protected_retirements = _parse_requirement_transition_retirements(
        protected_policy, "protected"
    )
    candidate_retirements = _parse_requirement_transition_retirements(
        candidate_policy, "candidate"
    )
    protected = _active_requirement_transition_authorizations(
        protected_rows, protected_retirements, "protected"
    )
    candidate = _active_requirement_transition_authorizations(
        candidate_rows, candidate_retirements, "candidate"
    )
    is_pdd_repository = manifest.repository_id == _PDD_REPOSITORY_ID
    authority = set(protected)
    if is_pdd_repository:
        authority.update(_BOOTSTRAP_REQUIREMENT_TRANSITIONS)
    policies = (
        read_git_blob(root, manifest.base_ref, PROFILE_PATH),
        read_git_blob(root, manifest.head_ref, PROFILE_PATH),
    )
    terra_sol_reconciliation = (
        is_pdd_repository
        and protected_policy is not None
        and candidate_policy is not None
        and policies[0] is not None
        and policies[1] is not None
        and (
            hashlib.sha256(protected_policy).hexdigest(),
            hashlib.sha256(candidate_policy).hexdigest(),
        )
        == _TERRA_SOL_COMPOSED_SCHEMA_2_HISTORY
        and (
            hashlib.sha256(policies[0]).hexdigest(),
            hashlib.sha256(policies[1]).hexdigest(),
        )
        == _TERRA_SOL_COMPOSED_PROFILE_BYTES
    )
    terra_sol_consumed_state = (
        is_pdd_repository
        and protected_policy is not None
        and candidate_policy is not None
        and policies[0] is not None
        and policies[1] is not None
        and (
            hashlib.sha256(protected_policy).hexdigest(),
            hashlib.sha256(candidate_policy).hexdigest(),
        )
        == _TERRA_SOL_COMPOSED_SCHEMA_2_HISTORY
        and (
            hashlib.sha256(policies[0]).hexdigest(),
            hashlib.sha256(policies[1]).hexdigest(),
        )
        == (
            _TERRA_SOL_COMPOSED_PROFILE_BYTES[1],
            _TERRA_SOL_COMPOSED_PROFILE_BYTES[1],
        )
    )
    policy_digests = (
        (
            hashlib.sha256(protected_policy).hexdigest(),
            hashlib.sha256(candidate_policy).hexdigest(),
        )
        if protected_policy is not None and candidate_policy is not None
        else None
    )
    profile_digests = (
        (
            hashlib.sha256(policies[0]).hexdigest(),
            hashlib.sha256(policies[1]).hexdigest(),
        )
        if policies[0] is not None and policies[1] is not None
        else None
    )
    gemini_36_terra_sol_state = is_pdd_repository and (
        (policy_digests, profile_digests)
        in {
            (
                _GEMINI_36_PHASE_A_SCHEMA_2_HISTORY,
                (_GEMINI_36_PROFILE_BYTES[0], _GEMINI_36_PROFILE_BYTES[0]),
            ),
            (
                (
                    _GEMINI_36_PHASE_A_SCHEMA_2_HISTORY[1],
                    _GEMINI_36_PHASE_A_SCHEMA_2_HISTORY[1],
                ),
                (_GEMINI_36_PROFILE_BYTES[0], _GEMINI_36_PROFILE_BYTES[0]),
            ),
            (
                (
                    _GEMINI_36_PHASE_A_SCHEMA_2_HISTORY[1],
                    _GEMINI_36_PHASE_A_SCHEMA_2_HISTORY[1],
                ),
                _GEMINI_36_PROFILE_BYTES,
            ),
            (
                (
                    _GEMINI_36_PHASE_A_SCHEMA_2_HISTORY[1],
                    _GEMINI_36_PHASE_A_SCHEMA_2_HISTORY[1],
                ),
                (_GEMINI_36_PROFILE_BYTES[1], _GEMINI_36_PROFILE_BYTES[1]),
            ),
        }
    )
    if (
        terra_sol_reconciliation
        or terra_sol_consumed_state
        or gemini_36_terra_sol_state
    ):
        # This candidate predates a dormant policy installation.  Expose only
        # its reviewed transitions while consuming the exact profile update,
        # then retain those transitions only at the exact consumed state.
        terra_sol_identities = {
            (item.prompt_path, item.language_id)
            for item in _TERRA_SOL_COMPOSED_REQUIREMENT_TRANSITIONS
        }
        candidate = tuple(
            item
            for item in candidate
            if (item.prompt_path, item.language_id) not in terra_sol_identities
        ) + _TERRA_SOL_COMPOSED_REQUIREMENT_TRANSITIONS
        authority.update(_TERRA_SOL_COMPOSED_REQUIREMENT_TRANSITIONS)
    pdd2168_terra_continuation = _is_exact_pdd2168_terra_continuation(
        manifest, (protected_policy, candidate_policy), policies
    )
    pdd2168_terra_consumed_state = _is_exact_pdd2168_terra_consumed_state(
        manifest, (protected_policy, candidate_policy), policies
    )
    pdd2168_gemini_36_composed_state = (
        _is_exact_pdd2168_gemini_36_composed_state(
            manifest, (protected_policy, candidate_policy), policies
        )
    )
    if (
        pdd2168_terra_continuation
        or pdd2168_terra_consumed_state
        or pdd2168_gemini_36_composed_state
    ):
        continuation_identities = {
            (item.prompt_path, item.language_id)
            for item in (
                _TERRA_SOL_COMPOSED_REQUIREMENT_TRANSITIONS
                + _PDD_2168_TERRA_CONTINUATION_REQUIREMENT_TRANSITIONS
            )
        }
        continuation_transitions = tuple(
            item
            for item in _TERRA_SOL_COMPOSED_REQUIREMENT_TRANSITIONS
            if (item.prompt_path, item.language_id) not in continuation_identities
        ) + _PDD_2168_TERRA_CONTINUATION_REQUIREMENT_TRANSITIONS
        candidate = tuple(
            item
            for item in candidate
            if (item.prompt_path, item.language_id) not in continuation_identities
        ) + continuation_transitions
        authority.update(continuation_transitions)
    pr1971_reconciliation = _is_exact_pr1971_pytest_reconciliation(
        manifest, (protected_policy, candidate_policy), policies, candidate
    )
    if pr1971_reconciliation:
        # Historical #1971 is accepted only as its complete, byte-bound
        # reconciliation; it is never installed as general replay authority.
        authority.update(_PR1971_COMBINED_REQUIREMENT_TRANSITIONS)
    prompt_paths = {item.prompt_path for item in (*protected_rows, *candidate)}
    prompts = {
        prompt_path: (
            read_git_blob(
                root,
                manifest.base_ref,
                _canonical_prompt_path(prompt_path, approved_aliases),
            ),
            read_git_blob(
                root,
                manifest.head_ref,
                _canonical_prompt_path(prompt_path, approved_aliases),
            ),
        )
        for prompt_path in prompt_paths
    }
    protected_by_identity = {
        (item.prompt_path, item.language_id): item for item in protected
    }
    _validate_candidate_retirements(
        root,
        manifest,
        approved_aliases,
        base,
        head,
        policies,
        prompts,
        protected_rows,
        protected_retirements,
        candidate_rows,
        candidate_retirements,
        protected,
        protected_policy,
        candidate_policy,
    )
    legacy_schema_2_reconciliation = (
        is_pdd_repository
        and protected_policy is not None
        and candidate_policy is not None
        and policies[0] is not None
        and policies[1] is not None
        and (
            (
                hashlib.sha256(protected_policy).hexdigest(),
                hashlib.sha256(candidate_policy).hexdigest(),
            ),
            (
                hashlib.sha256(policies[0]).hexdigest(),
                hashlib.sha256(policies[1]).hexdigest(),
            ),
        )
        in {
            (
                _LEGACY_PDD_1989_SCHEMA_2_HISTORY,
                _LEGACY_PDD_1989_PROFILE_BYTES,
            ),
            (
                _LEGACY_PDD_2168_SCHEMA_2_HISTORY,
                _LEGACY_PDD_2168_PROFILE_BYTES,
            ),
            (
                _PDD_2168_REBASED_SCHEMA_2_HISTORY,
                _PDD_2168_REBASED_PROFILE_BYTES,
            ),
            (
                _PDD_1875_COMPOSED_BASE_SCHEMA_2_HISTORY,
                _PDD_1875_COMPOSED_BASE_PROFILE_BYTES,
            ),
            (
                _PDD_1875_COMPOSED_SCHEMA_2_HISTORY,
                _PDD_1875_COMPOSED_PROFILE_BYTES,
            ),
        }
    )
    retired_by_candidate = {item.obsolete for item in candidate_retirements}
    new_authorizations = tuple(
        item
        for item in candidate
        if item not in protected
        and not (is_pdd_repository and item in _REPLAY_PROFILE_REQUIREMENT_TRANSITIONS)
        and not (
            is_pdd_repository and item in _PDD_2168_FINAL_GATE_REQUIREMENT_TRANSITIONS
        )
    )
    if (
        legacy_schema_2_reconciliation
        or pr1971_reconciliation
        or terra_sol_reconciliation
        or terra_sol_consumed_state
        or pdd2168_terra_continuation
        or pdd2168_terra_consumed_state
        or pdd2168_gemini_36_composed_state
    ):
        # The exact historical pair both installed and consumed its authority
        # before Phase-A isolation existed; validate it as consumption below.
        new_authorizations = ()
    elif gemini_36_terra_sol_state:
        # The exact Gemini policy states retain Terra/Sol's historical overlay
        # for stationary evaluation, but those synthetic rows are not newly
        # installed authority. Keep the two genuine Gemini rows visible during
        # Phase A and exclude only the overlay so Phase B can consume them.
        terra_sol_authority = set(_TERRA_SOL_COMPOSED_REQUIREMENT_TRANSITIONS)
        new_authorizations = tuple(
            item for item in new_authorizations if item not in terra_sol_authority
        )
    for item in candidate:
        if item in authority:
            if (
                item in _BOOTSTRAP_REQUIREMENT_TRANSITIONS
                and item not in protected
                and not (
                    is_pdd_repository
                    and item
                    in (
                        _REPLAY_PROFILE_REQUIREMENT_TRANSITIONS
                        + _PDD_2168_FINAL_GATE_REQUIREMENT_TRANSITIONS
                        + _PDD_1875_CHECKUP_REQUIREMENT_TRANSITIONS
                    )
                )
                and policies[0] != policies[1]
                and not legacy_schema_2_reconciliation
                and not pr1971_reconciliation
                and not terra_sol_reconciliation
                and not terra_sol_consumed_state
                and not pdd2168_terra_continuation
                and not pdd2168_terra_consumed_state
                and not pdd2168_gemini_36_composed_state
                and not gemini_36_terra_sol_state
            ):
                raise VerificationProfileError(
                    "candidate legacy bootstrap requirement transition changes "
                    "protected verification-profile bytes"
                )
            continue
        prompt_pair = prompts[item.prompt_path]
        prior = protected_by_identity.get((item.prompt_path, item.language_id))
        if not _candidate_authorization_is_strictly_dormant(
            manifest, base, head, policies, prompt_pair, item
        ):
            raise VerificationProfileError(
                "candidate requirement transition lacks protected authorization"
            )
        if (
            prior is not None
            and prior not in retired_by_candidate
            and not _authorization_is_consumed_at_current_state(
                manifest, base, head, prompt_pair, prior
            )
        ):
            raise VerificationProfileError(
                "candidate replaced unconsumed protected requirement transition"
            )
    candidate_authority = set(candidate_rows)
    for item in protected:
        if item in candidate_authority or legacy_schema_2_reconciliation:
            continue
        if is_pdd_repository and any(
            protected == item and replacement in candidate_authority
            for protected, replacement in _REPLAY_REQUIREMENT_REPLACEMENTS
        ):
            continue
        if is_pdd_repository and any(
            item.prompt_path == replacement.prompt_path
            and item.language_id == replacement.language_id
            and replacement in candidate_authority
            for replacement in _PDD_2168_FINAL_GATE_REQUIREMENT_TRANSITIONS
        ):
            continue
        if not _authorization_is_consumed_at_current_state(
            manifest, base, head, prompts[item.prompt_path], item
        ):
            raise VerificationProfileError(
                "candidate removed unconsumed protected requirement transition"
            )
    if candidate_policy != protected_policy:
        _validate_dormant_policy_installation(protected_policy, candidate_policy)
    return candidate, prompts, new_authorizations


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
    pytest_obligation: VerificationObligation | None = None,
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
    obligations = {
        obligation_id: replace(
            obligation,
            requirement_ids=tuple(
                (
                    authorization.to_requirement_id
                    if requirement_id == authorization.from_requirement_id
                    else requirement_id
                )
                for requirement_id in obligation.requirement_ids
            ),
        )
        for obligation_id, obligation in obligations.items()
    }
    if pytest_obligation is not None:
        obligations[pytest_obligation.obligation_id] = pytest_obligation
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
    pytest_obligation: VerificationObligation | None = None,
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
    prompts = context.prompts[authorization.prompt_path]
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
    result, reason = _expected_requirement_update(
        authorization, protected, candidate, pytest_obligation
    )
    return unit_id, result, reason


def _authorized_requirement_updates(
    root: Path,
    manifest: UnitManifest,
    base: dict[UnitId, _ProfileInput],
    head: dict[UnitId, _ProfileInput],
    authorizations: tuple[_RequirementTransitionAuthorization, ...],
    prompts: Mapping[PurePosixPath, tuple[bytes | None, bytes | None]],
) -> tuple[dict[UnitId, _ProfileInput], list[str]]:
    """Authorize only exact opaque requirement and human mapping replacements."""
    updates: dict[UnitId, _ProfileInput] = {}
    invalid: list[str] = []
    policies = (
        read_git_blob(root, manifest.base_ref, PROFILE_PATH),
        read_git_blob(root, manifest.head_ref, PROFILE_PATH),
    )
    rotation_policies = (
        read_git_blob(root, manifest.base_ref, ROTATION_POLICY_PATH),
        read_git_blob(root, manifest.head_ref, ROTATION_POLICY_PATH),
    )
    pr1971_pytest_reconciliation = _is_exact_pr1971_pytest_reconciliation(
        manifest, rotation_policies, policies, authorizations
    )
    pdd2168_reconciliation = _is_exact_pdd2168_reconciliation(
        manifest, rotation_policies, policies
    )
    pdd2168_replay_continuation = _is_exact_pdd2168_replay_continuation(
        manifest, rotation_policies, policies
    )
    pdd2168_terra_continuation = _is_exact_pdd2168_terra_continuation(
        manifest, rotation_policies, policies
    )
    pdd2168_terra_consumed_state = _is_exact_pdd2168_terra_consumed_state(
        manifest, rotation_policies, policies
    )
    pdd2168_gemini_36_composed_state = (
        _is_exact_pdd2168_gemini_36_composed_state(
            manifest, rotation_policies, policies
        )
    )
    pdd1875_reconciliation = (
        manifest.repository_id == _PDD_REPOSITORY_ID
        and _is_exact_combined_requirement_reconciliation(
            rotation_policies[0], rotation_policies[1], policies[0], policies[1]
        )
        and (
            hashlib.sha256(rotation_policies[0]).hexdigest(),
            hashlib.sha256(rotation_policies[1]).hexdigest(),
        )
        == _PDD_1875_COMPOSED_SCHEMA_2_HISTORY
        and (
            hashlib.sha256(policies[0]).hexdigest(),
            hashlib.sha256(policies[1]).hexdigest(),
        )
        == _PDD_1875_COMPOSED_PROFILE_BYTES
    )
    context = _RequirementTransitionContext(
        root, manifest, base, head, policies, prompts
    )
    for authorization in authorizations:
        unit_id = UnitId(
            manifest.repository_id,
            authorization.prompt_path,
            authorization.language_id,
        )
        if (
            pdd2168_reconciliation
            and authorization in _PDD_2168_FINAL_GATE_REQUIREMENT_TRANSITIONS
        ):
            updates[unit_id] = head[unit_id]
            continue
        if (
            pdd1875_reconciliation
            and authorization in _PDD_1875_CHECKUP_REQUIREMENT_TRANSITIONS
        ):
            updates[unit_id] = head[unit_id]
            continue
        if (
            (
                pdd2168_terra_continuation
                or pdd2168_terra_consumed_state
                or pdd2168_gemini_36_composed_state
            )
            and authorization
            in (
                _TERRA_SOL_COMPOSED_REQUIREMENT_TRANSITIONS
                + _PDD_2168_TERRA_CONTINUATION_REQUIREMENT_TRANSITIONS
            )
        ):
            # Estimation callers deliberately load a sparse subset of profile
            # rows.  The exact-state shortcut may still enumerate the full
            # historical transition list, so only materialize a transition
            # whose candidate unit was actually supplied.  Normal manifest
            # verification supplies every unit and retains the same authority.
            if unit_id in head:
                updates[unit_id] = head[unit_id]
            continue
        if pdd2168_replay_continuation and authorization in (
            _REPLAY_PROFILE_REQUIREMENT_TRANSITIONS
            + _PDD_2168_FINAL_GATE_REQUIREMENT_TRANSITIONS
        ):
            updates[unit_id] = head[unit_id]
            continue
        pytest_obligation = None
        if pr1971_pytest_reconciliation:
            pytest_obligation = _PR1971_COMBINED_PYTEST_OBLIGATIONS.get(
                (authorization.prompt_path, authorization.language_id)
            )
        unit_id, result, reason = _evaluate_requirement_authorization(
            context, authorization, pytest_obligation
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
    (
        requirement_authorizations,
        requirement_prompts,
        new_requirement_authorizations,
    ) = _load_requirement_transition_authorizations(
        root, manifest, base, head, approved_aliases
    )
    profile_additions = _authorized_profile_additions(root, manifest, base, head)
    if _is_exact_pdd2168_replay_continuation(
        manifest,
        (
            read_git_blob(root, manifest.base_ref, ROTATION_POLICY_PATH),
            read_git_blob(root, manifest.head_ref, ROTATION_POLICY_PATH),
        ),
        (
            read_git_blob(root, manifest.base_ref, PROFILE_PATH),
            read_git_blob(root, manifest.head_ref, PROFILE_PATH),
        ),
    ):
        mock_unit_id = UnitId(
            manifest.repository_id,
            PurePosixPath("pdd/prompts/mock_contract_validation_python.prompt"),
            "python",
        )
        profile_additions[mock_unit_id] = head[mock_unit_id]
    if new_requirement_authorizations:
        _validate_new_authorization_managed_prompt_bytes(
            root,
            manifest,
            approved_aliases,
            {
                _canonical_prompt_path(unit_id.prompt_relpath, approved_aliases)
                for unit_id in profile_additions
            },
        )
    requirement_updates, requirement_invalid = _authorized_requirement_updates(
        root,
        manifest,
        base,
        head,
        requirement_authorizations,
        requirement_prompts,
    )
    if requirement_updates:
        _validate_consumed_managed_prompt_bytes(
            root,
            manifest,
            approved_aliases,
            requirement_authorizations,
            requirement_updates,
            {
                _canonical_prompt_path(unit_id.prompt_relpath, approved_aliases)
                for unit_id in profile_additions
            },
        )
    invalid.extend(requirement_invalid)
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
