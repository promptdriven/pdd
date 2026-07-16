"""Exact preauthorization tests for the two PDD estimate profile rotations."""

from __future__ import annotations

import hashlib
import json
from pathlib import Path, PurePosixPath
from types import SimpleNamespace

import pytest

from pdd.sync_core import verification
from pdd.sync_core.types import UnitId
from pdd.sync_core.verification import PROFILE_PATH as PROFILE_REL_PATH


ROOT = Path(__file__).resolve().parents[1]
PROFILE_FILE = ROOT / PROFILE_REL_PATH
ROTATION_FILE = ROOT / ".pdd" / "verification-profile-rotations.json"
REPOSITORY_ID = "3b4d7b1c-d6cc-4752-ba93-6b98d1a710e0"

ESTIMATE_REQUIREMENT_ROTATIONS = (
    {
        "prompt_path": "pdd/prompts/commands/generate_python.prompt",
        "language_id": "python",
        "from_requirement_id": (
            "CONTRACT-SHA256:83b45ad928a9bac3567dea786c4b48819400247e63c7210d8cb5d26e4750a52f"
        ),
        "to_requirement_id": (
            "CONTRACT-SHA256:503f997914734dbef8e0542efd1f3c495fa15a652782e15bf63638e35c841403"
        ),
        "policy_path": ".pdd/verification-profiles.json",
        "base_policy_sha256": (
            "7df63fe892ac14382f226ea97dbd2ac186a8cb48213faec958ad32c51d51aeb5"
        ),
        "head_policy_sha256": (
            "a48aeb6ed7f2d64f46504158c96b6225cb60c3590182c71e069f3d26c94f4321"
        ),
        "base_prompt_sha256": (
            "83b45ad928a9bac3567dea786c4b48819400247e63c7210d8cb5d26e4750a52f"
        ),
        "head_prompt_sha256": (
            "503f997914734dbef8e0542efd1f3c495fa15a652782e15bf63638e35c841403"
        ),
    },
    {
        "prompt_path": "pdd/prompts/core/cli_python.prompt",
        "language_id": "python",
        "from_requirement_id": (
            "CONTRACT-SHA256:f1d49d5906b0a00226a0b33cf74be34ca4970efccc9531dbcd1b96c4b57e3724"
        ),
        "to_requirement_id": (
            "CONTRACT-SHA256:e01fb2968590ca4911044ef59f1091c2ea5de10b6257941078c63282c52e7d37"
        ),
        "policy_path": ".pdd/verification-profiles.json",
        "base_policy_sha256": (
            "7df63fe892ac14382f226ea97dbd2ac186a8cb48213faec958ad32c51d51aeb5"
        ),
        "head_policy_sha256": (
            "a48aeb6ed7f2d64f46504158c96b6225cb60c3590182c71e069f3d26c94f4321"
        ),
        "base_prompt_sha256": (
            "f1d49d5906b0a00226a0b33cf74be34ca4970efccc9531dbcd1b96c4b57e3724"
        ),
        "head_prompt_sha256": (
            "e01fb2968590ca4911044ef59f1091c2ea5de10b6257941078c63282c52e7d37"
        ),
    },
)
ESTIMATE_PROMPT_REPLACEMENTS = {
    "pdd/prompts/commands/generate_python.prompt": (
        b"Call `code_generator_main` with parsed options.",
        b"Resolve `pdd.code_generator_main.code_generator_main` inside each command "
        b"invocation and call it with parsed options. Do not cache or expose a mutable "
        b"wrapper-module alias: repeated and concurrent in-process CLI runs must always "
        b"use the canonical source dependency, so scoped test patches cannot leak through "
        b"a stale `pdd.commands.generate` module identity.",
    ),
    "pdd/prompts/core/cli_python.prompt": (
        b"The result callback still renders the human estimate table. "
        b"`--estimate-json` additionally treats the payload as quiet machine output.",
        b"The result callback still renders the human estimate table. "
        b"`--estimate-json` additionally treats the payload as quiet machine output. "
        b"If estimate JSON was requested but no estimate record was collected, write a "
        b"useful diagnostic to stderr and exit nonzero; never report success with empty "
        b"stdout.",
    ),
}
def _estimate_target_bytes() -> tuple[dict[str, bytes], bytes]:
    """Derive the reviewed #2058 prompt and profile bytes from this exact base."""
    prompts: dict[str, bytes] = {}
    for prompt_path, (old, new) in ESTIMATE_PROMPT_REPLACEMENTS.items():
        raw = (ROOT / prompt_path).read_bytes()
        assert raw.count(old) == 1
        prompts[prompt_path] = raw.replace(old, new)

    profile = json.loads(PROFILE_FILE.read_text(encoding="utf-8"))
    targets = {
        row["prompt_path"]: row
        for row in profile["profiles"]
        if row["prompt_path"] in prompts
    }
    assert set(targets) == set(prompts)
    for prompt_path, row in targets.items():
        requirement = f"CONTRACT-SHA256:{hashlib.sha256(prompts[prompt_path]).hexdigest()}"
        row["required_requirement_ids"] = [requirement]
        human = [
            item
            for item in row["obligations"]
            if item["obligation_id"] == "threshold-human-attestation"
        ]
        assert len(human) == 1
        human[0]["requirement_ids"] = [requirement]
    return prompts, (json.dumps(profile, indent=2) + "\n").encode()


def _estimate_transition_read(
    monkeypatch,
    *,
    head_profile: bytes,
    head_prompts: dict[str, bytes],
    base_rotation: bytes | None = None,
    head_rotation: bytes | None = None,
) -> None:
    """Install exact protected/candidate bytes for one rollout-policy check."""
    current_rotation = ROTATION_FILE.read_bytes()

    def transition_read(_root: Path, ref: str, path: PurePosixPath) -> bytes | None:
        if path == PROFILE_REL_PATH:
            return PROFILE_FILE.read_bytes() if ref == "protected-base" else head_profile
        if path == verification.ROTATION_POLICY_PATH:
            return (
                current_rotation if base_rotation is None else base_rotation
            ) if ref == "protected-base" else (
                current_rotation if head_rotation is None else head_rotation
            )
        prompt_path = path.as_posix()
        if ref == "candidate-head" and prompt_path in head_prompts:
            return head_prompts[prompt_path]
        resolved = ROOT / path
        return resolved.read_bytes() if resolved.is_file() else None

    monkeypatch.setattr(verification, "read_git_blob", transition_read)


def _estimate_inputs(raw: bytes):
    """Parse only the two exact profile rows exercised by this rollout."""
    paths = {item["prompt_path"] for item in ESTIMATE_REQUIREMENT_ROTATIONS}
    rows = json.loads(raw)["profiles"]
    return {
        UnitId(REPOSITORY_ID, PurePosixPath(row["prompt_path"]), row["language_id"]): (
            verification._ProfileInput(  # pylint: disable=protected-access
                tuple(sorted(row["required_requirement_ids"])),
                tuple(
                    sorted(
                        verification._obligation(item)  # pylint: disable=protected-access
                        for item in row["obligations"]
                    )
                ),
            )
        )
        for row in rows
        if row["prompt_path"] in paths
    }


def _estimate_updates(monkeypatch, head_profile, head_prompts, head_rotation=None):
    """Evaluate exact transition authority without loading the 466-unit denominator."""
    _estimate_transition_read(
        monkeypatch,
        head_profile=head_profile,
        head_prompts=head_prompts,
        head_rotation=head_rotation,
    )
    manifest = SimpleNamespace(
        repository_id=REPOSITORY_ID,
        base_ref="protected-base",
        head_ref="candidate-head",
    )
    authorizations = verification._load_requirement_transition_authorizations(  # pylint: disable=protected-access
        ROOT, manifest
    )
    updates, invalid = verification._authorized_requirement_updates(  # pylint: disable=protected-access
        ROOT,
        manifest,
        _estimate_inputs(PROFILE_FILE.read_bytes()),
        _estimate_inputs(head_profile),
        authorizations,
    )
    return authorizations, updates, invalid
def test_estimate_contract_rotations_are_exact_and_dormant(monkeypatch) -> None:
    """Preauthorize only the two reviewed #2058 prompt/profile transitions."""
    policy = json.loads(ROTATION_FILE.read_text(encoding="utf-8"))
    estimate_paths = {item["prompt_path"] for item in ESTIMATE_REQUIREMENT_ROTATIONS}
    rules = [
        row
        for row in policy["requirement_rotations"]
        if row["prompt_path"] in estimate_paths
    ]
    assert rules == list(ESTIMATE_REQUIREMENT_ROTATIONS)

    target_prompts, target_profile = _estimate_target_bytes()
    assert hashlib.sha256(PROFILE_FILE.read_bytes()).hexdigest() == (
        ESTIMATE_REQUIREMENT_ROTATIONS[0]["base_policy_sha256"]
    )
    assert hashlib.sha256(target_profile).hexdigest() == (
        ESTIMATE_REQUIREMENT_ROTATIONS[0]["head_policy_sha256"]
    )
    for rule in ESTIMATE_REQUIREMENT_ROTATIONS:
        prompt_path = rule["prompt_path"]
        assert hashlib.sha256((ROOT / prompt_path).read_bytes()).hexdigest() == (
            rule["base_prompt_sha256"]
        )
        assert hashlib.sha256(target_prompts[prompt_path]).hexdigest() == (
            rule["head_prompt_sha256"]
        )

    current_inputs = _estimate_inputs(PROFILE_FILE.read_bytes())
    assert len(current_inputs) == 2
    assert {
        item.requirements[0] for item in current_inputs.values()
    } == {item["from_requirement_id"] for item in ESTIMATE_REQUIREMENT_ROTATIONS}
    current_prompts = {
        item["prompt_path"]: (ROOT / item["prompt_path"]).read_bytes()
        for item in ESTIMATE_REQUIREMENT_ROTATIONS
    }
    _authorizations, updates, invalid = _estimate_updates(
        monkeypatch, PROFILE_FILE.read_bytes(), current_prompts
    )
    assert not invalid
    assert not updates


def test_estimate_contract_rotations_are_consumed_simultaneously(
    monkeypatch,
) -> None:
    """The #2058 target consumes both rows as one exact profile-file change."""
    target_prompts, target_profile = _estimate_target_bytes()
    _authorizations, updates, invalid = _estimate_updates(
        monkeypatch, target_profile, target_prompts
    )
    assert not invalid
    assert len(updates) == 2
    for rule in ESTIMATE_REQUIREMENT_ROTATIONS:
        unit_id = UnitId(
            REPOSITORY_ID, PurePosixPath(rule["prompt_path"]), rule["language_id"]
        )
        assert updates[unit_id].requirements == (rule["to_requirement_id"],)


@pytest.mark.parametrize(
    "substitution",
    (
        "candidate-only-extra",
        "partial",
        "wrong-prompt-binding",
        "wrong-policy-binding",
        "cross-unit",
        "validator-remap",
        "denominator-reduction",
        "protected-control-deletion",
    ),
)
def test_estimate_contract_rotations_reject_substitution(
    monkeypatch, substitution: str
) -> None:
    """Exact repository bootstrap authority cannot be split or repurposed."""
    # pylint: disable=too-many-branches,too-many-locals
    target_prompts, target_profile = _estimate_target_bytes()
    base_rotation = ROTATION_FILE.read_bytes()
    head_rotation = base_rotation
    profile = json.loads(target_profile)

    if substitution == "partial":
        cli_path = ESTIMATE_REQUIREMENT_ROTATIONS[1]["prompt_path"]
        target_prompts.pop(cli_path)
        base_profile = json.loads(PROFILE_FILE.read_text(encoding="utf-8"))
        base_cli = next(
            row for row in base_profile["profiles"] if row["prompt_path"] == cli_path
        )
        index = next(
            index
            for index, row in enumerate(profile["profiles"])
            if row["prompt_path"] == cli_path
        )
        profile["profiles"][index] = base_cli
        target_profile = (json.dumps(profile, indent=2) + "\n").encode()
    elif substitution == "validator-remap":
        row = next(
            row
            for row in profile["profiles"]
            if row["prompt_path"] == ESTIMATE_REQUIREMENT_ROTATIONS[0]["prompt_path"]
        )
        row["obligations"][0]["validator_id"] = "candidate-validator"
        target_profile = (json.dumps(profile, indent=2) + "\n").encode()
    elif substitution == "denominator-reduction":
        profile["profiles"] = [
            row
            for row in profile["profiles"]
            if row["prompt_path"] != ESTIMATE_REQUIREMENT_ROTATIONS[1]["prompt_path"]
        ]
        target_profile = (json.dumps(profile, indent=2) + "\n").encode()
    else:
        policy = json.loads(head_rotation)
        rules = policy["requirement_rotations"]
        estimate = [
            row
            for row in rules
            if row["prompt_path"]
            in {item["prompt_path"] for item in ESTIMATE_REQUIREMENT_ROTATIONS}
        ]
        if substitution == "candidate-only-extra":
            extra = dict(estimate[0])
            extra["prompt_path"] = "pdd/prompts/commands/test_python.prompt"
            rules.append(extra)
        elif substitution == "wrong-prompt-binding":
            estimate[0]["head_prompt_sha256"] = "0" * 64
        elif substitution == "wrong-policy-binding":
            estimate[0]["head_policy_sha256"] = "0" * 64
        elif substitution == "cross-unit":
            estimate[0]["prompt_path"] = estimate[1]["prompt_path"]
        elif substitution == "protected-control-deletion":
            policy["requirement_rotations"] = [
                row for row in rules if row not in estimate
            ]
        head_rotation = (json.dumps(policy, indent=2) + "\n").encode()

    if substitution in {
        "candidate-only-extra",
        "wrong-prompt-binding",
        "wrong-policy-binding",
        "cross-unit",
    }:
        _estimate_transition_read(
            monkeypatch,
            head_profile=target_profile,
            head_prompts=target_prompts,
            base_rotation=base_rotation,
            head_rotation=head_rotation,
        )
        manifest = SimpleNamespace(
            repository_id=REPOSITORY_ID,
            base_ref="protected-base",
            head_ref="candidate-head",
        )
        with pytest.raises(
            verification.VerificationProfileError,
            match=(
                "candidate requirement transition "
                "(?:lacks protected authorization|rules are duplicated or ambiguous)"
            ),
        ):
            verification._load_requirement_transition_authorizations(  # pylint: disable=protected-access
                ROOT, manifest
            )
        return

    _authorizations, updates, invalid = _estimate_updates(
        monkeypatch, target_profile, target_prompts, head_rotation
    )
    if substitution in {"protected-control-deletion", "denominator-reduction"}:
        assert len(updates) < 2
    else:
        assert invalid
        assert len(updates) < 2
