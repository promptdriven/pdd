"""Tests for protected base/head verification-profile authority."""

import json
import hashlib
import subprocess
from pathlib import Path, PurePosixPath
from types import SimpleNamespace

import pytest

from pdd.sync_core import build_unit_manifest, load_verification_profiles, verification
from pdd.sync_core.identity import initialize_repository_identity
from pdd.sync_core.types import UnitId
from pdd.sync_core.verification import PROFILE_PATH as PROFILE_REL_PATH
from pdd.sync_core.verification import VerificationProfileError


REPOSITORY_ID = "3b4d7b1c-d6cc-4752-ba93-6b98d1a710e0"
ROOT = Path(__file__).resolve().parents[1]
PROFILE_FILE = ROOT / PROFILE_REL_PATH
ROTATION_FILE = ROOT / ".pdd" / "verification-profile-rotations.json"


def _git(root: Path, *args: str) -> str:
    return subprocess.run(
        ["git", *args], cwd=root, capture_output=True, text=True, check=True
    ).stdout.strip()


def _commit(root: Path, message: str) -> str:
    _git(root, "add", ".")
    _git(root, "commit", "-q", "-m", message)
    return _git(root, "rev-parse", "HEAD")


def _profile(requirements=None, obligations=None):
    return {
        "profiles": [
            {
                "prompt_path": "prompts/widget_python.prompt",
                "language_id": "python",
                "required_requirement_ids": (
                    ["REQ-1"] if requirements is None else requirements
                ),
                "obligations": (
                    [
                        {
                            "obligation_id": "pytest",
                            "kind": "test",
                            "validator_id": "pytest",
                            "validator_config_digest": "pytest-v1",
                            "requirement_ids": ["REQ-1"],
                            "artifact_paths": ["tests/test_widget.py"],
                            "required": True,
                        }
                    ]
                    if obligations is None
                    else obligations
                ),
            }
        ]
    }


def _human_profile(root: Path, config_digest: str) -> dict:
    """Build an opaque-contract profile protected by human attestation."""
    prompt_path = root / "prompts/widget_python.prompt"
    requirement = (
        f"CONTRACT-SHA256:{hashlib.sha256(prompt_path.read_bytes()).hexdigest()}"
    )
    return {
        "profiles": [
            {
                "prompt_path": "prompts/widget_python.prompt",
                "language_id": "python",
                "required_requirement_ids": [requirement],
                "obligations": [
                    {
                        "obligation_id": "threshold-human-attestation",
                        "kind": "human-attestation",
                        "validator_id": "threshold-ed25519",
                        "validator_config_digest": config_digest,
                        "requirement_ids": [requirement],
                        "artifact_paths": ["prompts/widget_python.prompt"],
                        "required": True,
                    }
                ],
            }
        ]
    }


def _human_row(prompt_path: str, prompt_bytes: bytes) -> dict:
    """Build one opaque-contract profile row for multi-unit rotation tests."""
    requirement = f"CONTRACT-SHA256:{hashlib.sha256(prompt_bytes).hexdigest()}"
    return {
        "prompt_path": prompt_path,
        "language_id": "python",
        "required_requirement_ids": [requirement],
        "obligations": [
            {
                "obligation_id": "threshold-human-attestation",
                "kind": "human-attestation",
                "validator_id": "threshold-ed25519",
                "validator_config_digest": "threshold-ed25519-v1",
                "requirement_ids": [requirement],
                "artifact_paths": [prompt_path],
                "required": True,
            }
        ],
    }


def _requirement_rule(
    prompt_path: str,
    base_prompt: bytes,
    head_prompt: bytes,
    base_profile: bytes,
    head_profile: bytes,
) -> dict:
    """Bind one requirement transition to exact prompt and profile bytes."""
    base_digest = hashlib.sha256(base_prompt).hexdigest()
    head_digest = hashlib.sha256(head_prompt).hexdigest()
    return {
        "prompt_path": prompt_path,
        "language_id": "python",
        "from_requirement_id": f"CONTRACT-SHA256:{base_digest}",
        "to_requirement_id": f"CONTRACT-SHA256:{head_digest}",
        "policy_path": ".pdd/verification-profiles.json",
        "base_policy_sha256": hashlib.sha256(base_profile).hexdigest(),
        "head_policy_sha256": hashlib.sha256(head_profile).hexdigest(),
        "base_prompt_sha256": base_digest,
        "head_prompt_sha256": head_digest,
    }


def _rotation_authorization() -> dict:
    """Authorize the one future protected trust-policy transition."""
    return {
        "schema_version": 1,
        "rotations": [
            {
                "obligation_id": "threshold-human-attestation",
                "validator_id": "threshold-ed25519",
                "from_config_digest": "threshold-ed25519-v1",
                "policy_path": ".pdd/attestation-trust.json",
            }
        ],
    }


def _requirement_transition(
    root: Path, target_prompt: str, candidate_profile: dict | None = None
) -> tuple[dict, dict]:
    """Preauthorize one future exact opaque prompt/profile transition."""
    prompt_path = root / "prompts/widget_python.prompt"
    profile_path = root / ".pdd/verification-profiles.json"
    base_prompt = prompt_path.read_bytes()
    base_profile = profile_path.read_bytes()
    head_prompt = target_prompt.encode()
    requirement = f"CONTRACT-SHA256:{hashlib.sha256(head_prompt).hexdigest()}"
    if candidate_profile is None:
        candidate_profile = json.loads(profile_path.read_text())
        candidate_profile["profiles"][0]["required_requirement_ids"] = [requirement]
        candidate_profile["profiles"][0]["obligations"][0]["requirement_ids"] = [
            requirement
        ]
    head_profile = json.dumps(candidate_profile).encode()
    policy = {
        "schema_version": 2,
        "rotations": _rotation_authorization()["rotations"],
        "requirement_rotations": [
            {
                "prompt_path": "prompts/widget_python.prompt",
                "language_id": "python",
                "from_requirement_id": (
                    f"CONTRACT-SHA256:{hashlib.sha256(base_prompt).hexdigest()}"
                ),
                "to_requirement_id": requirement,
                "policy_path": ".pdd/verification-profiles.json",
                "base_policy_sha256": hashlib.sha256(base_profile).hexdigest(),
                "head_policy_sha256": hashlib.sha256(head_profile).hexdigest(),
                "base_prompt_sha256": hashlib.sha256(base_prompt).hexdigest(),
                "head_prompt_sha256": hashlib.sha256(head_prompt).hexdigest(),
            }
        ],
    }
    return policy, candidate_profile


def _repository(tmp_path: Path) -> Path:
    root = tmp_path / "repo"
    root.mkdir()
    _git(root, "init", "-q")
    _git(root, "config", "user.email", "profiles@example.com")
    _git(root, "config", "user.name", "Profiles Test")
    initialize_repository_identity(root, REPOSITORY_ID)
    (root / "prompts").mkdir()
    (root / "prompts/widget_python.prompt").write_text("REQ-1: Build widget\n")
    return root


def _manifest(root: Path, base: str, head: str):
    return build_unit_manifest(root, base_ref=base, head_ref=head)


def test_complete_protected_profile_has_full_coverage(tmp_path) -> None:
    """A complete protected profile covers its full requirement universe."""
    root = _repository(tmp_path)
    (root / ".pdd/verification-profiles.json").write_text(json.dumps(_profile()))
    commit = _commit(root, "profile")
    profiles = load_verification_profiles(root, _manifest(root, commit, commit))
    assert profiles.coverage == 1.0
    assert not profiles.invalid_reasons


def test_missing_profile_is_explicit_and_incomplete(tmp_path) -> None:
    """A missing profile fails explicitly with zero coverage."""
    root = _repository(tmp_path)
    commit = _commit(root, "no profile")
    profiles = load_verification_profiles(root, _manifest(root, commit, commit))
    assert profiles.coverage == 0.0
    assert any("profile is missing" in item for item in profiles.invalid_reasons)
    assert profiles.profiles[0].complete is False


def test_candidate_cannot_delete_protected_obligation(tmp_path) -> None:
    """Candidate policy cannot remove an obligation from the protected base."""
    root = _repository(tmp_path)
    profile_path = root / ".pdd/verification-profiles.json"
    profile_path.write_text(json.dumps(_profile()))
    base = _commit(root, "base profile")
    profile_path.write_text(json.dumps(_profile(obligations=[])))
    head = _commit(root, "delete obligation")
    profiles = load_verification_profiles(root, _manifest(root, base, head))
    effective = profiles.profiles[0]
    assert [item.obligation_id for item in effective.obligations] == ["pytest"]
    assert any(
        "removed protected obligation" in item for item in profiles.invalid_reasons
    )


def test_candidate_cannot_remap_protected_validator(tmp_path) -> None:
    """Candidate policy cannot remap a protected validator."""
    root = _repository(tmp_path)
    profile_path = root / ".pdd/verification-profiles.json"
    profile_path.write_text(json.dumps(_profile()))
    base = _commit(root, "base profile")
    changed = _profile()
    changed["profiles"][0]["obligations"][0]["validator_id"] = "candidate-validator"
    profile_path.write_text(json.dumps(changed))
    head = _commit(root, "remap validator")
    profiles = load_verification_profiles(root, _manifest(root, base, head))
    assert profiles.profiles[0].obligations[0].validator_id == "pytest"
    assert any(
        "changed protected obligation" in item for item in profiles.invalid_reasons
    )


def test_protected_authorization_rotates_human_policy_digest(tmp_path) -> None:
    """A protected rule can atomically bind the future trust-policy bytes."""
    root = _repository(tmp_path)
    prompt = root / "prompts/widget_python.prompt"
    prompt.write_text("Opaque contract\n")
    profile_path = root / ".pdd/verification-profiles.json"
    profile_path.write_text(json.dumps(_human_profile(root, "threshold-ed25519-v1")))
    rotation_path = root / ".pdd/verification-profile-rotations.json"
    rotation_path.write_text(json.dumps(_rotation_authorization()))
    base = _commit(root, "authorize policy rotation")

    trust_policy = (
        b'{"issuers":[{"issuer_id":"trusted-ci","public_key":"'
        b"YWFhYWFhYWFhYWFhYWFhYWFhYWFhYWFhYWFhYWFhYWE="
        b'"}]}'
    )
    # The rotation binds profile configuration to exact candidate policy bytes.
    (root / ".pdd/attestation-trust.json").write_bytes(trust_policy)
    final_digest = hashlib.sha256(trust_policy).hexdigest()
    profile_path.write_text(json.dumps(_human_profile(root, final_digest)))
    head = _commit(root, "install policy and restamp profile")

    profiles = load_verification_profiles(root, _manifest(root, base, head))
    assert not profiles.invalid_reasons
    obligation = profiles.profiles[0].obligations[0]
    assert obligation.validator_config_digest == final_digest


def test_policy_rotation_rejects_arbitrary_human_config_digest(tmp_path) -> None:
    """Protected rotation authority cannot be used to restamp arbitrary bytes."""
    root = _repository(tmp_path)
    prompt = root / "prompts/widget_python.prompt"
    prompt.write_text("Opaque contract\n")
    profile_path = root / ".pdd/verification-profiles.json"
    profile_path.write_text(json.dumps(_human_profile(root, "threshold-ed25519-v1")))
    rotation_path = root / ".pdd/verification-profile-rotations.json"
    rotation_path.write_text(json.dumps(_rotation_authorization()))
    base = _commit(root, "authorize policy rotation")

    (root / ".pdd/attestation-trust.json").write_text('{"issuers":[]}')
    profile_path.write_text(json.dumps(_human_profile(root, "arbitrary-config-digest")))
    head = _commit(root, "attempt arbitrary restamp")

    profiles = load_verification_profiles(root, _manifest(root, base, head))
    assert profiles.profiles[0].obligations[0].validator_config_digest == (
        "threshold-ed25519-v1"
    )
    assert any(
        "changed protected obligation" in item for item in profiles.invalid_reasons
    )


def test_protected_requirement_transition_is_valid_while_dormant(tmp_path) -> None:
    """Protected future authority must not invalidate unchanged protected bytes."""
    root = _repository(tmp_path)
    prompt = root / "prompts/widget_python.prompt"
    prompt.write_text("Opaque contract version one\n")
    profile_path = root / ".pdd/verification-profiles.json"
    profile_path.write_text(json.dumps(_human_profile(root, "threshold-ed25519-v1")))
    policy, _candidate_profile = _requirement_transition(
        root, "Opaque contract version two\n"
    )
    (root / ".pdd/verification-profile-rotations.json").write_text(json.dumps(policy))
    protected = _commit(root, "preauthorize future transition")

    profiles = load_verification_profiles(root, _manifest(root, protected, protected))

    assert not profiles.invalid_reasons
    assert profiles.coverage == 1.0


def test_exact_requirement_transition_updates_human_mapping(tmp_path) -> None:
    """Exact Git-bound prompt and human requirement replacement is accepted."""
    root = _repository(tmp_path)
    prompt = root / "prompts/widget_python.prompt"
    prompt.write_text("Opaque contract version one\n")
    profile_path = root / ".pdd/verification-profiles.json"
    profile_path.write_text(json.dumps(_human_profile(root, "threshold-ed25519-v1")))
    policy, candidate_profile = _requirement_transition(
        root, "Opaque contract version two\n"
    )
    (root / ".pdd/verification-profile-rotations.json").write_text(json.dumps(policy))
    base = _commit(root, "protected transition authority")

    prompt.write_text("Opaque contract version two\n")
    profile_path.write_text(json.dumps(candidate_profile))
    head = _commit(root, "consume exact transition")

    profiles = load_verification_profiles(root, _manifest(root, base, head))
    requirement = f"CONTRACT-SHA256:{hashlib.sha256(prompt.read_bytes()).hexdigest()}"
    assert not profiles.invalid_reasons
    assert profiles.coverage == 1.0
    assert profiles.profiles[0].required_requirement_ids == (requirement,)
    assert profiles.profiles[0].obligations[0].requirement_ids == (requirement,)


def test_dormant_requirement_transition_survives_unrelated_exact_transition(
    tmp_path,
) -> None:
    """A future row stays dormant while a sibling consumes its exact rule."""
    # pylint: disable=too-many-locals
    root = _repository(tmp_path)
    widget_path = "prompts/widget_python.prompt"
    gadget_path = "prompts/gadget_python.prompt"
    widget_v1 = b"Opaque widget contract version one\n"
    widget_v2 = b"Opaque widget contract version two\n"
    gadget_v1 = b"Opaque gadget contract version one\n"
    gadget_v2 = b"Opaque gadget contract version two\n"
    (root / widget_path).write_bytes(widget_v1)
    (root / gadget_path).write_bytes(gadget_v1)

    profile_path = root / ".pdd/verification-profiles.json"
    profile_v0 = {
        "profiles": [
            _human_row(widget_path, widget_v1),
            _human_row(gadget_path, gadget_v1),
        ]
    }
    profile_v1 = {
        "profiles": [
            _human_row(widget_path, widget_v1),
            _human_row(gadget_path, gadget_v2),
        ]
    }
    profile_v2 = {
        "profiles": [
            _human_row(widget_path, widget_v2),
            _human_row(gadget_path, gadget_v2),
        ]
    }
    profile_bytes = [
        json.dumps(item).encode() for item in (profile_v0, profile_v1, profile_v2)
    ]
    profile_path.write_bytes(profile_bytes[0])
    policy = {
        "schema_version": 2,
        "rotations": _rotation_authorization()["rotations"],
        "requirement_rotations": [
            _requirement_rule(
                gadget_path, gadget_v1, gadget_v2, profile_bytes[0], profile_bytes[1]
            ),
            _requirement_rule(
                widget_path, widget_v1, widget_v2, profile_bytes[1], profile_bytes[2]
            ),
        ],
    }
    (root / ".pdd/verification-profile-rotations.json").write_text(json.dumps(policy))
    base = _commit(root, "preauthorize staggered exact transitions")

    (root / gadget_path).write_bytes(gadget_v2)
    profile_path.write_bytes(profile_bytes[1])
    head = _commit(root, "consume gadget transition only")

    profiles = load_verification_profiles(root, _manifest(root, base, head))
    assert not profiles.invalid_reasons
    assert profiles.coverage == 1.0


@pytest.mark.parametrize("substitution", ["removed-requirement", "cross-profile"])
def test_exact_requirement_transition_rejects_profile_substitution(
    tmp_path, substitution
) -> None:
    """Exact file digests cannot authorize a partial or cross-unit remap."""
    # pylint: disable=too-many-locals
    root = _repository(tmp_path)
    widget_path = "prompts/widget_python.prompt"
    gadget_path = "prompts/gadget_python.prompt"
    widget_v1 = b"Opaque widget contract version one\n"
    widget_v2 = b"Opaque widget contract version two\n"
    gadget = b"Opaque gadget contract\n"
    (root / widget_path).write_bytes(widget_v1)
    (root / gadget_path).write_bytes(gadget)
    profile_path = root / ".pdd/verification-profiles.json"
    base_profile = {
        "profiles": [
            _human_row(widget_path, widget_v1),
            _human_row(gadget_path, gadget),
        ]
    }
    candidate_profile = json.loads(json.dumps(base_profile))
    target_requirement = f"CONTRACT-SHA256:{hashlib.sha256(widget_v2).hexdigest()}"
    target = candidate_profile["profiles"][
        0 if substitution == "removed-requirement" else 1
    ]
    target["required_requirement_ids"] = (
        [] if substitution == "removed-requirement" else [target_requirement]
    )
    target["obligations"][0]["requirement_ids"] = target["required_requirement_ids"]
    base_bytes = json.dumps(base_profile).encode()
    candidate_bytes = json.dumps(candidate_profile).encode()
    profile_path.write_bytes(base_bytes)
    policy = {
        "schema_version": 2,
        "rotations": _rotation_authorization()["rotations"],
        "requirement_rotations": [
            _requirement_rule(
                widget_path, widget_v1, widget_v2, base_bytes, candidate_bytes
            )
        ],
    }
    (root / ".pdd/verification-profile-rotations.json").write_text(json.dumps(policy))
    base = _commit(root, "authorize exact widget transition")

    (root / widget_path).write_bytes(widget_v2)
    profile_path.write_bytes(candidate_bytes)
    head = _commit(root, f"attempt {substitution}")

    profiles = load_verification_profiles(root, _manifest(root, base, head))
    assert any(
        marker in reason
        for reason in profiles.invalid_reasons
        for marker in (
            "requirement transition is partial or mismatched",
            "candidate removed protected requirements",
        )
    )


def test_candidate_cannot_add_its_own_requirement_authorization(tmp_path) -> None:
    """Exact candidate bytes still lack authority without a protected rule."""
    root = _repository(tmp_path)
    prompt = root / "prompts/widget_python.prompt"
    prompt.write_text("Opaque contract version one\n")
    profile_path = root / ".pdd/verification-profiles.json"
    profile_path.write_text(json.dumps(_human_profile(root, "threshold-ed25519-v1")))
    policy, candidate_profile = _requirement_transition(
        root, "Opaque contract version two\n"
    )
    base = _commit(root, "protected profile without transition authority")

    prompt.write_text("Opaque contract version two\n")
    profile_path.write_text(json.dumps(candidate_profile))
    (root / ".pdd/verification-profile-rotations.json").write_text(json.dumps(policy))
    head = _commit(root, "candidate self-authorization attempt")

    with pytest.raises(
        VerificationProfileError,
        match="candidate requirement transition lacks protected authorization",
    ):
        load_verification_profiles(root, _manifest(root, base, head))


def test_requirement_transition_rejects_wrong_bound_prompt(tmp_path) -> None:
    """Protected authority cannot cover bytes outside its exact four digests."""
    root = _repository(tmp_path)
    prompt = root / "prompts/widget_python.prompt"
    prompt.write_text("Opaque contract version one\n")
    profile_path = root / ".pdd/verification-profiles.json"
    profile_path.write_text(json.dumps(_human_profile(root, "threshold-ed25519-v1")))
    policy, candidate_profile = _requirement_transition(
        root, "Opaque contract version two\n"
    )
    policy["requirement_rotations"][0]["base_prompt_sha256"] = "0" * 64
    (root / ".pdd/verification-profile-rotations.json").write_text(json.dumps(policy))
    base = _commit(root, "protected mismatched transition")

    prompt.write_text("Opaque contract version two\n")
    profile_path.write_text(json.dumps(candidate_profile))
    head = _commit(root, "attempt mismatched transition")

    profiles = load_verification_profiles(root, _manifest(root, base, head))
    assert profiles.coverage == 0.0
    assert any("bindings mismatch" in item for item in profiles.invalid_reasons)


def test_exact_requirement_transition_cannot_remap_validator(tmp_path) -> None:
    """Exact byte bindings permit only the human requirement-ID replacement."""
    root = _repository(tmp_path)
    prompt = root / "prompts/widget_python.prompt"
    prompt.write_text("Opaque contract version one\n")
    profile_path = root / ".pdd/verification-profiles.json"
    profile_path.write_text(json.dumps(_human_profile(root, "threshold-ed25519-v1")))
    changed = json.loads(profile_path.read_text())
    target_prompt = "Opaque contract version two\n"
    target_requirement = (
        f"CONTRACT-SHA256:{hashlib.sha256(target_prompt.encode()).hexdigest()}"
    )
    changed["profiles"][0]["required_requirement_ids"] = [target_requirement]
    changed["profiles"][0]["obligations"][0]["requirement_ids"] = [target_requirement]
    changed["profiles"][0]["obligations"][0]["validator_id"] = "candidate-validator"
    policy, changed = _requirement_transition(root, target_prompt, changed)
    (root / ".pdd/verification-profile-rotations.json").write_text(json.dumps(policy))
    base = _commit(root, "protected exact transition")

    prompt.write_text(target_prompt)
    profile_path.write_text(json.dumps(changed))
    head = _commit(root, "attempt validator remap")

    profiles = load_verification_profiles(root, _manifest(root, base, head))
    assert profiles.coverage == 0.0
    assert any(
        "requirement transition changes protected fields" in item
        for item in profiles.invalid_reasons
    )
    assert profiles.profiles[0].obligations[0].validator_id == "threshold-ed25519"


def test_profile_digest_binds_declared_code_under_test(tmp_path) -> None:
    """The profile identity must bind its explicit product-code assignment."""
    root = _repository(tmp_path)
    first = _profile()
    first["profiles"][0]["obligations"][0]["code_under_test_paths"] = [
        "pdd/sync_core/descriptor_store.py"
    ]
    profile_path = root / ".pdd/verification-profiles.json"
    profile_path.write_text(json.dumps(first))
    first_commit = _commit(root, "first protected code assignment")
    first_digest = (
        load_verification_profiles(root, _manifest(root, first_commit, first_commit))
        .profiles[0]
        .profile_digest
    )

    second = _profile()
    second["profiles"][0]["obligations"][0]["code_under_test_paths"] = [
        "pdd/sync_core/supervisor.py"
    ]
    profile_path.write_text(json.dumps(second))
    second_commit = _commit(root, "second protected code assignment")
    second_digest = (
        load_verification_profiles(root, _manifest(root, second_commit, second_commit))
        .profiles[0]
        .profile_digest
    )

    assert first_digest != second_digest


def test_new_requirement_without_mapping_is_incomplete(tmp_path) -> None:
    """An unmapped new requirement leaves the candidate incomplete."""
    root = _repository(tmp_path)
    profile_path = root / ".pdd/verification-profiles.json"
    profile_path.write_text(json.dumps(_profile()))
    base = _commit(root, "base profile")
    (root / "prompts/widget_python.prompt").write_text(
        "REQ-1: Build widget\nREQ-2: Reject invalid input\n"
    )
    profile_path.write_text(json.dumps(_profile(requirements=["REQ-1", "REQ-2"])))
    head = _commit(root, "new unmapped requirement")
    profiles = load_verification_profiles(root, _manifest(root, base, head))
    assert profiles.coverage == 0.0
    assert any("profile is incomplete" in item for item in profiles.invalid_reasons)


def test_profile_cannot_invent_smaller_requirement_universe(tmp_path) -> None:
    """Profile requirements cannot shrink the prompt requirement universe."""
    root = _repository(tmp_path)
    (root / "prompts/widget_python.prompt").write_text(
        "REQ-1: Build widget\nREQ-2: Reject invalid input\n"
    )
    profile_path = root / ".pdd/verification-profiles.json"
    profile_path.write_text(json.dumps(_profile(requirements=["REQ-1"])))
    commit = _commit(root, "dishonest profile")
    profiles = load_verification_profiles(root, _manifest(root, commit, commit))
    assert any(
        "do not match immutable prompt requirements" in item
        for item in profiles.invalid_reasons
    )
    assert profiles.coverage == 0.0


def test_prompt_without_explicit_ids_requires_human_attestation(tmp_path) -> None:
    """Opaque prompt contracts require human attestation."""
    root = _repository(tmp_path)
    prompt = root / "prompts/widget_python.prompt"
    prompt.write_text("Build a widget with validated input.\n")
    digest = hashlib.sha256(prompt.read_bytes()).hexdigest()
    profile = _profile(requirements=[f"CONTRACT-SHA256:{digest}"])
    profile["profiles"][0]["obligations"][0]["requirement_ids"] = [
        f"CONTRACT-SHA256:{digest}"
    ]
    (root / ".pdd/verification-profiles.json").write_text(json.dumps(profile))
    commit = _commit(root, "contract digest")
    profiles = load_verification_profiles(root, _manifest(root, commit, commit))
    assert any("profile is incomplete" in item for item in profiles.invalid_reasons)
    assert profiles.coverage == 0.0


def test_candidate_only_profile_cannot_approve_itself(tmp_path) -> None:
    """A candidate-only profile cannot establish its own authority."""
    root = _repository(tmp_path)
    base = _commit(root, "unprofiled base")
    (root / ".pdd/verification-profiles.json").write_text(json.dumps(_profile()))
    head = _commit(root, "candidate profile")
    profiles = load_verification_profiles(root, _manifest(root, base, head))
    assert profiles.coverage == 0.0
    assert any("lacks protected approval" in item for item in profiles.invalid_reasons)


def test_profile_digest_binds_code_under_test_role_policy(tmp_path) -> None:
    """Profile identity binds the code-under-test role assignment."""
    root = _repository(tmp_path)
    profile_path = root / ".pdd/verification-profiles.json"
    support = _profile()
    profile_path.write_text(json.dumps(support))
    base = _commit(root, "support role")
    support_digest = (
        load_verification_profiles(root, _manifest(root, base, base))
        .profiles[0]
        .profile_digest
    )

    product = _profile()
    product["profiles"][0]["obligations"][0]["code_under_test_paths"] = [
        "src/widget.py"
    ]
    (root / "src").mkdir()
    (root / "src/widget.py").write_text("VALUE = 1\n")
    profile_path.write_text(json.dumps(product))
    head = _commit(root, "product role")
    product_digest = (
        load_verification_profiles(root, _manifest(root, head, head))
        .profiles[0]
        .profile_digest
    )
    assert support_digest != product_digest


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
            "71b12a08e5be55b958a737decde889c189f7ca00ceaddccd7b587f9c8b2a4b64"
        ),
        "head_policy_sha256": (
            "1b4641d57921012a4aa7c507bb38b31c29dcc8ad23b370f0c4b979d8ff0a5d18"
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
            "71b12a08e5be55b958a737decde889c189f7ca00ceaddccd7b587f9c8b2a4b64"
        ),
        "head_policy_sha256": (
            "1b4641d57921012a4aa7c507bb38b31c29dcc8ad23b370f0c4b979d8ff0a5d18"
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
        requirement = (
            f"CONTRACT-SHA256:{hashlib.sha256(prompts[prompt_path]).hexdigest()}"
        )
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
            return (
                PROFILE_FILE.read_bytes() if ref == "protected-base" else head_profile
            )
        if path == verification.ROTATION_POLICY_PATH:
            return (
                (current_rotation if base_rotation is None else base_rotation)
                if ref == "protected-base"
                else (current_rotation if head_rotation is None else head_rotation)
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

    target_prompts, _target_profile = _estimate_target_bytes()
    for rule in ESTIMATE_REQUIREMENT_ROTATIONS:
        prompt_path = rule["prompt_path"]
        assert (
            hashlib.sha256((ROOT / prompt_path).read_bytes()).hexdigest()
            == (rule["base_prompt_sha256"])
        )
        assert (
            hashlib.sha256(target_prompts[prompt_path]).hexdigest()
            == (rule["head_prompt_sha256"])
        )

    current_inputs = _estimate_inputs(PROFILE_FILE.read_bytes())
    assert len(current_inputs) == 2
    assert {item.requirements[0] for item in current_inputs.values()} == {
        item["from_requirement_id"] for item in ESTIMATE_REQUIREMENT_ROTATIONS
    }
    current_prompts = {
        item["prompt_path"]: (ROOT / item["prompt_path"]).read_bytes()
        for item in ESTIMATE_REQUIREMENT_ROTATIONS
    }
    _authorizations, updates, invalid = _estimate_updates(
        monkeypatch, PROFILE_FILE.read_bytes(), current_prompts
    )
    assert not invalid
    assert not updates


def test_estimate_contract_rotations_share_one_exact_profile_transition(
) -> None:
    """Both #2058 rows share one profile binding and exact replacements."""
    target_prompts, target_profile = _estimate_target_bytes()
    protected = _estimate_inputs(PROFILE_FILE.read_bytes())
    candidate = _estimate_inputs(target_profile)
    authorizations = {
        item.prompt_path.as_posix(): item
        for item in verification._parse_requirement_transition_authorizations(  # pylint: disable=protected-access
            ROTATION_FILE.read_bytes(), "protected"
        )
    }
    for rule in ESTIMATE_REQUIREMENT_ROTATIONS:
        unit_id = UnitId(
            REPOSITORY_ID, PurePosixPath(rule["prompt_path"]), rule["language_id"]
        )
        authorization = authorizations[rule["prompt_path"]]
        assert hashlib.sha256(target_prompts[rule["prompt_path"]]).hexdigest() == (
            authorization.bindings.head_prompt_sha256
        )
        update, reason = verification._expected_requirement_update(  # pylint: disable=protected-access
            authorization, protected[unit_id], candidate[unit_id]
        )
        assert reason is None
        assert update is not None
        assert update.requirements == (rule["to_requirement_id"],)


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
