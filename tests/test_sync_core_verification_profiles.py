"""Tests for protected base/head verification-profile authority."""

# This intentionally grouped profile-authority matrix exceeds Pylint's module
# line threshold.
# pylint: disable=too-many-lines

import base64
import hashlib
import json
import subprocess
import zlib
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
    requirement = f"CONTRACT-SHA256:{hashlib.sha256(prompt_path.read_bytes()).hexdigest()}"
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
    assert any("removed protected obligation" in item for item in profiles.invalid_reasons)

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
    assert any("changed protected obligation" in item for item in profiles.invalid_reasons)


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
    assert any("changed protected obligation" in item for item in profiles.invalid_reasons)


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
    target_requirement = f"CONTRACT-SHA256:{hashlib.sha256(target_prompt.encode()).hexdigest()}"
    changed["profiles"][0]["required_requirement_ids"] = [target_requirement]
    changed["profiles"][0]["obligations"][0]["requirement_ids"] = [
        target_requirement
    ]
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
    first_digest = load_verification_profiles(
        root, _manifest(root, first_commit, first_commit)
    ).profiles[0].profile_digest

    second = _profile()
    second["profiles"][0]["obligations"][0]["code_under_test_paths"] = [
        "pdd/sync_core/supervisor.py"
    ]
    profile_path.write_text(json.dumps(second))
    second_commit = _commit(root, "second protected code assignment")
    second_digest = load_verification_profiles(
        root, _manifest(root, second_commit, second_commit)
    ).profiles[0].profile_digest

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
    support_digest = load_verification_profiles(
        root, _manifest(root, base, base)
    ).profiles[0].profile_digest

    product = _profile()
    product["profiles"][0]["obligations"][0]["code_under_test_paths"] = ["src/widget.py"]
    (root / "src").mkdir()
    (root / "src/widget.py").write_text("VALUE = 1\n")
    profile_path.write_text(json.dumps(product))
    head = _commit(root, "product role")
    product_digest = load_verification_profiles(
        root, _manifest(root, head, head)
    ).profiles[0].profile_digest
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

_HISTORICAL_FIXTURE_MAX_ENCODED_BYTES = 65_536
_HISTORICAL_FIXTURE_MAX_COMPRESSED_BYTES = 49_152
_HISTORICAL_FIXTURE_MAX_DECOMPRESSED_BYTES = 524_288

# Archive-safe exact bytes for the protected #2058 base.  The payloads are
# zlib-compressed Base64 text so source archives need neither Git history nor a
# local object database to exercise the same 7df63fe... -> a48aeb6... rollout.
ESTIMATE_HISTORICAL_BASE_FIXTURES = {
    '.pdd/verification-profiles.json': {
        "size": 365026,
        "sha256": "7df63fe892ac14382f226ea97dbd2ac186a8cb48213faec958ad32c51d51aeb5",
        "zlib_base64": (
            "eNrsvV1vZbmxJfg+v8Lw83VfBoNkkP3W6Jd56J4BZvptMDgIRgQrD6yUNPpIV92L/u8TVGaVyy4ps+4Wa+9sYBfssnR0lD65"
            "uFZ8bMbHv/9vf/rTnx/lg33kyyd7eLze3f75P/8J/mW+fP9wN6439ugv/D/+/Z/+9O8v//78k4/3T5d7fvrgP/zzveq/fn7p"
            "8V//O//V5m9dPn754j99/smf/+XnX77h2x+e+Qe7XHX+8s/v+/sbHuz/e74+mF6+fPHRbp/8zX//HC/v+q//5//xP/6v//Jf"
            "/8df/u///b/EXP5zyU1TrYO4jcBSULFYL6E0ChIjp46xQsyhhRKQQWLqTSlzFKhc8c9f/uj/95fPcddvrj/wk0Pyj//X//7L"
            "V//wpi9/n6cPD/b44e5G//Lh+SPf/oWfnuzx6eUdv/wVX37zr9fbl1/4xts+8c1V+enu4Td/vmnMGdpbb5e723H94aLXH/wP"
            "fvU3//IJ/vGXvwb4Hwr6PwD/8v/ED0/XwfKZZK98kt/FuTf/9J8p5n/u08Oz/fKj//kzCV7+93/+y++m/eWv9tPD9faHy9P1"
            "o909+5t+evpwd/st8n9+13upL6CFNXeNhFVTaIlIAlhmGq2zNgc+Vy1RuIxOGiL46y0JBqXe+0n9DdRfBfr7qP8N3u0nAOf0"
            "7dNVLvwgHy6PT3YPwY/h4/2NPdmtPT5e/tt/++/fUsPNzcf3SkHd6IQhqQgxVAk9ch6JLDaBRjlhoCqkJLGSDItcGkQs6iZM"
            "ckE7pbBBCqtAf58U/iMMPFIXcHn86VZ20sMo0YjSUGW1UTNWHDlYSykMwggpJg4MhrkQUwH/GWFn5CI2sJ562KKHVaCv1sNv"
            "mXekDuJF7X4vvwAWsoYsgbPFGKtiaz0V6qHxiCV6HBuTaXeLFXKNGkuG2NmNWaMEo5w62KCDVaCv1sFvmXekDvAyrj/uJIPc"
            "BmUCjOooe56G1ClZCK276amWsRlIytZjrdVj1jG65JwqhhxHHXrKYIMMVoG+Wga/Id6RKrjwLd/89G92uX/QvXwCCGAOBMDJ"
            "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"
            "paT/L/O7//+//F/WcF0s"
        ),
    },
    'pdd/prompts/commands/generate_python.prompt': {
        "size": 11327,
        "sha256": "83b45ad928a9bac3567dea786c4b48819400247e63c7210d8cb5d26e4750a52f",
        "zlib_base64": (
            "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"
            "c7x/Bn29e+HjuDf/C1QaxG8="
        ),
    },
    'pdd/prompts/core/cli_python.prompt': {
        "size": 12595,
        "sha256": "f1d49d5906b0a00226a0b33cf74be34ca4970efccc9531dbcd1b96c4b57e3724",
        "zlib_base64": (
            "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"
            "W/qfBnq+jR0JmE5OChMj2Lsye/QPpmJa4w=="
        ),
    },
}
EstimateState = tuple[bytes, dict[str, bytes]]


def _historical_bytes(path: str) -> bytes:
    """Decode one bounded, hash-verified historical fixture without Git."""
    fixture = ESTIMATE_HISTORICAL_BASE_FIXTURES.get(path)
    if fixture is None:
        raise AssertionError(f"missing historical fixture for {path}")
    expected_size = fixture["size"]
    expected_hash = fixture["sha256"]
    encoded = "".join(fixture["zlib_base64"])
    if (
        not isinstance(expected_size, int)
        or expected_size < 0
        or expected_size > _HISTORICAL_FIXTURE_MAX_DECOMPRESSED_BYTES
        or not isinstance(expected_hash, str)
        or len(expected_hash) != 64
        or len(encoded) > _HISTORICAL_FIXTURE_MAX_ENCODED_BYTES
    ):
        raise AssertionError(f"historical fixture bounds are invalid for {path}")
    try:
        compressed = base64.b64decode(encoded, validate=True)
    except (ValueError, TypeError) as exc:
        raise AssertionError(f"historical fixture is not Base64 for {path}") from exc
    if len(compressed) > _HISTORICAL_FIXTURE_MAX_COMPRESSED_BYTES:
        raise AssertionError(f"historical fixture compressed bytes exceed limit: {path}")
    decompressor = zlib.decompressobj()
    raw = decompressor.decompress(compressed, expected_size + 1)
    if (
        len(raw) != expected_size
        or not decompressor.eof
        or decompressor.unconsumed_tail
        or decompressor.unused_data
    ):
        raise AssertionError(f"historical fixture decompression is invalid for {path}")
    actual_hash = hashlib.sha256(raw).hexdigest()
    if actual_hash != expected_hash:
        raise AssertionError(f"historical fixture hash mismatch for {path}")
    return raw


def _estimate_historical_base_bytes() -> EstimateState:
    """Load the exact protected prompt/profile bytes bound by #2058."""

    return (
        _historical_bytes(PROFILE_REL_PATH.as_posix()),
        {
            item["prompt_path"]: _historical_bytes(item["prompt_path"])
            for item in ESTIMATE_REQUIREMENT_ROTATIONS
        },
    )


def test_estimate_historical_fixture_is_git_independent(monkeypatch) -> None:
    """The archived #2058 base remains exact without a Git object database."""
    def no_history(*_args, **_kwargs):
        raise AssertionError("historical fixture must not invoke Git")

    monkeypatch.setattr(subprocess, "check_output", no_history)
    profile, prompts = _estimate_historical_base_bytes()

    assert hashlib.sha256(profile).hexdigest() == (
        ESTIMATE_REQUIREMENT_ROTATIONS[0]["base_policy_sha256"]
    )
    assert set(prompts) == {
        item["prompt_path"] for item in ESTIMATE_REQUIREMENT_ROTATIONS
    }
    for rule in ESTIMATE_REQUIREMENT_ROTATIONS:
        assert hashlib.sha256(prompts[rule["prompt_path"]]).hexdigest() == (
            rule["base_prompt_sha256"]
        )


def _estimate_target_bytes(base: EstimateState) -> EstimateState:
    """Derive the reviewed #2058 prompt and profile bytes from this exact base."""
    base_profile, base_prompts = base
    prompts: dict[str, bytes] = {}
    for prompt_path, (old, new) in ESTIMATE_PROMPT_REPLACEMENTS.items():
        raw = base_prompts[prompt_path]
        assert raw.count(old) == 1
        prompts[prompt_path] = raw.replace(old, new)

    profile = json.loads(base_profile)
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
    return (json.dumps(profile, indent=2) + "\n").encode(), prompts


def _estimate_transition_read(
    monkeypatch,
    base: EstimateState,
    head: EstimateState,
    base_rotation: bytes | None = None,
    head_rotation: bytes | None = None,
) -> None:
    """Install exact protected/candidate bytes for one rollout-policy check."""
    base_profile, base_prompts = base
    head_profile, head_prompts = head
    current_rotation = ROTATION_FILE.read_bytes()

    def transition_read(_root: Path, ref: str, path: PurePosixPath) -> bytes | None:
        if path == PROFILE_REL_PATH:
            return base_profile if ref == "protected-base" else head_profile
        if path == verification.ROTATION_POLICY_PATH:
            return (
                current_rotation if base_rotation is None else base_rotation
            ) if ref == "protected-base" else (
                current_rotation if head_rotation is None else head_rotation
            )
        prompt_path = path.as_posix()
        if ref == "protected-base" and prompt_path in base_prompts:
            return base_prompts[prompt_path]
        if ref == "candidate-head" and prompt_path in head_prompts:
            return head_prompts[prompt_path]
        resolved = ROOT / path
        return resolved.read_bytes() if resolved.is_file() else None

    monkeypatch.setattr(verification, "read_git_blob", transition_read)
    monkeypatch.setattr(
        verification,
        "read_git_blob_bounded",
        lambda root, ref, path, _max_bytes: transition_read(root, ref, path),
    )


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


def _estimate_updates(
    monkeypatch,
    base: EstimateState,
    head: EstimateState,
    head_rotation: bytes | None = None,
):
    """Evaluate exact transition authority without loading the 466-unit denominator."""
    _estimate_transition_read(
        monkeypatch,
        base,
        head,
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
        _estimate_inputs(base[0]),
        _estimate_inputs(head[0]),
        authorizations,
    )
    return authorizations, updates, invalid


def test_estimate_contract_rotations_are_exact_and_dormant(monkeypatch) -> None:
    """Keep both exact #2058 endpoints dormant after later policy rotations."""
    policy = json.loads(ROTATION_FILE.read_text(encoding="utf-8"))
    estimate_paths = {item["prompt_path"] for item in ESTIMATE_REQUIREMENT_ROTATIONS}
    rules = [
        row
        for row in policy["requirement_rotations"]
        if row["prompt_path"] in estimate_paths
    ]
    assert rules == list(ESTIMATE_REQUIREMENT_ROTATIONS)

    base = _estimate_historical_base_bytes()
    target = _estimate_target_bytes(base)
    assert hashlib.sha256(base[0]).hexdigest() == (
        ESTIMATE_REQUIREMENT_ROTATIONS[0]["base_policy_sha256"]
    )
    assert hashlib.sha256(target[0]).hexdigest() == (
        ESTIMATE_REQUIREMENT_ROTATIONS[0]["head_policy_sha256"]
    )
    for rule in ESTIMATE_REQUIREMENT_ROTATIONS:
        prompt_path = rule["prompt_path"]
        assert hashlib.sha256(base[1][prompt_path]).hexdigest() == (
            rule["base_prompt_sha256"]
        )
        assert hashlib.sha256(target[1][prompt_path]).hexdigest() == (
            rule["head_prompt_sha256"]
        )

    base_inputs = _estimate_inputs(base[0])
    assert len(base_inputs) == 2
    assert {
        item.requirements[0] for item in base_inputs.values()
    } == {item["from_requirement_id"] for item in ESTIMATE_REQUIREMENT_ROTATIONS}
    for stationary in (base, target):
        _authorizations, updates, invalid = _estimate_updates(
            monkeypatch, stationary, stationary
        )
        assert not invalid
        assert not updates


def test_estimate_contract_rotations_are_consumed_simultaneously(
    monkeypatch,
) -> None:
    """The #2058 target consumes both rows as one exact profile-file change."""
    base = _estimate_historical_base_bytes()
    target = _estimate_target_bytes(base)
    _authorizations, updates, invalid = _estimate_updates(
        monkeypatch,
        base,
        target,
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
    base = _estimate_historical_base_bytes()
    target_profile, target_prompts = _estimate_target_bytes(base)
    base_rotation = ROTATION_FILE.read_bytes()
    head_rotation = base_rotation
    profile = json.loads(target_profile)

    if substitution == "partial":
        cli_path = ESTIMATE_REQUIREMENT_ROTATIONS[1]["prompt_path"]
        target_prompts.pop(cli_path)
        base_profile_rows = json.loads(base[0])
        base_cli = next(
            row
            for row in base_profile_rows["profiles"]
            if row["prompt_path"] == cli_path
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
            base,
            (target_profile, target_prompts),
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
        monkeypatch,
        base,
        (target_profile, target_prompts),
        head_rotation=head_rotation,
    )
    if substitution in {"protected-control-deletion", "denominator-reduction"}:
        assert len(updates) < 2
    else:
        assert invalid
        assert len(updates) < 2
