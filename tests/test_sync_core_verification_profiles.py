"""Tests for protected base/head verification-profile authority."""

import json
import hashlib
import subprocess
from pathlib import Path

from pdd.sync_core import build_unit_manifest, load_verification_profiles
from pdd.sync_core.identity import initialize_repository_identity


REPOSITORY_ID = "3b4d7b1c-d6cc-4752-ba93-6b98d1a710e0"


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


def _requirement_rotation_authorization(
    base_profile: bytes,
    head_profile: bytes,
    from_requirement: str,
    to_requirement: str,
) -> dict:
    """Authorize one exact, byte-bound human contract replacement."""
    return {
        "schema_version": 2,
        "rotations": _rotation_authorization()["rotations"],
        "requirement_rotations": [
            {
                "prompt_path": "prompts/widget_python.prompt",
                "language_id": "python",
                "from_requirement_id": from_requirement,
                "to_requirement_id": to_requirement,
                "policy_path": ".pdd/verification-profiles.json",
                "from_policy_sha256": hashlib.sha256(base_profile).hexdigest(),
                "to_policy_sha256": hashlib.sha256(head_profile).hexdigest(),
            }
        ],
    }


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
    root = _repository(tmp_path)
    (root / ".pdd/verification-profiles.json").write_text(json.dumps(_profile()))
    commit = _commit(root, "profile")
    profiles = load_verification_profiles(root, _manifest(root, commit, commit))
    assert profiles.coverage == 1.0
    assert not profiles.invalid_reasons


def test_missing_profile_is_explicit_and_incomplete(tmp_path) -> None:
    root = _repository(tmp_path)
    commit = _commit(root, "no profile")
    profiles = load_verification_profiles(root, _manifest(root, commit, commit))
    assert profiles.coverage == 0.0
    assert any("profile is missing" in item for item in profiles.invalid_reasons)
    assert profiles.profiles[0].complete is False


def test_candidate_cannot_delete_protected_obligation(tmp_path) -> None:
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


def test_protected_authorization_rotates_human_contract_requirement(tmp_path) -> None:
    """A schema-2 rule replaces only its declared profile contract bytes."""
    root = _repository(tmp_path)
    prompt = root / "prompts/widget_python.prompt"
    prompt.write_text("Opaque base contract\n")
    profile_path = root / ".pdd/verification-profiles.json"
    base_profile = _human_profile(root, "threshold-ed25519-v1")
    base_bytes = json.dumps(base_profile).encode()
    from_requirement = base_profile["profiles"][0]["required_requirement_ids"][0]

    prompt.write_text("Opaque replacement contract\n")
    head_profile = _human_profile(root, "threshold-ed25519-v1")
    head_bytes = json.dumps(head_profile).encode()
    to_requirement = head_profile["profiles"][0]["required_requirement_ids"][0]

    prompt.write_text("Opaque base contract\n")
    profile_path.write_bytes(base_bytes)
    rotation_path = root / ".pdd/verification-profile-rotations.json"
    rotation_path.write_text(
        json.dumps(
            _requirement_rotation_authorization(
                base_bytes, head_bytes, from_requirement, to_requirement
            )
        )
    )
    base = _commit(root, "authorize exact contract replacement")

    prompt.write_text("Opaque replacement contract\n")
    profile_path.write_bytes(head_bytes)
    head = _commit(root, "replace contract")

    profiles = load_verification_profiles(root, _manifest(root, base, head))
    assert not profiles.invalid_reasons
    obligation = profiles.profiles[0].obligations[0]
    assert profiles.profiles[0].required_requirement_ids == (to_requirement,)
    assert obligation.requirement_ids == (to_requirement,)


def test_requirement_rotation_rejects_other_candidate_profile_bytes(tmp_path) -> None:
    """A candidate cannot reuse a rule whose target profile bytes differ."""
    root = _repository(tmp_path)
    prompt = root / "prompts/widget_python.prompt"
    prompt.write_text("Opaque base contract\n")
    profile_path = root / ".pdd/verification-profiles.json"
    base_profile = _human_profile(root, "threshold-ed25519-v1")
    base_bytes = json.dumps(base_profile).encode()
    from_requirement = base_profile["profiles"][0]["required_requirement_ids"][0]

    prompt.write_text("Authorized replacement contract\n")
    authorized_profile = _human_profile(root, "threshold-ed25519-v1")
    authorized_bytes = json.dumps(authorized_profile).encode()
    to_requirement = authorized_profile["profiles"][0]["required_requirement_ids"][0]

    prompt.write_text("Opaque base contract\n")
    profile_path.write_bytes(base_bytes)
    rotation_path = root / ".pdd/verification-profile-rotations.json"
    rotation_path.write_text(
        json.dumps(
            _requirement_rotation_authorization(
                base_bytes, authorized_bytes, from_requirement, to_requirement
            )
        )
    )
    base = _commit(root, "authorize one exact replacement")

    prompt.write_text("Different replacement contract\n")
    profile_path.write_text(json.dumps(_human_profile(root, "threshold-ed25519-v1")))
    head = _commit(root, "attempt another replacement")

    profiles = load_verification_profiles(root, _manifest(root, base, head))
    assert any(
        "candidate removed protected requirements" in item
        for item in profiles.invalid_reasons
    )


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
    root = _repository(tmp_path)
    base = _commit(root, "unprofiled base")
    (root / ".pdd/verification-profiles.json").write_text(json.dumps(_profile()))
    head = _commit(root, "candidate profile")
    profiles = load_verification_profiles(root, _manifest(root, base, head))
    assert profiles.coverage == 0.0
    assert any("lacks protected approval" in item for item in profiles.invalid_reasons)


def test_profile_digest_binds_code_under_test_role_policy(tmp_path) -> None:
    root = _repository(tmp_path)
    profile_path = root / ".pdd/verification-profiles.json"
    support = _profile()
    profile_path.write_text(json.dumps(support))
    base = _commit(root, "support role")
    support_digest = load_verification_profiles(root, _manifest(root, base, base)).profiles[0].profile_digest

    product = _profile()
    product["profiles"][0]["obligations"][0]["code_under_test_paths"] = ["src/widget.py"]
    (root / "src").mkdir()
    (root / "src/widget.py").write_text("VALUE = 1\n")
    profile_path.write_text(json.dumps(product))
    head = _commit(root, "product role")
    product_digest = load_verification_profiles(root, _manifest(root, head, head)).profiles[0].profile_digest
    assert support_digest != product_digest
