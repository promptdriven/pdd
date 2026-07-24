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


def _empty_requirement_policy() -> dict:
    """Build the protected schema-2 envelope before future rows are installed."""
    return {
        "schema_version": 2,
        "rotations": _rotation_authorization()["rotations"],
        "requirement_rotations": [],
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


def test_candidate_can_install_strictly_dormant_requirement_authorization(
    tmp_path,
) -> None:
    """A candidate may install exact future authority without consuming it."""
    root = _repository(tmp_path)
    prompt = root / "prompts/widget_python.prompt"
    prompt.write_text("Opaque contract version one\n")
    profile_path = root / ".pdd/verification-profiles.json"
    profile_path.write_text(json.dumps(_human_profile(root, "threshold-ed25519-v1")))
    policy, _candidate_profile = _requirement_transition(
        root, "Opaque contract version two\n"
    )
    rotation_path = root / ".pdd/verification-profile-rotations.json"
    rotation_path.write_text(json.dumps(_empty_requirement_policy()))
    base = _commit(root, "protected source bytes")

    rotation_path.write_text(json.dumps(policy))
    head = _commit(root, "install dormant transition authority")

    profiles = load_verification_profiles(root, _manifest(root, base, head))
    assert not profiles.invalid_reasons
    assert profiles.coverage == 1.0


def test_dormant_schema_2_admission_rejects_unrelated_managed_prompt_drift(
    tmp_path,
) -> None:
    """Ordinary Phase A cannot carry explicit-REQ drift in another managed prompt."""
    root = _repository(tmp_path)
    prompt = root / "prompts/widget_python.prompt"
    prompt.write_text("Opaque contract version one\n")
    other_path = "prompts/other_python.prompt"
    other = root / other_path
    other.write_text("REQ-OTHER: Protected requirement\n")
    profile_path = root / ".pdd/verification-profiles.json"
    profile = _human_profile(root, "threshold-ed25519-v1")
    other_row = _human_row(other_path, other.read_bytes())
    other_row["required_requirement_ids"] = ["REQ-OTHER"]
    other_row["obligations"][0]["requirement_ids"] = ["REQ-OTHER"]
    profile["profiles"].append(other_row)
    profile_path.write_text(json.dumps(profile))
    policy, _candidate_profile = _requirement_transition(
        root, "Opaque contract version two\n"
    )
    rotation_path = root / ".pdd/verification-profile-rotations.json"
    rotation_path.write_text(json.dumps(_empty_requirement_policy()))
    base = _commit(root, "protect ordinary Phase A source")

    other.write_text("REQ-OTHER: Drift without identifier change\n")
    rotation_path.write_text(json.dumps(policy))
    head = _commit(root, "install authority with unrelated prompt drift")

    with pytest.raises(VerificationProfileError, match="authority-only change"):
        load_verification_profiles(root, _manifest(root, base, head))


@pytest.mark.parametrize(
    "mutation",
    [
        "remove-rotations",
        "replace-rotations",
        "malformed-rotation",
        "schema-substitution",
        "envelope-substitution",
    ],
)
def test_candidate_dormant_authorization_preserves_policy_envelope(
    tmp_path, mutation
) -> None:
    """Installing future rows cannot replace the protected authority envelope."""
    root = _repository(tmp_path)
    prompt = root / "prompts/widget_python.prompt"
    prompt.write_text("Opaque contract version one\n")
    profile_path = root / ".pdd/verification-profiles.json"
    profile_path.write_text(json.dumps(_human_profile(root, "threshold-ed25519-v1")))
    policy, _candidate_profile = _requirement_transition(
        root, "Opaque contract version two\n"
    )
    rotation_path = root / ".pdd/verification-profile-rotations.json"
    rotation_path.write_text(json.dumps(_empty_requirement_policy()))
    base = _commit(root, "protected policy envelope")

    if mutation == "remove-rotations":
        policy["rotations"] = []
    elif mutation == "replace-rotations":
        policy["rotations"][0]["validator_id"] = "candidate-validator"
    elif mutation == "malformed-rotation":
        policy["rotations"] = [{"obligation_id": "threshold-human-attestation"}]
    elif mutation == "schema-substitution":
        policy["schema_version"] = 1
    else:
        policy["candidate_authority"] = []
    rotation_path.write_text(json.dumps(policy))
    head = _commit(root, f"attempt dormant install with {mutation}")

    with pytest.raises(VerificationProfileError, match="candidate"):
        load_verification_profiles(root, _manifest(root, base, head))


def test_candidate_can_replace_consumed_rule_with_next_dormant_authorization(
    tmp_path,
) -> None:
    """A consumed protected identity may advance to its next dormant transition."""
    root = _repository(tmp_path)
    prompt_path = "prompts/widget_python.prompt"
    prompt = root / prompt_path
    old_prompt = b"Opaque contract version zero\n"
    current_prompt = b"Opaque contract version one\n"
    future_prompt = b"Opaque contract version two\n"
    prompt.write_bytes(current_prompt)
    profile_path = root / ".pdd/verification-profiles.json"
    old_profile = json.dumps(
        {"profiles": [_human_row(prompt_path, old_prompt)]}
    ).encode()
    current_profile = json.dumps(
        {"profiles": [_human_row(prompt_path, current_prompt)]}
    ).encode()
    future_profile = json.dumps(
        {"profiles": [_human_row(prompt_path, future_prompt)]}
    ).encode()
    profile_path.write_bytes(current_profile)
    policy_path = root / ".pdd/verification-profile-rotations.json"
    policy_path.write_text(
        json.dumps(
            {
                "schema_version": 2,
                "rotations": _rotation_authorization()["rotations"],
                "requirement_rotations": [
                    _requirement_rule(
                        prompt_path,
                        old_prompt,
                        current_prompt,
                        old_profile,
                        current_profile,
                    )
                ],
            }
        )
    )
    base = _commit(root, "protected consumed transition")

    policy_path.write_text(
        json.dumps(
            {
                "schema_version": 2,
                "rotations": _rotation_authorization()["rotations"],
                "requirement_rotations": [
                    _requirement_rule(
                        prompt_path,
                        current_prompt,
                        future_prompt,
                        current_profile,
                        future_profile,
                    )
                ],
            }
        )
    )
    head = _commit(root, "replace consumed authority with next dormant rule")

    profiles = load_verification_profiles(root, _manifest(root, base, head))
    assert not profiles.invalid_reasons
    assert profiles.coverage == 1.0


def test_consumed_rule_replacement_preserves_surviving_protected_row(tmp_path) -> None:
    """A consumed row may be replaced only after exact surviving history."""
    root = _repository(tmp_path)
    widget_path = "prompts/widget_python.prompt"
    gadget_path = "prompts/gadget_python.prompt"
    widget_v0 = b"Widget contract version zero\n"
    widget_v1 = b"Widget contract version one\n"
    widget_v2 = b"Widget contract version two\n"
    gadget_v1 = b"Gadget contract version one\n"
    gadget_v2 = b"Gadget contract version two\n"
    (root / widget_path).write_bytes(widget_v1)
    (root / gadget_path).write_bytes(gadget_v1)
    profile_path = root / ".pdd/verification-profiles.json"
    old_profile = json.dumps(
        {
            "profiles": [
                _human_row(widget_path, widget_v0),
                _human_row(gadget_path, gadget_v1),
            ]
        }
    ).encode()
    current_profile = json.dumps(
        {
            "profiles": [
                _human_row(widget_path, widget_v1),
                _human_row(gadget_path, gadget_v1),
            ]
        }
    ).encode()
    widget_future_profile = json.dumps(
        {
            "profiles": [
                _human_row(widget_path, widget_v2),
                _human_row(gadget_path, gadget_v1),
            ]
        }
    ).encode()
    gadget_future_profile = json.dumps(
        {
            "profiles": [
                _human_row(widget_path, widget_v1),
                _human_row(gadget_path, gadget_v2),
            ]
        }
    ).encode()
    profile_path.write_bytes(current_profile)
    consumed = _requirement_rule(
        widget_path, widget_v0, widget_v1, old_profile, current_profile
    )
    surviving = _requirement_rule(
        gadget_path, gadget_v1, gadget_v2, current_profile, gadget_future_profile
    )
    replacement = _requirement_rule(
        widget_path, widget_v1, widget_v2, current_profile, widget_future_profile
    )
    policy_path = root / ".pdd/verification-profile-rotations.json"
    policy_path.write_text(
        json.dumps(
            {
                "schema_version": 2,
                "rotations": _rotation_authorization()["rotations"],
                "requirement_rotations": [consumed, surviving],
            }
        )
    )
    base = _commit(root, "protect consumed and surviving transitions")

    policy_path.write_text(
        json.dumps(
            {
                "schema_version": 2,
                "rotations": _rotation_authorization()["rotations"],
                "requirement_rotations": [surviving, replacement],
            }
        )
    )
    head = _commit(root, "replace consumed transition after surviving history")

    profiles = load_verification_profiles(root, _manifest(root, base, head))
    assert not profiles.invalid_reasons
    assert profiles.coverage == 1.0


def test_dormant_schema_2_admission_rejects_prepend_before_protected_row(
    tmp_path,
) -> None:
    """Phase A additions follow exact protected row history."""
    root = _repository(tmp_path)
    widget_path = "prompts/widget_python.prompt"
    gadget_path = "prompts/gadget_python.prompt"
    widget_v1 = b"Widget contract version one\n"
    widget_v2 = b"Widget contract version two\n"
    gadget_v1 = b"Gadget contract version one\n"
    gadget_v2 = b"Gadget contract version two\n"
    (root / widget_path).write_bytes(widget_v1)
    (root / gadget_path).write_bytes(gadget_v1)
    profile_path = root / ".pdd/verification-profiles.json"
    current_profile = json.dumps(
        {
            "profiles": [
                _human_row(widget_path, widget_v1),
                _human_row(gadget_path, gadget_v1),
            ]
        }
    ).encode()
    widget_future_profile = json.dumps(
        {
            "profiles": [
                _human_row(widget_path, widget_v2),
                _human_row(gadget_path, gadget_v1),
            ]
        }
    ).encode()
    gadget_future_profile = json.dumps(
        {
            "profiles": [
                _human_row(widget_path, widget_v1),
                _human_row(gadget_path, gadget_v2),
            ]
        }
    ).encode()
    profile_path.write_bytes(current_profile)
    protected = _requirement_rule(
        widget_path, widget_v1, widget_v2, current_profile, widget_future_profile
    )
    addition = _requirement_rule(
        gadget_path, gadget_v1, gadget_v2, current_profile, gadget_future_profile
    )
    policy_path = root / ".pdd/verification-profile-rotations.json"
    policy_path.write_text(
        json.dumps(
            {
                "schema_version": 2,
                "rotations": _rotation_authorization()["rotations"],
                "requirement_rotations": [protected],
            }
        )
    )
    base = _commit(root, "protect existing transition history")

    policy_path.write_text(
        json.dumps(
            {
                "schema_version": 2,
                "rotations": _rotation_authorization()["rotations"],
                "requirement_rotations": [addition, protected],
            }
        )
    )
    head = _commit(root, "prepend dormant transition")

    with pytest.raises(VerificationProfileError, match="protected representation"):
        load_verification_profiles(root, _manifest(root, base, head))


@pytest.mark.parametrize("mutation", ["key-order", "escaping", "path-lexeme"])
def test_dormant_schema_2_admission_rejects_protected_row_rewrite(
    tmp_path, mutation
) -> None:
    """Semantic equivalence cannot rewrite an unconsumed protected row token."""
    root = _repository(tmp_path)
    prompt_path = "prompts/widget_python.prompt"
    current_prompt = b"Opaque contract version one\n"
    future_prompt = b"Opaque contract version two\n"
    (root / prompt_path).write_bytes(current_prompt)
    profile_path = root / ".pdd/verification-profiles.json"
    current_profile = json.dumps(
        {"profiles": [_human_row(prompt_path, current_prompt)]}
    ).encode()
    future_profile = json.dumps(
        {"profiles": [_human_row(prompt_path, future_prompt)]}
    ).encode()
    profile_path.write_bytes(current_profile)
    row = _requirement_rule(
        prompt_path, current_prompt, future_prompt, current_profile, future_profile
    )
    policy_path = root / ".pdd/verification-profile-rotations.json"
    protected_policy = {
        "schema_version": 2,
        "rotations": _rotation_authorization()["rotations"],
        "requirement_rotations": [row],
    }
    policy_path.write_text(json.dumps(protected_policy))
    base = _commit(root, "protect exact row representation")

    rewritten = dict(reversed(tuple(row.items()))) if mutation == "key-order" else row
    candidate_raw = json.dumps(
        {
            "schema_version": 2,
            "rotations": _rotation_authorization()["rotations"],
            "requirement_rotations": [rewritten],
        }
    )
    if mutation == "escaping":
        candidate_raw = candidate_raw.replace(
            '"prompts/widget_python.prompt"', '"prompts\\/widget_python.prompt"'
        )
    elif mutation == "path-lexeme":
        candidate_raw = candidate_raw.replace(
            '"prompts/widget_python.prompt"', '"prompts//widget_python.prompt"'
        )
    policy_path.write_text(candidate_raw)
    head = _commit(root, f"rewrite protected row via {mutation}")

    with pytest.raises(VerificationProfileError, match="protected representation"):
        load_verification_profiles(root, _manifest(root, base, head))


@pytest.mark.parametrize("mutation", ["replace", "remove"])
def test_candidate_cannot_revoke_unconsumed_requirement_authorization(
    tmp_path, mutation
) -> None:
    """A candidate cannot revoke manager-reviewed authority before consumption."""
    root = _repository(tmp_path)
    prompt_path = "prompts/widget_python.prompt"
    current_prompt = b"Opaque contract version one\n"
    first_future_prompt = b"Opaque contract version two\n"
    replacement_future_prompt = b"Opaque contract version three\n"
    (root / prompt_path).write_bytes(current_prompt)
    profile_path = root / ".pdd/verification-profiles.json"
    current_profile = json.dumps(
        {"profiles": [_human_row(prompt_path, current_prompt)]}
    ).encode()
    first_future_profile = json.dumps(
        {"profiles": [_human_row(prompt_path, first_future_prompt)]}
    ).encode()
    replacement_future_profile = json.dumps(
        {"profiles": [_human_row(prompt_path, replacement_future_prompt)]}
    ).encode()
    profile_path.write_bytes(current_profile)
    policy_path = root / ".pdd/verification-profile-rotations.json"
    policy_path.write_text(
        json.dumps(
            {
                "schema_version": 2,
                "rotations": _rotation_authorization()["rotations"],
                "requirement_rotations": [
                    _requirement_rule(
                        prompt_path,
                        current_prompt,
                        first_future_prompt,
                        current_profile,
                        first_future_profile,
                    )
                ],
            }
        )
    )
    base = _commit(root, "protect unconsumed transition")

    replacement = (
        [
            _requirement_rule(
                prompt_path,
                current_prompt,
                replacement_future_prompt,
                current_profile,
                replacement_future_profile,
            )
        ]
        if mutation == "replace"
        else []
    )
    policy_path.write_text(
        json.dumps(
            {
                "schema_version": 2,
                "rotations": _rotation_authorization()["rotations"],
                "requirement_rotations": replacement,
            }
        )
    )
    head = _commit(root, f"attempt to {mutation} unconsumed authority")

    with pytest.raises(VerificationProfileError, match="unconsumed protected"):
        load_verification_profiles(root, _manifest(root, base, head))


def _stale_authority_sequence(
    tmp_path: Path,
    *,
    include_unrelated: bool = False,
    unrelated_alias: bool = False,
):
    """Build the #1790-first shape that leaves #2058 authority unreachable."""
    root = _repository(tmp_path)
    widget_path = "prompts/widget_python.prompt"
    gadget_path = "prompts/gadget_python.prompt"
    widget_v1, widget_v2, widget_v3 = (
        b"Widget contract version one\n",
        b"Widget contract version two\n",
        b"Widget contract version three\n",
    )
    gadget_v1, gadget_v2 = (
        b"Gadget contract version one\n",
        b"Gadget contract version two\n",
    )
    unrelated_path = "prompts/unrelated_python.prompt"
    unrelated_target = PurePosixPath("canonical-prompts/unrelated_python.prompt")
    unrelated_v1 = b"REQ-UNRELATED: Preserve this explicit requirement\n"
    (root / widget_path).write_bytes(widget_v1)
    (root / gadget_path).write_bytes(gadget_v1)
    if include_unrelated and unrelated_alias:
        target = root / unrelated_target
        target.parent.mkdir()
        target.write_bytes(unrelated_v1)
        (root / unrelated_path).symlink_to(
            "../canonical-prompts/unrelated_python.prompt"
        )
        (root / ".pdd/sync-aliases.json").write_text(
            json.dumps(
                {
                    "schema_version": 1,
                    "aliases": [
                        {
                            "alias_path": unrelated_path,
                            "canonical_path": unrelated_target.as_posix(),
                        }
                    ],
                }
            )
        )
    elif include_unrelated:
        (root / unrelated_path).write_bytes(unrelated_v1)
    profile_path = root / ".pdd/verification-profiles.json"
    unrelated_rows = []
    if include_unrelated:
        unrelated_row = _human_row(unrelated_path, unrelated_v1)
        unrelated_row["required_requirement_ids"] = ["REQ-UNRELATED"]
        unrelated_row["obligations"][0]["requirement_ids"] = ["REQ-UNRELATED"]
        unrelated_rows = [unrelated_row]
    profile_v0 = json.dumps(
        {
            "profiles": [
                _human_row(widget_path, widget_v1),
                _human_row(gadget_path, gadget_v1),
                *unrelated_rows,
            ]
        }
    ).encode()
    profile_v1 = json.dumps(
        {
            "profiles": [
                _human_row(widget_path, widget_v2),
                _human_row(gadget_path, gadget_v1),
                *unrelated_rows,
            ]
        }
    ).encode()
    profile_v2 = json.dumps(
        {
            "profiles": [
                _human_row(widget_path, widget_v1),
                _human_row(gadget_path, gadget_v2),
                *unrelated_rows,
            ]
        }
    ).encode()
    profile_v3 = json.dumps(
        {
            "profiles": [
                _human_row(widget_path, widget_v2),
                _human_row(gadget_path, gadget_v2),
                *unrelated_rows,
            ]
        }
    ).encode()
    profile_v4 = json.dumps(
        {
            "profiles": [
                _human_row(widget_path, widget_v3),
                _human_row(gadget_path, gadget_v1),
                *unrelated_rows,
            ]
        }
    ).encode()
    profile_path.write_bytes(profile_v0)
    first = _requirement_rule(widget_path, widget_v1, widget_v2, profile_v0, profile_v1)
    stale = _requirement_rule(gadget_path, gadget_v1, gadget_v2, profile_v0, profile_v2)
    policy_path = root / ".pdd/verification-profile-rotations.json"
    policy_path.write_text(
        json.dumps(
            {
                "schema_version": 2,
                "rotations": _rotation_authorization()["rotations"],
                "requirement_rotations": [first, stale],
            }
        )
    )
    authority_base = _commit(root, "protect #1790 and #2058 dormant authority")

    (root / widget_path).write_bytes(widget_v2)
    profile_path.write_bytes(profile_v1)
    stale_base = _commit(root, "consume #1790 first")
    replacement = _requirement_rule(
        gadget_path, gadget_v1, gadget_v2, profile_v1, profile_v3
    )
    next_widget = _requirement_rule(
        widget_path, widget_v2, widget_v3, profile_v1, profile_v4
    )
    return SimpleNamespace(
        root=root,
        authority_base=authority_base,
        stale_base=stale_base,
        policy_path=policy_path,
        profile_path=profile_path,
        first=first,
        stale=stale,
        replacement=replacement,
        next_widget=next_widget,
        profile_v0=profile_v0,
        profile_v1=profile_v1,
        profile_v3=profile_v3,
        widget_v1=widget_v1,
        gadget_v2=gadget_v2,
        unrelated_path=unrelated_path,
        unrelated_target=unrelated_target,
    )


def _retirement_policy(state, *, retirements=None, rows=None) -> dict:
    """Render one schema-3 append-only retirement candidate."""
    if rows is None:
        rows = [state.first, state.stale, state.replacement]
    if retirements is None:
        retirements = [{"obsolete": state.stale, "replacement": state.replacement}]
    return {
        "schema_version": 3,
        "rotations": _rotation_authorization()["rotations"],
        "requirement_rotations": rows,
        "requirement_rotation_retirements": retirements,
    }


def _empty_schema_3_policy(state, *, rows=None) -> dict:
    """Render an invalid schema-3 upgrade without a retirement/reissue record."""
    if rows is None:
        rows = [state.first, state.stale]
    return _retirement_policy(state, rows=rows, retirements=[])


def test_retire_unreachable_2058_authority_after_1790_consumes_first(tmp_path) -> None:
    """A protected stale row stays visible while fresh authority is reissued."""
    state = _stale_authority_sequence(tmp_path)
    state.policy_path.write_text(json.dumps(_retirement_policy(state)))
    reissue = _commit(state.root, "retire stale #2058 authority and reissue it")

    profiles = load_verification_profiles(
        state.root, _manifest(state.root, state.stale_base, reissue)
    )
    assert not profiles.invalid_reasons

    (state.root / "prompts/gadget_python.prompt").write_bytes(state.gadget_v2)
    state.profile_path.write_bytes(state.profile_v3)
    consumed = _commit(state.root, "consume fresh #2058 authority")
    profiles = load_verification_profiles(
        state.root, _manifest(state.root, reissue, consumed)
    )
    assert not profiles.invalid_reasons
    policy = json.loads(state.policy_path.read_text())
    assert policy["requirement_rotations"][:2] == [state.first, state.stale]
    assert policy["requirement_rotation_retirements"] == [
        {"obsolete": state.stale, "replacement": state.replacement}
    ]


def test_schema_3_upgrade_with_empty_retirements_rejects_rewritten_history(
    tmp_path,
) -> None:
    """A schema-3 upgrade cannot reformat a protected schema-2 authorization row."""
    state = _stale_authority_sequence(tmp_path)
    state.policy_path.write_text(
        json.dumps(
            _empty_schema_3_policy(
                state, rows=[dict(reversed(state.first.items())), state.stale]
            )
        )
    )
    candidate = _commit(state.root, "rewrite history during empty schema-3 upgrade")

    with pytest.raises(
        VerificationProfileError, match="rewrites protected representation"
    ):
        load_verification_profiles(
            state.root, _manifest(state.root, state.stale_base, candidate)
        )


def test_schema_3_upgrade_with_empty_retirements_is_rejected(tmp_path) -> None:
    """Schema 2 cannot enter schema 3 until it appends a valid retirement/reissue."""
    state = _stale_authority_sequence(tmp_path)
    state.policy_path.write_text(json.dumps(_empty_schema_3_policy(state)))
    candidate = _commit(state.root, "attempt empty schema-3 upgrade")

    with pytest.raises(VerificationProfileError, match="requires a retirement/reissue"):
        load_verification_profiles(
            state.root, _manifest(state.root, state.stale_base, candidate)
        )


def test_schema_3_history_rejects_rewrite_without_new_retirement(tmp_path) -> None:
    """Protected schema-3 rows stay token-identical in later stationary candidates."""
    state = _stale_authority_sequence(tmp_path)
    state.policy_path.write_text(json.dumps(_retirement_policy(state)))
    protected = _commit(state.root, "protect retirement history")
    policy = json.loads(state.policy_path.read_text())
    policy["requirement_rotations"][0] = dict(reversed(state.first.items()))
    state.policy_path.write_text(json.dumps(policy))
    candidate = _commit(state.root, "rewrite stationary schema-3 history")

    with pytest.raises(
        VerificationProfileError, match="rewrites protected representation"
    ):
        load_verification_profiles(
            state.root, _manifest(state.root, protected, candidate)
        )


def test_schema_3_phase_b_consumption_keeps_stationary_history(tmp_path) -> None:
    """A later Phase B still consumes the protected schema-3 replacement row."""
    state = _stale_authority_sequence(tmp_path)
    state.policy_path.write_text(json.dumps(_retirement_policy(state)))
    protected = _commit(state.root, "protect retirement history")

    (state.root / "prompts/gadget_python.prompt").write_bytes(state.gadget_v2)
    state.profile_path.write_bytes(state.profile_v3)
    candidate = _commit(state.root, "consume protected schema-3 authority")

    profiles = load_verification_profiles(
        state.root, _manifest(state.root, protected, candidate)
    )
    assert not profiles.invalid_reasons


@pytest.mark.parametrize("mutation", ["consume", "profile-bytes", "prompt-bytes"])
def test_retirement_reissue_rejects_same_candidate_byte_changes(
    tmp_path, mutation
) -> None:
    """Retirement Phase A cannot consume replacement authority or change bytes."""
    state = _stale_authority_sequence(tmp_path)
    if mutation == "consume":
        (state.root / "prompts/gadget_python.prompt").write_bytes(state.gadget_v2)
        state.profile_path.write_bytes(state.profile_v3)
    elif mutation == "profile-bytes":
        state.profile_path.write_bytes(
            json.dumps(json.loads(state.profile_v1), indent=2).encode()
        )
    else:
        (state.root / "prompts/gadget_python.prompt").write_text("unbound mutation\n")
    state.policy_path.write_text(json.dumps(_retirement_policy(state)))
    candidate = _commit(state.root, f"invalid retirement {mutation}")

    with pytest.raises(VerificationProfileError, match="candidate retirement"):
        load_verification_profiles(
            state.root, _manifest(state.root, state.stale_base, candidate)
        )


def test_retirement_reissue_rejects_unrelated_managed_prompt_byte_drift(
    tmp_path,
) -> None:
    """Retirement Phase A binds every expected prompt, not only its target row."""
    state = _stale_authority_sequence(tmp_path, include_unrelated=True)
    (state.root / state.unrelated_path).write_bytes(
        b"REQ-UNRELATED: Same identifier, changed protected bytes\n"
    )
    state.policy_path.write_text(json.dumps(_retirement_policy(state)))
    candidate = _commit(state.root, "change unrelated prompt during retirement")

    with pytest.raises(VerificationProfileError, match="managed prompt bytes"):
        load_verification_profiles(
            state.root, _manifest(state.root, state.stale_base, candidate)
        )


def test_retirement_reissue_rejects_canonical_file_alias_target_drift(tmp_path) -> None:
    """An unchanged alias blob cannot hide canonical prompt drift in Phase A."""
    state = _stale_authority_sequence(
        tmp_path, include_unrelated=True, unrelated_alias=True
    )
    alias_before = (state.root / state.unrelated_path).readlink()
    (state.root / state.unrelated_target).write_bytes(
        b"REQ-UNRELATED: Changed canonical target bytes\n"
    )
    assert (state.root / state.unrelated_path).readlink() == alias_before
    state.policy_path.write_text(json.dumps(_retirement_policy(state)))
    candidate = _commit(state.root, "change canonical alias target during retirement")

    with pytest.raises(VerificationProfileError, match="managed prompt bytes"):
        load_verification_profiles(
            state.root, _manifest(state.root, state.stale_base, candidate)
        )


def test_dormant_schema_2_admission_rejects_canonical_alias_target_drift(
    tmp_path,
) -> None:
    """Ordinary Phase A resolves approved aliases before checking every prompt."""
    state = _stale_authority_sequence(
        tmp_path, include_unrelated=True, unrelated_alias=True
    )
    alias_before = (state.root / state.unrelated_path).readlink()
    (state.root / state.unrelated_target).write_bytes(
        b"REQ-UNRELATED: Drift in canonical target during ordinary Phase A\n"
    )
    assert (state.root / state.unrelated_path).readlink() == alias_before
    state.policy_path.write_text(
        json.dumps(
            {
                "schema_version": 2,
                "rotations": _rotation_authorization()["rotations"],
                "requirement_rotations": [state.stale, state.next_widget],
            }
        )
    )
    candidate = _commit(state.root, "ordinary Phase A canonical alias drift")

    with pytest.raises(VerificationProfileError, match="authority-only change"):
        load_verification_profiles(
            state.root, _manifest(state.root, state.stale_base, candidate)
        )


def test_consuming_reissued_authority_rejects_unrelated_managed_prompt_drift(
    tmp_path,
) -> None:
    """Phase B may consume its row but cannot carry another managed prompt change."""
    state = _stale_authority_sequence(tmp_path, include_unrelated=True)
    state.policy_path.write_text(json.dumps(_retirement_policy(state)))
    reissue = _commit(state.root, "protect retirement and fresh authority")

    (state.root / "prompts/gadget_python.prompt").write_bytes(state.gadget_v2)
    state.profile_path.write_bytes(state.profile_v3)
    (state.root / state.unrelated_path).write_bytes(
        b"REQ-UNRELATED: Same requirement, unauthorized byte drift\n"
    )
    candidate = _commit(state.root, "consume authority with unrelated drift")

    with pytest.raises(VerificationProfileError, match="unmanaged prompt bytes"):
        load_verification_profiles(
            state.root, _manifest(state.root, reissue, candidate)
        )


def test_consuming_reissued_authority_allows_unchanged_unrelated_prompts(
    tmp_path,
) -> None:
    """Phase B remains usable when only its exact protected prompt changes."""
    state = _stale_authority_sequence(tmp_path, include_unrelated=True)
    state.policy_path.write_text(json.dumps(_retirement_policy(state)))
    reissue = _commit(state.root, "protect retirement and fresh authority")

    (state.root / "prompts/gadget_python.prompt").write_bytes(state.gadget_v2)
    state.profile_path.write_bytes(state.profile_v3)
    candidate = _commit(state.root, "consume fresh authority only")

    profiles = load_verification_profiles(
        state.root, _manifest(state.root, reissue, candidate)
    )
    assert not profiles.invalid_reasons


@pytest.mark.parametrize("mutation", ["row-order", "row-path", "retirement-order"])
def test_retirement_history_preserves_protected_json_representation(
    tmp_path, mutation
) -> None:
    """Semantic equality cannot rewrite protected historical JSON tokens."""
    state = _stale_authority_sequence(tmp_path)
    policy = _retirement_policy(state)
    if mutation == "row-order":
        policy["requirement_rotations"][0] = dict(reversed(state.first.items()))
        base = state.stale_base
    elif mutation == "row-path":
        policy["requirement_rotations"][1] = dict(state.stale)
        policy["requirement_rotations"][1][
            "prompt_path"
        ] = "prompts/./gadget_python.prompt"
        policy["requirement_rotation_retirements"][0]["obsolete"] = policy[
            "requirement_rotations"
        ][1]
        base = state.stale_base
    else:
        state.policy_path.write_text(json.dumps(policy))
        protected = _commit(state.root, "protect retirement history")
        policy["requirement_rotation_retirements"][0] = {
            "replacement": state.replacement,
            "obsolete": state.stale,
        }
        base = protected
    state.policy_path.write_text(json.dumps(policy))
    candidate = _commit(state.root, f"rewrite retirement history {mutation}")

    with pytest.raises(
        VerificationProfileError, match="rewrites protected representation"
    ):
        load_verification_profiles(state.root, _manifest(state.root, base, candidate))


@pytest.mark.parametrize(
    "location", ["top", "row", "retirement", "obsolete", "replacement"]
)
def test_rotation_policy_rejects_duplicate_json_members_at_every_nesting_level(
    tmp_path, location
) -> None:
    """Authority parsing rejects duplicate members before interpreting any row."""
    state = _stale_authority_sequence(tmp_path)
    row = json.dumps(state.stale, separators=(",", ":"))
    duplicate_row = f'{{"prompt_path":"{state.stale["prompt_path"]}",{row[1:]}'
    retirement = json.dumps(
        {"obsolete": state.stale, "replacement": state.replacement},
        separators=(",", ":"),
    )
    duplicate_retirement = f'{{"obsolete":{row},"obsolete":{row},"replacement":{row}}}'
    duplicate_obsolete = f'{{"obsolete":{duplicate_row},"replacement":{row}}}'
    duplicate_replacement = f'{{"obsolete":{row},"replacement":{duplicate_row}}}'
    retirement_value = {
        "retirement": duplicate_retirement,
        "obsolete": duplicate_obsolete,
        "replacement": duplicate_replacement,
    }.get(location, retirement)
    payload = (
        f'{{"schema_version":3,"rotations":[],"requirement_rotations":[{row}],'
        f'"requirement_rotation_retirements":[{retirement_value}]}}'
    )
    if location == "top":
        payload = payload.replace(
            '"schema_version":3,', '"schema_version":3,"schema_version":3,'
        )
    elif location == "row":
        payload = (
            f'{{"schema_version":2,"rotations":[],'
            f'"requirement_rotations":[{duplicate_row}]}}'
        )

    with pytest.raises(VerificationProfileError, match="duplicate JSON members"):
        verification._parse_requirement_transition_authorizations(  # pylint: disable=protected-access
            payload.encode(), "candidate"
        )


@pytest.mark.parametrize("target", ["live", "consumed"])
def test_retirement_rejects_live_or_consumed_protected_row(tmp_path, target) -> None:
    """Only a dormant row with an unreachable policy binding may be retired."""
    state = _stale_authority_sequence(tmp_path)
    if target == "live":
        base = state.authority_base
        (state.root / "prompts/widget_python.prompt").write_bytes(state.widget_v1)
        state.profile_path.write_bytes(state.profile_v0)
        replacement = _requirement_rule(
            "prompts/gadget_python.prompt",
            b"Gadget contract version one\n",
            state.gadget_v2,
            state.profile_v0,
            state.profile_v3,
        )
        obsolete = state.stale
    else:
        base = state.stale_base
        replacement = state.next_widget
        obsolete = state.first
    state.policy_path.write_text(
        json.dumps(
            _retirement_policy(
                state,
                rows=[state.first, state.stale, replacement],
                retirements=[{"obsolete": obsolete, "replacement": replacement}],
            )
        )
    )
    candidate = _commit(state.root, f"attempt to retire {target} row")

    with pytest.raises(VerificationProfileError, match="candidate retirement"):
        load_verification_profiles(state.root, _manifest(state.root, base, candidate))


@pytest.mark.parametrize(
    "mutation", ["missing", "modified", "duplicate", "fork", "chain", "cycle"]
)
def test_retirement_record_rejects_ambiguous_or_nonexact_history(
    tmp_path, mutation
) -> None:
    """Retirement records are exact single links, never deletion or a graph."""
    state = _stale_authority_sequence(tmp_path)
    policy = _retirement_policy(state)
    if mutation == "missing":
        policy["requirement_rotations"] = [state.first, state.replacement]
    elif mutation == "modified":
        policy["requirement_rotation_retirements"][0]["obsolete"] = dict(state.stale)
        policy["requirement_rotation_retirements"][0]["obsolete"][
            "head_prompt_sha256"
        ] = ("0" * 64)
    elif mutation == "duplicate":
        policy["requirement_rotation_retirements"].append(
            {"obsolete": state.stale, "replacement": state.replacement}
        )
    else:
        alternate = dict(state.replacement)
        alternate["head_policy_sha256"] = "0" * 64
        policy["requirement_rotations"].append(alternate)
        if mutation == "fork":
            link = {"obsolete": state.stale, "replacement": alternate}
        elif mutation == "chain":
            link = {"obsolete": state.replacement, "replacement": alternate}
        else:
            link = {"obsolete": state.replacement, "replacement": state.stale}
        policy["requirement_rotation_retirements"].append(link)
    state.policy_path.write_text(json.dumps(policy))
    candidate = _commit(state.root, f"invalid retirement {mutation}")

    with pytest.raises(VerificationProfileError, match="retirement|ambiguous"):
        load_verification_profiles(
            state.root, _manifest(state.root, state.stale_base, candidate)
        )


@pytest.mark.parametrize(
    "mutation",
    [
        "profile-bytes",
        "prompt",
        "base-policy-binding",
        "base-prompt-binding",
        "already-consumed",
    ],
)
def test_candidate_dormant_authorization_rejects_changed_source_state(
    tmp_path, mutation
) -> None:
    """Candidate-added authority cannot accompany or misstate protected source bytes."""
    root = _repository(tmp_path)
    prompt = root / "prompts/widget_python.prompt"
    prompt.write_text("Opaque contract version one\n")
    profile_path = root / ".pdd/verification-profiles.json"
    profile_path.write_text(json.dumps(_human_profile(root, "threshold-ed25519-v1")))
    policy, candidate_profile = _requirement_transition(
        root, "Opaque contract version two\n"
    )
    rotation_path = root / ".pdd/verification-profile-rotations.json"
    rotation_path.write_text(json.dumps(_empty_requirement_policy()))
    base = _commit(root, "protected source bytes")

    if mutation == "profile-bytes":
        profile_path.write_text(
            json.dumps(json.loads(profile_path.read_text()), indent=2)
        )
    elif mutation == "prompt":
        prompt.write_text("Unbound prompt mutation\n")
    elif mutation == "base-policy-binding":
        row = policy["requirement_rotations"][0]
        row["base_policy_sha256"] = "0" * 64
    elif mutation == "base-prompt-binding":
        row = policy["requirement_rotations"][0]
        row["base_prompt_sha256"] = "0" * 64
    else:
        prompt.write_text("Opaque contract version two\n")
        profile_path.write_text(json.dumps(candidate_profile))
    rotation_path.write_text(json.dumps(policy))
    head = _commit(root, f"attempt dormant authority with {mutation}")

    with pytest.raises(
        VerificationProfileError,
        match="candidate requirement transition lacks protected authorization",
    ):
        load_verification_profiles(root, _manifest(root, base, head))


def test_candidate_dormant_authorization_requires_exact_human_obligation(
    tmp_path,
) -> None:
    """Candidate authority fails closed without the threshold human mapping."""
    root = _repository(tmp_path)
    prompt_path = "prompts/widget_python.prompt"
    current_prompt = b"Opaque contract version one\n"
    future_prompt = b"Opaque contract version two\n"
    (root / prompt_path).write_bytes(current_prompt)
    current_row = _human_row(prompt_path, current_prompt)
    current_row["obligations"][0]["validator_id"] = "untrusted"
    future_row = _human_row(prompt_path, future_prompt)
    current_profile = json.dumps({"profiles": [current_row]}).encode()
    future_profile = json.dumps({"profiles": [future_row]}).encode()
    (root / ".pdd/verification-profiles.json").write_bytes(current_profile)
    policy = {
        "schema_version": 2,
        "rotations": _rotation_authorization()["rotations"],
        "requirement_rotations": [
            _requirement_rule(
                prompt_path,
                current_prompt,
                future_prompt,
                current_profile,
                future_profile,
            )
        ],
    }
    rotation_path = root / ".pdd/verification-profile-rotations.json"
    rotation_path.write_text(json.dumps(_empty_requirement_policy()))
    base = _commit(root, "protected malformed human obligation")

    rotation_path.write_text(json.dumps(policy))
    head = _commit(root, "attempt authority without threshold human mapping")

    with pytest.raises(
        VerificationProfileError,
        match="candidate requirement transition lacks protected authorization",
    ):
        load_verification_profiles(root, _manifest(root, base, head))


def test_exact_requirement_transition_updates_all_obligation_mappings(
    tmp_path,
) -> None:
    """Exact transition remaps every existing obligation to the new contract."""
    root = _repository(tmp_path)
    prompt = root / "prompts/widget_python.prompt"
    prompt.write_text("Opaque contract version one\n")
    profile_path = root / ".pdd/verification-profiles.json"
    protected_profile = _human_profile(root, "threshold-ed25519-v1")
    protected_requirement = protected_profile["profiles"][0][
        "required_requirement_ids"
    ][0]
    protected_profile["profiles"][0]["obligations"].append(
        {
            "obligation_id": "pytest",
            "kind": "test",
            "validator_id": "pytest",
            "validator_config_digest": "pytest-v1",
            "requirement_ids": [protected_requirement],
            "artifact_paths": ["tests/test_widget.py"],
            "required": True,
        }
    )
    profile_path.write_text(json.dumps(protected_profile))
    target_prompt = b"Opaque contract version two\n"
    target_requirement = f"CONTRACT-SHA256:{hashlib.sha256(target_prompt).hexdigest()}"
    candidate_profile = json.loads(json.dumps(protected_profile))
    candidate_profile["profiles"][0]["required_requirement_ids"] = [target_requirement]
    for obligation in candidate_profile["profiles"][0]["obligations"]:
        obligation["requirement_ids"] = [target_requirement]
    policy, candidate_profile = _requirement_transition(
        root,
        target_prompt.decode(),
        candidate_profile,
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
    assert all(
        obligation.requirement_ids == (requirement,)
        for obligation in profiles.profiles[0].obligations
    )


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
    """Exact byte bindings permit only existing obligation requirement remaps."""
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
            "CONTRACT-SHA256:91bbf9390f5489d3dbc3c8671d490feb4a7764d89270d2211875758c44a6ac2c"
        ),
        "to_requirement_id": (
            "CONTRACT-SHA256:9771b4f0be08d137421acf8e66dcdd262ec2795908c59b09a38e4ea5bc7acef0"
        ),
        "policy_path": ".pdd/verification-profiles.json",
        "base_policy_sha256": (
            "2885c95a2d45969754ff96f3c392be5082acfa817abba047b7e3933164217352"
        ),
        "head_policy_sha256": (
            "d0945b7c4fe316619a8ab8cc8eb38b970b95f5a5a42a408a312dae8c2bb9cd7d"
        ),
        "base_prompt_sha256": (
            "91bbf9390f5489d3dbc3c8671d490feb4a7764d89270d2211875758c44a6ac2c"
        ),
        "head_prompt_sha256": (
            "9771b4f0be08d137421acf8e66dcdd262ec2795908c59b09a38e4ea5bc7acef0"
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
                        verification._obligation(
                            item
                        )  # pylint: disable=protected-access
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
    authorizations, prompts, _new_authorizations = (
        verification._load_requirement_transition_authorizations(  # pylint: disable=protected-access
            ROOT, manifest
        )
    )
    updates, invalid = (
        verification._authorized_requirement_updates(  # pylint: disable=protected-access
            ROOT,
            manifest,
            _estimate_inputs(PROFILE_FILE.read_bytes()),
            _estimate_inputs(head_profile),
            authorizations,
            prompts,
        )
    )
    return authorizations, updates, invalid


def test_expected_requirement_update_restamps_bound_test_obligations() -> None:
    """An exact prompt transition may update only requirement bindings on tests."""
    previous = "CONTRACT-SHA256:before"
    current = "CONTRACT-SHA256:after"
    authorization = verification._RequirementTransitionAuthorization(  # pylint: disable=protected-access
        PurePosixPath("prompts/widget_python.prompt"),
        "python",
        previous,
        current,
        PROFILE_REL_PATH,
        verification._RequirementTransitionBindings(  # pylint: disable=protected-access
            "base-policy", "head-policy", "base-prompt", "head-prompt"
        ),
    )
    human = verification.VerificationObligation(
        "threshold-human-attestation",
        "human-attestation",
        "threshold-ed25519",
        "threshold-ed25519-v1",
        (previous,),
        (PurePosixPath("prompts/widget_python.prompt"),),
        True,
    )
    test_obligation = verification.VerificationObligation(
        "pytest-widget",
        "test",
        "pytest",
        "pytest-v1",
        (previous,),
        (PurePosixPath("tests/test_widget.py"),),
        True,
    )
    protected = verification._ProfileInput(  # pylint: disable=protected-access
        (previous,), (human, test_obligation)
    )
    candidate = verification._ProfileInput(  # pylint: disable=protected-access
        (current,),
        tuple(
            sorted(
                (
                    verification.replace(human, requirement_ids=(current,)),
                    verification.replace(test_obligation, requirement_ids=(current,)),
                )
            )
        ),
    )

    update, reason = (
        verification._expected_requirement_update(  # pylint: disable=protected-access
            authorization, protected, candidate
        )
    )

    assert reason is None
    assert update == candidate


def test_estimate_contract_rotations_are_exact_and_dormant(monkeypatch) -> None:
    """Preauthorize only the reviewed dormant generate transition."""
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
        assert hashlib.sha256((ROOT / prompt_path).read_bytes()).hexdigest() == (
            rule["base_prompt_sha256"]
        )
        assert hashlib.sha256(target_prompts[prompt_path]).hexdigest() == (
            rule["head_prompt_sha256"]
        )

    current_inputs = _estimate_inputs(PROFILE_FILE.read_bytes())
    assert len(current_inputs) == 1
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


def test_estimate_contract_rotations_share_one_exact_profile_transition() -> None:
    """The dormant #2058 row has one exact profile binding and replacement."""
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
        update, reason = (
            verification._expected_requirement_update(  # pylint: disable=protected-access
                authorization, protected[unit_id], candidate[unit_id]
            )
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
        "protected-control-deletion",
        "validator-remap",
        "denominator-reduction",
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
        target_prompts.clear()
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
            if row["prompt_path"] != ESTIMATE_REQUIREMENT_ROTATIONS[0]["prompt_path"]
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
            estimate[0]["prompt_path"] = "pdd/prompts/core/cli_python.prompt"
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
        "protected-control-deletion",
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
                "candidate (?:requirement transition "
                "(?:lacks protected authorization|rules are duplicated or ambiguous)"
                "|removed unconsumed protected requirement transition"
                "|schema-2 history rewrites protected representation)"
            ),
        ):
            verification._load_requirement_transition_authorizations(  # pylint: disable=protected-access
                ROOT, manifest
            )
        return

    _authorizations, updates, invalid = _estimate_updates(
        monkeypatch, target_profile, target_prompts, head_rotation
    )
    if substitution == "denominator-reduction":
        assert len(updates) < 2
    else:
        assert invalid
    assert not updates
