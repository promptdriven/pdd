"""Protected PDD inventory rollout policy tests."""

from __future__ import annotations

import hashlib
import json
import re
import subprocess
from dataclasses import replace
from pathlib import Path, PurePosixPath
from types import SimpleNamespace

import pytest

from pdd.sync_core import build_unit_manifest, load_verification_profiles, verification
from pdd.sync_core.manifest import ManifestRefs
from pdd.sync_core.types import UnitId
from pdd.sync_core.verification import PROFILE_PATH as PROFILE_REL_PATH


ROOT = Path(__file__).resolve().parents[1]
EXPECTED_PATH = ROOT / ".pdd" / "expected-managed.json"
OWNERSHIP_PATH = ROOT / ".pdd" / "sync-ownership.json"
PROFILE_FILE = ROOT / PROFILE_REL_PATH
ROTATION_FILE = ROOT / ".pdd" / "verification-profile-rotations.json"
REPOSITORY_ID = "3b4d7b1c-d6cc-4752-ba93-6b98d1a710e0"
EXPECTED_MANAGED_UNITS = 466
FOUNDATION_PROFILE_PATHS = {
    "pdd/sync_core/descriptor_store.py",
    "pdd/sync_core/signer_process.py",
    "pdd/sync_core/supervisor.py",
}
REQUIREMENT_ID = re.compile(r"\bREQ-[A-Za-z0-9_.:-]+\b")
PYTEST_VALIDATOR_CONFIG_DIGEST = (
    "7c29aa937a70b7db28c9353bbad309654e12d3fb4d317edf75b475bbc1880963"
)
FOUNDATION_PROFILE = "pdd/prompts/durable_sync_runner_python.prompt"
FOUNDATION_PROFILE_DIGEST = (
    "3fb63c651345467be6b2cb445b34edf979b35ffba1bb1ebb44a81f1313beb244"
)
FOUNDATION_OBLIGATIONS = {
    "pytest-descriptor-store": {
        "tests": (
            "tests/test_sync_core_candidate_artifact_provenance.py",
            "tests/test_sync_core_descriptor_store.py",
            "tests/test_sync_core_trust.py",
        ),
        "code": ("pdd/sync_core/descriptor_store.py",),
    },
    "pytest-supervisor": {
        "tests": (
            "tests/test_sync_core_lifecycle_scenarios.py",
            "tests/test_sync_core_runner.py",
            "tests/test_sync_core_supervisor.py",
        ),
        "code": ("pdd/sync_core/supervisor.py",),
    },
    "pytest-signer-process": {
        "tests": ("tests/test_sync_core_trust.py",),
        "code": ("pdd/sync_core/signer_process.py",),
    },
}
LEGACY_METADATA_EXAMPLE_PREAUTHORIZED_PATHS = {
    ".pdd/meta/agentic_common_python_run.json",
    ".pdd/meta/generate_model_catalog_python.json",
    ".pdd/meta/prompt_repair_python.json",
    ".pdd/meta/routing_policy_python.json",
    ".pdd/meta/routing_policy_python_run.json",
    ".pdd/meta/setup_tool_python.json",
    ".pdd/meta/setup_tool_python_run.json",
    "context/prompt_repair_example.py",
    "context/routing_policy_example.py",
}
PREAUTHORIZED_CHILD_PATHS = LEGACY_METADATA_EXAMPLE_PREAUTHORIZED_PATHS | {
    ".pdd/meta/agentic_checkup_orchestrator_python_run.json",
    ".pdd/meta/checkup_agentic_artifact_python.json",
    ".pdd/meta/story_regression_python.json",
    "context/checkup_agentic_artifact_example.py",
    "tests/test_checkup_agentic_artifact.py",
    "tests/test_unit_tests_workflow.py",
    "tests/test_ci_drift_heal_example_contract.py",
    "tests/test_sync_core_runner_jest.py",
    "tests/test_sync_core_runner_vitest.py",
    "tests/test_sync_core_runner_playwright.py",
    "tests/test_cloud_global_dry_run.py",
    "tests/test_continuous_sync_path_policy.py",
    "pdd/sync_core/human_attestation.py",
    "tests/test_sync_core_human_attestation.py",
}
PREAUTHORIZED_CHILD_OWNERSHIP = {
    "inventory": "HUMAN_OWNED",
    "role": "human-maintained",
    "owner": "pdd-maintainers",
    "preauthorize_absent": True,
}
CI_DETECT_REQUIREMENT_ROTATION = {
    "prompt_path": "pdd/prompts/ci_detect_changed_modules_python.prompt",
    "language_id": "python",
    "from_requirement_id": (
        "CONTRACT-SHA256:2d5d65f695fc6c8cd2f3e82f5c5d2a55ad3eb30fc4791b2a1d94ff8465ab6d10"
    ),
    "to_requirement_id": (
        "CONTRACT-SHA256:f0d873e5505d40035d3c7364fd3961b5602d21519ec9be2049c2f38b16239712"
    ),
    "policy_path": ".pdd/verification-profiles.json",
    "base_policy_sha256": (
        "58a704c9d5d351e6b83e2c42126cfe85214aa3ffbf6cb3e64ac4105f3fb19b3e"
    ),
    "head_policy_sha256": (
        "7df63fe892ac14382f226ea97dbd2ac186a8cb48213faec958ad32c51d51aeb5"
    ),
    "base_prompt_sha256": (
        "2d5d65f695fc6c8cd2f3e82f5c5d2a55ad3eb30fc4791b2a1d94ff8465ab6d10"
    ),
    "head_prompt_sha256": (
        "f0d873e5505d40035d3c7364fd3961b5602d21519ec9be2049c2f38b16239712"
    ),
}
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


def _git(root: Path, *args: str) -> None:
    subprocess.run(["git", *args], cwd=root, check=True, capture_output=True)


def _commit(root: Path, message: str) -> str:
    _git(root, "add", ".")
    _git(
        root,
        "-c",
        "user.name=PDD test",
        "-c",
        "user.email=pdd@example.test",
        "commit",
        "-m",
        message,
    )
    return subprocess.check_output(
        ["git", "rev-parse", "HEAD"], cwd=root, text=True
    ).strip()


def _requirements(prompt_path: PurePosixPath) -> list[str]:
    raw = (ROOT / prompt_path).read_bytes()
    explicit = sorted(set(REQUIREMENT_ID.findall(raw.decode("utf-8"))))
    return explicit or [f"CONTRACT-SHA256:{hashlib.sha256(raw).hexdigest()}"]


def _profile_bytes_as_protected_base(monkeypatch, profile_bytes: bytes) -> None:
    def protected_read(_root: Path, _ref: str, path: PurePosixPath) -> bytes | None:
        if path == PROFILE_REL_PATH:
            return profile_bytes
        resolved = ROOT / path
        return resolved.read_bytes() if resolved.is_file() else None

    monkeypatch.setattr(verification, "read_git_blob", protected_read)


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


def test_pdd_protected_inventory_is_complete_and_exact() -> None:
    """The committed PDD tree has a non-waived protected inventory partition."""
    assert EXPECTED_PATH.is_file(), "missing protected expected-managed registry"
    assert OWNERSHIP_PATH.is_file(), "missing protected sync ownership policy"

    expected = json.loads(EXPECTED_PATH.read_text(encoding="utf-8"))
    ownership = json.loads(OWNERSHIP_PATH.read_text(encoding="utf-8"))
    assert expected.keys() == {"schema_version", "units"}
    assert expected["schema_version"] == 1
    assert isinstance(expected["units"], list) and expected["units"]
    assert all(set(row) == {"prompt_path", "language_id"} for row in expected["units"])
    identities = {(row["prompt_path"], row["language_id"]) for row in expected["units"]}
    assert len(identities) == len(expected["units"]) == EXPECTED_MANAGED_UNITS

    assert ownership.keys() == {"rules"}
    assert isinstance(ownership["rules"], list) and ownership["rules"]
    assert all(
        set(row)
        in (
            {"pattern", "inventory", "role", "owner"},
            {"pattern", "inventory", "role", "owner", "preauthorize_absent"},
        )
        and row["inventory"] == "HUMAN_OWNED"
        and row["role"] in {"human-maintained", "excluded-project"}
        and row["owner"] == "pdd-maintainers"
        and row.get("preauthorize_absent", False)
        == (row["pattern"] in PREAUTHORIZED_CHILD_PATHS)
        and not any(token in row["pattern"] for token in ("*", "?", "["))
        for row in ownership["rules"]
    )
    patterns = [row["pattern"] for row in ownership["rules"]]
    assert len(patterns) == len(set(patterns))

    assert not (ROOT / ".pdd" / "sync-waivers.json").exists()
    assert PROFILE_FILE.is_file()
    assert not (ROOT / ".pdd" / "attestation-trust.json").exists()

    manifest = build_unit_manifest(ROOT, base_ref="HEAD", head_ref="HEAD")
    assert manifest.repository_id == REPOSITORY_ID
    assert not manifest.invalid_reasons
    assert not manifest.unaccounted_tracked_paths
    assert {
        (unit.prompt_relpath.as_posix(), unit.language_id)
        for unit in manifest.expected_managed
    } == identities
    assert len(manifest.expected_managed) == EXPECTED_MANAGED_UNITS

    foundation_paths = {
        PurePosixPath(path)
        for obligation in FOUNDATION_OBLIGATIONS.values()
        for path in obligation["code"]
    }
    foundation_candidates = {
        item.candidate_id.artifact_relpath: item
        for item in manifest.candidates
        if item.candidate_id.artifact_relpath in foundation_paths
    }
    assert set(foundation_candidates) == foundation_paths
    assert all(
        item.inventory.value == "HUMAN_OWNED"
        and item.candidate_id.role == "human-maintained"
        and item.ownership_provenance
        == f"protected-ownership:pdd-maintainers:{path.as_posix()}"
        for path, item in foundation_candidates.items()
    )

    managed_prompt_paths = {
        unit.unit_id.prompt_relpath.as_posix() for unit in manifest.managed_units
    }
    assert managed_prompt_paths == {path for path, _language in identities}
    tracked = (
        subprocess.check_output(
            ["git", "ls-tree", "-r", "-z", "--name-only", "HEAD"], cwd=ROOT
        )
        .decode("utf-8")
        .split("\0")[:-1]
    )
    assert {
        item.candidate_id.artifact_relpath.as_posix() for item in manifest.candidates
    } == set(tracked)


def test_detector_contract_rotation_is_exact_and_consumed() -> None:
    """Retain the exact authorization after adopting its reviewed head bytes."""
    policy = json.loads(ROTATION_FILE.read_text(encoding="utf-8"))
    rules = policy["requirement_rotations"]
    detector_rules = [
        row
        for row in rules
        if row["prompt_path"] == "pdd/prompts/ci_detect_changed_modules_python.prompt"
    ]
    assert detector_rules == [CI_DETECT_REQUIREMENT_ROTATION]
    prompt = ROOT / CI_DETECT_REQUIREMENT_ROTATION["prompt_path"]
    assert hashlib.sha256(prompt.read_bytes()).hexdigest() == (
        CI_DETECT_REQUIREMENT_ROTATION["head_prompt_sha256"]
    )

    manifest = build_unit_manifest(ROOT, base_ref="HEAD", head_ref="HEAD")
    profiles = load_verification_profiles(ROOT, manifest)
    assert not profiles.invalid_reasons
    assert profiles.coverage == 1.0

def _requirement_authorization_row(authorization) -> dict[str, str]:
    """Render one in-code exact authorization in protected-policy form."""
    return {
        "prompt_path": authorization.prompt_path.as_posix(),
        "language_id": authorization.language_id,
        "from_requirement_id": authorization.from_requirement_id,
        "to_requirement_id": authorization.to_requirement_id,
        "policy_path": authorization.policy_path.as_posix(),
        "base_policy_sha256": authorization.bindings.base_policy_sha256,
        "head_policy_sha256": authorization.bindings.head_policy_sha256,
        "base_prompt_sha256": authorization.bindings.base_prompt_sha256,
        "head_prompt_sha256": authorization.bindings.head_prompt_sha256,
    }


def test_pr1790_rotations_equal_exact_dormant_bootstrap_authority() -> None:
    """Committed rules exactly match code trust roots and remain future-only."""
    policy = json.loads(ROTATION_FILE.read_text(encoding="utf-8"))
    rows = policy["requirement_rotations"]
    bootstrap_rows = {
        (row["prompt_path"], row["language_id"]): row
        for row in map(
            _requirement_authorization_row,
            verification._BOOTSTRAP_REQUIREMENT_TRANSITIONS,  # pylint: disable=protected-access
        )
    }
    policy_rows = {(row["prompt_path"], row["language_id"]): row for row in rows}
    assert len(rows) == len(policy_rows) == len(bootstrap_rows) == 13
    assert policy_rows == bootstrap_rows

    profile_digest = hashlib.sha256(PROFILE_FILE.read_bytes()).hexdigest()
    pr1790_rows = [
        row
        for row in rows
        if row["head_policy_sha256"]
        == "e451dc7b076388f184e8c9f5f4f89c93a027bcf1d666f5c96b3767f76cb22af5"
    ]
    assert len(pr1790_rows) == 10
    base_policy_digest = pr1790_rows[0]["base_policy_sha256"]
    head_policy_digest = pr1790_rows[0]["head_policy_sha256"]
    assert profile_digest in {base_policy_digest, head_policy_digest}
    prompt_digest_field = (
        "base_prompt_sha256"
        if profile_digest == base_policy_digest
        else "head_prompt_sha256"
    )
    for row in pr1790_rows:
        assert row["base_policy_sha256"] == base_policy_digest
        assert row["head_policy_sha256"] == head_policy_digest
        prompt = ROOT / row["prompt_path"]
        assert (
            hashlib.sha256(prompt.read_bytes()).hexdigest() == row[prompt_digest_field]
        )
        assert row["base_prompt_sha256"] != row["head_prompt_sha256"]
        assert row["base_policy_sha256"] != row["head_policy_sha256"]


@pytest.mark.parametrize(
    "field,replacement",
    (
        ("prompt_path", "pdd/prompts/not_authorized_python.prompt"),
        ("language_id", "llm"),
        ("from_requirement_id", f"CONTRACT-SHA256:{'0' * 64}"),
        ("to_requirement_id", f"CONTRACT-SHA256:{'0' * 64}"),
        ("policy_path", ".pdd/not-the-profile-policy.json"),
        ("base_policy_sha256", "0" * 64),
        ("head_policy_sha256", "0" * 64),
        ("base_prompt_sha256", "0" * 64),
        ("head_prompt_sha256", "0" * 64),
    ),
)
def test_pr1790_bootstrap_transition_bindings_fail_closed(
    monkeypatch, field: str, replacement: str
) -> None:
    """Changing any identity or byte binding loses bootstrap authority."""
    row = json.loads(ROTATION_FILE.read_text(encoding="utf-8"))[
        "requirement_rotations"
    ][1]
    row[field] = replacement
    candidate = json.dumps(
        {"schema_version": 2, "rotations": [], "requirement_rotations": [row]}
    ).encode()

    monkeypatch.setattr(
        verification,
        "read_git_blob",
        lambda _root, ref, path: (
            candidate
            if ref == "candidate" and path == verification.ROTATION_POLICY_PATH
            else None
        ),
    )
    manifest = SimpleNamespace(
        repository_id=REPOSITORY_ID,
        base_ref="protected",
        head_ref="candidate",
    )

    with pytest.raises(
        verification.VerificationProfileError,
        match="candidate requirement transition",
    ):
        verification._load_requirement_transition_authorizations(  # pylint: disable=protected-access
            ROOT, manifest
        )


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


def test_rollout_profiles_cover_the_protected_pdd_denominator(monkeypatch) -> None:
    # pylint: disable=too-many-locals
    """Require one complete, reviewable profile for every protected PDD unit."""
    payload = json.loads(PROFILE_FILE.read_text(encoding="utf-8"))
    rows = payload["profiles"]
    manifest = build_unit_manifest(ROOT, base_ref="HEAD", head_ref="HEAD")
    assert not manifest.invalid_reasons
    assert not manifest.unaccounted_tracked_paths
    expected = {
        (unit.prompt_relpath.as_posix(), unit.language_id)
        for unit in manifest.expected_managed
    }
    actual = {(row["prompt_path"], row["language_id"]) for row in rows}

    assert len(expected) == EXPECTED_MANAGED_UNITS
    assert len(rows) == EXPECTED_MANAGED_UNITS
    assert len(actual) == len(rows)
    assert actual == expected

    for row in rows:
        prompt_path = PurePosixPath(row["prompt_path"])
        requirements = _requirements(prompt_path)
        assert row["required_requirement_ids"] == requirements
        human_obligations = [
            item
            for item in row["obligations"]
            if item["validator_id"] == "threshold-ed25519"
        ]
        assert len(human_obligations) == 1
        obligation = human_obligations[0]
        assert obligation["obligation_id"] == "threshold-human-attestation"
        assert obligation["kind"] == "human-attestation"
        assert obligation["validator_id"] == "threshold-ed25519"
        assert obligation["validator_config_digest"] == "threshold-ed25519-v1"
        assert obligation["required"] is True
        assert obligation["requirement_ids"] == requirements
        assert obligation["artifact_paths"] == [prompt_path.as_posix()]
        assert (ROOT / prompt_path).is_file()

    profile_bytes = PROFILE_FILE.read_bytes()
    protected_manifest = replace(
        manifest, refs=ManifestRefs("protected-base", "candidate-head")
    )
    _profile_bytes_as_protected_base(monkeypatch, profile_bytes)
    profiles = load_verification_profiles(ROOT, protected_manifest)
    assert not profiles.invalid_reasons
    assert profiles.coverage == 1.0
    assert len(profiles.profiles) == EXPECTED_MANAGED_UNITS

    pytest_obligations = [
        obligation
        for profile in profiles.profiles
        for obligation in profile.obligations
        if obligation.validator_id == "pytest"
    ]
    for obligation in pytest_obligations:
        assert obligation.validator_config_digest == PYTEST_VALIDATOR_CONFIG_DIGEST
    foundation_profile = next(
        profile
        for profile in profiles.profiles
        if profile.unit_id.prompt_relpath.as_posix() == FOUNDATION_PROFILE
    )
    assert foundation_profile.profile_digest == FOUNDATION_PROFILE_DIGEST
    foundation_pytest = {
        obligation.obligation_id: obligation
        for obligation in foundation_profile.obligations
        if obligation.validator_id == "pytest"
    }
    assert set(foundation_pytest) == set(FOUNDATION_OBLIGATIONS)
    for obligation_id, expected_obligation in FOUNDATION_OBLIGATIONS.items():
        obligation = foundation_pytest[obligation_id]
        assert obligation.kind == "test"
        assert obligation.required is True
        assert obligation.requirement_ids == foundation_profile.required_requirement_ids
        assert tuple(path.as_posix() for path in obligation.artifact_paths) == (
            expected_obligation["tests"]
        )
        assert tuple(path.as_posix() for path in obligation.code_under_test_paths) == (
            expected_obligation["code"]
        )
    assert {
        path.as_posix()
        for obligation in foundation_pytest.values()
        for path in obligation.code_under_test_paths
    } == FOUNDATION_PROFILE_PATHS


def test_rollout_profiles_cannot_self_authorize(monkeypatch) -> None:
    """A candidate copy is rejected until this rollout has merged as protected base."""
    manifest = build_unit_manifest(ROOT, base_ref="HEAD", head_ref="HEAD")
    candidate_manifest = replace(
        manifest, refs=ManifestRefs("protected-base", "candidate-head")
    )
    profile_bytes = PROFILE_FILE.read_bytes()

    def candidate_only_read(_root: Path, ref: str, path: PurePosixPath) -> bytes | None:
        if path == PROFILE_REL_PATH:
            return profile_bytes if ref == "candidate-head" else None
        resolved = ROOT / path
        return resolved.read_bytes() if resolved.is_file() else None

    monkeypatch.setattr(verification, "read_git_blob", candidate_only_read)
    profiles = load_verification_profiles(ROOT, candidate_manifest)

    assert profiles.coverage == 0.0
    assert len(profiles.invalid_reasons) == EXPECTED_MANAGED_UNITS * 2
    candidate_only = [
        reason
        for reason in profiles.invalid_reasons
        if "candidate-only profile lacks protected approval" in reason
    ]
    incomplete = [
        reason
        for reason in profiles.invalid_reasons
        if "verification profile is incomplete" in reason
    ]
    assert len(candidate_only) == EXPECTED_MANAGED_UNITS
    assert len(incomplete) == EXPECTED_MANAGED_UNITS


def _bootstrap_addition_fixture(monkeypatch):
    """Build one synthetic exact-byte candidate-only profile authorization."""
    prompt_path = PurePosixPath("prompts/bootstrap_python.prompt")
    prompt_bytes = b"Bootstrap an opaque managed unit.\n"
    policy_bytes = b'{"profiles":[]}\n'
    requirement_id = f"CONTRACT-SHA256:{hashlib.sha256(prompt_bytes).hexdigest()}"
    unit_id = UnitId(REPOSITORY_ID, prompt_path, "python")
    profile = verification._ProfileInput(  # pylint: disable=protected-access
        (requirement_id,),
        (
            verification.VerificationObligation(
                "threshold-human-attestation",
                "human-attestation",
                "threshold-ed25519",
                "threshold-ed25519-v1",
                (requirement_id,),
                (prompt_path,),
                True,
            ),
        ),
    )
    monkeypatch.setattr(
        verification,
        "_BOOTSTRAP_PROFILE_ADDITIONS",
        (
            (
                prompt_path,
                "python",
                requirement_id,
                hashlib.sha256(policy_bytes).hexdigest(),
                hashlib.sha256(prompt_bytes).hexdigest(),
            ),
        ),
    )
    blobs = {
        ("candidate", PROFILE_REL_PATH): policy_bytes,
        ("candidate", prompt_path): prompt_bytes,
    }
    monkeypatch.setattr(
        verification,
        "read_git_blob",
        lambda _root, ref, path: blobs.get((ref, path)),
    )
    manifest = SimpleNamespace(
        repository_id=REPOSITORY_ID,
        base_ref="protected",
        head_ref="candidate",
        expected_managed=(unit_id,),
    )
    return manifest, unit_id, profile, blobs


def test_exact_bootstrap_profile_addition_is_authorized(monkeypatch) -> None:
    """The reviewed repository-, policy-, prompt-, and profile-bound tuple works."""
    manifest, unit_id, profile, _blobs = _bootstrap_addition_fixture(monkeypatch)

    additions = (
        verification._authorized_profile_additions(  # pylint: disable=protected-access
            ROOT, manifest, {}, {unit_id: profile}
        )
    )

    assert additions == {unit_id: profile}


@pytest.mark.parametrize(
    "mutation",
    (
        "wrong-repository",
        "wrong-policy",
        "wrong-prompt",
        "altered-profile",
        "base-existing",
        "not-expected",
        "base-prompt-exists",
    ),
)
def test_bootstrap_profile_addition_fails_closed(monkeypatch, mutation: str) -> None:
    """Any deviation from the exact protected bootstrap tuple is rejected."""
    manifest, unit_id, profile, blobs = _bootstrap_addition_fixture(monkeypatch)
    base = {}
    head = {unit_id: profile}
    if mutation == "wrong-repository":
        manifest.repository_id = "00000000-0000-0000-0000-000000000000"
    elif mutation == "wrong-policy":
        blobs[("candidate", PROFILE_REL_PATH)] = b"different policy\n"
    elif mutation == "wrong-prompt":
        blobs[("candidate", unit_id.prompt_relpath)] = b"different prompt\n"
    elif mutation == "altered-profile":
        head[unit_id] = verification._ProfileInput(  # pylint: disable=protected-access
            profile.requirements, ()
        )
    elif mutation == "base-existing":
        base[unit_id] = profile
    elif mutation == "not-expected":
        manifest.expected_managed = ()
    elif mutation == "base-prompt-exists":
        blobs[("protected", unit_id.prompt_relpath)] = blobs[
            ("candidate", unit_id.prompt_relpath)
        ]

    additions = (
        verification._authorized_profile_additions(  # pylint: disable=protected-access
            ROOT, manifest, base, head
        )
    )

    assert not additions


def test_pdd_registry_prevents_candidate_denominator_reduction(tmp_path: Path) -> None:
    """Candidate additions must persist the denominator; removals remain debt."""
    root = tmp_path / "inventory"
    (root / ".pdd").mkdir(parents=True)
    (root / "prompts").mkdir()
    (root / ".pdd" / "repository-id").write_text(f"{REPOSITORY_ID}\n", encoding="ascii")
    (root / ".pdd" / "expected-managed.json").write_text(
        json.dumps(
            {
                "schema_version": 1,
                "units": [
                    {
                        "prompt_path": "prompts/owned_python.prompt",
                        "language_id": "python",
                    }
                ],
            }
        ),
        encoding="utf-8",
    )
    (root / ".pdd" / "sync-ownership.json").write_text(
        json.dumps(
            {
                "rules": [
                    {
                        "pattern": "README.md",
                        "inventory": "HUMAN_OWNED",
                        "role": "human-maintained",
                        "owner": "pdd-maintainers",
                    }
                ]
            }
        ),
        encoding="utf-8",
    )
    (root / "prompts" / "owned_python.prompt").write_text("owned", encoding="utf-8")
    (root / "README.md").write_text("human", encoding="utf-8")
    _git(root, "init", "-q")
    base = _commit(root, "protected baseline")

    (root / "prompts" / "added_python.prompt").write_text("added", encoding="utf-8")
    added = _commit(root, "candidate addition")
    addition_manifest = build_unit_manifest(root, base_ref=base, head_ref=added)
    assert len(addition_manifest.expected_managed) == 2
    assert any(
        "fixed-point" in reason
        and "protected expected-managed registry omits base unit" in reason
        for reason in addition_manifest.invalid_reasons
    )

    expected = json.loads(
        (root / ".pdd" / "expected-managed.json").read_text(encoding="utf-8")
    )
    expected["units"].append(
        {"prompt_path": "prompts/added_python.prompt", "language_id": "python"}
    )
    (root / ".pdd" / "expected-managed.json").write_text(
        json.dumps(expected), encoding="utf-8"
    )
    registered = _commit(root, "persist candidate denominator")
    registered_manifest = build_unit_manifest(root, base_ref=base, head_ref=registered)
    stable_manifest = build_unit_manifest(
        root, base_ref=registered, head_ref=registered
    )
    assert not registered_manifest.invalid_reasons
    assert not registered_manifest.unaccounted_tracked_paths
    assert not stable_manifest.invalid_reasons
    assert not stable_manifest.unaccounted_tracked_paths
    assert len(registered_manifest.expected_managed) == 2
    assert len(stable_manifest.expected_managed) == 2

    _git(root, "rm", "prompts/owned_python.prompt")
    removed = _commit(root, "candidate removal")
    removal_manifest = build_unit_manifest(root, base_ref=base, head_ref=removed)
    assert len(removal_manifest.expected_managed) == 2
    assert any(
        "removed managed unit lacks" in reason
        for reason in removal_manifest.invalid_reasons
    )


def test_candidate_cannot_delete_protected_denominator_controls(
    tmp_path: Path,
) -> None:
    """A head without either protected manifest cannot become the next base."""
    root = tmp_path / "deleted-controls"
    (root / ".pdd").mkdir(parents=True)
    (root / "prompts").mkdir()
    (root / ".pdd" / "repository-id").write_text(f"{REPOSITORY_ID}\n", encoding="ascii")
    (root / ".pdd" / "expected-managed.json").write_text(
        json.dumps(
            {
                "schema_version": 1,
                "units": [
                    {
                        "prompt_path": "prompts/owned_python.prompt",
                        "language_id": "python",
                    }
                ],
            }
        ),
        encoding="utf-8",
    )
    (root / ".pdd" / "sync-ownership.json").write_text(
        json.dumps(
            {
                "rules": [
                    {
                        "pattern": "README.md",
                        "inventory": "HUMAN_OWNED",
                        "role": "human-maintained",
                        "owner": "pdd-maintainers",
                    }
                ]
            }
        ),
        encoding="utf-8",
    )
    (root / "prompts" / "owned_python.prompt").write_text("owned", encoding="utf-8")
    (root / "README.md").write_text("human", encoding="utf-8")
    _git(root, "init", "-q")
    base = _commit(root, "protected baseline")

    _git(
        root,
        "rm",
        ".pdd/expected-managed.json",
        ".pdd/sync-ownership.json",
    )
    deleted = _commit(root, "delete protected controls")
    transition = build_unit_manifest(root, base_ref=base, head_ref=deleted)
    stable = build_unit_manifest(root, base_ref=deleted, head_ref=deleted)

    assert any(
        "protected sync ownership policy is missing" in reason
        for reason in transition.invalid_reasons
    )
    assert any(
        "protected expected-managed registry is missing" in reason
        for reason in transition.invalid_reasons
    )
    assert Path("README.md") in transition.unaccounted_tracked_paths
    assert Path("README.md") in stable.unaccounted_tracked_paths


def test_profile_candidate_accounts_for_foundation_paths_from_protected_base(
    tmp_path: Path,
) -> None:
    """A profile candidate cannot supply ownership missing from its protected base."""
    root = tmp_path / "profile-candidate"
    subprocess.run(
        ["git", "clone", "-q", "--no-hardlinks", str(ROOT), str(root)],
        check=True,
        capture_output=True,
    )
    base = subprocess.check_output(
        ["git", "rev-parse", "HEAD"], cwd=root, text=True
    ).strip()

    (root / ".pdd" / "verification-profiles.json").write_text(
        '{"schema_version": 1, "profiles": []}\n', encoding="utf-8"
    )
    _git(root, "add", "-f", ".pdd/verification-profiles.json")
    candidate = _commit(root, "candidate profile rollout")

    manifest = build_unit_manifest(root, base_ref=base, head_ref=candidate)
    assert manifest.refs.base == base
    assert manifest.refs.head == candidate
    assert not FOUNDATION_PROFILE_PATHS.intersection(
        path.as_posix() for path in manifest.unaccounted_tracked_paths
    )
    records = {
        item.candidate_id.artifact_relpath.as_posix(): item
        for item in manifest.candidates
        if item.candidate_id.artifact_relpath.as_posix() in FOUNDATION_PROFILE_PATHS
    }
    assert set(records) == FOUNDATION_PROFILE_PATHS
    assert all(
        item.inventory.value == "HUMAN_OWNED"
        and item.candidate_id.role == "human-maintained"
        and item.ownership_provenance == f"protected-ownership:pdd-maintainers:{path}"
        for path, item in records.items()
    )


def test_protected_base_pre_authorizes_absent_exact_child_paths(
    tmp_path: Path,
) -> None:
    """Known exact base rules safely classify later child-path additions."""
    ownership = json.loads(OWNERSHIP_PATH.read_text(encoding="utf-8"))
    rules = {row["pattern"]: row for row in ownership["rules"]}
    assert {path: rules.get(path) for path in PREAUTHORIZED_CHILD_PATHS} == {
        path: {
            "pattern": path,
            **PREAUTHORIZED_CHILD_OWNERSHIP,
        }
        for path in PREAUTHORIZED_CHILD_PATHS
    }
    root = tmp_path / "preauthorized-child-paths"
    subprocess.run(
        ["git", "clone", "-q", "--no-hardlinks", str(ROOT), str(root)],
        check=True,
        capture_output=True,
    )

    # A child PR can itself add a preauthorized path.  Build the protected base
    # explicitly so this regression continues to exercise absent-path routing
    # after such a child has merged into another branch.
    removed_existing_child_paths = False
    for path in PREAUTHORIZED_CHILD_PATHS:
        child_path = root / path
        if child_path.exists():
            _git(root, "rm", path)
            removed_existing_child_paths = True
    base = (
        _commit(root, "remove preauthorized child paths")
        if removed_existing_child_paths
        else subprocess.check_output(
            ["git", "rev-parse", "HEAD"], cwd=root, text=True
        ).strip()
    )
    baseline = build_unit_manifest(root, base_ref=base, head_ref=base)
    baseline_paths = {
        item.candidate_id.artifact_relpath.as_posix() for item in baseline.candidates
    }
    assert not PREAUTHORIZED_CHILD_PATHS.intersection(baseline_paths)
    baseline_denominator = len(baseline.expected_managed)

    for path in PREAUTHORIZED_CHILD_PATHS:
        child_path = root / path
        child_path.parent.mkdir(parents=True, exist_ok=True)
        child_path.write_text("# preauthorized child path\n", encoding="utf-8")
        # Some protected generated metadata paths are intentionally ignored in
        # ordinary development but remain valid exact rollout candidates.
        _git(root, "add", "-f", path)
    candidate = _commit(root, "add preauthorized child paths")

    manifest = build_unit_manifest(root, base_ref=base, head_ref=candidate)
    records = {
        item.candidate_id.artifact_relpath.as_posix(): item
        for item in manifest.candidates
        if item.candidate_id.artifact_relpath.as_posix() in PREAUTHORIZED_CHILD_PATHS
    }
    assert set(records) == PREAUTHORIZED_CHILD_PATHS
    for path, record in records.items():
        assert record.inventory.value == "HUMAN_OWNED"
        assert record.candidate_id.role == "human-maintained"
        assert not record.in_base and record.in_head
        assert record.ownership_provenance == (
            f"protected-ownership:pdd-maintainers:{path}"
        )
    assert not manifest.unaccounted_tracked_paths
    assert len(manifest.expected_managed) == baseline_denominator
