"""Protected PDD inventory rollout policy tests."""

from __future__ import annotations

import hashlib
import json
import re
import subprocess
from dataclasses import replace
from pathlib import Path, PurePosixPath

import pytest

from pdd.sync_core import build_unit_manifest, load_verification_profiles, verification
from pdd.sync_core import manifest as manifest_module
from pdd.sync_core.manifest import ManifestRefs
from pdd.sync_core.verification import PROFILE_PATH as PROFILE_REL_PATH


ROOT = Path(__file__).resolve().parents[1]
EXPECTED_PATH = ROOT / ".pdd" / "expected-managed.json"
OWNERSHIP_PATH = ROOT / ".pdd" / "sync-ownership.json"
PROFILE_FILE = ROOT / PROFILE_REL_PATH
ROTATION_FILE = ROOT / ".pdd" / "verification-profile-rotations.json"
REPOSITORY_ID = "3b4d7b1c-d6cc-4752-ba93-6b98d1a710e0"
EXPECTED_MANAGED_UNITS = 466
PROTECTED_BASE = "23ff583665b008b3d63d21ba57dad34e986fd5ae"
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
PREAUTHORIZED_CHILD_PATHS = {
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
UNAUTHORIZED_PR_METADATA_ADDITIONS = {
    ".pdd/meta/agentic_checkup_orchestrator_python_run.json",
    ".pdd/meta/code_generator_main_python_run.json",
    ".pdd/meta/fix_code_loop_python_run.json",
    ".pdd/meta/fix_error_loop_python_run.json",
    ".pdd/meta/get_test_command_python_run.json",
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
SYNC_DETERMINE_OPERATION_REQUIREMENT_ROTATION = {
    "prompt_path": "pdd/prompts/sync_determine_operation_python.prompt",
    "language_id": "python",
    "from_requirement_id": (
        "CONTRACT-SHA256:1dcdbb492c9bdd543fd6d07fcd712b4d9b939a26caf60c53e447514472c5c956"
    ),
    "to_requirement_id": (
        "CONTRACT-SHA256:015f38916d10072fb517102911d17143464321f4c2bf86fc69c049f42891602e"
    ),
    "policy_path": ".pdd/verification-profiles.json",
    "base_policy_sha256": (
        "fb18c71fedb583e092743c73301b68621c52382517aad96a1b6673e5c72b4bc6"
    ),
    "head_policy_sha256": (
        "e69feab07a0e6e2fba262805d5813a91f1cf50aedc203068fb0a45bb47da300e"
    ),
    "base_prompt_sha256": (
        "1dcdbb492c9bdd543fd6d07fcd712b4d9b939a26caf60c53e447514472c5c956"
    ),
    "head_prompt_sha256": (
        "015f38916d10072fb517102911d17143464321f4c2bf86fc69c049f42891602e"
    ),
}
SYNC_PROMPT_TRANSITION_APPEND = (
    " When the resolved prompt lives under a nested `.pddrc` `prompts_dir`, an "
    "architecture filename recorded relative to the repository prompt root "
    "(`<architecture root>/prompts`) MUST still select its matching architecture "
    "filepath before any `.pddrc` output fallback: the context-relative lookup is "
    "attempted first, and only a complete primary miss triggers a single retry "
    "keyed relative to the repository prompt root. Both lookup keys are computed "
    "lexically (no symlink resolution) so approved prompt-path aliases stay valid, "
    "and the retry MUST NOT activate when the prompt tree is not under "
    "`<architecture root>/prompts`. Each public `get_pdd_file_paths` resolution "
    "loads `architecture.json` exactly once and reuses that frozen module snapshot "
    "for ambiguity detection, prompt discovery, primary and alternate filepath "
    "selection, and example/test stem ambiguity decisions. An initial missing, "
    "unreadable, invalid, wrong-shaped, or empty architecture load is frozen as an "
    "empty snapshot and is not retried during that resolution. After a successful "
    "load, a later rewrite, invalidation, rename, or removal neither causes a reread "
    "nor disables snapshot-backed resolution. Standalone internal helpers called "
    "without a supplied snapshot may preserve their existing safe read behavior."
)


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
    return subprocess.check_output(["git", "rev-parse", "HEAD"], cwd=root, text=True).strip()


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


def _sync_transition_bytes() -> tuple[bytes, bytes, bytes, bytes]:
    """Return the exact protected and reviewed future prompt/profile bytes."""
    prompt_path = ROOT / SYNC_DETERMINE_OPERATION_REQUIREMENT_ROTATION["prompt_path"]
    base_prompt = prompt_path.read_bytes()
    marker = b"fallback path.\n"
    assert base_prompt.count(marker) == 1
    head_prompt = base_prompt.replace(
        marker,
        b"fallback path." + SYNC_PROMPT_TRANSITION_APPEND.encode("utf-8") + b"\n",
    )
    base_profile = PROFILE_FILE.read_bytes()
    profile = json.loads(base_profile)
    requirement = SYNC_DETERMINE_OPERATION_REQUIREMENT_ROTATION["to_requirement_id"]
    rows = [
        row
        for row in profile["profiles"]
        if row["prompt_path"]
        == SYNC_DETERMINE_OPERATION_REQUIREMENT_ROTATION["prompt_path"]
        and row["language_id"] == "python"
    ]
    assert len(rows) == 1
    rows[0]["required_requirement_ids"] = [requirement]
    human = [
        item
        for item in rows[0]["obligations"]
        if item["obligation_id"] == "threshold-human-attestation"
    ]
    assert len(human) == 1
    human[0]["requirement_ids"] = [requirement]
    head_profile = (json.dumps(profile, indent=2) + "\n").encode("utf-8")
    return base_prompt, head_prompt, base_profile, head_profile


def _rotation_bytes_without_sync_rule() -> bytes:
    """Return the protected policy immediately before this bootstrap install."""
    policy = json.loads(ROTATION_FILE.read_text(encoding="utf-8"))
    policy["requirement_rotations"] = [
        row
        for row in policy["requirement_rotations"]
        if row["prompt_path"]
        != SYNC_DETERMINE_OPERATION_REQUIREMENT_ROTATION["prompt_path"]
    ]
    return (json.dumps(policy, indent=2) + "\n").encode("utf-8")


def _load_sync_transition_profiles(
    monkeypatch,
    *,
    protected_rotation: bytes,
    candidate_rotation: bytes,
    candidate_prompt: bytes,
    candidate_profile: bytes,
):
    """Load one exact repository transition through synthetic protected refs."""
    base_prompt, _head_prompt, base_profile, _head_profile = _sync_transition_bytes()
    manifest = build_unit_manifest(ROOT, base_ref="HEAD", head_ref="HEAD")
    manifest = replace(manifest, refs=ManifestRefs("protected-base", "candidate-head"))

    def exact_read(_root: Path, ref: str, path: PurePosixPath) -> bytes | None:
        if path == verification.ROTATION_POLICY_PATH:
            return protected_rotation if ref == "protected-base" else candidate_rotation
        if path == PROFILE_REL_PATH:
            return base_profile if ref == "protected-base" else candidate_profile
        if (
            path.as_posix()
            == SYNC_DETERMINE_OPERATION_REQUIREMENT_ROTATION["prompt_path"]
        ):
            return base_prompt if ref == "protected-base" else candidate_prompt
        resolved = ROOT / path
        return resolved.read_bytes() if resolved.is_file() else None

    monkeypatch.setattr(verification, "read_git_blob", exact_read)
    monkeypatch.setattr(
        verification,
        "read_git_blob_bounded",
        lambda root, ref, path, _max_bytes: exact_read(root, ref, path),
    )
    return load_verification_profiles(ROOT, manifest)


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
        set(row) in (
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
    tracked = subprocess.check_output(
        ["git", "ls-tree", "-r", "-z", "--name-only", "HEAD"], cwd=ROOT
    ).decode("utf-8").split("\0")[:-1]
    assert {
        item.candidate_id.artifact_relpath.as_posix()
        for item in manifest.candidates
    } == set(tracked)


def test_pr_transition_has_complete_protected_inventory_and_profiles() -> None:
    """The exact protected rollout transition cannot self-authorize new metadata."""
    manifest = build_unit_manifest(ROOT, base_ref=PROTECTED_BASE, head_ref="HEAD")
    tracked = {
        path
        for path in subprocess.check_output(
            ["git", "ls-tree", "-r", "-z", "--name-only", "HEAD"], cwd=ROOT
        )
        .decode("utf-8")
        .split("\0")
        if path
    }

    assert not UNAUTHORIZED_PR_METADATA_ADDITIONS.intersection(tracked)
    assert not manifest.invalid_reasons
    assert not manifest.unaccounted_tracked_paths
    profiles = load_verification_profiles(ROOT, manifest)
    assert len(profiles.profiles) == EXPECTED_MANAGED_UNITS
    assert profiles.coverage == 1.0
    assert not profiles.invalid_reasons


def test_agentic_langtest_metadata_bootstrap_is_exactly_bound() -> None:
    # pylint: disable=protected-access
    """The one-time authority accepts only its exact repository transition."""
    authorization = manifest_module._PDD_AGENTIC_LANGTEST_METADATA_BOOTSTRAP
    protected = manifest_module._ownership_rules(ROOT, PROTECTED_BASE)
    protected_patterns = {rule.pattern for rule in protected}
    protected_only_paths = {
        ".github/toolchains/vitest/package.json",
        ".github/toolchains/vitest/package-lock.json",
        "tests/test_ci_drift_heal_example_contract.py",
    }
    assert protected_only_paths.issubset(protected_patterns)
    assert protected_only_paths.isdisjoint(
        rule.pattern for rule in authorization.rules
    )
    expected = {
        replace(rule, preauthorize_absent=True) for rule in authorization.rules
    }

    def invoke(
        auth=authorization,
        repository_id=REPOSITORY_ID,
        base=PROTECTED_BASE,
    ):
        return set(
            manifest_module._bootstrap_ownership_rules(
                ROOT, repository_id, base, "HEAD", protected, auth
            )
        )

    assert invoke() == expected
    assert not invoke(repository_id="wrong-repository")
    assert not invoke(base="HEAD")
    assert not invoke(replace(authorization, base_policy_sha256="0" * 64))
    assert not invoke(replace(authorization, head_policy_sha256="0" * 64))
    wrong_path = replace(
        authorization,
        blob_sha256=((PurePosixPath(".pdd/meta/unrelated.json"), "0" * 64),),
    )
    assert not invoke(wrong_path)
    wrong_blob = replace(
        authorization,
        blob_sha256=((authorization.blob_sha256[0][0], "0" * 64),),
    )
    assert not invoke(wrong_blob)
    for field, value in (
        ("owner", "candidate"),
        ("role", "generated"),
        ("inventory", manifest_module.InventoryStatus.MANAGED),
    ):
        changed_rule = replace(authorization.rules[0], **{field: value})
        assert not invoke(replace(authorization, rules=(changed_rule,)))


def test_consumed_metadata_bootstrap_does_not_reopen_candidate_authority(
    tmp_path: Path,
) -> None:
    """A protected metadata rollout remains stable but cannot bless another path."""
    stable = build_unit_manifest(ROOT, base_ref="HEAD", head_ref="HEAD")
    assert not stable.invalid_reasons
    records = {
        item.candidate_id.artifact_relpath.as_posix(): item
        for item in stable.candidates
        if item.candidate_id.artifact_relpath.as_posix()
        in {
            ".pdd/meta/agentic_langtest_python.json",
            ".pdd/meta/agentic_langtest_python_run.json",
        }
    }
    assert len(records) == 2
    assert all(item.inventory.value == "HUMAN_OWNED" for item in records.values())

    root = tmp_path / "consumed-bootstrap"
    subprocess.run(
        ["git", "clone", "-q", "--no-hardlinks", str(ROOT), str(root)],
        check=True,
        capture_output=True,
    )
    base = subprocess.check_output(
        ["git", "rev-parse", "HEAD"], cwd=root, text=True
    ).strip()
    policy_path = root / ".pdd/sync-ownership.json"
    policy = json.loads(policy_path.read_text(encoding="utf-8"))
    policy["rules"].append(
        {
            "pattern": ".pdd/meta/unrelated.json",
            "inventory": "HUMAN_OWNED",
            "role": "human-maintained",
            "owner": "pdd-maintainers",
        }
    )
    policy_path.write_text(json.dumps(policy), encoding="utf-8")
    unrelated = root / ".pdd/meta/unrelated.json"
    unrelated.write_text("{}\n", encoding="utf-8")
    _git(root, "add", "-f", ".pdd/meta/unrelated.json", ".pdd/sync-ownership.json")
    candidate = _commit(root, "candidate self-authorizes unrelated metadata")

    manifest = build_unit_manifest(root, base_ref=base, head_ref=candidate)
    assert PurePosixPath(".pdd/meta/unrelated.json") in (
        manifest.unaccounted_tracked_paths
    )


def test_detector_contract_rotation_is_exact_and_dormant() -> None:
    """Preauthorize only the reviewed future detector prompt/profile bytes."""
    policy = json.loads(ROTATION_FILE.read_text(encoding="utf-8"))
    rules = policy["requirement_rotations"]
    detector_rules = [
        row
        for row in rules
        if row["prompt_path"]
        == "pdd/prompts/ci_detect_changed_modules_python.prompt"
    ]
    assert detector_rules == [CI_DETECT_REQUIREMENT_ROTATION]
    prompt = ROOT / CI_DETECT_REQUIREMENT_ROTATION["prompt_path"]
    assert hashlib.sha256(prompt.read_bytes()).hexdigest() == (
        CI_DETECT_REQUIREMENT_ROTATION["base_prompt_sha256"]
    )

    manifest = build_unit_manifest(ROOT, base_ref="HEAD", head_ref="HEAD")
    profiles = load_verification_profiles(ROOT, manifest)
    assert not profiles.invalid_reasons
    assert profiles.coverage == 1.0


def test_sync_contract_transition_bootstrap_is_exact_and_dormant(
    monkeypatch,
) -> None:
    # pylint: disable=protected-access
    """Install only the reviewed transition and keep it dormant at base bytes."""
    policy_bytes = ROTATION_FILE.read_bytes()
    policy = json.loads(policy_bytes)
    rules = [
        row
        for row in policy["requirement_rotations"]
        if row["prompt_path"]
        == SYNC_DETERMINE_OPERATION_REQUIREMENT_ROTATION["prompt_path"]
    ]
    assert rules == [SYNC_DETERMINE_OPERATION_REQUIREMENT_ROTATION]

    bootstrap = [
        item
        for item in verification._BOOTSTRAP_REQUIREMENT_TRANSITIONS
        if item.prompt_path.as_posix()
        == SYNC_DETERMINE_OPERATION_REQUIREMENT_ROTATION["prompt_path"]
    ]
    assert len(bootstrap) == 1
    rule = bootstrap[0]
    expected = SYNC_DETERMINE_OPERATION_REQUIREMENT_ROTATION
    assert rule.language_id == expected["language_id"]
    assert rule.from_requirement_id == expected["from_requirement_id"]
    assert rule.to_requirement_id == expected["to_requirement_id"]
    assert rule.policy_path.as_posix() == expected["policy_path"]
    assert rule.bindings.base_policy_sha256 == expected["base_policy_sha256"]
    assert rule.bindings.head_policy_sha256 == expected["head_policy_sha256"]
    assert rule.bindings.base_prompt_sha256 == expected["base_prompt_sha256"]
    assert rule.bindings.head_prompt_sha256 == expected["head_prompt_sha256"]

    base_prompt, head_prompt, base_profile, head_profile = _sync_transition_bytes()
    assert hashlib.sha256(base_prompt).hexdigest() == expected["base_prompt_sha256"]
    assert hashlib.sha256(head_prompt).hexdigest() == expected["head_prompt_sha256"]
    assert hashlib.sha256(base_profile).hexdigest() == expected["base_policy_sha256"]
    assert hashlib.sha256(head_profile).hexdigest() == expected["head_policy_sha256"]

    first_install = _load_sync_transition_profiles(
        monkeypatch,
        protected_rotation=_rotation_bytes_without_sync_rule(),
        candidate_rotation=policy_bytes,
        candidate_prompt=base_prompt,
        candidate_profile=base_profile,
    )
    assert first_install.coverage == 1.0
    assert not first_install.invalid_reasons

    dormant = _load_sync_transition_profiles(
        monkeypatch,
        protected_rotation=policy_bytes,
        candidate_rotation=policy_bytes,
        candidate_prompt=base_prompt,
        candidate_profile=base_profile,
    )
    assert dormant.coverage == 1.0
    assert not dormant.invalid_reasons


@pytest.mark.parametrize("wrong_bytes", ["prompt", "profile"])
def test_sync_contract_transition_rejects_wrong_bound_bytes(
    monkeypatch, wrong_bytes: str
) -> None:
    """The future grant cannot consume prompt or profile bytes outside its hashes."""
    base_prompt, head_prompt, base_profile, head_profile = _sync_transition_bytes()
    if wrong_bytes == "prompt":
        head_prompt += b" "
    else:
        head_profile += b" "
    policy_bytes = ROTATION_FILE.read_bytes()

    profiles = _load_sync_transition_profiles(
        monkeypatch,
        protected_rotation=policy_bytes,
        candidate_rotation=policy_bytes,
        candidate_prompt=head_prompt,
        candidate_profile=head_profile,
    )

    authorization = next(
        item
        for item in verification._BOOTSTRAP_REQUIREMENT_TRANSITIONS
        if item.prompt_path.as_posix()
        == SYNC_DETERMINE_OPERATION_REQUIREMENT_ROTATION["prompt_path"]
    )
    assert not verification._transition_bytes_match(
        authorization,
        base_profile,
        head_profile,
        base_prompt,
        head_prompt,
    )
    expected_reason = (
        "profile requirements do not match immutable prompt requirements"
        if wrong_bytes == "prompt"
        else "requirement transition bindings mismatch"
    )
    assert any(expected_reason in reason for reason in profiles.invalid_reasons)


def test_sync_contract_candidate_cannot_self_authorize(monkeypatch) -> None:
    """A candidate-only rule outside the bootstrap cannot grant itself authority."""
    base_prompt, _head_prompt, base_profile, _head_profile = _sync_transition_bytes()
    policy = json.loads(ROTATION_FILE.read_text(encoding="utf-8"))
    rule = next(
        row
        for row in policy["requirement_rotations"]
        if row["prompt_path"]
        == SYNC_DETERMINE_OPERATION_REQUIREMENT_ROTATION["prompt_path"]
    )
    rule["head_prompt_sha256"] = "0" * 64
    candidate_rotation = (json.dumps(policy, indent=2) + "\n").encode("utf-8")

    with pytest.raises(
        verification.VerificationProfileError,
        match="candidate requirement transition lacks protected authorization",
    ):
        _load_sync_transition_profiles(
            monkeypatch,
            protected_rotation=_rotation_bytes_without_sync_rule(),
            candidate_rotation=candidate_rotation,
            candidate_prompt=base_prompt,
            candidate_profile=base_profile,
        )


def test_sync_contract_exact_future_consumption_succeeds(monkeypatch) -> None:
    """The exact future prompt and profile replacement consumes protected authority."""
    _base_prompt, head_prompt, _base_profile, head_profile = _sync_transition_bytes()
    policy_bytes = ROTATION_FILE.read_bytes()

    profiles = _load_sync_transition_profiles(
        monkeypatch,
        protected_rotation=policy_bytes,
        candidate_rotation=policy_bytes,
        candidate_prompt=head_prompt,
        candidate_profile=head_profile,
    )

    assert profiles.coverage == 1.0
    assert not profiles.invalid_reasons
    sync_profile = next(
        profile
        for profile in profiles.profiles
        if profile.unit_id.prompt_relpath.as_posix()
        == SYNC_DETERMINE_OPERATION_REQUIREMENT_ROTATION["prompt_path"]
    )
    assert sync_profile.required_requirement_ids == (
        SYNC_DETERMINE_OPERATION_REQUIREMENT_ROTATION["to_requirement_id"],
    )


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


def test_exact_working_tree_prompt_transitions_are_fully_covered(monkeypatch) -> None:
    """The exact base-to-working-tree transitions preserve full coverage."""
    manifest = build_unit_manifest(ROOT, base_ref="HEAD", head_ref="HEAD")
    candidate_manifest = replace(
        manifest, refs=ManifestRefs("protected-base", "candidate-working-tree")
    )

    def exact_read(_root: Path, ref: str, path: PurePosixPath) -> bytes | None:
        if ref == "candidate-working-tree":
            candidate = ROOT / path
            return candidate.read_bytes() if candidate.is_file() else None
        try:
            return subprocess.check_output(
                ["git", "show", f"{PROTECTED_BASE}:{path.as_posix()}"],
                cwd=ROOT,
            )
        except subprocess.CalledProcessError:
            return None

    monkeypatch.setattr(verification, "read_git_blob", exact_read)
    monkeypatch.setattr(
        verification,
        "read_git_blob_bounded",
        lambda root, ref, path, _max_bytes: exact_read(root, ref, path),
    )

    profiles = load_verification_profiles(ROOT, candidate_manifest)
    rotations = json.loads(ROTATION_FILE.read_text(encoding="utf-8"))[
        "requirement_rotations"
    ]

    assert profiles.coverage == 1.0
    assert len(profiles.profiles) == EXPECTED_MANAGED_UNITS
    assert not profiles.invalid_reasons
    assert {rotation["prompt_path"] for rotation in rotations} == {
        "pdd/prompts/ci_drift_heal_python.prompt",
        "pdd/prompts/ci_detect_changed_modules_python.prompt",
        "pdd/prompts/agentic_langtest_python.prompt",
        "pdd/prompts/fix_error_loop_python.prompt",
        "pdd/prompts/get_test_command_python.prompt",
        "pdd/prompts/sync_determine_operation_python.prompt",
    }
    assert len(rotations) == 6


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
    monkeypatch.setattr(
        verification,
        "read_git_blob_bounded",
        lambda root, ref, path, _max_bytes: candidate_only_read(root, ref, path),
    )
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
                "units": [{"prompt_path": "prompts/owned_python.prompt", "language_id": "python"}],
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
    (root / ".pdd" / "repository-id").write_text(
        f"{REPOSITORY_ID}\n", encoding="ascii"
    )
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
    (root / "prompts" / "owned_python.prompt").write_text(
        "owned", encoding="utf-8"
    )
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
        and item.ownership_provenance
        == f"protected-ownership:pdd-maintainers:{path}"
        for path, item in records.items()
    )


def test_protected_base_pre_authorizes_absent_exact_child_paths(
    tmp_path: Path,
) -> None:
    """Known exact base rules safely classify later child-path additions."""
    ownership = json.loads(OWNERSHIP_PATH.read_text(encoding="utf-8"))
    rules = {row["pattern"]: row for row in ownership["rules"]}
    assert {
        path: rules.get(path)
        for path in PREAUTHORIZED_CHILD_PATHS
    } == {
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
        item.candidate_id.artifact_relpath.as_posix()
        for item in baseline.candidates
    }
    assert not PREAUTHORIZED_CHILD_PATHS.intersection(baseline_paths)
    baseline_denominator = len(baseline.expected_managed)

    for path in PREAUTHORIZED_CHILD_PATHS:
        child_path = root / path
        child_path.parent.mkdir(parents=True, exist_ok=True)
        child_path.write_text("# preauthorized child path\n", encoding="utf-8")
        _git(root, "add", path)
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
