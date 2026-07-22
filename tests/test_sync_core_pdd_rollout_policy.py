"""Protected PDD inventory rollout policy tests."""

from __future__ import annotations

import hashlib
import io
import json
import re
import subprocess
import sys
import tarfile
from dataclasses import replace
from pathlib import Path, PurePosixPath
from types import SimpleNamespace

import pytest

from pdd.sync_core import build_unit_manifest, load_verification_profiles, verification
from pdd.sync_core import decommission as decommission_module
from pdd.sync_core import manifest as manifest_module
from pdd.sync_core.manifest import (
    ManifestRefs,
    OwnershipRule,
    _BOOTSTRAP_HUMAN_OWNERSHIP,  # pylint: disable=protected-access
    _REPLAY_HUMAN_OWNERSHIP,  # pylint: disable=protected-access
    _bootstrap_ownership_rules,  # pylint: disable=protected-access
    _replay_bootstrap_weakenings,  # pylint: disable=protected-access
)
from pdd.sync_core.types import InventoryStatus, UnitId
from pdd.sync_core.verification import PROFILE_PATH as PROFILE_REL_PATH
from tests.conftest import (
    authenticated_candidate_missing_refs,
    skip_if_authenticated_candidate_lacks_refs,
)


ROOT = Path(__file__).resolve().parents[1]
EXPECTED_PATH = ROOT / ".pdd" / "expected-managed.json"
OWNERSHIP_PATH = ROOT / ".pdd" / "sync-ownership.json"
PROFILE_FILE = ROOT / PROFILE_REL_PATH
ROTATION_FILE = ROOT / ".pdd" / "verification-profile-rotations.json"
REPOSITORY_ID = "3b4d7b1c-d6cc-4752-ba93-6b98d1a710e0"
EXPECTED_MANAGED_UNITS = 469
# #1989's dormant-bootstrap assertions retain their original immutable base;
# the replay audit intentionally binds to the current main that it was rebased
# onto.
PDD_1989_ACTUAL_BASE = "39a60ec06dc065a70ad63077b6f873aca95cbf45"
PDD_1989_ACTUAL_HEAD = "131f86d83e7f2058af861b8ee7bde432bbbf5027"
PR_2017_PHASE_A_BASE = "c887daba0d171585658f8205e79316e5f36f82c6"
PR_2017_PHASE_A_HEAD = "2cacc91f90759ff45f1ad976da3b773e1a5f07a5"
REPLAY_PROTECTED_BASE = "e10bd9b3d0d5ac94d1a56af88f5abf07cf8af775"
PR_1971_COMBINED_BASE = "ee9fcff457b23fb7123bb7e15666c9287409ad0f"
PR_1971_COMBINED_HEAD = REPLAY_PROTECTED_BASE
PDD_1875_PROTECTED_BASE = "eb1fc0e2ad14c1bd79e63cabe4fd6bc90c7929a5"
PR_1971_COMBINED_PROFILE_DIGEST = (
    "c566e1b87015632ca317e799f2756af9a25281c6e842c03ccad763b20d539bf1"
)
PR_1971_PYTEST_OBLIGATIONS = {
    "pdd/prompts/operation_log_python.prompt": {
        "obligation_id": "pytest-operation-log",
        "tests": ("tests/test_operation_log.py",),
        "code": ("pdd/operation_log.py",),
    },
    "pdd/prompts/server/routes/prompts_python.prompt": {
        "obligation_id": "pytest-server-routes-prompts",
        "tests": ("tests/server/routes/test_prompts.py",),
        "code": ("pdd/server/routes/prompts.py",),
    },
    "pdd/prompts/update_main_python.prompt": {
        "obligation_id": "pytest-update-main",
        "tests": ("tests/test_update_main.py",),
        "code": ("pdd/update_main.py",),
    },
}
PDD_1989_EXPECTED_MANAGED_UNITS = 468
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
    "382da1a7f9a6c94ad9c010792d0bcce2435663ddd4e7f42c3537c324be2643c9"
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
ISSUE_2083_VITEST_COORDINATOR_PREAUTHORIZED_PATHS = {
    "pdd/sync_core/native/vitest_fd_cloexec.c",
    "scripts/build_vitest_fd_cloexec_addon.py",
    "setup.py",
}
GATE1_PREAUTHORIZED_PATHS = {
    "docs/global_sync_extraction_manifest.md",
    "docs/global_sync_pdd_adapter_demand.json",
    "pdd/sync_core/adapter_demand_verifier.py",
    "tests/test_sync_core_adapter_demand_verifier.py",
}
GATE1_EXISTING_HUMAN_PATHS = {
    "docs/global_sync_evidence_ledger.yaml",
    "docs/global_sync_resolution_plan.md",
}
GATE1_CHANGED_PATHS = GATE1_PREAUTHORIZED_PATHS | GATE1_EXISTING_HUMAN_PATHS
GLOBAL_SYNC_LEDGER_PREAUTHORIZED_PATHS = {
    "docs/global_sync_evidence_ledger_source.yaml",
    "pdd/sync_core/global_sync_ledger.py",
    "tests/test_global_sync_ledger.py",
}
GLOBAL_SYNC_RUNTIME_LOCK_PREAUTHORIZED_PATHS = {
    ".pdd/global-sync/runtime-linux-x86_64-cp312.lock",
}
STANDALONE_CHECKER_PREAUTHORIZED_PATHS = {
    ".pdd/global-sync/standalone-checker-modules.json",
    "pdd/sync_core/standalone_package.py",
    "pdd/sync_core/checker_cli.py",
    "tests/test_sync_core_standalone_package.py",
    "tests/test_sync_core_checker_cli.py",
}
STANDALONE_CHECKER_GLOBAL_SYNC_PREAUTHORIZED_PATHS = {
    ".pdd/global-sync/standalone-checker-modules.json",
}
FUTURE_STANDALONE_CHECKER_AUTHORITY_PREFIXES = (
    ".pdd/global-sync/standalone-checker-",
    ".pdd/global-sync/gate2-",
    ".pdd/global-sync/oci-",
    ".pdd/global-sync/release-",
    ".pdd/global-sync/gate3-",
    ".pdd/global-sync/certificate-a-",
    "pdd/sync_core/checker_",
    "pdd/sync_core/standalone_",
    "pdd/sync_core/gate2_",
    "pdd/sync_core/oci_",
    "pdd/sync_core/release_",
    "pdd/sync_core/gate3_",
    "pdd/sync_core/certificate_a",
    "tests/test_sync_core_checker_",
    "tests/test_sync_core_standalone_",
    "tests/test_sync_core_gate2_",
    "tests/test_sync_core_oci_",
    "tests/test_sync_core_release_",
    "tests/test_sync_core_gate3_",
    "tests/test_sync_core_certificate_a",
)
FUTURE_STANDALONE_CHECKER_UNAUTHORIZED_PATHS = {
    ".pdd/global-sync/gate2-checker-release.json",
    ".pdd/global-sync/oci-checker-runtime.json",
    ".pdd/global-sync/release-checker-pin.json",
    ".pdd/global-sync/gate3-checker-pins.json",
    ".pdd/global-sync/certificate-a-checker.json",
}
PR_2017_ABSENT_METADATA_PATHS = {
    ".pdd/meta/agentic_langtest_python.json",
    ".pdd/meta/agentic_langtest_python_run.json",
    ".pdd/meta/code_generator_main_python_run.json",
    ".pdd/meta/fix_code_loop_python_run.json",
    ".pdd/meta/fix_error_loop_python_run.json",
    ".pdd/meta/get_test_command_python_run.json",
}
PREAUTHORIZED_CHILD_PATHS = (
    LEGACY_METADATA_EXAMPLE_PREAUTHORIZED_PATHS
    | ISSUE_2083_VITEST_COORDINATOR_PREAUTHORIZED_PATHS
    | GATE1_PREAUTHORIZED_PATHS
    | GLOBAL_SYNC_LEDGER_PREAUTHORIZED_PATHS
    | GLOBAL_SYNC_RUNTIME_LOCK_PREAUTHORIZED_PATHS
    | STANDALONE_CHECKER_PREAUTHORIZED_PATHS
    | PR_2017_ABSENT_METADATA_PATHS
    | {
        ".pdd/meta/user_story_tests_python.json",
        ".pdd/meta/user_story_tests_python_run.json",
        ".github/toolchains/playwright_manifest.py",
        ".pdd/meta/agentic_checkup_orchestrator_python_run.json",
        ".pdd/meta/checkup_agentic_artifact_python.json",
        ".pdd/meta/story_regression_python.json",
        "ci/cloud-batch/cloud-regression-runner.py",
        "context/checkup_agentic_artifact_example.py",
        "tests/test_checkup_agentic_artifact.py",
        "tests/test_cloud_batch_cloud_regression_runner.py",
        "tests/test_unit_tests_workflow.py",
        "tests/test_ci_drift_heal_example_contract.py",
        "tests/test_sync_core_runner_jest.py",
        "tests/test_sync_core_runner_vitest.py",
        "tests/test_sync_core_runner_playwright.py",
        "tests/test_cloud_global_dry_run.py",
        "tests/test_continuous_sync_path_policy.py",
        "pdd/sync_core/human_attestation.py",
        "tests/test_sync_core_human_attestation.py",
        ".pdd/meta/ci_detect_changed_modules_python.json",
        ".pdd/meta/evidence_manifest_python.json",
        ".pdd/meta/story_detection_result_python.json",
        "pdd/schemas/story_detection_result.schema.json",
        "pdd/schemas/story_detection_scope.schema.json",
        "scripts/manual_validate_pr_1875.py",
        "tests/test_e2e_story_failure_diagnostics.py",
        "tests/test_story_detection_result.py",
    }
)
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
STORY_REGRESSION_DORMANT_ROTATION = {
    "prompt_path": "pdd/prompts/story_regression_python.prompt",
    "language_id": "python",
    "from_requirement_id": (
        "CONTRACT-SHA256:88ba7a932f444bb1b91e17429ca8c211742fadc8457b96d71b648b2529785d4f"
    ),
    "to_requirement_id": (
        "CONTRACT-SHA256:fbd4c2c6592bcb6950868a6b57691a66c2c3cd16d0ffd4a39abf3081ba613931"
    ),
    "policy_path": ".pdd/verification-profiles.json",
    "base_policy_sha256": (
        "71b12a08e5be55b958a737decde889c189f7ca00ceaddccd7b587f9c8b2a4b64"
    ),
    "head_policy_sha256": (
        "56ea5d189034c9d85e91c86348689eb18c4c34fa67406258f78f0ae3330eaeb6"
    ),
    "base_prompt_sha256": (
        "88ba7a932f444bb1b91e17429ca8c211742fadc8457b96d71b648b2529785d4f"
    ),
    "head_prompt_sha256": (
        "fbd4c2c6592bcb6950868a6b57691a66c2c3cd16d0ffd4a39abf3081ba613931"
    ),
}
LEGACY_SCHEMA_1_REQUIREMENT_ROTATION = {
    "prompt_path": "pdd/prompts/ci_detect_changed_modules_python.prompt",
    "language_id": "python",
    "from_requirement_id": (
        "CONTRACT-SHA256:ef30764861a3080d2fb093ca747f86a3f46bba733a0cdc6a5634efc1b36a73a2"
    ),
    "to_requirement_id": (
        "CONTRACT-SHA256:2d5d65f695fc6c8cd2f3e82f5c5d2a55ad3eb30fc4791b2a1d94ff8465ab6d10"
    ),
    "policy_path": ".pdd/verification-profiles.json",
    "from_policy_sha256": (
        "ffd867088a7c9a92840130ffd9db9eb8f279e611a02afe501d02855ebb03930f"
    ),
    "to_policy_sha256": (
        "8a957dfa94fdc78ec9d1eb5ea6dfb0a08ff2452928a8b9f6a4dbd5368cb25f53"
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


def _synthetic_current_tree_repo(root: Path) -> str:
    """Recommit current tracked bytes without requiring candidate ancestors."""
    root.mkdir()
    archive = subprocess.check_output(["git", "archive", "HEAD"], cwd=ROOT)
    with tarfile.open(fileobj=io.BytesIO(archive), mode="r:") as source:
        source.extractall(root, filter="data")
    _git(root, "init", "-q")
    _git(root, "add", "-f", ".")
    _git(
        root,
        "-c",
        "user.name=PDD test",
        "-c",
        "user.email=pdd@example.test",
        "commit",
        "-qm",
        "synthetic current tree",
    )
    base = subprocess.check_output(
        ["git", "rev-parse", "HEAD"], cwd=root, text=True
    ).strip()
    _git(root, "update-ref", "refs/remotes/origin/main", base)
    return base


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


def test_story_regression_transition_is_exact_and_consumed() -> None:
    """Consume only the exact #2204-protected prompt/profile transition."""
    skip_if_authenticated_candidate_lacks_refs(
        ROOT, "exact replay history", REPLAY_PROTECTED_BASE
    )
    policy = json.loads(ROTATION_FILE.read_text(encoding="utf-8"))
    rows = [
        row
        for row in policy["requirement_rotations"]
        if row["prompt_path"] == STORY_REGRESSION_DORMANT_ROTATION["prompt_path"]
    ]
    assert rows == [STORY_REGRESSION_DORMANT_ROTATION]

    prompt_bytes = subprocess.check_output(
        [
            "git",
            "show",
            f"{REPLAY_PROTECTED_BASE}:{STORY_REGRESSION_DORMANT_ROTATION['prompt_path']}",
        ],
        cwd=ROOT,
    )
    profile_bytes = subprocess.check_output(
        [
            "git",
            "show",
            f"{REPLAY_PROTECTED_BASE}:{PROFILE_REL_PATH.as_posix()}",
        ],
        cwd=ROOT,
    )
    prompt_digest = hashlib.sha256(prompt_bytes).hexdigest()
    profile_digest = hashlib.sha256(profile_bytes).hexdigest()
    assert prompt_digest != STORY_REGRESSION_DORMANT_ROTATION["base_prompt_sha256"]
    assert prompt_digest == STORY_REGRESSION_DORMANT_ROTATION["head_prompt_sha256"]
    assert profile_digest != STORY_REGRESSION_DORMANT_ROTATION["base_policy_sha256"]
    # The row remains the exact historical transition, while the replay base
    # is now current main and therefore has its subsequently composed profile.
    assert (
        profile_digest
        == "c566e1b87015632ca317e799f2756af9a25281c6e842c03ccad763b20d539bf1"
    )

    protected_policy = json.loads(
        subprocess.check_output(
            [
                "git",
                "show",
                f"{REPLAY_PROTECTED_BASE}:.pdd/verification-profile-rotations.json",
            ],
            cwd=ROOT,
            text=True,
        )
    )
    pdd1989_rows = [
        row
        for row in protected_policy["requirement_rotations"]
        if row["head_policy_sha256"]
        == STORY_REGRESSION_DORMANT_ROTATION["base_policy_sha256"]
    ]
    assert len(pdd1989_rows) == 7
    assert {row["prompt_path"] for row in pdd1989_rows} == {
        "pdd/prompts/agentic_common_python.prompt",
        "pdd/prompts/commands/checkup_python.prompt",
        "pdd/prompts/generate_model_catalog_python.prompt",
        "pdd/prompts/llm_invoke_python.prompt",
        "pdd/prompts/prompt_repair_python.prompt",
        "pdd/prompts/routing_policy_python.prompt",
        "pdd/prompts/setup_tool_python.prompt",
    }
    assert {row["base_policy_sha256"] for row in pdd1989_rows} == {
        "f0f1d36e337541ba4425f081e236c42847f8132cb61f9f8fe06334a805fc5c7b"
    }


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


@pytest.mark.parametrize(
    "mutated_input",
    ("base_policy", "candidate_policy", "base_profile", "candidate_profile"),
)
def test_pdd1875_composed_reconciliation_is_exact(mutated_input: str) -> None:
    """The #2260 gate rejects a byte mutation on every reviewed boundary."""
    skip_if_authenticated_candidate_lacks_refs(
        ROOT, "exact #1875 protected history", PDD_1875_PROTECTED_BASE
    )
    inputs = {
        "base_policy": _git_blob(
            PDD_1875_PROTECTED_BASE,
            ROOT / ".pdd/verification-profile-rotations.json",
        ),
        "candidate_policy": ROTATION_FILE.read_bytes(),
        "base_profile": _git_blob(PDD_1875_PROTECTED_BASE, PROFILE_FILE),
        "candidate_profile": PROFILE_FILE.read_bytes(),
    }

    assert verification._is_exact_combined_requirement_reconciliation(  # pylint: disable=protected-access
        inputs["base_policy"],
        inputs["candidate_policy"],
        inputs["base_profile"],
        inputs["candidate_profile"],
    )
    inputs[mutated_input] += b" "
    assert not verification._is_exact_combined_requirement_reconciliation(  # pylint: disable=protected-access
        inputs["base_policy"],
        inputs["candidate_policy"],
        inputs["base_profile"],
        inputs["candidate_profile"],
    )


@pytest.mark.parametrize(
    "authorization",
    verification._PDD_1875_COMPOSED_REQUIREMENT_TRANSITIONS,  # pylint: disable=protected-access
    ids=lambda item: item.prompt_path.name,
)
def test_pdd1875_composed_reconciliation_binds_prompt_bytes(authorization) -> None:
    """Each reviewed profile transition remains bound to its exact prompt pair."""
    skip_if_authenticated_candidate_lacks_refs(
        ROOT, "exact #1875 protected history", PDD_1875_PROTECTED_BASE
    )
    base_profile = _git_blob(PDD_1875_PROTECTED_BASE, PROFILE_FILE)
    candidate_profile = PROFILE_FILE.read_bytes()
    base_prompt = _git_blob(PDD_1875_PROTECTED_BASE, ROOT / authorization.prompt_path)
    candidate_prompt = (ROOT / authorization.prompt_path).read_bytes()

    assert verification._transition_bytes_match(  # pylint: disable=protected-access
        authorization,
        base_profile,
        candidate_profile,
        base_prompt,
        candidate_prompt,
    )
    assert not verification._transition_bytes_match(  # pylint: disable=protected-access
        authorization,
        base_profile,
        candidate_profile,
        base_prompt,
        candidate_prompt + b" ",
    )


def _git_blob(ref: str, path: Path) -> bytes:
    """Read one historical policy byte sequence without rewriting it."""
    return subprocess.check_output(
        ["git", "show", f"{ref}:{path.relative_to(ROOT)}"], cwd=ROOT
    )


def test_pr1971_combined_profile_reconciliation_is_exact() -> None:
    """Retain #1971's four-byte reconciliation, independent of this replay."""
    skip_if_authenticated_candidate_lacks_refs(
        ROOT,
        "exact #1971 protected history",
        PR_1971_COMBINED_BASE,
        PR_1971_COMBINED_HEAD,
    )
    base_policy = _git_blob(PR_1971_COMBINED_BASE, ROTATION_FILE)
    base_profile = _git_blob(PR_1971_COMBINED_BASE, PROFILE_FILE)
    head_policy = _git_blob(PR_1971_COMBINED_HEAD, ROTATION_FILE)
    head_profile = _git_blob(PR_1971_COMBINED_HEAD, PROFILE_FILE)
    assert hashlib.sha256(head_profile).hexdigest() == PR_1971_COMBINED_PROFILE_DIGEST
    assert verification._is_exact_combined_requirement_reconciliation(  # pylint: disable=protected-access
        base_policy, head_policy, base_profile, head_profile
    )
    assert not verification._is_exact_combined_requirement_reconciliation(  # pylint: disable=protected-access
        base_policy + b" ", head_policy, base_profile, head_profile
    )
    assert not verification._is_exact_combined_requirement_reconciliation(  # pylint: disable=protected-access
        base_policy, head_policy, base_profile + b" ", head_profile
    )
    assert not verification._is_exact_combined_requirement_reconciliation(  # pylint: disable=protected-access
        base_policy, head_policy + b" ", base_profile, head_profile
    )
    assert not verification._is_exact_combined_requirement_reconciliation(  # pylint: disable=protected-access
        base_policy, head_policy, base_profile, head_profile + b" "
    )


def test_pr1971_combined_profile_reconciliation_is_consumed() -> None:
    """The historical ee9→e10 transition consumes all exact obligations."""
    skip_if_authenticated_candidate_lacks_refs(
        ROOT,
        "exact #1971 protected history",
        PR_1971_COMBINED_BASE,
        PR_1971_COMBINED_HEAD,
    )
    manifest = build_unit_manifest(
        ROOT, base_ref=PR_1971_COMBINED_BASE, head_ref=PR_1971_COMBINED_HEAD
    )
    profiles = load_verification_profiles(ROOT, manifest)
    assert len(profiles.profiles) == PDD_1989_EXPECTED_MANAGED_UNITS
    assert not profiles.invalid_reasons
    assert profiles.coverage == 1.0
    for prompt_path, expected in PR_1971_PYTEST_OBLIGATIONS.items():
        profile = next(
            item
            for item in profiles.profiles
            if item.unit_id.prompt_relpath.as_posix() == prompt_path
        )
        assert any(
            item.obligation_id == expected["obligation_id"]
            for item in profile.obligations
        )


def test_pr1971_combined_history_rejects_foreign_repository() -> None:
    """Exact #1971 bytes never grant authority outside the PDD repository."""
    skip_if_authenticated_candidate_lacks_refs(
        ROOT,
        "exact #1971 protected history",
        PR_1971_COMBINED_BASE,
        PR_1971_COMBINED_HEAD,
    )
    manifest = build_unit_manifest(
        ROOT, base_ref=PR_1971_COMBINED_BASE, head_ref=PR_1971_COMBINED_HEAD
    )
    base_policy = _git_blob(PR_1971_COMBINED_BASE, ROTATION_FILE)
    head_policy = _git_blob(PR_1971_COMBINED_HEAD, ROTATION_FILE)
    profiles = (
        _git_blob(PR_1971_COMBINED_BASE, PROFILE_FILE),
        _git_blob(PR_1971_COMBINED_HEAD, PROFILE_FILE),
    )
    authorizations = verification._parse_requirement_transition_authorizations(  # pylint: disable=protected-access
        head_policy, "candidate"
    )
    assert verification._is_exact_pr1971_pytest_reconciliation(  # pylint: disable=protected-access
        manifest, (base_policy, head_policy), profiles, authorizations
    )
    assert not verification._is_exact_pr1971_pytest_reconciliation(  # pylint: disable=protected-access
        replace(manifest, repository_id="foreign-repository"),
        (base_policy, head_policy),
        profiles,
        authorizations,
    )


def test_pr1971_reordered_obligation_bytes_are_rejected() -> None:
    """The historical exception is byte-bound, so a semantic reorder fails."""
    skip_if_authenticated_candidate_lacks_refs(
        ROOT,
        "exact #1971 protected history",
        PR_1971_COMBINED_BASE,
        PR_1971_COMBINED_HEAD,
    )
    base_policy = _git_blob(PR_1971_COMBINED_BASE, ROTATION_FILE)
    base_profile = _git_blob(PR_1971_COMBINED_BASE, PROFILE_FILE)
    payload = json.loads(_git_blob(PR_1971_COMBINED_HEAD, PROFILE_FILE))
    next(
        row
        for row in payload["profiles"]
        if row["prompt_path"] == "pdd/prompts/operation_log_python.prompt"
    )["obligations"].reverse()
    assert not verification._is_exact_combined_requirement_reconciliation(  # pylint: disable=protected-access
        base_policy,
        _git_blob(PR_1971_COMBINED_HEAD, ROTATION_FILE),
        base_profile,
        json.dumps(payload, indent=2).encode() + b"\n",
    )


@pytest.mark.parametrize("mutation", ("altered", "extra", "partial", "unrelated"))
def test_pr1971_pytest_obligation_semantic_mutations_are_rejected(
    mutation: str,
) -> None:
    """#1971's pytest addition accepts only its exact protected fields."""
    skip_if_authenticated_candidate_lacks_refs(
        ROOT,
        "exact #1971 protected history",
        PR_1971_COMBINED_BASE,
        PR_1971_COMBINED_HEAD,
    )
    base, base_invalid = verification._load_inputs(  # pylint: disable=protected-access
        ROOT, PR_1971_COMBINED_BASE, REPOSITORY_ID, {}
    )
    head, head_invalid = verification._load_inputs(  # pylint: disable=protected-access
        ROOT, PR_1971_COMBINED_HEAD, REPOSITORY_ID, {}
    )
    assert not base_invalid and not head_invalid
    target_path = PurePosixPath("pdd/prompts/operation_log_python.prompt")
    authorization_path = (
        PurePosixPath("pdd/prompts/pin_example_hack_python.prompt")
        if mutation == "unrelated"
        else target_path
    )
    authorization = next(
        item
        for item in verification._PR1971_COMBINED_REQUIREMENT_TRANSITIONS  # pylint: disable=protected-access
        if item.prompt_path == authorization_path
    )
    unit_id = UnitId(REPOSITORY_ID, authorization_path, "python")
    obligation = verification._PR1971_COMBINED_PYTEST_OBLIGATIONS[
        (  # pylint: disable=protected-access
            target_path,
            "python",
        )
    ]
    if mutation == "altered":
        obligations = tuple(
            sorted(
                (
                    replace(item, validator_config_digest="pytest-v2")
                    if item.obligation_id == obligation.obligation_id
                    else item
                )
                for item in head[unit_id].obligations
            )
        )
    elif mutation == "extra":
        obligations = tuple(
            sorted(
                (
                    *head[unit_id].obligations,
                    replace(obligation, obligation_id="pytest-operation-log-extra"),
                )
            )
        )
    elif mutation == "partial":
        obligations = tuple(
            sorted(
                (
                    replace(item, code_under_test_paths=())
                    if item.obligation_id == obligation.obligation_id
                    else item
                )
                for item in head[unit_id].obligations
            )
        )
    else:
        obligations = tuple(sorted((*head[unit_id].obligations, obligation)))
    candidate = replace(head[unit_id], obligations=obligations)
    assert verification._expected_requirement_update(  # pylint: disable=protected-access
        authorization,
        base[unit_id],
        candidate,
        None if mutation == "unrelated" else obligation,
    ) == (
        None,
        "requirement transition changes protected fields",
    )


def test_pr1971_profile_pytest_obligations_are_exact() -> None:
    """Keep the three protected test-to-code bindings in current profiles."""
    profiles = {
        row["prompt_path"]: row
        for row in json.loads(PROFILE_FILE.read_text(encoding="utf-8"))["profiles"]
    }
    for prompt_path, expected in PR_1971_PYTEST_OBLIGATIONS.items():
        obligation = next(
            item
            for item in profiles[prompt_path]["obligations"]
            if item["obligation_id"] == expected["obligation_id"]
        )
        assert obligation["validator_id"] == "pytest"
        assert obligation["validator_config_digest"] == PYTEST_VALIDATOR_CONFIG_DIGEST
        assert obligation["required"] is True
        assert (
            obligation["requirement_ids"]
            == profiles[prompt_path]["required_requirement_ids"]
        )
        assert tuple(obligation["artifact_paths"]) == expected["tests"]
        assert tuple(obligation["code_under_test_paths"]) == expected["code"]


@pytest.mark.parametrize("protected_source", ("schema-1", "schema-1-old-row", "absent"))
def test_exact_bootstrap_row_installs_from_legacy_protected_source(
    monkeypatch, protected_source: str
) -> None:
    """The exact in-code trust root can perform the first schema-2 install."""
    policy = json.loads(ROTATION_FILE.read_text(encoding="utf-8"))
    authorization = verification._BOOTSTRAP_REQUIREMENT_TRANSITIONS[
        0
    ]  # pylint: disable=protected-access
    rotations = policy["rotations"] if protected_source != "absent" else []
    protected_payload = {"schema_version": 1, "rotations": rotations}
    if protected_source == "schema-1-old-row":
        protected_payload["requirement_rotations"] = [
            LEGACY_SCHEMA_1_REQUIREMENT_ROTATION
        ]
    protected = (
        None if protected_source == "absent" else json.dumps(protected_payload).encode()
    )
    candidate = json.dumps(
        {
            "schema_version": 2,
            "rotations": rotations,
            "requirement_rotations": [_requirement_authorization_row(authorization)],
        }
    ).encode()

    def protected_read(_root: Path, ref: str, path: PurePosixPath) -> bytes | None:
        if path != verification.ROTATION_POLICY_PATH:
            return None
        return protected if ref == "protected" else candidate

    monkeypatch.setattr(verification, "read_git_blob", protected_read)
    manifest = SimpleNamespace(
        repository_id=REPOSITORY_ID,
        base_ref="protected",
        head_ref="candidate",
    )

    authorizations, _prompts, _new_authorizations = (
        verification._load_requirement_transition_authorizations(  # pylint: disable=protected-access
            ROOT, manifest
        )
    )
    assert authorizations == (authorization,)


@pytest.mark.parametrize("profile_source", ("absent", "schema-1"))
def test_exact_bootstrap_row_rejects_profile_byte_mutation(
    monkeypatch, profile_source: str
) -> None:
    """A legacy bootstrap cannot install while profile bytes drift."""
    authorization = verification._BOOTSTRAP_REQUIREMENT_TRANSITIONS[
        0
    ]  # pylint: disable=protected-access
    candidate = json.dumps(
        {
            "schema_version": 2,
            "rotations": [],
            "requirement_rotations": [_requirement_authorization_row(authorization)],
        }
    ).encode()
    protected_profile = (
        None if profile_source == "absent" else b'{"schema_version":1,"profiles":[]}\n'
    )
    candidate_profile = b'{\n  "schema_version": 1, "profiles": []\n}\n'

    def protected_read(_root: Path, ref: str, path: PurePosixPath) -> bytes | None:
        if path == verification.ROTATION_POLICY_PATH:
            return None if ref == "protected" else candidate
        if path == PROFILE_REL_PATH:
            return protected_profile if ref == "protected" else candidate_profile
        return None

    monkeypatch.setattr(verification, "read_git_blob", protected_read)
    manifest = SimpleNamespace(
        repository_id=REPOSITORY_ID,
        base_ref="protected",
        head_ref="candidate",
    )

    with pytest.raises(
        verification.VerificationProfileError,
        match="changes protected verification-profile bytes",
    ):
        verification._load_requirement_transition_authorizations(  # pylint: disable=protected-access
            ROOT, manifest
        )


def test_exact_replay_row_can_bind_changed_profile_bytes(monkeypatch) -> None:
    """Only the reviewed replay tuple may carry its exact profile transition."""
    authorization = verification._REPLAY_PROFILE_REQUIREMENT_TRANSITIONS[
        0
    ]  # pylint: disable=protected-access
    candidate = json.dumps(
        {
            "schema_version": 2,
            "rotations": [],
            "requirement_rotations": [_requirement_authorization_row(authorization)],
        }
    ).encode()

    def protected_read(_root: Path, ref: str, path: PurePosixPath) -> bytes | None:
        if path == verification.ROTATION_POLICY_PATH:
            return None if ref == "protected" else candidate
        if path == PROFILE_REL_PATH:
            return b"{}" if ref == "protected" else b'{"profiles": []}'
        return None

    monkeypatch.setattr(verification, "read_git_blob", protected_read)
    manifest = SimpleNamespace(
        repository_id=REPOSITORY_ID,
        base_ref="protected",
        head_ref="candidate",
    )

    authorizations, _prompts, additions = (
        verification._load_requirement_transition_authorizations(  # pylint: disable=protected-access
            ROOT, manifest
        )
    )

    assert authorizations == (authorization,)
    assert additions == ()


def test_non_pdd_replay_row_remains_a_new_authorization(monkeypatch) -> None:
    """A foreign repository cannot bypass managed-prompt isolation with replay data."""
    authorization = verification._REPLAY_PROMPT_REQUIREMENT_TRANSITIONS[
        0
    ]  # pylint: disable=protected-access
    protected = json.dumps(
        {
            "schema_version": 2,
            "rotations": [],
            "requirement_rotations": [],
        }
    ).encode()
    candidate = json.dumps(
        {
            "schema_version": 2,
            "rotations": [],
            "requirement_rotations": [_requirement_authorization_row(authorization)],
        }
    ).encode()

    def protected_read(_root: Path, ref: str, path: PurePosixPath) -> bytes | None:
        if path == verification.ROTATION_POLICY_PATH:
            return protected if ref == "protected" else candidate
        return None

    monkeypatch.setattr(verification, "read_git_blob", protected_read)
    monkeypatch.setattr(
        verification,
        "_candidate_authorization_is_strictly_dormant",  # pylint: disable=protected-access
        lambda *_args: True,
    )
    manifest = SimpleNamespace(
        repository_id="foreign-repository",
        base_ref="protected",
        head_ref="candidate",
    )

    authorizations, _prompts, additions = (
        verification._load_requirement_transition_authorizations(  # pylint: disable=protected-access
            ROOT, manifest
        )
    )

    assert authorizations == (authorization,)
    assert additions == (authorization,)
    monkeypatch.setattr(
        verification,
        "_managed_prompt_byte_changes",  # pylint: disable=protected-access
        lambda *_args: {authorization.prompt_path},
    )
    with pytest.raises(
        verification.VerificationProfileError,
        match="authority-only change modifies managed prompt bytes",
    ):
        verification._validate_new_authorization_managed_prompt_bytes(  # pylint: disable=protected-access
            ROOT, manifest, {}, set()
        )


def test_legacy_replay_history_exemption_is_repository_bound(monkeypatch) -> None:
    """Only PDD may read the reviewed non-append-only #1989 history pair."""
    first, second = verification._REPLAY_PROMPT_REQUIREMENT_TRANSITIONS[
        :2
    ]  # pylint: disable=protected-access
    protected = json.dumps(
        {
            "schema_version": 2,
            "rotations": [],
            "requirement_rotations": [
                _requirement_authorization_row(first),
                _requirement_authorization_row(second),
            ],
        }
    ).encode()
    candidate = json.dumps(
        {
            "schema_version": 2,
            "rotations": [],
            "requirement_rotations": [
                _requirement_authorization_row(second),
                _requirement_authorization_row(first),
            ],
        }
    ).encode()
    protected_rows = verification._parse_requirement_transition_authorizations(  # pylint: disable=protected-access
        protected, "protected"
    )
    candidate_rows = verification._parse_requirement_transition_authorizations(  # pylint: disable=protected-access
        candidate, "candidate"
    )

    class _Digest:
        def __init__(self, raw: bytes) -> None:
            self._raw = raw

        def hexdigest(self) -> str:
            return verification._LEGACY_PDD_1989_SCHEMA_2_HISTORY[  # pylint: disable=protected-access
                0 if self._raw == protected else 1
            ]

    monkeypatch.setattr(verification.hashlib, "sha256", _Digest)
    pdd_manifest = SimpleNamespace(repository_id=REPOSITORY_ID)
    verification._validate_schema_2_history_representation(  # pylint: disable=protected-access
        pdd_manifest, protected, candidate, protected_rows, candidate_rows
    )

    with pytest.raises(
        verification.VerificationProfileError,
        match="schema-2 history rewrites protected representation",
    ):
        verification._validate_schema_2_history_representation(  # pylint: disable=protected-access
            SimpleNamespace(repository_id="foreign-repository"),
            protected,
            candidate,
            protected_rows,
            candidate_rows,
        )


@pytest.mark.parametrize(
    "mutation", ("malformed-row", "non-list-rows", "extra-envelope-key")
)
def test_legacy_schema_1_bootstrap_rejects_malformed_envelope(
    monkeypatch, mutation: str
) -> None:
    """Historical rows are ignored as authority only after strict parsing."""
    policy = json.loads(ROTATION_FILE.read_text(encoding="utf-8"))
    authorization = verification._BOOTSTRAP_REQUIREMENT_TRANSITIONS[
        0
    ]  # pylint: disable=protected-access
    protected_payload = {
        "schema_version": 1,
        "rotations": policy["rotations"],
        "requirement_rotations": [dict(LEGACY_SCHEMA_1_REQUIREMENT_ROTATION)],
    }
    if mutation == "malformed-row":
        protected_payload["requirement_rotations"][0].pop("language_id")
    elif mutation == "non-list-rows":
        protected_payload["requirement_rotations"] = {}
    else:
        protected_payload["candidate_authority"] = []
    protected = json.dumps(protected_payload).encode()
    candidate = json.dumps(
        {
            "schema_version": 2,
            "rotations": policy["rotations"],
            "requirement_rotations": [_requirement_authorization_row(authorization)],
        }
    ).encode()

    def protected_read(_root: Path, ref: str, path: PurePosixPath) -> bytes | None:
        if path != verification.ROTATION_POLICY_PATH:
            return None
        return protected if ref == "protected" else candidate

    monkeypatch.setattr(verification, "read_git_blob", protected_read)
    manifest = SimpleNamespace(
        repository_id=REPOSITORY_ID,
        base_ref="protected",
        head_ref="candidate",
    )

    with pytest.raises(verification.VerificationProfileError, match="protected"):
        verification._load_requirement_transition_authorizations(  # pylint: disable=protected-access
            ROOT, manifest
        )


@pytest.mark.parametrize("mutation", ("non-list-rotations", "malformed-row"))
def test_stationary_schema_1_policy_is_validated_before_early_return(
    monkeypatch, mutation: str
) -> None:
    """Equal legacy bytes cannot bypass structural validation by staying stationary."""
    payload = {"schema_version": 1, "rotations": []}
    if mutation == "non-list-rotations":
        payload["rotations"] = {}
    else:
        payload["requirement_rotations"] = [{"prompt_path": "missing-fields"}]
    raw = json.dumps(payload).encode()

    monkeypatch.setattr(
        verification,
        "read_git_blob",
        lambda _root, _ref, path: (
            raw if path == verification.ROTATION_POLICY_PATH else None
        ),
    )
    manifest = SimpleNamespace(
        repository_id=REPOSITORY_ID,
        base_ref="protected",
        head_ref="candidate",
    )

    with pytest.raises(verification.VerificationProfileError, match="protected"):
        verification._load_requirement_transition_authorizations(  # pylint: disable=protected-access
            ROOT, manifest
        )


@pytest.mark.parametrize("schema_version", (True, 1.0, "1", False, 2.0))
def test_rotation_policy_parsers_reject_non_exact_integer_schema_versions(
    monkeypatch, schema_version
) -> None:
    """Every policy parser rejects bools and non-integer schema encodings."""
    schema_2 = json.dumps(
        {
            "schema_version": schema_version,
            "rotations": [],
            "requirement_rotations": [],
        }
    ).encode()
    schema_3 = json.dumps(
        {
            "schema_version": schema_version,
            "rotations": [],
            "requirement_rotations": [],
            "requirement_rotation_retirements": [],
        }
    ).encode()

    with pytest.raises(verification.VerificationProfileError):
        verification._parse_requirement_transition_authorizations(  # pylint: disable=protected-access
            schema_2, "candidate"
        )
    with pytest.raises(verification.VerificationProfileError):
        verification._parse_requirement_transition_retirements(  # pylint: disable=protected-access
            schema_3, "candidate"
        )
    with pytest.raises(verification.VerificationProfileError):
        verification._parse_dormant_policy_envelope(  # pylint: disable=protected-access
            schema_2, "candidate"
        )
    monkeypatch.setattr(
        verification,
        "read_git_blob",
        lambda _root, _ref, _path: schema_2,
    )
    with pytest.raises(verification.VerificationProfileError):
        verification._load_rotation_authorizations(  # pylint: disable=protected-access
            ROOT, "protected"
        )


@pytest.mark.parametrize(
    "mutation", ("remove-schema-1", "replace-schema-1", "add-to-absent")
)
def test_bootstrap_install_cannot_change_active_rotation_authority(
    monkeypatch, mutation: str
) -> None:
    """Legacy bootstrap changes only the envelope, never active authority."""
    policy = json.loads(ROTATION_FILE.read_text(encoding="utf-8"))
    authorization = verification._BOOTSTRAP_REQUIREMENT_TRANSITIONS[
        0
    ]  # pylint: disable=protected-access
    rotations = policy["rotations"]
    protected = (
        None
        if mutation == "add-to-absent"
        else json.dumps({"schema_version": 1, "rotations": rotations}).encode()
    )
    candidate_rotations = rotations if mutation == "add-to-absent" else []
    if mutation == "replace-schema-1":
        candidate_rotations = [dict(rotations[0], validator_id="candidate-validator")]
    candidate = json.dumps(
        {
            "schema_version": 2,
            "rotations": candidate_rotations,
            "requirement_rotations": [_requirement_authorization_row(authorization)],
        }
    ).encode()

    def protected_read(_root: Path, ref: str, path: PurePosixPath) -> bytes | None:
        if path != verification.ROTATION_POLICY_PATH:
            return None
        return protected if ref == "protected" else candidate

    monkeypatch.setattr(verification, "read_git_blob", protected_read)
    manifest = SimpleNamespace(
        repository_id=REPOSITORY_ID,
        base_ref="protected",
        head_ref="candidate",
    )

    with pytest.raises(verification.VerificationProfileError, match="candidate"):
        verification._load_requirement_transition_authorizations(  # pylint: disable=protected-access
            ROOT, manifest
        )


def test_pdd1989_transitions_cover_the_actual_merged_base() -> None:
    """The #1989 transition table must load a complete exact-base profile set."""
    skip_if_authenticated_candidate_lacks_refs(
        ROOT,
        "local git history for #1989 exact-base verification",
        PDD_1989_ACTUAL_BASE,
        PDD_1989_ACTUAL_HEAD,
    )
    manifest = build_unit_manifest(
        ROOT,
        base_ref=PDD_1989_ACTUAL_BASE,
        head_ref=PDD_1989_ACTUAL_HEAD,
    )

    profiles = load_verification_profiles(ROOT, manifest)

    assert len(manifest.expected_managed) == PDD_1989_EXPECTED_MANAGED_UNITS
    assert not manifest.invalid_reasons
    assert len(profiles.profiles) == PDD_1989_EXPECTED_MANAGED_UNITS
    assert not profiles.invalid_reasons
    assert profiles.coverage == 1.0


def test_pr2017_phase_a_is_dormant_on_current_protected_base() -> None:
    """The prerequisite installs authority without consuming protected bytes."""
    skip_if_authenticated_candidate_lacks_refs(
        ROOT, "exact #1875 protected history", PDD_1875_PROTECTED_BASE
    )
    manifest = build_unit_manifest(
        ROOT, base_ref=PDD_1875_PROTECTED_BASE, head_ref="HEAD"
    )

    profiles = load_verification_profiles(ROOT, manifest)

    assert len(manifest.expected_managed) == EXPECTED_MANAGED_UNITS
    assert not manifest.invalid_reasons
    assert len(profiles.profiles) == EXPECTED_MANAGED_UNITS
    assert not profiles.invalid_reasons
    assert profiles.coverage == 1.0


def test_replay_transitions_cover_the_actual_protected_base() -> None:
    """The replay transitions must load a complete exact-base profile set."""
    skip_if_authenticated_candidate_lacks_refs(
        ROOT,
        "exact replay history",
        REPLAY_PROTECTED_BASE,
        PDD_1875_PROTECTED_BASE,
    )
    manifest = build_unit_manifest(
        ROOT, base_ref=REPLAY_PROTECTED_BASE, head_ref=PDD_1875_PROTECTED_BASE
    )
    profiles = load_verification_profiles(ROOT, manifest)

    assert len(manifest.expected_managed) == EXPECTED_MANAGED_UNITS
    assert not manifest.invalid_reasons
    assert len(profiles.profiles) == EXPECTED_MANAGED_UNITS
    assert not profiles.invalid_reasons
    assert profiles.coverage == 1.0


def test_pr2017_phase_a_is_dormant_on_its_exact_protected_base() -> None:
    """The PR #2017 prerequisite installs authority without consuming bytes."""
    skip_if_authenticated_candidate_lacks_refs(
        ROOT,
        "exact #2017 protected history",
        PR_2017_PHASE_A_BASE,
        PR_2017_PHASE_A_HEAD,
    )
    manifest = build_unit_manifest(
        ROOT, base_ref=PR_2017_PHASE_A_BASE, head_ref=PR_2017_PHASE_A_HEAD
    )
    profiles = load_verification_profiles(ROOT, manifest)

    assert len(manifest.expected_managed) == 468
    assert not manifest.invalid_reasons
    assert not manifest.unaccounted_tracked_paths
    assert len(profiles.profiles) == 468
    assert not profiles.invalid_reasons
    assert profiles.coverage == 1.0


def _candidate_only_repo(tmp_path: Path) -> tuple[Path, str, str]:
    repo = tmp_path / "candidate-only"
    repo.mkdir()
    _git(repo, "init")
    (repo / "tracked.txt").write_text("candidate\n", encoding="utf-8")
    candidate_sha = _commit(repo, "candidate")
    candidate_tree = subprocess.check_output(
        ["git", "rev-parse", "HEAD^{tree}"], cwd=repo, text=True
    ).strip()
    return repo, candidate_sha, candidate_tree


def _set_candidate_only_identity(
    monkeypatch, candidate_sha: str, candidate_tree: str
) -> None:
    monkeypatch.setenv("PDD_CLOUD_SOURCE_IDENTITY_MODE", "candidate-tree-v1")
    monkeypatch.setenv("PDD_CANDIDATE_SHA", candidate_sha)
    monkeypatch.setenv("PDD_CANDIDATE_TREE", candidate_tree)


def test_pdd1989_history_guard_accepts_verified_candidate_only_repo(
    tmp_path: Path, monkeypatch
) -> None:
    """A verified candidate-only Git checkout intentionally lacks ancestors."""
    repo, candidate_sha, candidate_tree = _candidate_only_repo(tmp_path)
    _set_candidate_only_identity(monkeypatch, candidate_sha, candidate_tree)

    assert authenticated_candidate_missing_refs(
        repo, PDD_1989_ACTUAL_BASE, PDD_1989_ACTUAL_HEAD
    ) == (PDD_1989_ACTUAL_BASE, PDD_1989_ACTUAL_HEAD)


@pytest.mark.parametrize("marker", (None, "candidate-tree-v2"))
def test_pdd1989_history_guard_does_not_skip_without_verified_marker(
    tmp_path: Path, monkeypatch, marker: str | None
) -> None:
    """Ordinary shallow checkouts keep the exact-base assertion fail-closed."""
    repo, candidate_sha, candidate_tree = _candidate_only_repo(tmp_path)
    if marker is None:
        monkeypatch.delenv("PDD_CLOUD_SOURCE_IDENTITY_MODE", raising=False)
    else:
        monkeypatch.setenv("PDD_CLOUD_SOURCE_IDENTITY_MODE", marker)
    monkeypatch.setenv("PDD_CANDIDATE_SHA", candidate_sha)
    monkeypatch.setenv("PDD_CANDIDATE_TREE", candidate_tree)

    skip_if_authenticated_candidate_lacks_refs(
        repo,
        "local git history for #1989 exact-base verification",
        PDD_1989_ACTUAL_BASE,
        PDD_1989_ACTUAL_HEAD,
    )


@pytest.mark.parametrize("mismatch", ("sha", "tree", "sha-format", "tree-format"))
def test_pdd1989_history_guard_does_not_skip_mismatched_candidate_identity(
    tmp_path: Path, monkeypatch, mismatch: str
) -> None:
    """A forged or stale candidate identity cannot authorize a history skip."""
    repo, candidate_sha, candidate_tree = _candidate_only_repo(tmp_path)
    if mismatch == "sha":
        candidate_sha = "0" * 40
    elif mismatch == "tree":
        candidate_tree = "0" * 40
    elif mismatch == "sha-format":
        candidate_sha = "not-a-sha"
    else:
        candidate_tree = "not-a-tree"
    _set_candidate_only_identity(monkeypatch, candidate_sha, candidate_tree)

    skip_if_authenticated_candidate_lacks_refs(
        repo,
        "local git history for #1989 exact-base verification",
        PDD_1989_ACTUAL_BASE,
        PDD_1989_ACTUAL_HEAD,
    )


@pytest.mark.parametrize("missing", ("PDD_CANDIDATE_SHA", "PDD_CANDIDATE_TREE"))
def test_pdd1989_history_guard_does_not_skip_missing_candidate_identity(
    tmp_path: Path, monkeypatch, missing: str
) -> None:
    """The trusted mode marker alone cannot authorize a history skip."""
    repo, candidate_sha, candidate_tree = _candidate_only_repo(tmp_path)
    _set_candidate_only_identity(monkeypatch, candidate_sha, candidate_tree)
    monkeypatch.delenv(missing)

    skip_if_authenticated_candidate_lacks_refs(
        repo,
        "local git history for #1989 exact-base verification",
        PDD_1989_ACTUAL_BASE,
        PDD_1989_ACTUAL_HEAD,
    )


def test_pdd1989_history_guard_does_not_hide_missing_repository_identity(
    tmp_path: Path, monkeypatch
) -> None:
    """Available refs still require the protected repository identity blob."""
    repo, candidate_sha, candidate_tree = _candidate_only_repo(tmp_path)
    _set_candidate_only_identity(monkeypatch, candidate_sha, candidate_tree)

    skip_if_authenticated_candidate_lacks_refs(
        repo, "repository identity verification", candidate_sha, candidate_sha
    )
    with pytest.raises(
        manifest_module.ManifestError,
        match=r"base and head must contain \.pdd/repository-id",
    ):
        build_unit_manifest(repo, base_ref=candidate_sha, head_ref=candidate_sha)


def test_current_profile_rotation_matches_current_prompt_and_profile_rows() -> None:
    """An adopted rotation must not leave profile requirements stale."""
    policy = json.loads(ROTATION_FILE.read_text(encoding="utf-8"))
    profile_payload = json.loads(PROFILE_FILE.read_text(encoding="utf-8"))
    profile_digest = hashlib.sha256(PROFILE_FILE.read_bytes()).hexdigest()
    current_rows = [
        row
        for row in policy["requirement_rotations"]
        if row["head_policy_sha256"] == profile_digest
    ]
    assert current_rows
    profiles = {
        (row["prompt_path"], row["language_id"]): row
        for row in profile_payload["profiles"]
    }

    for rotation in current_rows:
        prompt_path = ROOT / rotation["prompt_path"]
        expected_requirement = rotation["to_requirement_id"]
        assert (
            hashlib.sha256(prompt_path.read_bytes()).hexdigest()
            == rotation["head_prompt_sha256"]
        )
        assert expected_requirement == (
            f"CONTRACT-SHA256:{rotation['head_prompt_sha256']}"
        )
        profile = profiles[(rotation["prompt_path"], rotation["language_id"])]
        assert profile["required_requirement_ids"] == [expected_requirement]
        human = next(
            item
            for item in profile["obligations"]
            if item["validator_id"] == "threshold-ed25519"
        )
        assert human["requirement_ids"] == [expected_requirement]


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
        "wrong-requirement",
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
    elif mutation == "wrong-requirement":
        prompt_path, language_id, _requirement_id, policy_digest, prompt_digest = (
            verification._BOOTSTRAP_PROFILE_ADDITIONS[
                0
            ]  # pylint: disable=protected-access
        )
        monkeypatch.setattr(
            verification,
            "_BOOTSTRAP_PROFILE_ADDITIONS",
            (
                (
                    prompt_path,
                    language_id,
                    f"CONTRACT-SHA256:{'0' * 64}",
                    policy_digest,
                    prompt_digest,
                ),
            ),
        )
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
    base = _synthetic_current_tree_repo(root)

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
    _synthetic_current_tree_repo(root)

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


def test_gate1_paths_are_exactly_preauthorized() -> None:
    """Only the four reviewed Gate 1 paths receive absent-path authority."""
    ownership = json.loads(OWNERSHIP_PATH.read_text(encoding="utf-8"))
    rules = {row["pattern"]: row for row in ownership["rules"]}
    assert {path: rules.get(path) for path in GATE1_PREAUTHORIZED_PATHS} == {
        path: {"pattern": path, **PREAUTHORIZED_CHILD_OWNERSHIP}
        for path in GATE1_PREAUTHORIZED_PATHS
    }
    assert {
        row["pattern"]
        for row in ownership["rules"]
        if row.get("preauthorize_absent", False)
        and (
            row["pattern"].startswith("pdd/sync_core/adapter_demand")
            or row["pattern"].startswith("tests/test_sync_core_adapter_demand")
            or row["pattern"].startswith("docs/global_sync_extract")
            or row["pattern"].startswith("docs/global_sync_pdd_adapter_demand")
        )
    } == GATE1_PREAUTHORIZED_PATHS


def test_gate1_paths_compose_with_protected_preauthorization(
    tmp_path: Path,
) -> None:
    """A branch-only checkout composes Gate 1 paths from protected preauth."""
    root = tmp_path / "gate1-preauth-composition"
    _synthetic_current_tree_repo(root)
    assert not any(
        "global-sync-gate1" in ref
        for ref in subprocess.check_output(
            ["git", "for-each-ref", "--format=%(refname)"], cwd=root, text=True
        ).splitlines()
    )

    inert_paths = {
        "docs/global_sync_extraction_manifest.md": b"# synthetic Gate 1 manifest\n",
        "docs/global_sync_pdd_adapter_demand.json": b"{}\n",
        "pdd/sync_core/adapter_demand_verifier.py": b'"""Synthetic Gate 1 verifier."""\n',
        "tests/test_sync_core_adapter_demand_verifier.py": (
            b'"""Synthetic Gate 1 verifier test."""\n'
        ),
    }
    for path, content in inert_paths.items():
        candidate = root / path
        candidate.parent.mkdir(parents=True, exist_ok=True)
        candidate.write_bytes(content)
    for path in GATE1_EXISTING_HUMAN_PATHS:
        candidate = root / path
        candidate.write_bytes(candidate.read_bytes() + b"\n")
    _commit(root, "compose synthetic Gate 1 path set")

    changed_paths = set(
        subprocess.check_output(
            ["git", "diff", "--name-only", "origin/main...HEAD"],
            cwd=root,
            text=True,
        ).splitlines()
    )
    assert changed_paths == GATE1_CHANGED_PATHS
    for detector in (
        "scripts/ci_detect_changed_modules.py",
        "pdd/ci_detect_changed_modules.py",
    ):
        result = subprocess.run(
            [sys.executable, detector, "--diff-base", "origin/main...HEAD"],
            cwd=root,
            check=False,
            capture_output=True,
            text=True,
        )
        assert result.returncode == 0, result.stderr
        assert not result.stdout.strip()

    manifest = build_unit_manifest(root, base_ref="origin/main", head_ref="HEAD")
    records = {
        item.candidate_id.artifact_relpath.as_posix(): item
        for item in manifest.candidates
        if item.candidate_id.artifact_relpath.as_posix() in GATE1_PREAUTHORIZED_PATHS
    }
    assert set(records) == GATE1_PREAUTHORIZED_PATHS
    assert not manifest.unaccounted_tracked_paths
    assert not manifest.invalid_reasons
    assert all(
        item.inventory.value == "HUMAN_OWNED"
        and item.candidate_id.role == "human-maintained"
        and item.ownership_provenance == f"protected-ownership:pdd-maintainers:{path}"
        for path, item in records.items()
    )
    assert len(manifest.expected_managed) == EXPECTED_MANAGED_UNITS


def test_global_sync_ledger_paths_are_exactly_preauthorized() -> None:
    """Only the three reviewed global-sync ledger paths are preauthorized."""
    ownership = json.loads(OWNERSHIP_PATH.read_text(encoding="utf-8"))
    rules = {row["pattern"]: row for row in ownership["rules"]}
    assert {
        path: rules.get(path) for path in GLOBAL_SYNC_LEDGER_PREAUTHORIZED_PATHS
    } == {
        path: {"pattern": path, **PREAUTHORIZED_CHILD_OWNERSHIP}
        for path in GLOBAL_SYNC_LEDGER_PREAUTHORIZED_PATHS
    }
    assert {
        row["pattern"]
        for row in ownership["rules"]
        if row.get("preauthorize_absent", False)
        and (
            row["pattern"].startswith("docs/global_sync_evidence_ledger_source")
            or row["pattern"].startswith("pdd/sync_core/global_sync_ledger")
            or row["pattern"].startswith("tests/test_global_sync_ledger")
        )
    } == GLOBAL_SYNC_LEDGER_PREAUTHORIZED_PATHS


def test_global_sync_runtime_lock_path_is_exactly_preauthorized() -> None:
    """Only the reviewed Linux CPython 3.12 target lock receives authority."""
    ownership = json.loads(OWNERSHIP_PATH.read_text(encoding="utf-8"))
    rules = {row["pattern"]: row for row in ownership["rules"]}
    assert {
        path: rules.get(path) for path in GLOBAL_SYNC_RUNTIME_LOCK_PREAUTHORIZED_PATHS
    } == {
        path: {"pattern": path, **PREAUTHORIZED_CHILD_OWNERSHIP}
        for path in GLOBAL_SYNC_RUNTIME_LOCK_PREAUTHORIZED_PATHS
    }
    assert {
        row["pattern"]
        for row in ownership["rules"]
        if row.get("preauthorize_absent", False)
        and row["pattern"].startswith(".pdd/global-sync/")
    } == (
        GLOBAL_SYNC_RUNTIME_LOCK_PREAUTHORIZED_PATHS
        | STANDALONE_CHECKER_GLOBAL_SYNC_PREAUTHORIZED_PATHS
    )
    assert (
        STANDALONE_CHECKER_GLOBAL_SYNC_PREAUTHORIZED_PATHS
        <= STANDALONE_CHECKER_PREAUTHORIZED_PATHS
    )

    # Existing independently reviewed preauthorization families stay exact.
    assert GATE1_PREAUTHORIZED_PATHS == {
        "docs/global_sync_extraction_manifest.md",
        "docs/global_sync_pdd_adapter_demand.json",
        "pdd/sync_core/adapter_demand_verifier.py",
        "tests/test_sync_core_adapter_demand_verifier.py",
    }
    assert GLOBAL_SYNC_LEDGER_PREAUTHORIZED_PATHS == {
        "docs/global_sync_evidence_ledger_source.yaml",
        "pdd/sync_core/global_sync_ledger.py",
        "tests/test_global_sync_ledger.py",
    }


def test_global_sync_runtime_lock_composes_without_sibling_authority(
    tmp_path: Path,
) -> None:
    """Protected preauthorization admits the exact lock and rejects a sibling."""
    root = tmp_path / "runtime-lock-preauthorization"
    base = _synthetic_current_tree_repo(root)
    exact = next(iter(GLOBAL_SYNC_RUNTIME_LOCK_PREAUTHORIZED_PATHS))
    exact_path = root / exact
    exact_path.parent.mkdir(parents=True, exist_ok=True)
    exact_path.write_text("synthetic reviewed target lock\n", encoding="utf-8")
    _git(root, "add", "-f", exact)
    exact_head = _commit(root, "add exact synthetic runtime lock")

    exact_manifest = build_unit_manifest(root, base_ref=base, head_ref=exact_head)
    exact_record = next(
        item
        for item in exact_manifest.candidates
        if item.candidate_id.artifact_relpath.as_posix() == exact
    )
    assert exact_record.inventory.value == "HUMAN_OWNED"
    assert exact_record.candidate_id.role == "human-maintained"
    assert exact_record.ownership_provenance == (
        f"protected-ownership:pdd-maintainers:{exact}"
    )
    assert not exact_manifest.unaccounted_tracked_paths
    assert not exact_manifest.invalid_reasons

    sibling = ".pdd/global-sync/runtime-linux-aarch64-cp312.lock"
    sibling_path = root / sibling
    sibling_path.write_text("unauthorized sibling lock\n", encoding="utf-8")
    _git(root, "add", "-f", sibling)
    sibling_head = _commit(root, "attempt sibling runtime lock")
    sibling_manifest = build_unit_manifest(
        root, base_ref=exact_head, head_ref=sibling_head
    )
    assert Path(sibling) in sibling_manifest.unaccounted_tracked_paths
    assert any(
        reason == f"{sibling}: tracked path has no ownership rule"
        for reason in sibling_manifest.invalid_reasons
    )


def test_standalone_checker_package_boundary_is_exactly_preauthorized() -> None:
    """Only the five reviewed standalone-checker boundary paths are allowed."""
    ownership = json.loads(OWNERSHIP_PATH.read_text(encoding="utf-8"))
    rules = {row["pattern"]: row for row in ownership["rules"]}
    assert len(STANDALONE_CHECKER_PREAUTHORIZED_PATHS) == 5
    assert {
        path: rules.get(path) for path in STANDALONE_CHECKER_PREAUTHORIZED_PATHS
    } == {
        path: {"pattern": path, **PREAUTHORIZED_CHILD_OWNERSHIP}
        for path in STANDALONE_CHECKER_PREAUTHORIZED_PATHS
    }
    assert [
        row["pattern"]
        for row in ownership["rules"]
        if row["pattern"] in STANDALONE_CHECKER_PREAUTHORIZED_PATHS
    ] == sorted(STANDALONE_CHECKER_PREAUTHORIZED_PATHS)

    preauthorized = {
        row["pattern"]
        for row in ownership["rules"]
        if row.get("preauthorize_absent", False)
    }
    assert {
        path
        for path in preauthorized
        if path.startswith(FUTURE_STANDALONE_CHECKER_AUTHORITY_PREFIXES)
    } == STANDALONE_CHECKER_PREAUTHORIZED_PATHS
    assert not preauthorized & FUTURE_STANDALONE_CHECKER_UNAUTHORIZED_PATHS
    assert all(
        not path.endswith("/") and not any(token in path for token in ("*", "?", "["))
        for path in STANDALONE_CHECKER_PREAUTHORIZED_PATHS
    )
    assert all(
        (ROOT / path).is_file() and not (ROOT / path).is_symlink()
        for path in sorted(STANDALONE_CHECKER_PREAUTHORIZED_PATHS)
    )


def test_standalone_checker_package_boundary_composes_offline_and_fails_closed(
    tmp_path: Path,
) -> None:
    """A branch-only checkout admits only the exact standalone boundary."""
    root = tmp_path / "standalone-checker-preauth-composition"
    _synthetic_current_tree_repo(root)
    assert not any(
        "standalone-checker" in ref
        for ref in subprocess.check_output(
            ["git", "for-each-ref", "--format=%(refname)"], cwd=root, text=True
        ).splitlines()
    )

    inert_paths = {
        ".pdd/global-sync/standalone-checker-modules.json": b'{"modules": []}\n',
        "pdd/sync_core/checker_cli.py": b'"""Synthetic checker CLI."""\n',
        "pdd/sync_core/standalone_package.py": b'"""Synthetic package boundary."""\n',
        "tests/test_sync_core_checker_cli.py": b'"""Synthetic checker CLI test."""\n',
        "tests/test_sync_core_standalone_package.py": (
            b'"""Synthetic package boundary test."""\n'
        ),
    }
    assert set(inert_paths) == STANDALONE_CHECKER_PREAUTHORIZED_PATHS
    for path, content in inert_paths.items():
        candidate = root / path
        candidate.parent.mkdir(parents=True, exist_ok=True)
        candidate.write_bytes(content)
    _git(root, "add", "-f", ".pdd/global-sync/standalone-checker-modules.json")
    exact_head = _commit(root, "compose synthetic standalone checker boundary")

    assert (
        set(
            subprocess.check_output(
                ["git", "diff", "--name-only", "origin/main...HEAD"],
                cwd=root,
                text=True,
            ).splitlines()
        )
        == STANDALONE_CHECKER_PREAUTHORIZED_PATHS
    )
    for detector in (
        "scripts/ci_detect_changed_modules.py",
        "pdd/ci_detect_changed_modules.py",
    ):
        result = subprocess.run(
            [sys.executable, detector, "--diff-base", "origin/main...HEAD"],
            cwd=root,
            check=False,
            capture_output=True,
            text=True,
        )
        assert result.returncode == 0, result.stderr
        assert not result.stdout.strip()

    manifest = build_unit_manifest(root, base_ref="origin/main", head_ref="HEAD")
    records = {
        item.candidate_id.artifact_relpath.as_posix(): item
        for item in manifest.candidates
        if item.candidate_id.artifact_relpath.as_posix()
        in STANDALONE_CHECKER_PREAUTHORIZED_PATHS
    }
    assert set(records) == STANDALONE_CHECKER_PREAUTHORIZED_PATHS
    assert not manifest.unaccounted_tracked_paths
    assert not manifest.invalid_reasons
    assert all(
        item.inventory.value == "HUMAN_OWNED"
        and item.candidate_id.role == "human-maintained"
        and item.ownership_provenance == f"protected-ownership:pdd-maintainers:{path}"
        for path, item in records.items()
    )
    assert len(manifest.expected_managed) == EXPECTED_MANAGED_UNITS

    for path in FUTURE_STANDALONE_CHECKER_UNAUTHORIZED_PATHS:
        candidate = root / path
        candidate.parent.mkdir(parents=True, exist_ok=True)
        candidate.write_text("unauthorized future authority\n", encoding="utf-8")
        _git(root, "add", "-f", path)
    unauthorized_head = _commit(root, "attempt future standalone authority")
    unauthorized_manifest = build_unit_manifest(
        root, base_ref=exact_head, head_ref=unauthorized_head
    )
    assert {Path(path) for path in FUTURE_STANDALONE_CHECKER_UNAUTHORIZED_PATHS} <= set(
        unauthorized_manifest.unaccounted_tracked_paths
    )
    assert {
        f"{path}: tracked path has no ownership rule"
        for path in FUTURE_STANDALONE_CHECKER_UNAUTHORIZED_PATHS
    } <= set(unauthorized_manifest.invalid_reasons)


def test_global_sync_ledger_paths_compose_with_protected_preauthorization(
    tmp_path: Path,
) -> None:
    """A branch-only checkout composes ledger paths from protected preauth."""
    root = tmp_path / "global-sync-ledger-preauth-composition"
    _synthetic_current_tree_repo(root)
    assert not any(
        "global-sync-ledger" in ref
        for ref in subprocess.check_output(
            ["git", "for-each-ref", "--format=%(refname)"], cwd=root, text=True
        ).splitlines()
    )

    inert_paths = {
        "docs/global_sync_evidence_ledger_source.yaml": b"ledger: {}\n",
        "pdd/sync_core/global_sync_ledger.py": b'"""Synthetic ledger."""\n',
        "tests/test_global_sync_ledger.py": b'"""Synthetic ledger test."""\n',
    }
    for path, content in inert_paths.items():
        candidate = root / path
        candidate.parent.mkdir(parents=True, exist_ok=True)
        candidate.write_bytes(content)
    _commit(root, "compose synthetic global-sync ledger paths")

    changed_paths = set(
        subprocess.check_output(
            ["git", "diff", "--name-only", "origin/main...HEAD"],
            cwd=root,
            text=True,
        ).splitlines()
    )
    assert changed_paths == GLOBAL_SYNC_LEDGER_PREAUTHORIZED_PATHS
    for detector in (
        "scripts/ci_detect_changed_modules.py",
        "pdd/ci_detect_changed_modules.py",
    ):
        result = subprocess.run(
            [sys.executable, detector, "--diff-base", "origin/main...HEAD"],
            cwd=root,
            check=False,
            capture_output=True,
            text=True,
        )
        assert result.returncode == 0, result.stderr
        assert not result.stdout.strip()

    manifest = build_unit_manifest(root, base_ref="origin/main", head_ref="HEAD")
    records = {
        item.candidate_id.artifact_relpath.as_posix(): item
        for item in manifest.candidates
        if item.candidate_id.artifact_relpath.as_posix()
        in GLOBAL_SYNC_LEDGER_PREAUTHORIZED_PATHS
    }
    assert set(records) == GLOBAL_SYNC_LEDGER_PREAUTHORIZED_PATHS
    assert not manifest.unaccounted_tracked_paths
    assert not manifest.invalid_reasons
    assert all(
        item.inventory.value == "HUMAN_OWNED"
        and item.candidate_id.role == "human-maintained"
        and item.ownership_provenance == f"protected-ownership:pdd-maintainers:{path}"
        for path, item in records.items()
    )
    assert len(manifest.expected_managed) == EXPECTED_MANAGED_UNITS


def test_pr2017_absent_metadata_authorization_is_exact_six_path_set() -> None:
    """PR #2017 adds only its reviewed metadata-path authorization rows."""
    skip_if_authenticated_candidate_lacks_refs(
        ROOT,
        "exact #2017 protected history",
        PR_2017_PHASE_A_BASE,
        PR_2017_PHASE_A_HEAD,
    )
    base_ownership = json.loads(
        subprocess.check_output(
            [
                "git",
                "show",
                f"{PR_2017_PHASE_A_BASE}:{OWNERSHIP_PATH.relative_to(ROOT)}",
            ],
            cwd=ROOT,
            text=True,
        )
    )
    phase_a_ownership = json.loads(
        subprocess.check_output(
            [
                "git",
                "show",
                f"{PR_2017_PHASE_A_HEAD}:{OWNERSHIP_PATH.relative_to(ROOT)}",
            ],
            cwd=ROOT,
            text=True,
        )
    )
    base_rules = base_ownership["rules"]
    phase_a_rules = phase_a_ownership["rules"]
    added_rules = [row for row in phase_a_rules if row not in base_rules]

    assert not [row for row in base_rules if row not in phase_a_rules]
    assert len(PR_2017_ABSENT_METADATA_PATHS) == len(added_rules) == 6
    assert {row["pattern"] for row in added_rules} == PR_2017_ABSENT_METADATA_PATHS
    assert added_rules == sorted(added_rules, key=lambda row: row["pattern"])
    assert all(
        row == {"pattern": row["pattern"], **PREAUTHORIZED_CHILD_OWNERSHIP}
        for row in added_rules
    )


def test_issue_2083_vitest_coordinator_paths_are_exactly_preauthorized() -> None:
    """The coordinator prerequisite grants no authority beyond three paths."""
    ownership = json.loads(OWNERSHIP_PATH.read_text(encoding="utf-8"))
    rules = {row["pattern"]: row for row in ownership["rules"]}
    matching_rules = [
        row
        for row in ownership["rules"]
        if row["pattern"] in ISSUE_2083_VITEST_COORDINATOR_PREAUTHORIZED_PATHS
    ]
    assert len(matching_rules) == len(ISSUE_2083_VITEST_COORDINATOR_PREAUTHORIZED_PATHS)
    assert {
        path: rules.get(path)
        for path in ISSUE_2083_VITEST_COORDINATOR_PREAUTHORIZED_PATHS
    } == {
        path: {
            "pattern": path,
            **PREAUTHORIZED_CHILD_OWNERSHIP,
        }
        for path in ISSUE_2083_VITEST_COORDINATOR_PREAUTHORIZED_PATHS
    }


def test_issue_2083_preauthorized_paths_are_not_candidate_bootstrap_rules() -> None:
    """Protected-main coordinator paths cannot expand candidate bootstrap authority."""
    bootstrap_paths = {rule.pattern for rule in _BOOTSTRAP_HUMAN_OWNERSHIP}
    assert bootstrap_paths.isdisjoint(ISSUE_2083_VITEST_COORDINATOR_PREAUTHORIZED_PATHS)


def _bootstrap_head_entry_fixture(monkeypatch) -> None:
    """Treat each reviewed story path as absent in base and present in head."""
    paths = {PurePosixPath(rule.pattern) for rule in _BOOTSTRAP_HUMAN_OWNERSHIP}
    monkeypatch.setattr(
        manifest_module,
        "read_git_tree_entry",
        lambda _root, ref, path: object() if ref == "head" and path in paths else None,
    )


@pytest.mark.parametrize(
    "field,value",
    (
        ("inventory", InventoryStatus.MANAGED),
        ("role", "excluded-project"),
        ("owner", "untrusted-owner"),
        ("preauthorize_absent", False),
        ("pattern", "pdd/schemas/unreviewed.json"),
    ),
)
def test_story_bootstrap_rejects_mutated_exact_rule(monkeypatch, field, value) -> None:
    """Any mutation of a reviewed row loses only that row's authority."""
    _bootstrap_head_entry_fixture(monkeypatch)
    mutated = list(_BOOTSTRAP_HUMAN_OWNERSHIP)
    mutated[0] = replace(mutated[0], **{field: value})

    result = _bootstrap_ownership_rules(
        ROOT,
        "3b4d7b1c-d6cc-4752-ba93-6b98d1a710e0",
        "base",
        "head",
        (),
        tuple(mutated),
    )

    assert result == tuple(_BOOTSTRAP_HUMAN_OWNERSHIP[1:])


def test_story_bootstrap_ignores_extra_candidate_rule(monkeypatch) -> None:
    """An extra exact-looking row cannot expand the immutable bootstrap set."""
    _bootstrap_head_entry_fixture(monkeypatch)
    extra = OwnershipRule(
        "docs/unreviewed.md",
        InventoryStatus.HUMAN_OWNED,
        "human-maintained",
        "pdd-maintainers",
        True,
    )
    result = _bootstrap_ownership_rules(
        ROOT,
        "3b4d7b1c-d6cc-4752-ba93-6b98d1a710e0",
        "base",
        "head",
        (),
        (*_BOOTSTRAP_HUMAN_OWNERSHIP, extra),
    )

    assert result == tuple(_BOOTSTRAP_HUMAN_OWNERSHIP)
    assert extra not in result


def test_replay_bootstrap_requires_each_exact_ordinary_candidate_rule(
    monkeypatch,
) -> None:
    """The rebased replay cannot self-authorize or widen its ownership set."""
    paths = {PurePosixPath(rule.pattern) for rule in _REPLAY_HUMAN_OWNERSHIP}
    monkeypatch.setattr(
        manifest_module,
        "read_git_tree_entry",
        lambda _root, ref, path: object() if ref == "head" and path in paths else None,
    )
    mutated = list(_REPLAY_HUMAN_OWNERSHIP)
    mutated[0] = replace(mutated[0], owner="untrusted-owner")

    result = _bootstrap_ownership_rules(
        ROOT,
        REPOSITORY_ID,
        "base",
        "head",
        (),
        tuple(mutated),
    )

    expected = tuple(
        replace(rule, preauthorize_absent=True) for rule in _REPLAY_HUMAN_OWNERSHIP[1:]
    )
    assert result == expected


@pytest.mark.parametrize(
    "mutation",
    ("mutated", "repository", "path", "present-in-base"),
)
def test_replay_bootstrap_weakening_exception_fails_closed(
    monkeypatch, mutation
) -> None:
    """Only the reviewed, absent exact replay paths may bridge policy stages."""
    head_rules = tuple(_REPLAY_HUMAN_OWNERSHIP)
    repository_id = REPOSITORY_ID
    base_paths: set[PurePosixPath] = set()
    if mutation == "mutated":
        head_rules = (replace(head_rules[0], owner="untrusted-owner"), *head_rules[1:])
    elif mutation == "repository":
        repository_id = "not-the-pdd-repository"
    elif mutation == "path":
        head_rules = (
            replace(head_rules[0], pattern="docs/unreviewed.md"),
            *head_rules[1:],
        )
    elif mutation == "present-in-base":
        base_paths.add(PurePosixPath(head_rules[0].pattern))

    paths = {PurePosixPath(rule.pattern) for rule in head_rules}
    monkeypatch.setattr(
        manifest_module,
        "read_git_tree_entry",
        lambda _root, ref, path: (
            object()
            if (ref == "head" and path in paths)
            or (ref == "base" and path in base_paths)
            else None
        ),
    )

    pairs = _replay_bootstrap_weakenings(
        ROOT, repository_id, "base", "head", (), head_rules
    )
    assert all(pair[0].pattern != _REPLAY_HUMAN_OWNERSHIP[0].pattern for pair in pairs)
    assert len(pairs) == (
        0 if mutation == "repository" else len(_REPLAY_HUMAN_OWNERSHIP) - 1
    )
    monkeypatch.setattr(decommission_module, "read_git_blob", lambda *_args: b"{}")
    effective_rules = tuple(
        replace(rule, preauthorize_absent=True) for rule in _REPLAY_HUMAN_OWNERSHIP
    )
    invalid = decommission_module.control_transition_invalid(
        ROOT, "base", "head", effective_rules, head_rules, pairs
    )
    assert any(
        reason.endswith(_REPLAY_HUMAN_OWNERSHIP[0].pattern) for reason in invalid
    )


def test_story_bootstrap_is_repository_bound(monkeypatch) -> None:
    """The exact paths are not a generic candidate-only ownership escape."""
    skip_if_authenticated_candidate_lacks_refs(
        ROOT, "repository identity verification", "HEAD"
    )
    _bootstrap_head_entry_fixture(monkeypatch)
    result = _bootstrap_ownership_rules(
        ROOT,
        "not-the-pdd-repository",
        "base",
        "head",
        (),
        tuple(_BOOTSTRAP_HUMAN_OWNERSHIP),
    )

    assert result == ()
