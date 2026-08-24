"""Protected PDD inventory rollout policy tests."""

from __future__ import annotations

import copy
import hashlib
import io
import json
import re
import subprocess
import sys
import tarfile
from dataclasses import replace
from functools import cache
from pathlib import Path, PurePosixPath
from types import SimpleNamespace

import pytest
import yaml

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


def _paths_added_since(base_ref: str, head_ref: str = "HEAD") -> frozenset[str]:
    """Repository paths tracked at ``head_ref`` but absent from ``base_ref``.

    ``manifest._ownership_rules`` loads ownership *only* from the protected
    base tree. A few regressions below pin a historical base commit in order to
    re-verify one exact transition, so any file added to the repository after
    that pin necessarily has no ownership rule in it — permanently, since the
    pin never moves.

    Left unfiltered, that turns those regressions into a blanket ban on adding
    files: every later PR fails them with "tracked path has no ownership rule"
    for paths that have nothing to do with the transition under test. Coverage
    is not lost by excluding them, because auto-heal builds the same manifest
    with ``base_ref=origin/main`` — a base that does move — and that is where a
    genuinely unowned new path is caught.
    """
    added = subprocess.check_output(
        ["git", "diff", "--diff-filter=A", "--name-only", base_ref, head_ref],
        cwd=ROOT,
        text=True,
    )
    return frozenset(line.strip() for line in added.splitlines() if line.strip())


def _invalid_reasons_for_base_paths(
    manifest, base_ref: str, head_ref: str = "HEAD"
) -> tuple[str, ...]:
    """``manifest.invalid_reasons`` minus paths added after ``base_ref``."""
    ignored = _paths_added_since(base_ref, head_ref)
    return tuple(
        reason
        for reason in manifest.invalid_reasons
        if reason.split(":", 1)[0].strip() not in ignored
    )


def _unaccounted_base_paths(
    manifest, base_ref: str, head_ref: str = "HEAD"
) -> tuple[PurePosixPath, ...]:
    """``manifest.unaccounted_tracked_paths`` minus post-base additions."""
    ignored = _paths_added_since(base_ref, head_ref)
    return tuple(
        path for path in manifest.unaccounted_tracked_paths if path.as_posix() not in ignored
    )


EXPECTED_PATH = ROOT / ".pdd" / "expected-managed.json"
OWNERSHIP_PATH = ROOT / ".pdd" / "sync-ownership.json"
PROFILE_FILE = ROOT / PROFILE_REL_PATH
ROTATION_FILE = ROOT / ".pdd" / "verification-profile-rotations.json"
AUTO_HEAL_WORKFLOW_PATH = ROOT / ".github" / "workflows" / "auto-heal.yml"
REPOSITORY_ID = "3b4d7b1c-d6cc-4752-ba93-6b98d1a710e0"
EXPECTED_MANAGED_UNITS = 475
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
# The historical #1875 profile candidate, retained independently from later
# prompt/profile reconciliations on the active branch.
PDD_1875_COMPOSED_HEAD = "b27837fd7fbf681bdec2b7eb311348b642b27979"
TERRA_SOL_PROTECTED_BASE = "b27837fd7fbf681bdec2b7eb311348b642b27979"
TERRA_SOL_COMPOSED_HEAD = "b3902318c35c279e49e6397838825c95bd568942"
SYNC_ROLLOUT_PROTECTED_BASE = "dec539aa8d0697e357e2077c1dbc73b0621aa617"
PR_2316_HISTORICAL_CANDIDATE = "817abe2d0d41355175c3e09b994928c166917123"
PR_2316_PHASE_A_PROTECTED = "8ac79847ff41f6cafd03b2074bfb4d7893d7b0c6"
PR_2316_PHASE_A_POLICY_SHA256 = (
    "4e3ca5e64238e7137fedc7c562b2dd5a2e61db61dae422f85c0aaebbc86cb6bb"
)
PR_2316_PHASE_A_PREDECESSOR_POLICY_SHA256 = (
    "3b5117e0ef31b19b68d7190f0753e7aacaef3f75133cabfe4c2470afe87c0a95"
)
PR_2316_PHASE_A_PROFILE_SHA256 = (
    "ffd7a11fb15a7aebb20c8199d506cf2deb8bb405b952dcda8444563c24e7a912"
)
PR_2316_PHASE_B_PROFILE_SHA256 = (
    "a2071278af121c6b41b93a2630041541292d70a4acec40751c34dcfdb1b77a9f"
)
PR_2316_PHASE_A_PROMPT_TREE_SHA256 = (
    "b1ea7718f06089e9f1d9edcb611c8483f495478958e85e8ee65d320cd14d714f"
)
PR_2316_PHASE_B_PROMPT_TREE_SHA256 = (
    "637087072d0cb5357b99348b962844b4c8da054b3dd382fc2798728995353bd4"
)
PR_2316_PHASE_B_LLM_INVOKE_PROMPT_SHA256 = (
    "10129606f47d4301052490b7767acc08d8fc713e48bcb2b867efadf2063f8d1e"
)
PR_2316_PHASE_B_MODEL_TESTER_PROMPT_SHA256 = (
    "4ab43d1625c4229c4088c6d71cdf92aadbe92b3467cde71b1f24d774b7cfc501"
)
RELEASE_VIDEO_OPT_OUT_PROTECTED_BASE = "c93332e9bc5956677280a3a015c32d16c99b54cb"
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
# These historical transition assertions build their manifests from frozen
# commits that predate the six conformance units on the current branch.
PDD_1875_EXPECTED_MANAGED_UNITS = 469
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
GLOBAL_SYNC_M0_PREAUTHORIZED_PATHS = {
    "docs/archive/global_sync_resolution_plan_history_2026-07-22.md",
    "docs/global_sync_execution_state.yaml",
    "docs/global_sync_m0_sample_metrics.json",
    "docs/global_sync_m0_sample_results.json",
    "docs/global_sync_m0_scope_report.md",
    "scripts/verify_global_sync_execution_contract.py",
    "scripts/verify_global_sync_m0_samples.py",
}
GLOBAL_SYNC_M0_UNAUTHORIZED_SIBLING_PATHS = {
    "docs/archive/global_sync_resolution_plan_history_2026-07-23.md",
    "docs/global_sync_m0_unreviewed.json",
    "scripts/verify_global_sync_m0_unreviewed.py",
}
KIMI_K3_PROVIDER_CATALOG_PREAUTHORIZED_PATHS = {
    "docs/kimi_k3.md",
    "pdd/data/provider_catalog.v1.json",
    "scripts/bootstrap_provider_catalog.py",
    "scripts/provider_catalog.py",
    "tests/test_kimi_k3_integration.py",
    "tests/test_provider_catalog.py",
}
GLOBAL_SYNC_M0_BOOTSTRAP_PREAUTHORIZED_PATHS = {
    ".github/workflows/global-sync-m0-bootstrap.yml",
    ".pdd/global-sync/m0-bootstrap-policy.json",
    "scripts/verify_global_sync_m0_bootstrap.py",
}
GLOBAL_SYNC_M0_BOOTSTRAP_GLOBAL_SYNC_PREAUTHORIZED_PATHS = {
    ".pdd/global-sync/m0-bootstrap-policy.json",
}
GLOBAL_SYNC_M0_BOOTSTRAP_CANDIDATE_PATHS = (
    GLOBAL_SYNC_M0_BOOTSTRAP_PREAUTHORIZED_PATHS
    | {"scripts/verify_global_sync_m0_samples.py"}
)
GLOBAL_SYNC_M0_BOOTSTRAP_UNAUTHORIZED_SIBLING_PATHS = {
    ".github/workflows/global-sync-m0-bootstrap-unreviewed.yml",
    ".pdd/global-sync/m0-bootstrap-policy-unreviewed.json",
    "scripts/verify_global_sync_m0_bootstrap_unreviewed.py",
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
SYNC_ROLLOUT_EXISTING_METADATA_PATHS = {
    ".pdd/meta/code_generator_python.json",
    ".pdd/meta/code_generator_python_run.json",
    ".pdd/meta/continue_generation_python.json",
    ".pdd/meta/continue_generation_python_run.json",
    ".pdd/meta/detect_change_python.json",
    ".pdd/meta/detect_change_python_run.json",
    ".pdd/meta/generate_test_python.json",
    ".pdd/meta/generate_test_python_run.json",
}
RELEASE_VIDEO_OPT_OUT_EXISTING_PATHS = {
    ".github/workflows/backfill-release-video-discord.yml",
    ".github/workflows/release.yml",
    "Makefile",
    "scripts/backfill_release_video_discord.py",
    "scripts/release_video.py",
    "tests/test_release_video.py",
    "tests/test_release_video_discord_backfill.py",
}
PREAUTHORIZED_CHILD_PATHS = (
    LEGACY_METADATA_EXAMPLE_PREAUTHORIZED_PATHS
    | ISSUE_2083_VITEST_COORDINATOR_PREAUTHORIZED_PATHS
    | GATE1_PREAUTHORIZED_PATHS
    | GLOBAL_SYNC_LEDGER_PREAUTHORIZED_PATHS
    | GLOBAL_SYNC_M0_PREAUTHORIZED_PATHS
    | KIMI_K3_PROVIDER_CATALOG_PREAUTHORIZED_PATHS
    | GLOBAL_SYNC_M0_BOOTSTRAP_PREAUTHORIZED_PATHS
    | GLOBAL_SYNC_RUNTIME_LOCK_PREAUTHORIZED_PATHS
    | STANDALONE_CHECKER_PREAUTHORIZED_PATHS
    | PR_2017_ABSENT_METADATA_PATHS
    | {
        "pdd/conformance/__init__.py",
        "scripts/validate_conformance_prompts.py",
        "tests/test_conformance_prompt_compatibility_exports.py",
        "tests/story_regression/test_story_pdd_generation_gates_preserved.py",
        "user_stories/contracts/pdd_generation_gates_preserved.contract.md",
        "user_stories/issues/conformance-gate-split.md",
        "user_stories/story__pdd_generation_gates_preserved.md",
        ".pdd/meta/agentic_architecture_python.json",
        ".pdd/meta/commands_generate_python.json",
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
        ".pdd/meta/postprocess_python.json",
        ".pdd/meta/story_detection_result_python.json",
        ".pdd/meta/unfinished_prompt_python.json",
        "pdd/schemas/story_detection_result.schema.json",
        "pdd/schemas/story_detection_scope.schema.json",
        "scripts/manual_validate_pr_1875.py",
        "tests/test_e2e_story_failure_diagnostics.py",
        "tests/test_story_detection_result.py",
        "research/omlx-qwen38-pi-prime/README.md",
        "research/omlx-qwen38-pi-prime/analyze.py",
        "research/omlx-qwen38-pi-prime/benchmark.py",
        "research/omlx-qwen38-pi-prime/results/2026-08-19-clean.json",
        "tests/test_omlx_pi_prime_benchmark.py",
        "research/omlx-qwen38-pi-deepseek-harness-2026-08-23/README.md",
        "research/omlx-qwen38-pi-deepseek-harness-2026-08-23/analyze.py",
        "research/omlx-qwen38-pi-deepseek-harness-2026-08-23/benchmark.py",
        "research/omlx-qwen38-pi-deepseek-harness-2026-08-23/results/2026-08-23-clean.json",
        "research/omlx-qwen38-pi-deepseek-harness-2026-08-23/revalidate_checkers.py",
        "research/omlx-qwen38-pi-deepseek-harness-2026-08-23/tool-lock/dsh/package-lock.json",
        "research/omlx-qwen38-pi-deepseek-harness-2026-08-23/tool-lock/dsh/package.json",
        "research/omlx-qwen38-pi-deepseek-harness-2026-08-23/tool-lock/pi/package-lock.json",
        "research/omlx-qwen38-pi-deepseek-harness-2026-08-23/tool-lock/pi/package.json",
        "tests/test_omlx_pi_deepseek_harness_benchmark.py",
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
STORY_PROMPT_PHASE_A_POLICY_SHA256 = (
    "b8b1e11ef85bbf76231c69a06f764935a1bdd2577a003d4299a98d62fa4bf67a"
)
STORY_PROMPT_PHASE_A_PROTECTED = (
    "60588697e7aeee2ad6e22332d913927297a8c2e2"
)
STORY_PROMPT_PHASE_A_PROFILE_SHA256 = (
    "85d01008145de7a7bc67bc6b458b7780a1fbaf24f9733708a0a1032ecb49a9f5"
)
STORY_PROMPT_CONSUMED_ROTATION = {
    "prompt_path": "pdd/prompts/user_story_tests_python.prompt",
    "language_id": "python",
    "from_requirement_id": (
        "CONTRACT-SHA256:c63d875cc5d488b8fd9bfdd72ea015f33962d22b5cde90b9be751de55a209e32"
    ),
    "to_requirement_id": (
        "CONTRACT-SHA256:1c467034344d9d87b8225995bc458bc8093e6759dd5c2eed8424b345f69a3ba7"
    ),
    "policy_path": ".pdd/verification-profiles.json",
    "base_policy_sha256": (
        "fe80e8278f3f262f9902e8af6e88f79476f55fcb830929d5c3bea5a87e6e72c3"
    ),
    "head_policy_sha256": (
        "79ac687426546e1c81bbf50f60d7f1067016ec2a9f34d3278bb514a6b1a72836"
    ),
    "base_prompt_sha256": (
        "c63d875cc5d488b8fd9bfdd72ea015f33962d22b5cde90b9be751de55a209e32"
    ),
    "head_prompt_sha256": (
        "1c467034344d9d87b8225995bc458bc8093e6759dd5c2eed8424b345f69a3ba7"
    ),
}
STORY_PROMPT_PHASE_A_REPLACEMENT = {
    "prompt_path": "pdd/prompts/user_story_tests_python.prompt",
    "language_id": "python",
    "from_requirement_id": (
        "CONTRACT-SHA256:1c467034344d9d87b8225995bc458bc8093e6759dd5c2eed8424b345f69a3ba7"
    ),
    "to_requirement_id": (
        "CONTRACT-SHA256:5b1353257a64a25b303d990803bb799da66504af558c3a5e972d95ad5a04bb3b"
    ),
    "policy_path": ".pdd/verification-profiles.json",
    "base_policy_sha256": STORY_PROMPT_PHASE_A_PROFILE_SHA256,
    "head_policy_sha256": (
        "6e765e03761e7dd678e5b02b147c60231c13fc8ab3de3fd722cf1181c017acb7"
    ),
    "base_prompt_sha256": (
        "1c467034344d9d87b8225995bc458bc8093e6759dd5c2eed8424b345f69a3ba7"
    ),
    "head_prompt_sha256": (
        "5b1353257a64a25b303d990803bb799da66504af558c3a5e972d95ad5a04bb3b"
    ),
}

_read_git_blob = verification.read_git_blob


@cache
def _story_prompt_phase_a_protected_blob(path: PurePosixPath) -> bytes | None:
    """Read an immutable Phase-A blob once, outside monkeypatched lookups."""
    return _read_git_blob(ROOT, STORY_PROMPT_PHASE_A_PROTECTED, path)


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


def _synthetic_current_tree_repo(root: Path, ref: str = "HEAD") -> str:
    """Recommit one exact tracked tree without requiring candidate ancestors."""
    root.mkdir()
    archive = subprocess.check_output(["git", "archive", ref], cwd=ROOT)
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
        "candidate_policy": _git_blob(PDD_1875_COMPOSED_HEAD, ROTATION_FILE),
        "base_profile": _git_blob(PDD_1875_PROTECTED_BASE, PROFILE_FILE),
        "candidate_profile": _git_blob(PDD_1875_COMPOSED_HEAD, PROFILE_FILE),
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
    candidate_profile = _git_blob(PDD_1875_COMPOSED_HEAD, PROFILE_FILE)
    base_prompt = _git_blob(PDD_1875_PROTECTED_BASE, ROOT / authorization.prompt_path)
    candidate_prompt = _git_blob(PDD_1875_COMPOSED_HEAD, ROOT / authorization.prompt_path)

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


@pytest.mark.parametrize(
    "mutated_input",
    ("base_policy", "candidate_policy", "base_profile", "candidate_profile"),
)
def test_terra_sol_composed_reconciliation_is_exact(mutated_input: str) -> None:
    """PR #2171 accepts no prompt/profile byte substitution."""
    skip_if_authenticated_candidate_lacks_refs(
        ROOT, "exact Terra/Sol protected history", TERRA_SOL_PROTECTED_BASE
    )
    inputs = {
        "base_policy": _git_blob(TERRA_SOL_PROTECTED_BASE, ROTATION_FILE),
        "candidate_policy": _git_blob(TERRA_SOL_COMPOSED_HEAD, ROTATION_FILE),
        "base_profile": _git_blob(TERRA_SOL_PROTECTED_BASE, PROFILE_FILE),
        "candidate_profile": _git_blob(TERRA_SOL_COMPOSED_HEAD, PROFILE_FILE),
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
    verification._TERRA_SOL_COMPOSED_REQUIREMENT_TRANSITIONS,  # pylint: disable=protected-access
    ids=lambda item: item.prompt_path.name,
)
def test_terra_sol_composed_reconciliation_binds_prompt_bytes(authorization) -> None:
    """Every PR #2171 profile update is bound to its exact prompt pair."""
    skip_if_authenticated_candidate_lacks_refs(
        ROOT, "exact Terra/Sol protected history", TERRA_SOL_PROTECTED_BASE
    )
    base_profile = _git_blob(TERRA_SOL_PROTECTED_BASE, PROFILE_FILE)
    candidate_profile = _git_blob(TERRA_SOL_COMPOSED_HEAD, PROFILE_FILE)
    base_prompt = _git_blob(TERRA_SOL_PROTECTED_BASE, ROOT / authorization.prompt_path)
    candidate_prompt = _git_blob(
        TERRA_SOL_COMPOSED_HEAD, ROOT / authorization.prompt_path
    )

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


def test_terra_sol_composed_reconciliation_consumes_only_reviewed_scope() -> None:
    """The protected base reaches a complete profile set only via the exact pair."""
    skip_if_authenticated_candidate_lacks_refs(
        ROOT, "exact Terra/Sol protected history", TERRA_SOL_PROTECTED_BASE
    )
    manifest = build_unit_manifest(
        ROOT, base_ref=TERRA_SOL_PROTECTED_BASE, head_ref=TERRA_SOL_COMPOSED_HEAD
    )

    profiles = load_verification_profiles(ROOT, manifest)

    assert not manifest.invalid_reasons
    assert not profiles.invalid_reasons
    assert profiles.coverage == 1.0


def _new_requirement_authorizations(
    base_ref: str, head_ref: str
) -> tuple[verification._RequirementTransitionAuthorization, ...]:  # pylint: disable=protected-access
    """Load newly installed rows through the production exact-ref boundary."""
    manifest = build_unit_manifest(ROOT, base_ref=base_ref, head_ref=head_ref)
    approved_aliases = verification.load_protected_aliases(ROOT, manifest)
    base, base_invalid = verification._load_inputs(  # pylint: disable=protected-access
        ROOT, manifest.base_ref, manifest.repository_id, approved_aliases
    )
    head, head_invalid = verification._load_inputs(  # pylint: disable=protected-access
        ROOT, manifest.head_ref, manifest.repository_id, approved_aliases
    )
    assert not base_invalid
    assert not head_invalid
    _, _, new_authorizations = (
        verification._load_requirement_transition_authorizations(  # pylint: disable=protected-access
            ROOT, manifest, base, head, approved_aliases
        )
    )
    return new_authorizations


def _story_prompt_phase_a_policy(protected_policy: bytes) -> bytes:
    """Build the exact direct replacement allowed after source consumption."""
    assert hashlib.sha256(protected_policy).hexdigest() == (
        verification._PR2376_DEPENDENCY_FIX_ROTATION_POLICY_BYTES[1]  # pylint: disable=protected-access
    )
    payload = json.loads(protected_policy)
    obsolete = next(
        row
        for row in payload["requirement_rotations"]
        if row["prompt_path"] == STORY_PROMPT_CONSUMED_ROTATION["prompt_path"]
        and row["from_requirement_id"]
        == STORY_PROMPT_CONSUMED_ROTATION["from_requirement_id"]
    )
    assert obsolete == STORY_PROMPT_CONSUMED_ROTATION
    payload["requirement_rotations"].remove(obsolete)
    payload["requirement_rotations"].append(
        copy.deepcopy(STORY_PROMPT_PHASE_A_REPLACEMENT)
    )
    candidate = (json.dumps(payload, indent=2) + "\n").encode("utf-8")
    assert hashlib.sha256(candidate).hexdigest() == STORY_PROMPT_PHASE_A_POLICY_SHA256
    return candidate


def _story_prompt_phase_a_manifest_with_blobs(
    monkeypatch,
    manifest,
    protected_policy: bytes,
    candidate_policy: bytes,
    protected_profile: bytes,
    candidate_profile: bytes,
    candidate_prompt_bytes: dict[PurePosixPath, bytes] | None = None,
):  # pylint: disable=too-many-arguments,too-many-positional-arguments
    """Bind synthetic Phase-A policy, profile, and prompt blobs to exact refs."""
    candidate_prompt_bytes = (
        {} if candidate_prompt_bytes is None else candidate_prompt_bytes
    )
    def phase_a_read(_root: Path, ref: str, path: PurePosixPath) -> bytes | None:
        if path == verification.ROTATION_POLICY_PATH:
            return protected_policy if ref == "protected" else candidate_policy
        if path == PROFILE_REL_PATH:
            return protected_profile if ref == "protected" else candidate_profile
        if ref == "candidate" and path in candidate_prompt_bytes:
            return candidate_prompt_bytes[path]
        return _story_prompt_phase_a_protected_blob(path)

    monkeypatch.setattr(verification, "read_git_blob", phase_a_read)
    candidate_paths = set(candidate_prompt_bytes)
    bound_paths = {
        item.candidate_id.artifact_relpath
        for item in manifest.candidates
        if item.candidate_id.artifact_relpath in candidate_paths
    }
    assert bound_paths == candidate_paths
    candidate_records = tuple(
        replace(
            item,
            head_object_id=hashlib.sha1(
                candidate_prompt_bytes[item.candidate_id.artifact_relpath]
            ).hexdigest(),
        )
        if item.candidate_id.artifact_relpath in candidate_prompt_bytes
        else item
        for item in manifest.candidates
    )
    return replace(
        manifest,
        refs=ManifestRefs("protected", "candidate"),
        candidates=candidate_records,
    )


def _load_story_prompt_phase_a_authorizations(  # pylint: disable=too-many-arguments,too-many-positional-arguments
    monkeypatch,
    manifest,
    protected_policy: bytes,
    candidate_policy: bytes,
    protected_profile: bytes,
    candidate_profile: bytes,
) -> tuple[
    tuple[verification._RequirementTransitionAuthorization, ...],
    tuple[verification._RequirementTransitionAuthorization, ...],
]:
    """Load a synthesized Phase-A policy through the production boundary."""
    manifest = _story_prompt_phase_a_manifest_with_blobs(
        monkeypatch,
        manifest,
        protected_policy,
        candidate_policy,
        protected_profile,
        candidate_profile,
    )
    base, base_invalid = verification._load_inputs(  # pylint: disable=protected-access
        ROOT, manifest.base_ref, manifest.repository_id, {}
    )
    head, head_invalid = verification._load_inputs(  # pylint: disable=protected-access
        ROOT, manifest.head_ref, manifest.repository_id, {}
    )
    assert not base_invalid
    assert not head_invalid
    authorizations, _prompts, new_authorizations = (
        verification._load_requirement_transition_authorizations(  # pylint: disable=protected-access
            ROOT, manifest, base, head, {}
        )
    )
    return authorizations, new_authorizations


def _load_story_prompt_phase_a_profiles(
    monkeypatch,
    manifest,
    protected_policy: bytes,
    candidate_policy: bytes,
    protected_profile: bytes,
    candidate_profile: bytes,
    candidate_prompt_bytes: dict[PurePosixPath, bytes],
):  # pylint: disable=too-many-arguments,too-many-positional-arguments
    """Exercise synthesized Phase-A blobs through the public profile loader."""
    manifest = _story_prompt_phase_a_manifest_with_blobs(
        monkeypatch,
        manifest,
        protected_policy,
        candidate_policy,
        protected_profile,
        candidate_profile,
        candidate_prompt_bytes,
    )
    return load_verification_profiles(ROOT, manifest)


@pytest.fixture(scope="module")
def story_prompt_phase_a_manifest():
    """Provide the unchanged protected inventory for every Phase-A candidate."""
    manifest = build_unit_manifest(
        ROOT,
        base_ref=STORY_PROMPT_PHASE_A_PROTECTED,
        head_ref=STORY_PROMPT_PHASE_A_PROTECTED,
    )
    assert not manifest.invalid_reasons
    return manifest


def test_story_prompt_phase_a_consumed_replacement_is_exact(  # pylint: disable=redefined-outer-name
    monkeypatch, story_prompt_phase_a_manifest
) -> None:
    """Only the reviewed direct consumed-row replacement preserves overlays."""
    protected_policy = _git_blob(STORY_PROMPT_PHASE_A_PROTECTED, ROTATION_FILE)
    profile = _git_blob(STORY_PROMPT_PHASE_A_PROTECTED, PROFILE_FILE)
    candidate_policy = _story_prompt_phase_a_policy(protected_policy)
    assert hashlib.sha256(profile).hexdigest() == STORY_PROMPT_PHASE_A_PROFILE_SHA256

    with monkeypatch.context() as phase_a_monkeypatch:
        authorizations, _new_authorizations = (
            _load_story_prompt_phase_a_authorizations(
                phase_a_monkeypatch,
                story_prompt_phase_a_manifest,
                protected_policy,
                candidate_policy,
                profile,
                profile,
            )
        )
    assert [
        _requirement_authorization_row(item)
        for item in authorizations
        if item.prompt_path.as_posix()
        == STORY_PROMPT_PHASE_A_REPLACEMENT["prompt_path"]
    ] == [STORY_PROMPT_PHASE_A_REPLACEMENT]

    with monkeypatch.context() as public_loader_monkeypatch:
        profiles = _load_story_prompt_phase_a_profiles(
            public_loader_monkeypatch,
            story_prompt_phase_a_manifest,
            protected_policy,
            candidate_policy,
            profile,
            profile,
            {},
        )
    assert not profiles.invalid_reasons
    assert profiles.coverage == 1.0

    with monkeypatch.context() as stationary_monkeypatch:
        authorizations, new_authorizations = (
            _load_story_prompt_phase_a_authorizations(
                stationary_monkeypatch,
                story_prompt_phase_a_manifest,
                candidate_policy,
                candidate_policy,
                profile,
                profile,
            )
        )
    assert [
        _requirement_authorization_row(item)
        for item in authorizations
        if item.prompt_path.as_posix()
        == STORY_PROMPT_PHASE_A_REPLACEMENT["prompt_path"]
    ] == [STORY_PROMPT_PHASE_A_REPLACEMENT]
    assert not new_authorizations


@pytest.mark.parametrize("mutation", ("policy-bytes", "row-binding", "profile-bytes"))
def test_story_prompt_phase_a_consumed_replacement_rejects_nearby_bytes(  # pylint: disable=redefined-outer-name
    monkeypatch, mutation: str, story_prompt_phase_a_manifest
) -> None:
    """The direct replacement cannot become reusable authority by mutation."""
    protected_policy = _git_blob(STORY_PROMPT_PHASE_A_PROTECTED, ROTATION_FILE)
    profile = _git_blob(STORY_PROMPT_PHASE_A_PROTECTED, PROFILE_FILE)
    candidate_policy = _story_prompt_phase_a_policy(protected_policy)
    candidate_profile = profile
    if mutation == "policy-bytes":
        candidate_policy += b" "
    elif mutation == "row-binding":
        payload = json.loads(candidate_policy)
        payload["requirement_rotations"][-1]["head_policy_sha256"] = "0" * 64
        candidate_policy = (json.dumps(payload, indent=2) + "\n").encode("utf-8")
    else:
        assert mutation == "profile-bytes"
        candidate_profile += b" "

    with pytest.raises(verification.VerificationProfileError):
        _load_story_prompt_phase_a_authorizations(
            monkeypatch,
            story_prompt_phase_a_manifest,
            protected_policy,
            candidate_policy,
            profile,
            candidate_profile,
        )


@pytest.mark.parametrize(
    "prompt_path",
    (
        PurePosixPath(STORY_PROMPT_PHASE_A_REPLACEMENT["prompt_path"]),
        PurePosixPath("pdd/prompts/code_generator_main_python.prompt"),
    ),
    ids=("target-prompt", "unrelated-managed-prompt"),
)
def test_story_prompt_phase_a_consumed_replacement_rejects_managed_prompt_drift(  # pylint: disable=redefined-outer-name
    monkeypatch, prompt_path: PurePosixPath, story_prompt_phase_a_manifest
) -> None:
    """The exact Phase-A exception rejects target and unrelated prompt drift."""
    protected_policy = _git_blob(STORY_PROMPT_PHASE_A_PROTECTED, ROTATION_FILE)
    profile = _git_blob(STORY_PROMPT_PHASE_A_PROTECTED, PROFILE_FILE)
    candidate_policy = _story_prompt_phase_a_policy(protected_policy)
    candidate_prompt = _git_blob(
        STORY_PROMPT_PHASE_A_PROTECTED, ROOT / prompt_path
    ) + b"\n% unauthorized drift\n"

    with pytest.raises(verification.VerificationProfileError) as error:
        _load_story_prompt_phase_a_profiles(
            monkeypatch,
            story_prompt_phase_a_manifest,
            protected_policy,
            candidate_policy,
            profile,
            profile,
            {prompt_path: candidate_prompt},
        )
    assert str(error.value) == (
        f"candidate retirement changes managed prompt bytes: {prompt_path}"
    )


def test_gemini_phase_a_policy_binds_exactly_two_future_authorizations() -> None:
    """The stable Phase-A policy contains only the two reviewed Gemini rows."""
    policy = json.loads(ROTATION_FILE.read_text(encoding="utf-8"))
    current_profile, future_profile = verification._GEMINI_36_PROFILE_BYTES
    rows = {
        (item["prompt_path"], item["language_id"])
        for item in policy["requirement_rotations"]
        if item["base_policy_sha256"] == current_profile
        and item["head_policy_sha256"] == future_profile
    }

    assert rows == {
        ("pdd/prompts/generate_model_catalog_python.prompt", "python"),
        ("pdd/prompts/llm_invoke_python.prompt", "python"),
    }


def test_gemini_phase_b_base_has_no_synthetic_new_authorizations() -> None:
    """The merged Phase-A state cannot block later prompt-only consumption."""
    assert _new_requirement_authorizations("HEAD", "HEAD") == ()


def _git_blob(ref: str, path: Path) -> bytes:
    """Read one historical policy byte sequence without rewriting it."""
    return subprocess.check_output(
        ["git", "show", f"{ref}:{path.relative_to(ROOT)}"], cwd=ROOT
    )


def _pr2316_phase_a_policy(protected_policy: bytes) -> bytes:
    """Build the separately prepared schema-3 Phase-A bytes exactly."""
    payload = json.loads(protected_policy)
    if payload["schema_version"] == 3:
        candidate = (json.dumps(payload, indent=2) + "\n").encode("utf-8")
        assert hashlib.sha256(candidate).hexdigest() == PR_2316_PHASE_A_POLICY_SHA256
        return candidate
    assert payload["schema_version"] == 2
    obsolete = next(
        item
        for item in payload["requirement_rotations"]
        if item["prompt_path"] == "pdd/prompts/llm_invoke_python.prompt"
        and item["base_prompt_sha256"]
        == "15c51e9dbc3bb536ab6d6dfa1a7927a30f33b1423398e326e5a06f9524896735"
    )
    llm_replacement = {
        "prompt_path": "pdd/prompts/llm_invoke_python.prompt",
        "language_id": "python",
        "from_requirement_id": (
            "CONTRACT-SHA256:09e5140c01bbf8136f4c487c873c816f8e75db75412c11794a8b7ea47259cf3c"
        ),
        "to_requirement_id": (
            "CONTRACT-SHA256:10129606f47d4301052490b7767acc08d8fc713e48bcb2b867efadf2063f8d1e"
        ),
        "policy_path": ".pdd/verification-profiles.json",
        "base_policy_sha256": (
            "ffd7a11fb15a7aebb20c8199d506cf2deb8bb405b952dcda8444563c24e7a912"
        ),
        "head_policy_sha256": (
            "a2071278af121c6b41b93a2630041541292d70a4acec40751c34dcfdb1b77a9f"
        ),
        "base_prompt_sha256": (
            "09e5140c01bbf8136f4c487c873c816f8e75db75412c11794a8b7ea47259cf3c"
        ),
        "head_prompt_sha256": (
            "10129606f47d4301052490b7767acc08d8fc713e48bcb2b867efadf2063f8d1e"
        ),
    }
    model_tester_replacement = {
        "prompt_path": "pdd/prompts/model_tester_python.prompt",
        "language_id": "python",
        "from_requirement_id": (
            "CONTRACT-SHA256:7c020d1e55839dfa7a962df32a3991952466bd3710afa3006122424f3d21c89b"
        ),
        "to_requirement_id": (
            "CONTRACT-SHA256:4ab43d1625c4229c4088c6d71cdf92aadbe92b3467cde71b1f24d774b7cfc501"
        ),
        "policy_path": ".pdd/verification-profiles.json",
        "base_policy_sha256": (
            "ffd7a11fb15a7aebb20c8199d506cf2deb8bb405b952dcda8444563c24e7a912"
        ),
        "head_policy_sha256": (
            "a2071278af121c6b41b93a2630041541292d70a4acec40751c34dcfdb1b77a9f"
        ),
        "base_prompt_sha256": (
            "7c020d1e55839dfa7a962df32a3991952466bd3710afa3006122424f3d21c89b"
        ),
        "head_prompt_sha256": (
            "4ab43d1625c4229c4088c6d71cdf92aadbe92b3467cde71b1f24d774b7cfc501"
        ),
    }
    payload["schema_version"] = 3
    payload["requirement_rotations"].extend(
        (llm_replacement, model_tester_replacement)
    )
    payload["requirement_rotation_retirements"] = [
        {
            "obsolete": copy.deepcopy(obsolete),
            "replacement": copy.deepcopy(llm_replacement),
        }
    ]
    candidate = (json.dumps(payload, indent=2) + "\n").encode("utf-8")
    assert hashlib.sha256(candidate).hexdigest() == PR_2316_PHASE_A_POLICY_SHA256
    return candidate


def _pr2316_phase_a_predecessor_policy(protected_policy: bytes) -> bytes:
    """Recover the exact schema-2 policy protected by the Phase-A transition."""
    payload = json.loads(protected_policy)
    if payload["schema_version"] == 3:
        assert (
            hashlib.sha256(protected_policy).hexdigest()
            == PR_2316_PHASE_A_POLICY_SHA256
        )
        assert len(payload["requirement_rotation_retirements"]) == 1
        replacement = payload["requirement_rotation_retirements"][0]["replacement"]
        assert payload["requirement_rotations"][-2] == replacement
        assert (
            payload["requirement_rotations"][-1]["prompt_path"]
            == "pdd/prompts/model_tester_python.prompt"
        )
        payload["schema_version"] = 2
        del payload["requirement_rotations"][-2:]
        del payload["requirement_rotation_retirements"]
    else:
        assert payload["schema_version"] == 2
    predecessor = (json.dumps(payload, indent=2) + "\n").encode("utf-8")
    assert (
        hashlib.sha256(predecessor).hexdigest()
        == PR_2316_PHASE_A_PREDECESSOR_POLICY_SHA256
    )
    return predecessor


def _replace_expected_bytes(
    source: bytes, old: bytes, new: bytes, expected_count: int
) -> bytes:
    """Replace an exact reviewed byte fixture without normalizing its source."""
    assert source.count(old) == expected_count
    return source.replace(old, new)


def _pr2316_phase_b_profile(phase_a_profile: bytes) -> bytes:
    """Build the byte-exact Phase-B verification profile from Phase A."""
    assert hashlib.sha256(phase_a_profile).hexdigest() == PR_2316_PHASE_A_PROFILE_SHA256
    candidate = _replace_expected_bytes(
        phase_a_profile,
        b"CONTRACT-SHA256:09e5140c01bbf8136f4c487c873c816f8e75db75412c11794a8b7ea47259cf3c",
        b"CONTRACT-SHA256:10129606f47d4301052490b7767acc08d8fc713e48bcb2b867efadf2063f8d1e",
        2,
    )
    candidate = _replace_expected_bytes(
        candidate,
        b"CONTRACT-SHA256:7c020d1e55839dfa7a962df32a3991952466bd3710afa3006122424f3d21c89b",
        b"CONTRACT-SHA256:4ab43d1625c4229c4088c6d71cdf92aadbe92b3467cde71b1f24d774b7cfc501",
        2,
    )
    assert hashlib.sha256(candidate).hexdigest() == PR_2316_PHASE_B_PROFILE_SHA256
    return candidate


def _pr2316_phase_b_llm_invoke_prompt(phase_a_prompt: bytes) -> bytes:
    """Build the reviewed Phase-B llm-invoke prompt from exact Phase-A bytes."""
    assert (
        hashlib.sha256(phase_a_prompt).hexdigest()
        == "09e5140c01bbf8136f4c487c873c816f8e75db75412c11794a8b7ea47259cf3c"
    )
    candidate = _replace_expected_bytes(
        phase_a_prompt,
        b"    - 'use_batch_mode': Use litellm.batch_completion if True.\n",
        (
            b"    - 'use_batch_mode': Use litellm.batch_completion if True, except that "
            b"ChatGPT subscription (`chatgpt/*`) models must fail closed before any "
            b"provider call because their Codex backend supports only the Responses "
            b"endpoint, not chat-completions batching. Tell callers to set "
            b"`use_batch_mode=False` and invoke items individually.\n"
        ),
        1,
    )
    candidate = _replace_expected_bytes(
        candidate,
        (
            b"    - For OpenAI gpt-5* models: Call litellm.responses() API to support "
            b"'reasoning' parameter. Build text.format block for structured output "
            b"(type=json_schema when output_pydantic/output_schema, else type=text). "
            b"Skip temperature for Responses API.\n"
        ),
        (
            b"    - For direct OpenAI gpt-5* API models: Call litellm.responses() to "
            b"support the `reasoning` parameter. Build a `text.format` block for "
            b"structured output (type=json_schema when output_pydantic/output_schema, "
            b"else type=text). Skip temperature for Responses API.\n"
            b"    - For ChatGPT subscription `chatgpt/*` models: always use "
            b"`litellm.responses()` for single invocations. Build list-form Responses "
            b"input from the final messages, preserving supported multimodal content: a "
            b'text/input_text message part becomes `{"type":"input_text","text":...}`, '
            b"and an OpenAI chat-completions `image_url` part (including a data URL from "
            b'code_generator) becomes `{"type":"input_image","image_url":...}`. The '
            b"subscription backend ignores Responses `text.format` and chat-completions "
            b"`response_format`/`json_schema`; when structured output is requested, omit "
            b"those fields and inject the JSON schema as an in-band system-message "
            b"instruction. Never fall back to `litellm.completion()` after a Responses "
            b"error. Batch invocation is unsupported: fail closed before auth/provider "
            b"dispatch with an actionable error rather than calling `litellm.completion()` "
            b"or `litellm.batch_completion()`.\n"
        ),
        1,
    )
    assert (
        hashlib.sha256(candidate).hexdigest()
        == PR_2316_PHASE_B_LLM_INVOKE_PROMPT_SHA256
    )
    return candidate


def _pr2316_phase_b_model_tester_prompt(phase_a_prompt: bytes) -> bytes:
    """Build the reviewed Phase-B model-tester prompt from exact Phase-A bytes."""
    assert (
        hashlib.sha256(phase_a_prompt).hexdigest()
        == "7c020d1e55839dfa7a962df32a3991952466bd3710afa3006122424f3d21c89b"
    )
    candidate = _replace_expected_bytes(
        phase_a_prompt,
        (
            b"<pdd-reason>Tests individual models via litellm.completion() with direct "
            b"API key passing and diagnostics.</pdd-reason>\n"
        ),
        (
            b"<pdd-reason>Tests individual models with provider-appropriate LiteLLM "
            b"calls, direct API key passing, and diagnostics.</pdd-reason>\n"
        ),
        1,
    )
    candidate = _replace_expected_bytes(
        candidate,
        (
            b"Tests a single configured model by making one `litellm.completion()` call "
            b"with a minimal prompt. Only runs when the user explicitly chooses it \xe2\x80\x94 no "
            b"surprise API costs. Uses `litellm.completion()` directly (not `llm_invoke`) "
            b"because `llm_invoke` doesn't allow choosing a specific model or key.\n"
        ),
        (
            b"Tests a single configured model by making one provider-appropriate LiteLLM "
            b"request with a minimal prompt. Only runs when the user explicitly chooses it "
            b"\xe2\x80\x94 no surprise API costs. Uses LiteLLM directly (not `llm_invoke`) because "
            b"`llm_invoke` doesn't allow choosing a specific model or key.\n"
        ),
        1,
    )
    candidate = _replace_expected_bytes(
        candidate,
        (
            b"2. Test call: `litellm.completion(model=..., messages=[...], timeout=8)`. "
            b"Only pass `api_key=` for single-var providers. Preserve the exact "
            b"`claude-opus-5` or `claude-fable-5` catalog model; they are distinct "
            b"Anthropic API identifiers. Strip only an optional `anthropic/` provider "
            b"prefix when required by the direct call.\n"
        ),
        (
            b"2. Test call: normally use `litellm.completion(model=..., messages=[...], "
            b"timeout=8)`. For ChatGPT subscription `chatgpt/*` rows, bridge `codex login` "
            b"credentials and apply the LiteLLM ChatGPT output patch, then use the Codex "
            b'Responses smoke path: `litellm.responses(model=..., input=[{"role":"user",'
            b'"content":[{"type":"input_text","text":"Say OK"}]}], timeout=8)`. '
            b"Treat the smoke test as successful only when the Responses payload contains a "
            b"nonempty `output_text`; an empty or missing response output is a failure. "
            b"Never send `chatgpt/*` smoke tests to chat-completions. Only pass `api_key=` "
            b"for single-var providers. Preserve the exact `claude-opus-5` or "
            b"`claude-fable-5` catalog model; they are distinct Anthropic API identifiers. "
            b"Strip only an optional `anthropic/` provider prefix when required by the "
            b"direct call.\n"
        ),
        1,
    )
    assert (
        hashlib.sha256(candidate).hexdigest()
        == PR_2316_PHASE_B_MODEL_TESTER_PROMPT_SHA256
    )
    return candidate


def _write_pr2316_phase_b_candidate(root: Path) -> None:
    """Synthesize only the exact Phase-B managed bytes from reachable Phase A."""
    policy_path = root / ".pdd" / "verification-profile-rotations.json"
    assert hashlib.sha256(policy_path.read_bytes()).hexdigest() == (
        PR_2316_PHASE_A_POLICY_SHA256
    )
    profile_path = root / ".pdd" / "verification-profiles.json"
    profile_path.write_bytes(_pr2316_phase_b_profile(profile_path.read_bytes()))
    llm_invoke_path = root / "pdd" / "prompts" / "llm_invoke_python.prompt"
    llm_invoke_path.write_bytes(
        _pr2316_phase_b_llm_invoke_prompt(llm_invoke_path.read_bytes())
    )
    model_tester_path = root / "pdd" / "prompts" / "model_tester_python.prompt"
    model_tester_path.write_bytes(
        _pr2316_phase_b_model_tester_prompt(model_tester_path.read_bytes())
    )


def _clone_pr2316_phase_a_history(root: Path) -> None:
    """Clone only the verifier branch's reachable history, without alternates."""
    subprocess.run(
        [
            "git",
            "clone",
            "-q",
            "--no-local",
            "--single-branch",
            "--no-tags",
            str(ROOT),
            str(root),
        ],
        check=True,
        capture_output=True,
    )
    _git(root, "cat-file", "-e", f"{PR_2316_PHASE_A_PROTECTED}^{{commit}}")


def _assert_pr2316_prompt_trees(
    root: Path,
    manifest,
    expected_base: str,
    expected_head: str,
) -> None:
    """Assert the complete managed prompt trees, not just the two target prompts."""
    approved_aliases = verification.load_protected_aliases(root, manifest)
    assert verification._managed_prompt_tree_sha256(  # pylint: disable=protected-access
        root,
        manifest,
        manifest.base_ref,
        approved_aliases,
    ) == expected_base
    assert verification._managed_prompt_tree_sha256(  # pylint: disable=protected-access
        root,
        manifest,
        manifest.head_ref,
        approved_aliases,
    ) == expected_head
def _pr2316_phase_a_predecessor_tree(root: Path) -> tuple[str, bytes]:
    """Rebuild the exact Phase-A predecessor from its pinned protected tree."""
    _synthetic_current_tree_repo(root, PR_2316_PHASE_A_PROTECTED)
    policy_path = root / ".pdd" / "verification-profile-rotations.json"
    phase_a_policy = policy_path.read_bytes()
    assert hashlib.sha256(phase_a_policy).hexdigest() == PR_2316_PHASE_A_POLICY_SHA256
    assert hashlib.sha256(
        (root / ".pdd" / "verification-profiles.json").read_bytes()
    ).hexdigest() == (
        verification._PR2316_STALE_LLM_REISSUE_PHASE_A_PROFILE_BYTES[  # pylint: disable=protected-access
            1
        ]
    )
    exact_policy = _pr2316_phase_a_policy(phase_a_policy)
    predecessor_policy = _pr2316_phase_a_predecessor_policy(phase_a_policy)
    policy_path.write_bytes(predecessor_policy)
    return _commit(root, "synthetic pr2316 protected predecessor"), exact_policy
@pytest.mark.timeout(600)
def test_pr2316_schema_3_legacy_retirement_is_exact_through_production_loader(
    tmp_path,
) -> None:
    """Only the prepared Phase-A bytes can retire the stale llm-invoke row."""
    root = tmp_path / "pr2316-phase-a"
    protected, exact_policy = _pr2316_phase_a_predecessor_tree(root)
    policy_path = root / ".pdd" / "verification-profile-rotations.json"

    def candidate_for(mutation: str, protected_ref: str) -> tuple[str, str]:
        _git(root, "checkout", "-q", "-B", f"pr2316-{mutation}", protected_ref)
        base = protected_ref
        candidate_policy = exact_policy
        if mutation == "altered-policy":
            payload = json.loads(candidate_policy)
            payload["requirement_rotations"][-1]["head_policy_sha256"] = "f" * 64
            candidate_policy = (json.dumps(payload, indent=2) + "\n").encode("utf-8")
        elif mutation == "reformatted-policy":
            candidate_policy = (
                json.dumps(
                    json.loads(candidate_policy), sort_keys=True, separators=(",", ":")
                )
                + "\n"
            ).encode("utf-8")
        elif mutation == "reordered-policy":
            payload = json.loads(candidate_policy)
            payload["requirement_rotations"][-2:] = reversed(
                payload["requirement_rotations"][-2:]
            )
            candidate_policy = (json.dumps(payload, indent=2) + "\n").encode("utf-8")
        elif mutation == "replacement-binding-substitution":
            payload = json.loads(candidate_policy)
            payload["requirement_rotation_retirements"][0]["replacement"][
                "head_policy_sha256"
            ] = "0" * 64
            candidate_policy = (json.dumps(payload, indent=2) + "\n").encode("utf-8")
        elif mutation == "foreign-repository":
            (root / ".pdd" / "repository-id").write_text(
                "e602f876-c944-4fe3-b91b-e8a94a39ecea\n", encoding="ascii"
            )
            base = _commit(root, "foreign protected base")
        policy_path.write_bytes(candidate_policy)
        if mutation == "target-prompt-drift":
            target = root / "pdd" / "prompts" / "llm_invoke_python.prompt"
            target.write_bytes(target.read_bytes() + b"\n# candidate drift\n")
        elif mutation == "unrelated-managed-prompt-drift":
            unrelated = root / "pdd" / "prompts" / "code_generator_python.prompt"
            unrelated.write_bytes(unrelated.read_bytes() + b"\n# candidate drift\n")
        return base, _commit(root, f"pr2316 candidate {mutation}")

    base, head = candidate_for("exact-phase-a", protected)
    manifest = build_unit_manifest(root, base_ref=base, head_ref=head)
    profiles = load_verification_profiles(root, manifest)
    assert manifest.repository_id == REPOSITORY_ID
    assert not manifest.invalid_reasons
    assert not profiles.invalid_reasons
    assert profiles.coverage == 1.0

    for mutation in (
        "altered-policy",
        "reformatted-policy",
        "reordered-policy",
        "replacement-binding-substitution",
        "target-prompt-drift",
        "unrelated-managed-prompt-drift",
        "foreign-repository",
    ):
        base, head = candidate_for(mutation, protected)
        manifest = build_unit_manifest(root, base_ref=base, head_ref=head)
        try:
            profiles = load_verification_profiles(root, manifest)
        except verification.VerificationProfileError:
            continue
        assert manifest.invalid_reasons or profiles.invalid_reasons, mutation


@pytest.mark.timeout(600)
def test_pr2316_historical_legacy_retirement_is_fully_bound_through_production_loader(
    tmp_path,
) -> None:
    """The legacy history accepts only its exact repository, bytes, and tree."""
    root = tmp_path / "pr2316-history"
    subprocess.run(
        ["git", "clone", "-q", "--shared", str(ROOT), str(root)],
        check=True,
        capture_output=True,
    )

    def candidate_for(mutation: str) -> tuple[str, str]:
        _git(
            root,
            "checkout",
            "-q",
            "-B",
            f"pr2316-history-{mutation}",
            SYNC_ROLLOUT_PROTECTED_BASE,
        )
        base = subprocess.check_output(
            ["git", "rev-parse", "HEAD"], cwd=root, text=True
        ).strip()
        repository_id_path = root / ".pdd" / "repository-id"
        if mutation == "foreign-repository":
            repository_id_path.write_text(
                "e602f876-c944-4fe3-b91b-e8a94a39ecea\n", encoding="ascii"
            )
            base = _commit(root, "foreign historical protected base")

        _git(root, "read-tree", "--reset", "-u", PR_2316_HISTORICAL_CANDIDATE)
        policy_path = root / ".pdd" / "verification-profile-rotations.json"
        candidate_policy = _pr2316_phase_a_policy(policy_path.read_bytes())
        if mutation == "replacement-binding-substitution":
            payload = json.loads(candidate_policy)
            payload["requirement_rotation_retirements"][0]["replacement"][
                "head_policy_sha256"
            ] = "0" * 64
            candidate_policy = (json.dumps(payload, indent=2) + "\n").encode("utf-8")
        elif mutation == "policy-formatting":
            candidate_policy += b" "
        policy_path.write_bytes(candidate_policy)

        if mutation == "profile-formatting":
            profile_path = root / ".pdd" / "verification-profiles.json"
            profile_path.write_bytes(profile_path.read_bytes() + b" ")
        elif mutation == "target-prompt-tree-drift":
            target = root / "pdd" / "prompts" / "llm_invoke_python.prompt"
            target.write_bytes(target.read_bytes() + b"\n# candidate drift\n")
        elif mutation == "unrelated-prompt-tree-drift":
            unrelated = root / "pdd" / "prompts" / "code_generator_python.prompt"
            unrelated.write_bytes(unrelated.read_bytes() + b"\n# candidate drift\n")
        elif mutation == "foreign-repository":
            repository_id_path.write_text(
                "e602f876-c944-4fe3-b91b-e8a94a39ecea\n", encoding="ascii"
            )
        return base, _commit(root, f"pr2316 historical candidate {mutation}")

    base, head = candidate_for("exact-history")
    manifest = build_unit_manifest(root, base_ref=base, head_ref=head)
    profiles = load_verification_profiles(root, manifest)
    assert manifest.repository_id == REPOSITORY_ID
    assert not _invalid_reasons_for_base_paths(
        manifest, SYNC_ROLLOUT_PROTECTED_BASE
    )
    assert not _unaccounted_base_paths(manifest, SYNC_ROLLOUT_PROTECTED_BASE)
    assert not profiles.invalid_reasons
    assert profiles.coverage == 1.0

    for mutation in (
        "replacement-binding-substitution",
        "policy-formatting",
        "profile-formatting",
        "target-prompt-tree-drift",
        "unrelated-prompt-tree-drift",
        "foreign-repository",
    ):
        base, head = candidate_for(mutation)
        manifest = build_unit_manifest(root, base_ref=base, head_ref=head)
        try:
            profiles = load_verification_profiles(root, manifest)
        except verification.VerificationProfileError:
            continue
        assert manifest.invalid_reasons or profiles.invalid_reasons, mutation


@pytest.mark.timeout(600)
def test_pr2316_phase_b_transition_is_exact_through_production_loader(tmp_path) -> None:
    """Only the reviewed Phase-B tree may consume the protected replacements."""
    root = tmp_path / "pr2316-phase-b"
    _clone_pr2316_phase_a_history(root)

    def candidate_for(mutation: str) -> tuple[str, str]:
        _git(
            root,
            "checkout",
            "-q",
            "-B",
            f"pr2316-phase-b-{mutation}",
            PR_2316_PHASE_A_PROTECTED,
        )
        base = subprocess.check_output(
            ["git", "rev-parse", "HEAD"], cwd=root, text=True
        ).strip()
        repository_id_path = root / ".pdd" / "repository-id"
        if mutation == "foreign-repository":
            repository_id_path.write_text(
                "e602f876-c944-4fe3-b91b-e8a94a39ecea\n", encoding="ascii"
            )
            base = _commit(root, "foreign pr2316 Phase-B protected base")

        _write_pr2316_phase_b_candidate(root)
        policy_path = root / ".pdd" / "verification-profile-rotations.json"
        if mutation == "policy-formatting":
            policy_path.write_bytes(policy_path.read_bytes() + b" ")
        elif mutation == "replacement-binding-substitution":
            payload = json.loads(policy_path.read_bytes())
            payload["requirement_rotations"][-2]["head_prompt_sha256"] = "0" * 64
            policy_path.write_bytes((json.dumps(payload, indent=2) + "\n").encode())
        elif mutation == "profile-formatting":
            profile_path = root / ".pdd" / "verification-profiles.json"
            profile_path.write_bytes(profile_path.read_bytes() + b" ")
        elif mutation == "target-prompt-drift":
            target = root / "pdd" / "prompts" / "llm_invoke_python.prompt"
            target.write_bytes(target.read_bytes() + b"\n# candidate drift\n")
        elif mutation == "unrelated-managed-prompt-drift":
            unrelated = root / "pdd" / "prompts" / "code_generator_python.prompt"
            unrelated.write_bytes(unrelated.read_bytes() + b"\n# candidate drift\n")
        elif mutation == "foreign-repository":
            repository_id_path.write_text(
                "e602f876-c944-4fe3-b91b-e8a94a39ecea\n", encoding="ascii"
            )
        return base, _commit(root, f"pr2316 Phase-B candidate {mutation}")

    base, head = candidate_for("exact-phase-b")
    manifest = build_unit_manifest(root, base_ref=base, head_ref=head)
    profiles = load_verification_profiles(root, manifest)
    assert manifest.repository_id == REPOSITORY_ID
    assert not manifest.invalid_reasons
    _assert_pr2316_prompt_trees(
        root,
        manifest,
        PR_2316_PHASE_A_PROMPT_TREE_SHA256,
        PR_2316_PHASE_B_PROMPT_TREE_SHA256,
    )
    assert not profiles.invalid_reasons
    assert profiles.coverage == 1.0

    for mutation in (
        "policy-formatting",
        "replacement-binding-substitution",
        "profile-formatting",
        "target-prompt-drift",
        "unrelated-managed-prompt-drift",
        "foreign-repository",
    ):
        base, head = candidate_for(mutation)
        manifest = build_unit_manifest(root, base_ref=base, head_ref=head)
        try:
            profiles = load_verification_profiles(root, manifest)
        except verification.VerificationProfileError:
            continue
        assert manifest.invalid_reasons or profiles.invalid_reasons, mutation


@pytest.mark.timeout(600)
def test_pr2316_phase_b_stationary_state_is_exact_through_production_loader(
    tmp_path,
) -> None:
    """Only the reviewed consumed Phase-B tree retains its historical overlay."""
    root = tmp_path / "pr2316-phase-b-stationary"
    _clone_pr2316_phase_a_history(root)

    def stationary_for(mutation: str) -> tuple[str, str]:
        _git(
            root,
            "checkout",
            "-q",
            "-B",
            f"pr2316-phase-b-stationary-{mutation}",
            PR_2316_PHASE_A_PROTECTED,
        )
        _write_pr2316_phase_b_candidate(root)
        ref = _commit(root, "synthetic pr2316 Phase-B candidate")
        if mutation == "policy-formatting":
            policy_path = root / ".pdd" / "verification-profile-rotations.json"
            policy_path.write_bytes(policy_path.read_bytes() + b" ")
        elif mutation == "profile-formatting":
            profile_path = root / ".pdd" / "verification-profiles.json"
            profile_path.write_bytes(profile_path.read_bytes() + b" ")
        elif mutation == "target-prompt-tree-drift":
            target = root / "pdd" / "prompts" / "llm_invoke_python.prompt"
            target.write_bytes(target.read_bytes() + b"\n# candidate drift\n")
        elif mutation == "unrelated-prompt-tree-drift":
            unrelated = root / "pdd" / "prompts" / "code_generator_python.prompt"
            unrelated.write_bytes(unrelated.read_bytes() + b"\n# candidate drift\n")
        elif mutation == "foreign-repository":
            (root / ".pdd" / "repository-id").write_text(
                "e602f876-c944-4fe3-b91b-e8a94a39ecea\n", encoding="ascii"
            )
        else:
            assert mutation == "exact-stationary"
        if mutation != "exact-stationary":
            ref = _commit(root, f"pr2316 Phase-B stationary {mutation}")
        return ref, ref

    base, head = stationary_for("exact-stationary")
    manifest = build_unit_manifest(root, base_ref=base, head_ref=head)
    profiles = load_verification_profiles(root, manifest)
    assert manifest.repository_id == REPOSITORY_ID
    assert not manifest.invalid_reasons
    _assert_pr2316_prompt_trees(
        root,
        manifest,
        PR_2316_PHASE_B_PROMPT_TREE_SHA256,
        PR_2316_PHASE_B_PROMPT_TREE_SHA256,
    )
    assert not profiles.invalid_reasons
    assert profiles.coverage == 1.0

    for mutation in (
        "policy-formatting",
        "profile-formatting",
        "target-prompt-tree-drift",
        "unrelated-prompt-tree-drift",
        "foreign-repository",
    ):
        base, head = stationary_for(mutation)
        manifest = build_unit_manifest(root, base_ref=base, head_ref=head)
        try:
            profiles = load_verification_profiles(root, manifest)
        except verification.VerificationProfileError:
            continue
        assert manifest.invalid_reasons or profiles.invalid_reasons, mutation


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


def test_pdd1875_phase_a_is_dormant_on_its_composed_head() -> None:
    """The #1875 prerequisite stays dormant at its exact composed head."""
    skip_if_authenticated_candidate_lacks_refs(
        ROOT, "exact #1875 protected history", PDD_1875_PROTECTED_BASE
    )
    manifest = build_unit_manifest(
        ROOT,
        base_ref=PDD_1875_PROTECTED_BASE,
        head_ref=PDD_1875_COMPOSED_HEAD,
    )

    profiles = load_verification_profiles(ROOT, manifest)

    assert len(manifest.expected_managed) == PDD_1875_EXPECTED_MANAGED_UNITS
    assert not manifest.invalid_reasons
    assert len(profiles.profiles) == PDD_1875_EXPECTED_MANAGED_UNITS
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

    assert len(manifest.expected_managed) == PDD_1875_EXPECTED_MANAGED_UNITS
    assert not manifest.invalid_reasons
    assert len(profiles.profiles) == PDD_1875_EXPECTED_MANAGED_UNITS
    assert not profiles.invalid_reasons
    assert profiles.coverage == 1.0


def test_conformance_split_profiles_load_from_actual_merge_base() -> None:
    """The conformance split preserves protected verification history verbatim."""
    skip_if_authenticated_candidate_lacks_refs(ROOT, "origin/main")
    manifest = build_unit_manifest(ROOT, base_ref="origin/main", head_ref="HEAD")

    assert not manifest.invalid_reasons
    profiles = load_verification_profiles(ROOT, manifest)

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


def test_sync_rollout_repair_executes_the_actual_protected_transition() -> None:
    """The rollout repair is valid only through its exact pre-Phase-B head."""
    skip_if_authenticated_candidate_lacks_refs(
        ROOT,
        "exact sync-rollout protected history",
        SYNC_ROLLOUT_PROTECTED_BASE,
        PR_2316_PHASE_A_PROTECTED,
    )
    rollout_head = PR_2316_PHASE_A_PROTECTED
    manifest = build_unit_manifest(
        ROOT,
        base_ref=SYNC_ROLLOUT_PROTECTED_BASE,
        head_ref=rollout_head,
    )

    assert (
        hashlib.sha256(_git_blob(SYNC_ROLLOUT_PROTECTED_BASE, PROFILE_FILE)).hexdigest(),
        hashlib.sha256(_git_blob("HEAD", PROFILE_FILE)).hexdigest(),
    ) in {
        verification._SYNC_ROLLOUT_REPAIR_PROFILE_BYTES,  # pylint: disable=protected-access
        (
            verification._SYNC_ROLLOUT_REPAIR_PROFILE_BYTES[0],  # pylint: disable=protected-access
            verification._TEMPERATURE_REGRESSION_PROFILE_BYTES[1],  # pylint: disable=protected-access
        ),
        (
            verification._SYNC_ROLLOUT_REPAIR_PROFILE_BYTES[0],  # pylint: disable=protected-access
            verification._PR2316_STALE_LLM_REISSUE_PHASE_B_PROFILE_BYTES[1],  # pylint: disable=protected-access
        ),
        (
            verification._SYNC_ROLLOUT_REPAIR_PROFILE_BYTES[0],  # pylint: disable=protected-access
            verification._CODE_GENERATOR_LANGUAGE_GATE_PROFILE_BYTES[1],  # pylint: disable=protected-access
        ),
        (
            verification._SYNC_ROLLOUT_REPAIR_PROFILE_BYTES[0],  # pylint: disable=protected-access
            verification._ZSH_GLOBAL_OPTION_PROFILE_BYTES[1],  # pylint: disable=protected-access
        ),
        (
            verification._SYNC_ROLLOUT_REPAIR_PROFILE_BYTES[0],  # pylint: disable=protected-access
            verification._CONFORMANCE_SPLIT_PROFILE_BYTES[1],  # pylint: disable=protected-access
        ),
        (
            verification._SYNC_ROLLOUT_REPAIR_PROFILE_BYTES[0],  # pylint: disable=protected-access
            verification._PR2376_DEPENDENCY_FIX_PROFILE_BYTES[1],  # pylint: disable=protected-access
        ),
        # Phase B consumes the preauthorized story row without changing this
        # historical repair's policy or prompt bytes.
        (
            verification._SYNC_ROLLOUT_REPAIR_PROFILE_BYTES[0],  # pylint: disable=protected-access
            verification._STORY_PROMPT_PHASE_B_PROFILE_BYTES[1],  # pylint: disable=protected-access
        ),
    }
    assert (
        hashlib.sha256(_git_blob(SYNC_ROLLOUT_PROTECTED_BASE, ROTATION_FILE)).hexdigest(),
        hashlib.sha256(_git_blob(rollout_head, ROTATION_FILE)).hexdigest(),
    ) in {
        verification._SYNC_ROLLOUT_REPAIR_ROTATION_POLICY_BYTES,  # pylint: disable=protected-access
        verification._PR2316_STALE_LLM_REISSUE_ROTATION_POLICY_BYTES,  # pylint: disable=protected-access
    }
    for prompt_path, _language_id, expected_digest in (
        verification._SYNC_ROLLOUT_REPAIR_PROMPT_BYTES  # pylint: disable=protected-access
    ):
        assert (
            hashlib.sha256(
                _git_blob(SYNC_ROLLOUT_PROTECTED_BASE, ROOT / prompt_path)
            ).hexdigest(),
            hashlib.sha256(_git_blob(rollout_head, ROOT / prompt_path)).hexdigest(),
        ) == (expected_digest, expected_digest)

    records = {
        item.candidate_id.artifact_relpath.as_posix(): item
        for item in manifest.candidates
        if item.candidate_id.artifact_relpath.as_posix()
        in SYNC_ROLLOUT_EXISTING_METADATA_PATHS
    }
    assert not _invalid_reasons_for_base_paths(
        manifest, SYNC_ROLLOUT_PROTECTED_BASE, rollout_head
    )
    assert not _unaccounted_base_paths(
        manifest, SYNC_ROLLOUT_PROTECTED_BASE, rollout_head
    )
    assert set(records) == SYNC_ROLLOUT_EXISTING_METADATA_PATHS
    assert all(
        item.in_base
        and item.in_head
        and item.inventory is InventoryStatus.HUMAN_OWNED
        and item.candidate_id.role == "human-maintained"
        and item.ownership_provenance
        == f"protected-ownership:pdd-maintainers:{path}"
        for path, item in records.items()
    )

    profiles = load_verification_profiles(ROOT, manifest)

    assert not profiles.invalid_reasons
    assert profiles.coverage == 1.0


def test_sync_rollout_repair_metadata_bridge_stays_ordinary() -> None:
    """The exact bridge cannot turn its base-existing paths into absences."""
    skip_if_authenticated_candidate_lacks_refs(
        ROOT,
        "exact sync-rollout protected history",
        SYNC_ROLLOUT_PROTECTED_BASE,
    )
    base_rules = manifest_module._ownership_rules(  # pylint: disable=protected-access
        ROOT, SYNC_ROLLOUT_PROTECTED_BASE
    )
    head_rules = manifest_module._ownership_rules(  # pylint: disable=protected-access
        ROOT, "HEAD"
    )
    effective = manifest_module._sync_rollout_repair_ownership_rules(  # pylint: disable=protected-access
        ROOT,
        REPOSITORY_ID,
        SYNC_ROLLOUT_PROTECTED_BASE,
        "HEAD",
        base_rules,
        head_rules,
    )
    expected = (
        manifest_module._SYNC_ROLLOUT_REPAIR_HUMAN_OWNERSHIP  # pylint: disable=protected-access
    )
    assert set(expected) <= set(effective)
    assert all(not rule.preauthorize_absent for rule in expected)

    mutated_head_rules = tuple(
        replace(rule, preauthorize_absent=True)
        if rule.pattern == expected[0].pattern
        else rule
        for rule in head_rules
    )
    assert manifest_module._sync_rollout_repair_ownership_rules(  # pylint: disable=protected-access
        ROOT,
        REPOSITORY_ID,
        SYNC_ROLLOUT_PROTECTED_BASE,
        "HEAD",
        base_rules,
        mutated_head_rules,
    ) == base_rules


def test_release_video_opt_out_uses_only_actual_base_owned_paths() -> None:
    """The v0.0.309 guard must not introduce a new tracked policy artifact."""
    skip_if_authenticated_candidate_lacks_refs(
        ROOT,
        "release-video opt-out protected history",
        RELEASE_VIDEO_OPT_OUT_PROTECTED_BASE,
    )
    manifest = build_unit_manifest(
        ROOT,
        base_ref=RELEASE_VIDEO_OPT_OUT_PROTECTED_BASE,
        head_ref="HEAD",
    )
    records = {
        item.candidate_id.artifact_relpath.as_posix(): item
        for item in manifest.candidates
        if item.candidate_id.artifact_relpath.as_posix()
        in RELEASE_VIDEO_OPT_OUT_EXISTING_PATHS
    }

    assert not _invalid_reasons_for_base_paths(
        manifest, RELEASE_VIDEO_OPT_OUT_PROTECTED_BASE
    )
    assert not _unaccounted_base_paths(manifest, RELEASE_VIDEO_OPT_OUT_PROTECTED_BASE)
    assert set(records) == RELEASE_VIDEO_OPT_OUT_EXISTING_PATHS
    assert all(item.in_base and item.in_head for item in records.values())
    makefile = records["Makefile"]
    assert (
        makefile.inventory is InventoryStatus.MANAGED
        and makefile.candidate_id.role == "code"
        and makefile.ownership_provenance == "architecture"
    )
    assert all(
        item.inventory is InventoryStatus.HUMAN_OWNED
        and item.candidate_id.role == "human-maintained"
        and item.ownership_provenance
        == f"protected-ownership:pdd-maintainers:{path}"
        for path, item in records.items()
        if path != "Makefile"
    )


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


def test_current_profile_reconciliation_matches_current_prompt_and_profile_rows() -> None:
    """An adopted exact transition must not leave profile requirements stale."""
    policy = json.loads(ROTATION_FILE.read_text(encoding="utf-8"))
    profile_payload = json.loads(PROFILE_FILE.read_text(encoding="utf-8"))
    profile_digest = hashlib.sha256(PROFILE_FILE.read_bytes()).hexdigest()
    current_rows = [
        row
        for row in policy["requirement_rotations"]
        if row["head_policy_sha256"] == profile_digest
    ]
    current_rows.extend(
        _requirement_authorization_row(authorization)
        for authorization in verification._TERRA_SOL_COMPOSED_REQUIREMENT_TRANSITIONS  # pylint: disable=protected-access
        if authorization.bindings.head_policy_sha256 == profile_digest
    )
    current_rows.extend(
        _requirement_authorization_row(authorization)
        for authorization in verification._GENERATE_RELIABILITY_COMPOSED_REQUIREMENT_TRANSITIONS  # pylint: disable=protected-access
        if authorization.bindings.head_policy_sha256 == profile_digest
    )
    current_rows.extend(
        _requirement_authorization_row(authorization)
        for authorization in verification._OPUS_FABLE_COMPOSED_REQUIREMENT_TRANSITIONS  # pylint: disable=protected-access
        if authorization.bindings.head_policy_sha256 == profile_digest
    )
    current_rows.extend(
        _requirement_authorization_row(authorization)
        for authorization in verification._TEMPERATURE_REGRESSION_COMPOSED_REQUIREMENT_TRANSITIONS  # pylint: disable=protected-access
        if authorization.bindings.head_policy_sha256 == profile_digest
    )
    current_rows.extend(
        _requirement_authorization_row(authorization)
        for authorization in verification._ZSH_GLOBAL_OPTION_COMPOSED_REQUIREMENT_TRANSITIONS  # pylint: disable=protected-access
        if authorization.bindings.head_policy_sha256 == profile_digest
    )
    current_rows.extend(
        _requirement_authorization_row(authorization)
        for authorization in verification._PR2376_DEPENDENCY_FIX_REQUIREMENT_TRANSITIONS  # pylint: disable=protected-access
        if authorization.bindings.head_policy_sha256 == profile_digest
    )
    if profile_digest == verification._SYNC_ROLLOUT_REPAIR_PROFILE_BYTES[1]:  # pylint: disable=protected-access
        current_rows.extend(
            {
                "prompt_path": prompt_path.as_posix(),
                "language_id": language_id,
                "to_requirement_id": f"CONTRACT-SHA256:{prompt_digest}",
                "head_prompt_sha256": prompt_digest,
            }
            for prompt_path, language_id, prompt_digest in (
                verification._SYNC_ROLLOUT_REPAIR_PROMPT_BYTES  # pylint: disable=protected-access
            )
        )
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


def test_global_sync_m0_paths_are_exactly_preauthorized() -> None:
    """Only the reviewed M0 evidence paths receive absent-path authority."""
    ownership = json.loads(OWNERSHIP_PATH.read_text(encoding="utf-8"))
    rules = {row["pattern"]: row for row in ownership["rules"]}
    assert len(GLOBAL_SYNC_M0_PREAUTHORIZED_PATHS) == 7
    assert {
        path: rules.get(path) for path in GLOBAL_SYNC_M0_PREAUTHORIZED_PATHS
    } == {
        path: {"pattern": path, **PREAUTHORIZED_CHILD_OWNERSHIP}
        for path in GLOBAL_SYNC_M0_PREAUTHORIZED_PATHS
    }
    preauthorized = {
        row["pattern"]
        for row in ownership["rules"]
        if row.get("preauthorize_absent", False)
    }
    assert not preauthorized & GLOBAL_SYNC_M0_UNAUTHORIZED_SIBLING_PATHS
    assert all(
        not path.endswith("/") and not any(token in path for token in ("*", "?", "["))
        for path in GLOBAL_SYNC_M0_PREAUTHORIZED_PATHS
    )


def test_global_sync_m0_bootstrap_paths_are_exactly_preauthorized() -> None:
    """Only the reviewed protected M0 bootstrap paths receive authority."""
    ownership = json.loads(OWNERSHIP_PATH.read_text(encoding="utf-8"))
    rules = {row["pattern"]: row for row in ownership["rules"]}
    assert len(GLOBAL_SYNC_M0_BOOTSTRAP_PREAUTHORIZED_PATHS) == 3
    assert {
        path: rules.get(path) for path in GLOBAL_SYNC_M0_BOOTSTRAP_PREAUTHORIZED_PATHS
    } == {
        path: {"pattern": path, **PREAUTHORIZED_CHILD_OWNERSHIP}
        for path in GLOBAL_SYNC_M0_BOOTSTRAP_PREAUTHORIZED_PATHS
    }
    bootstrap_authority = {
        row["pattern"]
        for row in ownership["rules"]
        if row.get("preauthorize_absent", False)
        and (
            row["pattern"].startswith(".github/workflows/global-sync-m0-")
            or row["pattern"].startswith(".pdd/global-sync/m0-bootstrap-")
            or row["pattern"].startswith("scripts/verify_global_sync_m0_bootstrap")
        )
    }
    assert bootstrap_authority == GLOBAL_SYNC_M0_BOOTSTRAP_PREAUTHORIZED_PATHS
    assert not bootstrap_authority & GLOBAL_SYNC_M0_BOOTSTRAP_UNAUTHORIZED_SIBLING_PATHS
    assert all(
        not path.endswith("/") and not any(token in path for token in ("*", "?", "["))
        for path in GLOBAL_SYNC_M0_BOOTSTRAP_PREAUTHORIZED_PATHS
    )


def test_global_sync_m0_bootstrap_candidate_cannot_self_authorize(
    tmp_path: Path,
) -> None:
    """Candidate-added ownership rows cannot authorize absent bootstrap paths."""
    root = tmp_path / "global-sync-m0-bootstrap-self-authorization"
    base = _synthetic_current_tree_repo(root)
    ownership_path = root / ".pdd" / "sync-ownership.json"
    ownership = json.loads(ownership_path.read_text(encoding="utf-8"))
    base_rules = [
        row
        for row in ownership["rules"]
        if row["pattern"] not in GLOBAL_SYNC_M0_BOOTSTRAP_PREAUTHORIZED_PATHS
    ]
    if ownership["rules"] != base_rules:
        ownership["rules"] = base_rules
        ownership_path.write_text(
            json.dumps(ownership, indent=2, sort_keys=True) + "\n",
            encoding="utf-8",
        )
        base = _commit(root, "remove protected M0 bootstrap authority")
    assert not {
        row["pattern"]
        for row in json.loads(ownership_path.read_text(encoding="utf-8"))["rules"]
        if row.get("preauthorize_absent", False)
    } & GLOBAL_SYNC_M0_BOOTSTRAP_PREAUTHORIZED_PATHS

    for path in sorted(GLOBAL_SYNC_M0_BOOTSTRAP_PREAUTHORIZED_PATHS):
        candidate = root / path
        candidate.parent.mkdir(parents=True, exist_ok=True)
        candidate.write_text("candidate bootstrap artifact\n", encoding="utf-8")
        _git(root, "add", "-f", path)
    ownership = json.loads(ownership_path.read_text(encoding="utf-8"))
    ownership["rules"].extend(
        {"pattern": path, **PREAUTHORIZED_CHILD_OWNERSHIP}
        for path in sorted(GLOBAL_SYNC_M0_BOOTSTRAP_PREAUTHORIZED_PATHS)
    )
    ownership_path.write_text(
        json.dumps(ownership, indent=2, sort_keys=True) + "\n", encoding="utf-8"
    )
    self_authorized_head = _commit(root, "candidate self-authorizes M0 bootstrap")

    manifest = build_unit_manifest(
        root, base_ref=base, head_ref=self_authorized_head
    )
    assert {
        PurePosixPath(path) for path in GLOBAL_SYNC_M0_BOOTSTRAP_PREAUTHORIZED_PATHS
    } <= set(manifest.unaccounted_tracked_paths)
    assert {
        f"{path}: tracked path has no ownership rule"
        for path in GLOBAL_SYNC_M0_BOOTSTRAP_PREAUTHORIZED_PATHS
    } <= set(manifest.invalid_reasons)


def test_global_sync_m0_bootstrap_candidate_composes_from_protected_base(
    tmp_path: Path,
) -> None:
    """The reviewed M0 bootstrap candidate is valid only atop protected preauth."""
    root = tmp_path / "global-sync-m0-bootstrap-protected-composition"
    base = _synthetic_current_tree_repo(root)
    candidate_contents = {
        ".github/workflows/global-sync-m0-bootstrap.yml": b"name: M0 bootstrap\n",
        ".pdd/global-sync/m0-bootstrap-policy.json": b"{}\n",
        "scripts/verify_global_sync_m0_bootstrap.py": b'"""M0 bootstrap."""\n',
        "scripts/verify_global_sync_m0_samples.py": b'"""M0 samples."""\n',
    }
    assert set(candidate_contents) == GLOBAL_SYNC_M0_BOOTSTRAP_CANDIDATE_PATHS
    for path, content in candidate_contents.items():
        candidate = root / path
        candidate.parent.mkdir(parents=True, exist_ok=True)
        candidate.write_bytes(content)
        _git(root, "add", "-f", path)
    candidate_head = _commit(root, "compose protected M0 bootstrap candidate")

    manifest = build_unit_manifest(root, base_ref=base, head_ref=candidate_head)
    records = {
        item.candidate_id.artifact_relpath.as_posix(): item
        for item in manifest.candidates
        if item.candidate_id.artifact_relpath.as_posix()
        in GLOBAL_SYNC_M0_BOOTSTRAP_CANDIDATE_PATHS
    }
    assert set(records) == GLOBAL_SYNC_M0_BOOTSTRAP_CANDIDATE_PATHS
    assert not manifest.unaccounted_tracked_paths
    assert not manifest.invalid_reasons
    assert all(
        item.inventory.value == "HUMAN_OWNED"
        and item.candidate_id.role == "human-maintained"
        and item.ownership_provenance == f"protected-ownership:pdd-maintainers:{path}"
        for path, item in records.items()
    )


def _workflow_value_references_secret(value: object, secret_names: tuple[str, ...]) -> bool:
    """Return whether a parsed workflow value contains an App-secret reference."""
    if isinstance(value, dict):
        return any(
            _workflow_value_references_secret(child, secret_names)
            for child in value.values()
        )
    if isinstance(value, list):
        return any(_workflow_value_references_secret(child, secret_names) for child in value)
    return isinstance(value, str) and any(
        secret_name.casefold() in value.casefold() for secret_name in secret_names
    )


def _assert_auto_heal_app_secret_consumers_are_restricted(
    jobs: dict[str, dict[str, object]],
) -> None:
    """Require the only App-secret consumer to be the restricted heal job."""
    app_secret_names = ("PDD_CLOUD_APP_ID", "PDD_CLOUD_APP_PRIVATE_KEY")
    consumer_jobs = {
        job_name
        for job_name, job in jobs.items()
        if _workflow_value_references_secret(job, app_secret_names)
    }

    assert consumer_jobs
    assert consumer_jobs == {"heal"}
    assert all(
        jobs[job_name].get("environment") == "pdd-cloud-read"
        for job_name in consumer_jobs
    )


def test_auto_heal_app_secret_consumers_use_restricted_environment() -> None:
    """Every App-secret consumer is bound to the main-restricted environment."""
    workflow = yaml.safe_load(AUTO_HEAL_WORKFLOW_PATH.read_text(encoding="utf-8"))

    _assert_auto_heal_app_secret_consumers_are_restricted(workflow["jobs"])


@pytest.mark.parametrize(
    "secret_reference",
    (
        "${{ secrets.pdd_cloud_app_id }}",
        "${{ secrets['PDD_CLOUD_APP_PRIVATE_KEY'] }}",
    ),
)
def test_auto_heal_rejects_second_job_with_alternate_app_secret_syntax(
    secret_reference: str,
) -> None:
    """Case-insensitive dot and bracket secret references cannot bypass the job gate."""
    jobs = {
        "heal": {
            "environment": "pdd-cloud-read",
            "steps": [{"with": {"app-id": "${{ secrets.PDD_CLOUD_APP_ID }}"}}],
        },
        "unprotected-app-consumer": {
            "steps": [{"env": {"APP_CREDENTIAL": secret_reference}}],
        },
    }

    with pytest.raises(AssertionError):
        _assert_auto_heal_app_secret_consumers_are_restricted(jobs)


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
        | GLOBAL_SYNC_M0_BOOTSTRAP_GLOBAL_SYNC_PREAUTHORIZED_PATHS
    )
    assert (
        STANDALONE_CHECKER_GLOBAL_SYNC_PREAUTHORIZED_PATHS
        <= STANDALONE_CHECKER_PREAUTHORIZED_PATHS
    )
    assert (
        GLOBAL_SYNC_M0_BOOTSTRAP_GLOBAL_SYNC_PREAUTHORIZED_PATHS
        <= GLOBAL_SYNC_M0_BOOTSTRAP_PREAUTHORIZED_PATHS
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


def test_global_sync_m0_paths_compose_without_sibling_authority(
    tmp_path: Path,
) -> None:
    """Protected M0 authority admits only the reviewed evidence paths."""
    root = tmp_path / "global-sync-m0-preauthorization"
    base = _synthetic_current_tree_repo(root)
    for path in GLOBAL_SYNC_M0_PREAUTHORIZED_PATHS:
        candidate = root / path
        candidate.parent.mkdir(parents=True, exist_ok=True)
        candidate.write_text("reviewed M0 evidence\n", encoding="utf-8")
        _git(root, "add", "-f", path)
    exact_head = _commit(root, "add reviewed M0 evidence")

    exact_manifest = build_unit_manifest(root, base_ref=base, head_ref=exact_head)
    records = {
        item.candidate_id.artifact_relpath.as_posix(): item
        for item in exact_manifest.candidates
        if item.candidate_id.artifact_relpath.as_posix()
        in GLOBAL_SYNC_M0_PREAUTHORIZED_PATHS
    }
    assert set(records) == GLOBAL_SYNC_M0_PREAUTHORIZED_PATHS
    assert not exact_manifest.unaccounted_tracked_paths
    assert not exact_manifest.invalid_reasons
    assert all(
        item.inventory.value == "HUMAN_OWNED"
        and item.candidate_id.role == "human-maintained"
        and item.ownership_provenance == f"protected-ownership:pdd-maintainers:{path}"
        for path, item in records.items()
    )

    for path in GLOBAL_SYNC_M0_UNAUTHORIZED_SIBLING_PATHS:
        candidate = root / path
        candidate.parent.mkdir(parents=True, exist_ok=True)
        candidate.write_text("unreviewed M0 evidence\n", encoding="utf-8")
        _git(root, "add", "-f", path)
    sibling_head = _commit(root, "attempt unreviewed M0 evidence")
    sibling_manifest = build_unit_manifest(
        root, base_ref=exact_head, head_ref=sibling_head
    )
    assert {
        Path(path) for path in GLOBAL_SYNC_M0_UNAUTHORIZED_SIBLING_PATHS
    } <= set(sibling_manifest.unaccounted_tracked_paths)
    assert {
        f"{path}: tracked path has no ownership rule"
        for path in GLOBAL_SYNC_M0_UNAUTHORIZED_SIBLING_PATHS
    } <= set(sibling_manifest.invalid_reasons)


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

    assert result == tuple(sorted(_BOOTSTRAP_HUMAN_OWNERSHIP[1:]))


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

    assert result == tuple(sorted(_BOOTSTRAP_HUMAN_OWNERSHIP))
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


def test_sync_rollout_repair_ownership_pin_tracks_the_actual_policy_file() -> None:
    """The bridge's head digest must equal the checked-in ownership bytes.

    ``_sync_rollout_repair_rules`` compares sha256 of ``.pdd/sync-ownership.json``
    against ``_SYNC_ROLLOUT_REPAIR_OWNERSHIP_BYTES`` and, on any mismatch, falls
    through to ``base_rules``. The eight repaired metadata paths then silently
    lose their ownership and resurface as unowned tracked paths.

    That makes every edit to the ownership policy — including a one-line
    preauthorization — a change that must re-pin this digest. Without this
    guard the failure surfaces as several unrelated-looking assertions about
    ``.pdd/meta/*`` paths rather than as the one-line cause.
    """
    actual = hashlib.sha256(
        (ROOT / ".pdd" / "sync-ownership.json").read_bytes()
    ).hexdigest()

    assert actual == manifest_module._SYNC_ROLLOUT_REPAIR_OWNERSHIP_BYTES[1], (  # pylint: disable=protected-access
        "`.pdd/sync-ownership.json` changed without re-pinning "
        "_SYNC_ROLLOUT_REPAIR_OWNERSHIP_BYTES[1] in pdd/sync_core/manifest.py. "
        f"Set it to {actual!r}."
    )


class _FakeManifest:
    """Minimal stand-in exposing only the two fields the filters read."""

    def __init__(self, invalid_reasons, unaccounted_tracked_paths):
        self.invalid_reasons = tuple(invalid_reasons)
        self.unaccounted_tracked_paths = tuple(unaccounted_tracked_paths)


def test_post_base_addition_filter_ignores_only_paths_added_after_the_base() -> None:
    """Pinned-base regressions must not become a blanket ban on new files.

    ``manifest._ownership_rules`` reads ownership only from the protected base,
    so a path added after a pinned base can never have a rule there. Filtering
    those out keeps the pinned-base guards meaningful without making the
    repository unable to accept new files.
    """
    # Cloud Batch shards run from an extracted source tarball with no git
    # history, so `git diff <pinned base>` exits 128 there. Skip exactly as the
    # sibling pinned-base regressions do rather than failing the release gate.
    skip_if_authenticated_candidate_lacks_refs(
        ROOT,
        "exact sync-rollout protected history",
        SYNC_ROLLOUT_PROTECTED_BASE,
    )
    base = SYNC_ROLLOUT_PROTECTED_BASE
    added = _paths_added_since(base)
    assert added, "expected at least one path added since the pinned base"

    new_path = sorted(added)[0]
    stale_path = "pdd/llm_invoke.py"
    assert stale_path not in added, "control path must predate the pinned base"

    manifest = _FakeManifest(
        invalid_reasons=(
            f"{new_path}: tracked path has no ownership rule",
            f"{stale_path}: tracked path has no ownership rule",
        ),
        unaccounted_tracked_paths=(PurePosixPath(new_path), PurePosixPath(stale_path)),
    )

    # The post-base addition is excluded; the pre-existing path still fails.
    assert _invalid_reasons_for_base_paths(manifest, base) == (
        f"{stale_path}: tracked path has no ownership rule",
    )
    assert _unaccounted_base_paths(manifest, base) == (PurePosixPath(stale_path),)


def test_post_base_addition_filter_is_inert_when_nothing_was_added() -> None:
    """Filtering against HEAD itself must change nothing."""
    manifest = _FakeManifest(
        invalid_reasons=("pdd/llm_invoke.py: tracked path has no ownership rule",),
        unaccounted_tracked_paths=(PurePosixPath("pdd/llm_invoke.py"),),
    )

    assert _paths_added_since("HEAD") == frozenset()
    assert _invalid_reasons_for_base_paths(manifest, "HEAD") == manifest.invalid_reasons
    assert _unaccounted_base_paths(manifest, "HEAD") == manifest.unaccounted_tracked_paths
