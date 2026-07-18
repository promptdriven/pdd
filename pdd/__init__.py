"""PDD - Prompt Driven Development"""

from importlib import import_module as _import_module
from importlib.metadata import PackageNotFoundError, version as _metadata_version
import os
import subprocess
from pathlib import Path


def _derive_git_aligned_version() -> str | None:
    """Return tag-aligned development version for the current git checkout."""
    repo_root = Path(__file__).resolve().parents[1]
    if not (repo_root / ".git").exists():
        return None
    try:
        result = subprocess.run(
            ["git", "tag", "--list", "--merged", "HEAD", "--sort=-v:refname", "v*"],
            cwd=repo_root,
            capture_output=True,
            text=True,
            check=False,
        )
        if result.returncode != 0:
            return None
        tags = [t.lstrip("v") for t in result.stdout.split()]
        latest = next((t for t in tags if t.count(".") == 2), None)
        if latest is None:
            return None

        head_tags = subprocess.check_output(
            ["git", "tag", "--points-at", "HEAD"], cwd=repo_root, text=True
        ).split()
        if f"v{latest}" in head_tags:
            return latest

        parts = [int(x) for x in latest.split(".")]
        parts[-1] += 1
        return ".".join(str(p) for p in parts) + ".dev0"
    except Exception:
        return None


def _load_package_version() -> str:
    """Return a version aligned with current tag strategy."""
    try:
        dist_version = _metadata_version("pdd-cli")
    except PackageNotFoundError:
        dist_version = "0.0.0+unknown"

    git_version = _derive_git_aligned_version()
    if git_version is None:
        return dist_version

    # Prefer git-aligned version when installed metadata is stale for this checkout.
    if dist_version != git_version:
        return git_version
    return dist_version


__version__ = _load_package_version()


def get_version() -> str:
    """Return the installed pdd-cli distribution version."""
    return _load_package_version()


# Strength parameter used for LLM extraction across the codebase
# Used in postprocessing, XML tagging, code generation, and other extraction
# operations. The module should have a large context window and be affordable.
EXTRACTION_STRENGTH = 0.5

DEFAULT_STRENGTH = float(os.getenv("PDD_STRENGTH_DEFAULT", "1.0"))

DEFAULT_TEMPERATURE = 0.0

DEFAULT_TIME = 0.25

# Public OAuth credentials for cloud mode
# These are safe to embed as they are public client identifiers:
# - Firebase API keys are designed to be public (client-side)
# - GitHub OAuth Client IDs are public (the secret stays server-side)
# Users still need to authenticate via GitHub OAuth to use cloud features.
_DEFAULT_FIREBASE_API_KEY = "AIzaSyC0w2jwRR82ZFgQs_YXJoEBqnnTH71X6BE"
_DEFAULT_GITHUB_CLIENT_ID = "Ov23liJ4eSm0y5W1L20u"


def _setup_cloud_defaults() -> None:
    """Set up default cloud credentials if not already set.

    Only sets defaults when:
    1. Not running inside cloud environment (K_SERVICE or FUNCTIONS_EMULATOR)
    2. Environment variables are not already set

    This prevents infinite loops when cloud endpoints call CLI internally,
    while providing a seamless experience for local users.
    """
    # Skip if running in cloud environment to prevent infinite loops
    if os.environ.get("K_SERVICE") or os.environ.get("FUNCTIONS_EMULATOR"):
        return

    # Set Firebase API key if not already set
    if not os.environ.get("NEXT_PUBLIC_FIREBASE_API_KEY"):
        os.environ["NEXT_PUBLIC_FIREBASE_API_KEY"] = _DEFAULT_FIREBASE_API_KEY

    # Set GitHub Client ID if not already set
    if not os.environ.get("GITHUB_CLIENT_ID"):
        os.environ["GITHUB_CLIENT_ID"] = _DEFAULT_GITHUB_CLIENT_ID


# Initialize cloud defaults on package import.
_setup_cloud_defaults()

# Keep the historical package-level API without importing the entire CLI and LLM
# stack for every ``import pdd``.  This matters especially for short-lived CLI
# subprocesses: Python imports the package before executing ``pdd.__main__``.
_LAZY_EXPORTS = {
    **{name: "agentic_common" for name in (
        "get_agent_provider_preference", "get_job_deadline", "Pricing",
        "get_available_agents", "run_agentic_task", "select_harness_for_task",
        "TaskClass", "TASK_CLASS_SINGLE_FILE", "TASK_CLASS_MULTI_FILE",
        "TASK_CLASS_REPO_SCALE", "TASK_CLASS_HIGH_ISOLATION", "github_save_state",
        "github_load_state", "github_clear_state", "validate_cached_state",
        "post_step_comment", "substitute_template_variables", "post_pr_comment",
        "post_final_comment", "_extract_step_report", "_sanitize_comment_body",
    )},
    **{name: "routing_policy" for name in (
        "RoutingConfig", "EscalationStep", "RoutingPolicyRow", "RoutingPolicy",
        "RoutingRecord", "default_policy", "load_policy", "select_config",
        "escalate", "resolve_model_for_tier", "emit_routing_record",
    )},
    "run_agentic_test_orchestrator": "agentic_test_orchestrator",
    "filepath_to_prompt_filename": "architecture_sync_helper",
    "run_agentic_e2e_fix_orchestrator": "agentic_e2e_fix_orchestrator",
    **{name: "ci_validation" for name in (
        "detect_ci_system", "post_ci_failure_comment", "run_ci_validation_loop",
    )},
    "run_agentic_e2e_fix": "agentic_e2e_fix",
    "run_agentic_bug_orchestrator": "agentic_bug_orchestrator",
    "run_agentic_update": "agentic_update",
    **{name: "update_main" for name in (
        "resolve_prompt_code_pair", "find_and_resolve_all_pairs",
        "get_git_changed_files", "derive_basename_and_language", "is_code_changed",
        "update_file_pair", "update_main",
    )},
    **{name: "ci_drift_heal" for name in (
        "DriftInfo", "HealResult", "detect_drift", "heal_module", "commit_and_push",
    )},
    "run_agentic_change_orchestrator": "agentic_change_orchestrator",
    **{name: "agentic_common_worktree" for name in (
        "get_git_root", "worktree_exists", "branch_exists", "remove_worktree",
        "delete_branch", "resolve_main_ref", "setup_worktree",
        "get_modified_and_untracked", "check_target_file_unchanged",
        "revert_out_of_scope_changes_with_dirs", "extract_block_marker",
    )},
    "LintCommand": "get_lint_commands",
    "get_lint_commands": "get_lint_commands",
    "split_main": "split_main",
    **{name: "split_validation" for name in (
        "ValidationFailure", "ValidationResult", "validate_extraction",
    )},
    **{name: "agentic_split_orchestrator" for name in (
        "run_agentic_split_orchestrator", "Diagnosis", "ModuleInvestigation",
        "TestOwnership", "PromptMetadata", "Child", "ParentChanges", "SplitPlan",
        "SplitOption", "OptionsConsidered", "QualitativeAssessment",
    )},
    "run_agentic_split": "agentic_split",
    # These names were overwritten by the later architecture/CI imports in the
    # previous eager-import implementation; retain that exact public behavior.
    "main": "ci_detect_changed_modules",
    "load_workflow_state": "agentic_architecture_orchestrator",
    "save_workflow_state": "agentic_architecture_orchestrator",
    "clear_workflow_state": "agentic_architecture_orchestrator",
    "run_agentic_architecture_orchestrator": "agentic_architecture_orchestrator",
    **{name: "agentic_multishot" for name in (
        "run_multishot_candidates", "MultishotResult", "MultishotCandidateRecord",
    )},
}

# Preserve the names historically exposed by ``from pdd import *``.  Lazy
# attributes are otherwise invisible to star-import because they are not in the
# module dictionary until first access.
__all__ = [
    "PackageNotFoundError", "os", "subprocess", "Path", "get_version",
    "EXTRACTION_STRENGTH", "DEFAULT_STRENGTH", "DEFAULT_TEMPERATURE",
    "DEFAULT_TIME", *sorted(name for name in _LAZY_EXPORTS if not name.startswith("_")),
]


def __getattr__(name: str):
    """Load legacy package-level exports only when callers request them."""
    module_name = _LAZY_EXPORTS.get(name)
    if module_name is None:
        raise AttributeError(f"module {__name__!r} has no attribute {name!r}")
    value = getattr(_import_module(f".{module_name}", __name__), name)
    globals()[name] = value
    return value


def __dir__() -> list[str]:
    """Include lazy public exports in interactive discovery."""
    return sorted(set(globals()) | set(_LAZY_EXPORTS))
