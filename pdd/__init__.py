"""PDD - Prompt Driven Development"""

from importlib.metadata import PackageNotFoundError, version as _metadata_version
import os


def _load_package_version() -> str:
    """Return the installed pdd-cli distribution version."""
    try:
        return _metadata_version("pdd-cli")
    except PackageNotFoundError:
        return "0.0.0+unknown"


__version__ = _load_package_version()

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


# Initialize cloud defaults on package import
_setup_cloud_defaults()
from .agentic_common import get_agent_provider_preference, get_job_deadline, Pricing, get_available_agents, run_agentic_task, github_save_state, github_load_state, github_clear_state, validate_cached_state, load_workflow_state, save_workflow_state, clear_workflow_state, post_step_comment, substitute_template_variables, post_pr_comment, post_final_comment, _extract_step_report, _sanitize_comment_body
from .agentic_test_orchestrator import run_agentic_test_orchestrator
from .architecture_sync_helper import filepath_to_prompt_filename
from .agentic_e2e_fix_orchestrator import run_agentic_e2e_fix_orchestrator
from .ci_validation import detect_ci_system, post_ci_failure_comment, run_ci_validation_loop
from .agentic_e2e_fix import run_agentic_e2e_fix
from .agentic_bug_orchestrator import run_agentic_bug_orchestrator
from .agentic_update import run_agentic_update
from .update_main import resolve_prompt_code_pair, find_and_resolve_all_pairs, get_git_changed_files, derive_basename_and_language, is_code_changed, update_file_pair, update_main
from .ci_drift_heal import DriftInfo, HealResult, detect_drift, heal_module, commit_and_push, main
from .agentic_change_orchestrator import run_agentic_change_orchestrator
from .agentic_common_worktree import get_git_root, worktree_exists, branch_exists, remove_worktree, delete_branch, resolve_main_ref, setup_worktree, get_modified_and_untracked, check_target_file_unchanged, revert_out_of_scope_changes_with_dirs, extract_block_marker
from .get_lint_commands import LintCommand, get_lint_commands
from .split_main import split_main
from .split_validation import ValidationFailure, ValidationResult, validate_extraction
from .agentic_split_orchestrator import run_agentic_split_orchestrator, Diagnosis, ModuleInvestigation, TestOwnership, PromptMetadata, Child, ParentChanges, SplitPlan, SplitOption, OptionsConsidered, QualitativeAssessment
from .agentic_split import run_agentic_split
from .ci_detect_changed_modules import main
from .agentic_architecture_orchestrator import load_workflow_state, save_workflow_state, clear_workflow_state, run_agentic_architecture_orchestrator
