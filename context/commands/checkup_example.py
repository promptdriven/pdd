import os
import sys
from pathlib import Path
from click.testing import CliRunner

# Import the checkup command from the pdd package
# Based on file structure: pdd/commands/checkup.py
from pdd.commands.checkup import checkup

def run_checkup_examples():
    runner = CliRunner()

    # --- Scenario 1: Local Architecture Validation ---
    # This mode scans the local directory for architectural consistency.
    # It does not require a GitHub URL or internet access.
    print("--- Running Local Architecture Validation ---")
    
    # Create a dummy architecture.json for the example if it doesn't exist
    # (Normally this would be present in a real project root)
    output_dir = Path("./output")
    output_dir.mkdir(exist_ok=True)
    
    # Execute the local validation mode
    # --validate-arch-includes: Flag to enable local diagnostics
    # --project-root: The directory to scan
    result_local = runner.invoke(checkup, [
        "--validate-arch-includes",
        "--project-root", str(output_dir),
        "--no-fix"
    ])
    
    print(f"Exit Code: {result_local.exit_code}")
    print(f"Output: {result_local.output}")


    # --- Scenario 2: GitHub Issue Health Check (Agentic Mode) ---
    # This mode uses LLMs to check the health of a project based on an issue.
    print("\n--- Running GitHub Issue Checkup (Dry Run) ---")
    
    # Note: This requires GITHUB_TOKEN and LLM API keys in a real environment.
    # We use --no-fix to prevent the agent from actually creating PRs/commits.
    target_issue = "https://github.com/example-org/example-repo/issues/1"
    
    # --no-fix: Report issues only, do not attempt agentic repairs.
    # --timeout-adder: Add 30 seconds to default AI step timeouts.
    # --no-github-state: Do not persist state to the GitHub issue comments.
    result_issue = runner.invoke(checkup, [
        target_issue,
        "--no-fix",
        "--timeout-adder", "30.0",
        "--no-github-state"
    ])
    
    # Note: In a headless environment without API keys, this might fail or return
    # a connection error, but it demonstrates the correct CLI invocation structure.
    print(f"Issue Check Command attempted for: {target_issue}")
    print(f"Result Exit Code: {result_issue.exit_code}")


    # --- Scenario 3: PR Verification Mode ---
    # Used to verify if an existing PR actually solves its associated issue.
    print("\n--- Running PR Verification Mode ---")
    
    pr_url = "https://github.com/example-org/example-repo/pull/123"
    issue_url = "https://github.com/example-org/example-repo/issues/1"
    
    # --pr: The Pull Request to verify.
    # --issue: The context/source of truth for requirements.
    # Note: --pr automatically forces --no-fix as per the module implementation.
    result_pr = runner.invoke(checkup, [
        "--pr", pr_url,
        "--issue", issue_url
    ])
    
    print(f"PR Verification attempted for PR {pr_url} against Issue {issue_url}")
    print(f"Result Exit Code: {result_pr.exit_code}")

if __name__ == "__main__":
    # The module relies on GITHUB_TOKEN for GitHub interactions.
    # If the example is just for local validation, we can proceed.
    if not os.environ.get("GITHUB_TOKEN") and "--validate-arch-includes" not in sys.argv:
        print("Notice: GITHUB_TOKEN not set. GitHub-based modes will fail if actually executed.")
    
    run_checkup_examples()

# =============================================================================
# Summary of Inputs and Outputs for the checkup function:
#
# Inputs (via Click decorators/arguments):
# - target (str): A GitHub issue URL (required unless using --validate-arch-includes or --pr).
# - validate_arch_includes (bool): Flag for local diagnostics mode.
# - project_root (Path): Directory to scan for local diagnostics (default: cwd).
# - strict (bool): If True, validates sample trees (examples/) during local check.
# - no_fix (bool): If True, agent identifies problems but does not apply code fixes.
# - timeout_adder (float): Seconds to add to default LLM/Step timeouts.
# - no_github_state (bool): If True, prevents writing progress state back to GitHub.
# - pr_url (str): The URL of a PR to verify (used in PR mode).
# - issue_url_opt (str): The URL of the source issue (required if --pr is provided).
#
# Returns (Optional[Tuple[str, float, str]]):
# - Tuple[0] (str): Success/Error message summary.
# - Tuple[1] (float): Total cost of the operation in USD (from @track_cost).
# - Tuple[2] (str): The primary AI model used for the checkup.
# =============================================================================