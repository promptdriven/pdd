"""
Example usage of the agentic_e2e_fix module.

This script demonstrates how to invoke the `run_agentic_e2e_fix` function,
which is the entry point for the agentic e2e fix workflow. It parses a GitHub
issue URL, fetches the issue content, and orchestrates the 9-step fix process.

Cross-machine support:
- If run on same machine as `pdd bug`: automatically finds the worktree
- If run on different machine: detects the branch from issue comments and
  warns if you're not on the correct branch (aborts unless --force is used)
"""

from pdd.agentic_e2e_fix import run_agentic_e2e_fix


def main():
    """Main function demonstrating agentic e2e fix usage."""
    # Example GitHub issue URL (typically created by pdd bug)
    #
    # Same machine as pdd bug:
    #   - Automatically finds worktree at .pdd/worktrees/fix-issue-42/
    #   - Uses that directory as cwd for all operations
    #
    # Different machine:
    #   - Parses issue comments to find branch name (e.g., fix/issue-42)
    #   - Compares against current git branch
    #   - If mismatch: aborts with suggestion to checkout correct branch
    #   - Use force=True to override the safety check
    #   - Falls back to current directory if no worktree found
    issue_url = "https://github.com/myorg/myrepo/issues/42"

    # Run the agentic e2e fix workflow
    success, message, total_cost, model_used, changed_files = run_agentic_e2e_fix(
        issue_url=issue_url,
        timeout_adder=30.0,      # Add 30 seconds to each step's timeout
        max_cycles=5,            # Maximum outer loop cycles
        resume=True,             # Resume from saved state if available
        force=False,             # Abort if branch mismatch detected (safety check)
        verbose=True,            # Show detailed output
        quiet=False              # Don't suppress output
    )

    # Handle results
    if success:
        print(f"E2E fix completed successfully!")
        print(f"Total cost: ${total_cost:.4f}")
        print(f"Model used: {model_used}")
        print(f"Files changed: {', '.join(changed_files)}")
    else:
        # Common failure cases:
        # - "Branch mismatch - use --force to override" (wrong branch)
        # - "gh CLI not found" (gh not installed)
        # - "Invalid GitHub URL" (malformed URL)
        # - "Max cycles (5) reached without all tests passing"
        print(f"E2E fix failed: {message}")
        print(f"Cost incurred: ${total_cost:.4f}")


if __name__ == "__main__":
    main()
