"""
Example usage of the agentic_e2e_fix module.

This script demonstrates how to invoke the `run_agentic_e2e_fix` function,
which is the entry point for the agentic e2e fix workflow. It parses a GitHub
issue URL, fetches the issue content, and orchestrates the 9-step fix process.
"""

from pdd.agentic_e2e_fix import run_agentic_e2e_fix


def main():
    """Main function demonstrating agentic e2e fix usage."""
    # Example GitHub issue URL (typically created by pdd bug)
    issue_url = "https://github.com/myorg/myrepo/issues/42"

    # Run the agentic e2e fix workflow
    success, message, total_cost, model_used, changed_files = run_agentic_e2e_fix(
        issue_url=issue_url,
        timeout_adder=30.0,      # Add 30 seconds to each step's timeout
        max_cycles=5,            # Maximum outer loop cycles
        resume=True,             # Resume from saved state if available
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
        print(f"E2E fix failed: {message}")
        print(f"Cost incurred: ${total_cost:.4f}")


if __name__ == "__main__":
    main()
