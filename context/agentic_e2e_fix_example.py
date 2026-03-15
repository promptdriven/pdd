"""
Example usage of the agentic_e2e_fix module.

This script demonstrates how to invoke the `run_agentic_e2e_fix` function.
Since the function relies on the GitHub CLI (`gh`) and interacts with real GitHub issues,
this example mocks the internal GitHub fetching functions to simulate a successful
E2E fix workflow without requiring actual API calls or a real issue.

Scenario:
    We simulate fetching data for a GitHub issue reporting an E2E test failure.
    The function will determine the working directory, fetch (mocked) issue content,
    and invoke the orchestrator to perform the fix.
"""

import sys
from pathlib import Path
from unittest.mock import patch, MagicMock

# Ensure the project root is in sys.path so we can import the module
# Adjust this path based on your actual project structure relative to this script
project_root = Path(__file__).resolve().parent.parent
sys.path.append(str(project_root))

try:
    # Import the module to be tested
    # Note: We assume the file is at pdd/agentic_e2e_fix.py
    from pdd.agentic_e2e_fix import run_agentic_e2e_fix
except ImportError:
    print("Error: Could not import 'pdd.agentic_e2e_fix'.")
    print("Ensure your PYTHONPATH is set correctly or the file structure matches.")
    sys.exit(1)


def mock_check_gh_cli() -> bool:
    """Mock gh CLI check to always return True."""
    return True


def mock_parse_github_url(url: str) -> tuple:
    """Mock URL parsing to return fixed owner, repo, number."""
    return "example-owner", "example-repo", 123


def mock_fetch_issue_data(owner: str, repo: str, number: int) -> tuple:
    """Mock fetching issue data."""
    issue_data = {
        "title": "E2E Test Failure in User Login Flow",
        "body": "The login E2E test fails intermittently due to timing issues.",
        "user": {"login": "test-author"},
        "comments_url": "https://api.github.com/repos/example-owner/example-repo/issues/123/comments"
    }
    return issue_data, None


def mock_fetch_issue_comments(comments_url: str) -> str:
    """Mock fetching comments."""
    return "--- Comment by test-author ---\nAdditional details: Happens on Chrome but not Firefox.\n"


def mock_find_working_directory(issue_number: int, issue_comments: str, quiet: bool, force: bool) -> tuple:
    """Mock working directory detection to return current directory with no abort."""
    return Path.cwd(), None, False


def main() -> None:
    """Main function to run the agentic E2E fix simulation."""
    # Define example parameters
    issue_url = "https://github.com/example-owner/example-repo/issues/123"

    print("Starting Agentic E2E Fix Simulation...")
    print("-" * 60)

    # Patch the internal functions
    # We patch where they are used in the agentic_e2e_fix module
    with patch("pdd.agentic_e2e_fix._check_gh_cli", mock_check_gh_cli), \
         patch("pdd.agentic_e2e_fix._parse_github_url", mock_parse_github_url), \
         patch("pdd.agentic_e2e_fix._fetch_issue_data", mock_fetch_issue_data), \
         patch("pdd.agentic_e2e_fix._fetch_issue_comments", mock_fetch_issue_comments), \
         patch("pdd.agentic_e2e_fix._find_working_directory", mock_find_working_directory):

        # Run the E2E fix function
        success, final_msg, total_cost, model, changed_files = run_agentic_e2e_fix(
            issue_url=issue_url,
            timeout_adder=0.0,
            max_cycles=1,  # Limit for demo
            resume=False,
            force=True,
            verbose=True,
            quiet=False,
            use_github_state=False,
            protect_tests=True
        )

    print("-" * 60)
    print("Simulation Complete.")
    print(f"Success: {success}")
    print(f"Final Message: {final_msg}")
    print(f"Total Cost: ${total_cost:.2f}")
    print(f"Model Used: {model}")
    print(f"Changed Files: {changed_files}")


if __name__ == "__main__":
    main()