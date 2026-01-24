"""Example showing how to use run_agentic_test for GitHub issue-based test generation."""

import sys
from pathlib import Path
from unittest.mock import patch, MagicMock

# Add the project root to sys.path
project_root = Path(__file__).resolve().parent.parent
sys.path.append(str(project_root))

from pdd.agentic_test import run_agentic_test


def main():
    """Demonstrate the agentic test workflow with a mocked GitHub issue."""

    # Example GitHub issue URL (test request)
    issue_url = "https://github.com/example/repo/issues/456"

    print(f"Running agentic test workflow for: {issue_url}")
    print("-" * 60)

    # Mock the agentic task execution to avoid real API calls
    # We also mock _check_gh_cli, _fetch_issue_data, and _ensure_repo_context to avoid environment dependencies
    with patch("pdd.agentic_test.run_agentic_test_orchestrator") as mock_orchestrator, \
         patch("pdd.agentic_test._check_gh_cli", return_value=True), \
         patch("pdd.agentic_test._fetch_issue_data") as mock_fetch, \
         patch("pdd.agentic_test._ensure_repo_context") as mock_context:
        
        # Mock issue data
        mock_fetch.return_value = ({
            "title": "Test Issue",
            "user": {"login": "tester"},
            "body": "Fix the login bug",
            "full_content_with_comments": "State: open\nLabels: bug\n\nFix the login bug",
            "labels": [{"name": "bug"}],
            "state": "open"
        }, None)
        
        # Mock repo context
        mock_context.return_value = (True, "/tmp/mock/repo")

        # Simulate successful 9-step workflow
        mock_orchestrator.return_value = (
            True,  # success
            "Tests generated and PR created.",  # message
            2.50,  # total_cost across all 9 steps
            "anthropic",  # model/provider used
            ["tests/e2e/test_login.spec.ts", "tests/e2e/test_dashboard.spec.ts"]  # changed_files
        )

        # --- EXECUTE THE MODULE ---
        success, message, cost, model, changed_files = run_agentic_test(
            issue_url=issue_url,
            verbose=True,
            quiet=False,
            timeout_adder=0.0,
            use_github_state=True
        )

    # Output the results
    print("\n--- Result Summary ---")
    print(f"Success       : {success}")
    print(f"Model Used    : {model}")
    print(f"Cost          : ${cost:.2f}")
    print(f"Changed Files : {changed_files}")
    print("-" * 30)
    print(f"Message       : {message}")
    print("\nTests generated in worktree. PR created and linked to issue.")


if __name__ == "__main__":
    main()