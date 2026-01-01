"""Example showing how to use run_agentic_bug for GitHub issue-based bug investigation."""

import sys
from pathlib import Path
from unittest.mock import patch, MagicMock

# Add the project root to sys.path
project_root = Path(__file__).resolve().parent.parent
sys.path.append(str(project_root))

from pdd.agentic_bug import run_agentic_bug


def main():
    """Demonstrate the agentic bug workflow with a mocked GitHub issue."""

    # Example GitHub issue URL
    issue_url = "https://github.com/example/repo/issues/42"

    print(f"Running agentic bug investigation for: {issue_url}")
    print("-" * 60)

    # Mock the agentic task execution to avoid real API calls
    with patch("pdd.agentic_bug.run_agentic_bug_orchestrator") as mock_orchestrator:
        # Simulate successful 8-step workflow
        mock_orchestrator.return_value = (
            True,  # success
            "Investigation complete. Created test_calculator_bug.py",  # message
            2.50,  # total_cost across all 8 steps
            "anthropic",  # model/provider used
            ["tests/test_calculator_bug.py"]  # changed_files
        )

        # --- EXECUTE THE MODULE ---
        success, message, cost, model, changed_files = run_agentic_bug(
            issue_url=issue_url,
            verbose=True,
            quiet=False
        )

    # Output the results
    print("\n--- Result Summary ---")
    print(f"Success       : {success}")
    print(f"Model Used    : {model}")
    print(f"Cost          : ${cost:.2f}")
    print(f"Changed Files : {changed_files}")
    print("-" * 30)
    print(f"Message       : {message}")


if __name__ == "__main__":
    main()
