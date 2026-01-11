"""Example showing how to use run_agentic_change for GitHub issue-based prompt modification."""

import sys
from pathlib import Path
from unittest.mock import patch, MagicMock

# Add the project root to sys.path
project_root = Path(__file__).resolve().parent.parent
sys.path.append(str(project_root))

from pdd.agentic_change import run_agentic_change


def main():
    """Demonstrate the agentic change workflow with a mocked GitHub issue."""

    # Example GitHub issue URL (feature request or change request)
    issue_url = "https://github.com/example/repo/issues/239"

    print(f"Running agentic change workflow for: {issue_url}")
    print("-" * 60)

    # Mock the agentic task execution to avoid real API calls
    with patch("pdd.agentic_change.run_agentic_change_orchestrator") as mock_orchestrator:
        # Simulate successful 12-step workflow
        mock_orchestrator.return_value = (
            True,  # success
            "Change complete. Modified prompts for new feature.",  # message
            1.80,  # total_cost across all 12 steps
            "anthropic",  # model/provider used
            ["prompts/user_service_python.prompt", "context/user_service_example.py"]  # changed_files
        )

        # --- EXECUTE THE MODULE ---
        success, message, cost, model, changed_files = run_agentic_change(
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
    print("\nNext step: Run 'pdd sync' on modified prompts to regenerate code.")


if __name__ == "__main__":
    main()
