"""Example showing how to use run_agentic_architecture for GitHub issue-based architecture generation."""

import sys
from pathlib import Path
from unittest.mock import patch, MagicMock

# Add the project root to sys.path
project_root = Path(__file__).resolve().parent.parent
sys.path.append(str(project_root))

from pdd.agentic_architecture import run_agentic_architecture


def main():
    """Demonstrate the agentic architecture workflow with a mocked GitHub issue."""

    # Example GitHub issue URL (contains PRD/requirements)
    issue_url = "https://github.com/example/repo/issues/42"

    print(f"Running agentic architecture workflow for: {issue_url}")
    print("-" * 60)

    # Mock the agentic task execution to avoid real API calls
    with patch("pdd.agentic_architecture.run_agentic_architecture_orchestrator") as mock_orchestrator:
        # Simulate successful 8-step workflow
        mock_orchestrator.return_value = (
            True,  # success
            "Architecture generated. Created architecture.json with 6 modules.",  # message
            2.50,  # total_cost across all 8 steps
            "anthropic",  # model/provider used
            ["architecture.json", "architecture_diagram.html"]  # output_files
        )

        # --- EXECUTE THE MODULE ---
        success, message, cost, model, output_files = run_agentic_architecture(
            issue_url=issue_url,
            verbose=True,
            quiet=False
        )

    # Output the results
    print("\n--- Result Summary ---")
    print(f"Success       : {success}")
    print(f"Model Used    : {model}")
    print(f"Cost          : ${cost:.2f}")
    print(f"Output Files  : {output_files}")
    print("-" * 30)
    print(f"Message       : {message}")
    print("\nNext step: Run 'pdd generate' on individual module prompts to generate code.")


if __name__ == "__main__":
    main()
