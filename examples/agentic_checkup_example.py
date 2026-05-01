import sys
import json
from pathlib import Path
from unittest.mock import patch

# Add the project root to sys.path
project_root: Path = Path(__file__).resolve().parent.parent
sys.path.append(str(project_root))

from pdd.agentic_checkup import run_agentic_checkup


def main() -> None:
    """Demonstrate the agentic checkup workflow with a mocked GitHub issue."""

    # Example GitHub issue URL
    issue_url: str = "https://github.com/example/repo/issues/42"

    print(f"Running agentic checkup for: {issue_url}")
    print("-" * 60)

    issue_payload = json.dumps(
        {
            "title": "Example issue",
            "body": "Check whether the generated PR fully resolves the workflow.",
            "comments_url": "https://api.github.com/repos/example/repo/issues/42/comments",
        }
    )

    # Mock GitHub and orchestrator calls to keep the example local and repeatable.
    with patch("pdd.agentic_checkup._check_gh_cli", return_value=True), \
         patch("pdd.agentic_checkup._run_gh_command", return_value=(True, issue_payload)), \
         patch("pdd.agentic_checkup._fetch_comments", return_value="No comments."), \
         patch("pdd.agentic_checkup.run_agentic_checkup_orchestrator") as mock_orchestrator:
        # Simulate successful checkup
        mock_orchestrator.return_value = (
            True,  # success
            "Checkup complete. Issues fixed.",  # message
            2.50,  # total_cost
            "anthropic",  # model_used
        )

        success, message, cost, model = run_agentic_checkup(
            issue_url=issue_url,
            verbose=True,
            quiet=False,
            no_fix=False,
        )

    # Output the results
    print("\n--- Result Summary ---")
    print(f"Success    : {success}")
    print(f"Model Used : {model}")
    print(f"Total Cost : ${cost:.2f}")
    print(f"Message    : {message}")


if __name__ == "__main__":
    main()
