"""Example showing how to use run_agentic_checkup for GitHub issue-based project health checks."""

import sys
from pathlib import Path
from unittest.mock import patch, MagicMock

project_root = Path(__file__).resolve().parent.parent
sys.path.append(str(project_root))

from pdd.agentic_checkup import run_agentic_checkup


def main():
    """Demonstrate the agentic checkup workflow with mocked dependencies."""
    issue_url = "https://github.com/example/myproject/issues/42"
    print(f"Running agentic checkup for: {issue_url}")
    print("-" * 60)

    with patch("pdd.agentic_checkup.run_agentic_checkup_orchestrator") as mock_orch, \
         patch("pdd.agentic_checkup._run_gh_command") as mock_gh, \
         patch("pdd.agentic_checkup._check_gh_cli", return_value=True), \
         patch("pdd.agentic_checkup._find_project_root", return_value=Path("/tmp/myproject")), \
         patch("pdd.agentic_checkup._load_architecture_json") as mock_arch:

        import json

        # Mock GitHub API — issue fetch
        mock_gh.return_value = (True, json.dumps({
            "title": "Check the entire CRM app",
            "body": "Run a full health check on all CRM modules",
            "comments_url": "",
        }))

        # Mock architecture.json
        mock_arch.return_value = (
            [
                {"filename": "crm_models_Python.prompt", "dependencies": []},
                {"filename": "crm_actions_Python.prompt", "dependencies": ["crm_models_Python.prompt"]},
            ],
            Path("/tmp/myproject/architecture.json"),
        )

        # Mock orchestrator — returns (success, message, cost, model)
        mock_orch.return_value = (
            True,
            "Checkup complete",
            5.25,
            "anthropic",
        )

        # --- EXECUTE THE MODULE ---
        success, message, cost, model = run_agentic_checkup(
            issue_url=issue_url,
            verbose=True,
            quiet=False,
            no_fix=False,
            timeout_adder=0.0,
            use_github_state=True,
        )

    print("\n--- Result Summary ---")
    print(f"Success    : {success}")
    print(f"Model Used : {model}")
    print(f"Total Cost : ${cost:.2f}")
    print(f"Message    : {message}")


if __name__ == "__main__":
    main()
