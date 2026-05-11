"""Example showing how to use run_agentic_checkup for GitHub issue-based project health checks."""

import sys
import os
import json
from pathlib import Path
from unittest.mock import patch, MagicMock

# Ensure we load the local 'pdd' package, not the system-installed one.
sys.path.insert(0, os.path.join(os.path.dirname(__file__), ".."))

from pdd.agentic_checkup import run_agentic_checkup


def main():
    """Demonstrate the agentic checkup workflow with mocked dependencies."""
    issue_url = "https://github.com/example/myproject/issues/42"
    print(f"Running agentic checkup for: {issue_url}")
    print()

    # We mock out side effects: GH CLI checks, API calls, and the orchestrator.
    with patch("pdd.agentic_checkup._check_gh_cli", return_value=True), \
         patch("pdd.agentic_checkup._gh_api") as mock_gh_api, \
         patch("pdd.agentic_checkup.find_project_root", return_value=Path("/tmp/myproject")), \
         patch("pdd.agentic_checkup._load_architecture_json") as mock_arch, \
         patch("pdd.agentic_checkup._load_pddrc_content") as mock_pddrc, \
         patch("pdd.agentic_checkup.run_agentic_checkup_orchestrator") as mock_orch:

        # _gh_api is called for:
        # 1. Fetching the issue JSON
        # 2. Fetching the comments (which uses --paginate)
        def gh_api_side_effect(args):
            if "repos/example/myproject/issues/42/comments" in args or "issues/42/comments" in args[0] or "--paginate" in args:
                return True, "[]", ""
            if "repos/example/myproject/issues/42" in args[0]:
                return True, json.dumps({
                    "title": "Check the entire CRM app",
                    "body": "Run a full health check on all CRM modules",
                    "comments_url": "https://api.github.com/repos/example/myproject/issues/42/comments",
                }), ""
            return True, "[]", ""

        mock_gh_api.side_effect = gh_api_side_effect

        # Mock architecture.json
        mock_arch.return_value = (
            [
                {"filename": "crm_models_Python.prompt", "dependencies": []},
                {"filename": "crm_actions_Python.prompt", "dependencies": ["crm_models_Python.prompt"]},
            ],
            Path("/tmp/myproject/architecture.json"),
        )

        mock_pddrc.return_value = "timeout_multiplier: 1.5"

        # Mock orchestrator — returns (success, message, cost, model)
        mock_orch.return_value = (
            True,
            "Checkup complete. No issues found.",
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
            use_github_state=False,
        )

    print("--- Result Summary ---")
    print(f"Success    : {success}")
    print(f"Model Used : {model}")
    print(f"Total Cost : ${cost:.2f}")
    print(f"Message    : {message}")
    print()


if __name__ == "__main__":
    main()
