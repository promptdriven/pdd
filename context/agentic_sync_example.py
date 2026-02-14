"""Example showing how to use run_agentic_sync for GitHub issue-based multi-module sync."""

import sys
from pathlib import Path
from unittest.mock import patch, MagicMock

# Add the project root to sys.path
project_root = Path(__file__).resolve().parent.parent
sys.path.append(str(project_root))

from pdd.agentic_sync import run_agentic_sync, _is_github_issue_url, _parse_llm_response


def main():
    """Demonstrate the agentic sync workflow with mocked dependencies."""

    # --- URL Detection ---
    # The sync command detects URLs vs basenames automatically
    assert _is_github_issue_url("https://github.com/owner/repo/issues/42")
    assert not _is_github_issue_url("my_module")

    # --- LLM Response Parsing ---
    llm_response = (
        'MODULES_TO_SYNC: ["auth", "user_service", "api_gateway"]\n\n'
        'DEPS_VALID: true\n'
    )
    modules, deps_valid, corrections = _parse_llm_response(llm_response)
    print(f"Modules to sync: {modules}")
    print(f"Dependencies valid: {deps_valid}")

    # --- Full Workflow (mocked) ---
    issue_url = "https://github.com/example/repo/issues/100"
    print(f"\nRunning agentic sync for: {issue_url}")
    print("-" * 60)

    with patch("pdd.agentic_sync.AsyncSyncRunner") as mock_runner_cls, \
         patch("pdd.agentic_sync.build_dep_graph_from_architecture") as mock_graph, \
         patch("pdd.agentic_sync.load_prompt_template") as mock_template, \
         patch("pdd.agentic_sync.run_agentic_task") as mock_task, \
         patch("pdd.agentic_sync._load_architecture_json") as mock_arch, \
         patch("pdd.agentic_sync._run_gh_command") as mock_gh, \
         patch("pdd.agentic_sync._check_gh_cli", return_value=True):

        # Mock GitHub API
        import json
        mock_gh.return_value = (True, json.dumps({
            "title": "Add caching layer",
            "body": "We need Redis caching for auth and user_service",
            "comments_url": "",
        }))

        # Mock architecture.json
        mock_arch.return_value = (
            [
                {"filename": "auth_python.prompt", "dependencies": []},
                {"filename": "user_service_python.prompt", "dependencies": ["auth_python.prompt"]},
            ],
            Path("/tmp/architecture.json"),
        )

        # Mock LLM response
        mock_template.return_value = "template {issue_content} {architecture_json}"
        mock_task.return_value = (
            True,
            'MODULES_TO_SYNC: ["auth", "user_service"]\nDEPS_VALID: true',
            0.08,
            "anthropic",
        )

        # Mock dependency graph and runner
        mock_graph.return_value = {"auth": [], "user_service": ["auth"]}
        mock_runner = MagicMock()
        mock_runner.run.return_value = (True, "All 2 modules synced successfully", 0.50)
        mock_runner_cls.return_value = mock_runner

        # --- EXECUTE THE MODULE ---
        success, message, cost, model = run_agentic_sync(
            issue_url=issue_url,
            verbose=True,
            quiet=False,
            budget=10.0,
            skip_verify=False,
        )

    # Output the results
    print("\n--- Result Summary ---")
    print(f"Success    : {success}")
    print(f"Model Used : {model}")
    print(f"Total Cost : ${cost:.2f}")
    print(f"Message    : {message}")


if __name__ == "__main__":
    main()
