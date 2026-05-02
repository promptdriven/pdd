"""Examples showing run_agentic_sync (issue URL) and run_global_sync (project-wide Tier 1)."""

import sys
from pathlib import Path
from unittest.mock import patch, MagicMock

# Add the project root to sys.path
project_root = Path(__file__).resolve().parent.parent
sys.path.append(str(project_root))

from pdd.agentic_sync import (
    _is_github_issue_url,
    _parse_llm_response,
    run_agentic_sync,
    run_global_sync,
)
from pdd.agentic_sync_runner import DepGraphFromArchitectureResult


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
         patch("pdd.agentic_sync.build_dep_graph_from_architecture_data") as mock_graph, \
         patch("pdd.agentic_sync._run_dry_run_validation") as mock_dry_run, \
         patch("pdd.agentic_sync._filter_already_synced") as mock_filter_synced, \
         patch("pdd.agentic_sync._detect_modules_from_branch_diff", return_value=[]), \
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
        mock_graph.return_value = DepGraphFromArchitectureResult(
            {"auth": [], "user_service": ["auth"]},
            [],
        )
        mock_dry_run.return_value = (
            True,
            {"auth": Path.cwd(), "user_service": Path.cwd()},
            [],
            0.0,
        )
        mock_filter_synced.return_value = ["auth", "user_service"]
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

    # --- Global Sync (no-argument `pdd sync`) ---
    print("\nRunning project-wide Tier 1 global sync (dry run)")
    print("-" * 60)

    with patch("pdd.agentic_sync._find_project_root", return_value=Path("/tmp/proj")), \
         patch("pdd.agentic_sync._load_architecture_json") as mock_arch, \
         patch("pdd.agentic_sync._architecture_module_basenames") as mock_basenames, \
         patch("pdd.agentic_sync._analyze_global_sync_modules") as mock_analyze, \
         patch("pdd.agentic_sync.build_dep_graph_from_architecture_data") as mock_graph, \
         patch("pdd.agentic_sync._dependency_ordered_modules") as mock_order, \
         patch("pdd.agentic_sync._print_global_sync_plan"):

        mock_arch.return_value = (
            {"modules": [
                {"filename": "auth_python.prompt", "dependencies": []},
                {"filename": "user_service_python.prompt",
                 "dependencies": ["auth_python.prompt"]},
            ]},
            Path("/tmp/proj/architecture.json"),
        )
        mock_basenames.return_value = ["auth", "user_service"]

        analysis = MagicMock()
        analysis.modules_to_sync = ["auth", "user_service"]
        analysis.module_cwds = {}
        analysis.estimated_cost = 0.42
        mock_analyze.return_value = analysis

        mock_graph.return_value = DepGraphFromArchitectureResult(
            {"auth": [], "user_service": ["auth"]},
            [],
        )
        mock_order.return_value = ["auth", "user_service"]

        # --- EXECUTE THE MODULE ---
        success, message, cost, model = run_global_sync(
            verbose=False,
            quiet=True,
            budget=20.0,
            dry_run=True,
        )

    print("\n--- Global Sync Result ---")
    print(f"Success    : {success}")
    print(f"Model Used : {model}")
    print(f"Total Cost : ${cost:.2f}")
    print(f"Message    : {message}")

    # --- Durable Issue Sync (--durable) ---
    # When durable=True, run_agentic_sync dispatches to DurableSyncRunner
    # instead of AsyncSyncRunner. Module identification, dependency-graph
    # construction, dry-run validation, fingerprint filtering, and initial
    # cost accounting are all unchanged.
    print("\nRunning durable agentic sync (mocked, --durable)")
    print("-" * 60)

    with patch("pdd.agentic_sync.DurableSyncRunner") as mock_durable_cls, \
         patch("pdd.agentic_sync.AsyncSyncRunner") as mock_async_cls, \
         patch("pdd.agentic_sync.build_dep_graph_from_architecture_data") as mock_graph, \
         patch("pdd.agentic_sync._run_dry_run_validation") as mock_dry_run, \
         patch("pdd.agentic_sync._filter_already_synced") as mock_filter_synced, \
         patch("pdd.agentic_sync._detect_modules_from_branch_diff", return_value=["auth"]), \
         patch("pdd.agentic_sync._load_architecture_json") as mock_arch, \
         patch("pdd.agentic_sync._run_gh_command") as mock_gh, \
         patch("pdd.agentic_sync._check_gh_cli", return_value=True):

        import json
        mock_gh.return_value = (True, json.dumps({
            "title": "Durable rerun safety",
            "body": "Cloud worker timed out; want resumable sync.",
            "comments_url": "",
        }))
        mock_arch.return_value = (
            [{"filename": "auth_python.prompt", "dependencies": []}],
            Path("/tmp/architecture.json"),
        )
        mock_graph.return_value = DepGraphFromArchitectureResult({"auth": []}, [])
        mock_dry_run.return_value = (True, {"auth": Path.cwd()}, [], 0.0)
        mock_filter_synced.return_value = ["auth"]
        mock_durable = MagicMock()
        mock_durable.run.return_value = (True, "1 module checkpointed", 0.20)
        mock_durable_cls.return_value = mock_durable

        success, message, cost, model = run_agentic_sync(
            issue_url="https://github.com/example/repo/issues/1328",
            verbose=False,
            quiet=True,
            budget=10.0,
            durable=True,
            durable_branch="sync/issue-1328",
            no_resume=False,
            durable_max_parallel=2,
        )

        # Durable mode dispatches to DurableSyncRunner, not AsyncSyncRunner.
        assert mock_durable_cls.called, "Expected DurableSyncRunner dispatch"
        assert not mock_async_cls.called, "AsyncSyncRunner must not run in durable mode"

    print("\n--- Durable Sync Result ---")
    print(f"Success    : {success}")
    print(f"Total Cost : ${cost:.2f}")
    print(f"Message    : {message}")


if __name__ == "__main__":
    main()
