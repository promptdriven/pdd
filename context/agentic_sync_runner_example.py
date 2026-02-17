"""Example showing how to use AsyncSyncRunner for parallel module sync."""

import sys
from pathlib import Path
from unittest.mock import patch, MagicMock

# Add the project root to sys.path
project_root = Path(__file__).resolve().parent.parent
sys.path.append(str(project_root))

from pdd.agentic_sync_runner import (
    AsyncSyncRunner,
    ModuleState,
    build_dep_graph_from_architecture,
    _format_duration,
    _parse_cost_from_csv,
)


def main():
    """Demonstrate the AsyncSyncRunner with mocked subprocess calls."""

    # --- Dependency Graph Building ---
    # build_dep_graph_from_architecture reads architecture.json and filters
    # to only include dependencies within the target basenames.
    print("--- Dependency Graph Example ---")
    # With a real architecture.json:
    # graph = build_dep_graph_from_architecture(Path("architecture.json"), ["auth", "user_service", "api"])
    # Result: {"auth": [], "user_service": ["auth"], "api": ["auth", "user_service"]}

    # --- Module State Tracking ---
    state = ModuleState()
    print(f"Initial state: {state.status}")  # "pending"

    # --- Duration Formatting ---
    print(f"45 seconds: {_format_duration(100.0, 145.0)}")    # "45s"
    print(f"2 minutes: {_format_duration(0.0, 125.0)}")       # "2m5s"

    # --- Runner Execution (mocked) ---
    print("\n--- AsyncSyncRunner Example ---")

    # Define modules and their dependencies
    basenames = ["db_schema", "models", "api_orders", "api_users"]
    dep_graph = {
        "db_schema": [],
        "models": ["db_schema"],
        "api_orders": ["models"],
        "api_users": ["models"],
    }

    # Sync options passed through to each subprocess
    sync_options = {
        "budget": 5.0,
        "skip_verify": False,
        "skip_tests": False,
        "agentic": True,
        "no_steer": True,
    }

    # GitHub info for live comment updates (set to None to disable)
    github_info = {
        "owner": "example",
        "repo": "myproject",
        "issue_number": 42,
        "cwd": Path.cwd(),
    }

    runner = AsyncSyncRunner(
        basenames=basenames,
        dep_graph=dep_graph,
        sync_options=sync_options,
        github_info=None,  # Disable GitHub comments for demo
        quiet=True,
    )

    # Mock the subprocess calls
    with patch.object(runner, "_sync_one_module") as mock_sync, \
         patch.object(runner, "_update_github_comment"):

        # Simulate: db_schema and models succeed, then api_orders and api_users run in parallel
        def fake_sync(basename):
            costs = {"db_schema": 0.12, "models": 0.08, "api_orders": 0.15, "api_users": 0.10}
            return (True, costs.get(basename, 0.0), "")

        mock_sync.side_effect = fake_sync

        # --- EXECUTE THE RUNNER ---
        success, message, total_cost = runner.run()

    print(f"Success    : {success}")
    print(f"Total Cost : ${total_cost:.2f}")
    print(f"Message    : {message}")

    # Show final module states
    print("\n--- Module States ---")
    for name, state in runner.module_states.items():
        print(f"  {name}: {state.status} (cost: ${state.cost:.2f})")

    # --- Comment Body Preview ---
    print("\n--- GitHub Comment Preview ---")
    body = runner._build_comment_body(issue_number=42)
    print(body)


if __name__ == "__main__":
    main()
